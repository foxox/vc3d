//Paired var list implementation using two paired types
 
#include <vcc.h>
#include <stdlib.h>   //malloc
 
typedef struct PairedA PairedA;
typedef struct PairedB PairedB;
 
typedef struct PairedA
{
	PairedB* pair;
} PairedA;

typedef struct PairedB
{
	PairedA* pair;
} PairedB;
 
typedef _(dynamic_owns) struct PairedVarLists
{
	//Used size of the arrays
	size_t num1;
	size_t num2;
	//Maximum sizes of the arrays
	size_t cap1;
	size_t cap2;
	//Size invariants
	_(invariant num1 <= cap1)
	_(invariant num2 <= cap2)
	_(invariant cap1 > 0)// && cap1 <= 10000)
	_(invariant cap2 > 0)// && cap2 <= 10000)
 
	//Arrays storing Paired objects
	PairedA* pairarray1;
	PairedB* pairarray2;
	//Require that the arrays do not overlap
	//_(invariant pairarray1 != pairarray2)
	_(invariant \arrays_disjoint(pairarray1, cap1, pairarray2, cap2))

	//Array objects (needed for free/dispose)
	_(ghost \object arrayob1)
	_(ghost \object arrayob2)
	//Array object invariants
	_(invariant arrayob1 == (PairedA[cap1])pairarray1)
	_(invariant arrayob2 == (PairedB[cap2])pairarray2)
	_(invariant \malloc_root(arrayob1))
	_(invariant \malloc_root(arrayob2))
	_(invariant \mine(arrayob1) && \mine(arrayob2))
 
	//Ownership
	_(invariant \forall size_t i; {&pairarray1[i]} i < cap1 ==>
		\mine(&pairarray1[i])
	)
	_(invariant \forall size_t j; {&pairarray2[j]} j < cap2 ==>
		\mine(&pairarray2[j])
	)

	//Pairing invariants
	//Note that either the :hints or the \mine()s are needed
	_(invariant \forall size_t i;
		//{:hint \mine(&pairarray1[i])}
		//{&pairarray1[i]}
		i < num1 ==>
		\in_array(pairarray1[i].pair, pairarray2, num2)
		//&& pairarray1[i].pair->pair == &pairarray1[i]
	)
	_(invariant \forall size_t j;
		//{:hint \mine(&pairarray2[j])}
		//{&pairarray2[j]}
		j < num2 ==>
		\in_array(pairarray2[j].pair, pairarray1, num1)
		//&& pairarray2[j].pair->pair == &pairarray2[j]
	)

	_(invariant \forall size_t i;
		//{:hint \mine(&pairarray1[i]) }
		//{:hint \in_array(pairarray1[i].pair, pairarray2, num2) }
		i < num1 ==>
		pairarray1[i].pair->pair == &pairarray1[i]
	)
	_(invariant \forall size_t j;
		//{:hint \mine(&pairarray2[j]) }
		//{:hint \in_array(pairarray2[j].pair, pairarray1, num1) }
		j < num2 ==>
		pairarray2[j].pair->pair == &pairarray2[j]
	)
} PairedVarLists;
 
 
void PairedVarListInit(PairedVarLists* dis)
	_(writes \extent(dis))
	_(ensures \wrapped(dis))
{
	_(ghost dis->\owns = {};)
 
	dis->num1 = 2;
	dis->num2 = 2;
	dis->cap1 = 2;
	dis->cap2 = 2;
 
	dis->pairarray1 = malloc(dis->num1*sizeof(PairedA));
	dis->pairarray2 = malloc(dis->num2*sizeof(PairedB));
	//Ignore malloc failure (this is just scratch work code)
	_(assume dis->pairarray1 != NULL)
	_(assume dis->pairarray2 != NULL)
 
	//Initialize the pairs
 
	//If any of these following few lines are removed, the PairedVarLists's
	//pairing invariant is not satisfied. Comment any of these to test that the
	//invariant is working correctly. 
	dis->pairarray1[0].pair = &dis->pairarray2[0];    
	dis->pairarray2[0].pair = &dis->pairarray1[0];    
	dis->pairarray1[1].pair = &dis->pairarray2[1];
	dis->pairarray2[1].pair = &dis->pairarray1[1];
	 
	//Set \owns
	_(ghost dis->\owns += &dis->pairarray1[0];)
	_(ghost dis->\owns += &dis->pairarray1[1];)
	_(ghost dis->\owns += &dis->pairarray2[0];)
	_(ghost dis->\owns += &dis->pairarray2[1];)

	//Wrap the owned pieces
	_(wrap &dis->pairarray1[0];)
	_(wrap &dis->pairarray1[1];)
	_(wrap &dis->pairarray2[0];)
	_(wrap &dis->pairarray2[1];)
 
	//Same for array objects
	_(ghost dis->\owns += (PairedA[dis->num1])dis->pairarray1)
	_(ghost dis->\owns += (PairedB[dis->num2])dis->pairarray2)
	_(wrap (PairedA[dis->num1])dis->pairarray1)
	_(wrap (PairedB[dis->num2])dis->pairarray2)
	_(ghost dis->arrayob1 = (PairedA[dis->num1])dis->pairarray1)
	_(ghost dis->arrayob2 = (PairedB[dis->num2])dis->pairarray2)
 
	_(wrap dis)  
}

void PairedVarListGrow(PairedVarLists* dis)
	_(requires dis->cap1-dis->num1 >= 2)
	_(requires dis->cap2-dis->num2 >= 2)
	_(updates dis)
	_(ensures dis->num1 == \old(dis->num1 + 2))
	_(ensures dis->num2 == \old(dis->num2 + 2))
{
	//_(assert &dis->pairarray1[dis->num1+0] \in dis->\owns)
	//_(assert dis->pairarray1[dis->num1+0].\owner == dis)

	_(unwrapping dis)
	{
		//_(assert dis->pairarray1[dis->num1+0].\owner == \me)

		_(unwrapping &dis->pairarray1[dis->num1+0])
		dis->pairarray1[dis->num1+0].pair = &dis->pairarray2[dis->num2+0];
		_(unwrapping &dis->pairarray2[dis->num2+0])
		dis->pairarray2[dis->num2+0].pair = &dis->pairarray1[dis->num1+0];

		_(unwrapping &dis->pairarray1[dis->num1+1])
		dis->pairarray1[dis->num1+1].pair = &dis->pairarray2[dis->num2+1];
		_(unwrapping &dis->pairarray2[dis->num2+1])
		dis->pairarray2[dis->num2+1].pair = &dis->pairarray1[dis->num1+1];
		
		dis->num1 += 2;
		dis->num2 += 2;
	}
}


void PairedVarListDispose(PairedVarLists* dis)
	_(requires \wrapped(dis))
	_(writes dis)
	_(ensures \extent_mutable(dis))
 
{
	_(unwrap dis)
 
	//These correspond with the /mine invariants in the PairedVarList struct
	_(assert \forall size_t i; i < dis->cap1 ==>
		\wrapped(&dis->pairarray1[i])
	)
	_(assert \forall size_t j; j < dis->cap2 ==>
		\wrapped(&dis->pairarray2[j])
	)
 
	_(unwrap dis->arrayob1)
	_(unwrap dis->arrayob2)
 
	for(size_t i = 0; i < dis->cap1; i++)
		_(writes \array_members(dis->pairarray1,dis->cap1))
		_(invariant \forall size_t j; j >= i && j < dis->cap1 ==>
			\wrapped(dis->pairarray1+j)
		)
		_(invariant \forall size_t j; j < i ==>
			\mutable(dis->pairarray1+j)
		)
	{
		_(unwrap &dis->pairarray1[i])
	}
 
	for(size_t i = 0; i < dis->cap2; i++)
		_(writes \array_members(dis->pairarray2,dis->cap2))
		_(invariant \forall size_t j; j >= i && j < dis->cap2 ==>
			\wrapped(dis->pairarray2+j)
		)
		_(invariant \forall size_t j; j < i ==>
			\mutable(dis->pairarray2+j)
		)
	{
		_(unwrap &dis->pairarray2[i])
	}
 
	free( _(PairedA[dis->cap1])dis->pairarray1);
	free( _(PairedB[dis->cap2])dis->pairarray2);
}
 
//This ensures that none of my function preconditions are inconsistent.
//Equivalent to using /smoke
void FunctionTester()
{
	PairedVarLists init_me;
	PairedVarListInit(&init_me);
	PairedVarListDispose(&init_me);
}