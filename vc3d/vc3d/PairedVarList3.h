//100% WORKING PAIRED LISTS IMPLEMENTATION, modified for variable size list
//Does not use witnesses
//For Tumblr
 
#include <vcc.h>
#include <stdlib.h>   //malloc
 
typedef struct Paired Paired;
 
typedef struct Paired
{
	Paired* pair;
} Paired;
 
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
	_(invariant cap1 > 0)
	_(invariant cap2 > 0)
 
	//Arrays storing Paired objects
	Paired* pairarray1;
	Paired* pairarray2;
	//Require that the arrays do not overlap
	_(invariant pairarray1 != pairarray2)
	_(invariant \arrays_disjoint(pairarray1, cap1, pairarray2, cap2))

	//Array objects (needed for free/dispose)
	_(ghost \object arrayob1)
	_(ghost \object arrayob2)
	//Array object invariants
	_(invariant arrayob1 == (Paired[cap1])pairarray1)
	_(invariant arrayob2 == (Paired[cap2])pairarray2)
	_(invariant \malloc_root(arrayob1))
	_(invariant \malloc_root(arrayob2))
	_(invariant \mine(arrayob1) && \mine(arrayob2))
 
	//Ownership
	_(invariant \forall \natural i; {&pairarray1[i]} i < cap1 ==>
		\mine(&pairarray1[i])
	)
	_(invariant \forall \natural j; {&pairarray2[j]} j < cap2 ==>
		\mine(&pairarray2[j])
	)

	//Pairing invariants
	//Note that either the :hints or the \mine()s are needed
	_(invariant \forall \natural i; {:hint \mine(&pairarray1[i])} i < num1 ==>
		//\mine(&pairarray1[i]) &&
		\in_array(pairarray1[i].pair, pairarray2, num2)
	)
	_(invariant \forall \natural j; {:hint \mine(&pairarray2[j])} j < num2 ==>
		//\mine(&pairarray2[j]) &&
		\in_array(pairarray2[j].pair, pairarray1, num1)
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
 
	dis->pairarray1 = malloc(dis->num1*sizeof(Paired));
	dis->pairarray2 = malloc(dis->num2*sizeof(Paired));
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
	_(ghost dis->\owns += (Paired[dis->num1])dis->pairarray1)
	_(ghost dis->\owns += (Paired[dis->num2])dis->pairarray2)
	_(wrap (Paired[dis->num1])dis->pairarray1)
	_(wrap (Paired[dis->num2])dis->pairarray2)
	_(ghost dis->arrayob1 = (Paired[dis->num1])dis->pairarray1)
	_(ghost dis->arrayob2 = (Paired[dis->num2])dis->pairarray2)
 
	_(wrap dis)  
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
 
	free( _(Paired[dis->cap1])dis->pairarray1);
	free( _(Paired[dis->cap2])dis->pairarray2);
}
 
//This ensures that none of my function preconditions are inconsistent.
//Equivalent to using /smoke
void FunctionTester()
{
	PairedVarLists init_me;
	PairedVarListInit(&init_me);
	PairedVarListDispose(&init_me);
}