//100% WORKING PAIRED LISTS IMPLEMENTATION, modified for variable size list
//Uses witnesses
 
#include <vcc.h>
#include <stdlib.h>   //malloc
 
typedef struct Paired Paired;
 
typedef struct Paired
{
	Paired* pair;
	//_(invariant \approves(\this->\owner, pair))
	//This isn't needed since no volatile updates happen to these
	//Any Paired owned by a PairedVarLists is wrapped except while the PairedVarLists is unwrapped
	//Wrapping the PairedVarLists forces all of its invariants about the Paired(s) to check
} Paired;
 
typedef _(dynamic_owns) struct PairedVarLists
{
	//Used size of the arrays
	size_t num1;
	size_t num2;
	//The maximum sizes of the following arrays
	size_t cap1;
	size_t cap2;
	//Size invariants
	_(invariant num1 <= cap1)
	_(invariant num2 <= cap2)
 
	//Heap arrays storing Paired objects
	Paired* pairarray1;
	Paired* pairarray2;
	//Insist that the arrays do not overlap
	_(invariant pairarray1 != pairarray2)
	_(invariant \arrays_disjoint(pairarray1, cap1, pairarray2, cap2))

	//Array objects
	_(ghost \object arrayob1)
	_(ghost \object arrayob2)
	//Array object invariants
	_(invariant arrayob1 == (Paired[cap1])pairarray1)
	_(invariant arrayob2 == (Paired[cap2])pairarray2)
	_(invariant \malloc_root(arrayob1))
	_(invariant \malloc_root(arrayob2))
	_(invariant \mine(arrayob1) && \mine(arrayob2))

	//Maps of witnesses for the pair indexes between the two arrays
	//This lets me avoid using existential quantification in the invariants for this object
	_(ghost \natural PairedArray1_witnesses[\natural];)
	_(ghost \natural PairedArray2_witnesses[\natural];)
	_(invariant \forall \natural i; i < num1 ==> PairedArray1_witnesses[i] < num2)
	_(invariant \forall \natural j; j < num2 ==> PairedArray2_witnesses[j] < num1)
 
	//Ownership
	_(invariant \forall \natural i; i < cap1 ==>
		\mine(&pairarray1[i])
	)
	_(invariant \forall \natural j; j < cap2 ==>
		\mine(&pairarray2[j])
	)

	//Pairing invariants
	_(invariant \forall \natural i; i < num1 ==>
		\mine(&pairarray1[i]) &&
		\mine(&pairarray2[PairedArray1_witnesses[i]]) &&
		pairarray2[PairedArray1_witnesses[i]].pair == &pairarray1[i]
	)
	_(invariant \forall \natural j; j < num2 ==>
		\mine(&pairarray2[j]) &&
		\mine(&pairarray1[PairedArray2_witnesses[j]]) &&
		pairarray1[PairedArray2_witnesses[j]].pair == &pairarray2[j]
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
	//Ignore malloc failure for the sake of testing the rest of this stuff concisely
	_(assume dis->pairarray1 != NULL)
	_(assume dis->pairarray2 != NULL)
 
	//Initialize the pairs and witnesses
 
	//If any of these following few lines are removed, the PairedVarLists's pairing invariant is not satisfied. Comment any of these to test that the invariant is working correctly.
 
	dis->pairarray1[0].pair = &dis->pairarray2[0];
	_(ghost dis->PairedArray1_witnesses[0] = 0)
	dis->pairarray2[0].pair = &dis->pairarray1[0];
	_(ghost dis->PairedArray2_witnesses[0] = 0)
 
	dis->pairarray1[1].pair = &dis->pairarray2[1];
	_(ghost dis->PairedArray1_witnesses[1] = 1)
	dis->pairarray2[1].pair = &dis->pairarray1[1];
	_(ghost dis->PairedArray2_witnesses[1] = 1)
	 
	//Set \owns
 
	_(ghost dis->\owns += &dis->pairarray1[0];)
	_(ghost dis->\owns += &dis->pairarray1[1];)
 
	_(ghost dis->\owns += &dis->pairarray2[0];)
	_(ghost dis->\owns += &dis->pairarray2[1];)
 
	_(wrap &dis->pairarray1[0];)
	_(wrap &dis->pairarray1[1];)
	_(wrap &dis->pairarray2[0];)
	_(wrap &dis->pairarray2[1];)
 
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
	_(assert \forall size_t i; i < dis->cap1 ==> \wrapped(&dis->pairarray1[i]))
	_(assert \forall size_t j; j < dis->cap2 ==> \wrapped(&dis->pairarray2[j]))
 
	_(unwrap dis->arrayob1)
	_(unwrap dis->arrayob2)
 
	for(size_t i = 0; i < dis->cap1; i++)
		_(writes \array_members(dis->pairarray1,dis->cap1))
		_(invariant \forall size_t j; j >= i && j < dis->cap1 ==> \wrapped(dis->pairarray1+j))
		_(invariant \forall size_t j; j < i ==> \mutable(dis->pairarray1+j))
	{
		_(unwrap &dis->pairarray1[i])
	}
 
	for(size_t i = 0; i < dis->cap2; i++)
		_(writes \array_members(dis->pairarray2,dis->cap2))
		_(invariant \forall size_t j; j >= i && j < dis->cap2 ==> \wrapped(dis->pairarray2+j))
		_(invariant \forall size_t j; j < i ==> \mutable(dis->pairarray2+j))
	{
		_(unwrap &dis->pairarray2[i])
	}
 
	free( _(Paired[dis->cap1])dis->pairarray1);
	free( _(Paired[dis->cap2])dis->pairarray2);
}
 
void FunctionTester()
{
	PairedVarLists init_me;
	PairedVarListInit(&init_me);
	PairedVarListDispose(&init_me);
}