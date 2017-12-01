#include "PairedListsWorkingSimplified.h"

_(isolate_proof)
void PairedListInit(PairedLists* dis)
	_(writes \extent(dis))
	_(ensures \wrapped(dis))
{
	_(ghost dis->\owns = {};)
 
	dis->num1 = 2;
	dis->num2 = 2;
 
	dis->pairarray1 = (Paired1*)malloc(dis->num1*sizeof(Paired1));
	dis->pairarray2 = (Paired2*)malloc(dis->num2*sizeof(Paired2));
	//Ignore mal_(invariant \mine(arrayob1) && \mine(arrayob2))loc failure for the sake of testing the rest of this stuff concisely
	_(assume dis->pairarray1 != NULL)
	_(assume dis->pairarray2 != NULL)
 
	//Initialize the pairs and witnesses
 
	//If any of these following few lines are removed, the PairedLists's pairing invariant is not satisfied. Comment any of these to test that the invariant is working correctly.
 


	 
	//Set \owns
 
	_(ghost dis->\owns += &dis->pairarray1[0];)
	_(ghost dis->\owns += &dis->pairarray1[1];)
 
	_(ghost dis->\owns += &dis->pairarray2[0];)
	_(ghost dis->\owns += &dis->pairarray2[1];)
 
	_(wrap &dis->pairarray1[0];)
	_(wrap &dis->pairarray1[1];)
	_(wrap &dis->pairarray2[0];)
	_(wrap &dis->pairarray2[1];)
 
	_(ghost dis->\owns += (Paired1[dis->num1])dis->pairarray1)
	_(ghost dis->\owns += (Paired2[dis->num2])dis->pairarray2)
	_(wrap (Paired1[dis->num1])dis->pairarray1)
	_(wrap (Paired2[dis->num2])dis->pairarray2)
 
	_(ghost dis->arrayob1 = (Paired1[dis->num1])dis->pairarray1)
	_(ghost dis->arrayob2 = (Paired2[dis->num2])dis->pairarray2)
 
	_(wrap dis)                                                                                             
}

_(isolate_proof)
void PairedListDispose(PairedLists* dis)
_(requires \wrapped(dis))
_(writes dis)
_(ensures \extent_mutable(dis))
{
	_(unwrap dis)
 
	_(assert \forall size_t i; i < dis->num1 ==> \wrapped(dis->pairarray1+i))
	_(assert \forall size_t i; i < dis->num2 ==> \wrapped(dis->pairarray2+i))
 
	_(unwrap dis->arrayob1)
	_(unwrap dis->arrayob2)
 
	for(size_t i = 0; i < dis->num1; i++)
		_(writes \array_members(dis->pairarray1, dis->num1))
		_(invariant \forall size_t j; j >= i && j < dis->num1 ==> \wrapped(dis->pairarray1+j))
		_(invariant \forall size_t j; j < i ==> \mutable(dis->pairarray1+j))
	{
		_(unwrap dis->pairarray1+i)
	}
 
	for(size_t i = 0; i < dis->num2; i++)
		_(writes \array_members(dis->pairarray2, dis->num2))
		_(invariant \forall size_t j; j >= i && j < dis->num2 ==> \wrapped(dis->pairarray2+j))
		_(invariant \forall size_t j; j < i ==> \mutable(dis->pairarray2+j))
	{
		_(unwrap dis->pairarray2+i)
	}
 
	free( _(Paired1[dis->num1]) dis->pairarray1);
	free( _(Paired2[dis->num2]) dis->pairarray2);
}
 
void FunctionTester()
{
	PairedLists init_me;
	PairedListInit(&init_me);
	PairedListDispose(&init_me);
}
