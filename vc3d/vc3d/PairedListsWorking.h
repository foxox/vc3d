//100% WORKING PAIRED LISTS IMPLEMENTATION
 
#include <vcc.h>
#include <cstdlib>   //malloc
 
typedef struct Paired Paired;
 
typedef struct Paired
{
    Paired* pair;
    //_(invariant \approves(\this->\owner, pair))
    //This isn't needed since no volatile updates happen to these
    //Any Paired owned by a PairedLists is wrapped except while the PairedLists is unwrapped
    //Wrapping the PairedLists forces all of its invariants about the Paired(s) to check
} Paired;
 
typedef _(dynamic_owns) struct PairedLists
{
    //The maximum sizes of the following arrays
    size_t num1;
    size_t num2;
 
    //Heap arrays storing Paired objects
    Paired* pairarray1;
    Paired* pairarray2;
    _(ghost \object arrayob1)
    _(ghost \object arrayob2)
    _(invariant arrayob1 == (Paired[num1])pairarray1)
    _(invariant arrayob2 == (Paired[num2])pairarray2)
    _(invariant \malloc_root(arrayob1))
    _(invariant \malloc_root(arrayob2))
    _(invariant \mine(arrayob1) && \mine(arrayob2))
 
    //Insist that the arrays do not overlap
    _(invariant pairarray1 != pairarray2)
    _(invariant \arrays_disjoint(pairarray1, num1, pairarray2, num2))
 
    //Maps of witnesses for the pair indexes between the two arrays
    //This lets me avoid using existential quantification in the invariants for this object
    _(ghost \natural PairedArray1_witnesses[\natural];)
    _(ghost \natural PairedArray2_witnesses[\natural];)
    _(invariant \forall \natural i; i < num1 ==> PairedArray1_witnesses[i] < num2)
    _(invariant \forall \natural j; j < num2 ==> PairedArray2_witnesses[j] < num1)
 
    //Pairing invariants
    //Why can't I pull out the \mine parts of this into separate parts like below?
    _(invariant \forall \natural i; i < num1 ==> \mine(&pairarray1[i]) && \mine(&pairarray2[PairedArray1_witnesses[i]]) && pairarray2[PairedArray1_witnesses[i]].pair == &pairarray1[i])
    _(invariant \forall \natural j; j < num2 ==> \mine(&pairarray2[j]) && \mine(&pairarray1[PairedArray2_witnesses[j]]) && pairarray1[PairedArray2_witnesses[j]].pair == &pairarray2[j])
 
    //Why can't I separate the \mine parts from the pair matching invariants (above) like this (below)?
    //_(invariant \forall \natural i; i < num1 ==> \mine(&pairarray1[i]))
    //_(invariant \forall \natural j; j < num2 ==> \mine(&pairarray2[j]))
    //_(invariant \forall \natural i; i < num1 ==> \mine(&pairarray2[PairedArray1_witnesses[i]]))
    //_(invariant \forall \natural j; j < num2 ==> \mine(&pairarray1[PairedArray2_witnesses[j]]))
    //_(invariant \forall \natural i; i < num1 ==> pairarray2[PairedArray1_witnesses[i]].pair == &pairarray1[i])
    //_(invariant \forall \natural j; j < num2 ==> pairarray1[PairedArray2_witnesses[j]].pair == &pairarray2[j])
 
    //The original attempt at an invariant, without witness storage. Inadmissible and I'm not sure how to fix that.
    /*_(invariant
        \forall size_t i; i < num1 ==>
            \mine(&pairarray1[i]) &&
            \exists size_t j;
                j < num2 &&
                \mine(&pairarray2[j]) &&
                &pairarray1[i] == pairarray2[j].pair)*/
 
} PairedLists;
 
 
void PairedListInit(PairedLists* dis)
    _(writes \extent(dis))
    _(ensures \wrapped(dis))
{
    _(ghost dis->\owns = {};)
 
    dis->num1 = 2;
    dis->num2 = 2;
 
    dis->pairarray1 = malloc(dis->num1*sizeof(Paired));
    dis->pairarray2 = malloc(dis->num2*sizeof(Paired));
    //Ignore malloc failure for the sake of testing the rest of this stuff concisely
    _(assume dis->pairarray1 != NULL)
    _(assume dis->pairarray2 != NULL)
 
    //Initialize the pairs and witnesses
 
    //If any of these following few lines are removed, the PairedLists's pairing invariant is not satisfied. Comment any of these to test that the invariant is working correctly.
 
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
 
void PairedListDispose(PairedLists* dis)
    _(requires \wrapped(dis))
    _(writes dis)
    _(ensures \extent_mutable(dis))
 
{
    _(unwrap dis)
 
    _(assert \forall size_t i; i < dis->num1 ==> \wrapped(&dis->pairarray1[i]))
    _(assert \forall size_t j; j < dis->num2 ==> \wrapped(&dis->pairarray2[j]))
 
    _(unwrap dis->arrayob1)
    _(unwrap dis->arrayob2)
 
    for(size_t i = 0; i < dis->num1; i++)
        _(writes \array_members(dis->pairarray1,dis->num1))
        _(invariant \forall size_t j; j >= i && j < dis->num1 ==> \wrapped(dis->pairarray1+j))
        _(invariant \forall size_t j; j < i ==> \mutable(dis->pairarray1+j))
    {
        _(unwrap &dis->pairarray1[i])
    }
 
    for(size_t i = 0; i < dis->num2; i++)
        _(writes \array_members(dis->pairarray2,dis->num2))
        _(invariant \forall size_t j; j >= i && j < dis->num2 ==> \wrapped(dis->pairarray2+j))
        _(invariant \forall size_t j; j < i ==> \mutable(dis->pairarray2+j))
    {
        _(unwrap &dis->pairarray2[i])
    }
 
    free( _(Paired[dis->num1])dis->pairarray1);
    free( _(Paired[dis->num2])dis->pairarray2);
}
 
void FunctionTester()
{
    PairedLists init_me;
    PairedListInit(&init_me);
    PairedListDispose(&init_me);
}