#pragma once

#include <vcc.h>
#include <stdlib.h>	//malloc
typedef unsigned int uint;

typedef struct Paired Paired;

typedef struct Paired
{
	Paired* pair;
	//_(invariant \approves(\this->\owner, pair))
} Paired;

typedef _(dynamic_owns) struct PairedLists
{
	//The maximum sizes of the following arrays
	uint num1;
	uint num2;

	//Heap arrays storing Paired objects
	Paired* pairarray1;
	Paired* pairarray2;

	//Maps of witnesses for the pair indexes between the two arrays
	//This lets me avoid using existential quantification in the invariants for this object
	_(ghost	uint PairedArray1_witnesses[uint];)
	_(ghost	uint PairedArray2_witnesses[uint];)

	//Why can't I separate these from the invariant below like this?
	//_(invariant \forall uint i; i < num1 ==> \mine(&pairarray1[i]))
	//_(invariant \forall uint i; i < num2 ==> \mine(&pairarray2[i]))

	//Why can't I pull out the \mine parts of this into separate parts like above?
	_(invariant \forall uint i; i < num1 ==> \mine(&pairarray1[i]) && \mine(&pairarray2[PairedArray1_witnesses[i]]) && pairarray2[PairedArray1_witnesses[i]].pair == &pairarray1[i])
	_(invariant \forall uint j; j < num2 ==> \mine(&pairarray2[j]) && \mine(&pairarray1[PairedArray2_witnesses[j]]) && pairarray1[PairedArray2_witnesses[j]].pair == &pairarray2[j])

	//The original attempt at an invariant, without witness storage. VCC reports it as inadmissible
	/*_(invariant
		\forall uint i; i < num1 ==>
			\mine(&pairarray1[i]) &&
			\exists uint j;
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

	//THESE DO NOT HELP HERE
	//_(ghost dis->\owns += (Paired[dis->num1])dis->pairarray1;)
	//_(ghost dis->\owns += (Paired[dis->num2])dis->pairarray2;)

	_(ghost dis->\owns += &dis->pairarray1[0];)
	_(ghost dis->\owns += &dis->pairarray1[1];)

	_(ghost dis->\owns += &dis->pairarray2[0];)
	_(ghost dis->\owns += &dis->pairarray2[1];)


	//THESE DO NOT HELP HERE
	//_(wrap (Paired[dis->num1])dis->pairarray1)
	//_(wrap (Paired[dis->num2])dis->pairarray2)

	_(wrap &dis->pairarray1[0];)
	_(wrap &dis->pairarray1[1];)
	_(wrap &dis->pairarray2[0];)
	_(wrap &dis->pairarray2[1];)

	_(wrap dis)
}




//Old crap

	//OWNERSHIP

	//THESE DO NOT HELP HERE
	//_(invariant \mine( (Paired[num1]) pairarray1) )
	//_(invariant \mine( (Paired[num2]) pairarray2) )

	//These invariants on ownership, when uncommented, help see whether the ownership or pair condition portion of the following invariant is failing when it fails.

	//_(invariant \forall uint i;
	//	i < num1
	//	==>
	//	\mine(&pairarray1[i])
	//)

	//_(invariant \forall uint i;
	//	i < num2
	//	==>
	//	\mine(&pairarray2[i])
	//)





	//_(invariant num1 > 0)
	//_(invariant num2 > 0)

	//_(invariant \forall uint i;
	//	i < num1
	//	==>

	//	\mine(&pairarray1[i]) &&
	//	\mine(pairarray1[i].pair) &&
	//	\mine(pairarray1[i].pair->pair) &&

	//	//Condition that each Paired object in pairarray1
	//	pairarray1[i].pair->pair == &pairarray1[i]
	//	//pair's pair points back to pair
	//)

	//_(invariant \forall uint i;
	//	i < num2
	//	==>

	//	\mine(&pairarray2[i]) &&
	//	\mine(pairarray2[i].pair) &&
	//	\mine(pairarray2[i].pair->pair) &&

	//	//Condition that each Paired object in pairarray2
	//	pairarray2[i].pair->pair == &pairarray2[i]
	//	//pair's pair points back to pair
	//)







	//idk
	//_(invariant \on_unwrap(\this,\mutable_array(pairarray1,num1)) )
	//_(invariant pairarray2 != NULL && \mutable_array(pairarray2,num2))
	/*_(invariant
		(\array_range(pairarray1,num1) \inter \array_range(pairarray2,num2)) == {}
	)*/

	//_(invariant \forall \object o; ( \mine(o) && (o \is Paired) ) ==>
	//	(\exists uint i; i < num1 && &pairarray1[i] == o)
	//	||
	//	(\exists uint i; i < num2 && &pairarray2[i] == o)
	//)

	//Get this to work, then go below
	/*_(invariant
		(\forall uint i; i < num1 ==> \mine(&pairarray1[i]) && \mine(pairarray1[i].pair) )
		&&
		(\forall uint i; i < num2 ==> \mine(&pairarray2[i]) && \mine(pairarray2[i].pair))
		&&
		(\exists uint i; i < num2 && \mine(&pairarray2[i]) && \mine(pairarray2[i].pair) && \mine(&pairarray1[0]) && pairarray2[i].pair == &pairarray1[0])
	)*/
	//_(invariant \exists uint i; i < num2 && pairarray2[i].pair == &pairarray1[0])


	//_(invariant \on_unwrap(\this, \exists \object j; j \in \array_range(pairarray2,num2) && j == &pairarray1[0]))
	//_(invariant \exists \object j; j \in \array_range(pairarray2,num2) && j == &pairarray1[0])

	//If the above works, then try this
	//_(invariant \forall uint i; {\mine(&pairarray1[i])} i < num1 && \mine(&pairarray1[i]) ==>
	//	\exists uint j; j < num2 && &pairarray1[i] == pairarray2[j].pair
	//)