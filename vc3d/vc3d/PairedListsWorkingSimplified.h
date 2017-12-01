//This is like PairedListsWorking, but without witnesses... fails!
 
#include <vcc.h>
//#include <cstdlib>   //malloc
#include <stdlib.h>   //malloc
 
typedef struct Paired1 Paired1;
typedef struct Paired2 Paired2;
 
typedef struct Paired1
{
	//Paired* pair;
	float num;

} Paired1;

typedef struct Paired2
{
	float num;

} Paired2;
 
typedef _(dynamic_owns) struct PairedLists
{
	//The maximum sizes of the following arrays
	size_t num1;
	size_t num2;

	_(invariant num1 > 0)
	_(invariant num2 > 0)
 
	//Heap arrays storing Paired objects
	Paired1* pairarray1;
	Paired2* pairarray2;

	//Insist that the arrays do not overlap
	_(invariant pairarray1 != pairarray2)
	_(invariant \arrays_disjoint(pairarray1, num1, pairarray2, num2))

	_(ghost \object arrayob1)
	_(ghost \object arrayob2)
	_(invariant arrayob1 == (Paired1[num1])pairarray1)
	_(invariant arrayob2 == (Paired2[num2])pairarray2)

	_(invariant \mine(arrayob1))
	_(invariant \mine(arrayob2))

	_(invariant arrayob1 != arrayob2)

	_(invariant \malloc_root(arrayob1))
	_(invariant \malloc_root(arrayob2))
	
 
	_(invariant \forall size_t i; {pairarray1+i} i < num1 ==> \mine(pairarray1+i))
	_(invariant \forall size_t i; {pairarray2+i} i < num2 ==> \mine(pairarray2+i))
 
 
} PairedLists;
 
void PairedListInit(PairedLists* dis);
void PairedListDispose(PairedLists* dis);

