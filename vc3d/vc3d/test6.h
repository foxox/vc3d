#include <vcc.h>
#include <stdlib.h>

typedef struct MyObject
{
	int field;
} MyObject;

typedef _(dynamic_owns) struct SimpleTestWithArray1
{
	MyObject* arr;
	size_t size;

	//Bad: second invariant cannot be shown to be admissible by default (though it is)
	//_(invariant \forall size_t i; i < size ==> \mine(&arr[i]))
	//_(invariant \forall size_t i; i < size ==> arr[i].field == 0)

	//Alternative: put all such invariants under one \forall
	//_(invariant \forall size_t i; i < size ==> \mine(arr+i) && arr[i].field == 0)

	//Optimal solution:
	//The problem with the first approach is that the first invariant triggers on \mine(arr+i)
	//It needs to trigger on arr+i in order for it to be available while VCC attempts to
	//convince itself that the second invariant (which mentions arr+i and not \mine(arr+i)
	//is admissible
	_(invariant \forall size_t i; /*{arr+i}*/ i < size ==> \mine(&arr[i]))
	_(invariant \forall size_t i; {:hint \mine(arr+i)} i < size ==> arr[i].field == 0)

} SimpleTestWithArray1;
