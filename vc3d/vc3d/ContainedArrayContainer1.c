#include <vcc.h>
#include <stdlib.h>	//malloc

typedef struct MyObject
{
	int field;
} MyObject;

typedef _(dynamic_owns) struct MyObjectArrayContainer
{
	MyObject* arr;
	size_t size;

	_(ghost \object arrob)
	_(invariant arrob == (MyObject[size])arr)
	_(invariant \malloc_root(arrob))
	_(invariant \mine(arrob))
	
	_(invariant \forall size_t i; i < size ==> \mine(arr+i))
} MyObjectArrayContainer;

void InitContainer(MyObjectArrayContainer* container)
	_(writes \extent(container) )
	_(ensures \wrapped(container))
	_(ensures \unchanged(container->size))
	_(requires container->size > 0)
{
	container->arr = malloc(sizeof(MyObject) * container->size);
	_(assume container->arr != NULL)

	_(ghost size_t i)
	_(ghost
		for (i=0; i<container->size; i++)
			_(writes \array_members(container->arr,container->size) )
			_(invariant \forall size_t j; j >= i && j < container->size ==> \mutable(container->arr+j))
			_(invariant \forall size_t j; j < i ==> \wrapped(container->arr+j))
		{
			_(wrap container->arr+i)
		}
	)

	_(ghost container->\owns = \array_members(container->arr,container->size))

	_(ghost container->arrob = (MyObject[container->size])container->arr)
	_(wrap container->arrob)
	_(ghost container->\owns += container->arrob)

	_(wrap container)
}
void DisposeContainer(MyObjectArrayContainer* container)
	_(requires \wrapped(container))
	_(writes container)
	_(ensures \extent_mutable(container) )
	_(requires container->size > 0)
	//Optional:
	//_(ensures \unchanged(container->size))
	//_(ensures container->arr == NULL)
	//_(ensures container->arrob == NULL)
{
	_(unwrap container)
	
	_(assert \forall size_t i; i < container->size ==> \wrapped(container->arr+i))

	_(ghost size_t i)
	_(ghost
		for (i = 0; i < container->size; i++)
			_(writes \array_members(container->arr,container->size))
			_(invariant \forall size_t j; j >= i && j < container->size ==> \wrapped(container->arr+j))
			_(invariant \forall size_t j; j < i ==> \mutable(container->arr+j))
		{
			_(unwrap container->arr+i)
		}
	)

	_(unwrap container->arrob)

	free(_(MyObject[container->size])container->arr);

	//Optional:
	//container->arr = NULL;
	//_(ghost container->arrob = NULL)
}

void ObjectArrayContainerMallocAndFree_Methods()
{
	MyObjectArrayContainer cont;
	MyObjectArrayContainer* container = &cont;

	container->size = 7;
	InitContainer(container);
	DisposeContainer(container);
}




typedef _(dynamic_owns) struct ContainedArrayContainer
{
	MyObjectArrayContainer containedarray1;
	MyObjectArrayContainer containedarray2;

	_(invariant \mine(&containedarray1))
	_(invariant \mine(&containedarray2))

	_(invariant \forall size_t i; i < containedarray1.size ==> \mine(&containedarray1.arr[i]) )
	_(invariant \forall size_t i; i < containedarray1.size ==> containedarray1.arr[i].field == 0)
} ContainedArrayContainer;

