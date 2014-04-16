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




typedef struct ContainedArrayContainer
{
	MyObjectArrayContainer containedarray1;
	MyObjectArrayContainer containedarray2;

	_(invariant \mine(&containedarray1))
	_(invariant \mine(&containedarray2))
} ContainedArrayContainer;













//
//void InitContainer3(MyObjectArrayContainer* container)
//	_(writes \extent(container) )
//	_(ensures \wrapped(container))
//	_(maintains container->size == 3)
//{
//	container->arr = malloc(sizeof(MyObject) * container->size);
//	_(assume container->arr != NULL)
//
//	_(wrap container->arr+0)
//	_(wrap container->arr+1)
//	_(wrap container->arr+2)
//
//	_(ghost container->\owns = \array_members(container->arr,container->size))
//
//	_(ghost container->arrob = (MyObject[container->size])container->arr)
//	_(wrap container->arrob)
//	_(ghost container->\owns += container->arrob)
//
//	_(wrap container)
//}
//
//void DisposeContainer3(MyObjectArrayContainer* container)
//	_(requires \wrapped(container))
//	_(writes container)
//	_(ensures \extent_mutable(container) )
//	_(requires container->size == 3)
//{
//	_(unwrap container)
//	
//	_(assert \forall size_t i; i < container->size ==> \wrapped(container->arr+i))
//
//	_(unwrap container->arr+0)
//	_(unwrap container->arr+1)
//	_(unwrap container->arr+2)
//
//	_(unwrap container->arrob)
//
//	FreeMyObjectArray(container->arr,container->size);
//}
//
//
//
//
//
//
//
//
//
//void FreeMyObjectArray(MyObject* arr, size_t size)
//	_(decreases 0)
//	_(writes (MyObject[size])arr)
//	_(writes \extent((MyObject[size])arr) )
//	_(requires \malloc_root((MyObject[size])arr))
//{
//	free(_(MyObject[size])arr);
//}
//
//void ObjectArrayContainerMallocAndFree_Contiguous()
//{
//	MyObjectArrayContainer cont;
//	MyObjectArrayContainer* container = &cont;
//
//	container->size = 10;
//	container->arr = malloc(sizeof(MyObject) * container->size);
//	_(assume container->arr != NULL)
//	
//	_(ghost size_t i)
//	_(ghost
//		for (i = 0; i < container->size; i++)
//			_(writes \array_members(container->arr,container->size))
//			_(invariant \forall size_t j; j >= i && j < container->size ==> \mutable(container->arr+j))
//			_(invariant \forall size_t j; j < i ==> \wrapped(container->arr+j))
//		{
//			_(wrap container->arr+i)
//		}
//	)
//
//	_(ghost
//		for (i = 0; i < container->size; i++)
//			_(writes \array_members(container->arr,container->size))
//			_(invariant \forall size_t j; j >= i && j < container->size ==> \wrapped(container->arr+j))
//			_(invariant \forall size_t j; j < i ==> \mutable(container->arr+j))
//		{
//			_(unwrap container->arr+i)
//		}
//	)
//	FreeMyObjectArray(container->arr,container->size);
//}
//
//void ObjectArrayContainerMallocAndFree_Block2()
//{
//	MyObjectArrayContainer cont;
//	MyObjectArrayContainer* container = &cont;
//
//	container->size = 3;
//	container->arr = malloc(sizeof(MyObject) * container->size);
//	_(assume container->arr != NULL)
//
//	_(ghost container->\owns = \array_members(container->arr,container->size))
//
//	_(ghost container->arrob = (MyObject[container->size])container->arr)
//	_(wrap container->arrob)
//	_(ghost container->\owns += container->arrob)
//	
//	//_(requires \full_context())
//	//_(writes \array_members(container->arr,container->size))
//	{
//		_(wrap container->arr+0)
//		_(wrap container->arr+1)
//		_(wrap container->arr+2)
//	}
//
//	_(wrap container)
//
//	_(requires \full_context())
//	_(writes container)
//	_(ensures \extent_mutable(container) )
//	{
//		_(unwrap container)
//		_(unwrap container->arrob)
//		_(unwrap container->arr+0)
//		_(unwrap container->arr+1)
//		_(unwrap container->arr+2)
//		FreeMyObjectArray(container->arr,container->size);
//	}
//}








////Initialize a MyObject array with variable size
//void MyObjectArrayContainerInit(MyObjectArrayContainer* container, size_t _size)
//	_(decreases 0)
//	_(writes \extent(container))
//	_(ensures \wrapped(container))
//	//_(requires _size==2)
//	_(ensures container->size == _size)
//{
//	_(ghost container->\owns = {})
//
//	container->size = _size;
//	container->arr = malloc(container->size * sizeof(MyObject));
//	_(assume container->arr != NULL)
//
//	//Keep track of the array object for the sake of destruction/disposal/free() later
//	_(ghost container->arrob = (MyObject[container->size])container->arr )
//	_(ghost container->\owns += container->arrob)
//	_(wrap container->arrob)
//
//	_(ghost container->\owns = container->\owns \union \array_members(container->arr,container->size) )
//	
//	_(ghost size_t i)
//	_(ghost
//		for (i = 0; i < container->size; i++)
//			_(decreases container->size-i)
//			_(writes \array_members(container->arr,container->size))
//			_(invariant \forall size_t j; j >= i && j < container->size ==> \mutable(&container->arr[j]))
//			_(invariant \forall size_t j; j < i ==> \wrapped(&container->arr[j]))
//			_(invariant container->size == _size)
//		{
//			_(wrap container->arr+i)
//			//_(assert \false)
//		}
//	)
//
//	_(wrap container)
//}
//
//void DisposeMyObjectArray(MyObject* objarr, size_t size)
//	_(decreases 0)
//    _(requires size > 0)
//    _(requires \forall size_t i; i < size ==> \wrapped(&objarr[i]))
//    _(writes \array_members(objarr,size));
////{
////    _(unwrap &objarr[0])
////    objarr[0].field = 3;
////}
//
////Dispose a MyObject array with variable size
//void MyObjectArrayContainerDispose(MyObjectArrayContainer* container, size_t size)
//	_(decreases 0)
//	_(requires \wrapped(container))
//	_(writes \extent(container->arr))
//	//_(ensures \extent_mutable(container))
//	_(requires container->size == 2 && size == container->size)
//{
//	////Establish writability of stuff owned by container
//	////_(assert \forall \object o; \in_array(o,container->arr,container->size) ==> o \in container->\owns)
//	//_(assert \forall \object o; o \in \array_members(container->arr,container->size) ==> o \in container->\owns)
//
//	//_(unwrap container)
//
//	////_(assert \forall \object o; \in_array(o,container->arr,container->size) ==> \fresh(o))
//	//_(assert \forall \object o; o \in \array_members(container->arr,container->size) ==> \fresh(o))
//	//
//	////_(assert \forall \object o; \in_array(o,container->arr,container->size) ==> \writable(o))
//	//_(assert \forall \object o; o \in \array_members(container->arr,container->size) ==> \writable(o))
//
//	//DisposeMyObjectArray(container->arr,container->size);
//
//
//
//	//_(ghost size_t i)
//	//_(ghost
//	//	for (i = 0; i < container->size; i++)
//	//		_(decreases container->size-i)
//	//		_(writes \array_members(container->arr,container->size) )
//	//		_(invariant \wrapped(container->arrob))
//	//		_(invariant \mutable(container))
//	//		_(invariant \forall size_t j; j < i ==> \mutable(container->arr+j))
//	//		_(invariant \forall size_t j; j >= i && j < container->size ==> \wrapped(container->arr+j))
//	//	{
//	//		_(assert &container->arr[1] \in container->\owns)
//	//		_(assert \wrapped(&container->arr[1]))
//	//		_(unwrap &container->arr[1])
//	//	}
//	//)
//
//
//	////Make arrayobject writable. This shows VCC that the free() below is okay
//	//_(unwrap container->arrob )
//
//	//free((void*) speccast(MyObject[container->size], container->arr));
//
//
//	//hmm. let's start with free and build up
//	free(_(MyObject*)container->arr);
//}
//
//void TestObjectContainingObjectArrayMalloc_VariableSize()
//{
//	MyObjectArrayContainer container;
//	size_t size = 2;
//
//	MyObjectArrayContainerInit(&container, size);
//
//	_(assert \wrapped(&container))
//	_(assert &container.arr \in \extent(&container))
//	//_(assert &container.arr[0] \in \extent(&container)) //false
//	
//	MyObjectArrayContainerDispose(&container, size);
//}





//void VCCError_TerminationChecking_Wrapped()
//	_(decreases 0)
//{
//	size_t size = 3;
//	MyObject* arr = malloc(sizeof(MyObject) * size);
//	if (arr!=NULL)
//	{
//		_(wrap arr+0)
//		_(wrap arr+1)
//		_(wrap arr+2)
//
//		_(decreases 0)	//with or without this, same error
//		//_(requires \forall size_t j; j < size ==> \wrapped(arr+j))
//		_(requires \full_context())
//		{
//			_(unwrap arr+0)
//				//anything
//		}
//	}
//}
//
//void VCCError_TerminationChecking_Wrapped_Obj()
//	_(decreases 0)
//{
//	MyObject obj;
//	_(wrap &obj)
//
//	_(decreases 0)
//	_(requires \wrapped(&obj))
//	_(requires \assume( \set_in(&obj, \domain(&obj))))
//	//_(requires \full_context())
//	{
//		_(unwrap &obj)
//			//anything
//	}
//}

