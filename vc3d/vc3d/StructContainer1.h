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
	_(invariant \forall size_t i; i < size ==> \mine(arr+i))
	//_(invariant \mine((MyObject[size])arr))
	_(invariant \malloc_root((MyObject[size])arr))
} MyObjectArrayContainer;

void ObjectArrayContainerMallocAndFree()
{
	MyObjectArrayContainer cont;
	MyObjectArrayContainer* container = &cont;
	container->arr = malloc(sizeof(MyObject) * 10);
	_(assume container->arr != NULL)

	container->size = 10;

	_(ghost container->\owns = \array_members(container->arr,container->size) )
	
	//_(ghost container->\owns += (MyObject[container->size])container->arr)
	//_(wrap (MyObject[container->size])container->arr)

	_(ghost size_t i)
	_(ghost
		for (i = 0; i < container->size; i++)
			_(writes \array_members(container->arr,container->size))
			_(invariant \forall size_t j; j >= i && j < container->size ==> \mutable(&container->arr[j]))
			_(invariant \forall size_t j; j < i ==> \wrapped(&container->arr[j]))
			_(invariant \malloc_root((MyObject[container->size])container->arr))
		{
			_(wrap container->arr+i)
		}
	)

	_(wrap container)
	_(unwrap container)

	//_(unwrap (MyObject[container->size])container->arr)

	free(_(MyObject[container->size])container->arr);
}

	//error VC8510: Assertion '\extent(p) is writable in call to free(_(MyObject[10])container->arr)' did not verify.

	//but... from the manual:

	//\objset \span(\object o)
	//The set consisting of o, along with a pointer to each primitive field of o.

	//\objset \extent(\object o)
	//This returns \span(o), along with \extent of any struct fields of o.

	//So \extent(p) is \extent((MyObject[10])container->arr) and
	//by these descriptions of \span and \extent that should be the
	//array object itself plus its fields.

	//but... also from the manual:

	//If the base type of the
	//array is an object type, the array object has no fields (other than the
	//implicit ones present in all objects), and so is not very useful.

	//...so shouldn't the \extent((MyObject[10])container->arr) just be the 
	//array object itself (plus implicit fields) and we already know that it is
	//writable because we just unwrapped it.
	
	//What am I missing?

#if 0



typedef _(dynamic_owns) struct MyObjectContainer
{
	MyObject* obj;
	_(invariant \mine(obj))
	//_(invariant \wrapped(obj))
	_(invariant \malloc_root(obj))
} MyObjectContainer;

void allocandwrap(MyObjectContainer* container)
	_(writes \extent(container))
	_(ensures \wrapped(container))
	_(ensures \fresh(container->obj))
{
	_(ghost container->\owns = {})
	container->obj = malloc(sizeof(MyObject));
	_(assume container->obj != NULL)
	
	_(wrap container->obj)
	_(assert \wrapped(container->obj))

	_(ghost container->\owns += container->obj)

	_(wrap container)
}

void freeinnerobject(MyObjectContainer* container)
	_(requires \malloc_root(container->obj))
	_(requires \extent_mutable(container->obj))
	_(writes \extent(container->obj))
	_(requires \thread_local(container))
{
	freeobject(container->obj);
}

void freeobject(MyObject* obj)
	_(requires \malloc_root(obj))
	_(requires \extent_mutable(obj))
	_(writes \extent(obj))
{
	free(obj);
}

void cleanup(MyObjectContainer* container)
	_(requires \wrapped(container))
	_(writes container)
	_(ensures \extent_mutable(container))
{
	_(unwrap container)
	_(unwrap container->obj)
	freeinnerobject(container);
	//free(container->obj);
}

void test()
{
	MyObjectContainer cont;
	allocandwrap(&cont);
	cleanup(&cont);
}


	/*_(assert container->obj \in container->\owns)
	_(unwrap container)*/
	
	//_(ghost size_t i)
	//_(ghost
	//	for (i = 0; i < 10; i++)
	//		_(decreases 10-i)
	//		_(writes container->obj)
	//		_(invariant \forall size_t j; {\match_ulong(j)} j <= 5 && j < 10 ==> \wrapped(container->obj))
	//	{
	//		if (i == 5)
	//			_(unwrap container->obj)
	//	}
	//)

	//_(assert \false)

	//free(_(MyObject*)container->obj);









void allocandwrap2(MyObjectArrayContainer* container)
	_(writes \extent(container))
	_(ensures \wrapped(container))
	_(ensures \malloc_root((MyObject[container->size])container->arr))
{
	//_(ghost container->\owns = {})
	container->arr = malloc(sizeof(MyObject) * container->size);
	_(assume container->arr != NULL)

	_(ghost container->\owns = \array_members(container->arr,container->size))

	_(ghost container->\owns += (MyObject[container->size])container->arr)
	_(wrap (MyObject[container->size])container->arr)

	_(ghost size_t i)
	_(ghost
		for (i = 0; i < container->size; i++)
			_(writes \array_members(container->arr,container->size))
			_(invariant \forall size_t j; j >= i && j < container->size ==> \mutable(&container->arr[j]))
			_(invariant \forall size_t j; j < i ==> \wrapped(&container->arr[j]))
			_(invariant \malloc_root((MyObject[container->size])container->arr))
		{
			_(wrap container->arr+i)
		}
	)

	_(wrap container)
}

void freeinnerobjectarray2(MyObjectArrayContainer* container)
	_(requires \malloc_root((MyObject[container->size])container->arr))
	_(requires \extent_mutable((MyObject[container->size])container->arr))
	_(writes \extent((MyObject[container->size])container->arr))
	_(requires \thread_local(container))
{
	freeobjectarray2(container->arr, container->size);
}

void freeobjectarray2(MyObject* arr, size_t size)
	_(requires \malloc_root((MyObject[size])arr) )
	_(requires \extent_mutable((MyObject[size])arr) )
	_(writes \extent((MyObject[size])arr))
{
	free(_(MyObject[size])arr);
}

void cleanup2(MyObjectArrayContainer* container)
	_(requires \wrapped(container))
	_(writes container)
	_(ensures \extent_mutable(container))

	_(requires container->size > 0)
{
	_(unwrap container)
	
	_(unwrap (MyObject[container->size])container->arr)

	//What can I do here?

	//error VC8510: Assertion '\extent((MyObject[container->size])container->arr) is writable in call to freeinnerobjectarray2(container)' did not verify.
	freeinnerobjectarray2(container);
	//free(container->arr);
}

void test2()
{
	MyObjectArrayContainer cont;
	allocandwrap2(&cont);
	cleanup2(&cont);
}




void objectarraymallocandfree()
{
	MyObject* arr = malloc(sizeof(MyObject) * 10);
	_(assume arr != NULL)
	free(_(MyObject[10])arr);
}




#endif