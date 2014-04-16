
#include <vcc.h>
#include <stdlib.h>	//malloc

#ifdef VERIFY
	#define speccast(_TYPE_, _EXPR_) ((_TYPE_)(_EXPR_))
#else
	#define speccast(_TYPE_, _EXPR_) (_EXPR_)
#endif

typedef struct MyObject
{
	int field;
} MyObject;


//SINGLE OBJECT NON-ARRAY TESTS

void MyObjectInit(MyObject** test)
	_(writes test)
	_(ensures \wrapped(*test) )
	_(ensures \fresh(*test) )
	_(ensures \malloc_root(*test))
{
	(*test) = malloc(sizeof(MyObject));
	_(assume *test != NULL)
	
	_(wrap *test)
}

void MyObjectDisposeWrapped(MyObject** test)
	_(requires \malloc_root( (*test) ) )
	_(requires \wrapped( (*test) ) )
	_(writes (*test) )
	_(writes test)
{
	_(unwrap (*test) )

	free( (MyObject*)(*test) );
}

void TestIndividualObjectMalloc()
{
	MyObject* someobj;

	MyObjectInit(&someobj);
	MyObjectDisposeWrapped(&someobj);
}

//ARRAY OF OBJECTS TEST

//Initialize a MyObject array with size 2
void MyObjectArrayInit_2(MyObject** test)
	_(writes test)
	_(ensures \malloc_root((MyObject[2])(*test)) )	_(writes test)
	_(ensures \fresh((MyObject[2])(*test)) )
	_(ensures \forall size_t i; i < 2 ==> \fresh(&(*test)[i]) )
	_(ensures \forall size_t i; i < 2 ==> \wrapped(&(*test)[i]) )
	_(ensures \wrapped((MyObject[2])(*test)) )

	_(ensures \thread_local_array(*test,2) )
{
	//Allocate memory for the array
	(*test) = malloc(sizeof(MyObject)*2);
	_(assume *test != NULL)
	
	//Keep track of the array object for the sake of destruction/disposal/free() later
	_(wrap (MyObject[2])(*test))

	//Each array item is its own object which needs to be wrapped
	_(wrap &(*test)[0])
	_(wrap &(*test)[1])
}

//Dispose a MyObject array with size 2
void MyObjectArrayDispose_2(MyObject** test)
	_(requires \forall size_t i; i < 2 ==> \wrapped(&(*test)[i]) )	//conflicts with writes arrayrange
	_(requires \wrapped((MyObject[2])(*test)) )
	_(requires \malloc_root((MyObject[2])(*test)) )
	_(writes (MyObject[2])(*test) )
	_(writes test)
	_(writes \array_members(*test,2))
{
	_(unwrap *test+0)
	_(unwrap &(*test)[1])

	//Make arrayobject writable. This shows VCC that the free() below is okay
	_(unwrap (MyObject[2])(*test) )

	_(assert \forall size_t i; i < 2 ==> \writable(&(*test)[i]))

	free((void*) speccast(MyObject[2], (*test)));
}

void TestObjectArrayMalloc()
{
	MyObject* test;	//pointer to array start in the heap

	MyObjectArrayInit_2(&test);	//allocated and initialized here
	
	_(assert \forall size_t i; i < 2 ==> \wrapped(&test[i]) )
	_(assert \forall size_t i; i < 2 ==> test[i].\valid )
	_(assert \forall size_t i; i < 2 ==> test[i].\closed )
	_(assert \forall size_t i; i < 2 ==> test[i].\owner == \me )
	_(assert \forall size_t i; i < 2 ==> \writable(&test[i]) )
	_(assert \forall size_t i; i < 2 ==> \thread_local(&test[i]) )
	_(assert \thread_local_array(test,2) )

	MyObjectArrayDispose_2(&test);
}




//OBJECT HOLDING ARRAY OF OBJECTS

typedef _(dynamic_owns) struct MyObjectArrayContainer
{
	MyObject* arr;
	size_t size;
	_(ghost \object arrob)
	_(invariant size == 2)
	_(invariant arrob == (MyObject[size])arr)
	_(invariant \malloc_root(arrob))
	_(invariant \mine(arrob))
	_(invariant \forall size_t i; i < size ==> \mine(arr+i))
} MyObjectArrayContainer;







//Initialize a MyObject array with size 2
void MyObjectArrayContainerInit_2(MyObjectArrayContainer* container)
	_(writes \extent(container))
	_(ensures \wrapped(container))
	_(ensures container->size == 2)
{
	//Allocate memory for the array
	container->arr = malloc(sizeof(MyObject)*2);
	container->size = 2;
	_(assume container->arr != NULL)

	_(ghost container->\owns = {})
	
	//Keep track of the array object for the sake of destruction/disposal/free() later
	_(ghost container->arrob = (MyObject[container->size])container->arr )
	_(wrap container->arrob)
	_(ghost container->\owns += container->arrob)

	//Each array item is its own object which needs to be wrapped
	_(wrap &container->arr[0])
	_(wrap &container->arr[1])

	_(ghost container->\owns += &container->arr[0])
	_(ghost container->\owns += &container->arr[1])

	_(wrap container)
}

//Dispose a MyObject array with size 2
void MyObjectArrayContainerDispose_2(MyObjectArrayContainer* container)
	_(writes container)
	_(requires \wrapped(container))
	_(ensures \extent_mutable(container))
	_(requires container->size == 2)
{
	_(unwrap container)
	_(unwrap &container->arr[0])

	_(assert &container->arr[1] \in container->\owns)
	_(assert \wrapped(&container->arr[1]))
	_(unwrap &container->arr[1])

	//Make arrayobject writable. This shows VCC that the free() below is okay
	_(unwrap container->arrob )

	free((void*) speccast(MyObject[2], container->arr));
}

void TestObjectContainingObjectArrayMalloc()
{
	MyObjectArrayContainer container;
	MyObjectArrayContainerInit_2(&container);
	_(assert \wrapped(&container))
	MyObjectArrayContainerDispose_2(&container);
}














//Initialize a MyObject array with variable size
void MyObjectArrayContainerInit(MyObjectArrayContainer* container, size_t _size)
	_(decreases 0)
	_(writes \extent(container))
	_(ensures \wrapped(container))
	_(requires _size==2)
	_(ensures container->size == _size)
{
	_(ghost container->\owns = {})

	container->size = _size;
	container->arr = malloc(container->size * sizeof(MyObject));
	_(assume container->arr != NULL)

	_(ghost container->\owns = container->\owns \union \array_members(container->arr,container->size) )

	//Keep track of the array object for the sake of destruction/disposal/free() later
	_(ghost container->arrob = (MyObject[container->size])container->arr )
	_(ghost container->\owns += container->arrob)
	_(wrap container->arrob)

	_(ghost size_t i)
	_(ghost
		for (i = 0; i < container->size; i++)
			_(decreases container->size-i)
			_(writes \array_members(container->arr,container->size))
			_(invariant \forall size_t j; j >= i && j < container->size ==> \mutable(&container->arr[j]))
			_(invariant \forall size_t j; j < i ==> \wrapped(&container->arr[j]))
			_(invariant container->size == _size)
		{
			_(wrap container->arr+i)
			//_(assert \false)
		}
	)

	_(wrap container)
}

//Dispose a MyObject array with variable size
void MyObjectArrayContainerDispose(MyObjectArrayContainer* container, size_t size)
	_(writes container)
	_(requires \wrapped(container))
	_(ensures \extent_mutable(container))
	_(requires container->size == 2)
{
	_(unwrap container)

	//_(assert &container->arr[0] \in container->\owns)
	//_(assert \wrapped(&container->arr[0]))
	_(unwrap &container->arr[0])

	_(assert &container->arr[1] \in container->\owns)
	_(assert \wrapped(&container->arr[1]))
	_(unwrap &container->arr[1])

	//Make arrayobject writable. This shows VCC that the free() below is okay
	_(unwrap container->arrob )

	free((void*) speccast(MyObject[container->size], container->arr));
}

void TestObjectContainingObjectArrayMalloc_VariableSize()
{
	MyObjectArrayContainer container;
	size_t size = 2;

	MyObjectArrayContainerInit(&container, size);

	_(assert \wrapped(&container))
	_(assert &container.arr \in \extent(&container))
	//_(assert &container.arr[0] \in \extent(&container)) //false
	
	MyObjectArrayContainerDispose(&container, size);
}
