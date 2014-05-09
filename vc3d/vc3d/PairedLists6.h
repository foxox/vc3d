
//ATTEMPT TO GET ARRAYS TO WORK IN DESTRUCTORS

//Works with size==2 fixed.

#include <vcc.h>
#include <cstdlib>	//malloc

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

	//_(writes &(*test)[0])
	//_(writes &(*test)[1])
	//Use this instead:
	_(writes \array_members(*test,2))
{
	//_(writes \array_members(*test,2))
	
	//_(writes *test+0, *test+1)
	//_(requires \full_context())
	//{
	_(unwrap *test+0)
	_(unwrap &(*test)[1])
	//}

	//Make arrayobject writable. This shows VCC that the free() below is okay
	_(unwrap (MyObject[2])(*test) )

	_(assert \forall size_t i; i < 2 ==> \writable(&(*test)[i]))

	free((void*) speccast(MyObject[2], (*test)));

	//_(assert \false)
}

void TestObjectArrayMalloc()
{
	MyObject* test;	//pointer to array start in the heap

	MyObjectArrayInit_2(&test);	//allocated and initialized here
	//test should be a valid and wrapped array of objects
	
	//_(assert \forall size_t i; i < 2 ==> \wrapped(&test[i]) )
	//_(assert \forall size_t i; i < 2 ==> test[i].\valid )
	//_(assert \forall size_t i; i < 2 ==> test[i].\closed )
	//_(assert \forall size_t i; i < 2 ==> test[i].\owner == \me )
	//_(assert \forall size_t i; i < 2 ==> \writable(&test[i]) )
	//_(assert \forall size_t i; i < 2 ==> \thread_local(&test[i]) )
	//_(assert \thread_local_array(test,2) )

	MyObjectArrayDispose_2(&test);
}

////Dispose a MyObject array with size 2
//void MyObjectArrayDispose_2_PART1(MyObject** test)
//	_(requires \forall size_t i; i < 2 ==> \wrapped(&(*test)[i]) )
//	_(requires \wrapped((MyObject[2])(*test)) )
//	_(maintains \malloc_root((MyObject[2])(*test)) )
//	_(writes test)
//	_(writes \array_members(*test,2))
//
//	//_(ensures \forall size_t i; i < 2 ==> \fresh(&(*test)[i]) )
//	//_(ensures \extent_fresh(*test))
//	_(writes (MyObject[2])(*test))
//{
//	_(unwrap *test+0)
//	_(unwrap &(*test)[1])
//	//_(assert \false)
//
//	_(unwrap (MyObject[2])(*test) )
//}
//
////Dispose a MyObject array with size 2
//void MyObjectArrayDispose_2_PART2(MyObject** test)
//	//_(requires \wrapped((MyObject[2])(*test)) )
//	_(requires \malloc_root((MyObject[2])(*test)) )
//
//	_(writes test)
//	//_(writes *test)
//	_(writes \extent(*test))
//	//_(requires \malloc_root(*test))
//	//_(writes \array_members(*test,2))
//	_(writes (MyObject[2])(*test) )
//	_(writes \extent( (MyObject[2])(*test)) )
//{
//	//Make arrayobject writable. This shows VCC that the free() below is okay
//	//_(unwrap (MyObject[2])(*test) )
//
//	//_(assert \forall size_t i; i < 2 ==> \writable(&(*test)[i]))
//
//	free((MyObject[2])(*test));
//	//free((void*) speccast(MyObject[2], (*test)));
//
//	//_(assert \false)
//}
//
//void TestObjectArrayMalloc_2PARTDISPOSE()
//{
//	MyObject* test;	//pointer to array start in the heap
//
//	MyObjectArrayInit_2(&test);	//allocated and initialized here
//	//test should be a valid and wrapped array of objects
//	MyObjectArrayDispose_2_PART1(&test);
//	MyObjectArrayDispose_2_PART2(&test);
//}


//...variable sized arrays next









////VARIABLE SIZE OBJECT ARRAY - TEST ONLY SWAPPING OUT ALL 2S FOR SIZE
//
////Initialize a MyObject array with size 2
//void MyObjectArrayInit_2_ALT(MyObject** test, size_t size)
//	_(requires size==2)
//	_(writes test)
//	_(ensures \malloc_root((MyObject[size])(*test)) )	_(writes test)
//	_(ensures \fresh((MyObject[size])(*test)) )
//	_(ensures \forall size_t i; i < size ==> \fresh(&(*test)[i]) )
//	_(ensures \forall size_t i; i < size ==> \wrapped(&(*test)[i]) )
//	_(ensures \wrapped((MyObject[size])(*test)) )
//{
//	//Allocate memory for the array
//	(*test) = malloc(sizeof(MyObject)*size);
//	_(assume *test != NULL)
//	
//	//Keep track of the array object for the sake of destruction/disposal/free() later
//	_(wrap (MyObject[size])(*test))
//
//	//Each array item is its own object which needs to be wrapped
//	_(wrap &(*test)[0])
//	_(wrap &(*test)[1])
//}
//
////Dispose a MyObject array with size 2
//void MyObjectArrayDispose_2_ALT(MyObject** test, size_t size)
//	_(requires size==2)
//	_(requires \forall size_t i; i < size ==> \wrapped(&(*test)[i]) )	//conflicts with writes arrayrange
//	_(requires \wrapped((MyObject[size])(*test)) )
//	_(requires \malloc_root((MyObject[size])(*test)) )
//	_(writes (MyObject[size])(*test) )
//	_(writes test)
//	_(writes \array_members(*test,size))
//{
//	//These alone are fine.
//	//_(unwrap *test+0)
//	//_(unwrap &(*test)[1])
//
//	//How can I replace those two unwraps with a loop to do the same? (or otherwise unwrap multiple parts of the array on once)
//	size_t i;
//	for (i = 0; i < size; i++)
//		_(invariant \forall size_t j; j < i ==> \mutable(&(*test)[j]))
//		_(invariant \forall size_t j; j >= i && j < size ==> \wrapped(&(*test)[j]))
//		_(writes \array_members(*test,size)) //BAD, throws off the fact that \extent((MyObject[size])(*test)) is writable, needed by free
//		_(writes (MyObject[size])(*test) )
//		//_(writes test)
//		_(invariant \wrapped((MyObject[size])(*test)) )
//	{
//		_(unwrap *test+i)
//	}
//
//
//	//Make arrayobject writable. This shows VCC that the free() below is okay
//	_(unwrap (MyObject[size])(*test) )
//
//	_(assert \forall size_t i; i < size ==> \writable(&(*test)[i]))
//
//	//free((void*) speccast(MyObject[size], (*test)));
//	free( (MyObject[size])(*test) );
//
//	//_(assert \false)
//}
//
//void TestObjectArrayMalloc_ALT()
//{
//	MyObject* test;	//pointer to array start in the heap
//
//	MyObjectArrayInit_2_ALT(&test, 2);	//allocated and initialized here
//	//test should be a valid and wrapped array of objects
//	
//	_(assert \forall size_t i; i < 2 ==> \wrapped(&test[i]) )
//	_(assert \forall size_t i; i < 2 ==> test[i].\valid )
//	_(assert \forall size_t i; i < 2 ==> test[i].\closed )
//	_(assert \forall size_t i; i < 2 ==> test[i].\owner == \me )
//	_(assert \forall size_t i; i < 2 ==> \writable(&test[i]) )
//	_(assert \forall size_t i; i < 2 ==> \thread_local(&test[i]) )
//
//	MyObjectArrayDispose_2_ALT(&test, 2);
//}













////ARRAY OF OBJECTS TEST - VARIABLE SIZE
//
////Initialize a MyObject array with size size
//void MyObjectArrayInit(MyObject** test, size_t size)
//	_(decreases 0)
//	_(writes test)
//	//Array
//	_(ensures \forall size_t i; i < size ==> \fresh(&(*test)[i]) )
//	_(ensures \forall size_t i; i < size ==> \wrapped(&(*test)[i]) )
//	//ArrayObject
//	_(ensures \malloc_root((MyObject[size])(*test)) )
//	_(ensures \fresh( (MyObject[size])(*test)) )
//	_(ensures \extent_fresh( (MyObject[size])(*test)) )
//	_(ensures \wrapped((MyObject[size])(*test)) )
//{
//	//Allocate memory for the array
//	(*test) = malloc(sizeof(MyObject)*size);
//	_(assume *test != NULL)
//	
//	//Keep track of the array object for the sake of destruction/disposal/free() later
//	_(wrap (MyObject[size])(*test))
//
//	//Each array item is its own object which needs to be wrapped
//	_(ghost size_t i)
//	_(ghost
//		for (i = 0; i < size; i++)
//			_(decreases size-i)
//			_(writes \array_members(*test,size))
//			_(invariant \forall size_t j; j < i ==> \wrapped(&(*test)[j]))
//			_(invariant \forall size_t j; j >= i && j < size ==> \mutable(&(*test)[j]))
//		{
//			_(wrap &(*test)[i])
//		}
//	)
//}
//
////Dispose a MyObject array with size size
//void MyObjectArrayDispose(MyObject** test, size_t size)
//	_(decreases 0)
//	_(writes test)
//	//Array
//	_(writes \array_members(*test,size))
//	_(requires \forall size_t i; i < size ==> \wrapped(&(*test)[i]) )
//	//ArrayObject
//	_(writes (MyObject[size])(*test) )
//	//_(requires \wrapped((MyObject[size])(*test)) )
//	_(requires \malloc_root((MyObject[size])(*test)) )
//{
//	_(ghost size_t i)
//	_(ghost
//		for (i = 0; i < size; i++)
//			_(decreases size-i)
//			_(writes \array_members(*test,size))
//			_(invariant \forall size_t j; j < i ==> \mutable(&(*test)[j]))
//			_(invariant \forall size_t j; j >= i && j < size ==> \wrapped(&(*test)[j]))
//		{
//			_(unwrap &(*test)[i])
//		}
//	)
//
//	//Make arrayobject mutable. This shows VCC that the free() below is okay
//	//_(unwrap (MyObject[size])(*test) )
//
//	//_(assert \false)
//	_(assert \forall size_t i; i < size ==> \mutable(&(*test)[i]))
//	_(assert \forall size_t i; i < size ==> \extent_mutable(&(*test)[i]))
//	//_(assert \mutable((MyObject[size])(*test)))
//	//_(assert \extent_mutable((MyObject[size])(*test)))
//
//	//free(speccast(MyObject[size], (*test)));
//	free((MyObject[size])(*test));
//}
//
//void TestObjectArrayVariableSizeMalloc()
//{
//	MyObject* test;	//pointer to array start in the heap
//
//	MyObjectArrayInit(&test, 2);	//allocated and initialized here
//	_(assert \extent_fresh( (MyObject[2])test ))
//	MyObjectArrayDispose(&test, 2);	//unwrapped and freed here
//}










//void quicktest(MyObject* myobj)
//	_(writes \array_range(myobj,1) )
//	_(requires \wrapped(myobj))
//{
//	_(assert \false)
//	_(unwrap myobj)
//}

//typedef struct A {
//  int x;
//} A;
//
//void bar(A *p)
//  _(writes \extent(p))
//  _(maintains \mutable(p));
//
//void foo(A*p)
//  //_(maintains \mutable_array(p,5))
//  //_(writes \array_range(p,5))
//  _(writes (A[5])p )
//  _(requires \wrapped( (A[5])p ) )
//  _(requires \wrapped(&p[0]))
//{
//	//_(assert \false)
//	_(unwrap (A[5])p )
//	_(unwrap &p[0])
//		//p[0].x = 3;
//
//  //bar(p+1);
//}


//void WriteIntArray(int* vals, size_t size)
//	_(requires size > 0)
//	_(writes \array_range(vals,size))
//{
//	_(assert \false)	//Fails here, like it should
//	vals[0] = 3;
//}
//
//void WriteSingleStruct(MyObject* obj)
//	_(requires \wrapped(obj))
//	_(writes obj)
//{
//	_(assert \false)	//Fails here, like it should
//	_(unwrap obj)
//	obj->field = 3;
//}
//
//void WriteStructArray1(MyObject* objarr, size_t size)
//	_(requires size > 0)
//	_(requires \forall size_t i; i < size ==> \wrapped(&objarr[i]))
//	_(writes &objarr[0])
//	//but what if I want all elements to be writable, no matter the size?
//{
//	_(assert \false)	//Fails here, like it should
//	_(unwrap &objarr[0])
//	objarr[0].field = 3;
//}
//
//void WriteStructArray2(MyObject* objarr, size_t size)
//	_(requires size > 0)
//	_(requires \forall size_t i; i < size ==> \wrapped(&objarr[i]))
//	_(writes \array_range(objarr,size))
//	//How can I make all elements writable? Is it even possible?
//{
//	//_(assert \false)	//NO FAILURE... means contract is inconsistent
//	_(unwrap &objarr[0])
//	objarr[0].field = 3;
//}
//
//void WriteStructArray2_fixed(MyObject* objarr, size_t size)
//    _(requires size > 0)
//    _(requires \forall size_t i; i < size ==> \wrapped(&objarr[i]))
//    _(writes \array_members(objarr,size))
//{
//    _(unwrap &objarr[0])
//    objarr[0].field = 3;
//}














//OBJECT HOLDING ARRAY OF OBJECTS

typedef _(dynamic_owns) struct
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
	//_(requires \forall size_t i; i < 2 ==> \wrapped(&(*test)[i]) )
	//_(requires \wrapped((MyObject[2])(*test)) )
	//_(requires \malloc_root((MyObject[2])(*test)) )
	//_(writes (MyObject[2])(*test) )
	//_(writes test)
	//_(writes &(*test)[0])
	//_(writes &(*test)[1])
	////Why can't I use this instead?
	//_(writes \array_range((*test),2))
	////What can I do to make this more flexible so I can have a variable size?
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

	//Keep track of the array object for the sake of destruction/disposal/free() later
	_(ghost container->arrob = (MyObject[container->size])container->arr )
	_(ghost container->\owns += container->arrob)
	_(wrap container->arrob)

	_(ghost container->\owns = container->\owns \union \array_members(container->arr,container->size) )
	
	_(ghost size_t i)
	//_(ghost \objset ownthese = {} )
	//_(ghost
	//for (i = 0; i < container->size; i++)
	//	_(decreases container->size-i)
	//	_(invariant \forall size_t j; j < container->size ==> \mutable(container->arr+j))
	//	_(invariant \mutable(container))
	//	_(invariant container->size == _size)
	//	_(writes ownthese)
	//{
	//	//_(ghost container->\owns += container->arr+i)
	//	ownthese += container->arr+i;
	//}
	//)
	//_(ghost container->\owns = container->\owns \union ownthese)

	//Old:
	//_(wrap container->arr+0)
	//_(wrap container->arr+1)

	//New:
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







//SCRAPS

//void TestObjectArrayMallocWithoutFunctions()
//{
//	MyObject* o;
//	MyObject** test = &o;
//	//INITIALIZE
//		//Allocate memory for the array
//		(*test) = malloc(sizeof(MyObject)*2);
//		_(assume *test != NULL)
//	
//		//Keep track of the array object for the sake of destruction/disposal/free() later
//		_(wrap (MyObject[2])(*test))
//
//		//Each array item is its own object which needs to be wrapped
//		_(wrap &(*test)[0])
//		_(wrap &(*test)[1])
//
//	//DISPOSE
//		_(unwrap &(*test)[0])
//		_(unwrap &(*test)[1])
//
//		//Make arrayobject writable. This shows VCC that the free() below is okay
//		_(unwrap (MyObject[2])(*test) )
//
//		free((void*) speccast(MyObject[2], (*test)));
//}


//	MyObjectInit(&someobj);
//	_(unwrap someobj)
//	MyObjectDisposeMutable(&someobj);
//
//void MyObjectDisposeMutable(MyObject** test)
//	_(requires \malloc_root( (*test) ) )
//	_(requires \mutable( (*test) ) )
//	_(writes \extent((*test)) )
//	_(writes test)
//{
//	free( (MyObject*)(*test) );
//}



//_(typedef \bool objmap[\object])
//_(ghost _(pure) \objset objmap_to_objset(objmap m))
//_(axiom \forall \object p; objmap m; {p \in objmap_to_objset(m)}
//  p \in objmap_to_objset(m) <==> m[p])
//
//_(logic \objset mapped_range(\object arr, \integer sz, \objset arrayIdx[\integer]) =
//  objmap_to_objset(
//    \lambda \object p;
//      0 <= \index_within(p, arr) &&
//      \index_within(p, arr) < sz &&
//      p \in arrayIdx[\index_within(p, arr)]))
//
////_(writes mapped_range(t->Configurations, 10, \lambda \integer i; \full_extent(&t->Configurations[i].rw)))
////_(writes mapped_range(*test, 2, \lambda \integer i; \full_extent(&(*test)[i])))





//CHECKPOINT
	////ARRAY OF OBJECTS TEST - VARIABLE SIZE
	//
	////Initialize a MyObject array with size size
	//void MyObjectArrayInit(MyObject** test, size_t size)
	//	_(requires size==2)
	//
	//	_(writes test)
	//	//Array
	//	_(ensures \forall size_t i; i < size ==> \fresh(&(*test)[i]) )
	//	_(ensures \forall size_t i; i < size ==> \wrapped(&(*test)[i]) )
	//	//ArrayObject
	//	_(ensures \malloc_root((MyObject[size])(*test)) )
	//	_(ensures \fresh((MyObject[size])(*test)) )
	//	_(ensures \wrapped((MyObject[size])(*test)) )
	//{
	//	//Allocate memory for the array
	//	(*test) = malloc(sizeof(MyObject)*size);
	//	_(assume *test != NULL)
	//	
	//	//Keep track of the array object for the sake of destruction/disposal/free() later
	//	_(wrap (MyObject[size])(*test))
	//
	//	//Each array item is its own object which needs to be wrapped
	//	_(wrap &(*test)[0])
	//	_(wrap &(*test)[1])
	//}
	//
	////Dispose a MyObject array with size size
	//void MyObjectArrayDispose(MyObject** test, size_t size)
	//	_(requires size==2)
	//
	//	_(writes test)
	//	//Array
	//	_(writes \array_members(*test,size))
	//	_(requires \forall size_t i; i < size ==> \wrapped(&(*test)[i]) )
	//	//ArrayObject
	//	_(writes (MyObject[size])(*test) )
	//	_(requires \wrapped((MyObject[size])(*test)) )
	//	_(requires \malloc_root((MyObject[size])(*test)) )
	//{
	//	_(unwrap *test+0)
	//	_(unwrap &(*test)[1])
	//
	//	//Make arrayobject writable. This shows VCC that the free() below is okay
	//	_(unwrap (MyObject[size])(*test) )
	//
	//	free((void*) speccast(MyObject[size], (*test)));
	//}
	//
	//void TestObjectArrayVariableSizeMalloc()
	//{
	//	MyObject* test;	//pointer to array start in the heap
	//
	//	MyObjectArrayInit(&test, 2);	//allocated and initialized here
	//	//test should be a valid and wrapped array of objects
	//	MyObjectArrayDispose(&test, 2);
	//}