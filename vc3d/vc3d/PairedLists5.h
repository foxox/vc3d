
//ATTEMPT TO GET ARRAYS TO WORK IN DESTRUCTORS

//Works with size==2 fixed.

#ifdef VERIFY
	#define speccast(_TYPE_, _EXPR_) ((_TYPE_)(_EXPR_))
#else
	#define speccast(_TYPE_, _EXPR_) (_EXPR_)
#endif

#include <vcc.h>
#include <stdlib.h>	//malloc

typedef struct Paired Paired;

typedef struct Paired
{
	int x;
	//_(invariant \approves(\this->\owner, pair))
} Paired;

typedef _(dynamic_owns) struct PairedLists
{
	//An array of Paired objects and its size
	Paired* test;
	size_t size;
	
	//DO NOT Restrict size in this file for the sake of testing
	//_(invariant size == 2)

	//_(invariant test != NULL)
	//Indicate that all Paired objects inthe array will be owned by this object
	_(invariant \forall \natural i; i < size ==> \mine(&test[i]))
	
	//Keep track of the array object encapsulating the array for the sake of destruction/disposal/free() later
	_(invariant \mine((Paired[size])test))
	_(invariant \malloc_root( (Paired[size])test ))
} PairedLists;


//Initialize a PairedLists object with internal size 2
void PairedListInit_2(PairedLists* dis)
	_(requires \extent_mutable(dis))
	_(writes \extent(dis))
	_(ensures \wrapped(dis))
	_(ensures \fresh(dis->test))
{
	//Initialize the \owns set. Needed because of _(dynamic_owns)
	_(ghost dis->\owns = {};)

	//Pick a size for the array; arbitrary
	dis->size = 2;

	//Allocate memory for the array
	dis->test = malloc(sizeof(Paired)*dis->size);
	_(assume dis->test != NULL)
	
	//Keep track of the array object for the sake of destruction/disposal/free() later
	_(ghost dis->\owns += (Paired[dis->size])dis->test;)
	_(wrap (Paired[dis->size])dis->test;)

	//Each array item is its own object which needs to be wrapped and added to \owns
	_(ghost dis->\owns += &dis->test[0];)
	_(ghost dis->\owns += &dis->test[1];)
	_(wrap &dis->test[0])
	_(wrap &dis->test[1])

	_(wrap dis)																								
}

//Dispose a PairedLists object with any internal size
void PairedListDispose_any(PairedLists* dis)
	_(requires \wrapped(dis))
	_(writes dis)
	_(ensures \extent_mutable(dis))
	//_(ensures dis->\owns == {})
	//_(ensures dis->test == NULL)
{
	_(ghost \object testarrob = (Paired[dis->size])dis->test)

	_(assert \forall \natural i; i < dis->size ==> &dis->test[i] \in dis->\owns )
	//_(assert \forall \object o; o \in \array_range(dis->test, dis->size) ==> o \in dis->\owns)

	//Unwrap the object so that its parts can be unwrapped/freed
	_(unwrap dis)
	_(assert \forall \natural j; j < dis->size ==> dis->test[j].\closed)

	//Hand-holding for the loop. Show that everything is wrapped before starting the loop.
	//_(assert \forall size_t j; j < dis->size ==> &dis->test[j] \in \array_range(dis->test, dis->size))
	//_(assert \forall \natural j; j < dis->size ==> \writable(&dis->test[j]))

	_(unwrap testarrob)

	////Loop over all objects in array, unwrapping them
	//for (size_t i = 0; i < dis->size; i++)
	//	/*_(invariant \thread_local(dis))
	//	_(invariant dis->size == \old(dis->size))
	//	_(invariant \forall \natural j; j < dis->size ==> \thread_local(&dis->test[j]))
	//	_(invariant \forall \natural j; j < dis->size ==> dis->test[j].\valid)

	//	_(invariant \forall size_t j; j < dis->size ==> &dis->test[j] \in dis->\owns)*/
	//	_(writes \extent(testarrob) )
	//	_(invariant \mutable(testarrob) )
	//	//_(writes \array_range(dis->test, dis->size))
	//{
	//	//Hand-holding for the array item unwrap in this loop
	//	//_(assert i < dis->size)
	//	//_(assert \thread_local(&dis->test[i]))
	//	//_(assert dis->test[i].\valid)

	//	//_(assert &dis->test[i] \in dis->\owns)

	//	//_(assert \wrapped(&dis->test[i]))
	//	//_(assume \writable(&dis->test[i]))

	//	//Make all parts (\extent) of the array writable, one by one
	//	_(unwrap &dis->test[i])
	//}

	//The free(p) below requires that \extent(p) is writeable. This establishes that.
	//_(assert \forall size_t j; j < dis->size ==> \writable(&dis->test[j]))
	//_(assert \mutable_array(dis->test, dis->size))

	//Make arrayobject writeable. This shows VCC that the free() below is okay
	//_(unwrap (Paired[dis->size])dis->test)

	free(speccast(Paired[dis->size], dis->test));

	_(ghost dis->\owns = {};)
	dis->test = NULL;
}

void FunctionTester()
{
	PairedLists init_me;
	_(assert \extent_mutable(&init_me))
	
	PairedListInit_2(&init_me);
	//_(assert \wrapped(&init_me))
	PairedListDispose_any(&init_me);
	//_(assert !\wrapped(&init_me))

	_(assert \extent_mutable(&init_me))
}





typedef struct MyObject
{
	int x;
	_(invariant x > 0)
} MyObject;

void MallocArrayTest()
{
	//Works okay
	//int* heaparr = (int*)malloc(2 * sizeof(int));
	//if (heaparr != NULL)
	//	free(_(int[2])heaparr);

	//Fails... why?
	//int* heaparr2 = (int*)malloc(1 * sizeof(int));
	//if (heaparr2 != NULL)
	//	free(_(int[1])heaparr2);
	//	//Assertion '_(int[1])heaparr2 is writable in call to free(_(int[1])heaparr2)' did not verify.

	//Works okay
	//unsigned int size = 1;
	//int* heaparr3 = (int*)malloc(size * sizeof(int));
	//if (heaparr3 != NULL)
	//	free(_(int[size])heaparr3);

	//???
	//int* heapvar = (int*)malloc(sizeof(int));
	//if (heapvar != NULL)
	//	free(heapvar);
	//	//Assertion '\extent(p) is writable in call to free(heapvar)' did not verify.

	
	const size_t arrsize = 1;
	size_t i = 1;

	//MyObject arr[arrsize];
	MyObject* arr = malloc(sizeof(MyObject) * arrsize);

	if (arr != NULL)
	{
		_(ghost \object arrob = (MyObject[arrsize])arr)
		_(assert \malloc_root(arr) )
		_(assert \writable(arrob) )
		//_(wrap arrob)
		//_(unwrap arrob)

		//for (i = 0; i < arrsize; i++)
		//{
			//_(ghost arr[i].\owner = \me)
		//}

		//_(assert \forall size_t j; j < arrsize ==> \thread_local(&arr[j]))
		//_(assert \forall size_t j; j < arrsize ==> arr[j].\owner == \me)
		//
		//_(assert arr \in \array_range(arr,arrsize) )
		//_(assert \forall size_t j; j < arrsize ==> arr+j \in \array_range(arr,arrsize) )
		//_(assert \forall size_t j; j < arrsize ==> &arr[j] \in \array_range(arr,arrsize) )
		
		//_(requires \full_context())
		////_(requires \forall size_t i; i < arrsize ==> \mutable(&arr[i]) )
		//_(writes \array_range(arr,arrsize))
		//_(ensures \forall size_t j; j < arrsize ==> \wrapped(&arr[j]) )
		//_(ensures \forall size_t j; j < arrsize ==> \writable(&arr[j]) )
		////_(ensures \forall size_t j; arr+j \in \array_range(arr,arrsize) ==> \writable(arr+j))
		//{
			for(i = 0; i < arrsize; i++)
				//_(invariant \writable(arrob) )
				_(writes \array_range(arr,arrsize))
				_(invariant \forall size_t j; j >= i && j < arrsize ==> \mutable(&arr[j]))	//for wrap
				_(invariant \forall size_t j; j < i ==> \wrapped(&arr[j])) //for wrap
			{
				arr[i].x = 3;
			
				_(wrap &arr[i])
			}
		//}

		_(assert \forall size_t j; j < arrsize ==> \wrapped(&arr[j]))
		_(assert \forall size_t j; j < arrsize ==> arr[j].\valid)
		_(assert \forall size_t j; j < arrsize ==> \thread_local(&arr[j]))
		_(assert \forall size_t j; j < arrsize ==> arr[j].\owner == \me)

		_(assert \forall size_t j; arr+j \in \array_range(arr,arrsize) ==> \writable(arr+j))
		_(assert \forall size_t j; j < arrsize ==> \writable(&arr[j]))

		//_(requires \full_context())
		////_(requires \forall size_t j; j < arrsize ==> \wrapped(&arr[j]))
		//_(ensures \forall size_t j; j < arrsize ==> \mutable(&arr[j]))
		//_(ensures \mutable_array(arr,arrsize))
		//_(writes \array_range(arr,arrsize))
		//{
			//_(assert \forall size_t j; arr+j \in \array_range(arr,arrsize) ==> \writable(arr+j))

			for(i = 0; i < arrsize; i++)
				//_(invariant \writable(arrob) )
				//_(writes \extent(arrob) )
				//_(writes \array_range(arr,arrsize))
			
				//_(invariant \forall size_t j; arr+j \in \array_range(arr,arrsize) ==> \writable(arr+j))
				_(invariant \forall size_t j; j < arrsize ==> \writable(&arr[j]))

				_(invariant \forall size_t j; j < i ==> \mutable(&arr[j]))
				_(invariant \forall size_t j; j >= i && j < arrsize ==> \wrapped(&arr[j]))
			{
				_(unwrap &arr[i])
			}
		//}

		_(assert \forall size_t j; j < arrsize ==> \mutable(&arr[j]))
		_(assert \forall size_t j; j < arrsize ==> \mutable(arr+j) )
		//_(assert \mutable_array(arr,arrsize))
		free(_(MyObject[arrsize])arr);
	}
}

void ExtraSimpleArrayTest()
{
	const size_t arrsize = 1;
	size_t i = 1;

	//MyObject arr[arrsize];
	MyObject* arr = malloc(sizeof(MyObject) * arrsize);
	_(assume arr != NULL)
	_(ghost \object arrob = (MyObject[arrsize])arr)
	_(assert \malloc_root(arr) )
	_(assert \writable(arrob) )
	free(_(MyObject[arrsize])arr);
}

void get(int a[])
  _(writes \array_range(a, 3))
{
  a[0] = 1;
  a[1] = 2;
  a[2] = 3;
}

void looper1()
{
  int b[3];
  int i;
  for (i = 0; i < 100; ++i)
    _(invariant \mutable(\embedding(&b[0])))
    _(writes \extent(\embedding(&b[0])))
  {
    get(b);
  }
}

void looper2()
{
  int b[3];
  int i;
  for (i = 0; i < 100; ++i)
    _(writes \array_range(b, 3))
  {
    get(b);
  }
}

void looper3()
{
  /*_(as_array) */int b[3];
  int i;
  for (i = 0; i < 100; ++i)
    _(invariant \mutable( (int[3]) b))
    _(writes \extent( (int[3]) b))
  {
    get(b);
  }
}
