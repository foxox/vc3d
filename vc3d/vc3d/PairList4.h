
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
	//Restrict size in this file for the sake of testing
	_(invariant size == 2)

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

//Dispose a PairedLists object with internal size 2
void PairedListDispose_2(PairedLists* dis)
	_(requires \wrapped(dis))
	_(writes dis)
	_(ensures \extent_mutable(dis))
	_(ensures dis->\owns == {})
	_(ensures dis->test == NULL)
{
	//_(assert \forall \natural i; i < dis->size ==> &dis->test[i] \in dis->\owns )


	//Unwrap the object so that its parts can be unwrapped/freed
	_(unwrap dis)

	////Hand-holding for the array item unwraps
	//_(assert 0 < dis->size)
	//_(assert 1 < dis->size)
	//_(assert \wrapped(&dis->test[0]))
	//_(assert \wrapped(&dis->test[1]))

	////Make all parts (\extent) of the array writable
	//_(unwrap &dis->test[0])
	//_(unwrap &dis->test[1])

	//test; see above

	_(assert &dis->test[0] \in dis->\owns)
	//_(assert 0 < dis->size)
	_(assert \wrapped(&dis->test[0]))
	_(unwrap &dis->test[0])

	_(assert &dis->test[1] \in dis->\owns)
	//_(assert 1 < dis->size)
	_(assert \wrapped(&dis->test[1]))
	_(unwrap &dis->test[1])

	//Make arrayobject writeable. This shows VCC that the free() below is okay
	_(unwrap (Paired[dis->size])dis->test)

	free((void*) speccast(Paired[dis->size], dis->test));

	_(ghost dis->\owns = {};)
	dis->test = NULL;
}

void FunctionTester()
{
	PairedLists init_me;
	PairedListInit_2(&init_me);
	//_(assert \wrapped(&init_me))
	PairedListDispose_2(&init_me);
	//_(assert !\wrapped(&init_me))
}
