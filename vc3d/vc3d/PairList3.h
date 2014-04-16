
//WORKING CONSTRUCTOR/DESTRUCTOR FOR A POINTER FIELD

#ifdef VERIFY
	#define speccast(_TYPE_, _EXPR_) ((_TYPE_)(_EXPR_))
#else
	#define speccast(_TYPE_, _EXPR_) (_EXPR_)
#endif

#include <vcc.h>
#include <stdlib.h>	//malloc
//typedef unsigned int size_t;

typedef struct Paired Paired;

typedef struct Paired
{
	int x;
	//_(invariant \approves(\this->\owner, pair))
} Paired;

typedef _(dynamic_owns) struct PairedLists
{
	Paired* test;

	_(invariant test != NULL)
	_(invariant \mine(test))// && test \in \domain(\this))
	_(invariant \malloc_root(test))
} PairedLists;


void PairedListInit(PairedLists* dis)
	_(requires \extent_mutable(dis))
	_(writes \extent(dis))
	_(ensures \wrapped(dis))
	_(ensures \fresh(dis->test))
{
	_(ghost dis->\owns = {};)

	dis->test = malloc(sizeof(Paired));
	_(assume dis->test != NULL)
	
	_(ghost dis->\owns += dis->test;)

	_(wrap dis->test;)

	_(wrap dis)																								
}

void PairedListDispose(PairedLists* dis)
	//_(requires \thread_local(dis))
	_(requires \wrapped(dis))
	_(writes dis)
	_(ensures \extent_mutable(dis))
	_(ensures dis->\owns == {})
	_(ensures dis->test == NULL)
	//_(decreases 0)
{
	_(unwrap dis)
	_(assert \thread_local(dis))

	_(assert \malloc_root(dis->test))

	_(unwrap dis->test)

	free((void*) dis->test);

	_(ghost dis->\owns = {};)
	dis->test = NULL;
}

void FunctionTester()
{
	PairedLists init_me;
	PairedListInit(&init_me);
	//_(assert \wrapped(&init_me))
	PairedListDispose(&init_me);
	//_(assert !\wrapped(&init_me))
}
