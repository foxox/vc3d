#include <vcc.h>
//#include <stdlib.h>
#include <stdlib.h>

typedef struct MyObject
{
	int field;
} MyObject;

typedef _(dynamic_owns) struct VarList
{
	size_t size;
	size_t used;
	MyObject* objects;

	//_(invariant size > 0)
	_(invariant used <= size)

	_(invariant \forall size_t i; {objects+i} i < size ==> \mine(objects+i))

	//Problem in increaseUsedByTwo function! Without this, assertions needed for dis->objects+dis->used+1
	_(invariant \forall size_t i; \forall size_t j; {objects+i+j} (i+j) < size ==> \mine(objects+i+j))

	_(invariant \forall size_t i; i < used ==> objects[i].field == 3)
} VarList;

void test()
{
	MyObject* aoeu;
	aoeu = malloc(sizeof(MyObject) * 10);
	_(assume aoeu != NULL)

	size_t j = 0;
	for (j = 0; j < 5; j++)
		_(writes \array_range(aoeu, 10))
		_(invariant \forall size_t k; k < j ==> aoeu[k].field == 3)
	{
		aoeu[j].field = 3;
	}

	_(assert \forall size_t i; i < 5 ==> aoeu[i].field == 3)
}

void initList(VarList* dis, size_t newsize, size_t newused)
	_(ensures \wrapped(dis))
	_(writes \extent(dis))
	_(requires newused <= newsize)
	_(requires newsize > 0)
{
	//Set up owns list
	_(ghost dis->\owns = {};)

	//Set list size
	dis->size = newsize;
	dis->used = newused;

	//Allocate memory for list elements
	dis->objects = malloc(sizeof(MyObject) * newsize);
	_(assume dis->objects != NULL)

	//List elements:

	//Set them up
	size_t j = 0;
	for (j = 0; j < dis->used; j++)
		_(writes \array_range(dis->objects, dis->used))
		_(invariant \forall size_t k; k < dis->used ==> \mutable(dis->objects+k))
		//_(invariant \mutable(dis->objects+j) )
		_(invariant \forall size_t k; k < j ==> dis->objects[k].field == 3)
	{
		dis->objects[j].field = 3;
	}

	//wrap them
	_(ghost size_t i;)
	_(ghost
		for(i = 0; i < dis->size; i++)
			_(writes \array_members(dis->objects, dis->size))
			_(invariant \forall size_t j; j >= i && j < dis->size ==> \mutable(dis->objects+j))
			_(invariant \forall size_t j; j < i ==> \wrapped(dis->objects+j))
			_(invariant \forall size_t j; j < dis->used ==> dis->objects[j].field == 3)
		{
			_(wrap dis->objects+i)
		}
	)
	//add them to owns list
	_(ghost dis->\owns = \array_members(dis->objects, dis->size))

	_(wrap dis)
}

void increaseUsedByTwo(VarList* dis)
	_(requires dis->size - dis->used >= 2)
	_(updates dis) 
	_(ensures dis->used == \old(dis->used)+2)
{
	//This needed without extra invariant
	//_(assert dis->objects+dis->used+1 \in dis->\owns)

	//Work-around:
	//_(assert dis->objects+(dis->used+1) \in dis->\owns)

	//Or simply:
	//_(assert &dis->objects[dis->used+1] \in dis->\owns)

	_(unwrapping dis)
	{
		_(unwrapping dis->objects+dis->used+0)
		{
			dis->objects[dis->used+0].field = 3;
		}
		_(unwrapping dis->objects+dis->used+1)
		{
			dis->objects[dis->used+1].field = 3;
		}
		dis->used += 2;
	}
}