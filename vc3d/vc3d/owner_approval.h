#pragma once

#include <vcc.h>
//#include <stdlib.h>	//malloc
//#include <stddef.h> //size_t
//typedef unsigned long uint;
//typedef unsigned long size_t;

//typedef struct MyObject MyObject;

typedef struct MyObject
{
	//volatile
		size_t x;
	//_(invariant \approves(\this->\owner, x))
} MyObject;

typedef
//_(dynamic_owns)
struct SimpleObjectApprover
{
	_(inline)
	MyObject val;

	//_(invariant \mine(&val) )

	_(invariant val.x == 15)
} SimpleObjectApprover;

void SimpleApprovalTest(SimpleObjectApprover* approver)
	_(maintains \wrapped(approver))
	//_(writes \extent(approver))
	_(writes approver)
	//_(writes \extent(approver->val))
{
	_(unwrapping approver)
	{
		//_(unwrapping approver->val)
		{
			approver->val.x = 15;
		}
	}

	_(unwrapping approver)
	{
		approver->val.x = 15;
	}
}



typedef _(dynamic_owns) struct SimpleObjectApproverDO
{
	MyObject* val;
	size_t size;

	//_(invariant \on_unwrap(\this, \mine(val)) )

	_(invariant \mine(val))

	_(invariant val->x == 15)
} SimpleObjectApproverDO;

typedef _(dynamic_owns) struct ObjectPointerApprover
{
	MyObject** val;
	size_t size;

	_(invariant size == 2)

	_(invariant \mine((MyObject[size])val))
	
	_(invariant \forall size_t i; i < size ==> \mine(val[i]))
	
	_(invariant \forall size_t i, j; i < size && j < size && i != j ==> val[i] != val[j])

	//_(invariant \exists size_t i; i < size && val[i]->x == 15)

} ObjectPointerApprover;

typedef _(dynamic_owns) struct ObjectApprover
{
	MyObject* val;
	size_t size;

	_(invariant size == 2)

	_(invariant \mine((MyObject[size])val))
	_(invariant \forall size_t i; i < size ==> \mine(&val[i]))

	//_(invariant \forall \object o; o \in \array_range(val,size) ==> \mine(o) )
	//_(invariant \forall size_t i; \mine(&val[i]) && i < size ==> val[i].x > 10)




	//Ignore these for now and move on.
	//ADDITIONAL INVARIANTS 1
	//This doesn't work
		//_(invariant \forall size_t i; i < size ==> \mine(&val[i]) )
	//This doesn't work (forall objects in the \array_range of val, o is mine
		//_(invariant \forall \object o; o \in \array_range(val,size) ==> \mine(o) )
	//This also doesn't work (adding info that any object in the range has a corresponding index)
		//_(invariant \forall \object o; o \in \array_range(val,size) ==> (\mine(o) && \exists size_t i; i < size && o == &val[i]) )
	//This doesn't work. Forall objects o and size_ts i, if o == &val[i] and i is a valid index, then o is mine and o is in the array and &val[i] is mine.
		//_(invariant \forall \object o; \forall size_t i; (i < size && o == &val[i]) ==> (\mine(o) && o \in \array_range(val,size) && \mine(&val[i])) )
	//But this does???
		//_(invariant \mine(&val[0]) && \mine(&val[1]))



	//LOOK HERE FIRST
	//Let's say I want the following invariant on this structure.
		//_(invariant \exists size_t i; i < size && val[i].x == 15)
	//This alone is not admissible, since (I THINK) &val[i] may not be owned by \this... meaning it may not be \closed...so it could change even while \this is \closed.
	//So an additional invariant is needed asserting that &val[i] is owned by this object.
	//See: ADDITIONAL INVARIANTS 1


	//Ignore for now and move onto the next block
	//ADDITIONAL INVARIANTS 2
 	//_(invariant \forall size_t i; i < size ==> \mine(&val[i]))
	//_(invariant \forall \object o; o \in \array_range(val,size) ==> \mine(o) )
	//Those don't work, but this will
	//_(invariant \mine(&val[0]) && \mine(&val[1]))

	//I could shape the invariant like this, but this still is not enough without additional invariants.
	//_(invariant \exists size_t i; i < size && \mine(&val[i]) && val[i].x == 15)
	//See: ADDITIONAL INVARIANTS 2

	


	//_(invariant \exists \object o; o \in \array_range(val,size) && ((MyObject*)o)->x == 15)
	_(invariant \on_unwrap(\this, \exists \object o; (o \in \array_range(val,size) && ((MyObject*)o)->x == 15) ) )

	//_(invariant \forall size_t j; {\mine(&val[j])} j < size ==> (\exists size_t i; i < size && \mine(&val[i]) && val[i].x == 15))
} ObjectApprover;





typedef struct ObjectFixedSizeApprover
{
	MyObject val[2];
	size_t size;

	_(invariant size == 2)

	//_(invariant \mine((MyObject[size])val))
	//_(invariant \mine((MyObject[2])val))
	//_(invariant \mine(&val[0]) && (&val[1]))

	_(ghost size_t witness)
	_(invariant witness < size)
	_(invariant \mine(&val[witness]) && val[witness].x == 15)
	//_(invariant \exists size_t i; i < size && val[i].x == 15)

	_(invariant val[0].x == 15 || val[1].x == 15)

	//Bad old stuff...see the witness above!
	//_(invariant \mine(&val[0]) && \mine(&val[1]))
	//_(invariant \forall size_t i; i < size ==> \mine(&val[i]))
	//_(invariant \mine(\array_range(val,size)))
	//_(invariant \exists size_t i; i < size && val[i].x == 15)
	//_(invariant \exists \object o; o \in \array_range(val,size) && ((MyObject*)o)->x == 15)
	//_(invariant \exists \object o; (o \in \array_range(val,size) && ((MyObject*)o)->x == 15) )
	//_(invariant \on_unwrap(\this, \exists \object o; (o \in \array_range(val,size) && ((MyObject*)o)->x == 15) ) )
} ObjectFixedSizeApprover;

//void ObjectFixedSizeApproverTest(ObjectFixedSizeApprover* ob)
//	_(maintains \wrapped(ob))
//	_(requires \mutable(&ob->val[0]))
//{
//	_(unwrapping &ob->val[0])
//	{
//	
//	}
//}




void ApprovalTest(ObjectFixedSizeApprover* approver)
	_(maintains \wrapped(approver))
	
	_(writes approver)
	//_(writes \span(approver))
	//_(writes \extent(approver))
	_(writes \array_range(approver->val,approver->size))
{
	//_(unwrapping approver)
	{
		approver->val[0].x = 10;
		approver->val[1].x = 10;
	}

	//_(unwrapping approver)
	{
		approver->val[0].x = 0;
	}
}


