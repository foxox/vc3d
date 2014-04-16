#include <vcc.h>
#include <stdlib.h>

typedef struct MyObject
{
	int field;
} MyObject;

typedef struct MyObjectWithPointer MyObjectWithPointer;
typedef struct MyObjectWithPointer
{
	MyObjectWithPointer* ptr;
} MyObjectWithPointer;

typedef _(dynamic_owns) struct SimpleTest
{
	MyObject* obj;
	_(invariant \mine(obj))
	_(invariant obj->field == 0)
} SimpleTest;

typedef _(dynamic_owns) struct SimpleTestWithArray1
{
	MyObject* arr;
	size_t size;

	//Bad: second invariant cannot be shown to be admissible by default (though it is)
	//_(invariant \forall size_t i; i < size ==> \mine(&arr[i]))
	//_(invariant \forall size_t i; i < size ==> arr[i].field == 0)

	//Alternative: put all such invariants under one \forall
	//_(invariant \forall size_t i; i < size ==> \mine(arr+i) && arr[i].field == 0)

	//Optimal solution:
	//The problem with the first approach is that the first invariant triggers on \mine(arr+i)
	//It needs to trigger on arr+i in order for it to be available while VCC attempts to
	//convince itself that the second invariant (which mentions arr+i and not \mine(arr+i)
	//is admissible
	_(invariant \forall size_t i; {arr+i} i < size ==> \mine(&arr[i]))
	_(invariant \forall size_t i; i < size ==> arr[i].field == 0)
} SimpleTestWithArray1;


//Array of objects with pointers; make invariant about where those pointers go
typedef _(dynamic_owns) struct DirectedGraph1
{
	MyObjectWithPointer* arr;
	size_t size;

	_(invariant \forall size_t i; {arr+i} i < size ==> \mine(&arr[i]))
	
	//_(invariant \forall size_t i; {arr+i} i < size ==>
	//			(\exists size_t j; j < size && arr[i].ptr == arr+j))
	//\in_array is equivalent and seems to perform better here
	_(invariant \forall size_t i; i < size ==> \in_array(arr[i].ptr,arr,size))

	//_(ghost size_t ptridxwits[size_t])
	//_(invariant \forall size_t i; i < size ==> ptridxwits[i] < size)
	//_(invariant \forall size_t i; i < size ==> arr+ptridxwits[i] == arr[i].ptr)
} DirectedGraph1;








typedef struct SimpleTestWithArrayStaticOwns
{
	MyObject arr[3];
	_(invariant \mine((MyObject[3])arr) )	//in ownership, array object of object array has no fields
	//So instead:
	//_(invariant \forall size_t i; i < 3 ==> \mine(&arr[i]))
	//But not without _(dynamic_owns)
	//So instead... do each one
	_(invariant \mine(arr+0) )
	_(invariant \mine(arr+1) )
	_(invariant \mine(arr+2) )

	_(invariant \forall size_t i; i < 3 ==> (arr[i].field == 0) )
	//_(invariant \forall size_t i; i < size ==> \mine(arr+i) && arr[i].field == 0)
} SimpleTestWithArrayStaticOwns;

//typedef _(dynamic_owns) struct SimpleTestWithArrayDynamicOwns
//{
//	MyObject arr[3];
//	_(invariant \mine((MyObject[3])arr) )	//in ownership, array object of object array has no fields
//	//So instead:
//	_(invariant \forall size_t i; i < 3 ==> \mine(&arr[i]))
//	//But that seems to miss something, because this reports as inadmissible:
//	_(invariant \forall size_t i; i < 3 ==> (arr[i].field == 0) )
//	//_(invariant \forall size_t i; i < size ==> \mine(arr+i) && arr[i].field == 0)
//} SimpleTestWithArrayDynamicOwns;


typedef struct SimpleTestWithArrayStaticOwnsInt
{
	int arr[10];
	_(invariant \mine((int[10])arr) )

	_(invariant \forall size_t i; i < 10 ==> (arr[i] == 0) )
} SimpleTestWithArrayStaticOwnsInt;


typedef _(dynamic_owns) struct SimpleTest2
{
	MyObjectWithPointer* obj1;
	MyObjectWithPointer* obj2;
	MyObjectWithPointer* obj3;
	MyObjectWithPointer* obj4;
	_(invariant \mine(obj1) && \mine(obj2) && \mine(obj3) && \mine(obj4))
	_(invariant obj1->ptr == obj2 || obj1->ptr == obj3 || obj1->ptr == obj4)
	_(invariant obj2->ptr == obj1 || obj1->ptr == obj3 || obj1->ptr == obj4)
	_(invariant obj3->ptr == obj2 || obj1->ptr == obj1 || obj1->ptr == obj4)
	_(invariant obj4->ptr == obj2 || obj1->ptr == obj3 || obj1->ptr == obj1)
	_(invariant obj1->ptr->ptr == 0)
} SimpleTest2;

