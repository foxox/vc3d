#include <vcc.h>
#include <stdlib.h>

typedef struct MyObject MyObject;

typedef struct MyObjectPtr
{
	MyObject* obj;
} MyObjectPtr;

typedef struct MyObject
{
    int field;
	int* ptr1;
	int* ptr2;

	MyObjectPtr aoeu;

} MyObject;

typedef _(dynamic_owns) struct MyObjectArrayContainer
{
    MyObject* arr;
	size_t size;

	_(invariant \forall size_t i; {arr+i} i < size ==> \mine(arr+i))
    _(invariant \forall size_t i; i < size ==> arr[i].field == 0)

	_(invariant \forall size_t i; i < size ==> arr[i].ptr1 == arr[i].ptr2)

	//_(invariant \forall size_t i; i < size ==> arr[i].aoeu.obj == arr+i)
	//_(invariant \forall size_t i; i < size ==> \mine(&arr[i].aoeu) && arr[i].aoeu.obj == arr+i)
	//_(invariant \forall size_t i; {arr+i} i < size ==> \mine(&arr[i].aoeu))
	//_(invariant \forall size_t i; i < size ==> arr[i].aoeu.obj == arr+i)

	//_(invariant \forall size_t i; i < size ==> arr[i].aoeu.obj->aoeu.obj == arr+i)
	//_(invariant \forall size_t i; i < size ==> \mine(&arr[i].aoeu) && \mine(&arr[i].aoeu.obj->aoeu) && arr[i].aoeu.obj->aoeu.obj == arr+i)
	_(invariant \forall size_t i; {arr+i} i < size ==> \mine(&arr[i].aoeu) && \mine(&arr[i].aoeu.obj->aoeu))
	_(invariant \forall size_t i; i < size ==> arr[i].aoeu.obj->aoeu.obj == arr+i)

} MyObjectArrayContainer;
 
