#include <vcc.h>
#include <stdlib.h>	//malloc

typedef struct MyObject
{
	int field;
} MyObject;

void ObjectArrayMallocAndFree_OK()
{
	MyObject* arr;
	size_t size = 10;
	arr = malloc(sizeof(MyObject) * size);
	_(assume arr != NULL)

	free(_(MyObject[size])arr);
}

void ObjectArrayMallocAndFree_StillOK()
{
	MyObject* arr;
	size_t size = 10;
	arr = malloc(sizeof(MyObject) * size);
	_(assume arr != NULL)

	//_(wrap (MyObject[size])arr)
	//_(unwrap (MyObject[size])arr)
	
	_(writes \extent((MyObject[size])arr))
	_(requires \full_context())
	{
		free(_(MyObject[size])arr);
	}
}

void ObjectArrayMallocAndFree_UnwrapBlock_OK()
{
	MyObject* arr;
	size_t size = 3;
	arr = malloc(sizeof(MyObject) * size);
	_(assume arr != NULL)

	_(wrap &arr[0])
	_(wrap &arr[1])
	_(wrap &arr[2])

	_(writes \span((MyObject[size])arr) )
	_(writes \array_members(arr,size) )	//for the unwraps
	_(requires \full_context() )
	{
		_(unwrap &arr[0])
		_(unwrap &arr[1])
		_(unwrap &arr[2])
		
		free(_(MyObject[size])arr);
	}
}

//void ObjectArrayMallocAndFree_NotOK()
//{
//	MyObject* arr;
//	size_t size = 10;
//	arr = malloc(sizeof(MyObject) * size);
//	_(assume arr != NULL)
//
//	_(wrap (MyObject[size])arr)
//	
//	_(writes (MyObject[size])arr)
//	//_(writes \extent((MyObject[size])arr) )	//conflicting?
//	_(requires \wrapped((MyObject[size])arr) )	//conflicting?
//	_(requires \malloc_root((MyObject[size])arr))
//	{
//		_(unwrap (MyObject[size])arr)
//		//error VC8510: Assertion '\extent(p) is writable in call to free(_(MyObject[size])arr)' did not verify.
//		//error VC9502: Call 'free(_(MyObject[size])arr)' did not verify.
//		//error VC9599: (related information) Precondition: 'the extent of the object being reclaimed is mutable'.
//		free(_(MyObject[size])arr);
//	}
//}




void FreeMyObjectArray(MyObject* arr, size_t size)
	_(decreases 0)
	//_(writes (MyObject[size])arr)
	_(writes \extent((MyObject[size])arr) )
	_(requires \malloc_root((MyObject[size])arr))
{
	free(_(MyObject[size])arr);
}



void ObjectArrayMallocAndFree_Better()
{
	MyObject* arr;
	size_t size = 10;
	arr = malloc(sizeof(MyObject) * size);
	_(assume arr != NULL)
	
	FreeMyObjectArray(arr,size);
}

void ObjectArrayMallocAndFree_WrapUnwrapLoopOK()
	_(decreases 0)
{
	MyObject* arr;
	size_t size = 10;
	arr = malloc(sizeof(MyObject) * size);
	_(assume arr != NULL)
	
	_(ghost size_t i)
	_(ghost
		for (i = 0; i < size; i++)
			_(decreases size-i)
			_(writes \array_members(arr,size))
			_(invariant \forall size_t j; j < size ==> \mutable(arr+j))
		{
			_(wrap arr+i)
			_(unwrap arr+i)
		}
	)

	FreeMyObjectArray(arr,size);
}

void ObjectArrayMallocAndFree_WrapUnwrapSeparate_OK()
	_(decreases 0)
{
	MyObject* arr;
	size_t size = 10;
	arr = malloc(sizeof(MyObject) * size);
	_(assume arr != NULL)
	
	_(ghost size_t i)
	_(ghost
		for (i = 0; i < size; i++)
			_(decreases size-i)
			_(writes \array_members(arr,size))
			_(invariant \forall size_t j; j >= i && j < size ==> \mutable(arr+j))
			_(invariant \forall size_t j; j < i ==> \wrapped(arr+j))
		{
			_(wrap arr+i)
		}
	)

	_(ghost
		for (i = 0; i < size; i++)
			_(decreases size-i)
			_(writes \array_members(arr,size))
			_(invariant \forall size_t j; j >= i && j < size ==> \wrapped(arr+j))
			_(invariant \forall size_t j; j < i ==> \mutable(arr+j))
		{
			_(unwrap arr+i)
		}
	)

	FreeMyObjectArray(arr,size);
}









//void FUNCTION2(MyObject* arr, size_t size)
//	//_(decreases 0)
//	_(writes \array_members(arr,size))	//for unwrapping
//	//_(writes (MyObject[size])arr )
//	_(writes \extent( (MyObject[size])arr ) )
//	_(requires \forall size_t j; j < size ==> \wrapped(arr+j) )
//	//_(requires \full_context())
//	_(requires \malloc_root( (MyObject[size])arr ))
//{
//	_(ghost size_t i)
//	_(ghost
//		for (i = 0; i < size; i++)
//			//_(decreases size-i)
//			_(writes \array_members(arr,size))
//			_(invariant \forall size_t j; j >= i && j < size ==> \wrapped(arr+j))
//			_(invariant \forall size_t j; j < i ==> \mutable(arr+j))
//		{
//			_(unwrap arr+i)
//		}
//	)
//	FreeMyObjectArray(arr,size);
//	//error VC8510: Assertion '\extent((MyObject[size])arr) is writable in call to FreeMyObjectArray(arr,size)' did not verify.
//}
//
//void ObjectArrayMallocAndFree_BlockUnWrapFree()
//	//_(decreases 0)
//{
//	MyObject* arr;
//	size_t size = 3;
//
//	//FUNCTION 1
//
//	arr = malloc(sizeof(MyObject) * size);
//	_(assume arr != NULL)
//	
//	//_(ghost
//	//	for (i = 0; i < size; i++)
//	//		//_(decreases size-i)
//	//		_(writes \array_members(arr,size))
//	//		_(invariant \forall size_t j; j >= i && j < size ==> \mutable(arr+j))
//	//		_(invariant \forall size_t j; j < i ==> \wrapped(arr+j))
//	//	{
//	//		_(wrap arr+i)
//	//	}
//	//)
//	_(wrap arr+0)
//	_(wrap arr+1)
//	_(wrap arr+2)
//
//	//END FUNCTION 1
//
//	//FUNCTION 2
//	FUNCTION2(arr,size);
//	//END FUNCTION 2
//}

//Cleaned up for forum post

void UnwrapAndFreeMyObjectArray(MyObject* arr, size_t size)
	_(writes \array_members(arr,size))
	_(writes \extent( (MyObject[size])arr ) )
	_(requires \forall size_t j; j < size ==> \wrapped(arr+j) )
	_(requires \malloc_root( (MyObject[size])arr ))
{
	_(ghost size_t i)
	_(ghost
		for (i = 0; i < size; i++)
			_(writes \array_members(arr,size))
			_(invariant \forall size_t j; j >= i && j < size ==> \wrapped(arr+j))
			_(invariant \forall size_t j; j < i ==> \mutable(arr+j))
		{
			_(unwrap arr+i)
		}
	)
	//FreeMyObjectArray(arr,size);
	free((MyObject[size])arr);
}

////////////////////////////////////////////////////////////////////////////////////

void ObjectArrayMallocAndFree_Test1()
{
	MyObject* arr;
	size_t size = 3;

	arr = malloc(sizeof(MyObject) * size);
	_(assume arr != NULL)
	
	//_(wrap arr+0)
	//_(wrap arr+1)
	//_(wrap arr+2)

	//UnwrapAndFreeMyObjectArray(arr,size);

	//_(writes \array_members(arr,size))
	_(writes \extent( (MyObject[size])arr ) )
	//_(requires \forall size_t j; j < size ==> \wrapped(arr+j) )
	_(requires \malloc_root( (MyObject[size])arr ))
	{
		//_(ghost size_t i)
		//_(ghost
		//	for (i = 0; i < size; i++)
		//		_(writes \array_members(arr,size))
		//		_(invariant \forall size_t j; j >= i && j < size ==> \wrapped(arr+j))
		//		_(invariant \forall size_t j; j < i ==> \mutable(arr+j))
		//	{
		//		_(unwrap arr+i)
		//	}
		//)
		//FreeMyObjectArray(arr,size);
		free((MyObject[size])arr);
	}
}


//void ObjectArrayMallocAndFree_NotOK()
//{
//	MyObject* arr;
//	size_t size = 10;
//	arr = malloc(sizeof(MyObject) * size);
//	_(assume arr != NULL)
//
//	_(wrap (MyObject[size])arr)
//
//	_(ghost size_t i)
//	_(ghost
//		for (i = 0; i < size; i++)
//			_(writes \array_members(arr,size))
//			_(invariant \forall size_t j; j >= i && j < size ==> \mutable(&arr[j]))
//			_(invariant \forall size_t j; j < i ==> \wrapped(&arr[j]))
//			_(invariant \malloc_root((MyObject[size])arr))
//		{
//			_(wrap arr+i)
//		}
//	)
//
//	_(unwrap (MyObject[size])arr)
//
//	free(_(MyObject[size])arr);
//}