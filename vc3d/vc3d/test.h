#include <vcc.h>
//#include <stdlib.h>	//malloc
//#include <stddef.h> //size_t
//typedef unsigned long uint;
//typedef unsigned long size_t;

//typedef struct MyObject MyObject;

typedef struct MyObject
{
	volatile
		size_t x;
	_(invariant \approves(\this->\owner, x))
} MyObject;

typedef
//_(dynamic_owns)
struct MyObjectUser
{
	//_(inline)
	MyObject val;

	_(invariant \mine(&val) )

	//unsigned int a;
	//_(invariant a == 0)

	_(invariant \this->val.x == 0)
} MyObjectUser;

void TestFunction(MyObjectUser* approver)
	_(maintains \wrapped(approver))
	
	//NOTICE TO ME
	//HERE I DISCOVERED THAT \SPAN AND \EXTENT SHOULD NOT BE USED WHEN THEY AREN'T NEEDED IN A WRITES CLAUSE

	_(writes approver)
	//_(writes \span(approver))
	//_(writes \extent(approver))
	//_(writes \extent(approver->val))
{
	_(unwrapping approver)
	{
		//_(unwrapping &approver->val)
		{
			_(atomic &approver->val)
			{
				approver->val.x = 10;
				_(bump_volatile_version &approver->val)
				
				//approver->a = 10;
			}
		}
	}

	//_(unwrap approver)
	//approver->val.x = 0;
	//_(wrap approver)
	}
