#include <vcc.h>

typedef struct MyObject
{
	size_t val;
} MyObject;

typedef struct MyObjectUser
{
	_(inline) MyObject obj;

	_(invariant obj.val == 15)
} MyObjectUser;

void TestFunction(MyObjectUser* objuser)
	_(maintains \wrapped(objuser))
	_(writes \extent(objuser))
{
    //Break the invariant?
	_(unwrapping objuser)
	{
		objuser->obj.val = 15;
	}
}

void TestFunctionTest()
{
	MyObjectUser aoeu;
	aoeu.obj.val = 15;
	_(wrap &aoeu)
		TestFunction(&aoeu);
	_(unwrap &aoeu)
}