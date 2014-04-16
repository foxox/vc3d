#include <vcc.h>

//typedef struct RandomObject
//{
//	int a;
//	int b;
//	int c;
//	_(invariant a == 0)
//} RandomObject;

typedef struct TestOb
{
	int a;

	//RandomObject* ob;

	_(invariant a == 0)
	//_(invariant \mine(ob))
} TestOb;



void testobModify(TestOb *sometestob)
	//_(writes sometestob)
	_(writes \span(sometestob))
	
	//_(writes sometestob->ob)
	//_(writes \span(sometestob->ob))

	//_(maintains \wrapped(sometestob->ob))
	_(maintains \wrapped(sometestob))
	
	//_(requires \false)
{
	//_(unwrapping sometestob->ob)
	{
	_(unwrapping sometestob)
	{
		sometestob->a = 5;
		//sometestob->ob->a = 5;
		sometestob->a = 0;
		//sometestob->ob->a = 0;
	}
	}
}

void testCall()
{
	TestOb sometestob;
	sometestob.a = 0;
	
	//RandomObject somerandomobject;
	//somerandomobject.a = 0;

	//sometestob.ob = &somerandomobject;

	//_(wrap sometestob.ob)
	//_(unwrap sometestob.ob)

	//_(wrap sometestob.ob)
	_(wrap &sometestob)
	testobModify(&sometestob);
	//_(unwrap sometestob.ob)
	_(unwrap &sometestob)
}

//void TestObInit(TestOb *input)
//	_(writes \extent(input))
//	//side effects
//	_(ensures \wrapped(input))
//{
//	input->a=0;
//	input->b=5;
//	_(wrap input)
//}
