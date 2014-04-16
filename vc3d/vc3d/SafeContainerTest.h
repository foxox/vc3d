#include <vcc.h>

//#include "commonheader.h"
#include <stdlib.h>	//malloc
#define null 0

typedef struct SafeString2
{
	unsigned int capacity;
	unsigned int len;
	char* content;

	_(invariant len < capacity)
	_(invariant content[len] == '\0')
	_(invariant \mine( (char[capacity])content ) )
} SafeString2;

void sstr_append_char(struct SafeString2* s, char c)
	_(requires \wrapped(s))
	_(requires s->len < s->capacity - 1)
	_(ensures \wrapped(s))
	_(writes s)
	_(decreases 0)
{
	_(unwrapping s)
	{
		_(unwrapping (char[s->capacity])(s->content))
		{
			s->content[s->len] = c;
			s->len++;
			s->content[s->len] = '\0';
		}
	}
}

int sstr_allocate(struct SafeString2* s, unsigned int cap, unsigned int len)
	_(ensures \result ==> \wrapped(s))
	_(requires len < cap && cap > 0)
	//_(requires \mutable(s))
	_(writes \extent(s))
{
	s->content = malloc(sizeof(char) * cap);
	if (s->content != NULL)
	{
		s->capacity = cap;
		s->len = len;
		s->content[len] = '\0';
		_(wrap (char[cap])(s->content) )
		_(wrap s)
		return 1;
	}
	return 0;
}




typedef _(dynamic_owns) struct SafeContainer2
{
	struct SafeString2 **strings;
	unsigned len;
	
	_(invariant \mine((struct SafeString2*[len])strings))
	_(invariant \forall unsigned i; i < len ==>
	\mine(strings[i]))
	_(invariant \forall unsigned i, j; i < len && j < len ==> i != j ==> strings[i] != strings[j])

	//Use witness; forget EXISTS
	//_(invariant \exists unsigned x; x < len && strings[x]->len == 5)
} SafeContainer2;




void sc_set(struct SafeContainer2 *c, struct SafeString2 *s, unsigned idx)
	_(requires \wrapped(c) && \wrapped(s))
	_(requires idx < c->len)
	_(ensures \wrapped(c))
	_(ensures c->strings[idx] == s)
	_(ensures \wrapped(\old(c->strings[idx])))
	_(ensures \fresh(\old(c->strings[idx])))
	_(ensures c->len == \old(c->len))
	_(writes c, s)
	_(decreases 0)
{
	_(assert !(s \in c->\owns))
	_(unwrapping c)
	{
		_(unwrapping (struct SafeString2 *[c->len])(c->strings))
		{
			c->strings[idx] = s;
		}
		
		_(
			ghost
			{
				c->\owns -= \old(c->strings[idx]);
				c->\owns += s;
			}
		)
	}
}

SafeContainer2* create_and_wrap_and_return_a_SafeContainer2()
	_(ensures \wrapped(\result))
{
	SafeContainer2* a;
	a = malloc(sizeof(SafeContainer2));
	_(assume a != null)

	a->len = 1;

	a->strings = malloc(sizeof(SafeString2*) * a->len);
	_(assume a->strings != NULL)

	_(ghost a->\owns = {}; )

	a->strings[0] = malloc(sizeof(SafeString2) * 1);
	_(assume a->strings[0] != NULL)
	a->strings[0]->capacity = 1;
	a->strings[0]->len = 0;
	a->strings[0]->content = malloc(sizeof(char) * a->strings[0]->capacity);
	_(assume a->strings[0]->content != NULL)
	a->strings[0]->content[a->strings[0]->len] = '\0';
	_(wrap (char[a->strings[0]->capacity])a->strings[0]->content)
	_(wrap a->strings[0])

	_(wrap (SafeString2[a->len])a->strings)

	_(ghost {
		a->\owns += a->strings[0];
		a->\owns += (SafeString2[a->len])a->strings;
	})
	_(wrap a)

	return a;
}

//void test1()
//{
//	SafeContainer2 a;
//	
//	a.len = 1;
//	
//	a.strings = malloc(sizeof(SafeString2*) * 1);
//	_(assume a.strings != NULL)
//	//Is this enough to imply that malloc succeeded?
//
//	_(ghost {
//		a.\owns = {};
//	})
//
//	a.strings[0] = malloc(sizeof(SafeString2) * 1);
//	_(assume a.strings[0] != NULL)
//	//Is this enough to imply that malloc succeeded?
//
//	a.strings[0]->capacity = 1;
//	a.strings[0]->len = 0;
//	a.strings[0]->content = malloc(sizeof(char) * 1);
//	_(assume a.strings[0]->content != NULL)
//	
//	_(ghost {
//		a.\owns += a.strings[0];
//	})
//
//	//Why do I need this?
//	//_(assume \writable((char[a.strings[0]->capacity])(a.strings[0]->content)))
//
//	_(wrap (char[a.strings[0]->capacity])a.strings[0]->content )
//
//	//Why does this wrap succeed? I'm not sure where the SafeString2 '\0' invariant is satisfied.... unless this malloc initializes allocated memory to zeros
//	_(wrap a.strings[0])
//
//	_(wrap &a)
//
//
//
//}

//void test3()
//{
//	SafeString2* s = malloc(sizeof(SafeString2));
//	_(assume s != NULL)
//	s->len = 1;
//	s->capacity = 2;
//	s->content = malloc(sizeof(char) * s->capacity);
//	_(assume s->content != NULL)
//	s->content[s->len] = '\0';
//	_(wrap (char[s->capacity])s->content)
//	_(wrap s)
//
//	SafeString2** strings = malloc(sizeof(SafeString2*) * 1);
//	_(assume strings != NULL)
//	strings[0] = malloc(sizeof(SafeString2) * 1);
//	_(assume strings[0] != NULL)
//	strings[0]->len = 0;
//	strings[0]->capacity = 1;
//
//	//strings[0]->content = malloc(sizeof(char) * strings[0]->capacity);
//	strings[0]->content = malloc(sizeof(char) * 1);
//
//	_(assume strings[0]->content != NULL)
//	strings[0]->content[strings[0]->len] = '\0';
//	_(wrap (char[strings[0]->capacity])strings[0]->content )
//	_(wrap strings[0])
//	
//}