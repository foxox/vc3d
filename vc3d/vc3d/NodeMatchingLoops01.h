#include <vcc.h>

typedef struct Node Node;
typedef _(dynamic_owns) struct Node
{
	Node* next;
	int f;
	_(invariant \forall Node* n;
		{\mine(n)}
		\mine(n) ==> n->f == 1
	)
	_(invariant \forall Node* n;
		{n->f}
		n->f ==> \mine(n->next)
	)
	//\mine(a)
} Node;

void test()
{
	Node n;
}