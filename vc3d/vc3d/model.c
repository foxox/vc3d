#include "model.h"

HEEdge *selectedEdges[MAXSELECTED];
HEFace *selectedFaces[MAXSELECTED];
HEVert *selectedVerts[MAXSELECTED];

SGNode* scene;

void initSelected()
{
	unsigned int i = 0;
	for (i = 0; i < MAXSELECTED; i++)
	{
		selectedEdges[i] = null;
		selectedFaces[i] = null;
		selectedVerts[i] = null;
	}
}
