#include "scenegraph.h"

//void SGNodeCleanNode(SGNode* dis)
//{
//
//}


//Goes up to "children" (lower geometry) nodes and gets geometry recursively
Mesh* SGNodeGetVertexes(SGNode* dis)
	//_(
	//	ghost int sum = 0;
	//	for (int i = 0; i < dis->childcount; i++)
	//	{
	//		ghost Mesh test = SGNodeGetVertexes(dis->children[i]);
	//		sum += test.numverts;
	//	}
	//)
	//_(ensures \result.numverts == sum)
{
	//SGNodeCleanNode(_sceneNode);

	uint i = 0;
	uint j = 0;

	size_t vertexCounter = 0;

	//the mesh to return
	Mesh* newMeshToReturn;
		
	//array to keep the Mesh*s generated for each child node. These need to be kept because the process of generating this node's Mesh* HAS to happen in 2 passes so that enough space can be allocated for its verts... one pass to collect counts, one to allocate and store the verts
	Mesh** childrenMeshes;
	
	if (dis->mesh == null)
	{
		childrenMeshes = (Mesh**)malloc(dis->childcount * sizeof(Mesh*));
		
		newMeshToReturn = (Mesh*)malloc(sizeof(Mesh));
		newMeshToReturn->numedges = 0;
		newMeshToReturn->numfaces = 0;
		newMeshToReturn->numverts = 0;

		//First get a Mesh from each child (recursive structure)
		for (i = 0; i < dis->childcount; i++)
		{
			Mesh* thisChildMesh = SGNodeGetVertexes(dis->children[i]);
			childrenMeshes[i] = thisChildMesh;
			newMeshToReturn->numedges += thisChildMesh->numedges;
			newMeshToReturn->numfaces += thisChildMesh->numfaces;
			newMeshToReturn->numverts += thisChildMesh->numverts;
		}

		//Then grab all of the verts from each of those, transform it, and build up this Mesh to return
		for (i = 0; i < dis->childcount; i++)
		{
			for (j = 0; j < childrenMeshes[i]->numverts; j++)
			{
				//transform
				newMeshToReturn->verts[vertexCounter++] = HEVertMat4Transform(childrenMeshes[i]->verts[j], dis->trans);
			}
		}
	}
	else	//dis->mesh not null, so this is a leaf node
	{
		//Bake out mesh to JUST triangle vert list
	}

	return newMeshToReturn;
}
