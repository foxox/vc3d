#pragma once

#include "commonheader.h"

#include "mesh.h"

#include "foxmath3.h"

typedef struct SGNode SGNode;

_(def \bool Vec3Equal(Vec3 a, Vec3 b)
{
	return a.x == b.x && a.y == b.y && a.z == b.z;
})

_(def \bool Vec4Equal(Vec4 a, Vec4 b)
{
	return a.r == b.r && a.g == b.g && a.b == b.b && a.a == b.a;
})

_(def \bool HEVertEqual(HEVert a, HEVert b)
{
	return Vec3Equal(a.pos, b.pos) && Vec4Equal(a.color, b.color) && (a.edge == b.edge);
})

typedef struct SGNode
{
	uint parentcount;
	uint childcount;
	SGNode* parents[10];
	SGNode* children[100];

	Mat4 trans;
	
	Mesh* mesh;

	//BOOL dirty;
	//uint numCachedVertexes;
	//uint numCachedIndexes;
	//HEVert *cachedVertexes;
	//uint *cachedIndexes;

	_(invariant parentcount <= 10)
	_(invariant childcount <= 100)
	_(invariant \forall uint i; i < parentcount ==> parents[i] != null)

	////Invariant that cached vertexes contains all mesh vertexes
	//_(invariant !dirty ==> 
	//	\forall uint i;
	//		i < mesh->numverts ==>
	//			\exists uint j;
	//				j < numCachedVertexes
	//				&& HEVertEqual(mesh->verts[i], cachedVertexes[j]))
	//_(invariant !dirty ==> numCachedVertexes == mesh->numverts)
} SGNode;

//extern void SGNodeCleanNode(SGNode*);

extern Mesh* SGNodeGetVertexes(SGNode*);
