#pragma once

#include <vcc.h>
//#include <cstdlib>   //malloc
#include <stdlib.h>   //malloc

typedef struct HEVert HEVert;
typedef struct HEEdge HEEdge;

typedef struct HEVert
{
	float pos;
	float color;

} HEVert;


typedef struct HEEdge
{

} HEEdge;

typedef _(dynamic_owns) struct Mesh
{
	//MEMBERS
	size_t capverts;
	size_t capedges;
	
	_(invariant capverts > 0)
	_(invariant capedges > 0)
	

	HEVert* verts;
	HEEdge* edges;
	

	_(invariant verts != edges)
	_(invariant \arrays_disjoint(verts, capverts, edges, capedges))
	
	_(ghost \object vertsao)
	_(ghost \object edgesao)
	_(invariant vertsao == (HEVert[capverts])verts)
	_(invariant edgesao == (HEEdge[capedges])edges)
	
	_(invariant \mine(vertsao) )
	_(invariant \mine(edgesao) )
	
	_(invariant vertsao != edgesao)
	
	_(invariant \malloc_root(vertsao))
	_(invariant \malloc_root(edgesao))
	
	//Array Elements are all \mine
	_(invariant \forall size_t i; {verts+i} i < capverts ==> \mine(verts+i))
	//_(invariant \forall size_t i; {faces+i} i < capfaces ==> \mine(&faces[i]))
	_(invariant \forall size_t i; {edges+i} i < capedges ==> \mine(edges+i))
	
} Mesh;

void MeshInitMeshUnitTriangle(Mesh* dis);
void MeshDisposeMesh(Mesh* dis);

