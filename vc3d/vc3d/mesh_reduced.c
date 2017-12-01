#include "mesh_reduced.h"

// http://www.flipcode.com/archives/The_Half-Edge_Data_Structure.shtml




//INITIALIZE A UNIT TRIANGLE WITH TWO SIDES. THIS IS THE SIMPLEST MESH
_(isolate_proof)
// /b:/vcsMaxCost:10 /b:/vcsMaxSplits:100
void MeshInitMeshUnitTriangle(Mesh* dis)
	_(writes \extent(dis))
	_(ensures \wrapped(dis))
{
	_(ghost dis->\owns = {};)

	dis->capverts = 3;
	dis->capedges = 6;


	dis->verts = (HEVert*)malloc(dis->capverts*sizeof(HEVert));
	dis->edges = (HEEdge*)malloc(dis->capedges*sizeof(HEEdge));
		
	_(assume dis->verts != NULL)
	_(assume dis->edges != NULL)
	
	//Initialize the triangle shape

	_(ghost {
	dis->\owns += &dis->verts[0];
	dis->\owns += &dis->verts[1];
	dis->\owns += &dis->verts[2];
	})
	_(wrap &dis->verts[0])
	_(wrap &dis->verts[1])
	_(wrap &dis->verts[2])

	//EDGES

	
	_(ghost {
	dis->\owns += &dis->edges[0];
	dis->\owns += &dis->edges[1];
	dis->\owns += &dis->edges[2];
	dis->\owns += &dis->edges[3];
	dis->\owns += &dis->edges[4];
	dis->\owns += &dis->edges[5];
	})
	_(wrap &dis->edges[0])
	_(wrap &dis->edges[1])
	_(wrap &dis->edges[2])
	_(wrap &dis->edges[3])
	_(wrap &dis->edges[4])
	_(wrap &dis->edges[5])

	//Array Objects
	_(ghost dis->vertsao = (HEVert[dis->capverts])dis->verts )
	_(ghost dis->edgesao = (HEVert[dis->capedges])dis->edges )
	
	_(ghost dis->\owns += dis->vertsao)
	_(ghost dis->\owns += dis->edgesao)
	
	_(wrap dis->vertsao)
	_(wrap dis->edgesao)

	_(wrap dis)
}


_(isolate_proof)
void MeshDisposeMesh(Mesh* dis)
_(requires \wrapped(dis))
_(writes dis)
_(ensures \extent_mutable(dis))
{
	_(unwrap dis)

	_(assert \forall size_t i; i < dis->capverts ==> \wrapped(dis->verts+i))
	_(assert \forall size_t i; i < dis->capedges ==> \wrapped(dis->edges+i))
	
	_(unwrap dis->vertsao)
	_(unwrap dis->edgesao)
	
	for (size_t i = 0; i < dis->capverts; i++)
		_(writes \array_members(dis->verts, dis->capverts))
		_(invariant \forall size_t j; j >= i && j < dis->capverts ==> \wrapped(dis->verts+j))
		_(invariant \forall size_t j; j < i ==> \mutable(dis->verts+j))
	{
		_(unwrap dis->verts+i)
	}

	for (size_t i = 0; i < dis->capedges; i++)
		_(writes \array_members(dis->edges, dis->capedges))
		_(invariant \forall size_t j; j >= i && j < dis->capedges ==> \wrapped(dis->edges+j))
		_(invariant \forall size_t j; j < i ==> \mutable(dis->edges+j))
	{
		_(unwrap dis->edges+i)
	}

	free( _(HEVert[dis->capverts]) dis->verts);
	free( _(HEEdge[dis->capedges]) dis->edges);
}






void MeshTester()
{
	Mesh m;
	MeshInitMeshUnitTriangle(&m);

	MeshDisposeMesh(&m);
}
