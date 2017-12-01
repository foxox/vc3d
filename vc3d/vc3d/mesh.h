#pragma once

#include "commonheader.h"

#include "foxmath3.h"


typedef struct HEVert HEVert;
typedef struct HEFace HEFace;
typedef struct HEEdge HEEdge;


typedef struct HEVert
{
	Vec3 pos;
	Vec4 color;
	HEEdge* edge;	//some halfedge coming from vert
	//_(ghost size_t edgeindexwit)

	//_(invariant \approves(\this->\owner, edge))
} HEVert;


typedef struct HEEdge
{
	HEVert* vert;	//vert at end of halfedge
	HEEdge* pair;	//opposite halfedge
	HEFace* face;	//face bordering halfedge inside right hand rule
	HEEdge* next;	//next one around face
	//_(ghost size_t vertindexwit)
	//_(ghost size_t pairindexwit)
	//_(ghost size_t faceindexwit)
	//_(ghost size_t nextindexwit)

	//_(invariant \approves(\this->\owner, vert))
	//_(invariant \approves(\this->\owner, pair))
	//_(invariant \approves(\this->\owner, face))
	//_(invariant \approves(\this->\owner, next))

	//_(ghost size_t selfwit)
} HEEdge;


typedef struct HEFace
{
	HEEdge* edge;	//some halfedge around face
	//_(ghost size_t edgeindexwit)

	Vec3 normal;

	//_(invariant \approves(\this->\owner, edge))
} HEFace;


typedef _(dynamic_owns) struct Mesh
{
	//MEMBERS

	size_t numverts;
	size_t numedges;
	size_t numfaces;

	size_t capverts;
	size_t capedges;
	size_t capfaces;

	HEVert* verts;
	HEEdge* edges;
	HEFace* faces;


	//INVARIANTS


	//Sizes
	_(invariant numverts <= capverts)
	_(invariant numedges <= capedges)
	_(invariant numfaces <= capfaces)

	_(invariant capverts > 0)
	_(invariant capedges > 0)
	_(invariant capfaces > 0)


	//Arrays disjoint
	_(invariant \arrays_disjoint(verts,capverts,edges,capedges))
	_(invariant \arrays_disjoint(verts,capverts,faces,capfaces))
	_(invariant \arrays_disjoint(edges,capedges,faces,capfaces))
	_(invariant verts != edges)
	_(invariant edges != faces)
	_(invariant faces != verts)


	//Array Objects
	//(needed for disposal?)
	_(ghost \object vertsao )
	_(ghost \object edgesao )
	_(ghost \object facesao )
	_(invariant vertsao == (HEVert[capverts])verts )
	_(invariant edgesao == (HEEdge[capedges])edges )
	_(invariant facesao == (HEFace[capfaces])faces )
	_(invariant \mine(vertsao) )
	_(invariant \mine(edgesao) )
	_(invariant \mine(facesao) )
	_(invariant vertsao != edgesao && vertsao != facesao && edgesao != facesao)
	_(invariant \malloc_root(vertsao))
	_(invariant \malloc_root(edgesao))
	_(invariant \malloc_root(facesao))



	//Array Elements are all \mine
	_(invariant \forall size_t i; {verts+i} i < capverts ==> \mine(&verts[i]))
	_(invariant \forall size_t i; {faces+i} i < capfaces ==> \mine(&faces[i]))
	_(invariant \forall size_t i; {edges+i} i < capedges ==> \mine(&edges[i]))
	

	

	//All pointed-to structures also belong to this mesh.
	//Verts, then Edges, then Faces





	//Member Ownership Invariants

	//_(invariant \forall size_t i;
	//	{:hint \mine(&verts[i]) }
	//	//{verts+i}
	//	i < numverts ==>
	//	\mine(verts[i].edge)
	//)
	//_(invariant \forall size_t i;
	//	{:hint \mine(&edges[i]) }
	//	//{edges+i}
	//	i < numedges ==>
	//	   \mine(edges[i].vert)
	//	&& \mine(edges[i].pair)
	//	&& \mine(edges[i].face)
	//	&& \mine(edges[i].next)

	//	&& \mine(edges[i].pair->next)
	//	&& \mine(edges[i].pair->vert)
	//)
	//_(invariant \forall size_t i;
	//	{:hint \mine(&faces[i]) }
	//	//{faces+i}
	//	i < numfaces ==>
	//	\mine(faces[i].edge)
	//)



	//Additional stuff to help verification??

	//_(invariant \forall size_t i;
	//	{:hint \mine(&edges[i]) }
	//	{edges+i}
	//	i < numedges ==>
	//	\in_array(edges[i].pair->vert, verts, numverts)
	//)

	//_(invariant \forall size_t i;
	//	//{:hint \mine(&verts[i]) }
	//	//{verts+i}
	//	{&verts[i]}
	//	i < numverts <==> \mine(verts+i) && \in_array(verts+i, verts, numverts)
	//)

	//_(invariant \forall size_t i;
	//	//{:hint \mine(&edges[i]) }
	//	//{edges+i}
	//	{&edges[i]}
	//	i < numedges <==> \mine(edges+i) && \in_array(edges+i, edges, numedges)
	//)

	//_(invariant \forall size_t i;
	//	//{:hint \mine(&faces[i]) }
	//	//{faces+i}
	//	{&faces[i]}
	//	i < numfaces <==> \mine(faces+i) && \in_array(faces+i, faces, numfaces)
	//)






	_(invariant \forall size_t i;
	//{verts[i].edge}
	i < numverts ==>
		\in_array(verts[i].edge, edges, numedges)
	)
	_(invariant \forall size_t i;
	i < numedges ==>
		\in_array(edges[i].vert, verts, numverts) &&
		\in_array(edges[i].pair, edges, numedges) &&		
		\in_array(edges[i].face, faces, numfaces) &&
		\in_array(edges[i].next, edges, numedges) 
	)
	_(invariant \forall size_t i;
	//{faces[i].edge}
	i < numfaces ==>
		\in_array(faces[i].edge, edges, numedges)
	)



	//Mesh Invariants

	//Edges

	//Paired edge invariant
	_(invariant \forall size_t i;
	{edges[i].pair->pair}
	i < numedges ==>
		edges[i].pair->pair == &edges[i]
	)

	//Edges loop to form triangles
	_(invariant \forall size_t i;
	//{:hint \mine(&edges[i])}
	//{:hint \mine(edges[i].next)}
	//{:hint \mine(edges[i].next->next)}
	//{:hint \mine(edges[i].next->next->next)}
	{edges[i].next->next->next}
	i < numedges ==>
		(edges + i) == edges[i].next->next->next
	)

	//All edges on triangle have the same face
	_(invariant \forall size_t i;
	//{:hint \mine(edges[i].face)}
	//{:hint \mine(edges[i].next)}
	//{:hint \mine(edges[i].next->face)}
	{edges[i].next->face}
	i < numedges ==>
		edges[i].face == edges[i].next->face
	)
	_(invariant \forall size_t i;
	//{:hint \mine(edges[i].face)}
	//{:hint \mine(edges[i].next)}
	//{:hint \mine(edges[i].next->next)}
	//{:hint \mine(edges[i].next->next->face)}
	{edges[i].next->next->face}
	i < numedges ==>
		edges[i].face == edges[i].next->next->face
	)

	//Faces
	
	//This face's edge's face matches this face
	//note that due to edge invariants we can also deduce that the other edges around this face will properly point to this face
	_(invariant \forall size_t i;
	//{:hint \mine(&faces[i])}
	//{:hint \mine(faces[i].edge->face)}
	{faces[i].edge->face}
	i < numfaces ==>	
		faces[i].edge->face == &faces[i]
	)


} Mesh;

HEVert HEVertMat4Transform(HEVert, Mat4);
HEVert HEVertMat4TransformNormal(HEVert, Mat4);

void MeshInitMeshUnitTriangle(Mesh* dis);
void MeshSplitEdge(Mesh *dis, HEEdge* edge);
void MeshDisposeMesh(Mesh* dis);


//ARCHIVE

//Mesh pointer witness invariant ideas
//Replaced with the \in_array invariants which work and are much more concise

	//Witnesses for the existence of field pointers within this same mesh
	//Each of vert/edge/face stores its own witnesses for index. That they match is checked here
	//_(invariant \forall size_t i; i < numverts ==> \mine(&verts[i]) && verts[i].edgeindexwit < numedges && verts[i].edge == &edges[verts[i].edgeindexwit])
	//_(invariant \forall size_t i; i < numedges ==> \mine(&edges[i]) &&
	//	edges[i].vertindexwit < numverts && edges[i].vert == &verts[edges[i].vertindexwit] &&
	//	edges[i].pairindexwit < numedges && edges[i].pair == &edges[edges[i].pairindexwit] &&
	//	edges[i].nextindexwit < numedges && edges[i].next == &edges[edges[i].nextindexwit] &&
	//	edges[i].faceindexwit < numfaces && edges[i].face == &faces[edges[i].faceindexwit]
	//)
	//_(invariant \forall size_t i; i < numfaces ==> \mine(&faces[i]) && faces[i].edgeindexwit < numedges && faces[i].edge == &edges[faces[i].edgeindexwit])


	//Use the witnesses to form structural invariants
	//_(invariant \forall size_t i; i < numedges ==> \mine(edges+i) )
	//_(invariant \forall size_t i; i < numedges ==> edges[i].nextindexwit < numedges)
	//_(invariant \forall \object o; \in_array(o,edges,numedges) ==> \mine(o) )
	//_(invariant \forall \object o; \in_array(o,edges,numedges) ==> ((HEEdge*)o)->nextindexwit < numedges)
	//_(invariant \forall HEEdge* e; \in_array(e,edges,numedges) ==> \mine(e))
	//_(invariant \forall HEEdge* e; \in_array(e,edges,numedges) ==> e->nextindexwit < numedges)
	//_(invariant \forall HEEdge* e; e \in \array_members(edges,numedges) ==> \mine(e))
	//_(invariant \forall HEEdge* e; e \in \array_members(edges,numedges) ==> e->nextindexwit < numedges)

	//_(invariant \forall size_t i; i < numedges ==> \mine(edges+i) && edges[i].nextindexwit < numedges && &edges[edges[edges[edges[i].nextindexwit].nextindexwit].nextindexwit] == &edges[i])