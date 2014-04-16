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
	HEFace* face;	//face bordering halfedge
	HEEdge* next;	//next one around face
	//_(ghost size_t vertindexwit)
	//_(ghost size_t pairindexwit)
	//_(ghost size_t faceindexwit)
	//_(ghost size_t nextindexwit)

	//_(invariant \approves(\this->\owner, vert))
	//_(invariant \approves(\this->\owner, pair))
	//_(invariant \approves(\this->\owner, face))
	//_(invariant \approves(\this->\owner, next))
} HEEdge;

typedef struct HEFace
{
	HEEdge* edge;	//some halfedge around face
	//_(ghost size_t edgeindexwit)

	Vec3 normal;

	//_(invariant \approves(\this->\owner, edge))
} HEFace;

//typedef struct Mesh
typedef _(dynamic_owns) struct Mesh
{
	size_t numverts;
	size_t numedges;
	size_t numfaces;

	size_t capverts;
	size_t capedges;
	size_t capfaces;

	HEVert* verts;
	HEEdge* edges;
	HEFace* faces;

	_(invariant capverts >= numverts)
	_(invariant capedges >= numedges)
	_(invariant capfaces >= numfaces)

	_(invariant numverts > 0)// && numverts < UINT_MAX-10)
	_(invariant numedges > 0)// && numedges < UINT_MAX-10)
	_(invariant numfaces > 0)// && numfaces < UINT_MAX-10)


	//Arrays
	_(invariant \arrays_disjoint(verts,capverts,edges,capedges))
	_(invariant \arrays_disjoint(verts,capverts,faces,capfaces))
	_(invariant \arrays_disjoint(edges,capedges,faces,capfaces))

	//Array Objects
	_(ghost \object vertsao )
	_(ghost \object edgesao )
	_(ghost \object facesao )
	_(invariant vertsao == (HEEdge[capverts])verts )
	_(invariant edgesao == (HEEdge[capedges])edges )
	_(invariant facesao == (HEEdge[capfaces])faces )
	_(invariant \mine(vertsao) )
	_(invariant \mine(edgesao) )
	_(invariant \mine(facesao) )
	_(invariant vertsao != edgesao && vertsao != facesao && edgesao != facesao)
	_(invariant \malloc_root(vertsao))
	_(invariant \malloc_root(edgesao))
	_(invariant \malloc_root(facesao))

	//Array Elements are all \mine
	_(invariant \forall size_t i; {verts+i} i < numverts ==> \mine(&verts[i]))
	_(invariant \forall size_t i; {faces+i} i < numfaces ==> \mine(&faces[i]))
	_(invariant \forall size_t i; {edges+i} i < numedges ==> \mine(&edges[i]))
	
	//All pointed-to structures also belong to this mesh
	_(invariant \forall size_t i; /*{verts+i}*/ i < numverts ==>
		\in_array(verts[i].edge, edges, numedges)
	)
	_(invariant \forall size_t i; /*{edges+i}*/ i < numedges ==>
		//\mine(&edges[i]) &&	//Not needed thanks to proper trigger on the \mine invariant above

		//\mine(edges[i].vert) &&
		//(\exists size_t j; j < numverts && edges[i].vert == &verts[j]) &&	//doesn't work, but \in_array does
		\in_array(edges[i].vert, verts, numverts) &&
		\in_array(edges[i].pair, edges, numedges) &&		
		\in_array(edges[i].face, faces, numfaces) &&
		\in_array(edges[i].next, edges, numedges) 
	)
	_(invariant \forall size_t i; /*{faces+i}*/ i < numfaces ==>
		\in_array(faces[i].edge, edges, numedges)
	)

	//VERTS

	//I'm not sure there is really any structure that is best captured with a vert as a starting point
	//Might be able to prevent mesh holes here?


	//EDGES

	_(invariant \forall size_t i; {&edges[i]} i < numedges ==>
		\mine(edges[i].pair) && \mine(edges[i].pair->pair)
	)
	_(invariant \forall size_t i; /*{edges+i}*/ i < numedges ==>
		//pair's pair matches self
		//\mine(edges[i].pair) && \mine(edges[i].pair->pair) &&
		&edges[i] == edges[i].pair->pair
	)

	//_(invariant \forall size_t i; {edges[i].next} i < numedges ==> \mine(edges[i].next) )
	_(invariant \forall size_t i; /*{edges+i}*/ i < numedges ==>
		//next ring gets back to this edge after going around the triangle
		\mine(edges[i].next) && \mine(edges[i].next->next) && \mine(edges[i].next->next->next) &&
		edges+i == edges[i].next->next->next
	)


	//FACES 

	//Ignore all of this: old stuff that I haven't gotten to reviewing yet

	//_(invariant \forall size_t i; i < numfaces ==>
	//	\mine(&faces[i]) &&

	//	\mine(faces[i].edge) &&
	//	/*(\exists size_t j; j < numedges &&
	//		\mine(&edges[j]) &&
	//		\mine(faces[i].edge) &&
	//		faces[i].edge == &edges[j]
	//	) &&*/

	//	\mine(faces[i].edge->next) &&
	//	\mine(faces[i].edge->next->next) &&
	//	\mine(faces[i].edge->next->next->next) &&

	//	//face's edge points back to face
	//	faces[i].edge->face == &faces[i] &&
	//	//face's edge's face pointer points back to the face
	//
	//	//next face matches
	//	faces[i].edge->next->face == &faces[i] &&

	//	//next next face matches (2/3 of the way around the triangle)
	//	faces[i].edge->next->next->face == &faces[i] &&

	//	//complete triangles (go around far enough to return)
	//	faces[i].edge->next->next->next == faces[i].edge
	//)

} Mesh;

HEVert HEVertMat4Transform(HEVert, Mat4);
HEVert HEVertMat4TransformNormal(HEVert, Mat4);

void MeshInitMesh(Mesh* dis);
void MeshSplitEdge(Mesh *m, HEEdge* edge);


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