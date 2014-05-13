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

	//GHOST MEMBERS
	_(ghost HEEdge* edgeset[] = {};)
	_(ghost HEVert* vertset[] = {};)
	_(ghost HEFace* faceset[] = {};)


	//INVARIANTS
	

	//Sizes
	_(invariant capverts >= numverts)
	_(invariant capedges >= numedges)
	_(invariant capfaces >= numfaces)

	_(invariant numverts > 0)
	_(invariant numedges > 0)
	_(invariant numfaces > 0)

	_(invariant capverts <= 10000)
	_(invariant capedges <= 10000)
	_(invariant capfaces <= 10000)


	//Arrays disjoint
	_(invariant \arrays_disjoint(verts,capverts,edges,capedges))
	_(invariant \arrays_disjoint(verts,capverts,faces,capfaces))
	_(invariant \arrays_disjoint(edges,capedges,faces,capfaces))


	//Array Objects
	//(needed for disposal?)
	//_(ghost \object vertsao )
	//_(ghost \object edgesao )
	//_(ghost \object facesao )
	//_(invariant vertsao == (HEEdge[capverts])verts )
	//_(invariant edgesao == (HEEdge[capedges])edges )
	//_(invariant facesao == (HEEdge[capfaces])faces )
	//_(invariant \mine(vertsao) )
	//_(invariant \mine(edgesao) )
	//_(invariant \mine(facesao) )
	//_(invariant vertsao != edgesao && vertsao != facesao && edgesao != facesao)
	//_(invariant \malloc_root(vertsao))
	//_(invariant \malloc_root(edgesao))
	//_(invariant \malloc_root(facesao))


	//Array Elements are all \mine
	//_(invariant \forall size_t i; {verts+i} i < capverts ==> \mine(&verts[i]))
	//_(invariant \forall size_t i; {faces+i} i < capfaces ==> \mine(&faces[i]))
	//_(invariant \forall size_t i; {edges+i} i < capedges ==> \mine(&edges[i]))




	//Verts
	//_(invariant \forall size_t i; {&verts[i]} i < capverts ==> \mine(&verts[i]))
	//_(invariant \forall size_t i; {&verts[i]} i < numverts ==>
	//	\in_array(verts[i].edge, edges, numedges)
	//	&&
	//	\mine(verts[i].edge)
	//)
	

	//Edges

	_(invariant \forall size_t i; \in_array(&edges[i], edges, numedges) ==> i < numedges)

	_(invariant \forall size_t i; {&edges[i]} i < capedges ==> \mine(&edges[i]))
	_(invariant \forall size_t i; /*{edges+i}*/ i < numedges ==>
		\in_array(edges[i].vert, verts, numverts) &&
		\in_array(edges[i].pair, edges, numedges) &&
		\in_array(edges[i].face, faces, numfaces) &&
		\in_array(edges[i].next, edges, numedges) &&

		//\mine(edges[i].pair) &&
		//\mine(edges[i].next) &&
		\mine(edges[i].vert) &&
		//\mine(edges[i].face)
		
		//\mine(edges[i].pair->next) &&
		//Why is this needed?
		//\mine(edges[i].pair->next->next) &&

		//\mine(edges[i].pair) &&
		//\mine(edges[i].pair->pair) &&
	
	
		//pair's pair matches self
		//NEEDED FOR VERIFICATION UNLESS ABOVE STATEMENT ALSO PRESENT
		//\mine(edges[i].pair) && \mine(edges[i].pair->pair) &&
		&edges[i] == edges[i].pair->pair &&
	
		//next ring gets back to this edge after going around the triangle
		//\mine(edges[i].next) &&
		//\mine(edges[i].next->next) &&
		\mine(edges[i].next->next->next) &&
		&edges[i] == edges[i].next->next->next
	)


	//Faces
	_(invariant \forall size_t i; {&faces[i]} i < capfaces ==> \mine(&faces[i]))
	_(invariant \forall size_t i; /*{faces+i}*/ i < numfaces ==>
		\in_array(faces[i].edge, edges, numedges)
	)



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