#include "mesh.h"

// http://www.flipcode.com/archives/The_Half-Edge_Data_Structure.shtml

HEVert HEVertMat4Transform(HEVert vert, Mat4 mat)
{
	HEVert returnme;
	returnme.color = vert.color;
	returnme.edge = vert.edge;
	returnme.pos = Vec3Mat4Transform(vert.pos, mat);
	return returnme;
}

HEVert HEVertMat4TransformNormal(HEVert vert, Mat4 mat)
{
	HEVert returnme;
	returnme.color = vert.color;
	returnme.edge = vert.edge;
	returnme.pos = Vec3Mat4TransformNormal(vert.pos, mat);
	return returnme;
}

//INITIALIZE A UNIT TRIANGLE WITH TWO SIDES. THIS IS THE SIMPLEST MESH
_(isolate_proof)
// /b:/vcsMaxCost:10 /b:/vcsMaxSplits:100
void MeshInitMeshUnitTriangle(Mesh* dis)
	_(writes \extent(dis))
	_(ensures \wrapped(dis))
{
	_(ghost dis->\owns = {};)

	//These allow me to use _(wrap (HEFace[dis->numfaces])dis->faces) syntax later, even for size=1
	dis->numverts = 3;
	dis->numedges = 6;
	dis->numfaces = 2;

	dis->capverts = dis->numverts;
	dis->capedges = dis->numedges;
	dis->capfaces = dis->numfaces;

	/*_(assert dis->numverts > 0)
	_(assert dis->numedges > 0)
	_(assert dis->numfaces > 0)*/

	dis->verts = malloc(dis->capverts*sizeof(HEVert));
	dis->edges = malloc(dis->capedges*sizeof(HEEdge));
	dis->faces = malloc(dis->capfaces*sizeof(HEFace));
	
	_(assume dis->verts != NULL)
	_(assume dis->edges != NULL)
	_(assume dis->faces != NULL)

	//Initialize the triangle shape

	dis->verts[0].pos = Vec3GenVec3(0,0,0);
	dis->verts[1].pos = Vec3GenVec3(1,0,0);
	dis->verts[2].pos = Vec3GenVec3(0,1,0);

	dis->verts[0].color = Vec4GenVec4(1,0,0,1);
	dis->verts[1].color = Vec4GenVec4(0,1,0,1);
	dis->verts[2].color = Vec4GenVec4(0,0,1,1);

	dis->verts[0].edge = &dis->edges[0];
	dis->verts[1].edge = &dis->edges[1];
	dis->verts[2].edge = &dis->edges[2];

	//_(ghost dis->verts[0].edgeindexwit = 0)
	//_(ghost dis->verts[1].edgeindexwit = 1)
	//_(ghost dis->verts[2].edgeindexwit = 2)

	_(ghost {
	dis->\owns += &dis->verts[0];
	dis->\owns += &dis->verts[1];
	dis->\owns += &dis->verts[2];
	})
	_(wrap &dis->verts[0])
	_(wrap &dis->verts[1])
	_(wrap &dis->verts[2])

	//EDGES

	dis->edges[0].vert = &dis->verts[1];
	dis->edges[1].vert = &dis->verts[2];
	dis->edges[2].vert = &dis->verts[0];

	//_(ghost dis->edges[0].vertindexwit = 1)
	//_(ghost dis->edges[1].vertindexwit = 2)
	//_(ghost dis->edges[2].vertindexwit = 0)
	
	dis->edges[3].vert = &dis->verts[0];
	dis->edges[4].vert = &dis->verts[1];
	dis->edges[5].vert = &dis->verts[2];

	//_(ghost dis->edges[3].vertindexwit = 0)
	//_(ghost dis->edges[4].vertindexwit = 1)
	//_(ghost dis->edges[5].vertindexwit = 2)

	dis->edges[0].pair = &dis->edges[3];
	dis->edges[1].pair = &dis->edges[4];
	dis->edges[2].pair = &dis->edges[5];
	dis->edges[3].pair = &dis->edges[0];
	dis->edges[4].pair = &dis->edges[1];
	dis->edges[5].pair = &dis->edges[2];

	//_(ghost dis->edges[0].pairindexwit = 3)
	//_(ghost dis->edges[1].pairindexwit = 4)
	//_(ghost dis->edges[2].pairindexwit = 5)
	//_(ghost dis->edges[3].pairindexwit = 0)
	//_(ghost dis->edges[4].pairindexwit = 1)
	//_(ghost dis->edges[5].pairindexwit = 2)

	dis->edges[0].next = &dis->edges[1];
	dis->edges[1].next = &dis->edges[2];
	dis->edges[2].next = &dis->edges[0];

	//_(ghost dis->edges[0].nextindexwit = 1)
	//_(ghost dis->edges[1].nextindexwit = 2)
	//_(ghost dis->edges[2].nextindexwit = 0)

	dis->edges[3].next = &dis->edges[4];
	dis->edges[4].next = &dis->edges[5];
	dis->edges[5].next = &dis->edges[3];

	//_(ghost dis->edges[3].nextindexwit = 4)
	//_(ghost dis->edges[4].nextindexwit = 5)
	//_(ghost dis->edges[5].nextindexwit = 3)

	dis->edges[0].face = &dis->faces[0];
	dis->edges[1].face = &dis->faces[0];
	dis->edges[2].face = &dis->faces[0];

	//_(ghost dis->edges[0].faceindexwit = 0)
	//_(ghost dis->edges[1].faceindexwit = 0)
	//_(ghost dis->edges[2].faceindexwit = 0)

	dis->edges[3].face = &dis->faces[1];
	dis->edges[4].face = &dis->faces[1];
	dis->edges[5].face = &dis->faces[1];

	//_(ghost dis->edges[3].faceindexwit = 1)
	//_(ghost dis->edges[4].faceindexwit = 1)
	//_(ghost dis->edges[5].faceindexwit = 1)

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

	//FACES

	dis->faces[0].edge = &dis->edges[0];
	dis->faces[0].normal = Vec3GenVec3(0,0,1);
	//_(ghost dis->faces[0].edgeindexwit = 0)

	dis->faces[1].edge = &dis->edges[3];
	dis->faces[1].normal = Vec3GenVec3(0.0f,0.0f, 0-1.0f);
	//_(ghost dis->faces[1].edgeindexwit = 3)

	_(ghost	{
	dis->\owns += &dis->faces[0];
	dis->\owns += &dis->faces[1];
	})
	_(wrap &dis->faces[0])
	_(wrap &dis->faces[1])


	//Array Objects
	//_(ghost dis->vertsao = (HEVert[dis->capverts])dis->verts )
	//_(ghost dis->edgesao = (HEVert[dis->capedges])dis->edges )
	//_(ghost dis->facesao = (HEVert[dis->capfaces])dis->faces )
	//_(ghost dis->\owns += dis->vertsao)
	//_(ghost dis->\owns += dis->edgesao)
	//_(ghost dis->\owns += dis->facesao)
	//_(wrap dis->vertsao)
	//_(wrap dis->edgesao)
	//_(wrap dis->facesao)

	_(wrap dis)
}

//Functions to grow or shrink the internal arrays
void MeshGrowEdges(Mesh *m)
	_(updates m);

void MeshShrinkEdges(Mesh *m)
	_(updates m);

void MeshEnsureVertCapacityChange(Mesh *m, int change)
	_(updates m)
	_(ensures ((\integer)m->capverts - (\integer)m->numverts) >= change);

void MeshEnsureEdgeCapacityChange(Mesh *m, int change)
	_(updates m)
	_(ensures ((\integer)m->capedges - (\integer)m->numedges) >= change);

void MeshEnsureFaceCapacityChange(Mesh *m, int change)
	_(updates m)
	_(ensures ((\integer)m->capfaces - (\integer)m->numfaces) >= change);


//SPLIT AN EDGE AT ITS CENTER, THEN SEW THE MESH BACK UP
//Requires that additional storage for new parts already exists.
_(isolate_proof)

void MeshSplitEdge(Mesh *m, HEEdge* e)
	_(updates m)
	
	_(requires e \in m->\owns)
	_(requires \in_array(e,m->edges,m->numedges) )
	
	//Verts +1
	//Edges -2+4+4
	//Faces -2+4
	_(requires m->capverts-m->numverts >= 1)
	_(requires m->capedges-m->numedges >= 6)
	_(requires m->capfaces-m->numfaces >= 2)

	_(ensures m->numverts == \old(m->numverts)+1)
	_(ensures m->numedges == \old(m->numedges)+6)
	_(ensures m->numfaces == \old(m->numfaces)+2)

{
	//Function Body 

	//Guiding assertions
	_(assert e->next \in m->\owns)
	_(assert e->pair->next \in m->\owns)
	//here's where those witnesses would help!

	#define e1 (e)
	#define e2 (e->next)
	#define e3 (e->next->next)
	#define e4 (e->pair)
	#define e5 (e->pair->next)
	#define e6 (e->pair->next->next)
	#define e7 (m->edges + (m->numedges+0))
	#define e8 (m->edges + (m->numedges+1))
	#define e9 (m->edges + (m->numedges+2))
	#define e10 (m->edges + (m->numedges+3))
	#define e11 (m->edges + (m->numedges+4))
	#define e12 (m->edges + (m->numedges+5))

	//_(assert m->numedges < m->capedges)
	//_(assert m->numedges < m->capedges-4)
	//_(assert e9 == m->edges + m->numedges + 2)
	//_(assert e9 == &m->edges[m->numedges+2])
	//_(assert \in_array(m->edges + (m->numedges + 2),m->edges,m->capedges))
	//_(assert \in_array(m->edges + (m->numedges + 2),m->edges,m->numedges+6))
	//_(assert \in_array(&m->edges[m->numedges+2],m->edges,m->capedges))
	//_(assert \in_array(&m->edges[m->numedges+2],m->edges,m->numedges+6))
	//_(assert \in_array(e9,m->edges,m->capedges))
	//_(assert \in_array(e9,m->edges,m->numedges+6))

	//_(assert e \in m->\owns)
	//_(assert e->pair \in m->\owns)
	//_(assert \in_array(e,m->edges,m->numedges))
	//_(assert e->pair->vert \in m->\owns)

	//HEVert* v1 = e->pair->vert;
	//HEVert* v2 = e->vert;
	////HEVert* v3 = m->verts + (m->numverts+0);
	//HEVert* v3 = &m->verts[m->numverts];
	#define v1 (e->pair->vert)
	#define v2 (e->vert)
	#define v3 (&m->verts[m->numverts])
	
	//_(assert v1 \in m->\owns)
	//_(assert v2 \in m->\owns)
	//_(assert v3 \in m->\owns)
	//_(assert \in_array(v1, m->verts, m->numverts))
	//_(assert \in_array(v2, m->verts, m->numverts))

	//_(assert \exists size_t i; i < m->numverts && v1 == &m->verts[i])
	//_(assert \exists size_t i; i < m->numverts && v2 == &m->verts[i])

	//HEFace* f1 = e->face;
	//HEFace* f2 = e->pair->face;
	//HEFace* f3 = m->faces + (m->numfaces+0);
	//HEFace* f4 = m->faces + (m->numfaces+1);
	#define f1 (e->face)
	#define f2 (e->pair->face)
	#define f3 (m->faces + (m->numfaces+0))
	#define f4 (m->faces + (m->numfaces+1))

	_(assert e1 \in m->\owns)
	_(assert e2 \in m->\owns)
	_(assert e3 \in m->\owns)
	_(assert e4 \in m->\owns)
	_(assert e5 \in m->\owns)
	_(assert e6 \in m->\owns)
	_(assert e7 \in m->\owns)
	_(assert e8 \in m->\owns)
	_(assert e9 \in m->\owns)
	_(assert e10 \in m->\owns)
	_(assert e11 \in m->\owns)
	_(assert e12 \in m->\owns)

	_(assert v1 \in m->\owns)
	_(assert v2 \in m->\owns)
	_(assert v3 \in m->\owns)

	_(assert f1 \in m->\owns)
	_(assert f2 \in m->\owns)
	_(assert f3 \in m->\owns)
	_(assert f4 \in m->\owns)

_(unwrap m)

	_(assert \wrapped(e1))
	_(assert \wrapped(e2))
	_(assert \wrapped(e3))
	_(assert \wrapped(e4))
	_(assert \wrapped(e5))
	_(assert \wrapped(e6))
	_(assert \wrapped(e7))
	_(assert \wrapped(e8))
	_(assert \wrapped(e9))
	_(assert \wrapped(e10))
	_(assert \wrapped(e11))
	_(assert \wrapped(e12))

	_(assert \wrapped(v1))
	_(assert \wrapped(v2))
	_(assert \wrapped(v3))

	_(assert \wrapped(f1))
	_(assert \wrapped(f2))
	_(assert \wrapped(f3))
	_(assert \wrapped(f4))

	_(assert \writable(e1))
	_(assert \writable(e2))
	_(assert \writable(e3))
	_(assert \writable(e4))
	_(assert \writable(e5))
	_(assert \writable(e6))
	_(assert \writable(e7))
	_(assert \writable(e8))
	_(assert \writable(e9))
	_(assert \writable(e10))
	_(assert \writable(e11))
	_(assert \writable(e12))

	_(assert \writable(v1))
	_(assert \writable(v2))
	_(assert \writable(v3))

	_(assert \writable(f1))
	_(assert \writable(f2))
	_(assert \writable(f3))
	_(assert \writable(f4))

	//Now reassign things

	_(assert \writable(e1))
	_(assert \wrapped(e1))
	_(unwrapping e1)
	{
		e1->next = e7;
		e1->pair = e9;
		e1->vert = v3;
	}

	_(assert \writable(e2))
	_(assert \wrapped(e2))
	_(unwrapping e2)
	{
		e2->face = f4;
		e2->next = e12;
	}

	_(assert \writable(e3))
	_(assert \wrapped(e3))
	_(unwrapping e3)
	{
		e3->face = f1;
	}

	_(assert \writable(e4))
	_(assert \wrapped(e4))
	_(unwrapping e4)
	{
		e4->face = f3;
		e4->next = e10;
		e4->pair = e11;
		e4->vert = v3;
	}

	_(assert \writable(e5))
	_(assert \wrapped(e5))
	_(unwrapping e5)
	{
		e5->next = e8;
	}

	_(assert \writable(e6))
	_(assert \wrapped(e6))
	_(unwrapping e6)
	{
		e6->face = f3;
	}

	_(assert \writable(e7))
	_(assert \wrapped(e7))
	_(unwrapping e7)
	{
		e7->face = f1;
		e7->next = e3;
		e7->pair = e12;
		e7->vert = e2->vert;
	}

	_(assert \wrapped(e8))
	_(assert \writable(e8))
	_(unwrapping e8)
	{
		e8->face = f2;
		e8->next = e9;
		e8->pair = e10;
		e8->vert = v3;
	}

	_(assert \writable(e9))
	_(assert \wrapped(e9))
	_(unwrapping e9)
	{
		e9->face = f2;
		e9->next = e5;
		e9->pair = e1;
		e9->vert = v1;
	}

	_(assert \writable(e10))
	_(assert \wrapped(e10))
	_(unwrapping e10)
	{
		e10->face = f3;
		e10->next = e6;
		e10->pair = e8;
		e10->vert = e5->vert;
	}

	_(assert \writable(e11))
	_(assert \wrapped(e11))
	_(unwrapping e11)
	{
		e11->face = f4;
		e11->next = e2;
		e11->pair = e4;
		e11->vert = v2;
	}

	_(assert \writable(e12))
	_(assert \wrapped(e12))
	_(unwrapping e12)
	{
		e12->face = f4;
		e12->next = e11;
		e12->pair = e7;
		e12->vert = v3;
	}

	_(assert \wrapped(v1))
	_(unwrapping v1)
	{
		v1->edge = e1;
	}

	_(unwrapping v2)
	{
		v2->edge = e4;
	}

	_(unwrapping v3)
	{
		v3->edge = e9;
	}

	_(assert \writable(f1))
	_(unwrapping f1)
	{
		f1->edge = e3;
	}

	_(unwrapping f2)
	{
		f2->edge = e5;
	}
	
	_(unwrapping f3)
	{
		f3->edge = e6;
	}

	_(unwrapping f4)
	{
		f4->edge = e2;
	}

	//_(assert m->numverts == \old(m->numverts))
	//_(assert m->numedges == \old(m->numedges))
	//_(assert m->numfaces == \old(m->numfaces))

	//_(assert m->numverts < 10000)
	//_(assert m->numedges < 10000)
	//_(assert m->numfaces < 10000)

	m->numverts += 1;
	m->numedges += 6;
	m->numfaces += 2;

	_(assert m->numverts == \old(m->numverts)+1)
	_(assert m->numedges == \old(m->numedges)+6)
	_(assert m->numfaces == \old(m->numfaces)+2)

	_(assert \in_array(m->edges + (\old(m->numedges)+2), m->edges,m->capedges))
	_(assert m->numedges == \old(m->numedges)+6)
	_(assert \in_array(m->edges + (m->numedges+2), m->edges,m->numedges))

	_(assert \in_array(e1,m->edges,m->numedges))
	_(assert \in_array(e4,m->edges,m->numedges))
	_(assert \in_array(e9,m->edges,m->numedges))
	_(assert \in_array(v1->edge,m->edges,m->numedges))
	_(assert \in_array(v2->edge,m->edges,m->numedges))
	_(assert \in_array(v3->edge,m->edges,m->numedges))
_(wrap m)
}