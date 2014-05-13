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
void MeshInitMeshUnitTriangle(Mesh* dis)
	_(writes \extent(dis))
	_(ensures \wrapped(dis))
{
	_(ghost dis->\owns = {};)

	//These allow me to use _(wrap (HEFace[dis->numfaces])dis->faces) syntax later, even for size=1
	dis->numverts = 3;
	dis->numedges = 6;
	dis->numfaces = 2;

	dis->capverts = 2*dis->numverts;
	dis->capedges = 2*dis->numedges;
	dis->capfaces = 2*dis->numfaces;

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
	_(ghost dis->vertsao = (HEVert[dis->capverts])dis->verts )
	_(ghost dis->edgesao = (HEVert[dis->capedges])dis->edges )
	_(ghost dis->facesao = (HEVert[dis->capfaces])dis->faces )
	_(ghost dis->\owns += dis->vertsao)
	_(ghost dis->\owns += dis->edgesao)
	_(ghost dis->\owns += dis->facesao)
	_(wrap dis->vertsao)
	_(wrap dis->edgesao)
	_(wrap dis->facesao)

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
void MeshSplitEdge(Mesh *m, HEEdge* e)
	_(updates m)
	
	//needed?
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
	//_(assert e->pair \in m->\owns)
	//_(assert e->next \in m->\owns)
	//_(assert e->pair->next \in m->\owns)
	//here's where those witnesses would help!

	HEEdge* e1 = e;
	HEEdge* e2 = e->next;
	HEEdge* e3 = e->next->next;
	HEEdge* e4 = e->pair;
	HEEdge* e5 = e->pair->next;
	HEEdge* e6 = e->pair->next->next;
	HEEdge* e7 = m->edges + (m->numedges+0);
	HEEdge* e8 = m->edges + (m->numedges+1);
	HEEdge* e9 = m->edges + (m->numedges+2);
	HEEdge* e10 = m->edges + (m->numedges+3);
	HEEdge* e11 = m->edges + (m->numedges+4);
	HEEdge* e12 = m->edges + (m->numedges+5);

	HEVert* v1 = e->pair->vert;
	HEVert* v2 = e->vert;
	HEVert* v3 = m->verts + (m->numverts+0);

	HEFace* f1 = e->face;
	HEFace* f2 = e->pair->face;
	HEFace* f3 = m->faces + (m->numfaces+0);
	HEFace* f4 = m->faces + (m->numfaces+1);

	//_(assert e->pair \in m->\owns)
	//_(assert e->pair->next \in m->\owns)
	//_(assert e->pair->next->next \in m->\owns)
	//_(assert e6 \in m->\owns)

	//_(assert e->pair \in m->\owns)
	//_(assert e->pair->vert \in m->\owns)
	_(assert v2 \in m->\owns)
	//_(assert v3 \in m->\owns)

	_(assert f2 \in m->\owns)
	//Was working here last, trying to get the right guiding
	//assertions here so the rest goes through!

_(unwrapping m)
{
	//Now reassign things

	_(unwrapping e1)
	{
		e1->next = e7;
		e1->pair = e9;
		e1->vert = v3;
	}

	_(unwrapping e2)
	{
		e2->face = f4;
		e2->next = e12;
	}

	_(unwrapping e3)
		e3->face = f1;
	
	_(unwrapping e4)
	{
		e4->face = f3;
		e4->next = e10;
		e4->pair = e11;
		e4->vert = v3;
	}

	_(unwrapping e5)
		e5->next = e8;
	
	_(unwrapping e6)
		e6->face = f3;
	
	_(unwrapping e7)
	{
		e7->face = f1;
		e7->next = e3;
		e7->pair = e12;
		e7->vert = e2->vert;
	}

	_(unwrapping e8)
	{
		e8->face = f2;
		e8->next = e9;
		e8->pair = e10;
		e8->vert = v3;
	}

	_(unwrapping e9)
	{
		e9->face = f2;
		e9->next = e5;
		e9->pair = e1;
		e9->vert = v1;
	}

	_(unwrapping e10)
	{
		e10->face = f3;
		e10->next = e6;
		e10->pair = e8;
		e10->vert = e5->vert;
	}

	_(unwrapping e11)
	{
		e11->face = f4;
		e11->next = e2;
		e11->pair = e4;
		e11->vert = v2;
	}

	_(unwrapping e12)
	{
		e12->face = f4;
		e12->next = e11;
		e12->pair = e7;
		e12->vert = v3;
	}

	_(unwrapping v1)
		v1->edge = e1;
	
	_(unwrapping v2)
		v2->edge = e4;

	_(unwrapping v3)
		v3->edge = e9;

	_(unwrapping f1, f2, f3, f4)
	{
		f1->edge = e3;
		f2->edge = e5;
		f3->edge = e6;
		f4->edge = e2;
	}

	m->numverts += 1;
	m->numedges += 3;
	m->numfaces += 2;
}

}