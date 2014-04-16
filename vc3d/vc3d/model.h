#pragma once

#include "commonheader.h"

#include "mesh.h"

#include "scenegraph.h"

//This is something like the Model in MVC

//This file is for global scene variables
//This might be made into some kind of "Model"/"World" module stuff in a more complete implementation

#define MAXSELECTED 100

extern HEEdge *selectedEdges[];
extern HEVert *selectedVerts[];
extern HEFace *selectedFaces[];
//TODO: do I need values here to record how much of the arrays are in use?

extern SGNode* scene;

extern void initSelected();
