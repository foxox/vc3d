#pragma once

#include "commonheader.h"

#include "model.h"

//This is something like the Controller in MVC

typedef enum ToolState ToolState;
typedef enum ToolChange ToolChange;

extern ToolState programToolState;

void selectAllToggle();

void toolTick();

void toolExtrudeBegin();
void toolExtrudeEnd();
void toolExtrudeCancel();

//void toolDelete(HEEdge*, HEFace*, HEVert*);

void toolChangeAttempt(ToolChange);
