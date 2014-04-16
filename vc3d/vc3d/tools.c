#include "tools.h"

typedef enum ToolState
{
	TS_Select,
	//Delete,
	TS_Extrude
} ToolState;

typedef enum ToolChange
{
	TC_Select,
	TC_Delete,
	TC_ExtrudeBegin='e',
	TC_ToolComplete,
	TC_ToolCancel,
	TC_SelectAllToggle='a'
} ToolChange;

ToolState programToolState = TS_Select;

char invalidstatemessage[50];
char* getToolStateString(ToolState state)
{
	sprintf_s(invalidstatemessage, 50, "Invalid or unknown ToolState: %d", state);
	switch (state)
	{
	case TS_Select: return "Select";
	//case Delete: return "Delete";
	case TS_Extrude: return "Extrude";
	default: return invalidstatemessage;
	}
}

void selectAllToggle()
{
	unsigned int i = 0;
	for (i = 0; i < 100; i++)
		selectedEdges[i] = null;
}

// Extrude Tool
// Begin Extrude
void toolExtrudeBegin(HEFace* selectedFace)
{
	programToolState = TS_Extrude;
	printf("Selected face: %d", selectedFace);
}
// End Extrude
void toolExtrudeEnd()
{

}
// Cancel Extrude
void toolExtrudeCancel()
{
	//easy, since operation doesn't change anything until End
	programToolState = TS_Select;
}

// Delete Tool
// Single stage tool, happens immediately
void toolDelete(HEEdge* selectedEdge, HEFace* selectedFace, HEVert* selectedVert)
{
	
}

// toolChangeAttempt(ToolChange)
// Connects tool change attempts to changes of program tool state
void toolChangeAttempt(ToolChange toolchange)
{
	//handle tool cancellations
	if (toolchange == TC_ToolCancel)
	{
		//Switch over all cancellable tools
		switch (programToolState)
		{
		case TS_Extrude:
			toolExtrudeCancel();
		}
	}

	//ignores bad states where tool should not be interrupted
	if (programToolState == TS_Select)
	{
		switch (toolchange)
		{
		case TC_ExtrudeBegin:		toolExtrudeBegin(selectedFaces[0]);
		case TC_SelectAllToggle:	selectAllToggle();
		}
	}
}

//// toolTick()
//// advances ToolState for program
//// connects tool in use with current selection and resets ToolState
//// when an operation completes
//void toolTick()
//{
//	//printf("toolTick() for state %s\n", getToolStateString(programToolState));
//
//	switch (programToolState)
//	{
//	case TS_Select:
//		{
//			
//		}
//	//case Delete:
//	//	{
//
//	//	}
//	case TS_Extrude:
//		{
//
//		}
//	}
//}
