#include "commonheader.h"

//#include <Windows.h>
#include "GL\glew.h"
#include "GL\freeglut.h"
#include "GL\GL.h"
#include "GL\glu.h"

#include "tools.h"
#include "model.h"

//This is something like the View in MVC

//static const HEVert vertexBufferData[] =
//{
//	{{-1.0f, -1.0f, 0.0f}, {1.0f, 0.0f, 0.0f}},
//	{{1.0f, -1.0f, 0.0f}, {0.0f, 1.0f, 0.0f}},
//	{{0.0f, 1.0f, 0.0f}, {0.0f, 0.0f, 1.0f}}
//};

static const float vertexBufferData[] =
{
	0.0f, 0.0f, 0.0f, 1.0f, 0.0f, 0.0f,
	0.0f, 1.0f, 0.0f, 0.0f, 1.0f, 0.0f,
	1.0f, 1.0f, 0.0f, 0.0f, 0.0f, 1.0f
};

GLuint vertexBuffer;
GLuint theProgram;

GLuint ProjectionMatrixUniformLocation;
GLuint ViewMatrixUniformLocation;
Mat4 ProjectionMatrix;
Mat4 ViewMatrix;

float cameraHorizontalAngle = 45.0f;
float cameraVerticalAngle = 0.0f;
//float cameraFOVY = 0.0f;
float cameraFOVX = 30.0f;
float cameraDistance = 5.0f;
float cameraZFar = 1000.0f;
float cameraZNear = 0.1f;

int windowWidth = 640;
int windowHeight = 480;


GLuint initShaderProgram()
{
	//GLenum errorCheck;

	const char shaderPathVertex[] = "vertex.shader";
	const char shaderPathFragment[] = "fragment.shader";

	// Create the shaders
	GLuint VertexShaderID = glCreateShader(GL_VERTEX_SHADER);
	GLuint FragmentShaderID = glCreateShader(GL_FRAGMENT_SHADER);

	char *strVertexShader;
	//[] = 
		//"#version 330\n"
		//"layout(location = 0) in vec4 position;\n"
		//"void main()\n"
		//"{\n"
		//"   gl_Position = position;\n"
		//"}\n";

	char *strFragmentShader;
	/*[] = 
		"#version 330\n"
		"out vec4 outputColor;\n"
		"void main()\n"
		"{\n"
		"   outputColor = vec4(1.0f, 0.0f, 1.0f, 1.0f);\n"
		"}\n";*/

	GLint Result = GL_FALSE;
	int InfoLogLength;

	//char const * VertexSourcePointer = strVertexShader;
	//char const * FragmentSourcePointer = strFragmentShader;

	GLuint ProgramID;

	FILE* file;
	long filesize;
	//size_t filebufsize;

	printf("Loading vertex shader from file...%s\n", shaderPathVertex);
	//load vertex shader file
	fopen_s(&file, shaderPathVertex, "r");
	if (file == null)
	{
		printf("Could not open vertex shader file!\n");
		return -1;
	}
	fseek(file, 0L, SEEK_END);
	filesize = ftell(file);
	//printf("filesize: %d\n", filesize);
	rewind(file);
	//filebufsize = sizeof(char) * (filesize + 1);
	strVertexShader = (char*)calloc(filesize+1, sizeof(char));
	fread_s(strVertexShader, filesize+1, sizeof(char), filesize, file);
	strVertexShader[filesize] = '\0';
	fclose(file);
	//printf(strVertexShader);
	//printf("\n");

	printf("Loading fragment shader from file...\n");
	//load fragment shader file
	fopen_s(&file, shaderPathFragment, "r");
	if (file == null)
	{
		printf("Could not open fragment shader file!\n");
		return -1;
	}
	fseek(file, 0, SEEK_END);
	filesize = ftell(file);
	rewind(file);
	//filebufsize = sizeof(char) * (filesize + 1);
	strFragmentShader = (char*)calloc(filesize+1, sizeof(char));
	fread_s(strFragmentShader, filesize+1, sizeof(char), filesize, file);
	strFragmentShader[filesize] = '\0';
	fclose(file);
	//printf(strFragmentShader);

	// Compile Vertex Shader
	printf("Compiling shader : %s\n", shaderPathVertex);
	glShaderSource(VertexShaderID, 1, &strVertexShader, null);
	glCompileShader(VertexShaderID);

	// Check Vertex Shader
	glGetShaderiv(VertexShaderID, GL_COMPILE_STATUS, &Result);
	glGetShaderiv(VertexShaderID, GL_INFO_LOG_LENGTH, &InfoLogLength);
	if (InfoLogLength > 0)
	{
		char* VertexShaderErrorMessage = (char*)malloc(sizeof(char)*(InfoLogLength+1));
		glGetShaderInfoLog(VertexShaderID, InfoLogLength, null, &VertexShaderErrorMessage[0]);
		printf("%s", &VertexShaderErrorMessage[0]);
	}

	// Compile Fragment Shader
	printf("Compiling shader : %s\n", shaderPathFragment);
	glShaderSource(FragmentShaderID, 1, &strFragmentShader , null);
	glCompileShader(FragmentShaderID);

	// Check Fragment Shader
	glGetShaderiv(FragmentShaderID, GL_COMPILE_STATUS, &Result);
	glGetShaderiv(FragmentShaderID, GL_INFO_LOG_LENGTH, &InfoLogLength);
	if (InfoLogLength > 0)
	{
		char* FragmentShaderErrorMessage = (char*)malloc(sizeof(char)*(InfoLogLength+1));
		glGetShaderInfoLog(FragmentShaderID, InfoLogLength, null, &FragmentShaderErrorMessage[0]);
		printf("%s", &FragmentShaderErrorMessage[0]);
	}


	// Link the program
	printf("Linking program...\n");
	ProgramID = glCreateProgram();
	glAttachShader(ProgramID, VertexShaderID);
	glAttachShader(ProgramID, FragmentShaderID);
	glLinkProgram(ProgramID);

	ViewMatrixUniformLocation = glGetUniformLocation(ProgramID, "ViewMatrix");
	ProjectionMatrixUniformLocation = glGetUniformLocation(ProgramID, "ProjectionMatrix");

	// Check the program
	glGetProgramiv(ProgramID, GL_LINK_STATUS, &Result);
	glGetProgramiv(ProgramID, GL_INFO_LOG_LENGTH, &InfoLogLength);
	if (InfoLogLength > 0)
	{
		char* ProgramErrorMessage = (char*)malloc(sizeof(char)*(InfoLogLength+1));
		glGetProgramInfoLog(ProgramID, InfoLogLength, null, &ProgramErrorMessage[0]);
		printf("%s", &ProgramErrorMessage[0]);
	}

	//todo: why are these deleted here?
	glDeleteShader(VertexShaderID);
	glDeleteShader(FragmentShaderID);

	printf("Shader program prepared.\n");
	return ProgramID;
}

void initVertexBuffers()
{
	// Generate 1 buffer, put the resulting identifier in vertexbuffer
	glGenBuffers(1, &vertexBuffer);
	// The following commands will talk about our 'vertexbuffer' buffer
	glBindBuffer(GL_ARRAY_BUFFER, vertexBuffer);
	// Give our vertices to OpenGL.
	glBufferData(GL_ARRAY_BUFFER, 18*sizeof(GL_FLOAT), vertexBufferData, GL_STATIC_DRAW);

	glVertexAttribPointer(
	   0,					// attribute in layout
	   3,					// size
	   GL_FLOAT,			// type
	   GL_FALSE,			// normalized?
	   6*sizeof(GL_FLOAT),					// stride
	   0					// array buffer offset
	);
	glVertexAttribPointer(1,3,GL_FLOAT,GL_FALSE,6*sizeof(float),(GLvoid*)(sizeof(GL_FLOAT)*3));

	glEnableVertexAttribArray(0);
	glEnableVertexAttribArray(1);
}

int init_resources()
{
	initVertexBuffers();

	glClearColor(0,0,0,1);
	//ProjectionMatrix = Mat4Transpose(Mat4GenPerspectiveProjection(cameraFOVX, (float)windowWidth/(float)windowHeight, cameraZNear, cameraZFar));
	ProjectionMatrix = Mat4GenPerspectiveProjection(cameraFOVX, (float)windowWidth/(float)windowHeight, cameraZNear, cameraZFar);

	theProgram = initShaderProgram();
	if (theProgram == -1)
		return 0;

	return 1;
}

void free_resources()
{
	glDisableVertexAttribArray(0);
	glDisableVertexAttribArray(1);

	glDeleteProgram(theProgram);

	//todo: cleanup resources
}

void refreshShaderProgram()
{
	glDeleteProgram(theProgram);
	theProgram = initShaderProgram();
}

float omega=0.0f;
void onDisplay(void)
{
	//printf("d");
	
	omega += 0.005f;

	glClear(GL_DEPTH_BUFFER_BIT | GL_COLOR_BUFFER_BIT);

	glUseProgram(theProgram);

	glBindBuffer(GL_ARRAY_BUFFER, vertexBuffer);
	glBufferData(GL_ARRAY_BUFFER, 18*sizeof(GL_FLOAT), vertexBufferData, GL_DYNAMIC_DRAW);

	//ViewMatrix = Mat4Transpose(Mat4GenTranslate(3.0f*sinf(omega), 0, 0));
	//ViewMatrix = Mat4GenLookAtTransform(Vec3GenVec3(0,0,5), Vec3GenVec3(0,0,0), Vec3GenVec3(0,1,0));
	ViewMatrix = Mat4GenLookAtTransform(Vec3GenVec3(cameraDistance*cosf(omega),cameraDistance*sinf(omega),cameraDistance), Vec3GenVec3(0.0f,0.0f,0.0f), Vec3GenVec3(0,0,1));

	glUniformMatrix4fv(ProjectionMatrixUniformLocation, 1, GL_TRUE, (GLfloat*)&ProjectionMatrix.mat[0][0]);
	glUniformMatrix4fv(ViewMatrixUniformLocation, 1, GL_FALSE, (GLfloat*)&ViewMatrix.mat[0][0]);
 
	// Draw the triangle !
	glDrawArrays(GL_TRIANGLES, 0, 3);
	// Starting from vertex 0; 3 vertices total -> 1 triangle

	glutSwapBuffers();
	glutPostRedisplay();
}

void onKeyboard(unsigned char key, int x, int y)
{
	printf("keyboard: %d, %d, %d\n", key, x, y);
	//27 is escape
	switch (key)
	{
	case 'q':	glutLeaveMainLoop();
	case 's':	refreshShaderProgram();
	default:	toolChangeAttempt(key);
	}
}

void onKeyboardSpecial(int key, int x, int y)
{
	printf("keyboard: %d, %d, %d\n", key, x, y);
}

//void mainToolTick(int val)
//{
//	toolTick();
//	glutTimerFunc(2000, mainToolTick, 0);
//}

void onMouseMove(int x, int y)
{
	//printf("mouse: %d,%d\n", x, y);
	glutWarpPointer(windowWidth / 2, windowHeight / 2);
}

void onMouseClick(int x, int y, int a, int b)
{

}

void onMouseWheel(int x, int y, int a, int b)
{

}

int main(int argc, char** argv)
{
	GLenum glew_status;

	/*Mat4 test;
	uint i = 0;
	float* matr;

	Mat4ZeroOut(&test);
	test.mat[0][0] = 1;
	test.mat[1][0] = 2;
	test.mat[2][0] = 3;
	test.mat[3][0] = 4;
	test.mat[0][1] = 5;
	printf("%f, ", *test.mat[0]);
	printf("%f, ", *test.mat[1]);
	printf("%f, ", *test.mat[2]);
	printf("%f, ", *test.mat[3]);
	printf("\n");
	matr = &test.mat[0][0];
	printf("%f, ", matr[0]);
	printf("%f, ", matr[1]);
	printf("%f, ", matr[2]);
	printf("%f, ", matr[3]);*/

	//for (i = 0; i < 16; i++)
		//printf("%d, ", test.mat[i]);
	//printf("\n");
	//for (i = 0; i < 16; i++)
		//printf("%f, ", test.mat[i]);
	//printf("mat num %f %f %f", test.mat[1][3], *(test.mat+13), *((float*)test.mat+13));

	Mesh somemesh;
	//MeshInitMesh(&somemesh);

	glutInit(&argc, argv);
	glutInitDisplayMode(GLUT_RGBA|GLUT_DOUBLE|GLUT_DEPTH);
	glutInitWindowSize(windowWidth, windowHeight);
	glutCreateWindow("VC3D");
 
	/* Extension wrangler initialising */
	glew_status = glewInit();
	if (glew_status != GLEW_OK)
	{
		fprintf(stderr, "Error: %s\n", glewGetErrorString(glew_status));
		return EXIT_FAILURE;
	}

	printf("Resource initialization...\n");
 
	if (1 == init_resources())
	{
		printf("Initialization complete.\n");
		printf("Setting input callbacks.\n");
		/* We can display it if everything goes OK */
		glutDisplayFunc(onDisplay);
		glutKeyboardFunc(onKeyboard);
		glutSpecialFunc(onKeyboardSpecial);
		glutMotionFunc(onMouseMove);
		glutMouseFunc(onMouseClick);
		glutMouseWheelFunc(onMouseWheel);
		//mainToolTick(0);

		glutReshapeFunc(null);

		//glutSetCursor(GLUT_CURSOR_NONE);

		glutMainLoop();
	}
 
	printf("Shutting down program...\n");
	/* If the program exits in the usual way,
	free resources and exit with a success */
	free_resources();

	printf("Seeya!");
	return 0;
}


