#version 330

layout(location = 0) in vec3 position;
layout(location = 1) in	vec3 color;

out vec4 ex_Color;

uniform mat4 ViewMatrix;
uniform mat4 ProjectionMatrix;

void main()
{
    gl_Position = ProjectionMatrix * ViewMatrix * vec4(position.x,position.y,position.z,1.0f);
	ex_Color = vec4(color.x,color.y,color.z,1.0f);
}
