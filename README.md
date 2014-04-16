vc3d
====

3d mesh library written in C and verified with VCC.

See my blog for this project: http://vc3d.tumblr.com/

I have been working on this for about a year but neglected to create a public repository because there had not been enough progress made for the code to be useful to anyone but me. I believe that the code is approaching a usable form now so I am making this repository in anticipation.

I am not a C programmer and never was, so I have no idea whether this code follows typical C programming styles. Where a C++ (or any OO language) class would be, I have structs. "Member"-like methods have the class/struct name prefixed on them to differentiate them from other functions. They take at least an input of a pointer to the associated type and I name all such inputs "dis", to parallel "this". I would use "this" directly, but Visual Studio's UI reacts oddly sometimes, treating the code as if it were C++ code. In some places, I have begun using preprocessor directives to make the code also compile as C++ with classes, but this is not complete.

GPLv3 license for now, but I am willing to issue it under different licenses - please contact me.
