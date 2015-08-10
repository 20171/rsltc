/* 
RSL Type Checker
Copyright (C) 2000 UNU/IIST

raise@iist.unu.edu
*/

#include "RSL_set.h"



#ifdef RSL_io

void input_SetToken (istream& s, SetToken& t)
{
    char c = 0;

    s >> c;
    switch(c)
    {
        case '{':
            t = st_open_set;
            break;
        case '}':
            t = st_close_set;
            break;
        case ',':
            t = st_enumeration_separator;
            break;
        default:
            t = st_error;
    }
}

#endif                                            // RSL_io
