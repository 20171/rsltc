/* 
RSL Type Checker
Copyright (C) 2000 UNU/IIST

raise@iist.unu.edu
*/

#include <cstdio>
#include <cassert>

#include "RSL_map.h"


#if defined RSL_io

void input_MapToken(istream& s, MapToken& t)
{
  char c = 0;
  
  s >> c;
  switch(c){
  case '[':
    t = mt_open_map;
    break;
  case ']':
    t = mt_close_map;
    break;
  case ',':
    t = mt_enumeration_separator;
    break;
  case '+':
    s >> c;
    t = (c == '>')? mt_maps_to : mt_error;
    break;
  default:
    t = mt_error;
  }
}

#endif // RSL_io
