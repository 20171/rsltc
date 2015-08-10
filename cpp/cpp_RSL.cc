#include "cpp_RSL.h"

char cpp_RCS[] = "CAP PROGRAMATOR (SYPRO DK) $Id: cpp_RSL.cc,v 2.4 1994/05/19 13:30:00 she Exp $";

string RSL_int_to_string (int f) {
  string s;
  char res [32];
  sprintf(res, "%d", f);
  s = res;
  return s;
}

string RSL_double_to_string (double f) {
  string s;
  char res [32];
  sprintf(res, "%#G", f);
  s = res;
  return s;
}

