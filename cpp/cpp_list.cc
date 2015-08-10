// This may look like C code, but it is really -*- C++ -*-
//
// @(#) CAP PROGRAMATOR (SYPRO DK) $Id: cpp_list.cc,v 2.4 1994/05/19 13:30:27 she Exp $
//
// Edited by CWG, UNU/IIST, December 1999, to conform with ANSI 
// scoping rules for `for' statements (for g++ compiler)


#if defined _base_test_  
#  include "cpp_test.h"
#endif

#include "cpp_list.h"


void
cpp_ln::down ()
{
#       if defined _base_test_
          cout << " ln-(" << ADDR (this);
          if (this) {
            cout << "|" << ref << "|";
            cpp_ln* p = next;
            while (p) {
              cout << ADDR (p) << "|" << p->ref << "|";
              p = p->next;
            }
          }
          cout << ")" << fl;
#       endif
; if (this == 0) return;
  cpp_ln* p = this;
  while (p && --p->ref == 0) {
    cpp_ln* n = p->next;
#       if defined _base_test_
          cout << "{" << ADDR (p) << "}" << fl;
#       endif
    delete p;
    p = n;
  }
}

cpp_list::cpp_list (cpp_ln* h, cpp_list* t): first (h)
{
  first->next = t->first;
  t->first->up ();
#       if defined _base_test_
          cout << " l(" << ADDR (this)
               << ")(" << ADDR (h) << "," << ADDR (t->first) << ")" << fl;
#       endif
}



cpp_ln&
cpp_list::operator[] (int n) const
{
// CWG: Scope of p changed to conform with ANSI scoping rules
  cpp_ln* p;

  for (p = first; --n > 0; p = p->next) ;
  return *p;
}


bool
cpp_list::operator== (const cpp_list& b) const
{
  cpp_ln* l = first;
  cpp_ln* r = b.first;
  for (;;) {
;   if (l == 0) return r == 0 ? 1 : 0;
;   if (r == 0) return 0;
;   if (l == r) return 1;
;   if (!l->eq (r)) return 0;
    l = l->next;
    r = r->next;
  }
}

cpp_ln*
cpp_list::operator+ (const cpp_list& y) const
{
  cpp_ln *a = first;
  cpp_ln *b = y.first;

  if (a) {
    cpp_ln *u = a->cp ();
    cpp_ln *v = u;
    for (a = a->next; a; a = a->next) {
      cpp_ln *n = a->cp ();
      v->next = n;
      v = n;
    }
    b->up ();
    v->next = b;
;   return u;
  }
  if (b) {
    b->up ();
;   return b;
  }
  return first;
}


int
cpp_list::operator! () const
{
  int l = 0;
  for (cpp_ln* p = first; p; p = p->next) ++l;
  return l;
}
