// This may look like C code, but it is really -*- C++ -*-
//
// @(#) CAP PROGRAMATOR (SYPRO DK) $Id: cpp_set.cc,v 2.4 1994/05/19 13:30:47 she Exp $
//

#if defined _base_test_
#  include <iostream>
#endif

#include "cpp_set.h"

cpp_sn*
cpp_set::copy () const
{
; if (first == 0) return 0;
  cpp_sn* t = 0;
  cpp_sn* f = 0;
  for (cpp_sn* p = first; p; p = p->next) {
    cpp_sn* q = p->cp ();
#       if defined _base_test_
          cout << "^" << ADDR (q) << fl;
#       endif
    if (t)
      t->next = q;
    else
      f = q;
    t = q;
  }
  t->next = 0;
  return f;
}


void
cpp_set::insert (cpp_sn* e)
{
; if ((*this)[e]) return;
  e->next = first;
  first = e;
  ++count;
}


void
cpp_set::remove_next (cpp_sn* p)
{
  cpp_sn* d = p->next;
  p->next = p->next->next;  // yes, I know
  --count;
  d->next = 0;
  d->del ();
}


void
cpp_set::remove_first ()
{
  cpp_sn* d = first;
  --count;
  first = first->next;
  d->next = 0;
  d->del ();
}

void
cpp_set::clear ()
{
; if (count == 0) return;
  cpp_sn* pn = first;
  for (int i = count; i; --i) {
    cpp_sn* p = pn;
    pn = pn->next;
    p->del ();
  }
  count = 0;
  first = 0;
}


void
cpp_set::assign (cpp_set* x, cpp_set* y)
{
; if (x == y) return;
; if (x->first == y->first) return;
  x->clear ();
; if (y->count == 0) return;
  x->count = y->count;
  x->first = y->copy ();
  return;
}


bool
cpp_set::operator[] (cpp_sn* p) const
{
; if (count == 0) return 0;
  for (cpp_sn* pn = first; pn; pn = pn->next) {
;   if (p->eq (pn)) return 1;
  }
  return 0;
}

bool
cpp_set::is_subset_of (cpp_set& y) const
{
; if (count == 0) return 1;
  for (cpp_sn* pn = first; pn; pn = pn->next) {
#       if defined _base_test_
          cout << "?" << ADDR (pn) << fl;
#       endif
;   if (!y[pn]) return 0;
  }
#       if defined _base_test_
          cout << "." << fl;
#       endif
  return 1;
}



bool
cpp_set::operator== (cpp_set* y) const
{
#       if defined _base_test_
          cout << "\n S==" << fl;
#       endif
; if (count != y->count) return 0;
  return is_subset_of (*y);
}


bool
cpp_set::operator<= (cpp_set* y) const
{
; if (count > y->count) return 0;
  return is_subset_of (*y);
}


bool
cpp_set::operator< (cpp_set* y) const
{
; if (count >= y->count) return 0;
  return is_subset_of (*y);
}
