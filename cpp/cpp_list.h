// This may look like C code, but it is really -*- C++ -*-
//
// @(#) CAP PROGRAMATOR (SYPRO DK) $Id: cpp_list.h,v 2.4 1994/05/19 13:30:35 she Exp $
//

#ifndef _cpp_list_h_
#define _cpp_list_h_

#if defined _base_test_
#  include "cpp_test.h"
#endif



struct cpp_ln {
  int     ref;   // reference count
  cpp_ln* next;  // address of next list node (or 0)

  cpp_ln ();
  virtual ~cpp_ln ();

  void up ();
  void down ();

  virtual bool     eq (cpp_ln*) const =0;
  virtual cpp_ln* cp () =0;
  virtual int     id ()
    {return (int) this;}
};

inline
cpp_ln::cpp_ln (): ref (1), next (0)
{
#       if defined _base_test_
          cout << " ln()" << ADDR (this) << "|0|" << fl;
#       endif
}


inline
cpp_ln::~cpp_ln ()
{
#       if defined _base_test_
          cout << " ~ln()" << ADDR (this);
          if (this)
            cout << "|" << ref << "|" << fl;
#       endif
  if (this && ref)
    down ();
}


inline void
cpp_ln::up ()
{
#       if defined _base_test_
          cout << " ln+(" << ADDR (this) << ")";
          if (this)
            cout << "|" << ref << "|" << fl;
#       endif
  if (this)
    ++ref;
}

struct cpp_list {
  cpp_ln* first;

  cpp_list ();
  cpp_list (cpp_ln*);
  cpp_list (cpp_ln*, cpp_list*);
  cpp_list (cpp_list&);

  ~cpp_list ();

  cpp_ln& operator[] (int) const;               // n'th element
  bool    operator== (const cpp_list&) const;   // equal?
  cpp_ln* operator+  (const cpp_list&) const;   // concatenation
  int     operator!  () const;                  // length
};

inline
cpp_list::cpp_list (): first (0)
{
#       if defined _base_test_
          cout << " l()" << ADDR (this) << fl;
#       endif
}


inline
cpp_list::cpp_list (cpp_ln* h): first (h)
{
#       if defined _base_test_
          cout << " l(" << ADDR (this) << ")(" << ADDR (h) << ")" << fl;
#       endif
}


inline
cpp_list::cpp_list (cpp_list& x): first (x.first)
{
  first->up ();
#       if defined _base_test_
          cout << " l&(" << ADDR (this)
               << ")(" << ADDR (&x) << "<" << ADDR (first) << ">)" << fl;
#       endif
}


inline
cpp_list::~cpp_list ()
{
#       if defined _base_test_
          cout << " ~l()" << ADDR (this) << "<" << ADDR (first) << ">";
          if (first)
            cout << "|" << first->ref << "|" << fl;
#       endif
  first->down ();
}


#endif
