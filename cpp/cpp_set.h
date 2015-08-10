// This may look like C code, but it is really -*- C++ -*-
//
// @(#) CAP PROGRAMATOR (SYPRO DK) $Id: cpp_set.h,v 2.4 1994/05/19 13:30:54 she Exp $
//

#ifndef _cpp_set_h_
#define _cpp_set_h_

#if defined _base_test_
#  include "cpp_test.h"
#endif



struct cpp_sn {
  cpp_sn* next;  // address of next set element node (or 0)

  cpp_sn ();
  virtual ~cpp_sn ();

  // compare two objects for element equality
  virtual bool eq (cpp_sn*) const =0;

  // create a copy of the object
  virtual cpp_sn* cp () =0;

  // delete the element
  virtual void del () =0;

  // get an integer identification of the node
  virtual int id () {return (int) this;}
};



inline
cpp_sn::cpp_sn (): next (0)
{
#       if defined _base_test_
          cout << "\n n" << ADDR (this) << fl;
#       endif
}


inline
cpp_sn::~cpp_sn ()
{
#       if defined _base_test_
          cout << "\n ~n" << ADDR (this) << fl;
#       endif
}

struct cpp_set {
  int     count;  // number of elements
  cpp_sn* first;  // the first element

  cpp_set ();
  ~cpp_set ();

  cpp_set (const cpp_set&);

  cpp_sn*  copy () const;                  // copy contents
  void     insert (cpp_sn*);               // insert
  void     remove_first ();
  void     remove_next (cpp_sn*);
  void     clear ();                       // clear
  bool     is_subset_of (cpp_set&) const;  // subset?
  void     assign (cpp_set*, cpp_set*);    // assignment

  bool     operator[] (cpp_sn*) const;     // isin?
  bool     operator== (cpp_set*) const;    // equal?
  bool     operator<= (cpp_set*) const;    // subset?
  bool     operator<  (cpp_set*) const;    // proper subset?
  int      operator!  () const             // length
    {return count;}
};

inline
cpp_set::cpp_set (): count (0), first (0)
{
#       if defined _base_test_
          cout << "\n s()" << ADDR (this) << fl;
#       endif
}

inline
cpp_set::~cpp_set ()
{
#       if defined _base_test_
          cout << " ~s" << ADDR (this) << ":" << ADDR (first) << fl;
#       endif
  if (this)
    delete first;
}

inline
cpp_set::cpp_set (const cpp_set& set): count (set.count), first (set.copy ())
{
#       if defined _base_test_
          cout << " s(" << ADDR (this) << ":" << ADDR (&set) << ")" << fl;
#       endif
}

#endif
