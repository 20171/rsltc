/* 
RSL Type Checker
Copyright (C) 2000 UNU/IIST

raise@iist.unu.edu
*/

#ifndef _RSL_list_h
#define _RSL_list_h

#if defined _list_test_
#  include "cpp_test.h"
#endif

#if defined(_RSL_list_output_) || defined(RSL_io)
#  include <iostream>
#endif

#include "cpp_list.h"
#include "RSL_set.h"

template<class E>
struct RSLListNode: cpp_ln
{
    E hd;                                         // element value

    RSLListNode (const E&);                          // constructor
    virtual ~RSLListNode ();                         // destructor

    bool eq (cpp_ln*) const;                       // equality test
    cpp_ln* cp ();                                // node copy
};

template<class E>
inline RSLListNode<E>::~RSLListNode ()
{
    #       if defined _list_test_
    cout << " ~<C>_n(" << ADDR (this);
    if (this)
        cout << "|" << ref << "|";
    #         if defined _int_
    cout << "[" << hd << "]";
    #         endif
    cout << ")" << fl;
    #       endif
    down ();
}


template<class E>
inline bool RSLListNode<E>::eq (cpp_ln* y) const
{
    #       if defined _list_test_
    cout << " <C>_n::eq(" << ADDR (this);
    #         if defined _int_
    cout << "[" << hd << "]";
    #         endif
    cout << "," << ADDR (y);
    #         if defined _int_
    cout << "[" << ((RSLListNode*) y)->hd << "]";
    #         endif
    cout << ")" << fl;
    #       endif
    return hd == ((RSLListNode*) y)->hd;
}


template<class E> struct RSLList;
template<class E> bool RSL_list_empty(const RSLList<E>& x);
template<class E> int len (const RSLList<E>& x);
template<class E> E hd (const RSLList<E>& x);
template<class E> RSLList<E> tl (const RSLList<E>& x);
template<class E> RSLList<E> tl_n (const RSLList<E>& x, const int n);
template<class E> bool isin (const E&, const RSLList<E>&);

template<class E> bool alll (bool (*pred)(const E), const RSLList<E>&);
template<class E> bool alll (bool (*pred)(const E&), const RSLList<E>&);
template<class E> bool existsl (bool (*pred)(const E), const RSLList<E>&);
template<class E> bool existsl (bool (*pred)(const E&), const RSLList<E>&);
template<class E> bool exists1l (bool (*pred)(const E), const RSLList<E>&);
template<class E> bool exists1l (bool (*pred)(const E&), const RSLList<E>&);
template<class E> E RSL_choosel (bool (*pred)(const E), const RSLList<E>&);
template<class E> E RSL_choosel (bool (*pred)(const E&), const RSLList<E>&);

template<class E> RSLSet<E>& elems (const RSLList<E>&);
template<class E> RSLSet<int>& inds (const RSLList<E>&);

#if defined _RSL_list_output_
template<class E> ostream& operator<< (ostream&, const RSLList<E>&);
#endif

template<class E> string RSL_to_string (const RSLList<E>&);

# if defined RSL_io
template<class E> ostream& operator<< (ostream&, const RSLList<E>&);
template<class E> istream& operator>> (istream&, RSLList<E>&);
#endif

template<class E>
struct RSLList: cpp_list
{
    RSLList ();                                      // constructors
    RSLList (const E&);
    RSLList (const E&, const RSLList&);
    RSLList (const RSLList&);
    ~RSLList ();                                     // destructors

    RSLList (cpp_ln*);                               // conversion
    const RSLList& operator= (const RSLList&);          // assignment

    // user operators
    bool operator== (const RSLList&) const;
    bool operator!= (const RSLList&) const;

    E operator[] (int) const;
    RSLList operator+ (const RSLList&) const;

  //    friend int len<> (const RSLList&);
  //    friend E hd<> (const RSLList&);
  //    friend RSLList tl<> (const RSLList&);
  //    friend RSLList tl_n<> (const RSLList&, const int n);
  //    friend bool isin <> (const E&, const RSLList&);

  //    friend bool all<> (bool (*pred)(const E), const RSLList&);
  //    friend bool all<> (bool (*pred)(const E&), const RSLList&);
  //    friend bool exists<> (bool (*pred)(const E), const RSLList&);
  //    friend bool exists<> (bool (*pred)(const E&), const RSLList&);
  //    friend bool exists1<> (bool (*pred)(const E), const RSLList&);
  //    friend bool exists1<> (bool (*pred)(const E&), const RSLList&);
  //    friend E RSL_choose<> (bool (*pred)(const E), const RSLList&);
  //    friend E RSL_choose<> (bool (*pred)(const E&), const RSLList&);

  //    friend RSLSet<E>& elems <> (const RSLList<E>&);
  //    friend RSLSet<int>& inds <> (const RSLList<E>&);

  //    #if defined _RSL_list_output_
  //    friend ostream& operator<< <> (ostream&, const RSLList<E>&);
  //    #endif

  //    friend string RSL_to_string<> (const RSLList&);

  //    # if defined RSL_io
  //    friend ostream& operator<< <> (ostream&, const RSLList<E>&);
  //    friend istream& operator>> <> (istream&, RSLList<E>&);
  //    #endif

};

template<class E>
inline RSLList<E>::RSLList (): cpp_list ()
{
    #       if defined _list_test_
    cout << " RSLList()"
        << ADDR (this) << "<" << ADDR (first) << ">" << fl;
    #       endif
}


template<class E>
inline RSLList<E>::RSLList (const RSLList& x): cpp_list ((cpp_list&) x)
{
    #       if defined _list_test_
    cout << " RSLList(&" << ADDR (&x) << ")" << ADDR (this)
        << "<" << ADDR (first) << ">" << fl;
    // following statement (with proper include) causes a g++ compiler crash
    //          assert (first == &x);
    #       endif
}


template<class E>
inline RSLList<E>::~RSLList ()
{
    #       if defined _list_test_
    cout << "\n ~RSLList()" << ADDR (this)
        << "<" << ADDR (first) << ">";
    if (first) cout << "|" << first->ref << "|";
    #         if defined _int_
    if (first)
        cout << "[" << ((RSLList_node*) first)->hd << "]";
    #         endif
    cout << "\n   " << fl;
    #       endif
    // this is no good! first->down (); WHY NOT ???
}


template<class E>
inline RSLList<E>::RSLList (cpp_ln *p)
{
    first = (RSLListNode<E>*) p;
}


template<class E>
inline bool RSLList<E>::operator== (const RSLList& y) const
{
    return (*(cpp_list*) this) == (*(cpp_list*) &y);
}


template<class E>
inline bool RSLList<E>::operator!= (const RSLList& y) const
{
    return !(*this == y);
}


template<class E>
inline E RSLList<E>::operator[] (int n) const
{
  //    return ((RSLListNode<E>&) (cpp_list::operator[] (n))).hd;
  // safer code:
  cpp_ln* pn;
  int c = n;
  for (pn = first; (pn && (--c > 0)); pn = pn->next);
  if (pn == 0) {
    string s = "List " + RSL_to_string((RSLList<E>)(*this)) + " applied to non-index " + RSL_to_string(n);
    RSL_fail(s);
  }
  return ((RSLListNode<E>*) pn)->hd;
}


template<class E>
inline RSLList<E> RSLList<E>::operator+ (const RSLList<E>& y) const
{
    return cpp_list::operator+ ((cpp_list&) y);
}

template<class E> 
inline bool RSL_list_empty(const RSLList<E>& x) {
  return (x.first==0);
}

template<class E>
inline int len (const RSLList<E>& x)
{
    return ! (cpp_list&) x;
}


template<class E>
inline E hd (const RSLList<E>& x)
{
  if (x.first==0){
    RSL_fail("Head of empty list");
  }
  return x[1];
}


template<class E>
inline RSLList<E> tl (const RSLList<E>& x)
{
  if (x.first==0){
  RSL_fail("Tail of empty list");
  }
  x.first->next->up ();
  return (RSLList<E>) x.first->next;
}

template<class E>
inline RSLList<E> tl_n (const RSLList<E>& x, const int n)
{
  int l = n;
  cpp_ln *pn;
  for (pn = x.first; (pn && l > 0); pn = pn->next) {
    l--;
  }
  if (l > 0) {
    RSL_fail("Tail of empty list");
  }
  pn->up ();
  return (RSLList<E>) pn;
}

template<class E>
bool isin (const E& e, const RSLList<E>& l) {
  bool result = false;
  for (cpp_ln *pn = l.first; (pn && !result); pn = pn->next){
    result = ((E&) e == ((RSLListNode<E>*) pn)->hd);
  }
  return result;
}

template<class E>
bool alll (bool (*pred)(const E), const RSLList<E>& l) {
  bool result = true;
  for (cpp_ln* pn = l.first; (pn && result); pn = pn->next) {
    result = (*pred)(((RSLListNode<E>*) pn)->hd);
  }
  return result;
}

template<class E>
bool alll (bool (*pred)(const E&), const RSLList<E>& l) {
  bool result = true;
  for (cpp_ln* pn = l.first; (pn && result); pn = pn->next) {
    result = (*pred)(((RSLListNode<E>*) pn)->hd);
  }
  return result;
}

template<class E>
bool existsl (bool (*pred)(const E), const RSLList<E>& l) {
  bool result = false;
  for (cpp_ln* pn = l.first; (pn && !result); pn = pn->next) {
    result = (*pred)(((RSLListNode<E>*) pn)->hd);
  }
  return result;
}

template<class E>
bool existsl (bool (*pred)(const E&), const RSLList<E>& l) {
  bool result = false;
  for (cpp_ln* pn = l.first; (pn && !result); pn = pn->next) {
    result = (*pred)(((RSLListNode<E>*) pn)->hd);
  }
  return result;
}

template<class E> 
bool exists1l (bool (*pred)(const E), const RSLList<E>& l) {
  E candidate;
  int count = 0;
  for (cpp_ln* pn = l.first; pn && (count < 2); pn = pn->next) {
    if ((*pred)(((RSLListNode<E>*) pn)->hd)) {
      if (count == 0) {
	candidate = ((RSLListNode<E>*) pn)->hd;
	count = 1;
      }
      else if (candidate != ((RSLListNode<E>*) pn)->hd) count++;
    }
  }
  return (count==1);
}

template<class E>
bool exists1l (bool (*pred)(const E&), const RSLList<E>& l) {
  E candidate;
  int count = 0;
  for (cpp_ln* pn = l.first; pn && (count < 2); pn = pn->next) {
    if ((*pred)(((RSLListNode<E>*) pn)->hd)) {
      if (count == 0) {
	candidate = ((RSLListNode<E>*) pn)->hd;
	count = 1;
      }
      else if (candidate != ((RSLListNode<E>*) pn)->hd) count++;
    }
  }
  return (count==1);
}
  
template<class E>
E RSL_choosel (bool (*pred)(const E), const RSLList<E>& l) {
  bool found = false;
  E r;
  for (cpp_ln* p = l.first; (p && !found); p = p->next) {
    r = ((RSLListNode<E>*) p)->hd;
    if ((*pred)(r)) {
      found = true;
    }
  }
  if (!found) RSL_fail("Choose from empty list");
  return r;
}

template<class E>
E RSL_choosel (bool (*pred)(const E&), const RSLList<E>& l) {
  bool found = false;
  E r;
  for (cpp_ln* p = l.first; (p && !found); p = p->next) {
    r = ((RSLListNode<E>*) p)->hd;
    if ((*pred)(r)) {
      found = true;
    }
  }
  if (!found) RSL_fail("Choose from empty list");
  return r;
}


template<class E>
RSLListNode<E>::RSLListNode (const E& h)
{
    hd = (E&) h;

    #       if defined _list_test_
    cout << " RSLList_n(" << ADDR (this);
    #         if defined _int_
    cout << "[" << hd << "]";
    #         endif
    cout << ")" << fl;
    #       endif
}


template<class E>
cpp_ln* RSLListNode<E>::cp ()
{
    return new RSLListNode<E> (hd);
}


template<class E>
RSLList<E>::RSLList (const E& hd): cpp_list (new RSLListNode<E> (hd))
{
    #       if defined _list_test_
    cout << " RSLList(" << ADDR (this);
    #         if defined _int_
    cout << "[" << hd << "]";
    #         endif
    cout << ")" << fl;
    #       endif
}


template<class E>
RSLList<E>::RSLList (const E& hd, const RSLList& tl)
: cpp_list (new RSLListNode<E> (hd), (cpp_list*) &tl)
{
    #       if defined _list_test_
    cout << " RSLList(" << ADDR (this);
    #         if defined _int_
    cout << "[" << hd << "]";
    #         endif
    cout << "," << ADDR (&tl) << ")" << fl;
    #       endif
}


template<class E>
const RSLList<E>& RSLList<E>::operator= (const RSLList& x)
{
    #       if defined _list_test_
    cout << " RSLList=(" << ADDR (this) << "<" << ADDR (first) << ">"
        << "," << ADDR (&x) << "<" << ADDR (x.first) << ">)" << fl;
    #       endif
    x.first->up ();
    first->down ();
    first = x.first;
    return *this;
}


template<class E>
RSLSet<E>& elems (const RSLList<E>& x)
{
    RSLSet<E> *ps = new RSLSet<E> ();

    if (x.first)
    {
        cpp_ln *pn = x.first;
        for ( ; pn; pn = pn->next)
        {
            ps->insert (new RSLSetNode<E> (((RSLListNode<E>*) pn)->hd));
        }
    }
    return *ps;
}


template<class E>
RSLSet<int>& inds (const RSLList<E>& x)
{
    RSLSet<int> *ps = new RSLSet<int> ();

    if (x.first)
    {
        int l = len (x);
        for (int i = 1; i <= l; ++i)
        {
            ps->insert (new RSLSetNode<int> (i));
        }
    }
    return *ps;
}


#if defined _RSL_list_output_

template<class E>
ostream& operator<< (ostream& s, const RSLList<E>& list)
{
    #       if defined _list_test_
    s << "(" << ADDR (&list) << ")";
    #       endif
    s << "<.";
    cpp_ln* p = list.first;
    if (p)
    {
        for (;;)
        {
            #       if defined _list_test_
            s << "(" << ADDR (p) << ")";
            #       endif
            s << ((RSLListNode<E>*) p)->hd;
            #       if defined _list_test_
            s << "(" << p->ref << "," << ADDR (p->next) << ")";
            #       endif
            p = p->next;
            ; if (p == 0) break;
            s << ",";
        }
    }
    return s << ".>";
}
#endif // _RSL_list_output_


template<class E>
string RSL_to_string (const RSLList<E>& list) {
  string s = "<.";
  cpp_ln* p = list.first;
  while(p) {
    s += RSL_to_string(((RSLListNode<E>*) p) -> hd);
    p = p -> next;
    if (p) s += ',';
  }
  s += ".>";
  return s;
}

#if defined RSL_io


template<class E>
ostream& operator<< (ostream& s, const RSLList<E>& list)
{
    s << "<.";
    cpp_ln* p = list.first;
    while (p)
    {
        s << ((RSLListNode<E>*) p) -> hd;
        p = p -> next;
        if (p) s << ",";
    }
    s << ".>";
    return s;
}


enum ListToken {lt_error, lt_open_list, lt_close_list, lt_enumeration_separator, lt_range_separator};
//                     <.          .>                 ,                   ..

void input_ListToken (istream&, ListToken&);
template<class E> static void input_elements (istream& , RSLList<E>&);
template<class E> static void input_enumeration (istream&, RSLList<E>&);

template<class E>
istream& operator>> (istream& s, RSLList<E>& list)
{
  char c;
  E elem1;
  RSLList<E> temp;

  s >> c;
  if (c != '<') {s.clear(ios::badbit); return s;}
  s >> c;
  if (c != '.') {s.clear(ios::badbit); return s;}
  if (s.peek() == '.') { // empty list
    s >> c;
    s >> c;
    if (c == '>') {
      if (s) list = RSLList<E>();
      return s;
    }
    else {s.clear(ios::badbit); return s;}
  }
  s >> elem1;
  if (!(s)) {s.clear(ios::badbit); return s;}
  s >> c;
  switch(c)
    {
    case ',':
      input_enumeration(s, temp);
      if (s) temp = RSLList<E>(elem1, temp);
      else {s.clear(ios::badbit); return s;}
      break;
    case '.':
      s >> c;
      switch(c)
	{
	case '.':
	  E elem2;
	  s >> elem2;
	  if (!(s)) {s.clear(ios::badbit); return s;}
	  s >> c;
	  if (c != '.') {s.clear(ios::badbit); return s;}
	  s >> c;
	  if (c != '>') {s.clear(ios::badbit); return s;}
	  temp = RSLList<E>();
	  if (elem1 <= elem2)
	    for (int elem = elem2; elem1 <= elem; elem--)
	      temp = RSLList<E>(elem, temp);
	  break;
	case '>':
	  temp = RSLList<E>(elem1);
	  break;
	default: {s.clear(ios::badbit); return s;}
	}
      break;
    default: {s.clear(ios::badbit); return s;}
    }
  if (s) list = temp;
  else cout << "stream is void\n";
  return s;
}
	  
template<class E>
void input_enumeration (istream& s, RSLList<E>& list)
{
    E elem;
    char c;
    RSLList<E> temp;

    s >> elem;
    if (s)
    {
        s >> c;
        if (s)
	  switch(c)
	    {
	    case ',':
	      input_enumeration(s, temp);
	      if (s) list = RSLList<E>(elem, temp);
	      break;
	    case '.':
	      s >> c;
	      if (s && c == '>') list = RSLList<E>(elem);
	      else s.clear(ios::badbit);
	      break;
	    default: s.clear(ios::badbit);
	    }
	else
            s.clear(ios::badbit);
    }
    else
        s.clear(ios::badbit);
}
	      
	    
	  
	  
	  
  
  



#endif // RSL_io

#endif // _RSL_list_h
