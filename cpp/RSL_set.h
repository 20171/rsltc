/* 
RSL Type Checker
Copyright (C) 2000 UNU/IIST

raise@iist.unu.edu
*/

#ifndef _RSL_set_h
#define _RSL_set_h

#include "cpp_set.h"
#include <string>
using namespace std;

#if defined(_RSL_set_output_) || defined(RSL_io)
#include <iostream>
#endif

// Nodes in the list that represents elements of a non-empty set.
//

template<class E>
struct RSLSetNode: cpp_sn
{
    E hd;                                         // element value

    RSLSetNode();                                    // constructors
    RSLSetNode(const E &);
    virtual inline ~ RSLSetNode();                   // destructor

    inline bool eq(cpp_sn *y) const;               // equality test
    cpp_sn *cp();                                 // node copy
    void del();                                   // node deletion
};

template<class E> inline RSLSetNode<E>::RSLSetNode (): cpp_sn ()
{
}


template<class E> inline  RSLSetNode<E>::~RSLSetNode ()
{
    #   ifdef _set_test_
    cout << " ~S" << ADDR (this);
    #      ifdef _int_
    cout << "[" << hd << "]";
    #      endif
    cout << fl;
    #   endif
}


template<class E> inline bool RSLSetNode<E>::eq (cpp_sn *y) const
{
    #   ifdef _set_test_
    cout << " eq(" << ADDR (this) << "," << ADDR (y) << ")";
    #      ifdef _int_
    cout << "[" << hd << "," << ((RSLSetNode*) y)->hd << "]";
    #      endif
    cout << fl;
    #   endif
    return hd == ((RSLSetNode*) y)->hd;
}


template<class E> struct RSLSet;
template<class E> bool RSL_set_empty (const RSLSet<E>&);
template<class E> int card (const RSLSet<E>&);
template<class E> bool isin (const E&, const RSLSet<E>&);

template<class E> bool alls (bool (*pred)(const E), const RSLSet<E>&);
template<class E> bool alls (bool (*pred)(const E&), const RSLSet<E>&);
template<class E> bool existss (bool (*pred)(const E), const RSLSet<E>&);
template<class E> bool existss (bool (*pred)(const E&), const RSLSet<E>&);
template<class E> bool exists1s (bool (*pred)(const E), const RSLSet<E>&);
template<class E> bool exists1s (bool (*pred)(const E&), const RSLSet<E>&);
template<class E> E RSL_chooses (bool (*pred)(const E), const RSLSet<E>&);
template<class E> E RSL_chooses (bool (*pred)(const E&), const RSLSet<E>&);

#ifdef _RSL_set_output_
template<class E> ostream& operator<< (ostream&, const RSLSet<E>&);
#endif

template<class E> string RSL_to_string (const RSLSet<E>&);

#ifdef RSL_io
template<class E> ostream& operator<< (ostream&, const RSLSet<E>&);
template<class E> istream& operator>> (istream&, RSLSet<E>&);
#endif

template<class E>
struct RSLSet : cpp_set
{
    RSLSet ();                                       // constructors
    RSLSet (const E&);
    RSLSet (const E&, const RSLSet&);
    RSLSet (const RSLSet&);
    ~RSLSet ();                                      // destructors

    RSLSet (cpp_sn*);                                // conversion
    RSLSet (cpp_sn*, const int i);                   // conversion
    const RSLSet& operator= (const RSLSet&);            // assignment

    // user operators
    bool operator== (const RSLSet&) const;
    bool operator<= (const RSLSet&) const;
    bool operator>= (const RSLSet&) const;
    bool operator!= (const RSLSet&) const;
    bool operator<  (const RSLSet&) const;
    bool operator>  (const RSLSet&) const;

    RSLSet operator* (const RSLSet&) const;            // intersection
    RSLSet operator+ (const RSLSet&) const;            // union
    RSLSet operator% (const RSLSet&) const;            // difference
    bool operator[] (const E&) const;              // is item in set?

  //    friend int card<> (const RSLSet&);

  //    friend bool isin<> (const E&, const RSLSet&);

  //    friend bool all<> (bool (*pred)(const E), const RSLSet&);
  //    friend bool all<> (bool (*pred)(const E&), const RSLSet&);
  //    friend bool exists<> (bool (*pred)(const E), const RSLSet&);
  //    friend bool exists<> (bool (*pred)(const E&), const RSLSet&);
  //    friend bool exists1<> (bool (*pred)(const E), const RSLSet&);
  //    friend bool exists1<> (bool (*pred)(const E&), const RSLSet&);
  //    friend E RSL_choose<> (bool (*pred)(const E), const RSLSet&);
  //    friend E RSL_choose<> (bool (*pred)(const E&), const RSLSet&);

  //    #ifdef _RSL_set_output_
  //    friend ostream& operator<< <> (ostream&, const RSLSet&);
  //    #endif

  //    friend string RSL_to_string<> (const RSLSet&);

  //    #ifdef RSL_io
  //    friend ostream& operator<< <> (ostream&, const RSLSet&);
  //    friend istream& operator>> <> (istream&, RSLSet&);
  //    #endif

};

template<class E>
inline RSLSet<E>::RSLSet ()
{
    count = 0;
    first = 0;
}


template<class E>
inline RSLSet<E>::~RSLSet ()
{
    clear ();
}


template<class E>
inline RSLSet<E>::RSLSet (cpp_sn *p)
{
  int i = 0;
  for (cpp_sn *pn = p; pn; pn = pn->next) {
    i++;
  }
  count = i;
  //cout << "Count c is " << count << endl;
  first = (RSLSetNode<E>*) p;
}


template<class E>
inline RSLSet<E>::RSLSet (cpp_sn *p, const int i)
{
  count = i;
  //cout << "Count c is " << count << endl;
  first = (RSLSetNode<E>*) p;
}


template<class E>
inline bool RSLSet<E>::operator== (const RSLSet& y) const
{
    return *(cpp_set*) this == (cpp_set*) &y;
}


template<class E>
inline bool RSLSet<E>::operator<= (const RSLSet& y) const
{
    return *(cpp_set*) this <= (cpp_set*) &y;
}


template<class E>
inline bool RSLSet<E>::operator>= (const RSLSet& y) const
{
    return *(cpp_set*) &y <= (cpp_set*) this;
}


template<class E>
inline bool RSLSet<E>::operator!= (const RSLSet& y) const
{
    return ! (*(cpp_set*) this == (cpp_set*) &y);
}


template<class E>
inline bool RSLSet<E>::operator< (const RSLSet& y) const
{
    return count < y.count && *(cpp_set*) this <= (cpp_set*) &y;
}


template<class E>
inline bool
RSLSet<E>::operator> (const RSLSet& y) const
{
    return count > y.count && *(cpp_set*) &y <= (cpp_set*) this;
}

template<class E> 
inline bool RSL_set_empty (const RSLSet<E>& x) {
  return (x.first==0);
}

template<class E>
inline int card (const RSLSet<E>& x)
{
    return x.count;
}

template<class E>
inline bool isin (const E& e, const RSLSet<E>& s)
{
  return s[e];
}

template<class E> bool alls (bool (*pred)(const E), const RSLSet<E>& s)
{
  bool result = true;
    for (cpp_sn* p = s.first; (p && result); p = p->next)
      {
        result = (*pred)(((RSLSetNode<E>*) p)->hd);
      }
  return result;
}

template<class E> bool alls (bool (*pred)(const E&), const RSLSet<E>& s)
{
  bool result = true;
    for (cpp_sn* p = s.first; (p && result); p = p->next)
      {
        result = (*pred)(((RSLSetNode<E>*) p)->hd);
      }
  return result;
}

template<class E> bool existss (bool (*pred)(const E), const RSLSet<E>& s)
{
  bool result = false;
    for (cpp_sn* p = s.first; (p && !result); p = p->next)
      {
        result = (*pred)(((RSLSetNode<E>*) p)->hd);
      }
  return result;
}

template<class E> bool existss (bool (*pred)(const E&), const RSLSet<E>& s)
{
  bool result = false;
    for (cpp_sn* p = s.first; (p && !result); p = p->next)
      {
        result = (*pred)(((RSLSetNode<E>*) p)->hd);
      }
  return result;
}

template<class E> bool exists1s (bool (*pred)(const E), const RSLSet<E>& s)
{
  int count = 0;
    for (cpp_sn* p = s.first; (p && (count < 2)); p = p->next)
      {
        if ((*pred)(((RSLSetNode<E>*) p)->hd)) count++; 
      }
  return (count==1);
}

template<class E> bool exists1s (bool (*pred)(const E&), const RSLSet<E>& s)
{
  int count = 0;
    for (cpp_sn* p = s.first; (p && (count < 2)); p = p->next)
      {
        if ((*pred)(((RSLSetNode<E>*) p)->hd)) count++; 
      }
  return (count==1);
}

template<class E>
E RSL_chooses (bool (*pred)(const E), const RSLSet<E>& s) {
  bool found = false;
  E r;
  for (cpp_sn* p = s.first; (p && !found); p = p->next) {
    r = ((RSLSetNode<E>*) p)->hd;
    if ((*pred)(r)) {
      found = true;
    }
  }
  if (!found) RSL_fail("Choose from empty set");
  return r;
}

template<class E>
E RSL_chooses (bool (*pred)(const E&), const RSLSet<E>& s) {
  bool found = false;
  E r;
  for (cpp_sn* p = s.first; (p && !found); p = p->next) {
    r = ((RSLSetNode<E>*) p)->hd;
    if ((*pred)(r)) {
      found = true;
    }
  }
  if (!found) RSL_fail("Choose from empty set");
  return r;  
}

template<class E>
inline E hd (const RSLSet<E>& x)
{
  if (x.first==0){
    RSL_fail("Head of empty set");
  }
  return ((RSLSetNode<E>*) x.first)->hd;
}



template<class E> RSLSetNode<E>::RSLSetNode (const E& h)
{
    next = this;
    hd = (E&) h;
    #   if defined _set_test_
    cout << " N" << ADDR (this);
    #      if defined _int_
    cout << "[" << hd << "]";
    #      endif
    cout << fl;
    #   endif
}


template<class E> cpp_sn *RSLSetNode<E>::cp ()
{
    return new RSLSetNode<E> (hd);
}


template<class E> void RSLSetNode<E>::del ()
{
    // ???
    #   if defined _int_
    hd = -hd;
    #   endif
    delete this;
}

// Implementation of the set class
//

template<class E>
RSLSet<E>::RSLSet (const E& item)
{
    count = 0;
    first = 0;
    insert (new RSLSetNode<E> (item));
    #       if defined _set_test_
    cout << " S(" << ADDR (this);
    #         if defined _int_
    cout << "[" << item << "]";
    #         endif
    cout << ")" << fl;
    #       endif
}


template<class E>
RSLSet<E>::RSLSet (const E& item, const RSLSet<E>& set)
{
    count = set.count;
    first = set.copy ();
    insert (new RSLSetNode<E> (item));
    #       if defined _set_test_
    cout << " S(" << ADDR (this);
    #         if defined _int_
    cout << "[" << item << "]";
    #         endif
    cout << "," << ADDR (&set) << ")" << fl;
    #       endif
}


template<class E>
RSLSet<E>::RSLSet (const RSLSet& set)
{
    count = set.count;
    first = set.copy ();
}


template<class E>
const RSLSet<E>& RSLSet<E>::operator= (const RSLSet& y)
{
    #       if defined _set_test_
    cout << "\n S=(" << ADDR (this) << "," << ADDR (&y) << ")" << fl;
    #       endif
    assign (this, (cpp_set*) &y);
    return *this;
}


template<class E>
RSLSet<E> RSLSet<E>::operator* (const RSLSet& y) const
{
  cpp_sn *res = 0;
  int cnt = 0;
  if (count != 0 && y.count != 0) {
    for (cpp_sn *pn = first; pn; pn = pn->next) {
      if (((cpp_set&)y)[pn]) {
	cpp_sn *n = pn->cp ();
        n->next = res;
        res = n;
        cnt++;
      }
    }
  }
  return RSLSet<E> (res, cnt);
}


template<class E>
RSLSet<E> RSLSet<E>::operator+ (const RSLSet& y) const
{
  cpp_sn* res = copy ();
  int cnt = count;
  for (cpp_sn *pn = y.first; pn; pn = pn->next) {
    if (!(*((cpp_set*)(this)))[pn]) {
      cpp_sn *n = pn->cp ();
      n->next = res;
      res = n;
      cnt++;
    }
  }
  return RSLSet<E> (res, cnt);
}


template<class E>
RSLSet<E> RSLSet<E>::operator% (const RSLSet& y) const
{
  cpp_sn *res = 0;
  int cnt = 0;
  if (count != 0) {
    for (cpp_sn *pn = first; pn; pn = pn->next) {
      if (!((cpp_set&)y)[pn]) {
	cpp_sn *n = pn->cp ();
	n->next = res;
	res = n;
	cnt++;
      }
    }
  }
  return RSLSet<E> (res, cnt);
}


template<class E>
bool RSLSet<E>::operator[] (const E& item) const
{
  RSLSetNode<E> *i = new RSLSetNode<E> (item);
  bool res = (*(cpp_set*)this)[i];
  delete i;
  return res;
}

template<class E>
string RSL_to_string (const RSLSet<E>& set) {
  string s = "{";
    if (set.count)
    {
        for (cpp_sn* p = set.first; p; p = p->next)
        {
            s += RSL_to_string(((RSLSetNode<E>*) p)->hd);
            if (p->next) s += ',';
        }
    }
    s += '}';
    return s;
}
  



#ifdef _RSL_set_output_

template<class E>
ostream& operator<< (ostream& s, const RSLSet<E>& set)
{
    #       if defined _set_test_
    s << "(" << ADDR (&set) << ")";
    #       endif
    s << "{";
    if (set.count)
    {
        for (cpp_sn* p = set.first; p; p = p->next)
        {
            #       if defined _set_test_
            s << "(" << ADDR (p) << ")";
            #       endif
            s << ((RSLSetNode<E>*) p)->hd;
            if (p->next) s << ",";
        }
    }
    return s << "}";
}

#endif                                            // _RSL_set_output_


#ifdef RSL_io


template<class E>
ostream& operator<< (ostream& s, const RSLSet<E>& set)
{
    s << "{";
    cpp_sn* p = set.first;
    while (p)
    {
        s << ((RSLSetNode<E>*) p) -> hd;
        p = p -> next;
        if (p) s << ",";
    }
    s << "}";
    return s;
}


enum SetToken {st_error, st_open_set, st_close_set, st_enumeration_separator};
//                     {          }                 ,

void input_SetToken (istream& s, SetToken& t);
template<class E> void input_elements (istream& , RSLSet<E>&);
template<class E> void input_enumeration (istream&, RSLSet<E>&);

template<class E>
istream& operator>> (istream& s, RSLSet<E>& set)
{
    SetToken t;
    RSLSet<E> temp;

    input_SetToken(s,t);
    if (t == st_open_set)
        input_elements(s, temp);
    else
        s.clear(ios::badbit);

    if (s) set = temp;

    return s;
}

template<class E>
void input_elements (istream& s, RSLSet<E>& set)
{
    RSLSet<E> temp;
    char peek_ahead = 0;
    SetToken t;

    s >> peek_ahead;
    if (peek_ahead == '}')                        // eol, empty set
        temp = RSLSet<E>();
    else
    {
        s.putback(peek_ahead);                    //it was probably part of an element, i.e. the list is probably non-empty
        input_enumeration(s, temp);
        if (s)
        {
            input_SetToken(s,t);
            if (s && t == st_close_set);
            else
                s.clear(ios::badbit);
        }
    }
    if (s) set = temp;
}


template<class E>
void input_enumeration (istream& s, RSLSet<E>& set)
{
    char peek_ahead = 0;
    E elem;

    s >> elem;
    if (s)
    {
        s >> peek_ahead;
        if (s)
        {
            if (peek_ahead == ',')
            {
                RSLSet<E> temp;
                input_enumeration(s, temp);
                if (s) set = RSLSet<E>(elem, temp);
            }
            else                                  //probably eol
            {
                s.putback(peek_ahead);
                set = RSLSet<E>(elem);
            }
        }
        else
            s.clear(ios::badbit);
    }
    else
        s.clear(ios::badbit);
}
#endif                                            // RSL_io

#endif // _RSL_set_h
