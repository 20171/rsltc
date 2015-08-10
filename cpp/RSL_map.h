/* 
RSL Type Checker
Copyright (C) 2000 UNU/IIST

raise@iist.unu.edu
*/

#ifndef _RSL_map_h
#define _RSL_map_h

#if defined _map_test_
#  include "cpp_test.h"
#endif

#include "RSL_set.h"

typedef void* Pix;



// A node represents the maplet [item +> cont].
//

template<class Dom, class Rng>
struct RSLMapNode {
// Data
  RSLMapNode  *link;
  Dom        item;
  Rng       cont;
// Constructors
  RSLMapNode (const Dom& h, RSLMapNode* l =0) { item = (Dom&) h; link = l; }
// Destructor
  ~RSLMapNode () {}
};

template<class Dom, class Rng>
RSLMapNode<Dom, Rng>* _copy (RSLMapNode<Dom, Rng> *t) {
; if (t == 0)  return 0;

  RSLMapNode<Dom, Rng> *l = _copy<Dom, Rng> (t->link);
  RSLMapNode<Dom, Rng> *x = new RSLMapNode<Dom, Rng> (t->item, l);
  x->cont = t->cont;
  return x;
}

template<class Dom, class Rng>
RSLMapNode<Dom, Rng>* seek_RSLNodes (RSLMapNode<Dom, Rng> *root, const Dom& key) {
  RSLMapNode<Dom, Rng> *t = root;
  while (t != 0) {if ((Dom&) key != t->item) t = t->link; else break;}
  return t;
}



template<class Dom, class Rng> struct RSLMap;
template<class Dom, class Rng> bool RSL_map_empty (const RSLMap<Dom, Rng>&);

template<class Dom, class Rng> const Rng& contents_RSLMap (Pix);
template<class Dom, class Rng> const Pix seek_RSLMap (const RSLMap<Dom, Rng>&, const Dom&);

template<class Dom, class Rng> RSLSet<Dom> dom (const RSLMap<Dom, Rng>&);
template<class Dom, class Rng> RSLSet<Rng> rng (const RSLMap<Dom, Rng>&);
template<class Dom, class Rng> Dom& hd (const RSLMap<Dom, Rng>&);
template<class Dom, class Rng> bool isin (const Dom&, const RSLMap<Dom, Rng>&);
template<class Dom, class Rng> bool allm (bool (*pred)(const Dom), const RSLMap<Dom, Rng>&);
template<class Dom, class Rng> bool allm (bool (*pred)(const Dom&), const RSLMap<Dom, Rng>&);
template<class Dom, class Rng> bool existsm (bool (*pred)(const Dom), const RSLMap<Dom, Rng>&);
template<class Dom, class Rng> bool existsm (bool (*pred)(const Dom&), const RSLMap<Dom, Rng>&);
template<class Dom, class Rng> bool exists1m (bool (*pred)(const Dom), const RSLMap<Dom, Rng>&);
template<class Dom, class Rng> bool exists1m (bool (*pred)(const Dom&), const RSLMap<Dom, Rng>&);
template<class Dom, class Rng> Dom RSL_choosem (bool (*pred)(const Dom), const RSLMap<Dom, Rng>&);
template<class Dom, class Rng> Dom RSL_choosem (bool (*pred)(const Dom&), const RSLMap<Dom, Rng>&);
template<class Dom, class Rng> string RSL_to_string (const RSLMap<Dom, Rng>&);
# if defined RSL_io
template<class Dom, class Rng> ostream& operator<< (ostream&, const RSLMap<Dom, Rng>&);
template<class Dom, class Rng> istream& operator>> (istream&, RSLMap<Dom, Rng>&);
#endif

template<class Dom, class Rng>
struct RSLMap {
// Data
  int       count;   // number of nodes
  RSLMapNode<Dom, Rng> *root;    // address of root node

// Constructors
#if defined _map_test_
  RSLMap ();
  RSLMap (const Dom&, const Rng&);
  RSLMap (const Dom&, const Rng&, const RSLMap&);
  RSLMap (const RSLMap&);
  RSLMap (RSLMapNode<Dom, Rng>*);
  RSLMap (RSLMapNode<Dom, Rng>*, const int);
#else
  RSLMap ()
    {count = 0; root = 0;}
  RSLMap (const Dom& item, const Rng& cont)
    {count = 0; root = 0; (*this)(item) = (Rng&) cont;}
  RSLMap (const Dom& item, const Rng& cont, const RSLMap& b)
    {count = b.count; root = _copy<Dom, Rng> (b.root); (*this)(item) = (Rng&) cont;}
  RSLMap (const RSLMap& b)
    {count = b.count; root = _copy<Dom, Rng> (b.root);}
  RSLMap (RSLMapNode<Dom, Rng> *p) {                     // conversion
    int i = 0;
    for (RSLMapNode<Dom, Rng> *pn = p; pn; pn = pn->link) {
      i++;
    }
    count = i;
    root = p;
  }

  RSLMap (RSLMapNode<Dom, Rng> *p, const int i) {        // conversion
    count = i;
    root = p;
  }

#endif

// Destructor
  ~RSLMap ()
    {_kill (root);}
// Conversions
// Assignment
  const RSLMap& operator= (const RSLMap<Dom, Rng>&);
// Service
  void _kill (RSLMapNode<Dom, Rng>*);
  void del (const Dom&);
  void clear ()
    {_kill (root); count = 0; root = 0;}
  //  template<Dom, Rng> friend const Rng& contents_RSLMap (Pix);
  //  template<Dom, Rng> friend const Pix seek_RSLMap (const RSLMap<Dom, Rng>&, const Dom&);

// User operators
  bool operator== (const RSLMap<Dom, Rng>&) const;   // equal?
  bool operator!= (const RSLMap& b) const  // not equal?
    {return !(*this == b);}
  Rng& operator() (const Dom&);                 // application
  Rng& operator[] (const Dom&) const;       // application
  RSLMap operator+ (const RSLMap&) const;   // dagger, union

  RSLMap operator/ (const RSLSet<Dom>&) const;   // restrict to
  RSLMap operator% (const RSLSet<Dom>&) const;   // restrict with

  //  friend RSLSet<Dom> dom <> (const RSLMap<Dom, Rng>&);
  //  friend RSLSet<Rng> rng <> (const RSLMap<Dom, Rng>&);
  //  friend Dom& hd <> (const RSLMap<Dom, Rng>&);
  //  friend bool isin <> (const Dom&, const RSLMap<Dom, Rng>&);
  //  friend bool all<> (bool (*pred)(const Dom), const RSLMap<Dom, Rng>&);
  //  friend bool all<> (bool (*pred)(const Dom&), const RSLMap<Dom, Rng>&);
  //  friend bool exists<> (bool (*pred)(const Dom), const RSLMap<Dom, Rng>&);
  //  friend bool exists<> (bool (*pred)(const Dom&), const RSLMap<Dom, Rng>&);
  //  friend bool exists1<> (bool (*pred)(const Dom), const RSLMap<Dom, Rng>&);
  //  friend bool exists1<> (bool (*pred)(const Dom&), const RSLMap<Dom, Rng>&);
  //  friend Dom RSL_choose<> (bool (*pred)(const Dom), const RSLMap<Dom, Rng>&);
  //  friend Dom RSL_choose<> (bool (*pred)(const Dom&), const RSLMap<Dom, Rng>&);
  //  friend string RSL_to_string<> (const RSLMap<Dom, Rng>&);

  //# if defined RSL_io
  //  friend ostream& operator<< <> (ostream&, const RSLMap<Dom, Rng>&);
  //  friend istream& operator>> <> (istream&, RSLMap<Dom, Rng>&);
  //#endif
};


/*

We define two applications: operator() and operator[].  Both m(x) and m[x]
return a reference to the range component with the domain value x, but
operator() re-arranges the map while operator[] leaves the map unchanged.
Furthermore, operator() may be called with an argument not in the domain:
a new maplet is inserted.

*/



// This function should be static

template<class Dom, class Rng>
inline const Rng& contents_RSLMap (Pix i) {
  if (i == 0) abort ();
  return ((RSLMapNode<Dom, Rng>*)i)->cont;
}



#if defined _map_test_

template<class Dom, class Rng>
RSLMap<Dom, Rng>::RSLMap () {
  count = 0;
  root = 0;
  cout << "\n M()" << ADDR (this) << fl;
}


template<class Dom, class Rng>
RSLMap<Dom, Rng>::RSLMap (const Dom& item, const Rng& cont) {
  count = 0;
  root = 0;
  (*this) (item) = (Rng&) cont;
  cout << "\n M(.)" << ADDR (this) << fl;;
#       if defined _int_
          cout << "[" << item << "+>" << cont << "]" << fl;
#       endif
}


template<class Dom, class Rng>
RSLMap<Dom, Rng>::RSLMap (const Dom& item, const Rng& cont, const RSLMap& b) {
  count = b.count;
  root = _copy<Dom, Rng> (b.root);
  (*this) (item) = (Rng&) cont;
  cout << "\n M(..)" << ADDR (this);
#       if defined _int_
          cout << "[" << item << "+>" << cont << "]";
#       endif
  cout << "/" << ADDR (&b) << fl;
}


template<class Dom, class Rng>
RSLMap<Dom, Rng>::RSLMap (const RSLMap& b) {
  count = b.count;
  root = _copy<Dom, Rng> (b.root);
}

template<class Dom, class Rng>
RSLMap<Dom, Rng>::RSLMap (RSLMapNode<Dom, Rng> *p) {     // conversion
  int i = 0;
  for (RSLMapNode<Dom, Rng> *pn = p; pn; pn = pn->link) {
    i++;
  }
  count = i;
  root = p;
}

template<class Dom, class Rng>
RSLMap<Dom, Rng>::RSLMap (RSLMapNode<Dom, Rng> *p, const int i) {
  count = i;
  root = p;
}

#endif // _map_test

template<class Dom, class Rng>
const Pix seek_RSLMap (const RSLMap<Dom, Rng>& map, const Dom& key) {
  RSLMapNode<Dom, Rng> *t = map.root;
//  while (t != 0 && ((Dom&) key) != t->item) t = t->link;
  while (t != 0) {if ((Dom&) key != t->item) t = t->link; else break;}
  return (Pix) t;
}


template<class Dom, class Rng>
void RSLMap<Dom, Rng>::_kill (RSLMapNode<Dom, Rng> *t) {
  if (t != 0) {
    _kill (t->link);
    delete t;
  }
}



template<class Dom, class Rng>
Rng& RSLMap<Dom, Rng>::operator() (const Dom& item) {
  RSLMapNode<Dom, Rng> *t = root;
  if (t == 0) {
    ++count;
    root = new RSLMapNode<Dom, Rng> (item);
;   return root->cont;
  }
//  while (t != 0 && ((Dom&) item) != t->item) t = t->link;
  while (t != 0) {if ((Dom&) item != t->item) t = t->link; else break;}
  if (t == 0) {
    ++count;
    t = new RSLMapNode<Dom, Rng> (item);
    t->link = root;
    root = t;
  }
  return t->cont;
}

template<class Dom, class Rng>
Rng& RSLMap<Dom, Rng>::operator[] (const Dom& item) const {
  RSLMapNode<Dom, Rng> *t = root;
//  while (t != 0 && ((Dom&) item) != t->item) t = t->link;
  while (t != 0) {if ((Dom&) item != t->item) t = t->link; else break;}
  if (t == 0){
    string s = "Map " + RSL_to_string((RSLMap<Dom, Rng>&)(*this)) + " applied to " + RSL_to_string((Dom&)item) + ": outside domain";
    // If the above causes Visual C++ errors
    // with "ambiguous calls of RSL_to_string"
    // you can replace it with the following
    //string s = "Map " + RSL_to_string((RSLMap<Dom, Rng>&)(*this)) + " applied to value outside domain";
    RSL_fail(s);
  }
  return t->cont;
}


template<class Dom, class Rng>
void RSLMap<Dom, Rng>::del (const Dom& key) {
  RSLMapNode<Dom, Rng> *t = (RSLMapNode<Dom, Rng>*) (seek_RSLMap (*this, key));
; if (t == 0) return;
  if (t == root) {
    root = t->link;
  } else {
    RSLMapNode<Dom, Rng> *p = root;
    while (p->link != t) p = p->link;
    p->link = t->link;
  }
  t->link = 0;
  --count;
  delete t;
}


template<class Dom, class Rng>
const RSLMap<Dom, Rng>& RSLMap<Dom, Rng>::operator= (const RSLMap<Dom, Rng>& b) {
; if (this == &b) return *this;
  clear ();
  count = b.count;
  root = _copy<Dom, Rng> (b.root);
  return *this;
}


template<class Dom, class Rng>
bool RSLMap<Dom, Rng>::operator== (const RSLMap& b) const {
  int n = count;
; if (n != b.count) return 0;
; if (n == 0) return 1;

  for (RSLMapNode<Dom, Rng> *pn = root; pn; pn = pn->link) {
    Pix i = seek_RSLMap (b, pn->item);
    if (i == 0 || (Rng&) /*contents_RSLMap(i)*/((RSLMapNode<Dom, Rng>*)i)->cont != pn->cont) return 0;
  }
  return 1;
}


template<class Dom, class Rng>
RSLMap<Dom, Rng> RSLMap<Dom, Rng>::operator+ (const RSLMap& b) const {
  RSLMapNode<Dom, Rng> *p = _copy<Dom, Rng> (root);
  int cnt = count;
  if (b.count)
    for (RSLMapNode<Dom, Rng> *pn = b.root; pn; pn = pn->link) {
      RSLMapNode<Dom, Rng> *i = seek_RSLNodes<Dom, Rng> (p, pn->item);
      if (i==0) {
	RSLMapNode<Dom, Rng> *t = new RSLMapNode<Dom, Rng> (pn->item);
	t->cont = pn->cont;
	t->link = p;
	p = t;
	cnt++;
      } else {
	i->cont = pn->cont;
      }
    }
  return RSLMap<Dom, Rng>(p, cnt);
}


template<class Dom, class Rng>
RSLMap<Dom, Rng> RSLMap<Dom, Rng>::operator/ (const RSLSet<Dom>& s) const {
  RSLMapNode<Dom, Rng> *res = 0;
  int cnt = 0;
  if (count) {
    for (RSLMapNode<Dom, Rng> *pn = root; pn; pn = pn->link) {
      if (s[pn->item]) {
	RSLMapNode<Dom, Rng> *n = new RSLMapNode<Dom, Rng> (pn->item, res);
	n->cont = pn->cont;
	res = n;
	cnt++;
      }
    }
  }
  return RSLMap<Dom, Rng>(res, cnt);
}

template<class Dom, class Rng>
RSLMap<Dom, Rng> RSLMap<Dom, Rng>::operator% (const RSLSet<Dom>& s) const {
  RSLMapNode<Dom, Rng> *res = 0;
  int cnt = 0;
  if (count) {
    for (RSLMapNode<Dom, Rng> *pn = root; pn; pn = pn->link) {
      if (!(s[pn->item])) {
	RSLMapNode<Dom, Rng> *n = new RSLMapNode<Dom, Rng> (pn->item, res);
	n->cont = pn->cont;
	res = n;
	cnt++;
      }
    }
  }
  return RSLMap<Dom, Rng>(res, cnt);
}

template<class Dom, class Rng>
RSLSet<Dom> dom (const RSLMap<Dom, Rng>& a) {
  cpp_sn *res = 0;
  if (a.count) {
    for (RSLMapNode<Dom, Rng> *pn = a.root; pn; pn = pn->link) {
      cpp_sn *n = (cpp_sn*)(new RSLSetNode<Dom> (pn->item));
      n->next = res;
      res = n;
    }
  }
  return RSLSet<Dom> (res, a.count);
}


template<class Dom, class Rng>
RSLSet<Rng> rng (const RSLMap<Dom, Rng>& a) {
  cpp_sn *res = 0;
  int cnt = 0;
  if (a.count) {
    for (RSLMapNode<Dom, Rng> *pn = a.root; pn; pn = pn->link) {
      cpp_sn *n = (cpp_sn*)(new RSLSetNode<Rng> (pn->cont));
      // may be duplicates
      for (cpp_sn *sn = res; sn; sn = sn->next) {
	if (n->eq (sn)) {
	  delete n;
	  n = 0;
	  break;
	}
      }
      if (n != 0) {
	n->next = res;
	res = n;
	cnt++;
      }
    }
  }
  return RSLSet<Rng> (res, cnt);
}

template<class Dom, class Rng> 
inline bool RSL_map_empty (const RSLMap<Dom, Rng>& map) {
  return (map.root==0);
}

template<class Dom, class Rng>
inline Dom& hd (const RSLMap<Dom, Rng>& map)
{
  if (map.root==0){
    RSL_fail("Head of empty map");
  }
  return map.root->item;
}

template<class Dom, class Rng>
bool isin (const Dom& e, const RSLMap<Dom, Rng>& m) {
  bool result = false;
  for (RSLMapNode<Dom, Rng> *pn = m.root; (pn && !result); pn = pn->link){
    result = ((Dom&) e == pn->item);
  }
  return result;
}

template<class Dom, class Rng>
bool allm (bool (*pred)(const Dom), const RSLMap<Dom, Rng>& m) {
  bool result = true;
  for (RSLMapNode<Dom, Rng> *pn = m.root; (pn && result); pn = pn->link) {
    result = (*pred)(pn->item);
  }
  return result;
}

template<class Dom, class Rng>
bool allm (bool (*pred)(const Dom&), const RSLMap<Dom, Rng>& m) {
  bool result = true;
  for (RSLMapNode<Dom, Rng> *pn = m.root; (pn && result); pn = pn->link) {
    result = (*pred)(pn->item);
  }
  return result;
}

template<class Dom, class Rng>
bool existsm (bool (*pred)(const Dom), const RSLMap<Dom, Rng>& m) {
  bool result = false;
  for (RSLMapNode<Dom, Rng> *pn = m.root; (pn && !result); pn = pn->link) {
    result = (*pred)(pn->item);
  }
  return result;
}

template<class Dom, class Rng>
bool existsm (bool (*pred)(const Dom&), const RSLMap<Dom, Rng>& m) {
  bool result = false;
  for (RSLMapNode<Dom, Rng> *pn = m.root; (pn && !result); pn = pn->link) {
    result = (*pred)(pn->item);
  }
  return result;
}

template<class Dom, class Rng> 
bool exists1m (bool (*pred)(const Dom), const RSLMap<Dom, Rng>& m) {
  int count = 0;
  for (RSLMapNode<Dom, Rng> *pn = m.root; (pn && (count < 2)); pn = pn->link) {
    if ((*pred)(pn->item)) count++; 
  }
  return (count==1);
}

template<class Dom, class Rng>
bool exists1m (bool (*pred)(const Dom&), const RSLMap<Dom, Rng>& m) {
  int count = 0;
  for (RSLMapNode<Dom, Rng> *pn = m.root; (pn && (count < 2)); pn = pn->link) {
    if ((*pred)(pn->item)) count++; 
  }
  return (count==1);
}

template<class Dom, class Rng>
Dom RSL_choosem (bool (*pred)(const Dom), const RSLMap<Dom, Rng>& m) {
  bool found = false;
  Dom r;
  for (RSLMapNode<Dom, Rng> *pn = m.root; (pn && !found); pn = pn->link) {
    r = pn->item;
    if ((*pred)(r)) {
      found = true;
    }
  }
  if (!found) RSL_fail("Choose from empty map");
  return r;  
}

template<class Dom, class Rng>
Dom RSL_choosem (bool (*pred)(const Dom&), const RSLMap<Dom, Rng>& m) {
  bool found = false;
  Dom r;
  for (RSLMapNode<Dom, Rng> *pn = m.root; (pn && !found); pn = pn->link) {
    r = pn->item;
    if ((*pred)(r)) {
      found = true;
    }
  }
  if (!found) RSL_fail("Choose from empty map");
  return r;  
}

template<class Dom, class Rng>
string RSL_to_string (const RSLMap<Dom, Rng>& map) {
  string s = "[";
  RSLMapNode<Dom, Rng>* p = map.root;
  while (p){
    s += RSL_to_string(p -> item);
    s += "+>";
    s += RSL_to_string(p -> cont);
    p = p -> link;
    if (p) s += ',';
  }
  s += ']';
  return s;
}

#if defined RSL_io

template<class Dom, class Rng>
ostream& operator<< (ostream& s, const RSLMap<Dom, Rng>& map)
{
  s << "[";
  RSLMapNode<Dom, Rng>* p = map.root;
  while (p){
    s << p -> item;
    s << "+>";
    s << p -> cont;
    p = p -> link;
    if (p) s << ",";
  }
  s << "]";
  return s;
}

enum MapToken {mt_error, mt_open_map, mt_close_map, mt_enumeration_separator, mt_maps_to};
//                     [            ]                 ,                +>          

void input_MapToken (istream&, MapToken&);
template<class Dom, class Rng> static void input_elements (istream& , RSLMap<Dom, Rng>&);
template<class Dom, class Rng> static void input_enumeration (istream&, RSLMap<Dom, Rng>&);

template<class Dom, class Rng>
istream& operator>> (istream& s, RSLMap<Dom, Rng>& map)
{
  MapToken t;
  RSLMap<Dom, Rng> temp;

  input_MapToken(s,t);
  if (t == mt_open_map)
    input_elements(s, temp);
  else
    s.clear(ios::badbit);

  if (s) map = temp;

  return s;
}


template<class Dom, class Rng>
void input_elements (istream& s, RSLMap<Dom, Rng>& map)
{
  RSLMap<Dom, Rng> temp;
  char peek_ahead = 0;
  MapToken t;

  s >> peek_ahead;
  s.putback(peek_ahead);
  if (peek_ahead == ']'){        // eol, empty map
    input_MapToken(s,t);
    if (s && t == mt_close_map)
     temp = RSLMap<Dom, Rng>();
    else
     s.clear(ios::badbit);
  }
  else{
    input_enumeration(s, temp);
    if (s){
      input_MapToken(s,t);
      if (s && t == mt_close_map)
	{}
      else
	s.clear(ios::badbit);
    }
  }
if (s) map = temp;
}

template<class Dom, class Rng>
void input_enumeration (istream& s, RSLMap<Dom, Rng>& map)
{
  char peek_ahead = 0;
  MapToken t;
  Dom item;
  Rng cont;

  s >> item;
  if (s){
    input_MapToken(s,t);
    if (s && t == mt_maps_to)
      s >> cont;
    else
      s.clear(ios::badbit);
  }
  if (s){
    s >> peek_ahead;
    if (s){
      if (peek_ahead == ','){
        RSLMap<Dom, Rng> temp;
        input_enumeration(s, temp);
        if (s) map = RSLMap<Dom, Rng>(item, cont, temp);
      }
      else{
        s.putback(peek_ahead);
        map = RSLMap<Dom, Rng>(item, cont);
      }
    }
    else
      s.clear(ios::badbit);
  }
  else
    s.clear(ios::badbit);
}

#endif // RSL_io

#endif /* _RSL_map_h */
