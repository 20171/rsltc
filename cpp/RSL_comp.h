/* 
RSL Type Checker
Copyright (C) 2000 UNU/IIST

raise@iist.unu.edu
*/

#ifndef _RSL_comp_h
#define _RSL_comp_h
#include "RSL_set.h"
#include "RSL_list.h"
#include "RSL_map.h"
#include "RSL_text.h"

template<class A, class B>
RSLSet<B> RSL_compss(B (*g)(const A), bool (*p)(const A), const RSLSet<A>& s) {
  RSLSet<B> r = RSLSet<B>();
  A a;
  for (cpp_sn* pn = s.first; pn; pn = pn->next) {
    a = ((RSLSetNode<A>*) pn)->hd;
    if ((*p)(a)) {
      r = RSLSet<B>((*g)(a), r);
    }
  }
  return r;
}

template<class A, class B>
RSLSet<B> RSL_compss(B (*g)(const A&), bool (*p)(const A&), const RSLSet<A>& s) {
  RSLSet<B> r = RSLSet<B>();
  A a;
  for (cpp_sn* pn = s.first; pn; pn = pn->next) {
    a = ((RSLSetNode<A>*) pn)->hd;
    if ((*p)(a)) {
      r = RSLSet<B>((*g)(a), r);
    }
  }
  return r;
}

template<class A, class B>
RSLSet<B> RSL_compls(B (*g)(const A), bool (*p)(const A), const RSLList<A>& l) {
  RSLSet<B> r = RSLSet<B>();
  A a;
  for (cpp_ln* pn = l.first; pn; pn = pn->next) {
    a = ((RSLListNode<A>*) pn)->hd;
    if ((*p)(a)) {
      r = RSLSet<B>((*g)(a), r);
    }
  }
  return r;
}

template<class A, class B>
RSLSet<B> RSL_compls(B (*g)(const A&), bool (*p)(const A&), const RSLList<A>& l) {
  RSLSet<B> r = RSLSet<B>();
  A a;
  for (cpp_ln* pn = l.first; pn; pn = pn->next) {
    a = ((RSLListNode<A>*) pn)->hd;
    if ((*p)(a)) {
      r = RSLSet<B>((*g)(a), r);
    }
  }
  return r;
}

template<class B>
RSLSet<B> RSL_compts(B (*g)(const RSL_char&), bool (*p)(const RSL_char&), const RSL_string& s) {
  RSLSet<B> r = RSLSet<B>();
  RSL_char a;
  int l = len(s);
  for (int i = 0 ; i < l ; ++i) {
    a = RSL_char(s.RSL_f1[i]);
    if ((*p)(a)) {
      r = RSLSet<B>((*g)(a), r);
    }
  }
  return r;
}

template<class A, class B, class C>
RSLSet<B> RSL_compms(B (*g)(const A), bool (*p)(const A), const RSLMap<A, C>& m) {
  RSLSet<B> r = RSLSet<B>();
  A a;
  for (RSLMapNode<A, C> *pn = m.root; pn; pn = pn->link) {
    a = pn->item;
    if ((*p)(a)) {
      r = RSLSet<B>((*g)(a), r);
    }
  }
  return r;
}

template<class A, class B, class C>
RSLSet<B> RSL_compms(B (*g)(const A&), bool (*p)(const A&), const RSLMap<A, C>& m) {
  RSLSet<B> r = RSLSet<B>();
  A a;
  for (RSLMapNode<A, C> *pn = m.root; pn; pn = pn->link) {
    a = pn->item;
    if ((*p)(a)) {
      r = RSLSet<B>((*g)(a), r);
    }
  }
  return r;
}

template<class A, class B>
RSLList<B> RSL_compll(B (*g)(const A), bool (*p)(const A), const RSLList<A>& l) {
  RSLList<B> r = RSLList<B>();
  A a;
  for (cpp_ln* pn = l.first; pn; pn = pn->next) {
    a = ((RSLListNode<A>*) pn)->hd;
    if ((*p)(a)) {
      r = r + RSLList<B>((*g)(a));
    }
  }
  return r;
}

template<class A, class B>
RSLList<B> RSL_compll(B (*g)(const A&), bool (*p)(const A&), const RSLList<A>& l) {
  RSLList<B> r = RSLList<B>();
  A a;
  for (cpp_ln* pn = l.first; pn; pn = pn->next) {
    a = ((RSLListNode<A>*) pn)->hd;
    if ((*p)(a)) {
      r = r + RSLList<B>((*g)(a));
    }
  }
  return r;
}

template<class B>
RSLList<B> RSL_comptl(B (*g)(const RSL_char&), bool (*p)(const RSL_char&), const RSL_string& s) {
  RSLList<B> r = RSLList<B>();
  RSL_char a;
  int l = len(s);
  for (int i = 0; i < l; ++i) {
    a = RSL_char(s.RSL_f1[i]);
    if ((*p)(a)) {
      r = r + RSLList<B>((*g)(a));
    }
  }
  return r;
}

template<class A>
RSL_string RSL_complt(RSL_char (*g)(const A), bool (*p)(const A), const RSLList<A>& l) {
  RSL_string r = RSL_string();
  A a;
  for (cpp_ln* pn = l.first; pn; pn = pn->next) {
    a = ((RSLListNode<A>*) pn)->hd;
    if ((*p)(a)) {
      r = r + (*g)(a);
    }
  }
  return r;
}

template<class A>
RSL_string RSL_complt(RSL_char (*g)(const A&), bool (*p)(const A&), const RSLList<A>& l) {
  RSL_string r = RSL_string();
  A a;
  for (cpp_ln* pn = l.first; pn; pn = pn->next) {
    a = ((RSLListNode<A>*) pn)->hd;
    if ((*p)(a)) {
      r = r + (*g)(a);
    }
  }
  return r;
}


RSL_string RSL_comptt(RSL_char (*g)(const RSL_char&), bool (*p)(const RSL_char&), const RSL_string& s) {
  RSL_string r = RSL_string();
  RSL_char a;
  int l = len(s);
  for (int i = 0; i < l; ++i) {
    a = RSL_char(s.RSL_f1[i]);
    if ((*p)(a)) {
      r = r + (*g)(a);
    }
  }
  return r;
}


template<class A, class B, class C>
RSLMap<B, C> RSL_compsm(B (*g1)(const A), C (*g2)(const A), bool (*p)(const A), const RSLSet<A>& s) {
  RSLMap<B, C> r = RSLMap<B, C>();
  A a;
  for (cpp_sn* pn = s.first; pn; pn = pn->next) {
    a = ((RSLSetNode<A>*) pn)->hd;
    if ((*p)(a)) {
      r = RSLMap<B, C>((*g1)(a), (*g2)(a), r);
    }
  }
  return r;
}

template<class A, class B, class C>
RSLMap<B, C> RSL_compsm(B (*g1)(const A&), C (*g2)(const A&), bool (*p)(const A&), const RSLSet<A>& s) {
  RSLMap<B, C> r = RSLMap<B, C>();
  A a;
  for (cpp_sn* pn = s.first; pn; pn = pn->next) {
    a = ((RSLSetNode<A>*) pn)->hd;
    if ((*p)(a)) {
      r = RSLMap<B, C>((*g1)(a), (*g2)(a), r);
    }
  }
  return r;
}

template<class A, class B, class C>
RSLMap<B, C> RSL_complm(B (*g1)(const A), C (*g2)(const A), bool (*p)(const A), const RSLList<A>& l) {
  RSLMap<B, C> r = RSLMap<B, C>();
  A a;
  for (cpp_ln* pn = l.first; pn; pn = pn->next) {
    a = ((RSLListNode<A>*) pn)->hd;
    if ((*p)(a)) {
      r = RSLMap<B, C>((*g1)(a), (*g2)(a), r);
    }
  }
  return r;
}

template<class A, class B, class C>
RSLMap<B, C> RSL_complm(B (*g1)(const A&), C (*g2)(const A&), bool (*p)(const A&), const RSLList<A>& l) {
  RSLMap<B, C> r = RSLMap<B, C>();
  A a;
  for (cpp_ln* pn = l.first; pn; pn = pn->next) {
    a = ((RSLListNode<A>*) pn)->hd;
    if ((*p)(a)) {
      r = RSLMap<B, C>((*g1)(a), (*g2)(a), r);
    }
  }
  return r;
}

template<class B, class C>
RSLMap<B, C> RSL_comptm(B (*g1)(const RSL_char&), C (*g2)(const RSL_char&), bool (*p)(const RSL_char&), const RSL_string& s) {
  RSLMap<B, C> r = RSLMap<B, C>();
  RSL_char a;
  int l = len(s);
  for (int i = 0; i < l; ++i) {
    a = RSL_char(s.RSL_f1[i]);
    if ((*p)(a)) {
      r = RSLMap<B, C>((*g1)(a), (*g2)(a), r);
    }
  }
  return r;
}

template<class A, class B, class C, class D>
RSLMap<B, D> RSL_compmm(B (*g1)(const A), D (*g2)(const A), bool (*p)(const A), const RSLMap<A, C>& m) {
  RSLMap<B, D> r = RSLMap<B, D>();
  A a;
  for (RSLMapNode<A, C> *pn = m.root; pn; pn = pn->link) {
    a = pn->item;
    if ((*p)(a)) {
      r = RSLMap<B, D>((*g1)(a), (*g2)(a), r);
    }
  }
  return r;
}

template<class A, class B, class C, class D>
RSLMap<B, D> RSL_compmm(B (*g1)(const A&), D (*g2)(const A&), bool (*p)(const A&), const RSLMap<A, C>& m) {
  RSLMap<B, D> r = RSLMap<B, D>();
  A a;
  for (RSLMapNode<A, C> *pn = m.root; pn; pn = pn->link) {
    a = pn->item;
    if ((*p)(a)) {
      r = RSLMap<B, D>((*g1)(a), (*g2)(a), r);
    }
  }
  return r;
}



#endif // _RSL_comp_h
