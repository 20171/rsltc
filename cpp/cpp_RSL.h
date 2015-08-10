// @(#) CAP PROGRAMATOR (SYPRO DK) $Id: cpp_RSL.h,v 2.5 1994/05/19 13:30:07 she Exp $
//

// Adapted by CWG 31/12/97 for current g++ compiler

#ifndef cpp_RSL_header_CPP
#define cpp_RSL_header_CPP

#include <string>
#include <math.h>
#include <sstream>
using namespace std;

#include <cstdio>

#ifdef RSL_io
#include <iostream>
#endif

extern char cpp_RCS[];

template<class E>
bool RSL_true(const E e) {
  return true;
}

template<class E>
bool RSL_true(const E& e) {
  return true;
}

template<class E>
E RSL_identity(const E e) {
  return e;
}

template<class E>
E RSL_identity(const E& e) {
  return e;
}

inline void RSL_warn(const string& s) {
#ifdef RSL_io
  cout << s << "\n";
#else
  abort();
#endif
}

template<class E>
E RSL_check(bool (*pred)(const E), const E e, const string& s){
  if (!(*pred)(e)) RSL_warn(s);
  return e;
}

template<class E>
E RSL_check(bool (*pred)(const E&), const E& e, const string& s){
  if (!(*pred)(e)) RSL_warn(s);
  return e;
}

inline void RSL_fail(const string& s) {
#ifdef RSL_io
  cout << s << "\n";
#endif //RSL_io
  abort();
}

inline bool RSL_is_Nat (int i)
{ return (i >= 0); }

inline int RSL_abs( int f )
{ return f < 0 ? -f : f; }

inline double RSL_abs( double f )
{ return f < 0 ? -f : f; }

inline int RSL_int( double f )
{ return int( f ); }

inline double real( int f )
{ return double( f ); }

inline string RSL_bool_to_string (bool b) {
#ifdef RSL_boolalpha
  return (b ? "true" : "false");
#else
  // needed instead for Bool input to work
  return (b ? "1" : "0");
#endif // RSL_boolalpha
}

inline string RSL_to_string (bool b) {
  return RSL_bool_to_string (b);
}

extern string RSL_int_to_string (int f);
inline string RSL_to_string (int f) {
  return RSL_int_to_string(f);
}

extern string RSL_double_to_string (double f);
inline string RSL_to_string (double f) {
  return RSL_double_to_string(f);
}

#ifdef RSL_pre
int RSL_DIV_INT(int x, int y){
  if (y==0) RSL_fail("Division of " + RSL_int_to_string(x) + " by zero");
  return (x / y);
}
#else
#define RSL_DIV_INT(x,y)  (x / y)
#endif // RSL_pre

#ifdef RSL_pre
double RSL_DIV_REAL(double x, double y){
  if (y==0) RSL_fail("Division of " + RSL_double_to_string(x) + " by zero");
  return (x / y);
}
#else
#define RSL_DIV_REAL(x,y)  (x / y)
#endif // RSL_pre

#ifdef RSL_pre
int RSL_REM_INT(int x, int y){
  if (y==0) RSL_fail(RSL_int_to_string(x) + " modulo zero");
  return (x % y);
}
#else
#define RSL_REM_INT(x,y)  (x % y)
#endif // RSL_pre

inline int RSL_EXP_INT(int x, int y){
#ifdef RSL_pre
  if (y<0) RSL_fail("Integer exponentiation of " + RSL_int_to_string(x) + " with negative exponent " + RSL_int_to_string(y));
  else if ((x==0) && (y==0)) RSL_fail("Cannot compute 0 ** 0");
#endif // RSL_pre
  return (int)pow((double)x, double(y));
}


inline double RSL_EXP_REAL(double x, double y){
#ifdef RSL_pre
  if ((x==0) && (y <= 0)) RSL_fail("Zero raised to non-positive power " + RSL_double_to_string(y));
  else {
    int inty = (int)y;
    if ((x<0) && !(y==inty))
      RSL_fail("Negative number " + RSL_double_to_string(x) + " raised to non-integer power " + RSL_double_to_string(y));
  }
#endif // RSL_pre
  return pow(x, y);
}



template<class T>
T string_to_RSL(const string& s)
{
  string s1 = s + '\0'; // prevents premature end of stream in RSL_fetch_token
  //  string s1 = s;
  istringstream ist(s1);
  T res;
#ifdef RSL_boolalpha
  ist >> boolalpha;
#endif // RSL_boolalpha
  ist >> res;
  return res;
}

struct RSL_class {
  int refcnt;
  RSL_class () {refcnt = 1;}
};

#ifdef RSL_io
#include "cpp_io.h"
#endif

#endif
