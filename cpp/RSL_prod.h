/* 
RSL Type Checker
Copyright (C) 2000 UNU/IIST

raise@iist.unu.edu
*/

#ifndef _RSL_prod_h
#define _RSL_prod_h

#ifdef RSL_io
#include <iostream>
#endif

char* RSL_constructor_fun() { return "";}
typedef char* (*RSL_cons_fun) ();

#ifdef RSL_io
static void RSL_input_cons(istream& RSL_is, RSL_input_token_type& RSL_token, const char* RSL_cons_string){
char RSL_buf[128];

 RSL_fetch_token(RSL_is, RSL_token, RSL_buf);
 if (RSL_token == RSL_constructor_token) {
   if (!RSL_streq(RSL_buf, RSL_cons_string)) {
     RSL_token = RSL_error_token;
   }
 }
}



static void RSL_input_token(istream& RSL_is, RSL_input_token_type& RSL_token){
char RSL_buf[128];

 RSL_fetch_token(RSL_is, RSL_token, RSL_buf);
 if (RSL_token == RSL_constructor_token) {
   RSL_token = RSL_error_token;
 }
}
#endif // RSL_io 


template<class T1, RSL_cons_fun RSL_cons>
struct RSLProduct1{
T1 RSL_f1;
 RSLProduct1(){}

 RSLProduct1(const RSLProduct1& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
}

 RSLProduct1(const T1 RSL_p1) : RSL_f1(RSL_p1){}

RSLProduct1 operator=(const RSLProduct1& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
return *this;
}

bool operator==(const RSLProduct1& RSL_v) const{
return RSL_f1 == RSL_v.RSL_f1;
}

bool operator!=(const RSLProduct1& RSL_v) const{
return !operator==(RSL_v);
}

};

template<class T1, RSL_cons_fun RSL_cons>
string RSL_to_string(const RSLProduct1<T1, RSL_cons>& RSL_v){
  string s = RSL_cons();
  return s + "(" + RSL_to_string(RSL_v.RSL_f1) + ')';
}

#ifdef RSL_io
template<class T1, RSL_cons_fun RSL_cons>
inline ostream& operator<<(ostream& RSL_os, const RSLProduct1<T1, RSL_cons>& RSL_v){
RSL_os << RSL_cons() << "(";
RSL_os << RSL_v.RSL_f1;
RSL_os << ")";
return RSL_os;
}

template<class T1, RSL_cons_fun RSL_cons>
inline istream& operator>>(istream& RSL_is, RSLProduct1<T1, RSL_cons>& RSL_v){
RSL_input_token_type RSL_token;
char* cons = RSL_cons();

 if (strlen(cons) != 0)
   {
     RSL_input_cons(RSL_is, RSL_token, cons);
     if (!(RSL_is && RSL_token == RSL_constructor_token))
       {
	 RSL_is.clear(ios::badbit);
	 return RSL_is;
       }
   }
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_lpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T1 RSL_p1;

RSL_is >> RSL_p1;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_rpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_v = RSLProduct1<T1, RSL_cons>(RSL_p1);
return RSL_is;
}

#endif // RSL_io

template<class T1, class T2, RSL_cons_fun RSL_cons>
struct RSLProduct2{
T1 RSL_f1;
T2 RSL_f2;
 RSLProduct2(){}

 RSLProduct2(const RSLProduct2& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
}

 RSLProduct2(const T1 RSL_p1, const T2 RSL_p2) : RSL_f1(RSL_p1), RSL_f2(RSL_p2){}

RSLProduct2 operator=(const RSLProduct2& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
return *this;
}

bool operator==(const RSLProduct2& RSL_v) const{
return RSL_f1 == RSL_v.RSL_f1 && RSL_f2 == RSL_v.RSL_f2;
}

bool operator!=(const RSLProduct2& RSL_v) const{
return !operator==(RSL_v);
}

};

template<class T1, class T2, RSL_cons_fun RSL_cons>
string RSL_to_string(const RSLProduct2<T1, T2, RSL_cons>& RSL_v){
  string s = RSL_cons();
  return s + "(" + RSL_to_string(RSL_v.RSL_f1) + ',' + RSL_to_string(RSL_v.RSL_f2) + ')';
}

#ifdef RSL_io
template<class T1, class T2, RSL_cons_fun RSL_cons>
inline ostream& operator<<(ostream& RSL_os, const RSLProduct2<T1, T2, RSL_cons>& RSL_v){
RSL_os << RSL_cons() << "(";
RSL_os << RSL_v.RSL_f1;
RSL_os << "," << RSL_v.RSL_f2;
RSL_os << ")";
return RSL_os;
}

template<class T1, class T2, RSL_cons_fun RSL_cons>
inline istream& operator>>(istream& RSL_is, RSLProduct2<T1, T2, RSL_cons>& RSL_v){
RSL_input_token_type RSL_token;
char* cons = RSL_cons();

 if (strlen(cons) != 0)
   {
     RSL_input_cons(RSL_is, RSL_token, cons);
     if (!(RSL_is && RSL_token == RSL_constructor_token))
       {
	 RSL_is.clear(ios::badbit);
	 return RSL_is;
       }
   }
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_lpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T1 RSL_p1;

RSL_is >> RSL_p1;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T2 RSL_p2;

RSL_is >> RSL_p2;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_rpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_v = RSLProduct2<T1, T2, RSL_cons>(RSL_p1, RSL_p2);
return RSL_is;
}

#endif // RSL_io

template<class T1, class T2, class T3, RSL_cons_fun RSL_cons>
struct RSLProduct3{
T1 RSL_f1;
T2 RSL_f2;
T3 RSL_f3;
 RSLProduct3(){}

 RSLProduct3(const RSLProduct3& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
}

 RSLProduct3(const T1 RSL_p1, const T2 RSL_p2, const T3 RSL_p3) : RSL_f1(RSL_p1), RSL_f2(RSL_p2), RSL_f3(RSL_p3){}

RSLProduct3 operator=(const RSLProduct3& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
return *this;
}

bool operator==(const RSLProduct3& RSL_v) const{
return RSL_f1 == RSL_v.RSL_f1 && RSL_f2 == RSL_v.RSL_f2 && RSL_f3 == RSL_v.RSL_f3;
}

bool operator!=(const RSLProduct3& RSL_v) const{
return !operator==(RSL_v);
}

};

template<class T1, class T2, class T3, RSL_cons_fun RSL_cons>
string RSL_to_string(const RSLProduct3<T1, T2, T3, RSL_cons>& RSL_v){
  string s = RSL_cons();
  return s + "(" + RSL_to_string(RSL_v.RSL_f1) + ',' + RSL_to_string(RSL_v.RSL_f2) + ',' + RSL_to_string(RSL_v.RSL_f3) + ')';
}

#ifdef RSL_io
template<class T1, class T2, class T3, RSL_cons_fun RSL_cons>
inline ostream& operator<<(ostream& RSL_os, const RSLProduct3<T1, T2, T3, RSL_cons>& RSL_v){
RSL_os << RSL_cons() << "(";
RSL_os << RSL_v.RSL_f1;
RSL_os << "," << RSL_v.RSL_f2;
RSL_os << "," << RSL_v.RSL_f3;
RSL_os << ")";
return RSL_os;
}

template<class T1, class T2, class T3, RSL_cons_fun RSL_cons>
inline istream& operator>>(istream& RSL_is, RSLProduct3<T1, T2, T3, RSL_cons>& RSL_v){
RSL_input_token_type RSL_token;
char* cons = RSL_cons();

 if (strlen(cons) != 0)
   {
     RSL_input_cons(RSL_is, RSL_token, cons);
     if (!(RSL_is && RSL_token == RSL_constructor_token))
       {
	 RSL_is.clear(ios::badbit);
	 return RSL_is;
       }
   }
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_lpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T1 RSL_p1;

RSL_is >> RSL_p1;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T2 RSL_p2;

RSL_is >> RSL_p2;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T3 RSL_p3;

RSL_is >> RSL_p3;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_rpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_v = RSLProduct3<T1, T2, T3, RSL_cons>(RSL_p1, RSL_p2, RSL_p3);
return RSL_is;
}

#endif // RSL_io

template<class T1, class T2, class T3, class T4, RSL_cons_fun RSL_cons>
struct RSLProduct4{
T1 RSL_f1;
T2 RSL_f2;
T3 RSL_f3;
T4 RSL_f4;
 RSLProduct4(){}

 RSLProduct4(const RSLProduct4& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
}

 RSLProduct4(const T1 RSL_p1, const T2 RSL_p2, const T3 RSL_p3, const T4 RSL_p4) : RSL_f1(RSL_p1), RSL_f2(RSL_p2), RSL_f3(RSL_p3), RSL_f4(RSL_p4){}

RSLProduct4 operator=(const RSLProduct4& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
return *this;
}

bool operator==(const RSLProduct4& RSL_v) const{
return RSL_f1 == RSL_v.RSL_f1 && RSL_f2 == RSL_v.RSL_f2 && RSL_f3 == RSL_v.RSL_f3 && RSL_f4 == RSL_v.RSL_f4;
}

bool operator!=(const RSLProduct4& RSL_v) const{
return !operator==(RSL_v);
}

};

template<class T1, class T2, class T3, class T4, RSL_cons_fun RSL_cons>
string RSL_to_string(const RSLProduct4<T1, T2, T3, T4, RSL_cons>& RSL_v){
  string s = RSL_cons();
  return s + "(" + RSL_to_string(RSL_v.RSL_f1) + ',' + RSL_to_string(RSL_v.RSL_f2) + ',' + RSL_to_string(RSL_v.RSL_f3) + ',' + RSL_to_string(RSL_v.RSL_f4) + ')';
}

#ifdef RSL_io
template<class T1, class T2, class T3, class T4, RSL_cons_fun RSL_cons>
inline ostream& operator<<(ostream& RSL_os, const RSLProduct4<T1, T2, T3, T4, RSL_cons>& RSL_v){
RSL_os << RSL_cons() << "(";
RSL_os << RSL_v.RSL_f1;
RSL_os << "," << RSL_v.RSL_f2;
RSL_os << "," << RSL_v.RSL_f3;
RSL_os << "," << RSL_v.RSL_f4;
RSL_os << ")";
return RSL_os;
}

template<class T1, class T2, class T3, class T4, RSL_cons_fun RSL_cons>
inline istream& operator>>(istream& RSL_is, RSLProduct4<T1, T2, T3, T4, RSL_cons>& RSL_v){
RSL_input_token_type RSL_token;
char* cons = RSL_cons();

 if (strlen(cons) != 0)
   {
     RSL_input_cons(RSL_is, RSL_token, cons);
     if (!(RSL_is && RSL_token == RSL_constructor_token))
       {
	 RSL_is.clear(ios::badbit);
	 return RSL_is;
       }
   }
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_lpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T1 RSL_p1;

RSL_is >> RSL_p1;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T2 RSL_p2;

RSL_is >> RSL_p2;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T3 RSL_p3;

RSL_is >> RSL_p3;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T4 RSL_p4;

RSL_is >> RSL_p4;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_rpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_v = RSLProduct4<T1, T2, T3, T4, RSL_cons>(RSL_p1, RSL_p2, RSL_p3, RSL_p4);
return RSL_is;
}

#endif // RSL_io

template<class T1, class T2, class T3, class T4, class T5, RSL_cons_fun RSL_cons>
struct RSLProduct5{
T1 RSL_f1;
T2 RSL_f2;
T3 RSL_f3;
T4 RSL_f4;
T5 RSL_f5;
 RSLProduct5(){}

 RSLProduct5(const RSLProduct5& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
RSL_f5 = RSL_v.RSL_f5;
}

 RSLProduct5(const T1 RSL_p1, const T2 RSL_p2, const T3 RSL_p3, const T4 RSL_p4, const T5 RSL_p5) : RSL_f1(RSL_p1), RSL_f2(RSL_p2), RSL_f3(RSL_p3), RSL_f4(RSL_p4), RSL_f5(RSL_p5){}

RSLProduct5 operator=(const RSLProduct5& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
RSL_f5 = RSL_v.RSL_f5;
return *this;
}

bool operator==(const RSLProduct5& RSL_v) const{
return RSL_f1 == RSL_v.RSL_f1 && RSL_f2 == RSL_v.RSL_f2 && RSL_f3 == RSL_v.RSL_f3 && RSL_f4 == RSL_v.RSL_f4 && RSL_f5 == RSL_v.RSL_f5;
}

bool operator!=(const RSLProduct5& RSL_v) const{
return !operator==(RSL_v);
}

};

template<class T1, class T2, class T3, class T4, class T5, RSL_cons_fun RSL_cons>
string RSL_to_string(const RSLProduct5<T1, T2, T3, T4, T5, RSL_cons>& RSL_v){
  string s = RSL_cons();
  return s + "(" + RSL_to_string(RSL_v.RSL_f1) + ',' + RSL_to_string(RSL_v.RSL_f2) + ',' + RSL_to_string(RSL_v.RSL_f3) + ',' + RSL_to_string(RSL_v.RSL_f4) + ',' + RSL_to_string(RSL_v.RSL_f5) + ')';
}

#ifdef RSL_io
template<class T1, class T2, class T3, class T4, class T5, RSL_cons_fun RSL_cons>
inline ostream& operator<<(ostream& RSL_os, const RSLProduct5<T1, T2, T3, T4, T5, RSL_cons>& RSL_v){
RSL_os << RSL_cons() << "(";
RSL_os << RSL_v.RSL_f1;
RSL_os << "," << RSL_v.RSL_f2;
RSL_os << "," << RSL_v.RSL_f3;
RSL_os << "," << RSL_v.RSL_f4;
RSL_os << "," << RSL_v.RSL_f5;
RSL_os << ")";
return RSL_os;
}

template<class T1, class T2, class T3, class T4, class T5, RSL_cons_fun RSL_cons>
inline istream& operator>>(istream& RSL_is, RSLProduct5<T1, T2, T3, T4, T5, RSL_cons>& RSL_v){
RSL_input_token_type RSL_token;
char* cons = RSL_cons();

 if (strlen(cons) != 0)
   {
     RSL_input_cons(RSL_is, RSL_token, cons);
     if (!(RSL_is && RSL_token == RSL_constructor_token))
       {
	 RSL_is.clear(ios::badbit);
	 return RSL_is;
       }
   }
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_lpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T1 RSL_p1;

RSL_is >> RSL_p1;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T2 RSL_p2;

RSL_is >> RSL_p2;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T3 RSL_p3;

RSL_is >> RSL_p3;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T4 RSL_p4;

RSL_is >> RSL_p4;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T5 RSL_p5;

RSL_is >> RSL_p5;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_rpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_v = RSLProduct5<T1, T2, T3, T4, T5, RSL_cons>(RSL_p1, RSL_p2, RSL_p3, RSL_p4, RSL_p5);
return RSL_is;
}

#endif // RSL_io

template<class T1, class T2, class T3, class T4, class T5, class T6, RSL_cons_fun RSL_cons>
struct RSLProduct6{
T1 RSL_f1;
T2 RSL_f2;
T3 RSL_f3;
T4 RSL_f4;
T5 RSL_f5;
T6 RSL_f6;
 RSLProduct6(){}

 RSLProduct6(const RSLProduct6& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
RSL_f5 = RSL_v.RSL_f5;
RSL_f6 = RSL_v.RSL_f6;
}

 RSLProduct6(const T1 RSL_p1, const T2 RSL_p2, const T3 RSL_p3, const T4 RSL_p4, const T5 RSL_p5, const T6 RSL_p6) : RSL_f1(RSL_p1), RSL_f2(RSL_p2), RSL_f3(RSL_p3), RSL_f4(RSL_p4), RSL_f5(RSL_p5), RSL_f6(RSL_p6){}

RSLProduct6 operator=(const RSLProduct6& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
RSL_f5 = RSL_v.RSL_f5;
RSL_f6 = RSL_v.RSL_f6;
return *this;
}

bool operator==(const RSLProduct6& RSL_v) const{
return RSL_f1 == RSL_v.RSL_f1 && RSL_f2 == RSL_v.RSL_f2 && RSL_f3 == RSL_v.RSL_f3 && RSL_f4 == RSL_v.RSL_f4 && RSL_f5 == RSL_v.RSL_f5 && RSL_f6 == RSL_v.RSL_f6;
}

bool operator!=(const RSLProduct6& RSL_v) const{
return !operator==(RSL_v);
}

};

template<class T1, class T2, class T3, class T4, class T5, class T6, RSL_cons_fun RSL_cons>
string RSL_to_string(const RSLProduct6<T1, T2, T3, T4, T5, T6, RSL_cons>& RSL_v){
  string s = RSL_cons();
  return s + "(" + RSL_to_string(RSL_v.RSL_f1) + ',' + RSL_to_string(RSL_v.RSL_f2) + ',' + RSL_to_string(RSL_v.RSL_f3) + ',' + RSL_to_string(RSL_v.RSL_f4) + ',' + RSL_to_string(RSL_v.RSL_f5) + ',' + RSL_to_string(RSL_v.RSL_f6) + ')';
}

#ifdef RSL_io
template<class T1, class T2, class T3, class T4, class T5, class T6, RSL_cons_fun RSL_cons>
inline ostream& operator<<(ostream& RSL_os, const RSLProduct6<T1, T2, T3, T4, T5, T6, RSL_cons>& RSL_v){
RSL_os << RSL_cons() << "(";
RSL_os << RSL_v.RSL_f1;
RSL_os << "," << RSL_v.RSL_f2;
RSL_os << "," << RSL_v.RSL_f3;
RSL_os << "," << RSL_v.RSL_f4;
RSL_os << "," << RSL_v.RSL_f5;
RSL_os << "," << RSL_v.RSL_f6;
RSL_os << ")";
return RSL_os;
}

template<class T1, class T2, class T3, class T4, class T5, class T6, RSL_cons_fun RSL_cons>
inline istream& operator>>(istream& RSL_is, RSLProduct6<T1, T2, T3, T4, T5, T6, RSL_cons>& RSL_v){
RSL_input_token_type RSL_token;
char* cons = RSL_cons();

 if (strlen(cons) != 0)
   {
     RSL_input_cons(RSL_is, RSL_token, cons);
     if (!(RSL_is && RSL_token == RSL_constructor_token))
       {
	 RSL_is.clear(ios::badbit);
	 return RSL_is;
       }
   }
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_lpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T1 RSL_p1;

RSL_is >> RSL_p1;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T2 RSL_p2;

RSL_is >> RSL_p2;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T3 RSL_p3;

RSL_is >> RSL_p3;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T4 RSL_p4;

RSL_is >> RSL_p4;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T5 RSL_p5;

RSL_is >> RSL_p5;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T6 RSL_p6;

RSL_is >> RSL_p6;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_rpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_v = RSLProduct6<T1, T2, T3, T4, T5, T6, RSL_cons>(RSL_p1, RSL_p2, RSL_p3, RSL_p4, RSL_p5, RSL_p6);
return RSL_is;
}

#endif // RSL_io

template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, RSL_cons_fun RSL_cons>
struct RSLProduct7{
T1 RSL_f1;
T2 RSL_f2;
T3 RSL_f3;
T4 RSL_f4;
T5 RSL_f5;
T6 RSL_f6;
T7 RSL_f7;
 RSLProduct7(){}

 RSLProduct7(const RSLProduct7& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
RSL_f5 = RSL_v.RSL_f5;
RSL_f6 = RSL_v.RSL_f6;
RSL_f7 = RSL_v.RSL_f7;
}

 RSLProduct7(const T1 RSL_p1, const T2 RSL_p2, const T3 RSL_p3, const T4 RSL_p4, const T5 RSL_p5, const T6 RSL_p6, const T7 RSL_p7) : RSL_f1(RSL_p1), RSL_f2(RSL_p2), RSL_f3(RSL_p3), RSL_f4(RSL_p4), RSL_f5(RSL_p5), RSL_f6(RSL_p6), RSL_f7(RSL_p7){}

RSLProduct7 operator=(const RSLProduct7& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
RSL_f5 = RSL_v.RSL_f5;
RSL_f6 = RSL_v.RSL_f6;
RSL_f7 = RSL_v.RSL_f7;
return *this;
}

bool operator==(const RSLProduct7& RSL_v) const{
return RSL_f1 == RSL_v.RSL_f1 && RSL_f2 == RSL_v.RSL_f2 && RSL_f3 == RSL_v.RSL_f3 && RSL_f4 == RSL_v.RSL_f4 && RSL_f5 == RSL_v.RSL_f5 && RSL_f6 == RSL_v.RSL_f6 && RSL_f7 == RSL_v.RSL_f7;
}

bool operator!=(const RSLProduct7& RSL_v) const{
return !operator==(RSL_v);
}

};

template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, RSL_cons_fun RSL_cons>
string RSL_to_string(const RSLProduct7<T1, T2, T3, T4, T5, T6, T7, RSL_cons>& RSL_v){
  string s = RSL_cons();
  return s + "(" + RSL_to_string(RSL_v.RSL_f1) + ',' + RSL_to_string(RSL_v.RSL_f2) + ',' + RSL_to_string(RSL_v.RSL_f3) + ',' + RSL_to_string(RSL_v.RSL_f4) + ',' + RSL_to_string(RSL_v.RSL_f5) + ',' + RSL_to_string(RSL_v.RSL_f6) + ',' + RSL_to_string(RSL_v.RSL_f7) + ')';
}

#ifdef RSL_io
template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, RSL_cons_fun RSL_cons>
inline ostream& operator<<(ostream& RSL_os, const RSLProduct7<T1, T2, T3, T4, T5, T6, T7, RSL_cons>& RSL_v){
RSL_os << "(";
RSL_os << RSL_v.RSL_f1;
RSL_os << "," << RSL_v.RSL_f2;
RSL_os << "," << RSL_v.RSL_f3;
RSL_os << "," << RSL_v.RSL_f4;
RSL_os << "," << RSL_v.RSL_f5;
RSL_os << "," << RSL_v.RSL_f6;
RSL_os << "," << RSL_v.RSL_f7;
RSL_os << ")";
return RSL_os;
}

template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, RSL_cons_fun RSL_cons>
inline istream& operator>>(istream& RSL_is, RSLProduct7<T1, T2, T3, T4, T5, T6, T7, RSL_cons>& RSL_v){
RSL_input_token_type RSL_token;
char* cons = RSL_cons();

 if (strlen(cons) != 0)
   {
     RSL_input_cons(RSL_is, RSL_token, cons);
     if (!(RSL_is && RSL_token == RSL_constructor_token))
       {
	 RSL_is.clear(ios::badbit);
	 return RSL_is;
       }
   }
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_lpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T1 RSL_p1;

RSL_is >> RSL_p1;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T2 RSL_p2;

RSL_is >> RSL_p2;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T3 RSL_p3;

RSL_is >> RSL_p3;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T4 RSL_p4;

RSL_is >> RSL_p4;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T5 RSL_p5;

RSL_is >> RSL_p5;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T6 RSL_p6;

RSL_is >> RSL_p6;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T7 RSL_p7;

RSL_is >> RSL_p7;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_rpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_v = RSLProduct7<T1, T2, T3, T4, T5, T6, T7, RSL_cons>(RSL_p1, RSL_p2, RSL_p3, RSL_p4, RSL_p5, RSL_p6, RSL_p7);
return RSL_is;
}

#endif // RSL_io

template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, RSL_cons_fun RSL_cons>
struct RSLProduct8{
T1 RSL_f1;
T2 RSL_f2;
T3 RSL_f3;
T4 RSL_f4;
T5 RSL_f5;
T6 RSL_f6;
T7 RSL_f7;
T8 RSL_f8;
 RSLProduct8(){}

 RSLProduct8(const RSLProduct8& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
RSL_f5 = RSL_v.RSL_f5;
RSL_f6 = RSL_v.RSL_f6;
RSL_f7 = RSL_v.RSL_f7;
RSL_f8 = RSL_v.RSL_f8;
}

 RSLProduct8(const T1 RSL_p1, const T2 RSL_p2, const T3 RSL_p3, const T4 RSL_p4, const T5 RSL_p5, const T6 RSL_p6, const T7 RSL_p7, const T8 RSL_p8) : RSL_f1(RSL_p1), RSL_f2(RSL_p2), RSL_f3(RSL_p3), RSL_f4(RSL_p4), RSL_f5(RSL_p5), RSL_f6(RSL_p6), RSL_f7(RSL_p7), RSL_f8(RSL_p8){}

RSLProduct8 operator=(const RSLProduct8& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
RSL_f5 = RSL_v.RSL_f5;
RSL_f6 = RSL_v.RSL_f6;
RSL_f7 = RSL_v.RSL_f7;
RSL_f8 = RSL_v.RSL_f8;
return *this;
}

bool operator==(const RSLProduct8& RSL_v) const{
return RSL_f1 == RSL_v.RSL_f1 && RSL_f2 == RSL_v.RSL_f2 && RSL_f3 == RSL_v.RSL_f3 && RSL_f4 == RSL_v.RSL_f4 && RSL_f5 == RSL_v.RSL_f5 && RSL_f6 == RSL_v.RSL_f6 && RSL_f7 == RSL_v.RSL_f7 && RSL_f8 == RSL_v.RSL_f8;
}

bool operator!=(const RSLProduct8& RSL_v) const{
return !operator==(RSL_v);
}

};


template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, RSL_cons_fun RSL_cons>
string RSL_to_string(const RSLProduct8<T1, T2, T3, T4, T5, T6, T7, T8, RSL_cons>& RSL_v){
  string s = RSL_cons();
  return s + "(" + RSL_to_string(RSL_v.RSL_f1) + ',' + RSL_to_string(RSL_v.RSL_f2) + ',' + RSL_to_string(RSL_v.RSL_f3) + ',' + RSL_to_string(RSL_v.RSL_f4) + ',' + RSL_to_string(RSL_v.RSL_f5) + ',' + RSL_to_string(RSL_v.RSL_f6) + ',' + RSL_to_string(RSL_v.RSL_f7) + ',' + RSL_to_string(RSL_v.RSL_f8) + ')';
}

#ifdef RSL_io
template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, RSL_cons_fun RSL_cons>
inline ostream& operator<<(ostream& RSL_os, const RSLProduct8<T1, T2, T3, T4, T5, T6, T7, T8, RSL_cons>& RSL_v){
RSL_os << "(";
RSL_os << RSL_v.RSL_f1;
RSL_os << "," << RSL_v.RSL_f2;
RSL_os << "," << RSL_v.RSL_f3;
RSL_os << "," << RSL_v.RSL_f4;
RSL_os << "," << RSL_v.RSL_f5;
RSL_os << "," << RSL_v.RSL_f6;
RSL_os << "," << RSL_v.RSL_f7;
RSL_os << "," << RSL_v.RSL_f8;
RSL_os << ")";
return RSL_os;
}

template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, RSL_cons_fun RSL_cons>
inline istream& operator>>(istream& RSL_is, RSLProduct8<T1, T2, T3, T4, T5, T6,T7, T8, RSL_cons>& RSL_v){
RSL_input_token_type RSL_token;
char* cons = RSL_cons();

 if (strlen(cons) != 0)
   {
     RSL_input_cons(RSL_is, RSL_token, cons);
     if (!(RSL_is && RSL_token == RSL_constructor_token))
       {
	 RSL_is.clear(ios::badbit);
	 return RSL_is;
       }
   }
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_lpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T1 RSL_p1;

RSL_is >> RSL_p1;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T2 RSL_p2;

RSL_is >> RSL_p2;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T3 RSL_p3;

RSL_is >> RSL_p3;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T4 RSL_p4;

RSL_is >> RSL_p4;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T5 RSL_p5;

RSL_is >> RSL_p5;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T6 RSL_p6;

RSL_is >> RSL_p6;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T7 RSL_p7;

RSL_is >> RSL_p7;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T8 RSL_p8;

RSL_is >> RSL_p8;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_rpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_v = RSLProduct8<T1, T2, T3, T4, T5, T6, T7, T8, RSL_cons>(RSL_p1, RSL_p2, RSL_p3, RSL_p4, RSL_p5, RSL_p6, RSL_p7, RSL_p8);
return RSL_is;
}

#endif // RSL_io

template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class T9, RSL_cons_fun RSL_cons>
struct RSLProduct9{
T1 RSL_f1;
T2 RSL_f2;
T3 RSL_f3;
T4 RSL_f4;
T5 RSL_f5;
T6 RSL_f6;
T7 RSL_f7;
T8 RSL_f8;
T9 RSL_f9;
 RSLProduct9(){}

 RSLProduct9(const RSLProduct9& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
RSL_f5 = RSL_v.RSL_f5;
RSL_f6 = RSL_v.RSL_f6;
RSL_f7 = RSL_v.RSL_f7;
RSL_f8 = RSL_v.RSL_f8;
RSL_f9 = RSL_v.RSL_f9;
}

 RSLProduct9(const T1 RSL_p1, const T2 RSL_p2, const T3 RSL_p3, const T4 RSL_p4, const T5 RSL_p5, const T6 RSL_p6, const T7 RSL_p7, const T8 RSL_p8, const T9 RSL_p9) : RSL_f1(RSL_p1), RSL_f2(RSL_p2), RSL_f3(RSL_p3), RSL_f4(RSL_p4), RSL_f5(RSL_p5), RSL_f6(RSL_p6), RSL_f7(RSL_p7), RSL_f8(RSL_p8), RSL_f9(RSL_p9){}

RSLProduct9 operator=(const RSLProduct9& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
RSL_f5 = RSL_v.RSL_f5;
RSL_f6 = RSL_v.RSL_f6;
RSL_f7 = RSL_v.RSL_f7;
RSL_f8 = RSL_v.RSL_f8;
RSL_f9 = RSL_v.RSL_f9;
return *this;
}

bool operator==(const RSLProduct9& RSL_v) const{
return RSL_f1 == RSL_v.RSL_f1 && RSL_f2 == RSL_v.RSL_f2 && RSL_f3 == RSL_v.RSL_f3 && RSL_f4 == RSL_v.RSL_f4 && RSL_f5 == RSL_v.RSL_f5 && RSL_f6 == RSL_v.RSL_f6 && RSL_f7 == RSL_v.RSL_f7 && RSL_f8 == RSL_v.RSL_f8 && RSL_f9 == RSL_v.RSL_f9;
}

bool operator!=(const RSLProduct9& RSL_v) const{
return !operator==(RSL_v);
}

};


template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class T9, RSL_cons_fun RSL_cons>
string RSL_to_string(const RSLProduct9<T1, T2, T3, T4, T5, T6, T7, T8, T9, RSL_cons>& RSL_v){
  string s = RSL_cons();
  return s + "(" + RSL_to_string(RSL_v.RSL_f1) + ',' + RSL_to_string(RSL_v.RSL_f2) + ',' + RSL_to_string(RSL_v.RSL_f3) + ',' + RSL_to_string(RSL_v.RSL_f4) + ',' + RSL_to_string(RSL_v.RSL_f5) + ',' + RSL_to_string(RSL_v.RSL_f6) + ',' + RSL_to_string(RSL_v.RSL_f7) + ',' + RSL_to_string(RSL_v.RSL_f8) + ',' + RSL_to_string(RSL_v.RSL_f9) + ')';
}

#ifdef RSL_io
template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class T9, RSL_cons_fun RSL_cons>
inline ostream& operator<<(ostream& RSL_os, const RSLProduct9<T1, T2, T3, T4, T5, T6, T7, T8, T9, RSL_cons>& RSL_v){
RSL_os << "(";
RSL_os << RSL_v.RSL_f1;
RSL_os << "," << RSL_v.RSL_f2;
RSL_os << "," << RSL_v.RSL_f3;
RSL_os << "," << RSL_v.RSL_f4;
RSL_os << "," << RSL_v.RSL_f5;
RSL_os << "," << RSL_v.RSL_f6;
RSL_os << "," << RSL_v.RSL_f7;
RSL_os << "," << RSL_v.RSL_f8;
RSL_os << "," << RSL_v.RSL_f9;
RSL_os << ")";
return RSL_os;
}

template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class T9, RSL_cons_fun RSL_cons>
inline istream& operator>>(istream& RSL_is, RSLProduct9<T1, T2, T3, T4, T5, T6,T7, T8, T9, RSL_cons>& RSL_v){
RSL_input_token_type RSL_token;
char* cons = RSL_cons();

 if (strlen(cons) != 0)
   {
     RSL_input_cons(RSL_is, RSL_token, cons);
     if (!(RSL_is && RSL_token == RSL_constructor_token))
       {
	 RSL_is.clear(ios::badbit);
	 return RSL_is;
       }
   }
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_lpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T1 RSL_p1;

RSL_is >> RSL_p1;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T2 RSL_p2;

RSL_is >> RSL_p2;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T3 RSL_p3;

RSL_is >> RSL_p3;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T4 RSL_p4;

RSL_is >> RSL_p4;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T5 RSL_p5;

RSL_is >> RSL_p5;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T6 RSL_p6;

RSL_is >> RSL_p6;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T7 RSL_p7;

RSL_is >> RSL_p7;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T8 RSL_p8;

RSL_is >> RSL_p8;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T9 RSL_p9;

RSL_is >> RSL_p9;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_rpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_v = RSLProduct9<T1, T2, T3, T4, T5, T6, T7, T8, T9, RSL_cons>(RSL_p1, RSL_p2, RSL_p3, RSL_p4, RSL_p5, RSL_p6, RSL_p7, RSL_p8, RSL_p9);
return RSL_is;
}

#endif // RSL_io

template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class T9, class T10, RSL_cons_fun RSL_cons>
struct RSLProduct10{
T1 RSL_f1;
T2 RSL_f2;
T3 RSL_f3;
T4 RSL_f4;
T5 RSL_f5;
T6 RSL_f6;
T7 RSL_f7;
T8 RSL_f8;
T9 RSL_f9;
T10 RSL_f10;
 RSLProduct10(){}

 RSLProduct10(const RSLProduct10& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
RSL_f5 = RSL_v.RSL_f5;
RSL_f6 = RSL_v.RSL_f6;
RSL_f7 = RSL_v.RSL_f7;
RSL_f8 = RSL_v.RSL_f8;
RSL_f9 = RSL_v.RSL_f9;
RSL_f10 = RSL_v.RSL_f10;
}

 RSLProduct10(const T1 RSL_p1, const T2 RSL_p2, const T3 RSL_p3, const T4 RSL_p4, const T5 RSL_p5, const T6 RSL_p6, const T7 RSL_p7, const T8 RSL_p8, const T9 RSL_p9, const T10 RSL_p10) : RSL_f1(RSL_p1), RSL_f2(RSL_p2), RSL_f3(RSL_p3), RSL_f4(RSL_p4), RSL_f5(RSL_p5), RSL_f6(RSL_p6), RSL_f7(RSL_p7), RSL_f8(RSL_p8), RSL_f9(RSL_p9), RSL_f10(RSL_p10){}

RSLProduct10 operator=(const RSLProduct10& RSL_v){
RSL_f1 = RSL_v.RSL_f1;
RSL_f2 = RSL_v.RSL_f2;
RSL_f3 = RSL_v.RSL_f3;
RSL_f4 = RSL_v.RSL_f4;
RSL_f5 = RSL_v.RSL_f5;
RSL_f6 = RSL_v.RSL_f6;
RSL_f7 = RSL_v.RSL_f7;
RSL_f8 = RSL_v.RSL_f8;
RSL_f9 = RSL_v.RSL_f9;
RSL_f10 = RSL_v.RSL_f10;
return *this;
}

bool operator==(const RSLProduct10& RSL_v) const{
return RSL_f1 == RSL_v.RSL_f1 && RSL_f2 == RSL_v.RSL_f2 && RSL_f3 == RSL_v.RSL_f3 && RSL_f4 == RSL_v.RSL_f4 && RSL_f5 == RSL_v.RSL_f5 && RSL_f6 == RSL_v.RSL_f6 && RSL_f7 == RSL_v.RSL_f7 && RSL_f8 == RSL_v.RSL_f8 && RSL_f9 == RSL_v.RSL_f9 && RSL_f10 == RSL_v.RSL_f10;
}

bool operator!=(const RSLProduct10& RSL_v) const{
return !operator==(RSL_v);
}

};

template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class T9, class T10, RSL_cons_fun RSL_cons>
string RSL_to_string(const RSLProduct10<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, RSL_cons>& RSL_v){
  string s = RSL_cons();
  return s + "(" + RSL_to_string(RSL_v.RSL_f1) + ',' + RSL_to_string(RSL_v.RSL_f2) + ',' + RSL_to_string(RSL_v.RSL_f3) + ',' + RSL_to_string(RSL_v.RSL_f4) + ',' + RSL_to_string(RSL_v.RSL_f5) + ',' + RSL_to_string(RSL_v.RSL_f6) + ',' + RSL_to_string(RSL_v.RSL_f7) + ',' + RSL_to_string(RSL_v.RSL_f8) + ',' + RSL_to_string(RSL_v.RSL_f9) + ',' + RSL_to_string(RSL_v.RSL_f10) + ')';
}

#ifdef RSL_io
template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class T9, class T10, RSL_cons_fun RSL_cons>
inline ostream& operator<<(ostream& RSL_os, const RSLProduct10<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, RSL_cons>& RSL_v){
RSL_os << "(";
RSL_os << RSL_v.RSL_f1;
RSL_os << "," << RSL_v.RSL_f2;
RSL_os << "," << RSL_v.RSL_f3;
RSL_os << "," << RSL_v.RSL_f4;
RSL_os << "," << RSL_v.RSL_f5;
RSL_os << "," << RSL_v.RSL_f6;
RSL_os << "," << RSL_v.RSL_f7;
RSL_os << "," << RSL_v.RSL_f8;
RSL_os << "," << RSL_v.RSL_f9;
RSL_os << "," << RSL_v.RSL_f10;
RSL_os << ")";
return RSL_os;
}

template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class T9, class T10, RSL_cons_fun RSL_cons>
inline istream& operator>>(istream& RSL_is, RSLProduct10<T1, T2, T3, T4, T5, T6,T7, T8, T9, T10, RSL_cons>& RSL_v){
RSL_input_token_type RSL_token;
char* cons = RSL_cons();

 if (strlen(cons) != 0)
   {
     RSL_input_cons(RSL_is, RSL_token, cons);
     if (!(RSL_is && RSL_token == RSL_constructor_token))
       {
	 RSL_is.clear(ios::badbit);
	 return RSL_is;
       }
   }
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_lpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T1 RSL_p1;

RSL_is >> RSL_p1;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T2 RSL_p2;

RSL_is >> RSL_p2;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T3 RSL_p3;

RSL_is >> RSL_p3;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T4 RSL_p4;

RSL_is >> RSL_p4;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T5 RSL_p5;

RSL_is >> RSL_p5;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T6 RSL_p6;

RSL_is >> RSL_p6;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T7 RSL_p7;

RSL_is >> RSL_p7;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T8 RSL_p8;

RSL_is >> RSL_p8;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T9 RSL_p9;

RSL_is >> RSL_p9;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_comma_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
T10 RSL_p10;

RSL_is >> RSL_p10;
if (!RSL_is)
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_input_token(RSL_is, RSL_token);
if (!(RSL_is && RSL_token == RSL_rpar_token))
{
RSL_is.clear(ios::badbit);
return RSL_is;
}
RSL_v = RSLProduct10<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, RSL_cons>(RSL_p1, RSL_p2, RSL_p3, RSL_p4, RSL_p5, RSL_p6, RSL_p7, RSL_p8, RSL_p9, RSL_p10);
return RSL_is;
}

#endif // RSL_io


#endif // _RSL_prod_h
