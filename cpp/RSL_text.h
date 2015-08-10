/* 
RSL Type Checker
Copyright (C) 2000 UNU/IIST

raise@iist.unu.edu
*/

#ifndef _RSL_text_h
#define _RSL_text_h

#include "RSL_set.h"

struct RSL_char{
  char RSL_f1;
  RSL_char();

  RSL_char(const RSL_char&);

  RSL_char(const char);

  RSL_char& operator=(const RSL_char&);

  bool operator==(const RSL_char&) const;

  bool operator!=(const RSL_char&) const;

};

inline RSL_char::RSL_char(){
  RSL_f1 = '\0';
}

inline RSL_char::RSL_char(const RSL_char& RSL_v){
  RSL_f1 = RSL_v.RSL_f1;
}

inline RSL_char::RSL_char(const char RSL_p1) : RSL_f1(RSL_p1){}

inline RSL_char& RSL_char::operator=(const RSL_char& RSL_v){
  RSL_f1 = RSL_v.RSL_f1;
  return *this;
}

inline bool RSL_char::operator==(const RSL_char& RSL_v) const{
  return RSL_f1 == RSL_v.RSL_f1;
}

inline bool RSL_char::operator!=(const RSL_char& RSL_v) const{
  return !operator==(RSL_v);
}

string RSL_escape_char(const char c){
  string s = "";
  switch(c){
  case '\a': s = "\\a"; break;
  case '\b': s = "\\b"; break;
  case '\f': s = "\\f"; break;
  case '\n': s = "\\n"; break;
  case '\r': s = "\\r"; break;
  case '\t': s = "\\t"; break;
  case '\v': s = "\\v"; break;
  case '\\': s = "\\\\"; break;
  case '\?': s = "\\\?"; break;
  case '\'': s = "\\\'"; break;
  case '\"': s = "\\\""; break;
  default: s +=  c; break;
  }
  return s;
}
inline string RSL_char_to_string (const RSL_char& c) {
  string s = "'";
  s += RSL_escape_char(c.RSL_f1);
  s += '\'';
  return s;
}
inline string RSL_to_string (const RSL_char& c) {
  return RSL_char_to_string(c);
}

inline char RSL_to_cpp (const RSL_char& c) {
  return c.RSL_f1;
}

#ifdef RSL_io
inline ostream& operator<<(ostream& RSL_os, const RSL_char& RSL_v){
  RSL_os << "\'" << RSL_escape_char(RSL_v.RSL_f1) << "\'";
  return RSL_os;
}

char RSL_get_oct(istream& RSL_is){
  int r = 0;
  char c;
  RSL_is.get(c);
  while ((RSL_is) && isdigit(c)){
    r = 8*r + c - '0';
    RSL_is.get(c);
  }
  RSL_is.putback(c);
  return (char)r;
}

char RSL_get_hex(istream& RSL_is){
  int r = 0;
  char c;
  RSL_is.get(c);
  while ((RSL_is) && isxdigit(c)){
    switch (c){
    case '0': case '1': case '2': case '3': case '4':
    case '5': case '6': case '7': case '8': case '9':
      r = 16*r + c - '0'; break;
    case 'a': case 'A': r = 16*r + 10; break;
    case 'b': case 'B': r = 16*r + 11; break;
    case 'c': case 'C': r = 16*r + 12; break;
    case 'd': case 'D': r = 16*r + 13; break;
    case 'e': case 'E': r = 16*r + 14; break;
    case 'f': case 'F': r = 16*r + 15; break;
    default: break;
    }
    RSL_is.get(c);
  }
  RSL_is.putback(c);
  return (char)r;
}  

inline istream& operator>>(istream& RSL_is, RSL_char& RSL_v){
  char c;
  char c1;
  RSL_is.get(c);
  while (RSL_is && isspace(c) && (c != EOF)) RSL_is.get(c);
  if (!(c == '\'')){
    RSL_is.clear(ios::badbit);
    RSL_v = RSL_char();
    return RSL_is;
  }
  RSL_is.get(c1);
  if (c1 == '\\'){
    RSL_is.get(c1);
    if (isdigit(c1)){
      RSL_is.putback(c1);
      c1 = RSL_get_oct(RSL_is);
    }
    else switch (c1){
    case 'a': c1 = '\a'; break;
    case 'b': c1 = '\b'; break;
    case 'f': c1 = '\f'; break;
    case 'n': c1 = '\n'; break;
    case 'r': c1 = '\r'; break;
    case 't': c1 = '\t'; break;
    case 'v': c1 = '\v'; break;
    case 'x': c1 = RSL_get_hex(RSL_is);
    default: break;
    }
  }
  RSL_is.get(c);
  if (!(c == '\'')){
    RSL_is.clear(ios::badbit);
    RSL_v = RSL_char();
    return RSL_is;
  }
  RSL_v = RSL_char(c1);
  return RSL_is;
}

#endif // RSL_io



struct RSL_string{
  string RSL_f1;
  RSL_string();

  RSL_string(const RSL_string&);

  RSL_string(const string);

  RSL_string& operator=(const RSL_string&);

  bool operator==(const RSL_string&) const;

  bool operator!=(const RSL_string&) const;

  RSL_string operator+ (const RSL_string&) const;

  RSL_string operator+ (const string&) const;

  RSL_string operator+ (const RSL_char&) const;

  RSL_char operator[] (int) const;
};

inline RSL_string::RSL_string(){
  RSL_f1 = "";
}

inline RSL_string::RSL_string(const RSL_string& RSL_v){
  RSL_f1 = RSL_v.RSL_f1;
}

inline RSL_string::RSL_string(const string RSL_p1) : RSL_f1(RSL_p1){}

inline RSL_string& RSL_string::operator= (const RSL_string& RSL_v){
  RSL_f1 = RSL_v.RSL_f1;
  return *this;
}

inline bool RSL_string::operator==(const RSL_string& RSL_v) const{
  return RSL_f1 == RSL_v.RSL_f1;
}

inline bool RSL_string::operator!=(const RSL_string& RSL_v) const{
  return !operator==(RSL_v);
}

inline RSL_string RSL_string::operator+(const RSL_string& RSL_v) const{
  return RSL_string(RSL_f1 + RSL_v.RSL_f1);
}

inline RSL_string RSL_string::operator+(const string& s) const{
  return RSL_string(RSL_f1 + s);
}

inline RSL_string RSL_string::operator+(const RSL_char& RSL_v) const{
  return RSL_string(RSL_f1 + RSL_v.RSL_f1);
}

inline RSL_char RSL_string::operator[] (int n) const{
  return RSL_char(RSL_f1[n-1]);
}

inline RSL_char hd (const RSL_string& s){
  if (s.RSL_f1.length() == 0){
    RSL_fail("Head of empty text");
  }
  return RSL_char(s.RSL_f1[0]);
}

inline RSL_string tl (const RSL_string& s){
  int l = s.RSL_f1.length();
  if (l == 0){
    RSL_fail("Tail of empty text");
  }
  return RSL_string(s.RSL_f1.substr(1, l - 1));
}

inline RSL_string tl_n (const RSL_string& s, const int n){
  int l = s.RSL_f1.length();
  if (l < n){
    RSL_fail("Tail of empty text");
  }
  return RSL_string(s.RSL_f1.substr(n, l - n));
}

RSLSet<int>& inds (const RSL_string& s){
  RSLSet<int> *ps = new RSLSet<int> ();
  int l = s.RSL_f1.length();
  for (int i = 1; i <= l; ++i){
    ps->insert (new RSLSetNode<int> (i));
  }
  return *ps;
}

RSLSet<RSL_char>& elems (const RSL_string& s){
  RSLSet<RSL_char> *ps = new RSLSet<RSL_char> ();
  int l = s.RSL_f1.length();
  for (int i = 0; i < l; ++i){
    ps->insert (new RSLSetNode<RSL_char> (RSL_char(s.RSL_f1[i])));
  }
  return *ps;
}
  

inline int len (const RSL_string& s){
  return s.RSL_f1.length();
}
  
bool isin (const RSL_char& c, const RSL_string& s){
  return (s.RSL_f1.find(c.RSL_f1) != string::npos);
}

bool allt (bool (pred)(const RSL_char&), const RSL_string& s) {
  bool result = true;
  int l = len(s);
  for (int i = 0; i < l; ++i) {
    result = (pred)(RSL_char(s.RSL_f1[i]));
  }
  return result;
}

bool existst (bool (pred)(const RSL_char&), const RSL_string& s) {
  bool result = false;
  int l = len(s);
  for (int i = 0; i < l; ++i) {
    result = (pred)(RSL_char(s.RSL_f1[i]));
  }
  return result;
}

bool exists1t (bool (pred)(const RSL_char&), const RSL_string& s) {
  char candidate;
  int count = 0;
  int l = len(s);
  for (int i = 0; (i < l) && (count < 2); ++i) {
    if ((pred)(RSL_char(s.RSL_f1[i]))) {
      if (count == 0) {
	candidate = s.RSL_f1[i];
	count = 1;
      }
      else if (candidate != s.RSL_f1[i]) count++;
    }
  }
  return (count==1);
}

RSL_char RSL_chooset (bool (pred)(const RSL_char&), const RSL_string& s) {
  bool found = false;
  RSL_char r;
  int l = len(s);
  for (int i = 0; i < l; ++i) {
    r = RSL_char(s.RSL_f1[i]);
    if ((pred)(r)) {
      found = true;
    }
  }
  if (!found) RSL_fail("Choose from empty text");
  return r;
}
inline string RSL_string_to_string (const RSL_string& s) {
  return "\"" + s.RSL_f1 + '\"';
}
inline string RSL_to_string (const RSL_string& s) {
  return RSL_string_to_string(s);
}

inline string RSL_to_cpp (const RSL_string& s) {
  return s.RSL_f1;
}

#ifdef RSL_io
inline ostream& operator<<(ostream& RSL_os, const RSL_string& RSL_v){
  RSL_os << "\"" << RSL_v.RSL_f1 << "\"";
  return RSL_os;
}
inline istream& operator>>(istream& RSL_is, RSL_string& RSL_v){
  char c;
  RSL_is.get(c);
  while (RSL_is && isspace(c) && (c != EOF)) RSL_is.get(c);
  if (!(c == '\"')){
    RSL_is.clear(ios::badbit);
    RSL_v = RSL_string();
    return RSL_is;
  }
  string s = "";
  RSL_is.get(c);
  while (RSL_is && (c != '\"') && (c != EOF)){
    s += c;
    if (c == '\\'){
      RSL_is.get(c);
      if (RSL_is && (c != EOF)){
	s += c;
      }
      else {
	RSL_is.clear(ios::badbit);
        RSL_v = RSL_string();
        return RSL_is;
      }
    }
    RSL_is.get(c);
  }
  if ((!RSL_is) || (c == EOF)) {
    RSL_is.clear(ios::badbit);
    RSL_v = RSL_string();
    return RSL_is;
  }
  RSL_v = RSL_string(s);
  return RSL_is;
}

#endif // RSL_io

#endif //_RSL_text_h
