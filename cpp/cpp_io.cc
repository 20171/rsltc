// This may look like C code, but it is really -*- C++ -*-
//
// Oct 23 1992. JR. Library file with auxillary definitions for RSL data type i/o.
//
// @(#) CAP PROGRAMATOR (SYPRO DK) $Id: cpp_io.cc,v 2.3 1994/05/19 13:30:15 she Exp $
//

#include "cpp_io.h"

#include <cctype>

static bool RSL_isop( char );

void RSL_fetch_token (istream& RSL_is, RSL_input_token_type& RSL_token, char* RSL_buf){
  char c = 0;

  RSL_is >> c;
  switch(c){
  case '(':
    RSL_token = RSL_lpar_token;
    break;
  case ')':
    RSL_token = RSL_rpar_token;
    break;
  case ',':
    RSL_token = RSL_comma_token;
    break;
  default:
    if( RSL_isop(c) ){
      int i = 1;

      RSL_buf[0] = c;
      RSL_is.get(c);
      if( c == '=' ){ /* <=, >= */
	RSL_buf[i++] = c;
	RSL_is.get(c);
      }
      if (!RSL_is) {
	RSL_is.clear(ios::badbit);
	RSL_buf[0] = 0;
	RSL_token = RSL_error_token;
      }
      else {
	RSL_is.putback(c);
	RSL_buf[i] = 0;
	RSL_token = RSL_constructor_token;
      }
    }
    else{
      if( !( isalpha(c) || c == '`' ) )
	RSL_token = RSL_error_token;
      else{
	int i = 1;

	RSL_buf[0] = c;
	RSL_is.get(c);
	while (RSL_is && ( isalnum(c) || c == '_' || c == '\'' || c == '`' )){
	  RSL_buf[i++] = c;
	  RSL_is.get(c);
	}
	if (!RSL_is) {
	  RSL_is.clear(ios::badbit);
	  RSL_buf[0] = 0;
	  RSL_token = RSL_error_token;
	}
	else {
	  RSL_is.putback(c);
	  RSL_buf[i] = 0;
	  RSL_token = RSL_constructor_token;
	}
      }
    }
  }
}

bool RSL_streq (const char* a, const char* b){
  int i = 0;

  while (a[i] == b[i] && a[i] != 0){ i++; }
  return a[i] == b[i];
}

bool RSL_streq (const char* a, const string b){
  return RSL_streq(a, b.c_str());
}

static bool RSL_isop( char c ){
  switch( c ){
    case '>': case '<': case '+': case '-':
    case '*': case '/': case '%': return true;
  }
  return false;
}
