// This may look like C code, but it is really -*- C++ -*-
//
// Nov 4 1992. JR. Library file with auxillary definitions for RSL data type i/o.
//
// @(#) CAP PROGRAMATOR (SYPRO DK) $Id: cpp_io.h,v 2.3 1994/05/19 13:30:20 she Exp $
//

#ifndef _cpp_io_h_
#define _cpp_io_h_

#ifdef RSL_io
#include <iostream>
#endif

#include <cctype>

typedef int RSL_input_token_type;

enum {
RSL_null_token,
RSL_error_token,
RSL_lpar_token,
RSL_rpar_token,
RSL_comma_token,
RSL_constructor_token,
Token_StartIndex
};

void RSL_fetch_token(istream&, RSL_input_token_type&, char*);

bool RSL_streq (const char*, const char*);

#endif // _cpp_io_h_
