/* 
RSL Type Checker
Copyright (C) 1998 UNU/IIST

raise@iist.unu.edu
*/

#ifndef _IDENTS_H /* if not defined then idents.h has not yet been included */
#define _IDENTS_H

#include <stdlib.h>
#include <stdio.h>
#include "errmsg.h"

typedef struct IDENTSTRUCT *IDENT;
/* void string_to_id (char *, IDENT *); to avoid compiler warning from gen.l */
void id_to_string (IDENT, char **);
void C_id_to_string (IDENT, char **);
void SML_id_to_string (IDENT, char **);
void PVS_id_to_string (IDENT, char **);
void Axiom_name_to_string (IDENT, char **);
void Make_mk_name(char *, char **);
void Make_from_name(char *, char *, char **);
void Make_to_name(char *, char *, char **);
void Make_disjointness_name(char *, char **);
void Make_induction_name(char *, char **);
void Char_to_string(char, char **);
void Text_to_string(char *, char **);
void Text_to_c_string(char *, char **);
void Len(char *, int *);
void Int_to_string(int, char **);
int Contains_E(char *); 
int Is_Primed(char *);
void Remove_Prime(char*, char**);
#endif /* _IdentS_H */
