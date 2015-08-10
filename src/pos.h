/* 
RSL Type Checker
Copyright (C) 1998 UNU/IIST

raise@iist.unu.edu
*/

#ifndef _POS_H /* if not defined then errmsg.h has not yet been included */
#define _POS_H

#include <stdlib.h>
#include "files.h"

#define yyLCODE 100L

extern long yypos;
#define DEFAULTPOS 0
#define yysetpos() { yylval.attr[0] = yypos; yypos += yyleng; }

void yyGetPos (long *);

void yyPosToNextLine (void);
void yyPosToFirstFile (FileId *);
void yyPosToNextFile (FileId *, long);

long yyColAtPos (long);
void yyDecryptPos (long, long *, long *, FileId **);
void DefaultPos (long *);
void PrintStreamPos (FILE *, long);
void PrintPos (long);
void LinePosAsString (long, char **);
void PosDecrypt (long, char **, char **, char **);
void PosAsString (long, char **);
void PrefixWithPos (long, char *, char **);
void PrefixAsComment (char *, char **);
void DumpPosTab (void);

/* Added for SAL use:                           */
void IncreaseCol(long pos, long *newpos);
#endif  /* _POS_H */
