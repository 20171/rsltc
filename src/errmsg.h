/* 
RSL Type Checker
Copyright (C) 1998 UNU/IIST

raise@iist.unu.edu
*/

#ifndef _ERRMSG_H /* if not defined then errmsg.h has not yet been included */
#define _ERRMSG_H
#include <stdio.h>
#include "idents.h"

int HasErrors (void);
void Error(char *, long);
void ErrorUsage (char *);
void Puterror(long);
void Putmsg(char *);
void Putchar(char);
void Putstr(char *);
void Putint(int);
void Putnl ();
void Putcc(long);
void Putstdmsg(char *);
void Putstdnl ();
void FinalMessage (int);
void Next_star (char *, char **);

#endif  /* _ERRMSG_H */
