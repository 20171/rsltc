/* 
RSL Type Checker
Copyright (C) 1998 UNU/IIST

raise@iist.unu.edu
*/

#define PRIVATE static

#include <stdio.h>
#include "errmsg.h"
#include "idents.h"
#include "files.h"
#include "pos.h"

int errorcount = 0;
int warningcount = 0;

int HasErrors (void) {
  return (errorcount != 0);
}

int cccount = 0;

/* Error Messages                                                     */
/*--------------------------------------------------------------------*/

void Error(msg, pos)
   char *msg;
   long pos;
{
  Puterror(pos);
  Putmsg(msg);
  Putnl();
   exit(1);
}

/*--------------------------------------------------------------------*/

void yyerror(msg)
   char *msg;
{
   long pos;

   yyGetPos(& pos);
   Error(msg, pos);
}

/*--------------------------------------------------------------------*/

void yylexerror (msg)
   char *msg;
{
   long pos;

   yyGetPos(& pos);
   Error(msg, pos);
}


/*--------------------------------------------------------------------*/

/* Added for RSL */

void ErrorUsage (char *text)
{
   fprintf(stdout, "%s\n", text);
   exit (2);
}

/*--------------------------------------------------------------------*/

void Puterror(long pos)
{
  /*   char *msg;
   msg = (char *) malloc (20);
   sprintf(msg, "line %d, col %d: ",
                 yyLineAtPos(pos), yyColAtPos(pos));
   Put(msg);
   free(msg)
   */
  errorcount++;
  PrintStreamPos(stdout, pos);
}

/*--------------------------------------------------------------------*/

void Putwarning(long pos)
{
  /*   char *msg;
   msg = (char *) malloc (20);
   sprintf(msg, "line %d, col %d: ",
                 yyLineAtPos(pos), yyColAtPos(pos));
   Put(msg);
   free(msg)
   */
  warningcount++;
  PrintStreamPos(stdout, pos);
  fprintf(stdout, "Warning: ");
}

/*--------------------------------------------------------------------*/

void Putmsg(char *msg)
{
 fprintf(stdout, "%s", msg); 
}

/*--------------------------------------------------------------------*/

void Putchar(char character)
{
 fprintf(stdout, "\'%c\'", character); /* Convert to octal with \\%o? */
}

/*--------------------------------------------------------------------*/

void Putstr(char *msg)
{
 fprintf(stdout, "\"%s\"", msg); 
}

/*--------------------------------------------------------------------*/

void Putint(int N)
{
  fprintf(stdout, "%d", N);
}

/*--------------------------------------------------------------------*/

void Putnl ()
{
  fprintf(stdout, "\n");
}

/*--------------------------------------------------------------------*/
/* Confidence condition functions; move elsewhere?                    */
/*--------------------------------------------------------------------*/

void Putcc(long pos)
{
  cccount++;
  PrintStreamPos(stdout, pos);
  fprintf(stdout, "CC:\n");
}


/*--------------------------------------------------------------------*/

void Putstdmsg(char *msg)
{
 fprintf(stdout, "%s", msg); 
}

/*--------------------------------------------------------------------*/

void Putstdnl ()
{
  fprintf(stdout, "\n");
}

/*--------------------------------------------------------------------*/

void FinalMessage (int ccwanted)
{

  if (ccwanted) {
    fprintf(stdout, "rsltc completed: %d confidence condition(s) generated\n", cccount);
  }
  fprintf(stdout, "rsltc completed: %d error(s) %d warning(s)\n", errorcount, warningcount);
}
   
/*--------------------------------------------------------------------*/

/* Print 1 as A*, 2 as B*, etc.
   Assumes n1 % 100 in range 1 to 52 */

void Print_poly (int n1) 
{
  char *str;
  int n;

  if (n1 < 1) {
    Putmsg("\npoly number ");
    Putint(n1);
    Putmsg(" out of range\n");
    ErrorUsage("Internal error: please report");
  }
  n = (n1 - 1) % 52;
  str = (char *) malloc (3);
  if (n >= 26) {
    str[0] = 'a'+n-26;
  } else {
    str[0] = 'A'+n;
  }
  str[1] = '*';
  str[2] = '\0';
  Putmsg(str);
}
