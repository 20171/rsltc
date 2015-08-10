/* RSL Type Checker */
/* Copyright (C) 1998 UNU/IIST */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

void Make_concatenation(ref_hd_str ,subscript, ref_value_expr)
     char * ref_hd_str; 
     long subscript;
     char * * ref_value_expr;
{
     char tostr[5];
     sprintf(tostr, "%ld_", subscript);
     *ref_value_expr = (char *) malloc (strlen(ref_hd_str) + 6);
     strcpy(*ref_value_expr,ref_hd_str);
     strcat(*ref_value_expr,tostr); 
}

/*----------------------------------------------------------------*/

void Concatenate3(char * str1, char * str2, char * str3, char * * res)
{
  *res = (char *) malloc (strlen(str1) + strlen(str2) + strlen(str3) + 1);
  if (*res == NULL) exit(1);
  sprintf(*res, "%s%s%s", str1, str2, str3);
}

void Concatenate(char * str1, char * str2, char * * res)
{
  *res = (char *) malloc (strlen(str1) + strlen(str2) + 1);
  if (*res == NULL) exit(1);
  sprintf(*res, "%s%s", str1, str2);
}

/* removes the last character of a string.  Intended for removing quotes. */
void PruneQuote(char * str, char * * res)
{
  int len;
  char *x;

  len = strlen(str);
  *res = (char *) malloc (len);
  if (*res == NULL) exit(1);
  strncpy(*res, str, len - 1);
  x = *res + len - 1;
  *x = '\0';
}

/*
main()
{
char * name[10];
Make_concatenation("xy",5,name);
printf("\n%s", name);
Make_concatenation("x",10,name);
printf("\n%s", name);
return 0;
}
*/
