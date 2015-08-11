/* 
RSL Type Checker
Copyright (C) 1998 UNU/IIST

raise@iist.unu.edu
*/

#include <stdio.h>
#include <string.h>
#include "pos.h"
#include "files.h"

/*--------------------------------------------------------------------*/

/* single chained List */
typedef struct PosInfoRec PosInfo; 
struct PosInfoRec
{
  /* line number in compilation         */
  /* concatenating all files            */
  long lineno;                 

  /* FileId of file containing lines    */
  /* up from lineno                     */
  FileId * file;                

  /* first line in file normally 1      */
  long startno;                
  
  PosInfo * next;
};

long yypos = 0;
long yyLineCount = 0;

/* Pointer to first and last Element in PosInfo List */
PosInfo * firstPosEntry = 0;    
PosInfo * lastPosEntry = 0;     

/*--------------------------------------------------------------------*/

void yyGetPos (long *ref_pos)
{
   *ref_pos = yypos-1;
}

/*--------------------------------------------------------------------*/

void yyPosToNextLine (void)
{
   yyLineCount++;
   yypos = yyLineCount*yyLCODE+1;
}

/*--------------------------------------------------------------------*/

void yyPosToFirstFile (FileId * file)
{
  yyLineCount = 1;
  yypos = yyLineCount*yyLCODE+1;
   
  firstPosEntry = (PosInfo *) malloc (sizeof (PosInfo));
  
  firstPosEntry->lineno = yyLineCount;
  firstPosEntry->file = file;
  firstPosEntry->startno = 1;
  firstPosEntry->next = 0;
  
  lastPosEntry = firstPosEntry;
}

/*--------------------------------------------------------------------*/

void yyPosToNextFile (FileId * file, long linenumber)
{
  yyLineCount++;
  yypos = yyLineCount*yyLCODE+1;
  
  lastPosEntry->next = (PosInfo *) malloc (sizeof (PosInfo));
  lastPosEntry = lastPosEntry->next;
  
  lastPosEntry->lineno = yyLineCount;
  lastPosEntry->file = file;
  lastPosEntry->startno = linenumber;
  lastPosEntry->next = 0;
}

/*--------------------------------------------------------------------*/

long yyLineAtPos (long pos)
{
   long l;
   l = pos / yyLCODE;
   return l;
}

/*--------------------------------------------------------------------*/

long yyColAtPos (long pos)
{
   long c;
   c = pos % yyLCODE;
   return c;
}

/*--------------------------------------------------------------------*/

void GetColAtPos (long pos,int *col)
{
   *col = pos % yyLCODE;
}

/*--------------------------------------------------------------------*/

void yyDecryptPos (long pos, long *line, long *column, FileId ** file)
{
  PosInfo * curr;
  long tmpline;
  
  tmpline = yyLineAtPos (pos);
  curr = firstPosEntry;
  if (curr->next != 0) {
    while (curr->next != 0 && curr->next->lineno <= tmpline) {
      curr = curr->next;
    }
  }
  *line   = tmpline - curr->lineno + curr->startno;
  *column = yyColAtPos (pos);
  *file   = curr->file;
}

/*--------------------------------------------------------------------*/

void DefaultPos (long *pos)
{
  *pos = DEFAULTPOS;
}

/*--------------------------------------------------------------------*/

void PrintStreamPos (FILE * dev, long pos)
{
  long line;
  long column;
  FileId *file;

  yyDecryptPos (pos, &line, &column, &file);  
  fprintFileId (dev, file);
  fprintf (dev, RSL_SUFFIX);
  fprintf (dev, ":%ld:%ld: ", line, column);
}

/*--------------------------------------------------------------------*/

void PrintPos (long pos)
{
  PrintStreamPos(stdout, pos);
}

/*--------------------------------------------------------------------*/

void PosAsString (long pos, char **res)
{
  long line;
  long column;
  FileId *file;
  char *filename;

  yyDecryptPos (pos, &line, &column, &file);
  fileid_to_string (file, &filename);
  *res = (char *) malloc (strlen(filename) + 20);
  sprintf(*res, "%s%s:%ld:%ld:", filename, RSL_SUFFIX, line, column); 
}

/*--------------------------------------------------------------------*/

void PosDecrypt (long pos, char **res, char **l, char **c )
{
  long line;
  long column;
  FileId *file;
  char *filename;

  yyDecryptPos (pos, &line, &column, &file);
  fileid_to_string (file, &filename);
  *res = (char *) malloc (strlen(filename) + 5);
  sprintf(*res, "%s%s", filename, RSL_SUFFIX); 
  *l = (char *) malloc (10);
  sprintf(*l, "%ld", line);
  *c = (char *) malloc (10);
  sprintf(*c, "%ld", column);
}

/*--------------------------------------------------------------------*/

void LinePosAsString (long pos, char **res)
{
  long line;
  long column;
  FileId *file;
  char *filename;

  yyDecryptPos (pos, &line, &column, &file);
  fileid_to_string (file, &filename);
  *res = (char *) malloc (strlen(filename) + 20);
  sprintf(*res, "%ld", line); 
}

/*--------------------------------------------------------------------*/

void PrefixWithPos (long pos, char * str, char **res)
{
  long line;
  long column;
  FileId *file;
  char *filename;

  yyDecryptPos (pos, &line, &column, &file);
  fileid_to_string (file, &filename);
  *res = (char *) malloc (strlen(filename) + strlen(str) + 24);
  sprintf(*res, "-- %s%s:%ld:%ld: %s",
	        filename, RSL_SUFFIX, line, column, str); 

}

void PrefixAsComment (char * str, char **res)
{
  *res = (char *) malloc (strlen(str) + 8);
  sprintf(*res, "-- %s", str);
}

/*--------------------------------------------------------------------*/
/* Debug routine */
/*--------------------------------------------------------------------*/

void DumpPosTab (void)
{
  PosInfo * curr;
  
  printf ("\n-------------------\n");
  printf ("pos table dump\n");
  printf ("-------------------\n");
  curr = firstPosEntry;
  while (curr != 0) {
    printf ("  lineno : % 5ld, startno : % 5ld, file : ", 
	    curr->lineno, curr->startno);
    fprintFileId (stdout, curr->file);
    printf ("\n");
    curr = curr->next;
  }
}

/*--------------------------------------------------------------------*/
/* Added for SAL use only                                             
/* -------------------------------------------------------------------*/

void IncreaseCol(long pos, long *newpos) {
  /* as the column is stored in the lower part of the word, it should be enough with adding one to whole value */
  *newpos = pos + 1;
}
