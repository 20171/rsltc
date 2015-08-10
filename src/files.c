/* 
RSL Type Checker
Copyright (C) 1998 UNU/IIST

raise@iist.unu.edu
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <limits.h>
#include "files.h"
#include "idents.h"
#include "errmsg.h"
#include "pos.h"

/*--------------------------------------------------------------------*/
/* IMPORTS */

extern FILE *yyin;
static int nest;
static int nline;
/* preget used when we need to look ahead twice 
   for comment starts and ends.  Avoids unsafe double ungetc.
   Set to null when no current double look ahead. */
static char preget;
/*--------------------------------------------------------------------*/
/* IMPLEMENTS */

void OpenFile (char *);
void Reopen (void);
void Find_comm(int *);
void Skip_string(char *,int *);
void Move_spaces(char *,char **);
void Change_sp(char *,char **);
void Block_to_str(char **,int *,int *,int *);
void Line_to_str(char **,int *,int *);
void Setplength(int);
void PpLength (int *);
FILE * NextFile (void);
static FileId *GetFileId (char *);
void string_to_fileid(char *, FileId **);
void strings_to_fileid(char *, char *, FileId **);
void fileid_to_string(FileId *, char **);
void prefix_path(char *, char *, char **);
void BaseName(FileId *, IDENT *);
void InsertContextFile (FileId *);

void Check_module_name (long, char *);
bool EqualFileId (IDENT, IDENT);

void fprintFileId (FILE *, FileId *);
void PrintFileId (FileId *);
void PrintDeps (void);
void Compact_path(char[]);




/* single chained list of source filenames split into directory path and id */
struct FileIdRec
{
   IDENT  basename;
   char * path;
   FileId * next;
};

/* points to the first (source), last and currently scanned entry  */
FileId * sourceFileIdEntry = 0;   
FileId * lastFileIdEntry = 0;     
FileId * currFileIdEntry = 0;      

/*--------------------------------------------------------------------*/

/* filename of current scanned file set by OpenFile and NextFile */
char currFilename [PATH_MAX + 1];

/*--------------------------------------------------------------------*/

/* absolute path of current file 
   set by SetPath and GetFileId; used by GetFileId
   so that all paths are absolute */
char currPath [PATH_MAX + 1];

/*--------------------------------------------------------------------*/

/* string used to print error messages */

char errMsg [PATH_MAX + 50];

/*--------------------------------------------------------------------*/

/* line length for pretty-printing */
static int plength;

/*--------------------------------------------------------------------*/
/* File handling */
/*--------------------------------------------------------------------*/

static bool EqualFilename (char *filename, char *pattern)
{
#ifdef _DOS
  #define filenamecompare(x, y) strcasecmp(x, y)
#else
  #define filenamecompare(x, y) strcmp(x, y)
#endif /* defined _DOS */

  if (filenamecompare(filename, pattern) == 0) {
    return TRUE;
  }
  return FALSE;
}

/*--------------------------------------------------------------------*/

void OpenFile (char * filename)
{
  char *suffptr;

  strcpy (currFilename, filename);
  strcpy (currPath, "");

  /* Add suffix if necessary, else check correct suffix */
  suffptr = strrchr (currFilename, (int) '.');
  if ((suffptr == (char *) 0) || (strncmp(suffptr, "./", 2) == 0))   {
    strcat (currFilename, RSL_SUFFIX);
    }
  else if (!EqualFilename (suffptr, RSL_SUFFIX)) {
    sprintf (errMsg, "'%s' is not a correct RSL source file name",
	     currFilename);
    ErrorUsage (errMsg);
  }
    

  yyin = fopen (currFilename, "r");
  if (yyin == NULL) {
    sprintf(errMsg, "cannot open source file: '%s'", currFilename);
    ErrorUsage (errMsg);
  }
  preget = '\0';
  
  sourceFileIdEntry = GetFileId (currFilename);

  /* set path of first file as base for future relative file names */
  strcpy(currPath, sourceFileIdEntry->path);

  lastFileIdEntry = sourceFileIdEntry;
  currFileIdEntry = sourceFileIdEntry;
  yyPosToFirstFile (currFileIdEntry);

}
/*--------------------------------------------------------------------*/
void Reopen (void)
{
  char *basename; 
  
  /* don't close current file - already closed */
  /* fclose (yyin); */
  
  id_to_string (sourceFileIdEntry->basename, &basename);
   
  sprintf (currFilename, "%s%s%s",
	   sourceFileIdEntry->path, basename, RSL_SUFFIX);
    

  yyin = fopen (currFilename, "r+");
  if (yyin == NULL) {
    printf("cannot open source file: '%s'", currFilename);
    exit(1); 
  }
  preget = '\0';
  
}


/*--------------------------------------------------------------------*/

FILE * NextFile (void)
{
  char *basename;
  FILE *next;

  /* close current file */
  fclose (yyin);

  currFileIdEntry = currFileIdEntry->next;
  if (currFileIdEntry == 0) /* no more files */ {
    return ((FILE *) 0);
  }

  /* set current path for relatively named context files in this file */
  strcpy(currPath, currFileIdEntry->path);

  id_to_string (currFileIdEntry->basename, &basename);
   
  /* search and open next file */
  sprintf (currFilename, "%s%s%s",
	   currFileIdEntry->path, basename, RSL_SUFFIX);
  next = fopen (currFilename, "r");
  if (next == NULL) {
    sprintf (errMsg, "cannot find RSL file '%s'", currFilename);
    ErrorUsage (errMsg);
    return ((FILE *) 0);
  }
  preget = '\0';
  /* reset pos */ 
  yyPosToNextFile(currFileIdEntry, 1);
  return (next);
}

/*--------------------------------------------------------------------*/

static FileId * GetFileId (char *filename)
{
  FileId * newId;
  int pathlen;
  int baselen;
  char absfilename [PATH_MAX + 1];
  char basename [PATH_MAX + 1];
  char * baseptr; 
  char * dosbaseptr; 
  char * suffptr;
  IDENT baseId;

  /* get absolute filename */
  if (strlen(filename) == 0) {
    sprintf(errMsg, "empty filename");
    ErrorUsage (errMsg);
  }

  if (filename[0] == '/') {
    /* filename is absolute */
    strcpy (absfilename, filename);
  }
#ifdef _DOS
  else if (filename[0] == '\\') {
    /* filename is absolute */
    strcpy (absfilename, filename);
  }
  else if ((strlen(filename) > 2) &&
	   (isalpha(filename[0])) && (filename[1] == ':')) {
    /* filename is absolute with drive letter */
    strcpy (absfilename, filename);
  }
#endif /* defined _DOS */
  else {
    if (strlen(currPath) > 0) {
    strcpy (absfilename, currPath);
    strcat (absfilename, filename);
    /* try to keep paths compact */
    Compact_path(absfilename);
    }
    else {
      strcpy (absfilename, filename);
    }
  }
  

  /* find start of basename */
  baseptr = strrchr (absfilename, (int) '/');

#ifdef _DOS
  dosbaseptr = strrchr (absfilename, (int) '\\');
  if (dosbaseptr > baseptr) baseptr = dosbaseptr;
#endif /* defined _DOS */

  if (baseptr == (char *) 0) {
    baseptr = absfilename;
  }
  else {
    baseptr++;
  }

  suffptr = strchr (baseptr, (int) '.');
  if (suffptr == (char *) 0) {
    suffptr = "";
  }
  pathlen = strlen (absfilename) - strlen (baseptr);
  baselen = strlen (baseptr) - strlen (suffptr);

  /* fill File entry completly */
  newId = (FileId *) malloc (sizeof (FileId));
  newId->path = (char *) malloc (pathlen + 1);
  
  strncpy (newId->path, absfilename, pathlen);
  newId->path [pathlen] = '\0';
  
  strncpy (basename, baseptr, baselen);
  basename [baselen] = '\0';
  string_to_id (basename, &baseId); 
  newId->basename = baseId;
  
  newId->next = 0;

  /* and return the new File entry */
  return newId;
}
  
/*--------------------------------------------------------------------*/

void string_to_fileid (char *filename, FileId **fileid)
{
  *fileid = GetFileId (filename);
}

/*--------------------------------------------------------------------*/

void strings_to_fileid (char *directory, char *filename, FileId **fileid)
{
  char * string;

  prefix_path(directory, filename, &string);
  *fileid = GetFileId (string);
}

/*--------------------------------------------------------------------*/

void prefix_path(char *str1, char *str2, char **string_ref)
{
  *string_ref = (char *) malloc(strlen(str1) + strlen(str2) + 2);
  strcpy(*string_ref, str1);
  strcat(*string_ref, "/");
  strcat(*string_ref, str2);
}

/*--------------------------------------------------------------------*/

void BaseName(FileId *fileid, IDENT *id)
{
  *id = fileid->basename;
}

/*--------------------------------------------------------------------*/

void fileid_to_string(FileId *fileid, char **ref_string)
{
  int pathlen;
  int baselen;
  char *base;

  pathlen = strlen(fileid->path);
  id_to_string(fileid->basename, &base);
  baselen = strlen(base);
  *ref_string = (char *) malloc(pathlen + baselen + 1);
  strcpy(*ref_string, fileid->path);
  strcat(*ref_string, base);
}

/*--------------------------------------------------------------------*/

void InsertContextFile (FileId * unit)
{
  FileId * i;
  char *f1;
  char *f2;
  int found;

  found = 0;
  id_to_string(unit->basename, &f1);
  i = sourceFileIdEntry;
  while ((i != 0) && (found == 0)) {
    id_to_string(i->basename, &f2);
    if (EqualFilename(f1, f2)) {
      found = 1;
    }
    else {
      i = i->next;
    }
  }
  if (found == 0) {
    lastFileIdEntry->next = unit;
    lastFileIdEntry = lastFileIdEntry->next;
  }
}


/*--------------------------------------------------------------------*/
/* Check on module names */
/*--------------------------------------------------------------------*/

void Check_module_name (long pos, char *modulename)
{
  char *filename;

  id_to_string(sourceFileIdEntry->basename, &filename);
  
  if (EqualFilename(modulename, filename)) {
    return;
  }
  Puterror(pos);
  Putmsg("Module name ");
  Putmsg(modulename);
  Putmsg(" does not match file name ");
  Putmsg(filename);
  Putmsg(".rsl\n");
  return;
  
}

/*--------------------------------------------------------------------*/

bool EqualFileId (IDENT id1, IDENT id2)
{
  char * s1;
  char * s2;

  if (id1 == id2) {
    return TRUE;
  }
#ifdef _DOS
  else {
    id_to_string(id1, &s1);
    id_to_string(id2, &s2);
    if (EqualFilename (s1, s2)) {
      return TRUE;
    }
  }
#endif /* defined _DOS */
  return FALSE;
}

/*--------------------------------------------------------------------*/
/* misc */
/*--------------------------------------------------------------------*/

void fprintFileId (FILE * dev, FileId * file)
{
  char * repr;
  
  id_to_string (file->basename, &repr);
  fprintf(dev, "%s%s", file->path, repr); 
}

/*--------------------------------------------------------------------*/

void PrintFileId(FileId * file)
{
  fprintFileId (stdout, file);
}

/*--------------------------------------------------------------------*/

void PrintDeps (void)
{
  FileId * i;
  
  fprintf (stdout, ": ");
  fprintFileId (stdout, sourceFileIdEntry);
  i = sourceFileIdEntry-> next;
  while (i != 0) {
    fprintf (stdout, " \\\n\t");
    fprintFileId (stdout, i);
    i = i->next;
  }
  fprintf (stdout, "\n");
  exit (0);
}

/*--------------------------------------------------------------------*/

/* recursively remove the pattern "dir/../" from a path */
/* BEWARE: this function overwrites the input string with the result */
void Compact_path(char str[])
{
  char buff1[PATH_MAX + 1];  /* we copy from buff1 to buff2 */
  char buff2[PATH_MAX + 1];  /* but skipping the pattern */
  int i1 = 0;        /* position in buff1 */
  int i2 = 0;        /* position in buff2 */
  int compacted = 0; /* did we compact? */
  char ch;
  
  strcpy(buff1, str);
  buff2[0] = '\0';
  for (;;) {
    char * slash = strchr(buff1+i1, '/');
    if (slash == 0) { /* no slash found; copy the remainder */
      	strcpy(buff2 + i2, buff1 + i1);
	if (compacted == 0) { /* nothing achieved on last pass - finished */
	  strcpy(str, buff2);
	  return;
	  }
	else { /* copy back to buff1 and start again */
	  strcpy(buff1, buff2);
	  i1 = 0;
	  i2 = 0;
	  compacted = 0;
	}
      }
    else {
      int len = slash - (buff1 + i1);
      ch = *(buff1 + i1);
      if ((strncmp(buff1 + i1 + len, "/../", 4) == 0) && isalnum(ch)) {
	/* we found the pattern - just skip over it */
	i1 += len + 4;
	compacted = 1;
      }
      else {
	/* copy the next directory plus slash to buff2 */
	strncpy(buff2 + i2, buff1 + i1, len + 1);
	i1 += len + 1;
	i2 += len + 1;
      }
    }
  }
}

/*------------------------------------------------------------------------*/
/* Change DOS \ to Unix / in a path */

void Dos_to_Unix(char *str, char** s_out)
{
  int i;
  int len;
  char ch;
  char *res;

  len = strlen(str)+1;
  res = (char *) malloc(strlen(str)+1);
  for (i=0; i < len; i++){
    ch = str[i];
    if (ch=='\\') ch='/';
    res[i] = ch;
  }
  *s_out=res;
}


/*------------------------------------------------------------------------*/
/* add comments */
/*------------------------------------------------------------------------*/

/* the next two functions plus the variable preget allow two ungetc's
   with only one actually being done to yyin */

char mygetc(){
  char ch;

  if (preget){
    ch = preget;
    preget = '\0';
    return ch;
  }
  else return fgetc(yyin);
}

void myungetc(char ch){
  if (preget) ungetc(preget, yyin);
  preget = ch;
}
    
    

void Find_comm(int *tp)
{
  int ch;
  for(;;) {
    while ((ch = mygetc()) == ' '||ch == '\t');
    switch (ch) {
    case EOF : 
      *tp = 0;
      return;
    case '\n' :
      nline = 1;
      break;
    case '/' :
      if ((ch = mygetc()) == EOF) {
        *tp = 0;
	myungetc('/');
        return; }
      if (ch == '*') 
        *tp = 1;
      else 
        *tp = 0;
      myungetc (ch);
      myungetc ('/');
      return; 
    case '-' :
      if ((ch = mygetc()) == EOF) {
        *tp = 0;
	myungetc('-');
        return; }
      if (ch == '-') 
        *tp = 2;
      else 
        *tp = 0;
      myungetc (ch);
      myungetc ('-');
      return; 
    default :
      myungetc(ch);
      *tp = 0;
      return; }
  }
}

void Skip_string(char *s,int * tp)
{
  int len;
  int i;
  char ch;

  len = strlen(s);
  for (i = 0; i < len; i++) ch = mygetc();
  Find_comm(tp);
  if (!*tp) nline = 0;
}

void Move_spaces(char *s,char **t)
{
  int ch;
  int len;
  char *cs;

  len = strlen(s);
  *t = (char *)malloc(len+1);
  if (*t == NULL) exit(1);
  cs = *t;
  while (ch = *s++)
    if (ch != ' ') *cs++ = ch;
  *cs = '\0';
}
  
void Change_sp(char *s,char **t)
{
  int ch;
  int len;
  char *cs;

  if(s[0] != ' ') *t = s;
  else {
    len = strlen(s);
    *t = (char *)malloc(len);
    if (*t == NULL) exit(1);
    cs = *t;
    s++;
    while (ch = *s++) *cs++ = ch;
    *cs = '\0'; }
}

void Block_to_str(char **s,int *f,int *b,int *tp)
{
  int ch;
  int rest = 15; /* space to try to terminate a long comment line cleanly */
  int n = plength - rest;
  char *cs;

  *f = nline;
  nline = 0;
  *s = (char *)malloc(plength);
  if (*s == NULL) exit(1);
  cs = *s;
  while ((ch = mygetc()) == ' '||ch == '\t'||ch == '\n');
  myungetc(ch);
  while (--n > 0) {
    ch = mygetc();
    *cs++ = ch;
    switch (ch) {
    case '*' : /* possible end comment */
      /* look ahead for end of comment */
      ch = mygetc();
      if (ch == '/') {
        *cs++ = ch;
	nest--;
	if (nest == 0) { /* reached end of last comment */
	  *cs = '\0';
	  Find_comm(tp);
	  *b = nline;
	  if (!*tp) nline = 0;
	  return;
	}
      }
      else { /* put look ahead back */
	myungetc(ch);
      }
      break;
    case '\n' :
      nline = 1;
      *--cs = '\0';
      *b = nline;
      *tp = 1;
      return;
    case '/' : /* possible nested comment */
      ch = mygetc();
      *cs++ = ch;
      if (ch == '*') {
	nest++;
      }
      break;
    default :
      ;
    }
  }

  while(--rest > 0) {
    ch = mygetc();
    switch (ch) {
    case ' ' :
    case '\t' :
    case '\n' :  
      *cs = '\0';
      nline = 1;
      *b = nline;
      *tp = 1;
      return;
    case '_' :
    case '(':
    case ')':
      *cs++ = ch;
      *cs = '\0';
      nline = 1;
      *b = nline;
      *tp = 1;
      return;
    case '*' :
      ch = mygetc();
      if (ch == '/') {
	*cs = '\0';
	nline = 1;
	*b = nline;
	*tp = 1;
	myungetc('/');
	myungetc('*');
	return; }
      else {
	*cs++ = '*';
	myungetc(ch);
	break; }
    case '/' :
      ch = mygetc();
      if (ch == '*') {
	*cs = '\0';
	nline = 1;
	*b = nline;
	*tp = 1;
	myungetc('*');
	myungetc('/');
	return; }
      else {
	*cs++ = '/';
	myungetc(ch);
	break; }
    default : *cs++ = ch;
    }
  }
  /* failed to find a good point to break.  Terminate anyway */
  *cs = '\0';
  nline = 1;
  *b = nline;
  *tp = 1;
}

void Line_to_str(char **s,int *f,int *tp)
{
  int ch;
  int rest = 15; /* space to try to terminate a long comment line cleanly */
  int n = plength - rest;
  char *cs;

  *f = nline;
  nline = 0;
  *s = (char *)malloc(plength);
  if (*s == NULL) exit(1);
  cs = *s;
  while (--n > 0)
    if ((*cs++ = mygetc()) == '\n') {
      nline = 1;
      *--cs = '\0';
      Find_comm(tp);
      if (!*tp) nline = 0;
      return; }
  while(--rest >= 0) {
    ch = mygetc();
    switch(ch) {
    case ' ' :
    case '\t' :
      *cs = '\0';
      nline = 1;
      *tp = 3;
      return;
    case '\n' :
      nline = 1;
      *cs = '\0';
      Find_comm(tp);
      if (!*tp) nline = 0;
      return; 
    default : *cs++ = ch;
    }
  }
  /* failed to find a good point to break.  Terminate anyway */
  *cs = '\0';
  nline = 1;
  /* check if next character is end of line (max length comment) */
  ch = mygetc();
  if (ch == '\n') *tp = 2; /* no more to come */
  else *tp = 3;            /* more to come */
  myungetc(ch);
}

void Setplength(int pl) {
  plength = pl; }

void PpLength (int *len) {
  *len = plength;
}

/* ---------------------------------------------------------------- */

time_t start_time;

void SetTime ()
{
  start_time = time (NULL);
}

/* ---------------------------------------------------------------- */

typedef char FILESPEC[PATH_MAX + 1];

static FILE *s_outputfile;

char* IdToString(IDENT Id)
{
  char* str;
  id_to_string(Id, &str);
  return str;
}

static int s_isnewline = 1;

void OpenOutputFile(IDENT Id, char *fileext, char *filetype, char **file)
{
  static FILESPEC filespec;

  sprintf(filespec, "%s%s%s", sourceFileIdEntry->path, IdToString(Id), fileext);
  if ( file != NULL )
    *file = filespec;
  s_outputfile = fopen (filespec, "w");
  if (s_outputfile == NULL) {
    sprintf(errMsg, "cannot rewrite %s file: '%s'", filetype, filespec);
    ErrorUsage (errMsg);
  }
  s_isnewline = 1;
}

static int s_indspc = 4;
static int s_curind = 0;
static int s_curpos = 0;
static int s_indentstacksize = 0;
static int s_indentstackp = 0;
static int* s_indentstack = NULL;

static
void WriteFileIndent()
{
    int i;
    if ( s_isnewline ) {
        for ( i = 0; i < s_curind; i++ )
            fputc(' ', s_outputfile);
        s_curpos = s_curind;
        s_isnewline = 0;
    }
}

void WriteIndntFile(int n)
{
  int i;
  for ( i = 0; i < n; i++ ) {
    fputc(' ', s_outputfile);
    s_curpos = s_curpos + n;
  }
}

void PushIndent()
{
    if ( s_indentstackp == s_indentstacksize ) {
        s_indentstacksize += 1024;
        s_indentstack = realloc(s_indentstack, s_indentstacksize*sizeof(int));
    }

    s_indentstack[s_indentstackp++] = s_curind;
}

void PopIndent()
{
    s_curind = s_indentstack[--s_indentstackp];
}

void SetIndentHere(int n)
{
    WriteFileIndent();
    s_curind = s_curpos+n;
}

void PushSetIndentHere(int n)
{
    PushIndent();
    SetIndentHere(n);
}

void GetFString(char *fmt, char* s, char** s_out)
{
  int n;
  n = strlen(fmt);
  n += strlen(s)-strlen("%s");
  *s_out = (char *) malloc(n+1);
  sprintf(*s_out, fmt, s);
}

void GetF2String(char *fmt, char* s1, char* s2, char** s_out)
{
  int n;
  n = strlen(fmt);
  n += strlen(s1)-strlen("%s");
  n += strlen(s2)-strlen("%s");
  *s_out = (char *) malloc(n+1);
  sprintf(*s_out, fmt, s1, s2);
}

void WriteFile(char *str)
{
    WriteFileIndent();
    fputs(str, s_outputfile);
    s_curpos += strlen(str);
}

void WriteFFile(char *fmt, char *str)
{
    WriteFileIndent();
    fprintf(s_outputfile, fmt, str);
    s_curpos += strlen(fmt);
    s_curpos += strlen(str)-strlen("%s");
}  

void WriteF2File(char *fmt, char *str1, char *str2)
{
    WriteFileIndent();
    fprintf(s_outputfile, fmt, str1, str2);
    s_curpos += strlen(fmt);
    s_curpos += strlen(str1)-strlen("%s");
    s_curpos += strlen(str2)-strlen("%s");
}  

void WriteF3File(char *fmt, char *str1, char *str2, char *str3)
{
    WriteFileIndent();
    fprintf(s_outputfile, fmt, str1, str2, str3);
    s_curpos += strlen(fmt);
    s_curpos += strlen(str1)-strlen("%s");
    s_curpos += strlen(str2)-strlen("%s");
    s_curpos += strlen(str3)-strlen("%s");
}  

void WriteF4File(char *fmt, char *str1, char *str2, char *str3, char *str4)
{
    WriteFileIndent();
    fprintf(s_outputfile, fmt, str1, str2, str3, str4);
    s_curpos += strlen(fmt);
    s_curpos += strlen(str1)-strlen("%s");
    s_curpos += strlen(str2)-strlen("%s");
    s_curpos += strlen(str3)-strlen("%s");
    s_curpos += strlen(str4)-strlen("%s");
}  

void WriteF5File(char *fmt, char *str1, char *str2, char *str3, char *str4, char *str5)
{
    WriteFileIndent();
    fprintf(s_outputfile, fmt, str1, str2, str3, str4, str5);
    s_curpos += strlen(fmt);
    s_curpos += strlen(str1)-strlen("%s");
    s_curpos += strlen(str2)-strlen("%s");
    s_curpos += strlen(str3)-strlen("%s");
    s_curpos += strlen(str4)-strlen("%s");
    s_curpos += strlen(str5)-strlen("%s");
}  

void WritelnFile(int n)
{
  int i;
  for ( i = 0; i < n; i++ ) {
    WriteFileIndent();
    fputc('\n', s_outputfile);
    s_isnewline = 1;
  }
}

void WriteFFileInt(char *fmt, int n)
{
  WriteFileIndent();
  fprintf(s_outputfile, fmt, n);
}

void CloseOutputFile()
{
  fclose(s_outputfile);
}

void SetFileIndentSpace(int n)
{
  s_indspc = n;
}

void IndentFile()
{
  s_curind += s_indspc;
}

void UnindentFile()
{
  s_curind -= s_indspc;
}

void NewSeqNum(int *num)
{
  static int s_num = 0;
  *num = ++s_num;
}

void Char_to_int(char ch, int *n)
{
    *n = (ch & 0xFF);
}

static
int is_displayable(char c)
{
    unsigned int n = (unsigned int)c;
    return 32 <= n && n < 128;
}


void String_to_SML_string(char* s, char** s_out)
{
    int n = 0;
    char *p = s;
    char *q;

    for ( ; *p ; p++ )
        n += is_displayable(*p)? 1 : 4;

    *(*s_out = (char *) malloc(n+1)) = 0;

    q = *s_out;
    p = s;
    while ( *p ) {
        if ( is_displayable(*p) ) {
            sprintf(q, "%c", *p);
            q++;
        } else {
            sprintf(q, "\\%03d", (unsigned)(*p));
            q += 4;
        }
        p++;
    }
}

void Char_to_SML_char(char c, char** s_out)
{   
    *(*s_out = (char *) malloc(5)) = 0;
    if ( is_displayable(c) )
        sprintf(*s_out, "%c", c);
    else
        sprintf(*s_out, "\\%03d", (unsigned)c);
}


void String_to_PVS_string(char* s, char** s_out)
{

}


void Char_to_PVS_char(char c, char** s_out)
{ 
  
}
void String_to_FDR_string(char* s, char** s_out)
{

}


void Char_to_FDR_char(char c, char** s_out)
{ 
  
}
void Pos_to_string(long pos, char** s_out)
{
  *s_out = (char *) malloc(13); 
  sprintf(*s_out, "%lX", pos); /* writes 13 bytes in Solaris */
}

void Get_env_string(char* var, char* def, char** s_out)
{
    char* val = getenv(var);
    if ( val == NULL )
        val = def;
    strcpy((*s_out = (char *) malloc(strlen(val)+1)), val);
}

void OpenSMLFile(IDENT Id, char **file) {OpenOutputFile(Id, SML_SUFFIX, "SML", file);}

void OpenPVSFile(IDENT Id, char **file) {OpenOutputFile(Id, PVS_SUFFIX, "PVS", file);}

void OpenSALFile(IDENT Id, char **file) {OpenOutputFile(Id, SAL_SUFFIX, "SAL", file);}

void OpenM4File(IDENT Id, char **file) {OpenOutputFile(Id, M4_SUFFIX, "m4", file);}

void OpenFDRFile(IDENT Id, char **file) {OpenOutputFile(Id, FDR_SUFFIX, "FDR", file);}

void OpenLTLFile(IDENT Id, char **file) {OpenOutputFile(Id, LTL_SUFFIX, "LTL", file);}
/* ---------------------------------------------------------------- */

void OpenGraphFile(IDENT Id, char **file) {OpenOutputFile(Id, VCG_SUFFIX, "graph", file);}

void WriteGraphString(char *str) {WriteFile(str);}

void WriteGraphId(IDENT Id) {WriteFile(IdToString(Id));}

void CloseGraphFile() {CloseOutputFile();}

/* ---------------------------------------------------------------- */

char hFilename [PATH_MAX + 1];
FILE *hfile;

void OpenHFile (IDENT Id, char **file)
{
  char *filename;

  id_to_string(Id, &filename);
  sprintf(hFilename, "%s%s%s", sourceFileIdEntry->path, filename, H_SUFFIX);
  *file = hFilename;
  hfile = fopen (hFilename, "w");
  if (hfile == NULL) {
    sprintf(errMsg, "cannot open header file: '%s'", hFilename);
    ErrorUsage (errMsg);
  }
  else fprintf(hfile, "// Translation produced by rsltc %s\n", ctime(&start_time));
}

void WriteHString (char *str)
{
  fputs(str, hfile);
}

void WriteHId (IDENT Id)
{
  char *str;

  id_to_string(Id, &str);
  fputs(str, hfile);
}

void WriteHText (char *str)
{
  fprintf(hfile, "\"%s\"", str);
}

void WriteHChar (char ch)
{
  fprintf(hfile, "\"%c\"", ch); /* Convert to octal with \\%o? */
}

void CloseHFile ()
{
  fclose(hfile);
}

/* ---------------------------------------------------------------- */

char* GetCcSuffix() {
  if (VisualCPP()) return CPP_SUFFIX;
  else return CC_SUFFIX;
}

char ccFilename [PATH_MAX + 1];
FILE *ccfile;

void OpenCcFile (IDENT Id, char **file)
{
  char *filename;

  id_to_string(Id, &filename);
  sprintf(ccFilename, "%s%s%s", sourceFileIdEntry->path, filename, GetCcSuffix());
  *file = ccFilename;
  ccfile = fopen (ccFilename, "w");
  if (ccfile == NULL) {
    sprintf(errMsg, "cannot open cc file: '%s'", ccFilename);
    ErrorUsage (errMsg);
  }
  else fprintf(ccfile, "// Translation produced by rsltc %s\n", ctime(&start_time));
}

void WriteCcString (char *str)
{
  fputs(str, ccfile);
}

void WriteCcId (IDENT Id)
{
  char *str;

  id_to_string(Id, &str);
  fputs(str, ccfile);
}

void WriteCcText (char *str)
{
  fprintf(ccfile, "\"%s\"", str);
}

void WriteCcChar (char ch)
{
  fprintf(ccfile, "\"%c\"", ch); /* Convert to octal with \\%o? */
}

void CloseCcFile ()
{
  fclose(ccfile);
}

/* ---------------------------------------------------------------- */

void WriteHCcString (char *str)
{
  WriteHString(str);
  WriteCcString(str);
}

/* ---------------------------------------------------------------- */

char javaFilename [PATH_MAX + 1];
FILE *javafile;

void OpenJavaFile (IDENT Id, char **file)
{
  char *filename;

  id_to_string(Id, &filename);
  sprintf(javaFilename, "%s%s%s", sourceFileIdEntry->path, filename, JAVA_SUFFIX);
  *file = javaFilename;
  javafile = fopen (javaFilename, "w");
  if (javafile == NULL) {
    sprintf(errMsg, "cannot open java file: '%s'", javaFilename);
    ErrorUsage (errMsg);
  }
  else fprintf(javafile, "// Translation produced by rsltc %s\n", ctime(&start_time));
}

void WriteJavaString (char *str)
{
  fputs(str, javafile);
}

void WriteJavaId (IDENT Id)
{
  char *str;

  id_to_string(Id, &str);
  fputs(str, javafile);
}

void WriteJavaText (char *str)
{
  fprintf(javafile, "\"%s\"", str);
}

void WriteJavaChar (char ch)
{
  fprintf(javafile, "\"%c\"", ch); /* Convert to octal with \\%o? */
}

void WriteJavaInt (int i)
{
  fprintf(javafile, "%d", i);
}

void CloseJavaFile ()
{
  fclose(javafile);
}
