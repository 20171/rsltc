/* 
RSL Type Checker
Copyright (C) 1998 UNU/IIST

raise@iist.unu.edu
*/

#ifndef _FILES_H /* if not defined then files.h has not yet been included */
#define _FILES_H
#include <stdio.h>
#include <time.h>
#include "idents.h"
#include "errmsg.h"

/*--------------------------------------------------------------------*/
/* EXPORTS */

#define bool int
#define FALSE 0
#define TRUE  1

/* suffix */
#define RSL_SUFFIX ".rsl"
#define VCG_SUFFIX ".vcg"
#define H_SUFFIX ".h"
#define CPP_SUFFIX ".cpp"
#define CC_SUFFIX ".cc"
#define JAVA_SUFFIX ".java"
#define SML_SUFFIX ".sml"
#define PVS_SUFFIX ".pvs"
#define SAL_SUFFIX ".sal"
#define M4_SUFFIX ".m4"
#define FDR_SUFFIX ".fdr2"
#define LTL_SUFFIX ".ltl"

#ifndef PATH_MAX
#define PATH_MAX _MAX_PATH
#endif /* not defined PATH_MAX */


typedef struct FileIdRec FileId;

typedef struct PathIdRec PathId;    

void OpenFile (char *);
void Reopen(void);
void Find_comm(int *);
void Skip_string(char *,int *);
void Move_spaces(char *,char **);
void Change_sp(char *,char **);
void Block_to_str(char **,int *,int *,int *);
void Line_to_str(char **,int *,int *);
void Setplength(int);
void PpLength (int *);
FILE * NextFile (void);
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

void Dos_to_Unix(char *, char**);

void SetTime (void);

void OpenGraphFile (IDENT, char **);
void WriteGraphString (char *);
void WriteGraphId (IDENT);
void CloseGraphFile ();

void OpenHFile (IDENT, char **);
void WriteHString (char *);
void WriteHId (IDENT);
void WriteHText (char *);
void WriteHChar (char);
void CloseHFile ();

void OpenCcFile (IDENT, char **);
void WriteCcString (char *);
void WriteCcId (IDENT);
void WriteCcText (char *);
void WriteCcChar (char);
void CloseCcFile ();

void WriteHCcString (char *);

void OpenJavaFile (IDENT, char **);
void WriteJavaString (char *);
void WriteJavaId (IDENT);
void WriteJavaText (char *);
void WriteJavaChar (char);
void WriteJavaInt (int);
void CloseJavaFile ();

void OpenSMLFile(IDENT, char **);

void OpenPVSFile(IDENT, char **);

void OpenFDRFile(IDENT, char **);

void OpenLTLFile(IDENT, char **);

void OpenOutputFile(IDENT, char *, char *, char **);
void WriteFile(char *str);
void WritelnFile(int n);
void WriteIndntFile(int n);
void WriteFFile(char *fmt, char *str);
void WriteF2File(char *fmt, char *str1, char *str2);
void WriteF3File(char *fmt, char *str1, char *str2, char *str3);
void WriteF4File(char *fmt, char *str1, char *str2, char *str3, char *str4);
void WriteFFileInt(char *fmt, int n);
void CloseOutputFile();
void SetFileIndentSpace(int);
void IndentFile();
void UnindentFile();
void SetIndentHere(int n);
void PushSetIndentHere(int n);
void PushIndent();
void PopIndent();
void NewSeqNum(int *num);
void Char_to_int(char ch, int *n);
void GetF2String(char *fmt, char* s1, char* s2, char** s_out);
void GetFString(char *fmt, char* s, char** s_out);
void Char_to_SML_char(char c, char** s_out);
void String_to_SML_string(char* s, char** s_out);
void Pos_to_string(long pos, char** s_out);
void Get_env_string(char* var, char* def, char** s_out);

void Char_to_PVS_char(char c, char** s_out);
void String_to_PVS_string(char* s, char** s_out);

	       

#endif  /* _FILES_H */
