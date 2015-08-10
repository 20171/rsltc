/* 
RSL Type Checker
Copyright (C) 1998 UNU/IIST

raise@iist.unu.edu
*/

#include "idents.h"
#include <string.h>

#define PRIVATE static
#define PUBLIC

/*--------------------------------------------------------------------*/

#define HashTabSize       2048
#define STRINGTAB_PIECE  10000
#define STRINGTAB_EXTRA    500

struct IDENTSTRUCT
{
   char  *firstposptr;
   long  length;
   IDENT next;
   long  meaning;
};
void Make_mk_name(char *, char **);
void Make_from_name(char *, char *, char **);
void Make_to_name(char *, char *, char **);
void Make_difference_name(char *, char **);
void Make_induction_name(char *, char **);
void Char_to_string(char, char **);
void Text_to_string(char *, char **);
void Len(char *, int *);
void Int_to_string(int, char **);


PRIVATE char *idstringtab_ptr;
PRIVATE char *idstringtab_endptr;

struct IDENTSTRUCT *idtab_ptr;
struct IDENTSTRUCT *idtab_endptr;

PRIVATE IDENT HashTab [HashTabSize];

PRIVATE int initialized = 0;

/*--------------------------------------------------------------------*/

PRIVATE void allocate_idstringtab ()
{
   idstringtab_ptr =
      (char *) malloc (STRINGTAB_PIECE + STRINGTAB_EXTRA);
   if (idstringtab_ptr == 0) {
      printf("memory allocation failed\n");
      exit(1);
   }
   idstringtab_endptr = idstringtab_ptr + STRINGTAB_PIECE - 1;
}

/*--------------------------------------------------------------------*/

#define IDTABPIECESIZE 500
typedef struct IDENTSTRUCT IDTAB [IDTABPIECESIZE];

PRIVATE void allocate_idtab ()
{
   idtab_ptr =
      (struct IDENTSTRUCT *)
      malloc (sizeof (IDTAB /*struct IDENTSTRUCT [IDTABPIECESIZE]*/ ) );
   if (idtab_ptr == 0) {
      printf("memory allocation failed\n");
      exit(1);
   }
   idtab_endptr = & idtab_ptr[IDTABPIECESIZE - 1];
}

/*--------------------------------------------------------------------*/

PRIVATE void InitIdents ()
{
   long i;

   for (i = 0; i<=HashTabSize-1; i++) HashTab[i] = 0;

   allocate_idtab ();
   allocate_idstringtab ();

   initialized = 1;
}

/*--------------------------------------------------------------------*/

void slice_to_id (idstart, idstop, ref_id)
   char *idstart; /* position of first character */
   char *idstop;  /* position  a f t e r  last character */
   IDENT *ref_id;

{
   long  hash, length;
   IDENT chain;
   IDENT  NewId;

   if (! initialized) InitIdents();

   length = idstop-idstart;
   hash = ( length*256 + ((*idstart)&0xf)*16 + (*(idstop-1)&0xf) ) 
   & (HashTabSize-1);
   chain = HashTab[hash];

   for(;;) {
      if (chain == 0) {
      
	 /* not in table */
	 
	 register char *i, *freeptr, *stop;

	 NewId = idtab_ptr;
	    
	 if (idtab_ptr == idtab_endptr)
	    allocate_idtab();
         else
	    idtab_ptr++;

	 /* copy id into string table */
	 i = idstart;
	 if (idstringtab_ptr > idstringtab_endptr)
	    allocate_idstringtab();
	 freeptr = idstringtab_ptr;
	 stop = idstop;
	 while (i < stop) {
	    *freeptr++ = *i++;
	 }
	 *freeptr = '\0';
	 freeptr++;
	    
	 NewId->firstposptr = idstringtab_ptr;
	 NewId->length = length;
	 NewId->next = HashTab[hash];
         NewId->meaning = 0;
	    
	 HashTab[hash] = NewId;

	 idstringtab_ptr= freeptr;
	 

	 break;
      }

      /* current token == ident at chain ? */
      
      if (chain->length == length) {
         register char *i, *j;
	 i = idstart; j = chain->firstposptr;
	 while (i != idstop && *i == *j) {
	    i++; j++;
         }

	 if (i == idstop && *j == '\0') {
	    
	    /* found */
	    
	    NewId = chain;
	    break;
	 }
      }

      chain = chain->next;
   }

   *ref_id = NewId;
}

/*--------------------------------------------------------------------*/
void string_to_id (string, ref_id)
   char *string;
   IDENT *ref_id;
{
   char *idstop;

   idstop = string;
   while (*idstop != '\0') idstop++;
   slice_to_id (string, idstop, ref_id);
}

/*--------------------------------------------------------------------*/
void id_to_string (id, ref_string)
   IDENT id;
   char **ref_string;
{
   *ref_string = id->firstposptr;
}
/*--------------------------------------------------------------------*/
/* Converts ' and ` in identifiers to rsL and Rsl for translation to C */
void C_id_to_string(id, ref_string)
     IDENT id;
     char **ref_string;
{
     *ref_string = id->firstposptr;
     if (strchr(id->firstposptr, '\'') == NULL &&
	 strchr(id->firstposptr, '`') == NULL) {
       return;
     } else {
       char *ptr1 = *ref_string;
       int len = 1; /* for terminator */
       while (*ptr1 != '\0') {
	 if ((*ptr1 == '\'') || (*ptr1 == '`')) len = len + 3;
	 else len++;
	 *ptr1++;
       }
       {
	 char *newstr = (char *) malloc(len);
	 char *ptr2 = newstr;
	 ptr1 = *ref_string;
	 while (*ptr1 != '\0') {
	   if (*ptr1 == '\'') {
	     *ptr2++ = 'r';
	     *ptr2++ = 's';
	     *ptr2++ = 'L';
	     *ptr1++;
	   } else if (*ptr1 == '`') {
	     *ptr2++ = 'R';
	     *ptr2++ = 's';
	     *ptr2++ = 'l';
	     *ptr1++;	   
	   } else {
	     *ptr2++ = *ptr1++;
	   }
	 }
	 *ptr2++ = '\0';
	 *ref_string = newstr;
       }
     }
}
     

/*--------------------------------------------------------------------*/
/* Converts ` in identifiers to Rsl for translation to PVS */
void PVS_id_to_string(id, ref_string)
     IDENT id;
     char **ref_string;
{
     *ref_string = id->firstposptr;
     if (strchr(id->firstposptr, '`') == NULL) {
       return;
     } else {
       char *ptr1 = *ref_string;
       int len = 1; /* for terminator */
       while (*ptr1 != '\0') {
	 if (*ptr1 == '`') len = len + 3;
	 else len++;
	 *ptr1++;
       }
       {
	 char *newstr = (char *) malloc(len);
	 char *ptr2 = newstr;
	 ptr1 = *ref_string;
	 while (*ptr1 != '\0') {
	   if (*ptr1 == '`') {
	     *ptr2++ = 'R';
	     *ptr2++ = 's';
	     *ptr2++ = 'l';
	     *ptr1++;	   
	   } else {
	     *ptr2++ = *ptr1++;
	   }
	 }
	 *ptr2++ = '\0';
	 *ref_string = newstr;
       }
     }
}     

/*--------------------------------------------------------------------*/
/* Converts ` in identifiers to Rsl for translation to SML */
void SML_id_to_string(id, ref_string)
     IDENT id;
     char **ref_string;
{
     *ref_string = id->firstposptr;
     if (strchr(id->firstposptr, '`') == NULL) {
       return;
     } else {
       char *ptr1 = *ref_string;
       int len = 1; /* for terminator */
       while (*ptr1 != '\0') {
	 if (*ptr1 == '`') len = len + 3;
	 else len++;
	 *ptr1++;
       }
       {
	 char *newstr = (char *) malloc(len);
	 char *ptr2 = newstr;
	 ptr1 = *ref_string;
	 while (*ptr1 != '\0') {
	   if (*ptr1 == '`') {
	     *ptr2++ = 'R';
	     *ptr2++ = 's';
	     *ptr2++ = 'l';
	     *ptr1++;	   
	   } else {
	     *ptr2++ = *ptr1++;
	   }
	 }
	 *ptr2++ = '\0';
	 *ref_string = newstr;
       }
     }
}
     

/*--------------------------------------------------------------------*/
void Axiom_name_to_string (id, ref_string)
   IDENT id;
   char **ref_string;
{
   char * temp;

   temp = id->firstposptr;
   *ref_string = (char *) malloc (strlen(temp) + 3);
   sprintf(*ref_string, "[%s]", temp);
}

/*--------------------------------------------------------------------*/
void DefMeaning (id, m)
   IDENT id;
   long m;
{
   id->meaning = m;
}

/*--------------------------------------------------------------------*/
void UndefMeaning (id)
   IDENT id;
{
   id->meaning = 0;
}

/*--------------------------------------------------------------------*/
int HasMeaning (id, ref_meaning)
   IDENT id;
   long *ref_meaning;
{
   if (id->meaning == 0)
      return 0;
   *ref_meaning = id->meaning;
   return 1;
}

/*--------------------------------------------------------------------*/
void ErrorI (str1, id, str2, pos)
   char *str1;
   IDENT id;
   char *str2;
   long pos;
{
   char *idrepr;
   char buf[300];

   id_to_string (id, &idrepr);
   sprintf(buf, "%s%s%s", str1, idrepr, str2);
   Error(buf, pos);
}

/*--------------------------------------------------------------------*/
void Make_mk_name(char *string, char **ref_string)
{
  *ref_string = (char *) malloc (strlen(string) + 4);
  sprintf(*ref_string, "mk_%s", string);
}

/*--------------------------------------------------------------------*/
void Make_from_name(char *string1, char *string2, char **ref_string)
{
  *ref_string = (char *) malloc (strlen(string1) + strlen(string2) + 7);
  sprintf(*ref_string, "%s_from_%s", string1, string2);
}

/*--------------------------------------------------------------------*/
void Make_to_name(char *string1, char *string2, char **ref_string)
{
  *ref_string = (char *) malloc (strlen(string1) + strlen(string2) + 5);
  sprintf(*ref_string, "%s_to_%s", string1, string2);
}

/*--------------------------------------------------------------------*/

void Make_disjointness_name(char *string, char **ref_string)
{
  *ref_string = (char *) malloc (strlen(string) + 20);
  sprintf(*ref_string, "%s_disjointness_axiom", string);
}

/*--------------------------------------------------------------------*/

void Make_induction_name(char *string, char **ref_string)
{
  *ref_string = (char *) malloc (strlen(string) + 17);
  sprintf(*ref_string, "%s_induction_axiom", string);
}

/*--------------------------------------------------------------------*/
void Char_to_string(char ch, char **ref_string)
{
  char *ch_string;

  ch_string = (char *) malloc (3);
  switch (ch) {
  case '\a' : strcpy(ch_string, "\\a"); break;
  case '\b' : strcpy(ch_string, "\\b"); break;
  case '\f' : strcpy(ch_string, "\\f"); break;
  case '\n' : strcpy(ch_string, "\\n"); break;
  case '\r' : strcpy(ch_string, "\\r"); break;
  case '\t' : strcpy(ch_string, "\\t"); break;
  case '\v' : strcpy(ch_string, "\\v"); break;
  case '\0' : strcpy(ch_string, "\\0"); break;
  default : ch_string[0] = ch; ch_string[1] = '\0'; break;
  }
  *ref_string = (char *) malloc (strlen(ch_string) + 2);
  sprintf(*ref_string, "'%s'", ch_string);
  free(ch_string);
}

/*--------------------------------------------------------------------*/
void Text_to_string(char *text, char **ref_string)
{
  int len = strlen(text);
  *ref_string = (char *) malloc (len + 3);
  sprintf(*ref_string, "\"%s\"", text);
}

/*--------------------------------------------------------------------*/
void Text_to_c_string(char *text, char **ref_string)
{
  int len = strlen(text);
  if (len == 1) {
    /* compiler seems confused about strings like "(" */
    *ref_string = (char *) malloc (len + 11);
    sprintf(*ref_string, "(string)\"%s\"", text);
  }
  else {
    *ref_string = (char *) malloc (len + 3);
    sprintf(*ref_string, "\"%s\"", text);
  }

}

/*-------------------------------------------------------------------*/
void Len(char *string, int *length)
{ 
  *length = strlen(string);
}

/*---------------------------------------------------------------------*/
void Int_to_string(int i, char **s)
{
  *s = (char *) malloc (7);
  sprintf(*s, "%hd", i); /*  writes 7 bytes in Solaris */
}
/*---------------------------------------------------------------------*/
int Contains_E(char *s)
{
  return (strchr(s, 'E') != NULL);
}

/*---------------------------------------------------------------------*/
int Is_primed(char *s) {
  return (strchr(s, '\'') != NULL);
}

void Remove_Prime(char *string, char **ref_string) {
  /*int len = strlen(string);
  char temp[len];
  memcpy(temp, &string[0], len-1);
  temp[len-1] = '\0';
  *ref_string = temp;*/
  
  int len = strlen(string);
  char temp[len];
  memcpy(temp, &string[0], len-1);
  temp[len-1] = '\0';
  *ref_string = (char *) malloc (len);
  sprintf(*ref_string, temp);
}


/*---------------------------------------------------------------------*/
/* raise x to the power y, y >= 0                                      */
/* necessary since we can't see pow in math.h or tgmath.h                */
long int power(long int x, long int y)
{
  long int p;
  int i;
  p = 1;
  i = 1;
  while (i <= y)
    {p = p * x;
     i = i + 1;
    }
  return p;
}

/*---------------------------------------------------------------------*/
/* convert a RSL real into a PVS number and a Divisor                  */
/* ex. 3.14159 is: base= 314159 and divisor= 100000                    */
void Convert_Real(IDENT id, long int *base , long int *divisor)
{
  char * rsl_real; // string for input real
  int total_Ln; // rsl real number total length
  int int_Ln;  // real number integer part length 
  int dec_Ln;  // real number decimal part length 
  char *dec_point;  // real number decimal point pointer
  char *dec_part;  // real number decimal part string pointer
  char *int_part2;  // real number integer part (copy) string pointer
  char *dec_part2;  // real number decimal part (copy) string pointer

  rsl_real = id->firstposptr;
  total_Ln = strlen(rsl_real);
  dec_point = strchr(rsl_real, (int)'.');
  dec_part = dec_point + 1;
  dec_Ln = strlen(dec_part);
  int_Ln = total_Ln - dec_Ln - 1;
  // integer part copy
  int_part2 = malloc(int_Ln + 1);
  strncpy(int_part2, rsl_real, int_Ln);
  int_part2[int_Ln] = '\0';
  // decimal part copy
  dec_part2 = malloc(dec_Ln + 1);
  strncpy(dec_part2, dec_part, dec_Ln + 1);
  if (atoi(dec_part2) == 0)
    {*divisor = 1;
     *base = atoi(int_part2);
    }
    else
      {*divisor = power(10, dec_Ln);
       *base = atoi(int_part2) * *divisor + atoi(dec_part2);
    }
  free(int_part2);
  free(dec_part2);
}

int Compare_substring(char *s1,char *s2,int num)
{
  int i = strncmp(s1,s2,num) ;
  return (i == 0);
}

int Compare_string(char *s1,char *s2,int num)
{
  int i = strcmp(s1,s2) ;
  return (i == 0);
}
