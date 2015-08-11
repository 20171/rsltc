
#define EOFCHAR EOF
#define NEXTCHAR (yypos++, input())

/* ---------------------------------------------- */

void SkipRestOfComment (void)
{
  int ch;
  int nest = 1;
  
  ch = NEXTCHAR;
  for (;;) {
    switch (ch) {
    case '\n' :
      yyPosToNextLine ();
      ch = NEXTCHAR;
      break;
    case EOFCHAR :
      yyerror ("unexpected eof in comment");
      exit (1);
      break;
    case '*' : /* possible end of comment */
      ch = NEXTCHAR;
      if (ch == '/') {
	nest--;
	if (nest == 0) { /* reached end of last comment */
	  return;
	}
	ch = NEXTCHAR;
      }
      break;
    case '/' :
      ch = NEXTCHAR;
      if (ch == '*') {
	nest++; 
	ch = NEXTCHAR;
      }
      break;
    default :
      ch = NEXTCHAR;
    }
  }
}

/* ---------------------------------------------- */

void SkipRestOfLineComment (void)
{
  int ch;
  
  do {
    ch = NEXTCHAR;
  } while ((ch != '\n') && (ch != EOFCHAR));
  yyPosToNextLine();
}

/* ---------------------------------------------- */

void ReadStringLiteral (void) 
{
  int ch;
  
  for(;;) {
    ch = NEXTCHAR;
    switch (ch) {
    case EOFCHAR :
      yylexerror("end of file inside string");
      break;
    case '\n' :
      yylexerror("end of line inside string");
      break;
    case '\\' : 
      AppendToString(ch);
      ch = NEXTCHAR;
      AppendToString (ch);
      break;
    case '"' : /* string read */
      yylval.attr [0] = yypos;
      GetStringRef(&yylval.attr[1]);
      return;
      break;
    default :
      AppendToString(ch);
    }
  }
}
