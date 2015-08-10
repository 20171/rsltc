'[^']' {  /* normal character example : 'a' */
  yylval.attr[1] = (long) yytext [1];
  yysetpos();
  return char_lit;
}
'\\.' { /* escaped character */
  unsigned char c;
  
  switch (yytext [2]) {
  case 'a' : c = '\a'; break;
  case 'b' : c = '\b'; break;
  case 'f' : c = '\f'; break;
  case 'n' : c = '\n'; break;
  case 'r' : c = '\r'; break;
  case 't' : c = '\t'; break;
  case 'v' : c = '\v'; break;
  case '0' : c = '\0'; break;
  default :  c =  yytext [2]; break;
  }
  yylval.attr[1] = (long) c;
  yysetpos();
  return char_lit;
}
'\\([0-7]{1,3})' { /* character given as octal number */
  long l;
  int i;
  
  for (i = 2, l = 0; i <= (yyleng - 2); i++) {
    l = l * 8 + (yytext [i] - '0');
  }
  yylval.attr[1] = (long) l;
  yysetpos();
  return char_lit;
}
'\\x[0-9A-Fa-f]{1,2}' { /* character given as hexadecimal number */
  long l;
  int i;
  
  for (i = 3, l = 0; i <= (yyleng - 2); i++) {
    int m;
    switch (yytext[i]) {
    case 'A' : case 'a' : m = 10; break;
    case 'B' : case 'b' : m = 11; break;
    case 'C' : case 'c' : m = 12; break;
    case 'D' : case 'd' : m = 13; break;
    case 'E' : case 'e' : m = 14; break;
    case 'F' : case 'f' : m = 15; break;
    default : m = (yytext[i] - '0'); break;
    }
    l = l * 16 + m;
  }
  yylval.attr[1] = (long) l;
  yysetpos();
  return char_lit;
}