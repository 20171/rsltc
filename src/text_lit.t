\" {
  yypos++; /* initial '"' */
  
  ReadStringLiteral ();
  return text_lit;
}
