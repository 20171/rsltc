(~|\.\.?)\/[a-zA-Z0-9_/.]+ {
  long fileid;
  string_to_fileid (yytext, &fileid);
  yylval.attr[1] = fileid;
  yysetpos();
  return filename;
}


