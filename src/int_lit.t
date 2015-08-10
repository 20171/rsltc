[0-9]+(E[0-9]+)? {
   long rslid;
   string_to_id (yytext, &rslid);
   yylval.attr[1] = rslid;
   yysetpos();
   return int_lit;
}
