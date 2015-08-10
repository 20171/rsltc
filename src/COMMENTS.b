"/*" {
   yypos++; yypos++; /* initial '/*' */
   SkipRestOfComment ();
}
"--" {
   yypos++; yypos++; /* initial '--' */
   SkipRestOfLineComment ();
}

