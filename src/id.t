[a-zA-Z][a-zA-Z0-9_\']* {
   long rslid;
   string_to_id (yytext, &rslid);
   yylval.attr[1] = rslid;
   yysetpos();
   return id;
}

([a-zA-Z]|`(alpha|beta|[gG]amma|[dD]elta|epsilon|zeta|eta|[tT]heta|iota|kappa|Lambda|mu|nu|[xX]i|[pP]i|rho|[sS]igma|tau|[uU]psilon|[pP]hi|chi|[pP]si|[oO]mega))([a-zA-Z0-9_\']|`(alpha|beta|[gG]amma|[dD]elta|epsilon|zeta|eta|[tT]heta|iota|kappa|Lambda|mu|nu|[xX]i|[pP]i|rho|[sS]igma|tau|[uU]psilon|[pP]hi|chi|[pP]si|[oO]mega))* {
   long rslid;
   string_to_id (yytext, &rslid);
   yylval.attr[1] = rslid;
   yysetpos();
   return id;
}

([a-zA-Z]|\016[DFGLOPQSUXYabcdefghikmnopqrstuxyz]|`(alpha|beta|[gG]amma|[dD]elta|epsilon|zeta|eta|[tT]heta|iota|kappa|Lambda|mu|nu|[xX]i|[pP]i|rho|[sS]igma|tau|[uU]psilon|[pP]hi|chi|[pP]si|[oO]mega))([a-zA-Z0-9_\']|\016[DFGLOPQSUXYabcdefghikmnopqrstuxyz]|`(alpha|beta|[gG]amma|[dD]elta|epsilon|zeta|eta|[tT]heta|iota|kappa|Lambda|mu|nu|[xX]i|[pP]i|rho|[sS]igma|tau|[uU]psilon|[pP]hi|chi|[pP]si|[oO]mega))* {
   long rslid;
   string_to_id (yytext, &rslid);
   yylval.attr[1] = rslid;
   yysetpos();
   return id;
}

