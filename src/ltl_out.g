-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu


'module' ltl_out

'use' ast print ext env objects values types pp cc pvs_gen_code

      fdr_ast         
      fdr_gen_ast     

 
'export' LTL_out_expr


-----------------------------
'action' LTL_out_expr(VALUE_EXPR,DECLS,Value_id)


  'rule' LTL_out_expr(VE,Decls,Process_id)
         Process_id'Ident -> Id_or_op
         where(Id_or_op -> id_op(Id))

	     Get_alph(Decls,Id)

         Translate_Value_expr_To_Fdr_value_expr(VE->FDR_VE)   
         Translate_Decls_To_Fdr_scripts(Decls->Fdr_Decls)  

         GenCode_Ltl_value_expr(FDR_VE)

	     LTL_out_alphabet()
         PrintProcId(Id)
         WritelnFile(1)


---------------------------------
-----  Get Alphabet   ------------
----------------------------------

'action' Get_alph(DECLS,IDENT)

  'rule' Get_alph(Decls,Proc_id)
         Translate_Decls_To_Fdr_scripts(Decls->FDR_Decls)  
	     Proc_decls(FDR_Decls,FDR_Decls,Proc_id) 
 
---------------------------
'action' Proc_decls(FDR_SCRIPTS,FDR_SCRIPTS,IDENT)

  'rule' Proc_decls(list(Fdr_script, Fdr_scripts),FDR_Decls,Proc_id):                                                              
	     Proc_decl(Fdr_script,FDR_Decls,Proc_id)
         Proc_decls(Fdr_scripts,FDR_Decls,Proc_id)
 
  'rule' Proc_decls(nil,FDR_Decls,Proc_id)

--------------------------------------
'action' Proc_decl(FDR_SCRIPT,FDR_SCRIPTS,IDENT)

  'rule' Proc_decl(fdr_def(Fdr_def, Fdr_script),FDR_Decls,Proc_id):     
         Proc(Fdr_def,FDR_Decls,Proc_id)
         Proc_decl(Fdr_script,FDR_Decls,Proc_id)

  'rule' Proc_decl(Fdr_Decl,FDR_Decls,Proc_id)
 
-----------------------------

'var' Al_in : FDR_ALPHABET
'var' Al_out : FDR_ALPHABET


'action' Proc(FDR_DEF,FDR_SCRIPTS,IDENT) 
	
  'rule' Proc(fdr_process_def(Ident,Fdr_pattern_exprs,Fdr_process_combination,Fdr_alphabet_in,Fdr_alphabet_out),FDR_Decls,Proc_id):
	     eq(Proc_id,Ident)
	     Is_empty(Fdr_alphabet_in -> Res_in)
	     Is_empty(Fdr_alphabet_out -> Res_out)
	     (| eq(Res_in,1)
	        eq(Res_out,1)

	        Al_in <- Fdr_alphabet_in  
	        Al_out <- Fdr_alphabet_out

	        Putmsg("\nAlphabet of process ")
	        Print_id(Proc_id)
	        ErrorUsage(" is empty")
	     ||
	        Al_in <- Fdr_alphabet_in  
	        Al_out <- Fdr_alphabet_out
	     |)

  'rule' Proc(Fdr_def,FDR_Decls,Proc_id) 


------------------------------------
---- Print Process Identifier ------
-------------------------------------

'action' PrintProcId(IDENT)

  'rule' PrintProcId(Id)
         WriteFile(" {")
	     Out_Ident(Id)
         WriteFile("}")

-------------------------------

'action' LTL_out_Ident(IDENT)

  'rule' LTL_out_Ident(Ident):
	     Is_valid_sym(Ident -> Al_in, Al_out)
         C_id_to_string(Ident -> IdentString)
         WriteFile(IdentString)


----------------------------
----- Print operator  -------
-----------------------------

'action' LTL_out_id_or_op(ID_OR_OP)

  'rule' LTL_out_id_or_op(id_op(Id)):
         --LTL_out_Ident(Id)
	     Out_Ident(Id)

  'rule' LTL_out_id_or_op(op_op(Op)):
         LTL_out_op(Op)

-----------------------------
'action' LTL_out_op(OP)

  'rule' LTL_out_op(Op):
         Op_to_print_string(Op -> Str)
         WriteFile(Str)

----------------------------



---- Is_not_sym return a sym if it is a chan_occ , 'nil' in other case --

'action' Is_not_sym(FDR_VALUE_EXPR -> STRING)

  'rule' Is_not_sym(fdr_chan_occ(Id_CH) -> Sym):
	     id_to_string (Id_CH -> StrSym)
	     where(StrSym -> Sym)

  'rule' Is_not_sym(Fdr -> Sym):
	     where("nil"-> Sym)


-------------------------
--  If Id_CH is a hidden symbol it will not in the alphabet
-------------------------
'action' Is_valid_sym(IDENT -> FDR_ALPHABET,FDR_ALPHABET)

  'rule' Is_valid_sym(Id -> Alph_in, Alph_out)
	     Al_in -> Alph_in
	     Al_out -> Alph_out
         Alphab(Id, Alph_in -> Isin_in)
         Alphab(Id, Alph_out -> Isin_out)

         (| ne(Isin_in,"1")
            ne(Isin_out,"1") 
	        Putmsg("\nError: Symbol ")
	        Print_id(Id)
	        ErrorUsage(" is hidden in the alphabet")
         ||
            (| eq(Isin_in,"1") || eq(Isin_out,"1") |)
         |)

------------------

'action' Alphab(IDENT,FDR_ALPHABET -> STRING)

  'rule' Alphab(Id, fdr_alpha_def(Ident,Fdr_pattern_exprs,Fdr_alpha) -> Isin):
	     Alphab_expr(Id, Fdr_alpha -> Isin2)
	     where(Isin2 -> Isin)

--------------------

'action' Alphab_expr(IDENT,FDR_ALPHA_EXPR -> STRING) 

  'rule' Alphab_expr(Id,Alpha -> Isin):
         where(Alpha ->fdr_enum_alpha(Fdr_enum_alpha_exprs))
         Enum_alphab_exprs(Id,Fdr_enum_alpha_exprs -> Isin2)
	     where(Isin2 -> Isin)

-------------------

'action' Enum_alphab_exprs(IDENT,FDR_ENUM_ALPHA_EXPRS -> STRING)

  'rule' Enum_alphab_exprs(Id,list(Fdr_enum_alpha_expr,Fdr_enum_alpha_exprsTail)-> Isin):
         Enum_alphab_expr(Id,Fdr_enum_alpha_expr -> Res)
	     (| eq(Res,"0")
            eq(Fdr_enum_alpha_exprsTail,nil)
	        where(Res -> Isin)
         ||
 	        ne(Res,"1")
	        ne(Res,"2")
	        Enum_alphab_exprs(Id,Fdr_enum_alpha_exprsTail -> Isin2) 
	        where(Isin2 -> Isin)
	     ||
	        eq(Res,"1")
	        where(Res -> Isin)
         |)   

  'rule' Enum_alphab_exprs(Id,nil -> Isin)
         where("2" -> Isin)

-----------------

'action' Enum_alphab_expr(IDENT,FDR_ENUM_ALPHA_EXPR -> STRING)

  'rule' Enum_alphab_expr(Id_CH,fdr_enum_alpha_expr(Ident,Fdr_value_exprs) -> Res):
	     (| ne(Id_CH,Ident)
	        where("0" -> Res)
         ||
	        eq(Id_CH,Ident)
	        where("1" -> Res)
	     |)

  'rule' Enum_alphab_expr(Id,Fdr -> Res):
	     where("2" -> Res)



----------------------------------------------
--- Print negation of a symbol in Alphabet ----
--------------------------------------------

'action' LTL_out_neg_alph(STRING)

  'rule' LTL_out_neg_alph(Sym)
         WriteFile("(")
         WriteFile("delta")
	     GetProc(Sym ->A_in,A_out)
         WriteFile(")")

-----------------------------
'action' GetProc(STRING -> FDR_ALPHABET,FDR_ALPHABET) 
	
  'rule' GetProc(Sym -> Alph_in, Alph_out):
	     Al_in -> Alph_in
	     Al_out -> Alph_out
         Alph(Sym,Alph_in)
         Alph(Sym,Alph_out)   

  'rule' GetProc(Sym -> Alph_in, Alph_out):
	     Al_in -> Alph_in
	     Al_out -> Alph_out

------------------

'action' Alph(STRING,FDR_ALPHABET)

  'rule' Alph(Sym,fdr_alpha_def(Ident,Fdr_pattern_exprs,Fdr_alpha)):
	     Alpha_expr(Sym,Fdr_alpha)

--------------------

'action' Alpha_expr(STRING,FDR_ALPHA_EXPR) 

  'rule' Alpha_expr(Sym,Alpha):
         where(Alpha ->fdr_enum_alpha(Fdr_enum_alpha_exprs))
         Enum_al_exprs(Sym,Fdr_enum_alpha_exprs)

-------------------

'action' Enum_al_exprs(STRING,FDR_ENUM_ALPHA_EXPRS)

  'rule' Enum_al_exprs(Sym,list(Fdr_enum_alpha_expr,Fdr_enum_alpha_exprsTail)):
         Enum_al_expr(Sym,Fdr_enum_alpha_expr)
	     Enum_al_exprs(Sym,Fdr_enum_alpha_exprsTail)
  
  'rule' Enum_al_exprs(Sym,nil)

-----------------

'action' Enum_al_expr(STRING,FDR_ENUM_ALPHA_EXPR)

  'rule' Enum_al_expr(Sym,fdr_enum_alpha_expr(Ident,Fdr_value_exprs)):
	     id_to_string (Ident -> StrId)         
	     ne(Sym,StrId)
	     WriteFile("||")
	     WriteFile(StrId)

  'rule' Enum_al_expr(Sym,Fdr):




------------------------------------
------ Print final Alphabet --------
---------------------------------

'action' LTL_out_alphabet()

  'rule' LTL_out_alphabet()
         WriteFile(" {")
	     Get_proc( -> AIn, AOut) 
         WriteFile("}")

-----------------

'action' Get_proc( -> FDR_ALPHABET,FDR_ALPHABET) 
	
  'rule' Get_proc( -> Alph_in, Alph_out):
	     Al_in -> Alph_in
	     Al_out -> Alph_out

	     Is_empty(Alph_in -> Res_in)
	     Is_empty(Alph_out -> Res_out) 
	     (| 
	        eq(Res_in,1)
	        eq(Res_out,0)
	        Alphabet(Alph_out)
	     ||
	        eq(Res_in,0)
	        eq(Res_out,1)
            Alphabet(Alph_in)
	     ||
	        eq(Res_in,0)
	        eq(Res_out,0)
            Alphabet(Alph_in)
            WriteFile("$") -- separator of alphabet symbols
            Alphabet(Alph_out)   
	     |)

  'rule' Get_proc( -> Alph_in, Alph_out):
	     Al_in -> Alph_in
	     Al_out -> Alph_out

------------------

'action' Alphabet(FDR_ALPHABET)

  'rule' Alphabet(fdr_alpha_def(Ident,Fdr_pattern_exprs,Fdr_alpha)):
	 Alphabet_expr(Fdr_alpha)

--------------------

'action' Alphabet_expr(FDR_ALPHA_EXPR) 

  'rule' Alphabet_expr(Alpha):
         where(Alpha ->fdr_enum_alpha(Fdr_enum_alpha_exprs))
         Enum_alphabet_exprs(Fdr_enum_alpha_exprs)

-------------------

'action' Enum_alphabet_exprs(FDR_ENUM_ALPHA_EXPRS)

  'rule' Enum_alphabet_exprs(list(Fdr_enum_alpha_expr,Fdr_enum_alpha_exprsTail)):
         Enum_alphabet_expr(Fdr_enum_alpha_expr)
         [|ne(Fdr_enum_alpha_exprsTail,nil)
           WriteFile("$") 
         |]
	     Enum_alphabet_exprs(Fdr_enum_alpha_exprsTail)
  
  'rule' Enum_alphabet_exprs(nil)

-----------------

'action' Enum_alphabet_expr(FDR_ENUM_ALPHA_EXPR)

  'rule' Enum_alphabet_expr(fdr_enum_alpha_expr(Ident,Fdr_value_exprs)):
	     Out_Ident(Ident)   

  'rule' Enum_alphabet_expr(Fdr):



---------------------
---- Is_empty   -----
----------------------

'action' Is_empty(FDR_ALPHABET -> INT)

  'rule' Is_empty(fdr_alpha_def(Ident,Fdr_pattern_exprs,Fdr_alpha) -> Res):
	     where(Fdr_alpha -> fdr_enum_alpha(Fdr_enum_alpha_exprs))
	     Enum_alpha_exprs(Fdr_enum_alpha_exprs -> Res)

  'rule' Is_empty(Fdr -> Res):
         where(0 -> Res)
	     ErrorUsage("\nError: Alphabet is empty")

--------------------

'action' Enum_alpha_exprs(FDR_ENUM_ALPHA_EXPRS -> INT)

  'rule' Enum_alpha_exprs(list(Fdr_enum_alpha_expr,Fdr_enum_alpha_exprsTail) -> Res):
	     where(0 -> Res)
  
  'rule' Enum_alpha_exprs(nil -> Res)
	     where(1 -> Res)
         


--  Copy of fdr_gen_code (adaptation to LTL translation)
---------------------------------------
-----------value definition------------
---------------------------------------

'action' GenCode_Ltl_value_exprs(FDR_VALUE_EXPRS)

  'rule' GenCode_Ltl_value_exprs(list(Fdr_value_expr,Fdr_value_exprsTail)):
	     GenCode_Ltl_value_expr(Fdr_value_expr)
	     GenCode_Ltl_value_exprs(Fdr_value_exprsTail)

  'rule' GenCode_Ltl_value_exprs(nil)


'action' GenCode_Ltl_value_expr(FDR_VALUE_EXPR)

  'rule' GenCode_Ltl_value_expr(fdr_pref_expr(Fdr_op,Fdr_value_expr)):
         [|ne(Fdr_op,nil)
           GenCode_Ltl_op(Fdr_op)
           GenCode_Ltl_value_expr(Fdr_value_expr)
         |]

  'rule' GenCode_Ltl_value_expr(fdr_infi_expr(Fdr_value_expr1,Fdr_op,Fdr_value_expr2)):
 	     [|ne(Fdr_op,nil)
           GenCode_Ltl_value_expr(Fdr_value_expr1)  
           GenCode_Ltl_op(Fdr_op)  

           GenCode_Ltl_value_expr(Fdr_value_expr2)       
	     |]

  'rule' GenCode_Ltl_value_expr(fdr_fun_appl1(Fdr_fun,Fdr_value_expr)):
         [|ne(Fdr_fun,nil)
           WriteFile("(")   
           GenCode_Ltl_value_expr(Fdr_value_expr)
           WriteFile(")")   
	     |]

  'rule' GenCode_Ltl_value_expr(fdr_fun_appl2(Fdr_fun,Fdr_value_expr1,Fdr_value_expr2)):
         (| eq(Fdr_fun,fdr_R) || eq(Fdr_fun,fdr_U) |)
         WriteFile("(")   
         GenCode_Ltl_value_expr(Fdr_value_expr1)
         WriteFile(" ")   
         WriteFile(" ")   
         GenCode_Ltl_value_expr(Fdr_value_expr2)
         WriteFile(")")        

  'rule' GenCode_Ltl_value_expr(fdr_fun_appl2(Fdr_fun,Fdr_value_expr1,Fdr_value_expr2)):
 	     ne(Fdr_fun,nil)
         WriteFile("(")   
         GenCode_Ltl_value_expr(Fdr_value_expr1)
	     WriteFile(",")
         GenCode_Ltl_value_expr(Fdr_value_expr2)
         WriteFile(")")   

  'rule' GenCode_Ltl_value_expr(fdr_function(I,Fdr_value_exprs)):
	     string_to_id ("G" -> G)
	     string_to_id ("F" -> F)
	     string_to_id ("U" -> U)
	     string_to_id ("R" -> R)
	     string_to_id ("X" -> X)
	     ne(I, G)
	     ne(I, F)
	     ne(I, U)
	     ne(I, R)
	     ne(I, X)

	     Out_Ident(I)
	     WriteFile("(")   
         GenCode_Ltl_value_exprs(Fdr_value_exprs)
         WriteFile(")")


  'rule' GenCode_Ltl_value_expr(fdr_function(I,Fdr_value_exprs)):
	     string_to_id ("G" -> G)
	     string_to_id ("F" -> F)
	     string_to_id ("X" -> X)
	     (| 
	        eq(I, G) 
            WriteFile("[]")   
         || 
	        eq(I, F) 
            WriteFile("<>")   
         || 
	        eq(I, X) 
            WriteFile("X")   
         |)
         WriteFile("(")   
         GenCode_Ltl_value_exprs(Fdr_value_exprs)
         WriteFile(")")


  'rule' GenCode_Ltl_value_expr(fdr_function(I,Fdr_value_exprs)):
	     where(Fdr_value_exprs -> list(A1, list(A2,nil)))
	     string_to_id ("U" -> U)
	     string_to_id ("R" -> R)
         WriteFile("(")   
         GenCode_Ltl_value_expr(A1)
	     (| 
	        eq(I, U) 
            WriteFile(" U ")   
         || 
	        eq(I, R) 
            WriteFile(" V ")   
         |)
         GenCode_Ltl_value_expr(A2)
         WriteFile(")")


  'rule' GenCode_Ltl_value_expr(fdr_function(I,Fdr_value_exprs)):
	     string_to_id ("G" -> G)
	     string_to_id ("F" -> F)
	     string_to_id ("U" -> U)
	     string_to_id ("R" -> R)
	     string_to_id ("X" -> X)
	     ne(I, G) 
	     ne(I, F) 
	     ne(I, U) 
	     ne(I, R) 
	     ne(I, X) 
         LTL_out_Ident(I)
         WriteFile("(")   
         GenCode_Ltl_value_exprs(Fdr_value_exprs)
         WriteFile(")")


  'rule' GenCode_Ltl_value_expr(fdr_ax_prefix(P, C, E)):
         Translate_Value_expr_To_Fdr_value_expr(E->Fdr_exp)
         Is_not_sym(Fdr_exp -> Sym)
         (| ne(Sym,"nil")
	        string_to_id (Sym -> Id)
	        Is_valid_sym(Id -> Al_in, Al_out)
	        LTL_out_neg_alph(Sym)
	     || 
            eq(Sym,"nil")
            WriteFile("!(")   
            GenCode_Ltl_value_expr(Fdr_exp)
            WriteFile(")")   
	     |)

  'rule' GenCode_Ltl_value_expr(fdr_infix_occ(P,L,I,Q,R)):
         I'Ident -> Id
         WriteFile("(")
         Translate_Value_expr_To_Fdr_value_expr(L->Fdr_L1)
         GenCode_Ltl_value_expr(Fdr_L1)
         WriteFile(" ")
         LTL_out_id_or_op(Id)
         WriteFile(" ")
         Translate_Value_expr_To_Fdr_value_expr(R->Fdr_R1)
         GenCode_Ltl_value_expr(Fdr_R1)
         WriteFile(")")

  'rule' GenCode_Ltl_value_expr(fdr_ax_infix(P,L,C,R,_)):

  'rule' GenCode_Ltl_value_expr(fdr_chan_occ(Id_CH)):
         LTL_out_Ident(Id_CH)

  'rule' GenCode_Ltl_value_expr(fdr_named_val(Ident)):
         Out_Ident(Ident)

  'rule' GenCode_Ltl_value_expr(fdr_literal_expr(Fdr_value_literal)):
         WriteFile(" delta ")

  'rule' GenCode_Ltl_value_expr(fdr_bracket (Fdr_value_expr)):
         WriteFile("(")   
         GenCode_Ltl_value_expr(Fdr_value_expr)
         WriteFile(")") 
 
  'rule' GenCode_Ltl_value_expr(nil)


-----prefix, infix operator----------
'action' GenCode_Ltl_op (FDR_OP)

  'rule' GenCode_Ltl_op(fdr_and):WriteFile(" && ")

  'rule' GenCode_Ltl_op(fdr_or):WriteFile(" || ")

  'rule' GenCode_Ltl_op(fdr_implies):WriteFile(" -> ")


