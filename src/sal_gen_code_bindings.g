-- RSL Type Checker
-- Copyright (C) 1998 - 2005 UNU/IIST

-- raise@iist.unu.edu

-- This module generates the SAL bindings

 
'module' sal_gen_code_bindings

'use' ast print 
      ext -- DefaultPos
      env 
      objects 
      values 
      types 
      pp 
      cc
      sal_aux
      sal_ast
      sal_gen_code_aux
      sal_gen_code_types
      sal_gen_code

'export' 
	 SAL_Out_LetBindings
	 SAL_Out_Bindings
	 SAL_Gen_LetBindings
	 SAL_Out_LambdaBindings
	 SAL_Out_Binding
------------------------------------------------------
-- Bindings...
------------------------------------------------------

'action' SAL_Out_Bindings(SAL_BINDINGS, SAL_LET_BINDINGS, 
					SAL_TYPE_EXPR -> SAL_LET_BINDINGS)

  'rule' SAL_Out_Bindings(BS:list(B,list(_,_)), LBS, 
	     user_defined(sal_tuple_type(list(sal_tuple(T), nil))) -> LBS1):
	 -- Extracting the position:
	 (|
	     where(B -> sal_prod_binding(P,_))
	 ||
	     where(B -> sal_typed_prod(P,_,_))
	 ||
	     where(B -> sal_typed_id(P,_,_))
	 |)
	 -- product parameter has been made into single one because of
	 -- curried function with precondition
	 SAL_Out_Binding(sal_typed_prod(P, BS, T), LBS, sal_tuple(T) -> LBS1)

  'rule' SAL_Out_Bindings(list(B, BS), LBS, T -> LBS1):
	 (|
	   where(T -> user_defined(sal_tuple_type(list(TT, TTS))))
	 ||
	   where(SAL_TUPLE_ELEM'nil -> TT)
	   where(SAL_TUPLE_ELEMS'nil -> TTS)
	 |)
	 SAL_Out_Binding(B, LBS, TT -> LBS2)
	 (|
	   ne(BS, nil)
	   WriteFile(", ")
	   (|
	      eq(T,nil)
	      SAL_Out_Bindings(BS, LBS2, nil -> LBS1)
	   ||
	      where(T -> Expr)
	      SAL_Out_Bindings(BS, LBS2, user_defined(sal_tuple_type(TTS))
							-> LBS1) 
	   |)
	   
	 ||
	   where(LBS2 -> LBS1)
	 |)


  'rule' SAL_Out_Bindings(nil, LBS, _ -> LBS):

  'rule' SAL_Out_Bindings(BS , _,T-> nil):
	 print(" Bindings------------------------------------------\n")
	 print(BS)
	 print("Type ------------------------------------------\n")
	 print(T)
	 print("----------------------------------------------------\n")

'action' SAL_Out_Binding(SAL_BINDING, SAL_LET_BINDINGS, 
				      SAL_TUPLE_ELEM -> SAL_LET_BINDINGS)

  'rule' SAL_Out_Binding(sal_typed_id(Pos, IdOp, T), LBS, _ -> LBS):
	 SAL_Out_IdOp(IdOp)
	 [|
	   ne(T, nil)
	   WriteFile(": ")
	   SAL_Out_Type_Expr(T)
         |]

  'rule' SAL_Out_Binding(sal_typed_prod(Pos, BS, T), LBS, TT -> LBS1):
	 SAL_Gen_Prod_Ident("" -> IdProd)
	 id_to_string(IdProd -> IdProdStrng)
	 WriteFile(IdProdStrng)
	 WriteFile(": ")
	 SAL_Out_Type_Expr(T)
	 SAL_Gen_LetBindings(IdProd, BS, LBS -> LBS1)
	 [|
	     ne(LBS, LBS1)
	     Puterror(Pos)
	     Putmsg("Nested product bindings not allowed\n")
	 |]


  'rule' SAL_Out_Binding(sal_prod_binding(Pos, BS), LBS, _ -> LBS1):
	 SAL_Gen_Prod_Ident("" -> IdProd)
	 id_to_string(IdProd -> IdProdStrng)
	 WriteFile(IdProdStrng)
	 SAL_Gen_LetBindings(IdProd, BS, LBS -> LBS1)
 	 [|
	     ne(LBS, LBS1)
	     Puterror(Pos)
	     Putmsg("Nested product bindings not allowed\n")
	 |]

--------------------------------------------------
'action' SAL_Out_LetBindings(SAL_LET_BINDINGS)

  'rule' SAL_Out_LetBindings(list(LetBinding, LetBindingsTail)):
	 SAL_Out_LetBinding(LetBinding)
	 [|
	   ne(LetBindingsTail, nil)
	   WriteFile(", ")
	 |]
	 SAL_Out_LetBindings(LetBindingsTail)

  'rule' SAL_Out_LetBindings(nil):


--------------------------------------------------
'action' SAL_Out_LetBinding(SAL_LET_BINDING)

  'rule' SAL_Out_LetBinding(sal_let_bind(LetBind, Expr)):
 	 SAL_Out_LetBind(LetBind)
	 where(Expr -> ExprDis)
	 where(SAL_TYPE_EXPR'nil -> TypeExpr)
	 [|
	   ne(TypeExpr, nil)
	   WriteFile(" : ")
 	   SAL_Out_Type_Expr(TypeExpr)
	 |]
	 WriteFile(" = ")
 	 SAL_Out_Expr(ExprDis)

  'rule' SAL_Out_LetBinding(sal_let_binds(LetBinds, Expr)):
 	 WriteFile("(")
	 SAL_Out_LetBinds(LetBinds)
 	 WriteFile(") = ")	 
 	 SAL_Out_Expr(Expr)

  'rule' SAL_Out_LetBinding(nil):


--------------------------------------------------
'action' SAL_Out_LetBinds(SAL_LETBINDS)

  'rule' SAL_Out_LetBinds(list(LetBind, LetBindsTail)):
	 SAL_Out_LetBind(LetBind)
	 [|
	   ne(LetBindsTail, nil)
	   WriteFile(", ")
	 |]
	 SAL_Out_LetBinds(LetBindsTail)

  'rule' SAL_Out_LetBinds(nil):


--------------------------------------------------
'action' SAL_Out_LetBind(SAL_LETBIND)

  'rule' SAL_Out_LetBind(sal_let_idop(IdOp, nil, nil)):
	 SAL_Out_IdOp(IdOp)

-------------------------------------------------

'action' SAL_Gen_LetBindings(IDENT, SAL_BINDINGS, 
				    SAL_LET_BINDINGS -> SAL_LET_BINDINGS)

  'rule' SAL_Gen_LetBindings(Id, BS, LBS ->
	   list(sal_let_binds(LetBinds, sal_named_val(id_op(id(Id)))), LBS2)):
	 SAL_Bindings_to_Letbinds(BS, LBS -> LetBinds, LBS2)
	 
'action' SAL_Bindings_to_Letbinds(SAL_BINDINGS, SAL_LET_BINDINGS 
					-> SAL_LETBINDS, SAL_LET_BINDINGS)
	 
  'rule' SAL_Bindings_to_Letbinds(list(sal_typed_id(Pos, IdOp,_), BS), LBS 
                          -> list(sal_let_idop(IdOp,nil,nil), LetBinds), LBS1):
         SAL_Bindings_to_Letbinds(BS, LBS -> LetBinds, LBS1)

  'rule' SAL_Bindings_to_Letbinds(list(sal_prod_binding(Pos, BS1), BS), LBS 
                          -> list(sal_let_idop(id(IdProd),nil,nil), LetBinds), LBS1):
	 SAL_Gen_Prod_Ident("" -> IdProd)
	 SAL_Gen_LetBindings(IdProd, BS1, LBS -> LBS2)
	 SAL_Bindings_to_Letbinds(BS, LBS2 -> LetBinds, LBS1)

  'rule' SAL_Bindings_to_Letbinds(list(sal_typed_prod(Pos, BS1, _), BS), LBS 
                          -> list(sal_let_idop(id(IdProd),nil,nil), LetBinds), LBS1):
	 SAL_Gen_Prod_Ident("" -> IdProd)
	 SAL_Gen_LetBindings(IdProd, BS1, LBS -> LBS2)
	 SAL_Bindings_to_Letbinds(BS, LBS2 -> LetBinds, LBS1)

  'rule' SAL_Bindings_to_Letbinds(nil, LBS -> nil, LBS):

----------------------------------------------------
'action' SAL_Out_LambdaBindings(SAL_LAMBDA_BINDINGS, 
					SAL_LET_BINDINGS -> SAL_LET_BINDINGS)

  'rule' SAL_Out_LambdaBindings(list(bindings(BS), LmbdBndngsTail), LBS -> LBS2):
	 SAL_Out_Bindings(BS, LBS, nil -> LBS1)
	 SAL_Out_LambdaBindings(LmbdBndngsTail, LBS1 -> LBS2)

  'rule' SAL_Out_LambdaBindings(nil, LBS -> LBS)
	 


