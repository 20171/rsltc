-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module generates the PVS code 
-- from the PVS abstract syntax tree

 
'module' pvs_gen_code

'use' ast print ext env objects values types pp cc
      pvs pvs_ast pvs_aux pvs_gen_ast sml

'export' 
	 Gen_PVS_Code Init_Var_Gen_Code Init_Indexes
	 Gen_Prod_Ident CcLemmaName JudgementName

	 Out_Idents Out_Ident



--------------------------------------------------
--  Variables
--------------------------------------------------

--------------------------------------------------
-- Used to generate different Product Identifiers
'var' ProdIndex		:	INT
'var' ProdIndex2	:	INT


--------------------------------------------------
-- Used to generate different Axiom Identifiers
'var' AxiomIndex		:	INT


--------------------------------------------------
-- Used to generate different Lemma Identifiers
'var' LemmaIndex		:	INT


--------------------------------------------------
-- Used to generate different Judgement Identifiers
'var' JudgementIndex		:	INT


--------------------------------------------------
--  Actions
--------------------------------------------------


--------------------------------------------------
'action' Gen_PVS_Code(THEORY_ELEMENTS)

  'rule' Gen_PVS_Code(TheoryElements):
	 Process_Theory_Elements(TheoryElements)


--------------------------------------------------
'action' Init_Var_Gen_Code

  'rule' Init_Var_Gen_Code:
	 -- Product Index Identifier stars w/0
	 ProdIndex <- 0
	 -- Product Index Identifier (2) stars w/0
	 ProdIndex2 <- 0

'action' Init_Indexes

  'rule' Init_Indexes:
	 -- Indexes start from 0
	 AxiomIndex <- 0
	 LemmaIndex <- 0
	 JudgementIndex <- 0


--------------------------------------------------
'action' Process_Theory_Elements(THEORY_ELEMENTS)

  'rule' Process_Theory_Elements(list(TheoryElement, TheoryElementsTail)):
	 Process_Theory_Element(TheoryElement)
	 Process_Theory_Elements(TheoryElementsTail)

	 -- no more TheoryElements
  'rule' Process_Theory_Elements(nil):



--------------------------------------------------
'action' Process_Theory_Element(THEORY_ELEMENT)

  'rule' Process_Theory_Element(importing(Importing)):
	 Process_Importing(Importing)

  'rule' Process_Theory_Element(theory_decl(TheoryDecl)):
	 Process_Theory_Decl(TheoryDecl)

  'rule' Process_Theory_Element(rec_decl(TheoryElements)):
	 Process_Recursive_Elements(TheoryElements)

	 -- for debugging
  'rule' Process_Theory_Element(mark_decl(Msg)):
	 WritelnFile(2)
	 WriteFile("% ")
	 WriteFile(Msg)
	 WritelnFile(2)


--------------------------------------------------
'action' Process_Importing(IMPORTING)

  'rule' Process_Importing(theory_name(Theory_Names)):

  'rule' Process_Importing(theory_map(Dom, Rng)):
	 WriteFile("  IMPORTING Map[")
	 Out_Type_Expr(Dom)
	 WriteFile(", ")
	 Out_Type_Expr(Rng)
	 WriteFile("]")
	 WritelnFile(2)

  'rule' Process_Importing(theory_ranged_set(TypeExpr)):
	 WriteFile("  IMPORTING Ranged_Set")
	 WritelnFile(2)

  'rule' Process_Importing(theory_ranged_list(TypeExpr)):
	 WriteFile("  IMPORTING Ranged_List")
	 WritelnFile(2)

         -- not used
  'rule' Process_Importing(theory_comp_list(TypeExpr)):
/*
	 WriteFile("  IMPORTING [")
	 Out_Type_Expr(TypeExpr)
	 WriteFile("]")
	 WritelnFile(2)
*/


--------------------------------------------------
'action' Process_Theory_Decl(THEORY_DECL)

  'rule' Process_Theory_Decl(type_decl(Ids, Bindings, EqFrom, TypeExpr, Containing)):
	 Process_Type_Decl(type_decl(Ids, Bindings, EqFrom, TypeExpr, Containing))

  'rule' Process_Theory_Decl(var_decl(IdOps, TypeExpr)):

  'rule' Process_Theory_Decl(const_decl(ConstantDecl)):
	 Process_Const_Decl(ConstantDecl)

  'rule' Process_Theory_Decl(formula_decl(Strng, FormName, Expr)):
	 Process_Form_Decl(formula_decl(Strng, FormName, Expr))

  'rule' Process_Theory_Decl(judgement_decl(Strng, Id, Params, Type, Pre)):
	 Process_Judgement_Decl(judgement_decl(Strng, Id, Params, Type, Pre))

  'rule' Process_Theory_Decl(post_decl(Strng, Id, Params, Type, Pre, Post)):
	 Process_Post_Decl(post_decl(Strng, Id, Params, Type, Pre, Post))

  'rule' Process_Theory_Decl(inline_datatype(Id, DataTypeParts)):
	 Process_DataType(Id, DataTypeParts)


--------------------------------------------------
'action' Process_Type_Decl(THEORY_DECL)

  'rule' Process_Type_Decl(type_decl(Ids, Bindings, EqFrom, TypeExpr, Containing)):
	 WriteIndntFile(2)
	 Out_Idents(Ids)
	 -- Avoid TCC from non-emptiness for abbreviations
	 -- since decided by RHS.
	 -- Particularly useful when RHS is a subtype.
	 (|
	   where(EqFrom -> equal)
	   WriteFile(": TYPE = ")
	   Out_Type_Expr(TypeExpr)
	   WriteFile(";")
	 ||
	   WriteFile(": TYPE+;")
	 |)
	 WritelnFile(2)


--------------------------------------------------
'action' Process_Const_Decl(CONSTANT_DECL)

	 -- RSL Commented Typing
  'rule' Process_Const_Decl(nodef(IdOps, TypeExpr, Containing)):
	 WriteIndntFile(2)
	 Out_IdOps(IdOps)
	 WriteFile(" : ")
	 Out_Type_Expr(TypeExpr)
	 WriteFile(";")
	 WritelnFile(2)

	 -- RSL Explicit Value Declaration
  'rule' Process_Const_Decl(expl_const(IdOps, TypeExpr, Containing)):
	 -- only single typing, single binding allowed in RSL
	 WriteIndntFile(2)
	 Out_IdOps(IdOps)
	 WriteFile(" : ")
	 Out_Type_Expr(TypeExpr)
	 WriteFile(" = ")
	 WritelnFile(1)
	 WriteIndntFile(4)
	 Out_PVS_Expr(Containing)
	 WriteFile(";")
	 WritelnFile(1)
	 WriteIndntFile(2)
	 WriteFile("AUTO_REWRITE ")
	 Out_IdOps(IdOps)
	 WriteFile(";")
	 WritelnFile(2)

	 -- RSL Implicit Value Declaration
  'rule' Process_Const_Decl(impl_const(IdOps, TypeExpr, Containing)):
	 -- RSL
	 -- x : T :- e
	 -- PVS
	 -- x : T
	 -- x_ax_: AXIOM e
	 -- only single typing, single binding allowed in RSL
	 WriteFile("  % Axiom for implicit value declaration")
	 WritelnFile(1)
	 WriteIndntFile(2)
	 Out_IdOps(IdOps)
	 WriteFile(" : ")
	 Out_Type_Expr(TypeExpr)
	 WritelnFile(1)
	 WriteIndntFile(4)
	 Out_IdOps(IdOps)
	 Gen_Axiom_Name("_axiom" -> AxiomName)
	 WriteFile(AxiomName)
	 WriteFile(": AXIOM ")
	 WritelnFile(1)
	 WriteIndntFile(6)
	 Out_PVS_Expr(Containing)
	 WriteFile(";")
	 WritelnFile(1)
	 WriteIndntFile(2)
	 WriteFile("AUTO_REWRITE ")
	 Out_IdOps(IdOps)
	 WriteFile(AxiomName)
	 WriteFile(";")
	 WritelnFile(2)

	  -- Explicit function signature (from mutual recursion)
	  -- (also used for implicit)
  'rule' Process_Const_Decl(expl_fun_const(IdOp, _, Params, TypeExpr, nil, PreExpr)):
	 WriteIndntFile(2)
	 Out_IdOp(IdOp)
	 WriteFile(" : ")
	 (|
	   eq(PreExpr, nil)
	   Out_Type_Expr(TypeExpr)
	 ||
	   Include_pre_in_param_type(Params, TypeExpr, PreExpr, nil -> Params1, TypeExpr1)
	 Out_Type_Expr(TypeExpr1)
	 |)
	 WriteFile(";")
	 WritelnFile(2)
	 	 

	 -- RSL Explicit Function Declaration: total function, Pre = nil
  'rule' Process_Const_Decl(expl_fun_const(IdOp, Recursive, Params, TypeExpr, Expr, nil)):
	 -- RSL
	 -- f : T1 -> T2
	 -- f(x) is e(x)
	 -- PVS
	 -- f(x: T1): T2 = e(x)
	 -- Is the function recursive?
	 (|
	   eq(Recursive, nil)
	   -- No, it is not a recursive function
	   WriteIndntFile(2)
	   Out_IdOp(IdOp)
	   Out_Params(Params, TypeExpr, nil -> LBS, Result)
	   WriteFile(": ")
	   Out_Type_Expr(Result)
	   WriteFile(" = ")
	   WritelnFile(1)
	   [|
	     ne(LBS, nil)
	     WriteFile("    LET ")
	     Out_LetBindings(LBS)
	     WriteFile(" IN")
	     WritelnFile(1)
	   |]
	   WriteIndntFile(4)
	   Out_PVS_Expr(Expr)
	   WriteFile(";")
	   WritelnFile(1)
	   WriteIndntFile(2)
	   WriteFile("AUTO_REWRITE ")
	   Out_IdOp(IdOp)
	   WriteFile(";")
	   WritelnFile(2)

	 ||
	   -- Yes, it's recursive
	   -- Function Signature
	   WriteIndntFile(2)
	   Out_IdOp(IdOp)
	   WriteFile(" : ")
	   Out_Type_Expr(TypeExpr)
	   WritelnFile(1)
	   -- Function Axiom
	   Out_Function_Axiom(expl_fun_const(IdOp, Recursive, Params,
                                    TypeExpr, Expr, nil))
	   WriteFile(";")
	   WritelnFile(2)
	 |)

         -- use subtype for non-recursive function with precondition
	 -- since more convenient in proof to unfold than to use axiom
	 -- RSL
	 -- f : T1 -~-> T2
	 -- f(x) is e(x)
	 -- pre e1(x)
	 -- PVS
	 -- f(x : {x:T1 | e1(x)}) : T2 = e(x)
  'rule' Process_Const_Decl(expl_fun_const(IdOp, Recursive, Params, TypeExpr, Expr, PreExpr)):
	 eq(Recursive, nil)  -- not recursive
	 WriteIndntFile(2)
	 Out_IdOp(IdOp)
	 Include_pre_in_params(Params, TypeExpr, PreExpr, nil -> Params1, TypeExpr1)
	 Out_Params(Params1, TypeExpr1, nil -> LBS, Result)
	 WriteFile(": ")
	 Out_Type_Expr(Result)
	 WriteFile(" = ")
	 WritelnFile(1)
	 [|
	   ne(LBS, nil)
	   WriteFile("    LET ")
	   Out_LetBindings(LBS)
	   WriteFile(" IN")
	   WritelnFile(1)
	 |]
	 WriteIndntFile(4)
	 Out_PVS_Expr(Expr)
	 WriteFile(";")
	 WritelnFile(1)
	 WriteIndntFile(2)
	 WriteFile("AUTO_REWRITE ")
	 Out_IdOp(IdOp)
	 WriteFile(";")
	 WritelnFile(2)




	 -- RSL Explicit Function Declaration:
	 -- recursive partial function, Pre <> nil
  'rule' Process_Const_Decl(expl_fun_const(IdOp, Recursive, Params, TypeExpr, Expr, PreExpr)):
	 -- RSL
	 -- f : T1 -~-> T2
	 -- f(x) is e(x)
	 -- pre e1(x)
	 -- PVS
	 -- f: [{x:T1 | e1(x)} -> T2]
	 -- f_ax: AXIOM FORALL (x: {x:T1 | e1(x)}): f(x) = e(x)
	 -- Function Signature
	 WriteIndntFile(2)
	 Out_IdOp(IdOp)
	 WriteFile(" : ")
	 Include_pre_in_param_type(Params, TypeExpr, PreExpr, nil -> Params1, TypeExpr1)
	 Out_Type_Expr(TypeExpr1)
	 WritelnFile(1)
	 -- Function Axiom
	 Out_Function_Axiom(expl_fun_const(IdOp, Recursive, Params1,
                                    TypeExpr1, Expr, nil))
	 WriteFile(";")
	 WritelnFile(2)

	 -- RSL Implicit Function Declaration: total function, Pre = nil
	 -- RSL Implicit Function Declaration: partial function, Pre <> nil
  'rule' Process_Const_Decl(impl_fun_const(IdOp, Params, TypeExpr,
						  PostCond, PreExpr)):
	 -- RSL
	 -- f : T1 -~-> T2
	 -- f(x) as id
	 -- post e1(x, id)
	 -- pre e2(x)
	 -- PVS
	 -- f: [{x:T1 | e2(x)} -> T2]
	 -- f_ax: AXIOM FORALL (x: {x:T1 | e2(x)}):
	 --   LET id = f(x) IN e1(x, id)

	 -- Function Signature
	 WriteIndntFile(2)
	 Out_IdOp(IdOp)
	 WriteFile(": ")
	 (|
	   eq(PreExpr, nil)
	   where(Params -> Params1)
	   where(TypeExpr -> TypeExpr1)
	 ||
	   Include_pre_in_param_type(Params, TypeExpr, PreExpr, nil ->
						   Params1, TypeExpr1)
	 |)
	 Out_Type_Expr(TypeExpr1)
	 WritelnFile(1)
	 -- Function Axiom
  	 Out_Function_Axiom(impl_fun_const(IdOp, Params1,
				TypeExpr1, PostCond, nil))
	 WriteFile(";")
	 WritelnFile(2)


--------------------------------------------------
-- puts out the axioms necessary for:
-- partial and recursive explicit functions
-- and implicit functions, total, partial and recursive
'action' Out_Function_Axiom(CONSTANT_DECL)

	 -- RSL Explicit Function Declaration:
	 -- partial function, Pre <> nil
	 -- Same for recursive function
  'rule' Out_Function_Axiom(expl_fun_const(IdOp, Recursive, Params,
                                TypeExpr, Expr, PreExpr)):
	 -- out axiom name
	 WriteFile("  % Axiom for ")
	 Out_IdOp(IdOp)
	 WriteFile(" function")
	 WritelnFile(1)
	 WriteIndntFile(2)
	 Out_IdOp_alpha(IdOp)
	 Gen_Axiom_Name("_axiom" -> AxiomName)
	 WriteFile(AxiomName)
	 WriteFile(": AXIOM FORALL ")
	 Out_Params(Params, TypeExpr, nil -> LBS, Result)
	 WriteFile(": ")
	 WritelnFile(1)
	 [|
	   ne(LBS, nil)
	   WriteFile("    LET ")
	   Out_LetBindings(LBS)
	   WriteFile(" IN")
	   WritelnFile(1)
	 |]
	 [| -- partial function
	   ne(PreExpr, nil)
	   -- Pre condition
	   WriteFile("    % precondition")
	   WritelnFile(1)
	   WriteIndntFile(6)
	   (|
	     PVS_lower_precedence(PreExpr, 18)
	     Out_PVS_Expr(PreExpr)
	   ||
	     Out_PVS_Expr(bracket(PreExpr))
	   |)
	   WritelnFile(1)
	   WriteFile("    IMPLIES")
	   WritelnFile(1)
	 |]
	 WriteIndntFile(6)
	 Out_IdOp(IdOp)
	 Out_Arguments_from_Params(Params)
	 WritelnFile(1)
	 WriteFile("      =")
	 WritelnFile(1)
	 WriteFile("      % definition")
	 WritelnFile(1)
	 WriteIndntFile(8)
	 (|
	   PVS_lower_precedence(Expr, 14)
	   Out_PVS_Expr(Expr)
	 ||
	   Out_PVS_Expr(bracket(Expr))
	 |)
	 WritelnFile(1)

	 -- RSL Implicit Function Declaration:
	 -- total function, Pre = nil
	 -- partial function, Pre <> nil
	 -- same for recursive functions
  'rule' Out_Function_Axiom(impl_fun_const(IdOp, Params,
				TypeExpr, PostCond, PreExpr))
	 WriteFile("  % Axiom for ")
	 Out_IdOp(IdOp)
	 WriteFile(" function")
	 WritelnFile(1)
	 WriteIndntFile(2)
	 -- out axiom name
	 Out_IdOp(IdOp)  -- f
	 Gen_Axiom_Name("_axiom" -> AxiomName)
	 WriteFile(AxiomName)
	 WriteFile(": AXIOM FORALL ")
	 Out_Params(Params, TypeExpr, nil -> LBS, Result)
	 WriteFile(": ")
	 WritelnFile(1)
	 [|
	   ne(LBS, nil)
	   WriteFile("    LET ")
	   Out_LetBindings(LBS)
	   WriteFile(" IN")
	   WritelnFile(1)
	 |]
	 [| -- partial function
	   ne(PreExpr, nil)
	   WriteFile("    % precondition")
	   WritelnFile(1)
	   WriteIndntFile(6)
	   (|
	     PVS_lower_precedence(PreExpr, 18)
	     Out_PVS_Expr(PreExpr)
	   ||
	     Out_PVS_Expr(bracket(PreExpr))
	   |)
	   WritelnFile(1)
	   WriteFile("    IMPLIES")
	   WritelnFile(1)
	 |]
	 where(PostCond -> postcond(Bindings, PostExpr))
	 [| -- bindings??
	   ne(Bindings, nil)
	   WriteFile("      LET (")
	   Out_PVSBindings(Bindings, nil, nil -> LBS1)
	   WriteFile(") = ")
	   Out_IdOp(IdOp)
	   Out_Arguments_from_Params(Params)
	   [|
	     ne(LBS1, nil)
	     WriteFile(", ")
	     Out_LetBindings(LBS1)
	   |]
	   WriteFile(" IN ")
	 |]
	 Out_PVS_Expr(PostExpr)



--------------------------------------------------
'action' Process_Form_Decl(THEORY_DECL)

  'rule' Process_Form_Decl(formula_decl(Strng, axiom, Expr)):
	 WriteIndntFile(2)
	 (|
	   ne(Strng, "")
	   where(Strng -> Name)
	 ||
	   Gen_Axiom_Name("RSL_axiom" -> AxiomIdString)
	   where(AxiomIdString -> Name)
	 |)
	 WriteFile(Name)
	 WriteFile(": AXIOM ")
	 WritelnFile(1)
	 WriteIndntFile(4)
	 Out_PVS_Expr(Expr)
	 WriteFile(";")
	 WritelnFile(1)
	 WriteIndntFile(2)
	 WriteFile("AUTO_REWRITE ")
	 WriteFile(Name)
	 WriteFile(";")
	 WritelnFile(2)

  'rule' Process_Form_Decl(formula_decl(Strng, lemma, Expr)):
	 WriteIndntFile(2)
	 (|
	   ne(Strng, "")
	   WriteFile(Strng)
	 ||
	   Gen_Axiom_Name("RSL_lemma" -> LemmaIdString)
	   WriteFile(LemmaIdString)
	 |)
	 WriteFile(": LEMMA ")
	 WritelnFile(1)
	 WriteIndntFile(4)
	 Out_PVS_Expr(Expr)
	 WriteFile(";")
	 WritelnFile(2)

  'rule' Process_Form_Decl(formula_decl(_, nil, _)):

--------------------------------------------------
'action' Process_Judgement_Decl(THEORY_DECL)

  'rule' Process_Judgement_Decl(judgement_decl(Strng, IdOp, Params, TypeExpr, PreExpr)):
	 WriteIndntFile(2)
	 WriteFile(Strng)
	 WriteFile(": JUDGEMENT ")
	 Out_IdOp(IdOp)
	 Include_pre_in_params(Params, TypeExpr, PreExpr, nil -> Params1, TypeExpr1)
	 Out_Params(Params1, TypeExpr1, nil -> LBS, Result)
	 WriteFile(" HAS_TYPE ")
	 Out_Type_Expr(Result)
	 WriteFile(";")
	 WritelnFile(2)

--------------------------------------------------
'action' Process_Post_Decl(THEORY_DECL)

  'rule' Process_Post_Decl(post_decl(Strng, IdOp, Params, TypeExpr, PostCond, PreExpr)):
	 WriteFile("  % Post condition lemma for ")
	 Out_IdOp(IdOp)
	 WriteFile(" function")
	 WritelnFile(1)
	 WriteIndntFile(2)
	 WriteFile(Strng)
	 WriteFile(": LEMMA FORALL ")
	 Out_Params(Params, TypeExpr, nil -> LBS, Result)
	 WriteFile(": ")
	 WritelnFile(1)
	 [|
	   ne(LBS, nil)
	   WriteFile("    LET ")
	   Out_LetBindings(LBS)
	   WriteFile(" IN")
	   WritelnFile(1)
	 |]
	 [| -- partial function
	   ne(PreExpr, nil)
	   WriteFile("    % precondition")
	   WritelnFile(1)
	   WriteIndntFile(6)
	   (|
	     PVS_lower_precedence(PreExpr, 18)
	     Out_PVS_Expr(PreExpr)
	   ||
	     Out_PVS_Expr(bracket(PreExpr))
	   |)
	   WritelnFile(1)
	   WriteFile("    IMPLIES")
	   WritelnFile(1)
	 |]
	 where(PostCond -> postcond(Bindings, PostExpr))
	 [| -- bindings??
	   ne(Bindings, nil)
	   WriteFile("      LET (")
	   Out_PVSBindings(Bindings, nil, nil -> LBS1)
	   WriteFile(") = ")
	   Out_IdOp(IdOp)
	   Out_Arguments_from_Params(Params)
	   [|
	     ne(LBS1, nil)
	     WriteFile(", ")
	     Out_LetBindings(LBS1)
	   |]
	   WriteFile(" IN ")
	 |]
	 Out_PVS_Expr(PostExpr)
	 WriteFile(";")
	 WritelnFile(2)

--------------------------------------------------
-- Process the Theory elements that are recursive
-- functions elements (functions), mutual and simple
--------------------------------------------------
'action' Process_Recursive_Elements(THEORY_ELEMENTS)

  'rule' Process_Recursive_Elements(list(theory_decl(
				   const_decl(
			             expl_fun_const(IdOp,
					       Recursive,
                                               Params,
                                               TypeExpr,
                                               Expr, Pre))),
                        TheoryElementsTail)):
	 Out_Function_Axiom(expl_fun_const(
                                IdOp,
				Recursive,
                                Params,
                                TypeExpr,
                                Expr,
                                Pre
                            )
                           )
	 WritelnFile(2)
         Process_Recursive_Elements(TheoryElementsTail)

  'rule' Process_Recursive_Elements(list(theory_decl(
			    const_decl(
			      impl_fun_const(
                                IdOp,
                                Params,
                                TypeExpr,
                                postcond(
                                  Bindings,
                                  PostExpr
                                ),
                                Pre
                              )
                            )
                          ),
                        TheoryElementsTail)):
	 Out_Function_Axiom(impl_fun_const(
                                IdOp,
                                Params,
                                TypeExpr,
                                postcond(
                                  Bindings,
                                  PostExpr
                                ),
                                Pre
                            )
                           )
	 WritelnFile(2)
         Process_Recursive_Elements(TheoryElementsTail)

  'rule' Process_Recursive_Elements(list(TheoryElement,
                                         TheoryElementsTail)):
	 Process_Theory_Element(TheoryElement)
         Process_Recursive_Elements(TheoryElementsTail)

  'rule' Process_Recursive_Elements(nil):


--------------------------------------------------
'action' Out_Fun_Signatures(THEORY_ELEMENTS)

  'rule' Out_Fun_Signatures(list(theory_decl(
				   const_decl(
			             expl_fun_const(IdOp,
					       Recursive,
                                               Params,
                                               TypeExpr,
                                               Expr, Pre))),
                        TheoryElementsTail)):
	 Out_IdOp(IdOp)
	 WriteFile(": ")
	 Out_Type_Expr(TypeExpr)
	 WritelnFile(2)
	 Out_Fun_Signatures(TheoryElementsTail)

  'rule' Out_Fun_Signatures(list(theory_decl(const_decl(
			impl_fun_const(IdOp, Params,
                                  TypeExpr, Expr, Pre))),
                        TheoryElementsTail)):
	 Out_IdOp(IdOp)
	 WriteFile(": ")
	 Out_Type_Expr(TypeExpr)
	 WritelnFile(2)
	 Out_Fun_Signatures(TheoryElementsTail)

  'rule' Out_Fun_Signatures(nil):


-- not used
--------------------------------------------------
'action' Out_Fun_Axioms(THEORY_ELEMENTS)

  'rule' Out_Fun_Axioms(list(
                          theory_decl(
			    const_decl(
			      expl_fun_const(
                                IdOp,
				Recursive,
                                Params,
                                TypeExpr,
                                Expr,
                                Pre
                              )
                            )
                          ),
                        TheoryElementsTail)):
	 Out_Function_Axiom(expl_fun_const(
                                IdOp,
				Recursive,
                                Params,
                                TypeExpr,
                                Expr,
                                Pre
                            )
                           )
	 WritelnFile(2)
	 Out_Fun_Axioms(TheoryElementsTail)

  'rule' Out_Fun_Axioms(list(
                          theory_decl(
			    const_decl(
			      impl_fun_const(
                                IdOp,
                                Params,
                                TypeExpr,
                                postcond(
                                  Bindings,
                                  PostExpr
                                ),
                                Pre
                              )
                            )
                          ),
                        TheoryElementsTail)):
	 Out_Function_Axiom(impl_fun_const(
                                IdOp,
                                Params,
                                TypeExpr,
                                postcond(
                                  Bindings,
                                  PostExpr
                                ),
                                Pre
                            )
                           )
	 WritelnFile(2)
	 Out_Fun_Axioms(TheoryElementsTail)

  'rule' Out_Fun_Axioms(list(TheoryElement, TheoryElementsTail)):

  'rule' Out_Fun_Axioms(nil):


--------------------------------------------------
'action' Process_DataType(IDENT, DATA_TYPE_PARTS)

  'rule' Process_DataType(Id, DataTypeParts):
	 WriteIndntFile(2)
	 C_id_to_string(Id -> IdString)
	 WriteFile(IdString)
	 WriteFile(": DATATYPE")
	 WritelnFile(1)
	 WriteIndntFile(2)
	 WriteFile("BEGIN")
	 WritelnFile(1)
	 Out_DataTypeParts(DataTypeParts)
	 WritelnFile(1)
	 WriteIndntFile(2)
	 WriteFile("END ")
	 WriteFile(IdString)
	 WritelnFile(2)


--------------------------------------------------
'action' Out_DataTypeParts(DATA_TYPE_PARTS)

  'rule' Out_DataTypeParts(list(DataTypePart, DataTypeParts)):
	 WriteIndntFile(4)
	 Out_DataTypePart(DataTypePart)
	 [|
	   ne(DataTypeParts, nil)
	   WritelnFile(1)
	 |]
	 Out_DataTypeParts(DataTypeParts)

  'rule' Out_DataTypeParts(nil):


--------------------------------------------------
'action' Out_DataTypePart(DATA_TYPE_PART)

  'rule' Out_DataTypePart(part(construct(
				IdOp, Accesors),
			  IdOpConst, _)):
	 Out_IdOp(IdOp)
	 [|
	   ne(Accesors, nil)
	   WriteFile("(")
	   Out_Accesors(Accesors)
	   WriteFile(")")
	 |]
	 WriteFile(": ")
	 Out_IdOp(IdOp)
	 WriteFile("?")


--------------------------------------------------
'action' Out_Accesors(ACCESORS)

  'rule' Out_Accesors(list(Accesor, Accesors)):
	 Out_Accesor(Accesor)
	 [|
	   ne(Accesors, nil)
	   WriteFile(", ")
	 |]
	 Out_Accesors(Accesors)

  'rule' Out_Accesors(nil):


--------------------------------------------------
'action' Out_Accesor(ACCESOR)

  'rule' Out_Accesor(accesor(IdOps, TypeExpr)):
	 Out_IdOps(IdOps)
	 WriteFile(": ")
	 Out_Type_Expr(TypeExpr)


--------------------------------------------------
'action' Out_Type_Expr(PVS_TYPE_EXPR)

  'rule' Out_Type_Expr(bool):
	 WriteFile("bool")

  'rule' Out_Type_Expr(int):
	 WriteFile("int")

  'rule' Out_Type_Expr(nat):
	 WriteFile("nat")

  'rule' Out_Type_Expr(real):
	 WriteFile("real")

  'rule' Out_Type_Expr(text):
	 WriteFile("list[char]")

  'rule' Out_Type_Expr(char):
	 WriteFile("char")

  'rule' Out_Type_Expr(defined(Ident, TypeExpr, NameQualif)):
	 Out_NameQualif(NameQualif)
	 Out_Ident(Ident)

  'rule' Out_Type_Expr(named_type(IdOp, NameQualif)):
	 Out_NameQualif(NameQualif)
	 Out_IdOp(IdOp)

  'rule' Out_Type_Expr(fun_type(IdOp, Domain, Result)):
	 WriteFile("FUNCTION ")
	 WriteFile("[")
	 Out_Type_Expr(Domain)
	 WriteFile(" -> ")
	 Out_Type_Expr(Result)
	 WriteFile("]")

  'rule' Out_Type_Expr(tuple_type(list(Tuple, nil))):
	 Out_Tuple_List(list(Tuple, nil))

  'rule' Out_Type_Expr(tuple_type(TupleList)):
	 WriteFile("[")
	 Out_Tuple_List(TupleList)
	 WriteFile("]")

  'rule' Out_Type_Expr(record_type(FieldDecls)):
	 WriteFile("record_type")

  'rule' Out_Type_Expr(finite_map(Dom, Rng)):
	 WriteFile("finite_map[")
	 Out_Type_Expr(Dom)
	 WriteFile(", ")
	 Out_Type_Expr(Rng)
	 WriteFile("]")

  'rule' Out_Type_Expr(infinite_map(Dom, Rng)):
	 WriteFile("map[")
	 Out_Type_Expr(Dom)
	 WriteFile(", ")
	 Out_Type_Expr(Rng)
	 WriteFile("]")

  'rule' Out_Type_Expr(finite_set(TypeExpr)):
	 WriteFile("finite_set[")
	 Out_Type_Expr(TypeExpr)
	 WriteFile("]")

  'rule' Out_Type_Expr(infinite_set(TypeExpr)):
	 WriteFile("set[")
	 Out_Type_Expr(TypeExpr)
	 WriteFile("]")

  'rule' Out_Type_Expr(bracket_type(TypeExpr)):
	 Out_Type_Expr(TypeExpr)

  'rule' Out_Type_Expr(list_type(TypeExpr)):
	 WriteFile("list[")
	 Out_Type_Expr(TypeExpr)
	 WriteFile("]")

  'rule' Out_Type_Expr(subtype(SetBinding, RestrictionExpr)):
	 WriteFile("{")
	 Out_Subtype(SetBinding, RestrictionExpr)
	 WriteFile("}")

  'rule' Out_Type_Expr(union_type):
	 WriteFile("union_type")

  'rule' Out_Type_Expr(undefined_type):
	 WriteFile("undefined type")

  'rule' Out_Type_Expr(uninterpreted_type):
	 WriteFile("uninterpreted type")

  'rule' Out_Type_Expr(not_supported):
	 WriteFile("not supported")

  'rule' Out_Type_Expr(any):
	 WriteFile("any")

  'rule' Out_Type_Expr(none):
	 WriteFile("none")

  'rule' Out_Type_Expr(poly):
	 WriteFile("poly")

  'rule' Out_Type_Expr(nil):
	 WriteFile("nil")


--------------------------------------------------
'action' Out_Subtype(SETBINDING, PVS_EXPR)

  'rule' Out_Subtype(bindings(BS), Expr):
	 Out_PVSBindings(BS, nil, nil -> LBS)
	 WriteFile(" | ")
	 [|
	   ne(LBS, nil)
	   WriteFile("LET ")
	   Out_LetBindings(LBS)
	   WriteFile(" IN ")
	 |]
	 Out_PVS_Expr(Expr)



--------------------------------------------------
'action' Out_PVS_Expr(PVS_EXPR)

  'rule' Out_PVS_Expr(literal_expr(Literal)):
	 Out_PVS_Literal(Literal)

  'rule' Out_PVS_Expr(named_val(id_op(IdOp))):
	 Out_IdOp(IdOp) 

  'rule' Out_PVS_Expr(product(Exprs)):
	 WriteFile("(")
	 Out_Tuple_Expr(Exprs)
	 WriteFile(")")

  'rule' Out_PVS_Expr(ranged_set(LeftExpr, RightExpr)):
	 WriteFile("ranged_set(")
	 Out_PVS_Expr(LeftExpr)
	 WriteFile(", ")
	 Out_PVS_Expr(RightExpr)
	 WriteFile(")")

  'rule' Out_PVS_Expr(enum_set(Exprs)):
	 (|
	   ne(Exprs, nil)
	   Out_Enum_Set(Exprs)
	 ||
	   WriteFile("emptyset")
	 |)

	 -- RSL : { x | x: T :- p(x) }
         -- PVS : { x: T | p(x) }
  'rule' Out_PVS_Expr(comp_simp_set(bindings(PBS), RestExpr)):
	 WriteFile("{ ")
	 Out_PVSBindings(PBS, nil, nil -> LBS)
	 WriteFile(" | ")
	 (|
	   ne(RestExpr, nil)
	   [|
	     ne(LBS, nil)
	     WriteFile("LET ")
	     Out_LetBindings(LBS)
	     WriteFile(" IN ")
	   |]
	   Out_PVS_Expr(RestExpr)
	 ||
	   WriteFile("true")
	 |)
	 WriteFile(" }")
	 
     

	 -- RSL : { f(x) | x: T :- p(x) }, where f: T -> U
         -- PVS : { u: U | EXISTS (x: T) : u = f(x) AND p(x) }
  'rule' Out_PVS_Expr(comp_set(Expr, TypeOfExpr,
			       bindings(PBS), RestExpr)):
	 WriteFile("{yu_ : ")
	 Out_Type_Expr(TypeOfExpr)
	 WritelnFile(1)
	 WriteFile("      | EXISTS (")
	 Out_PVSBindings(PBS, nil, nil -> LBS)
	 WriteFile("): ")
	 [|
	   ne(LBS, nil)
	   WriteFile("LET ")
	   Out_LetBindings(LBS)
	   WriteFile(" IN ")
	 |]
	 WritelnFile(1)
	 WriteIndntFile(8)
	 [|
	   ne(RestExpr, nil)
	   (|
	     PVS_lower_precedence(RestExpr, 16)
	     Out_PVS_Expr(RestExpr)
	   ||
	     Out_PVS_Expr(bracket(RestExpr))
	   |)
  	   WriteFile(" AND ")
	 |]
	 WriteFile("yu_ = ")
	 (|
	   PVS_lower_precedence(Expr, 14)
	   Out_PVS_Expr(Expr)
	 ||
	   Out_PVS_Expr(bracket(Expr))
	 |)
	 WriteFile("}")

  'rule' Out_PVS_Expr(ranged_list(LeftExpr, RightExpr)):
	 WriteFile("ranged_list(")
	 Out_PVS_Expr(LeftExpr)
	 WriteFile(", ")
	 Out_PVS_Expr(RightExpr)
	 WriteFile(")")

  'rule' Out_PVS_Expr(enum_list(Exprs)):
	 (|
	   eq(Exprs, nil)
	   WriteFile("null")
	 ||
	   WriteFile("(:")
	   Out_Enum_List(Exprs)
	   WriteFile(":)")
	 |)

  'rule' Out_PVS_Expr(comp_list(Expr, limit(PVSBindings, ListExpr, RestExpr))):
	 WriteFile("map(LAMBDA (")
	 PVSBindings_to_expr(PVSBindings -> E1)
	 DefaultPos(-> P)
	 where(PVS_EXPR'infix_occ(E1, val_id(P, op_symb(function_op(isin))),
			 ListExpr) -> E2)
	 (|
	   ne(RestExpr, nil)
	   where(PVS_EXPR'ax_infix(E2, and, RestExpr) -> E3)
	 ||
	   where(E2 -> E3)
	 |)
	 Include_pre_in_bindings(PVSBindings, E3, nil -> PVSBindings1, _)
	 Out_PVSBindings(PVSBindings1, nil, nil -> LBS1)
	 WriteFile("): ")
	 [|
	   ne(LBS1, nil)
	   WriteFile("LET ")
	   Out_LetBindings(LBS1)
	   WriteFile(" IN ")
	 |]
	 Out_PVS_Expr(Expr)
	 (|
	   ne(RestExpr, nil)
	   WriteFile(", filter(")
	   Out_PVS_Expr(ListExpr)
	   WriteFile(", LAMBDA (")
	   Include_pre_in_bindings(PVSBindings, E2, nil -> PVSBindings2, _)
	   Out_PVSBindings(PVSBindings2, nil, nil -> LBS2)
	   WriteFile("): ")
	   [|
	     ne(LBS2, nil)
	     WriteFile("LET ")
	     Out_LetBindings(LBS2)
	     WriteFile(" IN ")
	   |]
	   Out_PVS_Expr(RestExpr)
	   WriteFile("))")
	 ||
	   WriteFile(", ")
	   Out_PVS_Expr(ListExpr)
	   WriteFile(")")
	 |)

  'rule' Out_PVS_Expr(enum_map(ExprPairs)):
	 (|
	   eq(ExprPairs, nil)
	   WriteFile("empty_map")
	 ||
	   Out_Enum_Map(ExprPairs)
	 |)

         -- [ x +> e(x) | x : T :- p(x) ]
	 -- LAMBDA (x:T): IF p(x) THEN mk_rng(e(x)) ELSE nil ENDIF
  'rule' Out_PVS_Expr(comp_rng_map(Expr, TypeExprDom, TypeExprRng,
						      bindings(PBS), Pred)):
	 WriteFile("LAMBDA (")
	 Out_PVSBindings(PBS, nil, nil -> LBS)
	 WriteFile("): ")
	 [|
	   ne(LBS, nil)
	   WriteFile("LET ")
	   Out_LetBindings(LBS)
	   WriteFile(" IN ")
	 |]
	 (|
	   eq(Pred, nil)
	   WriteFile("mk_rng(")
	   Out_PVS_Expr(Expr)
	   WriteFile(")")
	 ||
	   WriteFile("IF ")
	   Out_PVS_Expr(Pred)
	   WriteFile(" THEN mk_rng(")
	   Out_PVS_Expr(Expr)
	   -- nil needs coercion to avoid TCC
	   WriteFile(") ELSE nil::Maprange_adt[")
	   Out_Type_Expr(TypeExprRng)
	   WriteFile("].Maprange ENDIF") 
	 |) 
	 

         -- [ e1(x) +> e2(x) | x : T :- p(x) ]
	 -- where e1(x) has type T1
	 -- LAMBDA (x1:T1):
	 -- LET x = RSL_inverse(LAMBDA (x:T): e1(x))(x1) IN
	 -- IF p(x) THEN mk_rng(e2(x)) ELSE nil ENDIF
  'rule' Out_PVS_Expr(comp_map(pair(Expr1, Expr2), TypeExprDom, TypeExprRng,
						   bindings(PBS), Pred)):
	 WriteFile("LAMBDA (")
	 -- Generate new Product identifier and add 1 to ProdIndex
	 Gen_Prod_Ident("lb_" -> LambdaB)
	 Out_Ident(LambdaB) 
	 WriteFile(" : ")
	 Out_Type_Expr(TypeExprDom)
	 WriteFile("):")
	 WritelnFile(1)
	 WriteFile("LET (")
	 Out_PVSBindings(PBS, nil, nil -> LBS)
	 WriteFile(") = RSL_inverse(LAMBDA (")
	 Out_PVSBindings(PBS, nil, nil -> LBS1)
	 WriteFile("): ")
	 [|
	   ne(LBS1, nil)
	   WriteFile("LET ")
	   Out_LetBindings(LBS1)
	   WriteFile(" IN ")
	 |]
	 Out_PVS_Expr(Expr1)
	 WriteFile(")(")
	 Out_Ident(LambdaB)
	 WriteFile(") IN")
	 WritelnFile(1)
	 [|
	   ne(LBS, nil)
	   WriteFile("LET ")
	   Out_LetBindings(LBS)
	   WriteFile(" IN ")
	 |]
	 (|
	   eq(Pred, nil)
	   WriteFile("mk_rng(")
	   Out_PVS_Expr(Expr2)
	   WriteFile(")")
	 ||
	   WriteFile("IF ")
	   Out_PVS_Expr(Pred)
	   WriteFile(" THEN mk_rng(")
	   Out_PVS_Expr(Expr2)
	   -- nil needs coercion to avoid TCC
	   WriteFile(") ELSE nil::Maprange_adt[")
	   Out_Type_Expr(TypeExprRng)
	   WriteFile("].Maprange ENDIF")
	 |) 

  'rule' Out_PVS_Expr(function(LambdaBindings, Expr)):
	 WriteFile("LAMBDA (")
	 Out_LambdaBindings(LambdaBindings, nil -> LBS)
	 WriteFile("): ")
	 WritelnFile(1)
	 [|
	   ne(LBS, nil)
	   WriteFile("    LET ")
	   Out_LetBindings(LBS)
	   WriteFile(" IN")
	   WritelnFile(1)
	 |]
	 Out_PVS_Expr(Expr)
	 WritelnFile(1)

  'rule' Out_PVS_Expr(list_applic(ListExpr, Arguments)):
	 WriteFile("nth(")
	 Out_PVS_Expr(ListExpr)
	 where(Arguments -> argument(P, list(E, nil)))
	 string_to_id("1" -> One)
	 where(argument(P, list(PVS_EXPR'infix_occ(E,
			      val_id(P, op_symb(infix_op(minus))),
			      literal_expr(int(One))), nil)) -> Arguments1)
	 WriteFile(", ")
	 -- Generate new Product identifier and add 1 to ProdIndex
	 Gen_Prod_Ident("" -> IdProd)
	 Out_Arguments(Arguments1, IdProd)
	 WriteFile(")")

  'rule' Out_PVS_Expr(map_applic(MapExpr, Arguments)):
	 WriteFile("rng_part")
	 WriteFile("(")
	 (|
	   PVS_lower_precedence(MapExpr, 1)
	   Out_PVS_Expr(MapExpr)
	 ||
	   Out_PVS_Expr(bracket(MapExpr))
	 |)
	 -- Generate new Product identifier and add 1 to ProdIndex
	 Gen_Prod_Ident("" -> IdProd)
	 Out_Arguments(Arguments, IdProd)
	 WriteFile(")")

  'rule' Out_PVS_Expr(funct_applic(FunExpr, Arguments)):
	 (|
	   PVS_lower_precedence(FunExpr, 1)
	   Out_PVS_Expr(FunExpr)
	 ||
	   Out_PVS_Expr(bracket(FunExpr))
	 |)
	 -- Generate new Product identifier and add 1 to ProdIndex
	 Gen_Prod_Ident("" -> IdProd)
	 Out_Arguments(Arguments, IdProd)

  'rule' Out_PVS_Expr(quantified(exists1, bindings(PBS), Expr)):
	 WriteFile("exists1(LAMBDA (")
	 Out_PVSBindings(PBS, nil, nil -> LBS)
	 WriteFile("): ")
	 [|
	   ne(LBS, nil)
	   WriteFile("LET ")
	   Out_LetBindings(LBS)
	   WriteFile(" IN ")
	 |]
	 Out_PVS_Expr(Expr)
	 WriteFile(")")
	 WritelnFile(1)

  'rule' Out_PVS_Expr(quantified(BindingOp, bindings(PBS), Expr)):
	 Out_BindingOp(BindingOp)
	 WriteFile("(")
	 Out_PVSBindings(PBS, nil, nil -> LBS)
	 WriteFile("): ")
	 [|
	   ne(LBS, nil)
	   WriteFile("LET ")
	   Out_LetBindings(LBS)
	   WriteFile(" IN ")
	 |]
	 Out_PVS_Expr(Expr)
	 WritelnFile(1)

  'rule' Out_PVS_Expr(equivalence(LeftExpr, RightExpr, PreExpr)):
	 [|
	   ne(PreExpr, nil)
	   (|
	     PVS_lower_precedence(PreExpr, 18)
	     Out_PVS_Expr(PreExpr)
	   ||
	     Out_PVS_Expr(bracket(PreExpr))
	   |)
	   WriteFile(" IMPLIES ")
	 |]
	 (|
	   PVS_lower_precedence(LeftExpr, 14)
	   Out_PVS_Expr(LeftExpr)
	 ||
	   Out_PVS_Expr(bracket(LeftExpr))
	 |)
	 WriteFile(" = ")
	 (|
	   PVS_lower_precedence(RightExpr, 14)
	   Out_PVS_Expr(RightExpr)
	 ||
	   Out_PVS_Expr(bracket(RightExpr))
	 |)
	 WritelnFile(1)

  'rule' Out_PVS_Expr(post(Expr, TypeExpr, PostCond, PreExpr)):
	 -- RSL (where e1 has type T)
	 -- e1 as id
	 -- post e2(id)
	 -- pre e3
	 -- PVS
	 -- e3
	 -- IMPLIES
	 --   LET id = e1 IN e2(id)

	 where(PostCond -> postcond(Bindings, PostExpr))
	 [| -- Exists a precondition ?
	   ne(PreExpr, nil)
	   (|
	     PVS_lower_precedence(PreExpr, 18)
	     Out_PVS_Expr(PreExpr)
	   ||
	     Out_PVS_Expr(bracket(PreExpr))
	   |)
	   WriteFile(" IMPLIES ")
	 |]
	 [| -- bindings??
	   ne(Bindings, nil)
	   WriteFile("LET (")
	   Out_PVSBindings(Bindings, nil, nil -> LBS)  -- id
	   WriteFile(") = ")
	   Out_PVS_Expr(Expr)  -- e1
	   [|
	     ne(LBS, nil)
	     WriteFile(", ")
	     Out_LetBindings(LBS)
	   |]
	   WriteFile(" IN ")
	 |]
	 Out_PVS_Expr(PostExpr)  -- e2

  'rule' Out_PVS_Expr(disamb(Expr, TypeExpr)):
	 Out_PVS_Expr(Expr)
	 (| -- only disambiguate once
	   where(Expr -> disamb(_,_))
	 ||
	   WriteFile(" :: ")
	   Out_Type_Expr(TypeExpr)
	 |)

  'rule' Out_PVS_Expr(bracket(Expr)):
	 WriteFile("(")
	 Out_PVS_Expr(Expr)
	 WriteFile(")")

  'rule' Out_PVS_Expr(ax_infix(LeftExpr, Connective, RightExpr)): 
	 PVS_connective_precedence(Connective -> P)
	 (|
	   PVS_lower_precedence(LeftExpr, P)
	   Out_PVS_Expr(LeftExpr)
	 ||
	   Out_PVS_Expr(bracket(LeftExpr))
	 |)
	 Out_PVS_Connective(Connective)
	 (|
	   PVS_lower_precedence(RightExpr, P)
	   Out_PVS_Expr(RightExpr)
	 ||
	   Out_PVS_Expr(bracket(RightExpr))
	 |)

-- special code for isin_map
  'rule' Out_PVS_Expr(funct_expr(val_id(Pos, IdOp), nil, Expr1, Expr2)):
	 where(IdOp -> op_symb(function_op(isin_map)))
	 WriteFile(" nonnil?(")
	 Out_PVS_Expr(Expr2)
	 WriteFile("(")
	 Out_PVS_Expr(Expr1)
	 WriteFile("))")

-- special code for notisin_map
  'rule' Out_PVS_Expr(funct_expr(val_id(Pos, IdOp), nil, Expr1, Expr2)):
	 where(IdOp -> op_symb(function_op(notisin_map)))
	 WriteFile(" nil?(")
	 Out_PVS_Expr(Expr2)
	 WriteFile("(")
	 Out_PVS_Expr(Expr1)
	 WriteFile("))")

-- special code for override(e1, e2) where e2 is a singleton maplet
  'rule' Out_PVS_Expr(funct_expr(val_id(Pos, IdOp), nil, Expr1, Expr2)):
	 where(IdOp -> op_symb(function_op(override)))
	 where(Expr2 -> enum_map(list(pair(D,R),nil)))
	 WriteFile(" add_in_map(")
	 Out_PVS_Expr(D)
	 WriteFile(", ")
	 Out_PVS_Expr(R)
	 WriteFile(", ")
	 Out_PVS_Expr(Expr1)
	 WriteFile(")")

  'rule' Out_PVS_Expr(funct_expr(val_id(Pos, IdOp), NameQualif, Expr1, Expr2)):
	 Out_NameQualif(NameQualif)
	 Out_IdOp(IdOp)
	 WriteFile("(")
	 Out_PVS_Expr(Expr1)
	 [|
	   ne(Expr2, nil)
	   WriteFile(", ")
	   Out_PVS_Expr(Expr2)
	 |]
	 WriteFile(")")

  'rule' Out_PVS_Expr(ax_prefix(Connective, Expr)): 
	 Out_PVS_Connective(Connective)
	 (|
	   PVS_lower_precedence(Expr, 15)
	   Out_PVS_Expr(Expr)
	 ||
	   Out_PVS_Expr(bracket(Expr))
	 |)

  'rule' Out_PVS_Expr(let_expr(nil, Expr)):
	 Out_PVS_Expr(Expr)

  'rule' Out_PVS_Expr(let_expr(LetBindings, Expr)):
	 WriteFile("LET ")
	 Out_LetBindings(LetBindings)
	 WritelnFile(1)
	 WriteFile(" IN")
	 WritelnFile(1)
	 WriteFile("  ")
	 Out_PVS_Expr(Expr)
	 WritelnFile(1)

  'rule' Out_PVS_Expr(if_expr(Expr, ThenExpr, Elsifs, Else)):
	 [| -- if with no else not supported
	   ne(Else, nil)
	   WriteFile("IF ")
	   Out_PVS_Expr(Expr)
	   WritelnFile(1)
	   WriteFile("THEN ")
	   Out_PVS_Expr(ThenExpr)
	   [|
	     ne(Elsifs, nil)
	     Out_Elsifs(Elsifs)
	   |]
	   where(Else -> else(ElseExpr))
	   WritelnFile(1)
	   WriteFile("ELSE ")
	   Out_PVS_Expr(ElseExpr)
	   WritelnFile(1)
	   WriteFile("ENDIF")
	 |]

 
  'rule' Out_PVS_Expr(val_occ(val_id(Pos, IdOp), NameQualif)):
	 Out_NameQualif(NameQualif)
	 Out_IdOp(IdOp) 

-- deal with "= empty" specially
  'rule' Out_PVS_Expr(infix_occ(LeftExpr, val_id(Pos, op_symb(infix_op(eq))),
					  RightExpr)):
	 (|
	   Is_empty_pvs_set_or_map(RightExpr)
	   WriteFile("empty?(")
	   Out_PVS_Expr(LeftExpr)
	   WriteFile(")")
	 ||
	   Is_empty_pvs_list(RightExpr)
	   WriteFile("null?(")
	   Out_PVS_Expr(LeftExpr)
	   WriteFile(")")
	 ||
	   Is_empty_pvs_set_or_map(LeftExpr)
	   WriteFile("empty?(")
	   Out_PVS_Expr(RightExpr)
	   WriteFile(")")
	 ||
	   Is_empty_pvs_list(LeftExpr)
	   WriteFile("null?(")
	   Out_PVS_Expr(RightExpr)
	   WriteFile(")")
	 |)

-- deal with "~= empty" specially
  'rule' Out_PVS_Expr(infix_occ(LeftExpr, val_id(Pos, op_symb(infix_op(neq))), 
					  RightExpr)):
	 (|
	   Is_empty_pvs_set_or_map(RightExpr)
	   WriteFile("nonempty?(")
	   Out_PVS_Expr(LeftExpr)
	   WriteFile(")")
	 ||
	   Is_empty_pvs_list(RightExpr)
	   WriteFile("cons?(")
	   Out_PVS_Expr(LeftExpr)
	   WriteFile(")")
	 ||
	   Is_empty_pvs_set_or_map(LeftExpr)
	   WriteFile("nonempty?(")
	   Out_PVS_Expr(RightExpr)
	   WriteFile(")")
	 ||
	   Is_empty_pvs_list(LeftExpr)
	   WriteFile("cons?(")
	   Out_PVS_Expr(RightExpr)
	   WriteFile(")")
	 |)

-- otherwise translate e1 ~= e2 as NOT (e1 = e2)
-- as latter simplifies better in PVS
  'rule' Out_PVS_Expr(infix_occ(LeftExpr, val_id(Pos, op_symb(infix_op(neq))), 
					  RightExpr)):
	 WriteFile("NOT (")
	 Out_PVS_Expr(LeftExpr)
	 WriteFile(" = ")
	 Out_PVS_Expr(RightExpr)
	 WriteFile(")")

-- user defined operators? TODO
  'rule' Out_PVS_Expr(infix_occ(LeftExpr, val_id(Pos, IdOp), 
			        RightExpr)):
	 (| -- operator symbol
	   where(IdOp -> op_symb(Op))
	   (| -- infix_op
	     where(Op -> infix_op(Oper))
	     PVS_infix_precedence(Oper -> P)
	     (|
	       PVS_lower_precedence(LeftExpr, P)
	       Out_PVS_Expr(LeftExpr)
	     ||
	       Out_PVS_Expr(bracket(LeftExpr))
	     |)
	     Out_IdOp(IdOp) 
	     (|
	       PVS_lower_precedence(RightExpr, P)
	       Out_PVS_Expr(RightExpr)
	     ||
	       Out_PVS_Expr(bracket(RightExpr))
	     |)
	   || -- prefix_op
	     where(Op -> prefix_op(_))
	     print("internal ERR (gen_code) - prefix_op in an infix_occ")
	   || -- function_op
	     where(Op -> function_op(Oper))
	     Out_IdOp(IdOp) 
	     WriteFile("(")
	     Out_PVS_Expr(LeftExpr)
	     [|
	       ne(RightExpr, nil)
	       WriteFile(", ")
	       Out_PVS_Expr(RightExpr)
	     |]
	     WriteFile(")")
	   |)
	 || -- 
	   print("internal ERR (gen_code) - non operator in infix position")
	 |)

  'rule' Out_PVS_Expr(prefix_occ(val_id(Pos, IdOp), 
		                 Expr)):
	 (| -- operator symbol
	   where(IdOp -> op_symb(Op))
	   (| -- prefix_op
	     where(Op -> prefix_op(Op1))
	     Out_IdOp(IdOp) 
	     (|
	       PVS_lower_precedence(Expr, 14)
	       Out_PVS_Expr(Expr)
	     ||
	       Out_PVS_Expr(bracket(Expr))
	     |)
	   || -- infix_op
	     where(Op -> infix_op(Op2))
	     (|
	       eq(Op2, minus)
	       Out_IdOp(IdOp) 
	       (|
		 PVS_lower_precedence(Expr, 9)
		 Out_PVS_Expr(Expr)
	       ||
		 Out_PVS_Expr(bracket(Expr))
	       |)
	     ||
	       print("internal ERR (gen_code):")
	       print("  infix_op in a prefix_occ")
	     |)
	   || -- function_op
	     where(Op -> function_op(_))
	     Out_IdOp(IdOp) 
	     WriteFile("(")
	     Out_PVS_Expr(Expr)
	     WriteFile(")")
	   |)
	 ||
	   Out_IdOp(IdOp) 
	   Out_PVS_Expr(bracket(Expr))
	 |)

	 -- @@ not supported
  'rule' Out_PVS_Expr(env_local(
--			 decls	:	DECLS,
--			 env	:	CLASS_ENV,
			 Expr)):
--	 WriteFile("env_local ")

  'rule' Out_PVS_Expr(no_val):
	 WriteFile("no_val ")

	 -- not supported
  'rule' Out_PVS_Expr(no_def):

  'rule' Out_PVS_Expr(not_supported):

  'rule' Out_PVS_Expr(nil):


--------------------------------------------------
'action' Out_Elsifs(PVS_ELSIF_BRANCHES)

  'rule' Out_Elsifs(list(Elsif, ElsifsTail)):
	 Out_Elsif(Elsif)
	 Out_Elsifs(ElsifsTail)

  'rule' Out_Elsifs(nil):


--------------------------------------------------
'action' Out_Elsif(PVS_ELSIF_BRANCH)

  'rule' Out_Elsif(elsif(IfExpr, ThenExpr)):
	 WritelnFile(1)
	 WriteFile("ELSIF ")
	 Out_PVS_Expr(IfExpr)
	 WritelnFile(1)
	 WriteFile("THEN ")
	 Out_PVS_Expr(ThenExpr)

--------------------------------------------------
'condition' Is_empty_pvs_set_or_map(PVS_EXPR)

  'rule' Is_empty_pvs_set_or_map(enum_set(nil)):

  'rule' Is_empty_pvs_set_or_map(enum_map(nil)):

  'rule' Is_empty_pvs_set_or_map(bracket(E)):
	 Is_empty_pvs_set_or_map(E)

  'rule' Is_empty_pvs_set_or_map(disamb(E, _)):
	 Is_empty_pvs_set_or_map(E)

'condition' Is_empty_pvs_list(PVS_EXPR)

  'rule' Is_empty_pvs_list(enum_list(nil)):

  'rule' Is_empty_pvs_list(bracket(E)):
	 Is_empty_pvs_list(E)

  'rule' Is_empty_pvs_list(disamb(E, _)):
	 Is_empty_pvs_list(E)




--------------------------------------------------
'action' Gen_TheoryElems(THEORY_ELEMENTS)

  'rule' Gen_TheoryElems(list(TheoryElem, TheoryElemsTail)):
	 Gen_TheoryElem(TheoryElem)
	 Gen_TheoryElems(TheoryElemsTail)

  'rule' Gen_TheoryElems(nil):


--------------------------------------------------
'action' Gen_TheoryElem(THEORY_ELEMENT)

  'rule' Gen_TheoryElem(importing(Importing)):
	 Putmsg("Internal error (gen_code): importing in value expresion")
	 Putnl()

  'rule' Gen_TheoryElem(theory_decl(TheoryDecl)):
	 Gen_TheoryDecl(TheoryDecl)

  'rule' Gen_TheoryElem(nil):


--------------------------------------------------
'action' Gen_TheoryDecl(THEORY_DECL)

  'rule' Gen_TheoryDecl(type_decl(_, _, _, _, _)):
	 print("type_decl in value expresion")

  'rule' Gen_TheoryDecl(var_decl(_, _)):
	 print("var_decl in value expresion")

  'rule' Gen_TheoryDecl(const_decl(ConstantDecl)):
	 Gen_ConstantDecl(ConstantDecl)

  'rule' Gen_TheoryDecl(formula_decl(_, _, _)):
	 print("formula_decl in value expresion")

  'rule' Gen_TheoryDecl(nil):
	 print("TheoryDecl, nil in value expresion")


--------------------------------------------------
'action' Gen_ConstantDecl(CONSTANT_DECL)

  'rule' Gen_ConstantDecl(nodef(IdOps, TypeExpr, Expr)):
	 Out_IdOps(IdOps)

  'rule' Gen_ConstantDecl(expl_const(IdOps, TypeExpr, Expr)):
	 Out_IdOps(IdOps)

  'rule' Gen_ConstantDecl(impl_const(IdOps, TypeExpr, Expr)):
	 Out_IdOps(IdOps)

  'rule' Gen_ConstantDecl(expl_fun_const(IdOp, _, _, _, _, _)):
	 Out_IdOp(IdOp)

  'rule' Gen_ConstantDecl(impl_fun_const(IdOp, _, _, _, _)):
	 Out_IdOp(IdOp)


--------------------------------------------------
'action' Out_Enum_Set(PVS_EXPRS)

  'rule' Out_Enum_Set(list(Expr, ExprsTail)):
	 WriteFile("add(")
	 Out_PVS_Expr(Expr)
	 (|
	   eq(ExprsTail, nil)
	   WriteFile(", emptyset")
	 ||
	   WriteFile(", ")
	 |)
	 Out_Enum_Set(ExprsTail)
	 WriteFile(")")

  'rule' Out_Enum_Set(nil):

--------------------------------------------------
'action' Out_Enum_List(PVS_EXPRS)

  'rule' Out_Enum_List(list(Expr, ExprsTail)):
	 Out_PVS_Expr(Expr)
	 [|
	   ne(ExprsTail, nil)
	   WriteFile(", ")
	 |]
	 Out_Enum_List(ExprsTail)

  'rule' Out_Enum_List(nil):

--------------------------------------------------
'action' Out_Enum_Map(PVS_EXPR_PAIRS)

  'rule' Out_Enum_Map(list(pair(LeftExpr, RightExpr), ExprPairsTail)):
	 WriteFile("add_in_map(")
	 Out_PVS_Expr(LeftExpr)
	 WriteFile(", ")
	 Out_PVS_Expr(RightExpr)
	 (|
	   eq(ExprPairsTail, nil)
	   WriteFile(", empty_map")
	 ||
	   WriteFile(", ")
	 |)
	 Out_Enum_Map(ExprPairsTail)
	 WriteFile(")")

  'rule' Out_Enum_Map(nil):


--------------------------------------------------
'action' Out_PVS_Literal(PVS_VALUE_LITERAL)

  'rule' Out_PVS_Literal(bool_true):
	 WriteFile("true")

  'rule' Out_PVS_Literal(bool_false):
	 WriteFile("false")

  'rule' Out_PVS_Literal(int(IdentInt)):
	 id_to_string(IdentInt -> StringInt)
	 WriteFile(StringInt)
	 -- disambiguate from real
	 WriteFile("::int")

  'rule' Out_PVS_Literal(real(IdentReal)): 
	 Out_Real(IdentReal)

  'rule' Out_PVS_Literal(text(String)): 
	 WriteFile(String)

  'rule' Out_PVS_Literal(char(Char)):
	 Char_to_int(Char -> CharInt)
	 Int_to_string(CharInt -> StringChar)
	 WriteFile("char(")
	 WriteFile(StringChar)
	 WriteFile(")")

  'rule' Out_PVS_Literal(nil):


--------------------------------------------------
'action' Out_Real(IDENT)

  'rule' Out_Real(IdentReal):
	 Convert_Real(IdentReal -> Base, Divisor)
	 Int_to_string(Base -> BaseStrng)
	 (|
	   eq(Divisor, 1)
	   WriteFile(BaseStrng)
	 ||
	   WriteFile("(")
	   WriteFile(BaseStrng)
	   WriteFile(" / ")
	   Int_to_string(Divisor -> DivisorStrng)
	   WriteFile(DivisorStrng)
	   WriteFile(")")
	 |)


--------------------------------------------------
'action' Out_PVS_Connective(PVS_CONNECTIVE)

  'rule' Out_PVS_Connective(implies):
	 WriteFile(" IMPLIES")
	 WritelnFile(1)
 
  'rule' Out_PVS_Connective(or):
	 WriteFile(" OR")
	 WritelnFile(1)
 
  'rule' Out_PVS_Connective(and):
	 WriteFile(" AND")
	 WritelnFile(1)
 
  'rule' Out_PVS_Connective(not):
	 WriteFile(" NOT ")


--------------------------------------------------
'action' Out_BindingOp(BINDING_OP)
 
  'rule' Out_BindingOp(lambda):
	 WriteFile(" LAMBDA ")
 
  'rule' Out_BindingOp(forall):
	 WriteFile(" FORALL ")
 
  'rule' Out_BindingOp(exists):
	 WriteFile(" EXISTS ")
 
  'rule' Out_BindingOp(exists1):
	 WriteFile(" exists1")
 
  'rule' Out_BindingOp(nil):
	 Putmsg("PVS Internal Error (gen_code): BindingOp nil")
	 Putnl()


--------------------------------------------------
'action' Out_Tuple_Expr(PVS_EXPRS)

  'rule' Out_Tuple_Expr(list(PVSExpr, PVSExprsTail)):
	 Out_PVS_Expr(PVSExpr)
	 [|
	   ne(PVSExprsTail, nil)
	   WriteFile(", ")
	 |]
	 Out_Tuple_Expr(PVSExprsTail)

  'rule' Out_Tuple_Expr(nil):


--------------------------------------------------
'action' Out_IdOps(ID_OP_S)

  'rule' Out_IdOps(list(IdOp, IdOpsTail)):
	 Out_IdOp(IdOp)
	 [|
	   ne(IdOpsTail, nil)
	   WriteFile(", ")
	 |]
	 Out_IdOps(IdOpsTail)

  'rule' Out_IdOps(nil):


--------------------------------------------------
'action' Out_IdOp(ID_OP)

  'rule' Out_IdOp(id(Ident)):
	 Out_Ident(Ident)

  'rule' Out_IdOp(op_symb(Op)):
	 Out_Op(Op)

'action' Out_IdOp_alpha(ID_OP)

  'rule' Out_IdOp_alpha(id(Ident)):
	 Out_Ident(Ident)

  'rule' Out_IdOp_alpha(op_symb(Op)):
	 Out_Op_alpha(Op)

--------------------------------------------------
'action' Out_Projections(PROJECTION_LIST)

  'rule' Out_Projections(list(Projection, ProjectionsTail)):
	 WriteFile("`")
	 Int_to_string(Projection -> ProjectionString)
	 WriteFile(ProjectionString)
	 Out_Projections(ProjectionsTail)

  'rule' Out_Projections(nil):
 

--------------------------------------------------
'action' Out_Idents(IDENTS)

  'rule' Out_Idents(list(Ident, IdentsTail)):
	 Out_Ident(Ident)
	 Out_Idents(IdentsTail)

  'rule' Out_Idents(nil):


--------------------------------------------------
'action' Out_Ident(IDENT)

  'rule' Out_Ident(Ident):
	 C_id_to_string(Ident -> IdentString)
	 WriteFile(IdentString)


--------------------------------------------------
'action' Out_Tuple_List(TUPLE_LIST)

  'rule' Out_Tuple_List(list(tuple(IdOp, TypeExpr), TupleListTail)):
	 [|
	   ne(IdOp, nil)
	   Out_IdOp(IdOp)
	   WriteFile(":")
	 |]
	 Out_Type_Expr(TypeExpr)
	 [|
	   ne(TupleListTail, nil)
	   WriteFile(", ")
	 |]
	 Out_Tuple_List(TupleListTail)

  'rule' Out_Tuple_List(nil):


--------------------------------------------------
'action' Out_Op(PVS_OP)

  -- Infix Operators
  'rule' Out_Op(infix_op(eq)):
	 WriteFile(" = ")
  'rule' Out_Op(infix_op(neq)):
	 WriteFile(" /= ")
  'rule' Out_Op(infix_op(gt)):
	 WriteFile(" > ")
  'rule' Out_Op(infix_op(lt)):
	 WriteFile(" < ")
  'rule' Out_Op(infix_op(ge)):
	 WriteFile(" >= ")
  'rule' Out_Op(infix_op(le)):
	 WriteFile(" <= ")
  'rule' Out_Op(infix_op(mult)):
	 WriteFile(" * ")
  'rule' Out_Op(infix_op(div)):
	 WriteFile(" / ")
  'rule' Out_Op(infix_op(plus)):
	 WriteFile(" + ")
  'rule' Out_Op(infix_op(minus)):
	 WriteFile(" - ")

  -- Functions operators
  'rule' Out_Op(function_op(supset)):
	 WriteFile(" strict_supset?")
  'rule' Out_Op(function_op(subset)):
	 WriteFile(" strict_subset?")
  'rule' Out_Op(function_op(supseteq)):
	 WriteFile(" supset?")
  'rule' Out_Op(function_op(subseteq)):
	 WriteFile(" subset?")
  'rule' Out_Op(function_op(isin)):
	 WriteFile(" member")
  'rule' Out_Op(function_op(notisin)):
 	 WriteFile(" NOT member")
  'rule' Out_Op(function_op(isin_map)):
	 WriteFile(" member")
  'rule' Out_Op(function_op(notisin_map)):
 	 WriteFile(" NOT member")
  'rule' Out_Op(function_op(rem)):
 	 WriteFile(" rsl_int_rem")
  'rule' Out_Op(function_op(difference)):
 	 WriteFile(" difference")
  'rule' Out_Op(function_op(restriction_by)):
 	 WriteFile(" restriction_by")
  'rule' Out_Op(function_op(int_div)):
	 WriteFile(" rsl_int_div")
  'rule' Out_Op(function_op(restriction_to)):
	 WriteFile(" restriction_to")
  'rule' Out_Op(function_op(union)):
	 WriteFile(" union")
  'rule' Out_Op(function_op(override)):
	 WriteFile(" override")
  'rule' Out_Op(function_op(add_in_map)):
	 WriteFile(" add_in_map")
  'rule' Out_Op(function_op(hash)):
	 WriteFile(" o")
  'rule' Out_Op(function_op(inter)):
	 WriteFile(" intersection")
  'rule' Out_Op(function_op(exp)):
	 WriteFile(" expt")
  'rule' Out_Op(function_op(abs)):
	 WriteFile(" abs")
  'rule' Out_Op(function_op(card)):
	 WriteFile(" card")
  'rule' Out_Op(function_op(len)):
	 WriteFile(" length")
  'rule' Out_Op(function_op(inds)):
	 WriteFile(" inds")
  'rule' Out_Op(function_op(elems)):
	 WriteFile(" list2set")
  'rule' Out_Op(function_op(hd)):
	 WriteFile(" car")
  'rule' Out_Op(function_op(hd_set)):
	 WriteFile(" choose_set")
  'rule' Out_Op(function_op(hd_map)):
	 WriteFile(" choose_map")
  'rule' Out_Op(function_op(tl)):
	 WriteFile(" cdr")
  'rule' Out_Op(function_op(append)):
	 WriteFile(" append")
  'rule' Out_Op(function_op(dom)):
	 WriteFile(" dom")
  'rule' Out_Op(function_op(rng)):
	 WriteFile(" rng")

  'rule' Out_Op(identity):

  'rule' Out_Op(not_supported):
	 WriteFile("Operator not supported")

'action' Out_Op_alpha(PVS_OP)

  -- Infix Operators
  'rule' Out_Op_alpha(infix_op(eq)):
	 WriteFile("eq")
  'rule' Out_Op_alpha(infix_op(neq)):
	 WriteFile("neq")
  'rule' Out_Op_alpha(infix_op(gt)):
	 WriteFile("gt")
  'rule' Out_Op_alpha(infix_op(lt)):
	 WriteFile("lt")
  'rule' Out_Op_alpha(infix_op(ge)):
	 WriteFile("ge")
  'rule' Out_Op_alpha(infix_op(le)):
	 WriteFile("le")
  'rule' Out_Op_alpha(infix_op(mult)):
	 WriteFile("mult")
  'rule' Out_Op_alpha(infix_op(div)):
	 WriteFile("div")
  'rule' Out_Op_alpha(infix_op(plus)):
	 WriteFile("plus")
  'rule' Out_Op_alpha(infix_op(minus)):
	 WriteFile("minus")

  -- Functions operators
  'rule' Out_Op_alpha(function_op(supset)):
	 WriteFile("strict_supset")
  'rule' Out_Op_alpha(function_op(subset)):
	 WriteFile("strict_subset")
  'rule' Out_Op_alpha(function_op(supseteq)):
	 WriteFile("supset")
  'rule' Out_Op_alpha(function_op(subseteq)):
	 WriteFile("subset")
  'rule' Out_Op_alpha(function_op(isin)):
	 WriteFile("member")
  'rule' Out_Op_alpha(function_op(notisin)):
 	 WriteFile("not_member")
  'rule' Out_Op_alpha(function_op(isin_map)):
	 WriteFile("member")
  'rule' Out_Op_alpha(function_op(notisin_map)):
 	 WriteFile("not_member")
  'rule' Out_Op_alpha(function_op(rem)):
 	 WriteFile("rem")
  'rule' Out_Op_alpha(function_op(difference)):
 	 WriteFile("difference")
  'rule' Out_Op_alpha(function_op(restriction_by)):
 	 WriteFile("restriction_by")
  'rule' Out_Op_alpha(function_op(int_div)):
	 WriteFile("int_div")
  'rule' Out_Op_alpha(function_op(restriction_to)):
	 WriteFile("restriction_to")
  'rule' Out_Op_alpha(function_op(union)):
	 WriteFile("union")
  'rule' Out_Op_alpha(function_op(override)):
	 WriteFile("override")
  'rule' Out_Op_alpha(function_op(add_in_map)):
	 WriteFile("add_in_map")
  'rule' Out_Op_alpha(function_op(hash)):
	 WriteFile("hash")
  'rule' Out_Op_alpha(function_op(inter)):
	 WriteFile("intersection")
  'rule' Out_Op_alpha(function_op(exp)):
	 WriteFile("exp")
  'rule' Out_Op_alpha(function_op(abs)):
	 WriteFile("abs")
  'rule' Out_Op_alpha(function_op(card)):
	 WriteFile("card")
  'rule' Out_Op_alpha(function_op(len)):
	 WriteFile("len")
  'rule' Out_Op_alpha(function_op(inds)):
	 WriteFile("inds")
  'rule' Out_Op_alpha(function_op(elems)):
	 WriteFile("elems")
  'rule' Out_Op_alpha(function_op(hd)):
	 WriteFile("hd")
  'rule' Out_Op_alpha(function_op(hd_set)):
	 WriteFile("choose_set")
  'rule' Out_Op_alpha(function_op(hd_map)):
	 WriteFile("choose_map")
  'rule' Out_Op_alpha(function_op(tl)):
	 WriteFile("tl")
  'rule' Out_Op_alpha(function_op(append)):
	 WriteFile("conc")
  'rule' Out_Op_alpha(function_op(dom)):
	 WriteFile("dom")
  'rule' Out_Op_alpha(function_op(rng)):
	 WriteFile("rng")

  'rule' Out_Op_alpha(identity):
	 WriteFile("convert")		-- used for int and real

  'rule' Out_Op_alpha(not_supported):
	 WriteFile("Operator_not_supported")

   

--------------------------------------------------
'action' Out_NameQualif(NAME_QUALIF)

  'rule' Out_NameQualif(qualif(IdAt, IdOp, Actuals)):
	 Out_IdOp(IdOp)
	 WriteFile(".")

  'rule' Out_NameQualif(nil):
 

--------------------------------------------------
--------------------------------------------------
-- Out Bindings, Setbindings, Arguments,
-- LetBindings, LambdaBindings
--------------------------------------------------
--------------------------------------------------

--------------------------------------------------
'action' Out_Arguments_List(ARGUMENTS_LIST, IDENT)

  'rule' Out_Arguments_List(list(Arguments, ArgumentsListTail), IdProd):
	 Out_Arguments(Arguments, IdProd)
	 Out_Arguments_List(ArgumentsListTail, IdProd)

  'rule' Out_Arguments_List(nil, IdProd):
	

--------------------------------------------------
'action' Out_Arguments(ARGUMENTS, IDENT)

  'rule' Out_Arguments(argument(Pos, Exprs), IdProd):
	 WriteFile("(")
	 Out_Tuple_Expr(Exprs)
	 WriteFile(")")

--------------------------------------------------
'action' Out_Arguments_from_Params(PVS_FORMAL_FUN_PARAMETERS)

  'rule' Out_Arguments_from_Params(list(Bindings, ParamsTail)):
	 WriteFile("(")
	 Out_Argument_from_Param(Bindings)
	 WriteFile(")")
	 Out_Arguments_from_Params(ParamsTail)

  'rule' Out_Arguments_from_Params(nil):

'action' Out_Argument_from_Param(PVS_BINDINGS)

  'rule' Out_Argument_from_Param(list(B, BS)):
	 Out_Arg(B)
	 [|
	   ne(BS, nil)
	   WriteFile(", ")
	   Out_Argument_from_Param(BS)
	 |]

'action' Out_Arg(PVS_BINDING)

  'rule' Out_Arg(typed_id(IdOp, _)):
	 Out_IdOp(IdOp)

  'rule' Out_Arg(prod_binding(BS)):
	 WriteFile("(")
	 Out_Argument_from_Param(BS)
	 WriteFile(")")

  'rule' Out_Arg(typed_prod(BS, _)):
	 Out_Arg(prod_binding(BS))

--------------------------------------------------
'action' Include_pre_in_bindings(PVS_BINDINGS, PVS_EXPR, LETBINDINGS ->
					       PVS_BINDINGS, PVS_TYPE_EXPR)

  'rule' Include_pre_in_bindings(list(B, nil), Pre, LBS -> list(B1, nil), DOM)
	 -- last binding: change type to subtype based on Pre
	 -- assumed comes from function definition, so must be typed
	 (|
	   eq(LBS, nil)
	   where(Pre -> Cond)
	 ||
	   where(PVS_EXPR'let_expr(LBS, Pre) -> Cond)
	 |)
	 (|
	   where(B -> typed_id(IdOp, T))
	   where(PVS_TYPE_EXPR'subtype(bindings(list(B, nil)), Cond) -> DOM)
	   where(typed_id(IdOp, DOM) -> B1)
	 ||
	   where(B -> typed_prod(BS, T))
	   where(PVS_TYPE_EXPR'subtype(bindings(list(B, nil)), Cond) -> DOM)
	   where(typed_prod(BS, DOM) -> B1)
	 |)
	 

  'rule' Include_pre_in_bindings(list(B, BS), Pre, LBS -> list(B, BS1), DOM):
	 PVSBinding_to_type(B, LBS -> Id, T, LBS1)
	 Include_pre_in_bindings(BS, Pre, LBS1 -> BS1, TS)
	 (|
	   where(TS -> tuple_type(TL))
	   where(tuple_type(list(tuple(id(Id), T), TL)) -> DOM)
	 ||
	   where(tuple_type(list(tuple(id(Id), T), list(tuple(nil, TS), nil))) -> DOM)
	 |)

--------------------------------------------------
'action' Add_ids_to_domain(PVS_BINDINGS, LETBINDINGS ->
					 PVS_TYPE_EXPR, LETBINDINGS)

-- assumes bindings are typed
  'rule' Add_ids_to_domain(list(B, nil), LBS ->
				tuple_type(list(tuple(id(Id), T), nil)), LBS1):
	 PVSBinding_to_type(B, LBS -> Id, T, LBS1)

  'rule' Add_ids_to_domain(list(B, BS), LBS ->
				tuple_type(list(tuple(id(Id), T), TL)), LBS2):
	 PVSBinding_to_type(B, LBS -> Id, T, LBS1)
	 Add_ids_to_domain(BS, LBS1 -> tuple_type(TL), LBS2)

--------------------------------------------------
'action' Out_PVSBindings(PVS_BINDINGS, LETBINDINGS, PVS_TYPE_EXPR -> LETBINDINGS)

  'rule' Out_PVSBindings(BS:list(_,list(_,_)), LBS, tuple_type(list(tuple(id(Id), T), nil)) -> LBS1):
	 -- product parameter has been made into single one because of
	 -- curried function with precondition
	 Out_PVSBinding(typed_prod(BS, T), LBS, tuple(id(Id), T) -> LBS1)

  'rule' Out_PVSBindings(list(B, BS), LBS, T -> LBS1):
	 (|
	   where(T -> tuple_type(list(TT, TTS)))
	 ||
	   where(TUPLE'nil -> TT)
	   where(TUPLE_LIST'nil -> TTS)
	 |)
	 Out_PVSBinding(B, LBS, TT -> LBS2)
	 (|
	   ne(BS, nil)
	   WriteFile(", ")
	   Out_PVSBindings(BS, LBS2, tuple_type(TTS) -> LBS1)
	 ||
	   where(LBS2 -> LBS1)
	 |)

  'rule' Out_PVSBindings(nil, LBS, _ -> LBS):

'action' Out_PVSBinding(PVS_BINDING, LETBINDINGS, TUPLE -> LETBINDINGS)

  'rule' Out_PVSBinding(typed_id(IdOp, T), LBS, _ -> LBS):
	 Out_IdOp(IdOp)
	 [|
	   ne(T, nil)
	   WriteFile(": ")
	   Out_Type_Expr(T)
         |]

  'rule' Out_PVSBinding(typed_prod(BS, T), LBS, TT -> LBS1):
	 (|
	   where(TT -> tuple(id(IdProd), _))
	 ||
	   Gen_Prod_Ident("" -> IdProd)
	 |)
	 id_to_string(IdProd -> IdProdStrng)
	 WriteFile(IdProdStrng)
	 WriteFile(": ")
	 Out_Type_Expr(T)
	 Gen_LetBindings(IdProd, BS, LBS -> LBS1)

  'rule' Out_PVSBinding(prod_binding(BS), LBS, _ -> LBS1):
	 Gen_Prod_Ident("" -> IdProd)
	 id_to_string(IdProd -> IdProdStrng)
	 WriteFile(IdProdStrng)
	 Gen_LetBindings(IdProd, BS, LBS -> LBS1)

--------------------------------------------------
'action' PVSBinding_to_type(PVS_BINDING, LETBINDINGS ->
					 IDENT, PVS_TYPE_EXPR, LETBINDINGS)
-- assumes all bindings are typed

  'rule' PVSBinding_to_type(typed_prod(BS, T), LBS -> IdProd, T, LBS1):
	 Gen_Prod_Ident("" -> IdProd)
	 Gen_LetBindings(IdProd, BS, LBS -> LBS1)
	 

  'rule' PVSBinding_to_type(typed_id(id(Id), T), LBS -> Id, T, LBS):

--------------------------------------------------
'action' Gen_LetBindings(IDENT, PVS_BINDINGS, LETBINDINGS -> LETBINDINGS)

  'rule' Gen_LetBindings(Id, BS, LBS ->
	   list(let_binds(LetBinds, named_val(id_op(id(Id)))), LBS2)):
	 Bindings_to_Letbinds(BS, LBS -> LetBinds, LBS2)
	 
'action' Bindings_to_Letbinds(PVS_BINDINGS, LETBINDINGS -> LETBINDS, LETBINDINGS)
	 
  'rule' Bindings_to_Letbinds(list(typed_id(IdOp,_), BS), LBS 
                          -> list(let_idop(IdOp,nil,nil), LetBinds), LBS1):
         Bindings_to_Letbinds(BS, LBS -> LetBinds, LBS1)

  'rule' Bindings_to_Letbinds(list(prod_binding(BS1), BS), LBS 
                          -> list(let_idop(id(IdProd),nil,nil), LetBinds), LBS1):
	 Gen_Prod_Ident("" -> IdProd)
	 Gen_LetBindings(IdProd, BS1, LBS -> LBS2)
	 Bindings_to_Letbinds(BS, LBS2 -> LetBinds, LBS1)

  'rule' Bindings_to_Letbinds(list(typed_prod(BS1, _), BS), LBS 
                          -> list(let_idop(id(IdProd),nil,nil), LetBinds), LBS1):
	 Gen_Prod_Ident("" -> IdProd)
	 Gen_LetBindings(IdProd, BS1, LBS -> LBS2)
	 Bindings_to_Letbinds(BS, LBS2 -> LetBinds, LBS1)

  'rule' Bindings_to_Letbinds(nil, LBS -> nil, LBS):

--------------------------------------------------
'action' Out_LetBindings(LETBINDINGS)

  'rule' Out_LetBindings(list(LetBinding, LetBindingsTail)):
	 Out_LetBinding(LetBinding)
	 [|
	   ne(LetBindingsTail, nil)
	   WriteFile(", ")
	 |]
	 Out_LetBindings(LetBindingsTail)

  'rule' Out_LetBindings(nil):


--------------------------------------------------
'action' Out_LetBinding(LETBINDING)

  'rule' Out_LetBinding(let_bind(LetBind, Expr)):
 	 Out_LetBind(LetBind)
	 (|
	   where(Expr -> disamb(ExprDis, TypeExpr))
	 ||
	   where(Expr -> ExprDis)
	   where(PVS_TYPE_EXPR'nil -> TypeExpr)
	 |)
	 [|
	   ne(TypeExpr, nil)
	   WriteFile(" : ")
 	   Out_Type_Expr(TypeExpr)
	 |]
	 WriteFile(" = ")
 	 Out_PVS_Expr(ExprDis)

  'rule' Out_LetBinding(let_binds(LetBinds, Expr)):
 	 WriteFile("(")
	 Out_LetBinds(LetBinds)
 	 WriteFile(") = ")	 
 	 Out_PVS_Expr(Expr)

  'rule' Out_LetBinding(nil):


--------------------------------------------------
'action' Out_LetBinds(LETBINDS)

  'rule' Out_LetBinds(list(LetBind, LetBindsTail)):
	 Out_LetBind(LetBind)
	 [|
	   ne(LetBindsTail, nil)
	   WriteFile(", ")
	 |]
	 Out_LetBinds(LetBindsTail)

  'rule' Out_LetBinds(nil):


--------------------------------------------------
'action' Out_LetBind(LETBIND)

  'rule' Out_LetBind(let_idop(IdOp, nil, nil)):
	 Out_IdOp(IdOp)

-------------------------------------------------
'action' Out_LambdaBindings(LAMBDABINDINGS, LETBINDINGS -> LETBINDINGS)

  'rule' Out_LambdaBindings(list(bindings(BS), LmbdBndngsTail), LBS -> LBS2):
	 Out_PVSBindings(BS, LBS, nil -> LBS1)
	 (|
	   ne(LmbdBndngsTail, nil)
	   WriteFile(", ")
	   Out_LambdaBindings(LmbdBndngsTail, LBS1 -> LBS2)
	 ||
	   where(LBS1 -> LBS2)
	 |)

  'rule' Out_LambdaBindings(nil, LBS -> LBS)
	 



--------------------------------------------------
'action' Out_Params(PVS_FORMAL_FUN_PARAMETERS,
                         PVS_TYPE_EXPR, LETBINDINGS ->
			 LETBINDINGS, PVS_TYPE_EXPR)

  'rule' Out_Params(list(Bindings, ParamsTail),
                         fun_type(_, Domain, Result),
                         Letbindings -> Letbindingsout, Resultout):
	 WriteFile("(")
	 Out_PVSBindings(Bindings, Letbindings, Domain -> Letbindings1)
	 WriteFile(")")
	 Out_Params(ParamsTail, Result, Letbindings1 ->
				     Letbindingsout, Resultout)
	
  'rule' Out_Params(L, bracket_type(T), LB -> LB1, T1):
	 Out_Params(L, T, LB -> LB1, T1)

  'rule' Out_Params(nil, TypeExpr, Letbindings ->
			      Letbindings, TypeExpr):

--------------------------------------------------
'action' Include_pre_in_params(PVS_FORMAL_FUN_PARAMETERS, 
			       PVS_TYPE_EXPR,  PVS_EXPR, LETBINDINGS ->
			PVS_FORMAL_FUN_PARAMETERS, PVS_TYPE_EXPR)

  'rule' Include_pre_in_params(BS, T, nil, _ -> BS, T):

  'rule' Include_pre_in_params(BS, bracket_type(T), E, LB -> BS1, T1):
	 Include_pre_in_params(BS, T, E, LB -> BS1, T1)

  'rule' Include_pre_in_params(list(BS, nil),
			       fun_type(Id, _, Result), Pre, LBS ->
				  list(BS1, nil), fun_type(Id, Domain, Result)):
	 -- last one: change type to subtype based on pre
	 Include_pre_in_bindings(BS, Pre, LBS -> BS1, Domain)

  'rule' Include_pre_in_params(list(BS, ParamsTail),
			       fun_type(Id, _, Result), Pre, LBS ->
	          list(BS, ParamsTail1), fun_type(Id, Domain, Result1))
	 Add_ids_to_domain(BS, LBS -> Domain, LBS1)
	 Include_pre_in_params(ParamsTail, Result, Pre, LBS1 ->
						   ParamsTail1, Result1)

'action' Include_pre_in_param_type(PVS_FORMAL_FUN_PARAMETERS, 
			       PVS_TYPE_EXPR,  PVS_EXPR, LETBINDINGS ->
			PVS_FORMAL_FUN_PARAMETERS, PVS_TYPE_EXPR)

-- last or single parameter: treat as normal
  'rule' Include_pre_in_param_type(list(BS, nil), T, Pre, LBS -> BS1, T1):
	 Include_pre_in_params(list(BS, nil), T, Pre, LBS -> BS1, T1)

-- for curried function where the type is needed, 
-- parameters apart from the last must be single, not tuples
  'rule' Include_pre_in_param_type(list(list(B, nil), ParamsTail),
			       fun_type(Id, _, Result), Pre, LBS ->
	          list(list(B, nil), ParamsTail1), fun_type(Id, Domain, Result1)):
	 Add_ids_to_domain(list(B, nil), LBS -> Domain, LBS1)
	 Include_pre_in_param_type(ParamsTail, Result, Pre, LBS1 ->
						   ParamsTail1, Result1)

  'rule' Include_pre_in_param_type(list(BS, ParamsTail),
			       fun_type(Id, Domain, Result), Pre, LBS ->
	          list(BS, ParamsTail1), fun_type(Id, Domain1, Result1)):
	 Gen_Prod_Ident("" -> IdProd)
	 Gen_LetBindings(IdProd, BS, LBS -> LBS1)
	 where(tuple_type(list(tuple(id(IdProd), Domain), nil)) -> Domain1)
	 where(typed_id(id(IdProd), Domain) -> B)
	 Include_pre_in_param_type(ParamsTail, Result, Pre, LBS1 ->
						   ParamsTail1, Result1)


--------------------------------------------------
--  Auxiliary Actions
---------------------------------------------------

--------------------------------------------------
--  Generate Axiom Name
---------------------------------------------------
--------------------------------------------------
'action' Gen_Axiom_Name(STRING -> STRING)
	 
  'rule' Gen_Axiom_Name(IdStrng -> AxiomStrng):
	 AxiomIndex -> AxiomIndex1
	 AxiomIndex <- AxiomIndex1 + 1
	 Int_to_string(AxiomIndex1 -> AxiomIndxStrng)
	 Concatenate(IdStrng, AxiomIndxStrng -> AxiomStrng)

-------------------------------------------------

'action' CcLemmaName(ID_OR_OP -> STRING)

  'rule' CcLemmaName(Id -> S)
	 (|
	   where(Id -> id_op(Ident))
	   C_id_to_string(Ident -> S1)
	 ||
	   where(Id -> op_op(Op))
	   Op_to_alpha_string(Op -> S1)
	 |)
	 LemmaIndex -> LemmaIndex1
	 LemmaIndex <- LemmaIndex1 + 1
	 Int_to_string(LemmaIndex1 -> LemmaIndxStrng)
	 Concatenate3(S1, "_cc", LemmaIndxStrng -> S)

'action' JudgementName(ID_OR_OP -> STRING)

  'rule' JudgementName(Id -> S)
	 (|
	   where(Id -> id_op(Ident))
	   C_id_to_string(Ident -> S1)
	 ||
	   where(Id -> op_op(Op))
	   Op_to_alpha_string(Op -> S1)
	 |)
	 JudgementIndex -> JudgementIndex1
	 JudgementIndex <- JudgementIndex1 + 1
	 Int_to_string(JudgementIndex1 -> JudgementIndxStrng)
	 Concatenate3(S1, "_judgement", JudgementIndxStrng -> S)



--------------------------------------------------
--  Generate Product Identifier
---------------------------------------------------
--------------------------------------------------
'action' Gen_Prod_Ident(STRING -> IDENT)
	 
  'rule' Gen_Prod_Ident(IdStrng -> IdProd):
	 (|
	   eq(IdStrng, "")
	   where("prod" -> IdStrng1)
	 ||
	   where(IdStrng -> IdStrng1)
	 |)
	 ProdIndex -> ProdIndex1
	 ProdIndex <- ProdIndex1 + 1
	 ProdIndex -> ProdIndex2
	 Int_to_string(ProdIndex2 -> ProdIndxStrng)
	 Concatenate3(IdStrng1, ProdIndxStrng, "_" -> ProdIdStrng)
	 string_to_id(ProdIdStrng -> IdProd)
	 Add_1_to_ProdIndex2

--------------------------------------------------
'action' Substract_1_to_ProdIndex
	 
  'rule' Substract_1_to_ProdIndex
	 ProdIndex -> ProdIndex2
	 ProdIndex <- ProdIndex2 - 1


--------------------------------------------------
'action' Add_1_to_ProdIndex2
	 
  'rule' Add_1_to_ProdIndex2
	 ProdIndex2 -> ProdIndex1
	 ProdIndex2 <- ProdIndex1 + 1


--------------------------------------------------
'action' ProdIndex_min_ProdIndex2
	 
  'rule' ProdIndex_min_ProdIndex2
	 ProdIndex -> PI
	 ProdIndex2 -> PI2
	 ProdIndex <- PI - PI2
	 ProdIndex -> PI3


