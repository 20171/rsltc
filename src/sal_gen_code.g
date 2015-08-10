-- RSL Type Checker
-- Copyright (C) 1998 - 2005 UNU/IIST

-- raise@iist.unu.edu

-- This module generates the SAL code 
-- from the SAL abstract syntax tree

 
'module' sal_gen_code

'use' ast print 
      ext -- DefaultPos
      env objects values types pp cc 
      sal_global_vars
      sal_aux
      sal_ast
      sal_gen_ast        -- Sharing arument handling...
      sal_gen_code_types -- SAL_Out_Type_Decl
      sal_gen_code_aux
      sal_gen_code_bindings
      sal_print
      
'export' 
         SAL_Out_Model
SAL_Out_Arguments
SAL_Out_Tuple_Expr

         SAL_Gen_Code 
         SAL_Init_Var_Gen_Code 
         SAL_Init_Indexes

         SAL_Out_Expr
         --Gen_Prod_Ident CcLemmaName JudgementName

         -- REMOVE (should not be exported)
         Gen_SAL_Context
         Gen_SAL_End
         -- Remove from here!
         SAL_Out_Expr
         SAL_Out_Accesors
         SAL_Out_Accesor        -- used in sal_gen_code_aux
         SAL_Gen_Prod_Ident

         SAL_Catenate_Namespaces         

--------------------------------------------------
--  Variables
--------------------------------------------------

--------------------------------------------------
-- Used to generate different Product Identifiers
'var' SAL_ProdIndex     :       INT
'var' SAL_ProdIndex2    :       INT


--------------------------------------------------
-- Used to generate different Axiom Identifiers
--'var' AxiomIndex      :     INT


--------------------------------------------------
-- Used to generate different Lemma Identifiers
--'var' LemmaIndex              :       INT


--------------------------------------------------
-- Used to generate different Judgement Identifiers
--'var' JudgementIndex          :       INT


--------------------------------------------------
-- Used to store the current Binding environment





--------------------------------------------------
--  Actions
--------------------------------------------------

'action' SAL_Init_Var_Gen_Code

  'rule' SAL_Init_Var_Gen_Code:
         -- Product Index Identifier stars w/0
         SAL_ProdIndex <- 0
         -- Product Index Identifier (2) stars w/0
         SAL_ProdIndex2 <- 0
         -- Init the binding env:
         Current_LBS_Env <- nil

'action' SAL_Init_Indexes

  'rule' SAL_Init_Indexes:
         -- Indexes start from 0
--       AxiomIndex <- 0
--       LemmaIndex <- 0
--       JudgementIndex <- 0

-------------------------------------------------------------------------------
-- SAL_Out_Model
-------------------------------------------------------------------------------
-- Generates the SAL code from SAL's AST
-- In particular, it just keep the control over the context list in
-- the model, invoking the proper routine for outputting the context's contents.
-------------------------------------------------------------------------------

'action' SAL_Out_Model(SAL_MODEL)

  'rule' SAL_Out_Model(model(ModelElems)):
         SAL_Init_Var_Gen_Code
         SAL_Out_Model_Elems(ModelElems)


'action' SAL_Out_Model_Elems(SAL_CONTEXTS)

  'rule' SAL_Out_Model_Elems(list(Context, ContextList)):
         where(Context -> context(Ident, OptCid, Context_Constants))
         (|
            (|
                -- Don't generate the context if all the elements
                -- inside the spec file have already been moved to
                -- some other contexts...
                eq(Context_Constants,nil)
            ||
                OpenSALFile(Ident -> F)  -- in files.c
                where(OptCid -> cid(Cid))
                -- Putmsg("Generating ")
                -- Print_id(Ident)
                -- Putmsg(".sal ...\n")
                SAL_Current_Cid <- Cid
                Gen_SAL_Context(Ident, Cid)
                SAL_Gen_Code(Context_Constants)
                Gen_SAL_End
                CloseOutputFile
                Putmsg("Generated ")
                Print_id(Ident)
                Putmsg(".sal\n")
            |)

         ||
            print("Internal error! Unknown context...")
            Print_id(Ident)
         |)
         -- Process the rest:
         SAL_Out_Model_Elems(ContextList)

  'rule' SAL_Out_Model_Elems(list(Context, ContextList)):
         where(Context -> macro_context(Ident, OptCid, MacroConstants))
         OpenM4File(Ident -> F)  -- in files.c
         where(OptCid -> cid(Cid))
         -- Putmsg("Generating ")
         -- Print_id(Ident)
         -- Putmsg(".m4 ... ")
         -- Necessary for qualification...
         SAL_Current_Cid <- Cid
         Gen_SAL_Macro_Code(Ident, MacroConstants)
         CloseOutputFile
         Putmsg("Generated ")
         Print_id(Ident)
         Putmsg(".m4\n")
         -- Process the rest:
         SAL_Out_Model_Elems(ContextList)

  'rule' SAL_Out_Model_Elems(nil):


-------------------------------------------------------------------------------

'action' Gen_SAL_Context(IDENT, SAL_context_id)

  'rule' Gen_SAL_Context(Id, Cid):
         id_to_string(Id -> S)  -- in idents.c
         WriteFFile("%s", S)
         Cid'Args -> ArgList
         [|
            ne(ArgList,nil)
            WriteFile("{;")
            SAL_Out_Context_Param_Decl(ArgList)
            WriteFile("} ")
         |]
         WriteFile(" : CONTEXT =")
         WritelnFile(1)
         WriteFile("BEGIN")
         WritelnFile(1)


'action' Gen_SAL_End

  'rule' Gen_SAL_End:
         WriteFile("END")

---------------------------------------------
'action' SAL_Out_Context_Param_Decl(SAL_CONTEXT_ARGS)

  'rule' SAL_Out_Context_Param_Decl(list(Elem,Rest))
         (|
            where(Elem -> value_arg(Vid))
            Vid'IdOp -> IdOp
            SAL_Out_IdOp(IdOp)
            WriteFile(" : ")
            Vid'Type -> T
            SAL_Out_Type_Expr(T)
         ||
            where(Elem -> type_arg(Tid))
            Tid'Ident -> Id
            SAL_Out_Ident(Id)
            WriteFile(" : ")
            Tid'TExpr -> T
            SAL_Out_Type_Expr(T)
            
         |)
         [|
            ne(Rest,nil)
            WriteFile(", ")
         |]
         SAL_Out_Context_Param_Decl(Rest)

  'rule' SAL_Out_Context_Param_Decl(nil)
-- debug
'action' PrintArgList(SAL_TYPE_IDS)

  'rule' PrintArgList(list(H,T))
         H'Ident -> Id
         H'Args -> Args
         Print_id(Id)
         PrintArgList(T)

  'rule' PrintArgList(nil)

-------------------------------------------------------------------------------
'action' SAL_Gen_Code(SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Gen_Code(ContextElems):
         SAL_Process_Context_Elems(ContextElems)

--------------------------------------------------
'action' SAL_Process_Context_Elems(SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Process_Context_Elems(list(ContextElem, ContextElemsTail)):
         SAL_Process_Context_Elem(ContextElem)
         SAL_Process_Context_Elems(ContextElemsTail)

         -- no more ContextElems
  'rule' SAL_Process_Context_Elems(nil):


--------------------------------------------------
'action' SAL_Process_Context_Elem(SAL_CONTEXT_CONSTANT)

  'rule' SAL_Process_Context_Elem(sal_type_decl(Ident,Tid,Args)):
         SAL_Process_Type_Decl(Ident, Args)

  'rule' SAL_Process_Context_Elem(sal_const_decl(Const_decl)):
         SAL_Process_Const_Elem_Decl(Const_decl)
-- resume 0--
--  'rule' SAL_Process_Context_Elem(rec_decl(ContextElems)):--sal_assertion_decl
  'rule' SAL_Process_Context_Elem(sal_object_decl(Id,Pos,Oid,DataPart,Methd)):
         -- Doing nothing so far...

  'rule' SAL_Process_Context_Elem(module_decl(Ident, Ts_id, Input, Local, Init, Transition))
         SAL_Out_Ident(Ident)
         WriteFile(": MODULE = \n")
         WriteFile("BEGIN\n")
         [|
            ne(Input,nil)
            WriteIndntFile(2)
            WriteFile("INPUT\n")
            SAL_Out_Variables(Input)
	    WriteFile("\n")
         |]
         [|
            ne(Local,nil)
            WriteIndntFile(2)
            WriteFile("LOCAL\n")
            SAL_Out_Variables(Local)
	    WriteFile("\n")
         |]
         [|
            ne(Init,nil)
            WriteIndntFile(2)
            WriteFile("INITIALIZATION\n")
            SAL_Out_Initialization(Init)
         |]
         WriteIndntFile(2)
	 [|
	    ne(Transition, nil)
	    WriteFile("TRANSITION\n")
	    WriteIndntFile(2)
	    WriteFile("[\n")
	    SAL_Out_Transitions(Transition)
	    WriteIndntFile(2)
	    WriteFile("]\n")
	 |]
	 WriteFile("END;\n")


  'rule' SAL_Process_Context_Elem(assertion_decl(Pos,Ident, TS_Id, Prop))
         SAL_Out_Ident(Ident)
         WriteFile(" : THEOREM ")
         TS_Id'Ident -> TSIdent
         SAL_Out_Ident(TSIdent)
         WriteFile(" |- ")
         SAL_Out_Expr(Prop)
         WriteFile(";\n")

  'rule' SAL_Process_Context_Elem(S)
         Putmsg("Debugging predicate activated in SAL_Process_Context_Elem\n")
         print(S)

--------------------------------------------------
'action' SAL_Process_Type_Decl(IDENT,SAL_TYPE_EXPR)

  'rule' SAL_Process_Type_Decl(Ident,TypeExpr):
         WriteIndntFile(2)
         SAL_Out_Ident(Ident)
         WriteFile(": TYPE = ")
         SAL_Out_Type_Expr(TypeExpr)    
--WriteFile("Typedec") -- TODO: Delete
         WriteFile(";")
         WritelnFile(2)

--------------------------------------------------

'action' SAL_Process_Const_Elem_Decl(SAL_CONSTANT_DECL)

         -- RSL Commented Typing
  'rule' SAL_Process_Const_Elem_Decl(sal_nodef(IdOps, TypeExpr, Containing)):
         WriteIndntFile(2)
         SAL_Out_IdOps(IdOps)
         WriteFile(" : ")
         SAL_Out_Type_Expr(TypeExpr)
         WriteFile(";")
         WritelnFile(2)

         -- RSL Explicit Value Declaration
  'rule' SAL_Process_Const_Elem_Decl(sal_expl_const(IdOps, 
                                        Vid,TypeExpr, Containing)):
         -- only single typing, single binding allowed in RSL
         WriteIndntFile(2)
         SAL_Out_IdOps(IdOps)
         WriteFile(" : ")
         SAL_Out_Type_Expr(TypeExpr)
         WriteFile(" = ")
         WritelnFile(1)
         WriteIndntFile(4)
         SAL_Out_Expr(Containing)
         WriteFile(";")
         WritelnFile(2)


   -- TYPE BOUNDARIES... only used in SAL_GLOBAL:
  'rule' SAL_Process_Const_Elem_Decl(sal_param_decl(Decls, Tid)):
         Tid'Ident -> TypeName
         WriteFile("% Boundaries for ")
         SAL_Out_Ident(TypeName)
         WriteFile(" type:")
         WritelnFile(1)
         SAL_Out_Boundaries(Decls)

         -- Explicit function signature (from mutual recursion)
         -- (also used for implicit)
  'rule' SAL_Process_Const_Elem_Decl(
           sal_fun_const(IdOp, Vid,_, Params, ResultType, Namespace, nil, PreExpr)):
         WriteIndntFile(2)
         SAL_Out_IdOp(IdOp)
         WriteFile(" : ")
         (|
           eq(PreExpr, nil)
           SAL_Out_Type_Expr(ResultType)
         ||
           -- This is the PVS approach... not valid in SAL...
           -- SAL_Include_pre_in_param_type(Params, TypeExpr, PreExpr, nil ->  Params1, TypeExpr1)
           -- SAL_Out_Type_Elem(TypeExpr1)
           
           -- Temporary solution: (valid only when preconditions are
           --  not tested) (ignoring the precondition!)
           SAL_Out_Type_Expr(ResultType)
         |)
         WriteFile(";")
         WritelnFile(2)


	 -- PRECONDITIONS!!
	 -- RSL
	 -- f : T1 -~-> T2
	 -- f(x) is e(x)
	 -- pre e1(x)
	 -- PVS
	 -- f(x : {x:T1 | e1(x)}) : T2 = e(x)
  'rule' SAL_Process_Const_Elem_Decl(
              sal_fun_const(IdOp, Vid,Recursive, Params, ResultType, Namespace, Expr, _)):
         eq(Recursive, nil)  -- not recursive
         WriteIndntFile(2)
         SAL_Out_IdOp(IdOp)

         WriteFile("(")
         SAL_Out_Params(Params)
         WriteFile(")")
         WriteFile(": ")
         SAL_Out_Type_Expr(ResultType)
         WriteFile(" = ")
         WritelnFile(1)
         [|
                ne(Namespace, nil)
                Push_Namespace(Namespace)
         |]
         WriteIndntFile(4)
         SAL_Out_Expr(Expr)
         WriteFile(";")
         WritelnFile(2)
         [|
                ne(Namespace, nil)
                Pop_Namespace()
         |]


         -- RSL Explicit Function Declaration:
         -- recursive partial function, Pre <> nil
  'rule' SAL_Process_Const_Elem_Decl(
                sal_fun_const(IdOp, Vid,Recursive, Params, ResultType,_, Expr, PreExpr)):
         -- RSL
         -- f : T1 -~-> T2
         -- f(x) is e(x)
         -- pre e1(x)
         -- PVS CAHNGE THIS
         -- f: [{x:T1 | e1(x)} -> T2]
         -- f_ax: AXIOM FORALL (x: {x:T1 | e1(x)}): f(x) = e(x)

         -- Function Signature
         WriteIndntFile(2)
         SAL_Out_IdOp(IdOp)
         WriteFile(" : ")
         -- Same here... ignoring preconditions (for the moment only)
--       SAL_Include_pre_in_param_type(Params, TypeExpr, PreExpr, nil -> Params1, TypeExpr1)
--       SAL_Out_Type_Elem(TypeExpr1)
         -- New solution (temporary, valid for non-precond checking approach)
         SAL_Out_Type_Expr(ResultType)
         WritelnFile(1)
         -- Function Axiom
         --Out_Function_Axiom(expl_fun_const(IdOp, Recursive, Params1,TypeExpr1, Expr, nil))
         WriteFile(";")
         WritelnFile(2)


------------------------------------------------------------------
'action' SAL_Out_Boundaries(SAL_CONSTANT_DECLS)

  'rule' SAL_Out_Boundaries(list(sal_expl_const(IdOp,Vid,TElem,Containing),T)):
         WriteIndntFile(2)
         SAL_Out_IdOps(IdOp)
         WriteFile(" : ")
         SAL_Out_Type_Expr(TElem)
         WriteFile(" = ")
         SAL_Out_Expr(Containing)
         WriteFile(";")
         WritelnFile(2)
         SAL_Out_Boundaries(T)

  'rule' SAL_Out_Boundaries(nil):


------------------------------------------------------------------

/*

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
         SAL_Out_IdOp(IdOp)
         WriteFile(" function")
         WritelnFile(1)
         WriteIndntFile(2)
         SAL_Out_IdOp_alpha(IdOp)
         Gen_Axiom_Name("_axiom" -> AxiomName)
         WriteFile(AxiomName)
         WriteFile(": AXIOM FORALL ")
         SAL_Out_Params(Params, TypeExpr, nil -> LBS, Result)
         WriteFile(": ")
         WritelnFile(1)
         [|
           ne(LBS, nil)
           WriteFile("    LET ")
           SAL_Out_LetBindings(LBS)
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
             SAL_lower_precedence(PreExpr, 18)
             SAL_Out_Expr(PreExpr)
           ||
             SAL_Out_Expr(bracket(PreExpr))
           |)
           WritelnFile(1)
           WriteFile("    IMPLIES")
           WritelnFile(1)
         |]
         WriteIndntFile(6)
         SAL_Out_IdOp(IdOp)
         Out_Arguments_from_Params(Params)
         WritelnFile(1)
         WriteFile("      =")
         WritelnFile(1)
         WriteFile("      % definition")
         WritelnFile(1)
         WriteIndntFile(8)
         (|
           SAL_lower_precedence(Expr, 14)
           SAL_Out_Expr(Expr)
         ||
           SAL_Out_Expr(bracket(Expr))
         |)
         WritelnFile(1)

         -- RSL Implicit Function Declaration:
         -- total function, Pre = nil
         -- partial function, Pre <> nil
         -- same for recursive functions
  'rule' Out_Function_Axiom(impl_fun_const(IdOp, Params,
                                TypeExpr, PostCond, PreExpr))
         WriteFile("  % Axiom for ")
         SAL_Out_IdOp(IdOp)
         WriteFile(" function")
         WritelnFile(1)
         WriteIndntFile(2)
         -- out axiom name
         SAL_Out_IdOp(IdOp)  -- f
         Gen_Axiom_Name("_axiom" -> AxiomName)
         WriteFile(AxiomName)
         WriteFile(": AXIOM FORALL ")
         SAL_Out_Params(Params, TypeExpr, nil -> LBS, Result)
         WriteFile(": ")
         WritelnFile(1)
         [|
           ne(LBS, nil)
           WriteFile("    LET ")
           SAL_Out_LetBindings(LBS)
           WriteFile(" IN")
           WritelnFile(1)
         |]
         [| -- partial function
           ne(PreExpr, nil)
           WriteFile("    % precondition")
           WritelnFile(1)
           WriteIndntFile(6)
           (|
             SAL_lower_precedence(PreExpr, 18)
             SAL_Out_Expr(PreExpr)
           ||
             SAL_Out_Expr(bracket(PreExpr))
           |)
           WritelnFile(1)
           WriteFile("    IMPLIES")
           WritelnFile(1)
         |]
         where(PostCond -> postcond(Bindings, PostExpr))
         [| -- bindings??
           ne(Bindings, nil)
           WriteFile("      LET (")
           SAL_Out_Bindings(Bindings, nil, nil -> LBS1)
           WriteFile(") = ")
           SAL_Out_IdOp(IdOp)
           Out_Arguments_from_Params(Params)
           [|
             ne(LBS1, nil)
             WriteFile(", ")
             SAL_Out_LetBindings(LBS1)
           |]
           WriteFile(" IN ")
         |]
         SAL_Out_Expr(PostExpr)



--------------------------------------------------
'action' Process_Form_Decl(THEORY_DECL)

  'rule' Process_Form_Decl(formula_decl(Strng, axiom, Expr)):
         WriteIndntFile(2)
         (|
           ne(Strng, "")
           WriteFile(Strng)
         ||
           Gen_Axiom_Name("RSL_axiom" -> AxiomIdString)
           WriteFile(AxiomIdString)
         |)
         WriteFile(": AXIOM ")
         WritelnFile(1)
         WriteIndntFile(4)
         SAL_Out_Expr(Expr)
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
         SAL_Out_Expr(Expr)
         WriteFile(";")
         WritelnFile(2)

  'rule' Process_Form_Decl(formula_decl(_, nil, _)):

--------------------------------------------------


--------------------------------------------------
'action' Process_Post_Decl(THEORY_DECL)

  'rule' Process_Post_Decl(post_decl(Strng, IdOp, Params, TypeExpr, PostCond, PreExpr)):
         WriteFile("  % Post condition lemma for ")
         SAL_Out_IdOp(IdOp)
         WriteFile(" function")
         WritelnFile(1)
         WriteIndntFile(2)
         WriteFile(Strng)
         WriteFile(": LEMMA FORALL ")
         SAL_Out_Params(Params, TypeExpr, nil -> LBS, Result)
         WriteFile(": ")
         WritelnFile(1)
         [|
           ne(LBS, nil)
           WriteFile("    LET ")
           SAL_Out_LetBindings(LBS)
           WriteFile(" IN")
           WritelnFile(1)
         |]
         [| -- partial function
           ne(PreExpr, nil)
           WriteFile("    % precondition")
           WritelnFile(1)
           WriteIndntFile(6)
           (|
             SAL_lower_precedence(PreExpr, 18)
             SAL_Out_Expr(PreExpr)
           ||
             SAL_Out_Expr(bracket(PreExpr))
           |)
           WritelnFile(1)
           WriteFile("    IMPLIES")
           WritelnFile(1)
         |]
         where(PostCond -> postcond(Bindings, PostExpr))
         [| -- bindings??
           ne(Bindings, nil)
           WriteFile("      LET (")
           SAL_Out_Bindings(Bindings, nil, nil -> LBS1)
           WriteFile(") = ")
           SAL_Out_IdOp(IdOp)
           Out_Arguments_from_Params(Params)
           [|
             ne(LBS1, nil)
             WriteFile(", ")
             SAL_Out_LetBindings(LBS1)
           |]
           WriteFile(" IN ")
         |]
         SAL_Out_Expr(PostExpr)
         WriteFile(";")
         WritelnFile(2)

--------------------------------------------------
-- Process the Theory elements that are recursive
-- functions elements (functions), mutual and simple
--------------------------------------------------
'action' Process_Recursive_Elements(SAL_CONTEXT_CONSTANTS)

  'rule' Process_Recursive_Elements(list(theory_decl(
                                   const_decl(
                                     expl_fun_const(IdOp,
                                               Recursive,
                                               Params,
                                               TypeExpr,
                                               Expr, Pre))),
                        ContextElemsTail)):
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
         Process_Recursive_Elements(ContextElemsTail)

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
                        ContextElemsTail)):
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
         Process_Recursive_Elements(ContextElemsTail)

  'rule' Process_Recursive_Elements(list(TheoryElement,
                                         ContextElemsTail)):
         SAL_Process_Context_Elem(TheoryElement)
         Process_Recursive_Elements(ContextElemsTail)

  'rule' Process_Recursive_Elements(nil):


--------------------------------------------------
'action' Out_Fun_Signatures(SAL_CONTEXT_CONSTANTS)

  'rule' Out_Fun_Signatures(list(theory_decl(
                                   const_decl(
                                     expl_fun_const(IdOp,
                                               Recursive,
                                               Params,
                                               TypeExpr,
                                               Expr, Pre))),
                        ContextElemsTail)):
         SAL_Out_IdOp(IdOp)
         WriteFile(": ")
         SAL_Out_Type_Expr(TypeExpr)
         WritelnFile(2)
         Out_Fun_Signatures(ContextElemsTail)

  'rule' Out_Fun_Signatures(list(theory_decl(const_decl(
                        impl_fun_const(IdOp, Params,
                                  TypeExpr, Expr, Pre))),
                        ContextElemsTail)):
         SAL_Out_IdOp(IdOp)
         WriteFile(": ")
         SAL_Out_Type_Expr(TypeExpr)
         WritelnFile(2)
         Out_Fun_Signatures(ContextElemsTail)

  'rule' Out_Fun_Signatures(nil):


-- not used
--------------------------------------------------
'action' Out_Fun_Axioms(SAL_CONTEXT_CONSTANTS)

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
                        ContextElemsTail)):
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
         Out_Fun_Axioms(ContextElemsTail)

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
                        ContextElemsTail)):
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
         Out_Fun_Axioms(ContextElemsTail)

  'rule' Out_Fun_Axioms(list(TheoryElement, ContextElemsTail)):

  'rule' Out_Fun_Axioms(nil):

*/

--------------------------------------------------
'action' SAL_Out_Accesors(SAL_DESTRUCTORS)

  'rule' SAL_Out_Accesors(list(Accesor, Accesors)):
         SAL_Out_Accesor(Accesor)
         [|
           ne(Accesors, nil)
           WriteFile(", ")
         |]
         SAL_Out_Accesors(Accesors)

  'rule' SAL_Out_Accesors(nil):


--------------------------------------------------
'action' SAL_Out_Accesor(SAL_DESTRUCTOR)

  'rule' SAL_Out_Accesor(sal_destructor(IdOps, Vid,TypeExpr,_)):
         SAL_Out_IdOps(IdOps)
         WriteFile(": ")
         SAL_Out_Type_Expr(TypeExpr)

--------------------------------------------------

--------------------------------------------------
'action' SAL_Out_Expr(SAL_VALUE_EXPR)

  'rule' SAL_Out_Expr(sal_literal(Literal)):
         SAL_Out_Literal(Literal)

  'rule' SAL_Out_Expr(sal_resolved_literal(Literal, Tid))
--       SAL_Out_Qualif_from_Tid(Tid)
         SAL_Out_Literal(Literal)

  'rule' SAL_Out_Expr(sal_named_val(id_op(IdOp))):
         SAL_Out_IdOp(IdOp) 

  'rule' SAL_Out_Expr(sal_product(Exprs)):
         WriteFile("(")
         SAL_Out_Tuple_Expr(Exprs)
         WriteFile(")")

  'rule' SAL_Out_Expr(sal_ranged_set(LeftExpr, RightExpr, DomType)):
         WriteFile("LAMBDA (x_ : ")
         SAL_Out_Type_Expr(DomType)
         WriteFile(") : x_ >= ")
         SAL_Out_Expr(LeftExpr)
         WriteFile(" AND x_ <= ")
         SAL_Out_Expr(RightExpr)

  'rule' SAL_Out_Expr(sal_ranged_cc_set(Ident, Type, ElemType, Restriction, DomType)):
	 -- Generating the proper constructor first:
	 where(Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 where(ElemType -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,ElemTid)),_)))
	 -- Set constructor:
	 Tid'Constructor -> vid(Const)
	 SAL_Out_Value_from_Vid(Const)
	 WriteFile("(LAMBDA (")
	 SAL_Out_Ident(Ident)
	 WriteFile(" : ")
         SAL_Out_Type_Expr(DomType)
         WriteFile(") : LET ")
	 SAL_Out_Ident(Ident)
	 WriteFile(" : ")
	 SAL_Out_Type_Expr(ElemType)
	 WriteFile(" = ")
	 -- Elem constructor
	 ElemTid'Constructor -> vid(ElemConst)
	 SAL_Out_Value_from_Vid(ElemConst)
	 WriteFile("(")
	 SAL_Out_Ident(Ident)
	 WriteFile(") IN ")
         SAL_Out_Expr(Restriction)
	 WriteFile(")")

  'rule' SAL_Out_Expr(sal_enum_set(Tid,Type,Exprs)):
         (|
           ne(Exprs, nil)
           SAL_Out_Enum_Set(Tid,Type,Exprs)
         ||
           SAL_Out_Qualif_for_Sets(Tid, Type)
           WriteFile("empty_set")
         |)

         -- RSL : { x | x: T :- p(x) }
         -- SAL : LAMBDA (x : T) : p(x)
  'rule' SAL_Out_Expr(sal_comp_simp_set(bindings(PBS), RestExpr)):
         WriteFile("LAMBDA (")
         SAL_Out_Bindings(PBS, nil, nil -> LBS)
         WriteFile("): ")
         [|
             ne(LBS, nil)
             WriteFile("LET ")
             SAL_Out_LetBindings(LBS)
             WriteFile(" IN ")
         |]
         SAL_Out_Expr(RestExpr)
         
     

         -- RSL : { f(x) | x: T :- p(x) }, where f: T -> U
         -- SAL : LAMBDA (u: U) : EXISTS (x : T) : f(x) = u AND p(x) 
  'rule' SAL_Out_Expr(sal_comp_set(Expr, TypeOfExpr,
                               bindings(PBS), RestExpr)):
         
         WriteFile("LAMBDA (yu_ :")
         SAL_Out_Type_Expr(TypeOfExpr)
         WriteFile(") :")
         WriteFile(" EXISTS (")
         SAL_Out_Bindings(PBS, nil, nil -> LBS)
         WriteFile("): ")
         [|
           ne(LBS, nil)
           WriteFile("LET ")
           SAL_Out_LetBindings(LBS)
           WriteFile(" IN ")
         |]
         WritelnFile(1)
         WriteIndntFile(8)
         [|
           ne(RestExpr, nil)
           (|
             SAL_lower_precedence(RestExpr, 16)
             SAL_Out_Expr(RestExpr)
           ||
             SAL_Out_Expr(sal_bracket(RestExpr))
           |)
           WriteFile(" AND ")
         |]
         WriteFile("yu_ = ")
         (|
           SAL_lower_precedence(Expr, 14)
           SAL_Out_Expr(Expr)
         ||
           SAL_Out_Expr(sal_bracket(Expr))
         |)

  'rule' SAL_Out_Expr(sal_comp_cc_set(Id, TypeOfExpr,
                               bindings(PBS), RestExpr)):
         
         WriteFile("LAMBDA (")
	 SAL_Out_Ident(Id)
	 WriteFile(" : ")
         SAL_Out_Type_Expr(TypeOfExpr)
         WriteFile(") : EXISTS (")
         SAL_Out_Bindings(PBS, nil, nil -> LBS)
         WriteFile(") : ")
         [|
           ne(LBS, nil)
           WriteFile("LET ")
           SAL_Out_LetBindings(LBS)
           WriteFile(" IN ")
         |]
	 SAL_Out_Expr(RestExpr)
	 

  'rule' SAL_Out_Expr(sal_ranged_list(LeftExpr, RightExpr)):
         WriteFile("LAMBDA (x_ : ) : IF (x_ <= ")
         SAL_Out_Expr(RightExpr)
         WriteFile(" - ")
         SAL_Out_Expr(LeftExpr)
         WriteFile(") THEN x_ + ")
         SAL_Out_Expr(LeftExpr)
         WriteFile("ELSE nil;")

  'rule' SAL_Out_Expr(sal_enum_list(Exprs)):
         (|
           ne(Exprs, nil)
           SAL_Out_Enum_List(Exprs)
         ||
           WriteFile("emptylist")
         |)


  'rule' SAL_Out_Expr(sal_comp_list(Expr, sal_limit(SALBindings, ListExpr, RestExpr))):
/*       WriteFile("LAMBDA (")
         SALBindings_to_expr(SALBindings -> E1)
         DefaultPos(-> P) -- ext.g
         
        -- do something here!
         where(SAL_VALUE_EXPR'sal_infix_occ(E1, val_id(sal_op_symb(sal_function_op(isin)),Vid),ListExpr) -> E2)
         (|
           ne(RestExpr, nil)
           where(SAL_VALUE_EXPR'sal_ax_infix(E2, and, RestExpr) -> E3)
         ||
           where(E2 -> E3)
         |)
         SAL_Include_pre_in_bindings(SALBindings, E3, nil -> SALBindings1,_)
         SAL_Out_Bindings(SALBindings1, nil, nil -> LBS1)
         WriteFile("): ")
         [|
           ne(LBS1, nil)
           WriteFile("LET ")
           SAL_Out_LetBindings(LBS1)
           WriteFile(" IN ")
         |]
         SAL_Out_Expr(Expr)
         (|
           ne(RestExpr, nil)
           WriteFile(", filter(")
           SAL_Out_Expr(ListExpr)
           WriteFile(", LAMBDA (")
           SAL_Include_pre_in_bindings(SALBindings, E2, nil -> SALBindings2, _)
           SAL_Out_Bindings(SALBindings2, nil, nil -> LBS2)
           WriteFile("): ")
           [|
             ne(LBS2, nil)
             WriteFile("LET ")
             SAL_Out_LetBindings(LBS2)
             WriteFile(" IN ")
           |]
           SAL_Out_Expr(RestExpr)
           WriteFile("))")
         ||
           WriteFile(", ")
           SAL_Out_Expr(ListExpr)
           WriteFile(")")
         |)
*/
         Putmsg("Comprehended lists are not accepted!!!!!!!!!!!!\n")

  'rule' SAL_Out_Expr(sal_enum_map(Tid, D, R,ExprPairs)):
         (|
           eq(ExprPairs, nil)
           SAL_Out_Qualif_for_Maps(Tid, D, R)
           WriteFile("empty_map")
         ||
           SAL_Out_Enum_Map(Tid, D, R, ExprPairs)
         |)

         -- [ x +> e(x) | x : T :- p(x) ]
         -- LAMBDA (x:T): IF p(x) THEN mk_rng(e(x)) ELSE nil ENDIF
  'rule' SAL_Out_Expr(sal_comp_rng_map(Expr, ValVid, NilVid, bindings(PBS), Pred)):
         -- Generating the LAMBDA:
         WriteFile("LAMBDA (")
         SAL_Out_Bindings(PBS, nil, nil -> LBS)
         WriteFile("): ")
         [|
           ne(LBS, nil)
           WriteFile("LET ")
           SAL_Out_LetBindings(LBS)
           WriteFile(" IN ")
         |]
         (|
           eq(Pred, nil)
           SAL_Out_Value_from_Vid(ValVid)
           WriteFile("(")
           SAL_Out_Expr(Expr)
           WriteFile(")")
         ||
           WriteFile("IF ")
           SAL_Out_Expr(Pred)
           WriteFile(" THEN ")
           SAL_Out_Value_from_Vid(ValVid)
           WriteFile("(")
           SAL_Out_Expr(Expr)
           WriteFile(") ELSE ")
           SAL_Out_Value_from_Vid(NilVid)
           WriteFile(" ENDIF")
         |) 

         -- [ e1(x) +> e2(x) | x : T :- p(x) ] where e1 : T -> U1, e2 : T -> U2
         -- LAMBDA (u : U1) : IF EXISTS (x : T) : e1(x) = u AND p(x)
         --                   THEN e2(x)
         --                   ELSE nil ENDIF;

  'rule' SAL_Out_Expr(sal_comp_map(pair(Expr1, Expr2), Tid, bindings(PBS), Pred)):
/*       WriteFile("LAMBDA (")
         -- Generate new Product identifier and add 1 to ProdIndex
         SAL_Gen_Prod_Ident("lb_" -> LambdaB)
         SAL_Out_Ident(LambdaB) 
         WriteFile(" : ")
         SAL_Out_Type_Expr(TypeExprDom)
         WriteFile("):")
         WritelnFile(1)
         WriteFile("LET (")
         SAL_Out_Bindings(PBS, nil, nil -> LBS)
         WriteFile(") = RSL_inverse(LAMBDA (")
         SAL_Out_Bindings(PBS, nil, nil -> LBS1)
         WriteFile("): ")
         [|
           ne(LBS1, nil)
           WriteFile("LET ")
           SAL_Out_LetBindings(LBS1)
           WriteFile(" IN ")
         |]
         SAL_Out_Expr(Expr1)
         WriteFile(")(")
         SAL_Out_Ident(LambdaB)
         WriteFile(") IN")
         WritelnFile(1)
         [|
           ne(LBS, nil)
           WriteFile("LET ")
           SAL_Out_LetBindings(LBS)
           WriteFile(" IN ")
         |]
         (|
           eq(Pred, nil)
           WriteFile("mk_rng(")
           SAL_Out_Expr(Expr2)
           WriteFile(")")
         ||
           WriteFile("IF ")
           SAL_Out_Expr(Pred)
           WriteFile(" THEN mk_rng(")
           SAL_Out_Expr(Expr2)
           -- nil needs coercion to avoid TCC
           WriteFile(") ELSE nil::Maprange_adt[")
           SAL_Out_Type_Expr(TypeExprRng)
           WriteFile("].Maprange ENDIF")
         |) 
*/

  'rule' SAL_Out_Expr(sal_function(LambdaBindings, Expr)):
         WriteFile("LAMBDA (")
         SAL_Out_LambdaBindings(LambdaBindings, nil -> LBS)
         WriteFile("): ")
         WritelnFile(1)
         [|
           ne(LBS, nil)
           WriteFile("    LET ")
           SAL_Out_LetBindings(LBS)
           WriteFile(" IN")
           WritelnFile(1)
         |]
         SAL_Out_Expr(Expr)
         WritelnFile(1)

  'rule' SAL_Out_Expr(sal_list_applic(ListExpr, Arguments)):
         SAL_Out_Expr(ListExpr)
         WriteFile("(")
         where(Arguments -> sal_argument(list(E, nil)))
         SAL_Out_Expr(E)
         WriteFile(")")

  'rule' SAL_Out_Expr(sal_map_applic(Tid, MapExpr, Arguments)):
         Tid'TExpr -> rsl_built_in(sal_finite_map(_,_,RngType))
         where(RngType -> type_refs(sal_defined(_,_,Map_Range_Tid)))
         Map_Range_Tid'TExpr -> Type
         -- Processing the Map_range type to extract the "val" destructor:
         where(Type -> user_defined(sal_variant_type(Dparts)))
         where(Dparts -> list(_,list(ValPart,nil)))
         -- val part
         where(ValPart -> sal_part(ValConst,_))
         where(ValConst -> sal_construc(_,ValVid,Destrs,_))
         -- real RANGE type (got from the destructor)
         where(Destrs -> list(sal_destructor(_,DestrVid,_,_), nil))
         -- Out the val destructor:
         SAL_Out_Value_from_Vid(DestrVid)
         WriteFile("(")
         SAL_Out_Expr(MapExpr)
         WriteFile("(")
         where(Arguments -> sal_argument(list(E, nil)))
         SAL_Out_Expr(E)
         WriteFile(")")
         WriteFile(")")

  'rule' SAL_Out_Expr(sal_cc_map_applic(MapTid, MapExpr, Arguments)):
  	 MapTid'OperationsCid -> cid(Cid)
	 Cid'Ident -> OpsId
	 SAL_Out_Ident(OpsId)
	 WriteFile("!apply(")
         where(Arguments -> sal_argument(list(E, nil)))
         SAL_Out_Expr(E)
	 WriteFile(", ")
         SAL_Out_Expr(MapExpr)
	 WriteFile(")")

  'rule' SAL_Out_Expr(sal_funct_applic(FunExpr, Arguments)):
         (|
           SAL_lower_precedence(FunExpr, 1)
           SAL_Out_Expr(FunExpr)
         ||
           SAL_Out_Expr(sal_bracket(FunExpr))
         |)
         -- Generate new Product identifier and add 1 to ProdIndex
--       SAL_Gen_Prod_Ident("" -> IdProd)
         SAL_Out_Arguments(Arguments)

  'rule' SAL_Out_Expr(sal_destr_applic(RecordName, Destr)):
         SAL_Out_Expr(RecordName)
         WriteFile(".")
         SAL_Out_Expr(Destr)

  'rule' SAL_Out_Expr(sal_quantified(exists1, bindings(PBS), Expr)): -- TODO: exists1???
         WriteFile("EXISTS (")
         SAL_Out_Bindings(PBS, nil, nil -> LBS)
         WriteFile("): ")
         [|
           eq(LBS, nil)
           SAL_Out_Expr(Expr)
	   WriteFile(" AND (FORALL (")
	   SAL_Modify_Bindings(PBS -> PBS1)
	   SAL_Out_Bindings(PBS1, nil, nil -> LBS1)
	   WriteFile("): ")
	   SAL_Modify_Expr(PBS, Expr -> Expr1)
	   SAL_Out_Expr(Expr1)
	   WriteFile(" => ")
	   SAL_Out_Bound_Ineq_vars(PBS)
	   WriteFile(") ")
	   WritelnFile(1)
	 |]

-- rewrite all x : T :- L1 /\ L2 => R as all x : T :- L1 => L2 => R
  'rule' SAL_Out_Expr(sal_quantified(forall, bindings(PBS), Expr)):
	 where(Expr -> sal_ax_infix(Left, implies, Right))
	 SAL_Split_conjunct(Left -> L1, L2)
	 where(sal_ax_infix(L1, implies, sal_ax_infix(L2, implies, Right)) -> Expr1)
	 SAL_Out_Expr(sal_quantified(forall, bindings(PBS),  Expr1))

-- use subtypes when possible
-- all x : T :- x isin S => Q
-- translated as
-- FORALL (x: {x: T | x isin S}): Q
  'rule' SAL_Out_Expr(sal_quantified(forall, bindings(PBS), Expr)):
	 where(Expr -> sal_ax_infix(Left, implies, Right))
	 (|
	   where(Left -> sal_recogniser(_,_)) -- used for (not)isin_map
	   -- enough?
	 ||
	   where(Left -> sal_infix_occ(_, val_id(Idop), _))
	   where(Idop -> sal_set_op(sal_function_op(isin),_,_))
	 |)
	 where(PBS -> list(sal_typed_id(P, IdOp, SALType), nil))
	 WriteFile(" FORALL (")
	 SAL_Out_IdOp(IdOp)
	 WriteFile(": {")
	 SAL_Out_IdOp(IdOp)
	 WriteFile(": ")
	 SAL_Out_Type_Expr(SALType)
	 WriteFile(" | ")
	 SAL_Out_Expr(Left)
	 WriteFile("}): ")
	 SAL_Out_Expr(Right)

-- rewrite exists x : T :- (L1 /\ L2) /\ R as all x : T :- L1 /\ (L2 /\ R)
  'rule' SAL_Out_Expr(sal_quantified(exists, bindings(PBS), Expr)):
	 where(Expr -> sal_ax_infix(Left, and, Right))
	 SAL_Split_conjunct(Left -> L1, L2)
	 where(sal_ax_infix(L1, and, sal_ax_infix(L2, and, Right)) -> Expr1)
	 SAL_Out_Expr(sal_quantified(exists, bindings(PBS),  Expr1))

-- use subtypes when possible
-- exists x : T :- x isin S /\ P
-- translated as
-- EXISTS (x: {x: T | x isin S }): P
  'rule' SAL_Out_Expr(sal_quantified(exists, bindings(PBS), Expr)):
	 where(Expr -> sal_ax_infix(Left, and, Right))
	 (|
	   where(Left -> sal_recogniser(_,_)) -- used for (not)isin_map
	   -- enough?
	 ||
	   where(Left -> sal_infix_occ(_, val_id(Idop), _))
	   where(Idop -> sal_set_op(sal_function_op(isin),_,_))
	 |)
	 where(PBS -> list(sal_typed_id(P, IdOp, SALType), nil))
	 WriteFile(" EXISTS (")
	 SAL_Out_IdOp(IdOp)
	 WriteFile(": {")
	 SAL_Out_IdOp(IdOp)
	 WriteFile(": ")
	 SAL_Out_Type_Expr(SALType)
	 WriteFile(" | ")
	 SAL_Out_Expr(Left)
	 WriteFile("}): ")
	 SAL_Out_Expr(Right)

  'rule' SAL_Out_Expr(sal_quantified(BindingOp, bindings(PBS), Expr)):
         SAL_Out_BindingOp(BindingOp)
         WriteFile("(")
         SAL_Out_Bindings(PBS, nil, nil -> LBS)
         WriteFile("): ")
         [|
           ne(LBS, nil)
           WriteFile("LET ")
           SAL_Out_LetBindings(LBS)
           WriteFile(" IN ")
         |]
         SAL_Out_Expr(Expr)
         WritelnFile(1)

/*  'rule' SAL_Out_Expr(sal_ranged_set_quantified(BindingOp, bindings(PBS), Expr)):
         SAL_Out_BindingOp(BindingOp)
         WriteFile("(")
         SAL_Out_Bindings(PBS, nil, nil -> LBS)
         WriteFile("): ")
         [|
           ne(LBS, nil)
           WriteFile("LET ")
           SAL_Out_LetBindings(LBS)
           WriteFile(" IN ")
         |]
         SAL_Out_Expr(Expr)
         WritelnFile(1)*/


  'rule' SAL_Out_Expr(sal_equivalence(LeftExpr, RightExpr, PreExpr)):
         [|
           ne(PreExpr, nil)
           (|
             SAL_lower_precedence(PreExpr, 18)
             SAL_Out_Expr(PreExpr)
           ||
             SAL_Out_Expr(sal_bracket(PreExpr))
           |)
           WriteFile(" IMPLIES ")
         |]
         (|
           SAL_lower_precedence(LeftExpr, 14)
           SAL_Out_Expr(LeftExpr)
         ||
           SAL_Out_Expr(sal_bracket(LeftExpr))
         |)
         WriteFile(" = ")
         (|
           SAL_lower_precedence(RightExpr, 14)
           SAL_Out_Expr(RightExpr)
         ||
           SAL_Out_Expr(sal_bracket(RightExpr))
         |)
         WritelnFile(1)

  'rule' SAL_Out_Expr(sal_bracket(Expr)):
         WriteFile("(")
         SAL_Out_Expr(Expr)
         WriteFile(")")

  'rule' SAL_Out_Expr(sal_ax_infix(LeftExpr, Connective, RightExpr)): 
         SAL_connective_precedence(Connective -> P)
         (|
           SAL_lower_precedence(LeftExpr, P)
           SAL_Out_Expr(LeftExpr)
         ||
           SAL_Out_Expr(sal_bracket(LeftExpr))
         |)
         SAL_Out_Connective(Connective)
         (|
           SAL_lower_precedence(RightExpr, P)
           SAL_Out_Expr(RightExpr)
         ||
           SAL_Out_Expr(sal_bracket(RightExpr))
         |)

  'rule' SAL_Out_Expr(sal_funct_expr(val_id(IdOp), Qualif,Expr1, Expr2)):
/*
         SAL_PrintIdOp(IdOp)
         SAL_Out_Object_Qualif(Qualif)
         SAL_Out_IdOp(IdOp)
         WriteFile("(")
         SAL_Out_Expr(Expr1)
         [|
           ne(Expr2, nil)
           WriteFile(", ")
           SAL_Out_Expr(Expr2)
         |]
         WriteFile(")")
*/
         -- This is going to be more complex by the time the lifted
         -- type system get introduced...
         
         -- SAL_Out_Object_Qualif(Qualif) -- Needed in the future!
         SAL_Out_Expr(Expr1)
         SAL_Out_IdOp(IdOp)
         SAL_Out_Expr(Expr2)
         

  'rule' SAL_Out_Expr(sal_ax_prefix(Connective, Expr)): 
         SAL_Out_Connective(Connective)
         (|
           SAL_lower_precedence(Expr, 15)
           SAL_Out_Expr(Expr)
         ||
           SAL_Out_Expr(sal_bracket(Expr))
         |)

  'rule' SAL_Out_Expr(sal_let_expr(Ident, TElem, Namespace,_,InitExpr, BodyExpr)):
         WriteFile("LET ")
         SAL_Out_Ident(Ident)
         WriteFile(" : ")
         SAL_Out_Type_Expr(TElem)
         WriteFile(" = ")
         SAL_Out_Expr(InitExpr)
         WriteFile(" IN")
         WritelnFile(1)
         WriteFile("  ")
         Push_Namespace(Namespace)
         SAL_Out_Expr(BodyExpr)
         Pop_Namespace()
         WritelnFile(1)

 'rule' SAL_Out_Expr(sal_esp_let_expr(Ident, TElem, InitExpr, Transition)):
         WriteFile("LET ")
         SAL_Out_Ident(Ident)
         WriteFile(" : ")
         SAL_Out_Type_Expr(TElem)
         WriteFile(" = ")
         SAL_Out_Expr(InitExpr)
         WriteFile(" IN")
         WritelnFile(1)
         SAL_Out_Transition(Transition)
         WritelnFile(1)

  'rule' SAL_Out_Expr(sal_if_expr(Expr, ThenExpr, Elsifs, Else)):
         [| -- if with no else not supported
           ne(Else, nil)
           WriteFile("IF ")
           SAL_Out_Expr(Expr)
           WritelnFile(1)
           WriteFile("THEN ")
           SAL_Out_Expr(ThenExpr)
           [|
             ne(Elsifs, nil)
             SAL_Out_Elsifs(Elsifs)
           |]
           where(Else -> else(ElseExpr))
           WritelnFile(1)
           WriteFile("ELSE ")
           SAL_Out_Expr(ElseExpr)
           WritelnFile(1)
           WriteFile("ENDIF")
         |]

 
  'rule' SAL_Out_Expr(sal_esp_value_occ(Vid))
         SAL_Out_Qualif_from_Vid(Vid)
         Vid'IdOp -> IdOp
         SAL_Out_IdOp(IdOp)

  'rule' SAL_Out_Expr(sal_recogniser(Vid, Args))
         SAL_Out_Qualif_from_Vid(Vid)
         Vid'IdOp -> IdOp
         SAL_Out_IdOp(IdOp)
         WriteFile("?")
         SAL_Out_Arguments(Args)

  'rule' SAL_Out_Expr(sal_value_occ(val_id(IdOp), Qualif)):
         -- The value ocurrence is dependant on the possible bindings
         -- over tuples (in the arguments...)
         Current_LBS_Env -> CurrEnv
         (|
             -- The current binding env is nill -> no bindings
             -- introduced in this scope...
             -- Normal handling of the value:
             eq(CurrEnv, nil)
             SAL_Out_Object_Qualif(Qualif)
             SAL_Out_IdOp(IdOp) 
         ||
             look_up_binding_in_namespace(IdOp -> BElem)
             (|
                -- The current value is not mentioned in the bindings...
                eq(BElem, nil)
                -- Again, normal handling...
                SAL_Out_Object_Qualif(Qualif)
                SAL_Out_IdOp(IdOp)
             ||
                -- A binding matching this name was found...
                -- Replace the occurrence with the proper name and
                -- tuple field number...
                SAL_Out_Binding_Element(BElem)
             |)

         |)

  'rule' SAL_Out_Expr(sal_value_occ(record_val_id(_,IdOp,Index),_))
         SAL_Out_IdOp(IdOp)
         WriteFile(".")
         Int_to_string(Index -> IndStr)
         WriteFile(IndStr)

  'rule' SAL_Out_Expr(sal_value_occ(complex_val_id(_,Expr,Index),_))
         WriteFile("(")
         SAL_Out_Expr(Expr)
         WriteFile(").")
         Int_to_string(Index -> IndStr)
         WriteFile(IndStr)
         
/*  'rule' SAL_Out_Expr(sal_infix_occ(LeftExpr, 
           val_id(sal_op_symb(sal_infix_op(eq))), RightExpr)):
         (|
           SAL_Is_empty_set_map_list(RightExpr)
           WriteFile("is_empty(")
           SAL_Out_Expr(LeftExpr)
           WriteFile(")")
         ||
           SAL_Is_empty_set_map_list(RightExpr)
           WriteFile("is_empty(")
           SAL_Out_Expr(LeftExpr)
           WriteFile(")")
         |)

  'rule' SAL_Out_Expr(sal_infix_occ(LeftExpr, 
           val_id(sal_op_symb(sal_infix_op(neq))), RightExpr)):
         (|
           SAL_Is_empty_set_map_list(RightExpr)
           WriteFile("nonempty?(")
           SAL_Out_Expr(LeftExpr)
           WriteFile(")")
         ||
           SAL_Is_empty_set_map_list(RightExpr)
           WriteFile("nonempty?(")
           SAL_Out_Expr(LeftExpr)
           WriteFile(")")
         |)
*/
-- user defined operators? TODO
  'rule' SAL_Out_Expr(sal_infix_occ(LeftExpr, val_id(IdOp),RightExpr)):
         (| -- operator symbol
           where(IdOp -> sal_op_symb(Op))
           (| -- infix_op
             where(Op -> sal_infix_op(Oper))
             SAL_infix_precedence(Oper -> P)
             (|
               SAL_lower_precedence(LeftExpr, P)
               SAL_Out_Expr(LeftExpr)
             ||
               SAL_Out_Expr(sal_bracket(LeftExpr))
             |)
             SAL_Out_IdOp(IdOp) 
             (|
               SAL_lower_precedence(RightExpr, P)
               SAL_Out_Expr(RightExpr)
             ||
               SAL_Out_Expr(sal_bracket(RightExpr))
             |)
           || -- prefix_op
             where(Op -> sal_prefix_op(_))
             print("internal ERR (gen_code) - prefix_op in an infix_occ")
           || -- function_op
             where(Op -> sal_function_op(Oper))
             SAL_Out_IdOp(IdOp) 
             WriteFile("(")
             SAL_Out_Expr(LeftExpr)
             [|
               ne(RightExpr, nil)
               WriteFile(", ")
               SAL_Out_Expr(RightExpr)
             |]
             WriteFile(")")
           |)
         || -- 
           print("internal ERR (gen_code) - non operator in infix position")
         |)

  'rule' SAL_Out_Expr(sal_prefix_occ(val_id(IdOp),Qualif,Expr)):
         (| -- operator symbol
           where(IdOp -> sal_op_symb(Op))
           (| -- prefix_op
             where(Op -> sal_prefix_op(Op1))
             SAL_Out_IdOp(IdOp) 
             (|
               SAL_lower_precedence(Expr, 14)
               SAL_Out_Expr(Expr)
             ||
               SAL_Out_Expr(sal_bracket(Expr))
             |)
           || -- infix_op
             where(Op -> sal_infix_op(Op2))
             (|
               eq(Op2, minus)
               SAL_Out_IdOp(IdOp) 
               (|
                 SAL_lower_precedence(Expr, 9)
                 SAL_Out_Expr(Expr)
               ||
                 SAL_Out_Expr(sal_bracket(Expr))
               |)
             ||
               print("internal ERR (gen_code):")
               print("  infix_op in a prefix_occ")
             |)
           || -- function_op
             where(Op -> sal_function_op(_))
             SAL_Out_Object_Qualif(Qualif)
             SAL_Out_IdOp(IdOp) 
             WriteFile("(")
             SAL_Out_Expr(Expr)
             WriteFile(")")
           |)
         ||
           SAL_Out_IdOp(IdOp) 
           SAL_Out_Expr(sal_bracket(Expr))
         |)

  'rule' SAL_Out_Expr(sal_esp_prefix_occ(val_id(IdOp), Left, Right)):
	 SAL_Out_IdOp(IdOp)
         WriteFile("(")
         SAL_Out_Expr(Left)
         WriteFile(", ")
         SAL_Out_Expr(Right)
         WriteFile(")")

  'rule' SAL_Out_Expr(sal_esp_unary_prefix_occ(val_id(IdOp), Left)):
  	 SAL_Out_IdOp(IdOp)   
         WriteFile("(")
         SAL_Out_Expr(Left)
         WriteFile(")")

  'rule' SAL_Out_Expr(sal_esp_ternary_occ(val_id(IdOp), E1, E2, E3)):
	 SAL_Out_IdOp(IdOp)
         WriteFile("(")
         SAL_Out_Expr(E1)
         WriteFile(", ")
         SAL_Out_Expr(E2)
         WriteFile(", ")
         SAL_Out_Expr(E3)
         WriteFile(")")

  'rule' SAL_Out_Expr(sal_var_occ(Pos, VarId))
         VarId'Ident -> Ident
         SAL_Out_Variable_Id(Ident)      

  'rule' SAL_Out_Expr(no_val):
         WriteFile("no_val ")

         -- not supported
  'rule' SAL_Out_Expr(no_def):

  'rule' SAL_Out_Expr(not_supported):

  'rule' SAL_Out_Expr(nil):

  'rule' SAL_Out_Expr(sal_array_expr(T, Type, V)):
         --WriteFile("[[i : ")
         WriteFile("[[")
         SAL_Out_Bindings(T, nil, nil -> _)
         --SAL_Out_Type_Expr(Type)
         WriteFile("] ")
         SAL_Out_Expr(V)
         WriteFile("]")

  'rule' SAL_Out_Expr(sal_array_var_occ(_,VarId,Index)):
         VarId'Ident -> Ident
         SAL_Out_Variable_Id(Ident)
         SAL_Out_Array_Indexes(Index)
         /*WriteFile("[")
         SAL_Out_Expr(Index)
         WriteFile("]")*/

/*  'rule' SAL_Out_Expr(sal_cc_array_var_occ(P,Id,Index)):
         Id'Type -> Temp
         --Id'Ident -> Ident
         Reverse_SAL_VALUE_EXPRS(Index, nil, Temp, nil -> ReversedIndex, Types)
         SAL_Out_Array_CC_Var_occ(ReversedIndex, Types, sal_var_occ(P,Id))*/
         /*SAL_Remove_Brackets(Temp -> rsl_built_in(sal_array(Tid,T1,T2)))
         Tid'Lifted_Tid -> tid(LiftedTid)
         LiftedTid'OperationsCid -> cid(Cid)
         Cid'Ident -> OpsId
         SAL_Out_Ident(OpsId)
         WriteFile("!access(")
         SAL_Out_Expr(Index)
         WriteFile(", ")
         Id'Ident -> Ident
         SAL_Out_Variable_Id(Ident)
         WriteFile(")")*/

  'rule' SAL_Out_Expr(sal_cc_array_set(P,Ar,Type,Index,Value)):
         --Id'Type -> Type
         SAL_Remove_Brackets(Type -> Type2)
         where(Type2 -> rsl_built_in(sal_array(Tid,T1,T2)))
         Tid'Lifted_Tid -> tid(LiftedTid)
         LiftedTid'OperationsCid -> cid(Cid)
         Cid'Ident -> OpsId
         --Id'Ident -> Ident
         --id_to_string(Ident -> S)
         --Remove_Prime(S -> S2)
         --string_to_id(S2 -> Ident2)
         SAL_Out_Ident(OpsId)
         WriteFile("!set(")
         (|
           where(Index -> list(H,nil))
           SAL_Out_Expr(H)
           WriteFile(", ")
           SAL_Out_Expr(Value)
           WriteFile(", ")
           (|
             where(Ar -> sal_var_occ(_,Id))
             Id'Ident -> Ident
             id_to_string(Ident -> S)
             Remove_Prime(S -> S2)
             string_to_id(S2 -> Ident2)
             SAL_Out_Variable_Id(Ident2)
           ||
             SAL_Out_Expr(Ar)
           |)
           WriteFile(")") 
         ||
           --Reverse_SAL_VALUE_EXPRS(Index, nil, Type, nil -> ReversedIndex, Types)
           where(Index -> list(H, Tail))
           --where(Types -> list(Type1, TypeTail))
           SAL_Out_Expr(H)
           WriteFile(", ")
           SAL_Out_Array_CC_Set(Tail, list(H,nil), T2, list(Type,nil), Ar, Value)
           WriteFile(", ")
           (|
             where(Ar -> sal_var_occ(_,Id))
             Id'Ident -> Ident
             id_to_string(Ident -> S)
             Remove_Prime(S -> S2)
             string_to_id(S2 -> Ident2)
             SAL_Out_Variable_Id(Ident2)
           ||
             SAL_Out_Expr(Ar)
           |)
           WriteFile(")")
         |)

/*  'rule' SAL_Out_Expr(sal_array_val_occ(_, Val, Index)):
         SAL_Out_Expr(Val)
         SAL_Out_Array_Indexes(Index)*/

/*  'rule' SAL_Out_Expr(sal_cc_array_val_occ(_, Val, Index, ArrayTid)):
         --SAL_Out_Expr(Val)
         ArrayTid'TExpr -> Type
         Reverse_SAL_VALUE_EXPRS(Index, nil, Type, nil -> ReversedIndex, Types)
         SAL_Out_Array_CC_Val_occ(ReversedIndex, Types, Val)*/

  'rule' SAL_Out_Expr(sal_array_access(Name, Index))
         SAL_Out_Expr(Name)
         WriteFile("[")
         SAL_Out_Expr(Index)
         WriteFile("]")

  'rule' SAL_Out_Expr(sal_cc_array_access(Name, Index, Tid))
         Tid'Lifted_Tid -> tid(LiftedTid)
         LiftedTid'OperationsCid -> cid(Cid)
         Cid'Ident -> OpsId
         SAL_Out_Ident(OpsId)
         WriteFile("!access(")
         SAL_Out_Expr(Index)
         WriteFile(", ")
	 SAL_Out_Expr(Name)
         WriteFile(")")

  'rule' SAL_Out_Expr(T)
         Putmsg("Debugging predicate activated in SAL_Out_Expr\n")
         print(T)


'action' SAL_Out_Array_Indexes(SAL_VALUE_EXPRS)
  'rule' SAL_Out_Array_Indexes(nil)

  'rule' SAL_Out_Array_Indexes(list(H,T))
         WriteFile("[")
         SAL_Out_Expr(H)
         WriteFile("]")
         SAL_Out_Array_Indexes(T)

         

'action' SAL_Out_Array_CC_Set(SAL_VALUE_EXPRS, SAL_VALUE_EXPRS, SAL_TYPE_EXPR, SAL_TYPE_EXPRS, SAL_VALUE_EXPR, SAL_VALUE_EXPR)
  'rule' SAL_Out_Array_CC_Set(nil, _, _, _, _, _)

  'rule' SAL_Out_Array_CC_Set(list(H,Tail), Used, Type, UsedTypes, Ident, Val)
         SAL_Remove_Brackets(Type -> rsl_built_in(sal_array(Tid,T1,T2)))
         Tid'Lifted_Tid -> tid(LiftedTid)
         LiftedTid'OperationsCid -> cid(Cid)
         Cid'Ident -> OpsId
	 SAL_Out_Ident(OpsId)
         WriteFile("!set(")
         SAL_Out_Expr(H)
         WriteFile(",")
         (|
	   where(Tail -> nil)
           SAL_Out_Expr(Val)
         ||
           SAL_Out_Array_CC_Set(Tail, list(H,Used), T2, list(Type, UsedTypes), Ident, Val)
         |)
         WriteFile(",")
         SAL_Out_Array_CC_Var_occ(Used, UsedTypes, Ident)
         WriteFile(")")

'action' SAL_Out_Array_CC_Var_occ(SAL_VALUE_EXPRS, SAL_TYPE_EXPRS, SAL_VALUE_EXPR)
  'rule' SAL_Out_Array_CC_Var_occ(list(H,nil), list(Type,nil), IdentExpr)
         where(IdentExpr -> sal_var_occ(_,Id))
         Id'Ident -> Ident
         id_to_string(Ident -> S)
         Remove_Prime(S -> S2)
         string_to_id(S2 -> Ident2)
         SAL_Remove_Brackets(Type -> rsl_built_in(sal_array(Tid,T1,T2)))
         Tid'Lifted_Tid -> tid(LiftedTid)
         LiftedTid'OperationsCid -> cid(Cid)
         Cid'Ident -> OpsId
         SAL_Out_Ident(OpsId)
         WriteFile("!access(")
         SAL_Out_Expr(H)
         WriteFile(", ")
         SAL_Out_Variable_Id(Ident2)
         --SAL_Out_Expr(Ident)
         WriteFile(")")

  'rule' SAL_Out_Array_CC_Var_occ(list(H,Tail), list(Type,TypeTail), Id)
         SAL_Remove_Brackets(Type -> rsl_built_in(sal_array(Tid,T1,T2)))
         Tid'Lifted_Tid -> tid(LiftedTid)
         LiftedTid'OperationsCid -> cid(Cid)
         Cid'Ident -> OpsId
         SAL_Out_Ident(OpsId)
         WriteFile("!access(")
         SAL_Out_Expr(H)
         WriteFile(", ")
         SAL_Out_Array_CC_Var_occ(Tail, TypeTail, Id)
         WriteFile(")")

/*'action' SAL_Out_Array_CC_Val_occ(SAL_VALUE_EXPRS, SAL_TYPE_EXPRS, SAL_VALUE_EXPR)
  'rule' SAL_Out_Array_CC_Val_occ(list(H,nil), list(Type,nil), Ident)
         SAL_Remove_Brackets(Type -> rsl_built_in(sal_array(Tid,T1,T2)))
         Tid'Lifted_Tid -> tid(LiftedTid)
         LiftedTid'OperationsCid -> cid(Cid)
         Cid'Ident -> OpsId
         SAL_Out_Ident(OpsId)
         WriteFile("!access(")
         SAL_Out_Expr(H)
         WriteFile(", ")
         SAL_Out_Expr(Ident)
         WriteFile(")")

  'rule' SAL_Out_Array_CC_Val_occ(list(H,Tail), list(Type,TypeTail), Id)
         SAL_Remove_Brackets(Type -> rsl_built_in(sal_array(Tid,T1,T2)))
         Tid'Lifted_Tid -> tid(LiftedTid)
         LiftedTid'OperationsCid -> cid(Cid)
         Cid'Ident -> OpsId
         SAL_Out_Ident(OpsId)
         WriteFile("!access(")
         SAL_Out_Expr(H)
         WriteFile(", ")
         SAL_Out_Array_CC_Val_occ(Tail, TypeTail, Id)
         WriteFile(")")*/



--------------------------------------------------
'action' SAL_Out_Elsifs(SAL_ELSIF_BRANCHES)

  'rule' SAL_Out_Elsifs(list(Elsif, ElsifsTail)):
         SAL_Out_Elsif(Elsif)
         SAL_Out_Elsifs(ElsifsTail)

  'rule' SAL_Out_Elsifs(nil):

'action' Reverse_SAL_VALUE_EXPRS(SAL_VALUE_EXPRS, SAL_VALUE_EXPRS, SAL_TYPE_EXPR, SAL_TYPE_EXPRS -> SAL_VALUE_EXPRS, SAL_TYPE_EXPRS)
  'rule' Reverse_SAL_VALUE_EXPRS(nil, Reversed, _, Types -> Reversed, Types)

  'rule' Reverse_SAL_VALUE_EXPRS(list(H,T), Reversed, Type, Types -> Res, TypesRes)
         SAL_Remove_Brackets(Type -> rsl_built_in(sal_array(Tis, T1, T2)))
         Reverse_SAL_VALUE_EXPRS(T, list(H,Reversed), T2, list(Type,Types) -> Res, TypesRes)


--------------------------------------------------
'action' SAL_Out_Elsif(SAL_ELSIF_BRANCH)

  'rule' SAL_Out_Elsif(elsif(IfExpr, ThenExpr)):
         WritelnFile(1)
         WriteFile("ELSIF ")
         SAL_Out_Expr(IfExpr)
         WritelnFile(1)
         WriteFile("THEN ")
         SAL_Out_Expr(ThenExpr)

--------------------------------------------------
'action' SAL_Out_Object_Qualif(SAL_OBJ_QUALIF)

  'rule' SAL_Out_Object_Qualif(Qualif)
	 [|
	    where(Qualif -> qualif(Oid))
	    -- Getting the context where the object schema was translated:
	    Oid'Cid -> Cid
	    -- Getting the current context:
	    SAL_Current_Cid -> CurrCid
	    [|
	       -- Qualify if declared outside the current context:
	       ne(Cid, CurrCid)
	       Cid'Ident -> Id
	       SAL_Out_Ident(Id)
	       WriteFile("!")
	    |]
	 |]
--------------------------------------------------
'condition' SAL_Split_conjunct(SAL_VALUE_EXPR -> SAL_VALUE_EXPR, SAL_VALUE_EXPR)

  'rule' SAL_Split_conjunct(V -> V1, V2):
	 (|
	   where(V -> sal_ax_infix(V1, and, V2))
	 ||
	   where(V -> sal_bracket(V0))
	   SAL_Split_conjunct(V0 -> V1, V2)
	 |) 

--------------------------------------------------
'condition' SAL_Is_empty_set_map_list(SAL_VALUE_EXPR)

  'rule' SAL_Is_empty_set_map_list(sal_enum_set(_,_,nil)):

  'rule' SAL_Is_empty_set_map_list(sal_enum_map(_,_,_, nil)):

  'rule' SAL_Is_empty_set_map_list(sal_enum_list(nil)):

  'rule' SAL_Is_empty_set_map_list(sal_bracket(E)):
         SAL_Is_empty_set_map_list(E)

--------------------------------------------------
/*
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
'action' Gen_ConstantDecl(SAL_CONSTANT_DECL)

  'rule' Gen_ConstantDecl(sal_nodef(IdOps, TypeExpr, Expr)):
         SAL_Out_IdOps(IdOps)

  'rule' Gen_ConstantDecl(sal_expl_const(IdOps, TypeExpr, Expr)):
         SAL_Out_IdOps(IdOps)

  'rule' Gen_ConstantDecl(sal_fun_const(IdOp, _, _, _, _, _)):
         SAL_Out_IdOp(IdOp)
*/
--------------------------------------------------
'action' SAL_Out_Enum_Set(SAL_type_id, SAL_TYPE_EXPR, SAL_VALUE_EXPRS)

  'rule' SAL_Out_Enum_Set(Tid, Type, list(Expr, ExprsTail)):
         SAL_Out_Qualif_for_Sets(Tid, Type)
         WriteFile("add(")
         SAL_Out_Expr(Expr)
         (|
           eq(ExprsTail, nil)
           WriteFile(", ")
           SAL_Out_Qualif_for_Sets(Tid, Type)
           WriteFile("empty_set")
         ||
           WriteFile(", ")
         |)
         SAL_Out_Enum_Set(Tid, Type, ExprsTail)
         WriteFile(")")

  'rule' SAL_Out_Enum_Set(_,_,nil):

--------------------------------------------------
'action' SAL_Out_Enum_List(SAL_VALUE_EXPRS)

  'rule' SAL_Out_Enum_List(list(Expr, ExprsTail)):
         Default_Int_Tid -> IntTid
         IntTid'OperationsCid -> OptCid
         where(OptCid -> cid(Cid))
         Cid'Ident -> Ident
         SAL_Out_Ident(Ident)
         WriteFile("!")
         WriteFile("add(")
         SAL_Out_Expr(Expr)
         (|
           eq(ExprsTail, nil)
           WriteFile(", ")
           SAL_Out_Ident(Ident)
           WriteFile("!empty_list")
         ||
           WriteFile(", ")
         |)
         SAL_Out_Enum_List(ExprsTail)

  'rule' SAL_Out_Enum_List(nil):

--------------------------------------------------
'action' SAL_Out_Enum_Map(SAL_type_id, SAL_TYPE_EXPR, SAL_TYPE_EXPR, SAL_VALUE_EXPR_PAIRS)

  'rule' SAL_Out_Enum_Map(Tid, D, R, list(pair(LeftExpr, RightExpr), ExprPairsTail)):
         SAL_Out_Qualif_for_Maps(Tid, D, R)
         WriteFile("add(")
         SAL_Out_Expr(LeftExpr)
         WriteFile(", ")
         SAL_Out_Expr(RightExpr)
         (|
           eq(ExprPairsTail, nil)
           WriteFile(", ")
           SAL_Out_Qualif_for_Maps(Tid, D, R)
           WriteFile("empty_map")
         ||
           WriteFile(", ")
         |)
         SAL_Out_Enum_Map(Tid, D, R, ExprPairsTail)
         WriteFile(")")

  'rule' SAL_Out_Enum_Map(_,_,_, nil):


--------------------------------------------------
'action' SAL_Out_Literal(SAL_VALUE_LITERAL)

  'rule' SAL_Out_Literal(bool_true):
         WriteFile("TRUE")

  'rule' SAL_Out_Literal(bool_false):
         WriteFile("FALSE")

  'rule' SAL_Out_Literal(integ(IdentInt)):
         id_to_string(IdentInt -> StringInt)
         WriteFile(StringInt)

  'rule' SAL_Out_Literal(nil):


--------------------------------------------------

'action' SAL_Out_Connective(SAL_LOGIC_CONNECTIVE)

  'rule' SAL_Out_Connective(implies):
         WriteFile(" => ")
         WritelnFile(1)
 
  'rule' SAL_Out_Connective(or):
         WriteFile(" OR")
         WritelnFile(1)
 
  'rule' SAL_Out_Connective(and):
         WriteFile(" AND")
         WritelnFile(1)
 
  'rule' SAL_Out_Connective(not):
         WriteFile(" NOT ")


--------------------------------------------------
'action' SAL_Out_BindingOp(SAL_BINDING_OP)
 
  'rule' SAL_Out_BindingOp(lambda):
         WriteFile(" LAMBDA ")
 
  'rule' SAL_Out_BindingOp(forall):
         WriteFile(" FORALL ")
 
  'rule' SAL_Out_BindingOp(exists):
         WriteFile(" EXISTS ")
 
  'rule' SAL_Out_BindingOp(exists1):
         WriteFile(" EXISTS ")
 
  'rule' SAL_Out_BindingOp(nil):
         Putmsg("SAL Internal Error (gen_code): BindingOp nil")
         Putnl()


--------------------------------------------------
'action' SAL_Out_Tuple_Expr(SAL_VALUE_EXPRS)

  'rule' SAL_Out_Tuple_Expr(list(SALExpr, SALExprsTail)):
         SAL_Out_Expr(SALExpr)
         [|
           ne(SALExprsTail, nil)
           WriteFile(", ")
         |]
         SAL_Out_Tuple_Expr(SALExprsTail)

  'rule' SAL_Out_Tuple_Expr(nil):


--------------------------------------------------
/* SEE THIS!!! Seems not to be necessary!
'action' SAL_Out_IdOps(SAL_ID_OP)

  'rule' SAL_Out_IdOps(list(IdOp, IdOpsTail)):
         SAL_Out_IdOp(IdOp)
         [|
           ne(IdOpsTail, nil)
           WriteFile(", ")
         |]
         SAL_Out_IdOps(IdOpsTail)

  'rule' SAL_Out_IdOps(nil):

*/




--------------------------------------------------
/*
'action' Out_Projections(PROJECTION_LIST)

  'rule' Out_Projections(list(Projection, ProjectionsTail)):
         WriteFile("`")
         Int_to_string(Projection -> ProjectionString)
         WriteFile(ProjectionString)
         Out_Projections(ProjectionsTail)

  'rule' Out_Projections(nil):
 
*/


--------------------------------------------------
-- Out Bindings, Setbindings, Arguments,
-- LetBindings, LambdaBindings
--------------------------------------------------
--------------------------------------------------
/*NOT USED so far
--------------------------------------------------
'action' SAL_Out_Arguments_List(SAL_ARGUMENTS_LIST, IDENT)

  'rule' SAL_Out_Arguments_List(list(Arguments, ArgumentsListTail), IdProd):
         SAL_Out_Arguments(Arguments, IdProd)
         SAL_Out_Arguments_List(ArgumentsListTail, IdProd)

  'rule' SAL_Out_Arguments_List(nil, IdProd):
        
*/
--------------------------------------------------
'action' SAL_Out_Arguments(SAL_ARGS)

  'rule' SAL_Out_Arguments(sal_argument(Exprs)):
         WriteFile("(")
         SAL_Out_Tuple_Expr(Exprs)
         WriteFile(")")
/*
--------------------------------------------------
'action' Out_Arguments_from_Params(SAL_FORMAL_FUN_PARAMETERS)

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

'action' Out_Arg(SAL_BINDING)

  'rule' Out_Arg(typed_id(IdOp, _)):
         SAL_Out_IdOp(IdOp)

  'rule' Out_Arg(prod_binding(BS)):
         WriteFile("(")
         Out_Argument_from_Param(BS)
         WriteFile(")")

  'rule' Out_Arg(typed_prod(BS, _)):
         Out_Arg(prod_binding(BS))
*/

--------------------------------------------------
'action' SAL_Add_ids_to_domain(SAL_BINDINGS, SAL_LET_BINDINGS ->
                                         SAL_TYPE_EXPR, SAL_LET_BINDINGS)

-- assumes bindings are typed
  'rule' SAL_Add_ids_to_domain(list(B, nil), LBS -> Type, LBS1):
         
         where(B -> sal_typed_prod(_, Bind,TypeExpr1))
         SALBinding_to_type(B, LBS -> Id, T, LBS1)
         where(user_defined(sal_tuple_type(list(sal_tuple(T),nil))) -> Type)


  'rule' SAL_Add_ids_to_domain(list(B, BS), LBS ->
         user_defined(sal_tuple_type(list(sal_tuple(T),TL))),LBS2):
         SALBinding_to_type(B, LBS -> Id, T, LBS1)
         SAL_Add_ids_to_domain(BS, LBS1 -> 
            user_defined(sal_tuple_type(TL)), LBS2)

--------------------------------------------------

--------------------------------------------------
'action' SALBinding_to_type(SAL_BINDING, SAL_LET_BINDINGS ->
                                         IDENT, SAL_TYPE_EXPR, SAL_LET_BINDINGS)
-- assumes all bindings are typed

  'rule' SALBinding_to_type(sal_typed_prod(_, BS, T), LBS -> IdProd, T, LBS1):
         SAL_Gen_Prod_Ident("" -> IdProd)
         SAL_Gen_LetBindings(IdProd, BS, LBS -> LBS1)
         

  'rule' SALBinding_to_type(sal_typed_id(_, id(Id), T), LBS -> Id, T, LBS):

--------------------------------------------------

--------------------------------------------------
'action' SAL_Out_Params(SAL_FORMAL_FUN_PARAMETERS)

  'rule' SAL_Out_Params(list(formal_param(Ident, TElem,_), Params))
         SAL_Out_Ident(Ident)
         WriteFile(" : ")
         SAL_Out_Type_Expr(TElem)
         [|
            ne(Params, nil)
            WriteFile(", ")
            SAL_Out_Params(Params)
         |]
         
  'rule' SAL_Out_Params(nil)
/*
'action' SAL_Out_Params(SAL_FORMAL_FUN_PARAMETERS,
                         SAL_TYPE_ELEM, SAL_LET_BINDINGS -> SAL_LET_BINDINGS, SAL_TYPE_ELEM)

  'rule' SAL_Out_Params(list(Bindings, ParamsTail),
             type_elem(Pos,Qualif,user_defined(sal_fun_type(Domain, Result))),
                         Letbindings -> Letbindingsout, Resultout):
         WriteFile("(")
         SAL_Out_Bindings(Bindings, Letbindings, Domain -> Letbindings1)
         WriteFile(")")
         SAL_Out_Params(ParamsTail, Result, Letbindings1 ->
                                     Letbindingsout, Resultout)

        
  'rule' SAL_Out_Params(nil, TypeExpr, Letbindings ->
                              Letbindings, TypeExpr):
*/

--------------------------------------------------
--  Auxiliary Actions
---------------------------------------------------
/*
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


*/
--------------------------------------------------
--  Generate Product Identifier
---------------------------------------------------
--------------------------------------------------
'action' SAL_Gen_Prod_Ident(STRING -> IDENT)
         
  'rule' SAL_Gen_Prod_Ident(IdStrng -> IdProd):
         (|
           eq(IdStrng, "")
           where("prod" -> IdStrng1)
         ||
           where(IdStrng -> IdStrng1)
         |)
         SAL_ProdIndex -> SAL_ProdIndex1
         SAL_ProdIndex <- SAL_ProdIndex1 + 1
         SAL_ProdIndex -> SAL_ProdIndex2
         Int_to_string(SAL_ProdIndex2 -> ProdIndxStrng)
         Concatenate3(IdStrng1, ProdIndxStrng, "_" -> ProdIdStrng)
         string_to_id(ProdIdStrng -> IdProd)
         SAL_Add_1_to_ProdIndex2


--------------------------------------------------
'action' SAL_Add_1_to_ProdIndex2
         
  'rule' SAL_Add_1_to_ProdIndex2
         SAL_ProdIndex2 -> SAL_ProdIndex1
         SAL_ProdIndex2 <- SAL_ProdIndex1 + 1


---------------------------------------------------------------
'action' SAL_PrintIdOp(SAL_ID_OP)

  'rule' SAL_PrintIdOp(id(Id)):
--       Putmsg("IdOp is ")
         Print_id(Id)

  'rule' SAL_PrintIdOp(sal_op_symb(Op)):
         Putmsg("IdOp: op_symb")
         Putnl()
         print(Op)

  'rule' SAL_PrintIdOp(nil):
         print("IdOp: nil")

--------------------------------------------------------------------------

'action' SAL_Generate_Binding_Namespace(SAL_LET_BINDINGS -> BINDING_NAMESPACE)

  'rule' SAL_Generate_Binding_Namespace(list(sal_let_binds(SLBS, sal_named_val(Name)), Rest) -> Env)
         SAL_Generate_Ind_Binding_Namespace(0, SLBS, Name -> Env0)
         SAL_Generate_Binding_Namespace(Rest -> Env1)
         SAL_Catenate_Namespaces(Env0, Env1 -> Env)

  'rule' SAL_Generate_Binding_Namespace(nil -> nil)


'action' SAL_Generate_Ind_Binding_Namespace(INT, SAL_LETBINDS, SAL_NAME -> BINDING_NAMESPACE)
         
  'rule' SAL_Generate_Ind_Binding_Namespace(Index, list(sal_let_idop(IdOp,
                                  SB, TElem), Rest), Name -> Result):
         where(binding_elem(Index, IdOp, Name) -> Res1)
--       where(NewIndex <- Index + 1)
         SAL_Generate_Ind_Binding_Namespace(Index+1, Rest, Name -> Res2)
         where(BINDING_NAMESPACE'list(Res1, Res2) -> Result)

  'rule' SAL_Generate_Ind_Binding_Namespace(_, nil,_ -> nil)

'action' SAL_Catenate_Namespaces(BINDING_NAMESPACE,BINDING_NAMESPACE
                                                -> BINDING_NAMESPACE)

  'rule' SAL_Catenate_Namespaces(list(H,T), Tail -> Result)
         SAL_Catenate_Namespaces(T, Tail -> Res)
         where(BINDING_NAMESPACE'list(H, Res) -> Result)

  'rule' SAL_Catenate_Namespaces(nil, Tail -> Tail)

-----------------------------------------------------------------
'action' look_up_binding_in_namespace(SAL_ID_OP -> BINDING_ELEM)

  'rule' look_up_binding_in_namespace(IdOp -> BE)
         Current_LBS_Env -> Env
--juan
         internal_look_up_binding_in_namespace(IdOp, Env -> BE)


'action' internal_look_up_binding_in_namespace(SAL_ID_OP, 
                         BINDING_NAMESPACE_STACK -> BINDING_ELEM)
  'rule' internal_look_up_binding_in_namespace(IdOp, list(H,T) ->  Result)
         internal_look_up_binding_in_namespace1(IdOp, H -> Result1)
         (|
            ne(Result1, nil)
            where(Result1 -> Result)
         ||
            eq(Result1, nil)
            internal_look_up_binding_in_namespace(IdOp, T -> Result2)
            where(Result2 -> Result)
         |)
                

  'rule' internal_look_up_binding_in_namespace(_, nil -> nil)

'action' internal_look_up_binding_in_namespace1(SAL_ID_OP,
                               BINDING_NAMESPACE -> BINDING_ELEM)

  'rule' internal_look_up_binding_in_namespace1(IdOp, list(H,T) -> Result)
         (|
            SAL_match_Names_with_Binding_Elem(H,IdOp)
            where(H -> Result)
         ||
            internal_look_up_binding_in_namespace1(IdOp, T -> Result)
         |)


  'rule' internal_look_up_binding_in_namespace1(_, nil -> nil)

--------------------------------------------------------------------------------
-- SAL_match_Names_with_Binding_Elem
--------------------------------------------------------------------------------
-- Verifies if there is a match in the binding element with the name
-- passed as argument...
--------------------------------------------------------------------------------

'condition' SAL_match_Names_with_Binding_Elem(BINDING_ELEM, SAL_ID_OP)

     'rule' SAL_match_Names_with_Binding_Elem(
              binding_elem(_, _,id_op(IdOp2)), IdOp):
            eq(IdOp, IdOp2)

     'rule' SAL_match_Names_with_Binding_Elem(nested_elem(_,id_op(IdOp2),_), IdOp):
            eq(IdOp, IdOp2)

     'rule' SAL_match_Names_with_Binding_Elem(nested_elem(_,_,BElem), IdOp):
            SAL_match_Names_with_Binding_Elem(BElem, IdOp)

--------------------------------------------------------------------------------
'action' SAL_Out_Binding_Element(BINDING_ELEM)

  'rule' SAL_Out_Binding_Element(binding_elem(Index, ArgName, T))
         SAL_Out_IdOp(ArgName)
         WriteFile(".")
         Int_to_string(Index -> Str)
         WriteFile(Str)

  'rule' SAL_Out_Binding_Element(nested_elem(Index, _,BElem))
         SAL_Out_Binding_Element(BElem)
         WriteFile(".")
         Int_to_string(Index -> Str)
         WriteFile(Str)

--------------------------------------------------------------------------------
'action' SAL_Out_Variables(SAL_VAR_DECLS)

  'rule' SAL_Out_Variables(list(var_decl(Pos, Id,_,Type), Rest))
         SAL_Out_Variable_Id(Id)
         WriteFile(" : ")
         SAL_Out_Type_Expr(Type)
          [|
            ne(Rest,nil)
            WriteFile(",")
            WriteFile("\n")
         |]
         SAL_Out_Variables(Rest)

  'rule' SAL_Out_Variables(nil)
--------------------------------------------------------------------------------
'action' SAL_Out_Initialization(SAL_INITIALIZATIONS)

  'rule' SAL_Out_Initialization(list(init(VarId, Expr), Rest))
         VarId'Ident -> Id
         WriteIndntFile(4)
         SAL_Out_Variable_Id(Id)
         WriteFile(" = ")
         SAL_Out_Expr(Expr)
         WriteFile(";\n")
         SAL_Out_Initialization(Rest)

  'rule' SAL_Out_Initialization(nil)
--------------------------------------------------------------------------------
'action' SAL_Out_Transitions(SAL_TRANSITIONS)

  'rule' SAL_Out_Transitions(list(H,T))
         SAL_Out_Transition(H)
         [|
            ne(T,nil)
            WriteFile("\n")
            WriteIndntFile(2)
            WriteFile("[]")
         |]
         WriteFile("\n")
         SAL_Out_Transitions(T)

  'rule' SAL_Out_Transitions(nil)

'action' SAL_Out_Transition(SAL_TRANSITION)
  'rule' SAL_Out_Transition(transition(OptIdent, Guard,Cmnds))
         WriteIndntFile(4)
         [|
             where(OptIdent -> ident(Id))
             SAL_Out_Ident(Id)
             WriteFile(" :\n")
             WriteIndntFile(4)
         |]
         SAL_Out_Expr(Guard)
         WriteFile(" -->\n")
         SAL_Out_Commands(Cmnds)

  'rule' SAL_Out_Transition(comprehended(Binds, Pos, Trans))
         WriteFile("([] (")
         SAL_Out_Bindings(Binds, nil, nil -> LBS)
         WriteFile("):\n")
         [|
           ne(LBS, nil)
           WriteFile("LET ")
           SAL_Out_LetBindings(LBS)
           WriteFile(" IN ")
         |]
         SAL_Out_Transition(Trans)
         WriteFile(")\n")

  'rule' SAL_Out_Transition(cc_comprehended(Binds, LetExpr1))
         WriteFile("([] (")
         SAL_Out_Bindings(Binds, nil, nil -> LBS)
         WriteFile("):\n")
         [|
           ne(LBS, nil)
           WriteFile("LET ")
           SAL_Out_LetBindings(LBS)
           WriteFile(" IN ")
         |]
	 (|
	    where(LetExpr1 -> sal_esp_let_expr(Ident, TElem, InitExpr, Transition))
	    where(Transition -> transition(OptIdent, Guard,Cmnds))
	    where(OptIdent -> ident(Id))
            SAL_Out_Ident(Id)
            WriteFile(" :\n")
            WriteIndntFile(4)
	    where(sal_esp_let_expr(Ident, TElem, InitExpr, transition(nil, Guard,Cmnds)) -> LetExpr)
	 ||
	    where(LetExpr1 -> LetExpr)
	 |)
         SAL_Out_Expr(LetExpr)
         WriteFile(")\n")


  'rule' SAL_Out_Transition(else_trans(OptIdent, Cmnds))
         WriteIndntFile(4)
         [|
             where(OptIdent -> ident(Id))
             SAL_Out_Ident(Id)
             WriteFile(":\n")
             WriteIndntFile(4)
         |]
         WriteFile("ELSE")
         WriteFile(" -->\n")
         SAL_Out_Commands(Cmnds)
         WriteFile("\n")

'action' SAL_Out_Commands(SAL_VALUE_EXPRS)

  'rule' SAL_Out_Commands(list(Expr, Exprs))
         WriteIndntFile(6)
         SAL_Out_Expr(Expr)
         [|
            ne(Exprs,nil)
            WriteFile(";\n")
         |]
         SAL_Out_Commands(Exprs)

  'rule' SAL_Out_Commands(nil)

--------------------------------------------------------------------------------------------
-- Gen_SAL_Macro_Code
--------------------------------------------------------------------------------------------

'action' Gen_SAL_Macro_Code(IDENT, MACRO_CONSTANTS)

  'rule' Gen_SAL_Macro_Code(Id, list(M, Rest))
         SAL_Process_Macro_Constant(Id, M)
         Gen_SAL_Macro_Code(Id, Rest)

  'rule' Gen_SAL_Macro_Code(Id, nil)

'action' SAL_Process_Macro_Constant(IDENT, MACRO_CONSTANT)

  'rule' SAL_Process_Macro_Constant(Id, macro_set_cmd(SetTid, _))
         SetTid'TExpr -> SetType
         where(SetType -> rsl_built_in(sal_finite_set(Tid, ElemType)))
         WriteFile("include(`set_prelude')\n")
         WriteFile("__Generate_Set_Ops(")
         SAL_Out_Ident(Id)
         WriteFile(", ")
         SAL_Out_Type_Expr(SetType)
         WriteFile(", ")
         SAL_Out_Type_Expr(ElemType)
         WriteFile(")")

  'rule' SAL_Process_Macro_Constant(Id, macro_cc_set_cmd(SetTid,
						ElemType, LiftedElemType))
         WriteFile("include(`set_cc_prelude')\n")
         WriteFile("__Generate_CC_Set_Ops(")
         SAL_Out_Ident(Id)
         WriteFile(", ")
	 -- Set type:
         SAL_Out_Type_from_Tid(SetTid)
         WriteFile(", ")
	 -- Lifted Elem's type
	 where(LiftedElemType -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,ETid)),_)))
	 SAL_Out_Type_from_Tid(ETid)
	 WriteFile(", ")
	 -- Set constructor:
	 SetTid'Constructor -> vid(Const)
	 SAL_Out_Value_from_Vid(Const)
	 WriteFile(", ")
	 -- Set nav constructor:
	 SetTid'DefaultNav -> vid(NavConst)
	 SAL_Out_Value_from_Vid(NavConst)
	 WriteFile(", ")
	 -- The type's non-nav accesor
         SetTid'Lifted_fields -> Fields
         SAL_Find_Accesor_in_Fields(Fields, Const -> AccesorVid)
         SAL_Out_Qualif_from_Vid(AccesorVid)
         AccesorVid'IdOp -> AccIdOp
         SAL_Out_IdOp(AccIdOp)
         WriteFile(", ")
	 -- The type's nav accesor
         SAL_Find_Accesor_in_Fields(Fields, NavConst -> NavAccesorVid)
         SAL_Out_Qualif_from_Vid(NavAccesorVid)
         NavAccesorVid'IdOp -> NavAccIdOp
         SAL_Out_IdOp(NavAccIdOp)
         WriteFile(", ")
	 -- ELEMENT TYPE elements:
	 -- Nav-constructor:
	 ETid'DefaultNav -> vid(ENavConst)
	 SAL_Out_Value_from_Vid(ENavConst)
	 WriteFile(", ")
	 -- Nav-value accesor:
	 ETid'Lifted_fields -> EFields
	 SAL_Find_Accesor_in_Fields(EFields, ENavConst -> ENavAccesorVid)
         SAL_Out_Value_from_Vid(ENavAccesorVid)
         WriteFile(", ")
         -- Bool lifted result:
         Default_Bool_Tid -> BTid
         BTid'Lifted_Tid -> tid(LBTid)
         SAL_Out_Qualif_from_Tid(LBTid)
         LBTid'Ident -> BIdent
         SAL_Out_Ident(BIdent)
         WriteFile(", ")
         -- Bool non-nav constructor
         LBTid'Constructor -> vid(BConsVid)
         SAL_Out_Qualif_from_Vid(BConsVid)
         BConsVid'IdOp -> BIdOp
         SAL_Out_IdOp(BIdOp)
	 WriteFile(", ")
	 -- Bool nav-constructor
	 LBTid'DefaultNav -> vid(BNavConstVid)
	 SAL_Out_Qualif_from_Vid(BNavConstVid)
         BNavConstVid'IdOp -> BNavIdOp
         SAL_Out_IdOp(BNavIdOp)
	 WriteFile(", ")
	 -- Bool non-nav accesor:
	 LBTid'Lifted_fields -> BFields
         SAL_Find_Accesor_in_Fields(BFields, BConsVid -> BAccesorVid)
	 SAL_Out_Value_from_Vid(BAccesorVid)
	 WriteFile(", ")
	 -- ELEMENT TYPE non-nav accessor
	 ETid'Constructor -> vid(EConst)
	 SAL_Find_Accesor_in_Fields(EFields, EConst -> EAccesorVid)
	 SAL_Out_Value_from_Vid(EAccesorVid)
	 WriteFile(", ")
	 -- non-lifted ELEMENT TYPE
	 SAL_Out_Type_Expr(ElemType) 
         WriteFile(")")

  'rule' SAL_Process_Macro_Constant(Id, macro_map_cmd(MapTid, TExpr,DomSetCid,RngSetCid,DomSetTid,RngSetTid))
         MapTid'TExpr -> MapType
         where(MapType -> rsl_built_in(sal_finite_map(_,DomType,RngType)))
         where(TExpr -> user_defined(sal_variant_type(Dparts)))
         where(Dparts -> list(NilPart,list(ValPart,nil)))
         -- Extracting the Ids int the MAP_RANGE part:
         -- nil part:
         where(NilPart -> sal_part(NilConst,_))
         where(NilConst -> sal_construc(_,NilVid,_,_))
         -- val part
         where(ValPart -> sal_part(ValConst,_))
         where(ValConst -> sal_construc(_,ValVid,Destrs,_))
         -- real RANGE type (got from the destructor)
         where(Destrs -> list(sal_destructor(_,DestrVid,SALRngType,_), nil))

         WriteFile("include(`map_prelude')\n")
         WriteFile("__Generate_Map_Ops(")
         SAL_Out_Ident(Id)
         WriteFile(", ")
         SAL_Out_Type_Expr(MapType)
         WriteFile(", ")
         SAL_Out_Type_Expr(DomType)
         WriteFile(", ")
         SAL_Out_Value_from_Vid(NilVid)
         WriteFile(", ")
         SAL_Out_Value_from_Vid(ValVid)
         WriteFile(", ")
         DomSetCid'Ident -> Id1
         SAL_Out_Ident(Id1)
         WriteFile(", ")
         RngSetCid'Ident -> Id2
         SAL_Out_Ident(Id2)
         WriteFile(", ")
         SAL_Out_Type_Expr(SALRngType)
         WriteFile(", ")
         SAL_Out_Type_from_Tid(DomSetTid)
         WriteFile(", ")
         SAL_Out_Type_from_Tid(RngSetTid)
         WriteFile(", ")
         SAL_Out_Value_from_Vid(DestrVid)
         WriteFile(")")

  'rule' SAL_Process_Macro_Constant(Id, macro_cc_map_cmd(MapTid,
			DomTid,RngTid,DomSetTid,RngSetTid, InvApplVid,
			D, R, MD, MR, MapRangeTid))
         WriteFile("include(`map_cc_prelude')\n")
         WriteFile("__Generate_Map_CC_Ops(")
         SAL_Out_Ident(Id)
         WriteFile(", ")
	 -- the map type: (1)
	 SAL_Out_Type_from_Tid(MapTid)
	 WriteFile(", ")
	 -- map non-nav constructor: (2)
	 MapTid'Constructor -> vid(MapConst)
	 SAL_Out_Value_from_Vid(MapConst)
	 WriteFile(", ")
	 -- map non-nav value accessor: (3)
	 MapTid'Lifted_fields -> MapFields
         SAL_Find_Accesor_in_Fields(MapFields, MapConst -> MapAccesorVid)
	 SAL_Out_Value_from_Vid(MapAccesorVid)
	 WriteFile(", ")
	 -- map nav constructor: (4)
	 MapTid'DefaultNav -> vid(MapNavConst)
	 SAL_Out_Value_from_Vid(MapNavConst)
	 WriteFile(", ")
	 -- map nav value accessor: (5)
	 SAL_Find_Accesor_in_Fields(MapFields, MapNavConst -> MapNavAccesorVid)
	 SAL_Out_Value_from_Vid(MapNavAccesorVid)
	 WriteFile(", ")
	 -- domain type: (6)
	 SAL_Out_Type_from_Tid(DomTid)
	 WriteFile(", ")
	 -- Domain type non-nav constructor: (7)
	 DomTid'Constructor -> vid(DomConst)
	 SAL_Out_Value_from_Vid(DomConst)
	 WriteFile(", ")
	 -- Domain type nav constructor: (8)
	 DomTid'DefaultNav -> vid(DomNavConst)
	 SAL_Out_Value_from_Vid(DomNavConst)
	 WriteFile(", ")
	 -- Domain type nav value accesor: (9)
	 DomTid'Lifted_fields -> DomFields
	 SAL_Find_Accesor_in_Fields(DomFields, DomNavConst -> DomNavAccesorVid)
	 SAL_Out_Value_from_Vid(DomNavAccesorVid)
	 WriteFile(", ")
	 -- Range type (10):
	 SAL_Out_Type_from_Tid(RngTid)
	 WriteFile(", ")
	 -- Range type non-nav constructor (11):
	 RngTid'Constructor -> vid(RngConst)
	 SAL_Out_Value_from_Vid(RngConst)
	 WriteFile(", ")
	 -- Range type nav constructor: (12)
	 RngTid'DefaultNav -> vid(RngNavConst)
	 SAL_Out_Value_from_Vid(RngNavConst)
	 WriteFile(", ")
	 -- Range type nav value accesor: (13)
	 RngTid'Lifted_fields -> RngFields
	 SAL_Find_Accesor_in_Fields(RngFields, RngNavConst -> RngNavAccesorVid)
	 SAL_Out_Value_from_Vid(RngNavAccesorVid)
	 WriteFile(", ")
	 -- Invalid application nav value: (14)
	 SAL_Out_Value_from_Vid(InvApplVid)
	 WriteFile(", ")
	 -- Dom-set type: (15)
	 SAL_Out_Type_from_Tid(DomSetTid)
	 WriteFile(", ")
	 -- Dom-set nav constructor (16)
	 DomSetTid'DefaultNav -> vid(DomSetNavConst)
	 SAL_Out_Value_from_Vid(DomSetNavConst)
	 WriteFile(", ")
	 -- Dom-set nav value accesor: (17)
	 DomSetTid'Lifted_fields -> DomSetFields
	 SAL_Find_Accesor_in_Fields(DomSetFields, DomSetNavConst -> DomSetNavAccesorVid)
	 SAL_Out_Value_from_Vid(DomSetNavAccesorVid)
	 WriteFile(", ")
	 -- Dom-set operation context (18)
	 DomSetTid'OperationsCid -> cid(DomSetOpsCid)
	 DomSetOpsCid'Ident -> DomOpsCidIdent
	 SAL_Out_Ident(DomOpsCidIdent)
	 WriteFile(", ")
	 -- Bool OPS context:
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 LBTid'OperationsCid -> cid(BoolOpsCid)
	 BoolOpsCid'Ident -> BoolOpsCidIdent
	 SAL_Out_Ident(BoolOpsCidIdent)
	 WriteFile(", ")
	 -- Rng-set type: (20)
	 SAL_Out_Type_from_Tid(RngSetTid)
	 WriteFile(", ")
	 -- Rng-set non-nav constructor: (21)
	 RngSetTid'Constructor -> vid(RngSetConst)
	 SAL_Out_Value_from_Vid(RngSetConst)
	 WriteFile(", ")
	 -- Rng-set nav constructor (22)
	 RngSetTid'DefaultNav -> vid(RngSetNavConst)
	 SAL_Out_Value_from_Vid(RngSetNavConst)
	 WriteFile(", ")
	 -- Bool non nav constructor (23):
	 LBTid'Constructor -> vid(BoolConst)
	 SAL_Out_Value_from_Vid(BoolConst)
	 WriteFile(", ")
	 -- Dom-set non-nav constructor: (24)
	 DomSetTid'Constructor -> vid(DomSetConst)
	 SAL_Out_Value_from_Vid(DomSetConst)
	 WriteFile(", ")
	 -- Bool type (25)
	 SAL_Out_Type_from_Tid(LBTid)
	 WriteFile(", ")
	 -- Bool nav constructor: (26)
	 LBTid'DefaultNav -> vid(BoolNavConst)
	 SAL_Out_Value_from_Vid(BoolNavConst)
	 WriteFile(", ")
	 -- non-lifted domain type (27)
	 SAL_Out_Type_Expr(D)
	 WriteFile(", ")
	 -- domain type non-nav accessor (28)
	 SAL_Find_Accesor_in_Fields(DomFields, DomConst -> DomAccesorVid)
	 SAL_Out_Value_from_Vid(DomAccesorVid)
	 WriteFile(", ")
	 -- range type non-nav accessor (29)
	 SAL_Find_Accesor_in_Fields(RngFields, RngConst -> RngAccesorVid)
	 SAL_Out_Value_from_Vid(RngAccesorVid)
	 WriteFile(", ")
	 -- non-lifted range type+nil (30)
	 SAL_Out_Type_from_Tid(MapRangeTid)
	 WriteFile(", ")
	 -- range type+nil non-nil accessor (31)
	 MapRangeTid'TExpr -> MapRangeTypeExpr
	 where(MapRangeTypeExpr -> user_defined(sal_variant_type(DTParts)))
	 where(DTParts -> list(Nil_Part, list(Val_Part, nil)))
	 where(Val_Part -> sal_part(Val_Construct,_))
	 where(Val_Construct -> sal_construc(_,ValVid,Destrs,_))
         where(Destrs -> list(sal_destructor(_,DestrVid,SALRngType,_), nil)) 
         where(Nil_Part -> sal_part(Nil_Construct,_))
         where(Nil_Construct -> sal_construc(_,NilVid,_,_))
	 SAL_Out_Value_from_Vid(DestrVid)
	 WriteFile(", ")
	 -- range type+nil nil constructor (32)
	 SAL_Out_Value_from_Vid(NilVid)
	 WriteFile(", ")
	 -- range type+nil non-nil constructor (33)
	 SAL_Out_Value_from_Vid(ValVid)
	 WriteFile(", ")
	 -- maximal non-lifted range types (34)
	 SAL_Out_Type_Expr(MR)
	 WriteFile(", ")
	 -- maximal non-lifted domain type (35)
	 SAL_Out_Type_Expr(MD)
WriteFile(", ")
--Normal range type (36)
SAL_Out_Type_Expr(R)
         WriteFile(")")

  'rule' SAL_Process_Macro_Constant(Id, macro_int_cmd(Tid))
         Tid'Cid -> cid(Cid)
         Cid'Ident -> CidIdent
         WriteFile("include(`int_prelude')\n")
         WriteFile("__Generate_Int_Ops(")
         SAL_Out_Ident(Id)
         WriteFile(", ")
         SAL_Out_Ident(CidIdent)
         WriteFile("!")
         Tid'Ident -> IntId
         SAL_Out_Ident(IntId)
         WriteFile(")")

  'rule' SAL_Process_Macro_Constant(Id, macro_int_cc_cmd(Tid, BoolTid, Div_by_zero_vid))
         Tid'Cid -> cid(Cid)
         Cid'Ident -> CidIdent
         WriteFile("include(`int_cc_prelude')\n")
         WriteFile("__Generate_Int_CC_Ops(")
         SAL_Out_Ident(Id)
         WriteFile(", ")
         -- The type's name
         SAL_Out_Ident(CidIdent)
         WriteFile("!")
         Tid'Ident -> IntId
         SAL_Out_Ident(IntId)
         WriteFile(", ")
         -- The type's proper constructor
         Tid'Constructor -> vid(ConsVid)
         SAL_Out_Qualif_from_Vid(ConsVid)
         ConsVid'IdOp -> IdOp
         SAL_Out_IdOp(IdOp)
         WriteFile(", ")
	 -- The type's nav constructor
	 Tid'DefaultNav -> vid(NavConstVid)
	 SAL_Out_Qualif_from_Vid(NavConstVid)
         NavConstVid'IdOp -> NavIdOp
         SAL_Out_IdOp(NavIdOp)
	 WriteFile(", ")
         -- The type's non-nav accesor
         Tid'Lifted_fields -> Fields
         SAL_Find_Accesor_in_Fields(Fields, ConsVid -> AccesorVid)
         SAL_Out_Qualif_from_Vid(AccesorVid)
         AccesorVid'IdOp -> AccIdOp
         SAL_Out_IdOp(AccIdOp)
         WriteFile(", ")
	 -- The type's nav accesor
         SAL_Find_Accesor_in_Fields(Fields, NavConstVid -> NavAccesorVid)
         SAL_Out_Qualif_from_Vid(NavAccesorVid)
         NavAccesorVid'IdOp -> NavAccIdOp
         SAL_Out_IdOp(NavAccIdOp)
         WriteFile(", ")
         -- Bool lifted result:
         Default_Bool_Tid -> BTid
         BTid'Lifted_Tid -> tid(LBTid)
         SAL_Out_Qualif_from_Tid(LBTid)
         LBTid'Ident -> BIdent
         SAL_Out_Ident(BIdent)
         WriteFile(", ")
         -- Bool lifted constructor
         LBTid'Constructor -> vid(BConsVid)
         SAL_Out_Qualif_from_Vid(BConsVid)
         BConsVid'IdOp -> BIdOp
         SAL_Out_IdOp(BIdOp)
	 WriteFile(", ")
	 -- Bool nav-constructor
	 LBTid'DefaultNav -> vid(BNavConstVid)
	 SAL_Out_Qualif_from_Vid(BNavConstVid)
         BNavConstVid'IdOp -> BNavIdOp
         SAL_Out_IdOp(BNavIdOp)
	 WriteFile(", ")
	 -- nav value for division-by-zero
	 SAL_Out_Qualif_from_Vid(Div_by_zero_vid)
         Div_by_zero_vid'IdOp -> Div_by_zero_vidIdOp
         SAL_Out_IdOp(Div_by_zero_vidIdOp)
         WriteFile(")")

  'rule' SAL_Process_Macro_Constant(Id, macro_bool_cc_cmd(Tid))
         Tid'Cid -> cid(Cid)
         Cid'Ident -> CidIdent
         WriteFile("include(`bool_cc_prelude')\n")
         WriteFile("__Generate_Bool_CC_Ops(")
         SAL_Out_Ident(Id)
         WriteFile(", ")
         -- The type's name
         SAL_Out_Ident(CidIdent)
         WriteFile("!")
         Tid'Ident -> IntId
         SAL_Out_Ident(IntId)
         WriteFile(",")
	 -- The non-nav constructor:
	 Tid'Constructor -> vid(ConsVid)
         SAL_Out_Qualif_from_Vid(ConsVid)
         ConsVid'IdOp -> IdOp
         SAL_Out_IdOp(IdOp)
         WriteFile(", ")
	 -- The type's nav constructor
	 Tid'DefaultNav -> vid(NavConstVid)
	 SAL_Out_Qualif_from_Vid(NavConstVid)
         NavConstVid'IdOp -> NavIdOp
         SAL_Out_IdOp(NavIdOp)
	 WriteFile(", ")
         -- The type's non-nav accesor
         Tid'Lifted_fields -> Fields
         SAL_Find_Accesor_in_Fields(Fields, ConsVid -> AccesorVid)
         SAL_Out_Qualif_from_Vid(AccesorVid)
         AccesorVid'IdOp -> AccIdOp
         SAL_Out_IdOp(AccIdOp)
         WriteFile(")")

  'rule' SAL_Process_Macro_Constant(Id, macro_type_cc_cmd(Tid))
         Tid'Cid -> cid(Cid)
         Cid'Ident -> CidIdent
         WriteFile("include(`cc_type_prelude')\n")
         WriteFile("__Generate_CC_Types_Ops(")
         SAL_Out_Ident(Id)
         WriteFile(", ")
         -- The type's name
         SAL_Out_Ident(CidIdent)
         WriteFile("!")
         Tid'Ident -> IntId
         SAL_Out_Ident(IntId)
         WriteFile(", ")
         -- The type's proper constructor
         Tid'Constructor -> vid(ConsVid)
         SAL_Out_Qualif_from_Vid(ConsVid)
         ConsVid'IdOp -> IdOp
         SAL_Out_IdOp(IdOp)
         WriteFile(", ")
	 -- The type's nav constructor
	 Tid'DefaultNav -> vid(NavConstVid)
	 SAL_Out_Qualif_from_Vid(NavConstVid)
         NavConstVid'IdOp -> NavIdOp
         SAL_Out_IdOp(NavIdOp)
	 WriteFile(", ")
         -- The type's non-nav accesor
         Tid'Lifted_fields -> Fields
         SAL_Find_Accesor_in_Fields(Fields, ConsVid -> AccesorVid)
         SAL_Out_Qualif_from_Vid(AccesorVid)
         AccesorVid'IdOp -> AccIdOp
         SAL_Out_IdOp(AccIdOp)
         WriteFile(", ")
	 -- The type's nav accesor
         SAL_Find_Accesor_in_Fields(Fields, NavConstVid -> NavAccesorVid)
         SAL_Out_Qualif_from_Vid(NavAccesorVid)
         NavAccesorVid'IdOp -> NavAccIdOp
         SAL_Out_IdOp(NavAccIdOp)
         WriteFile(", ")
         -- Bool lifted result:
         Default_Bool_Tid -> BTid
         BTid'Lifted_Tid -> tid(LBTid)
         SAL_Out_Qualif_from_Tid(LBTid)
         LBTid'Ident -> BIdent
         SAL_Out_Ident(BIdent)
         WriteFile(", ")
         -- Bool lifted constructor
         LBTid'Constructor -> vid(BConsVid)
         SAL_Out_Qualif_from_Vid(BConsVid)
         BConsVid'IdOp -> BIdOp
         SAL_Out_IdOp(BIdOp)
	 WriteFile(", ")
	 -- Bool nav-constructor
	 LBTid'DefaultNav -> vid(BNavConstVid)
	 SAL_Out_Qualif_from_Vid(BNavConstVid)
         BNavConstVid'IdOp -> BNavIdOp
         SAL_Out_IdOp(BNavIdOp)
	 WriteFile(")")

--  'rule' SAL_Process_Macro_Constant(Id, macro_cmd(list, ListTid, Type))

--    'rule' SAL_Process_Macro_Constant(Id, macro_map_cmd(MapTid, TExpr,DomSetCid,RngSetCid,_,_))
           --print(TExpr)

    'rule' SAL_Process_Macro_Constant(Id, macro_array_cmd(ArrayTid, TExpr, DomSetCid, RangeSetCid,_,_))

    'rule' SAL_Process_Macro_Constant(Id, macro_cc_array_cmd(ArrayTid,
			DomTid,RngTid,DomSetTid,RngSetTid, InvApplVid,
			D, R, MD, MR))
         WriteFile("include(`array_cc_prelude')\n")
         WriteFile("__Generate_Array_CC_Ops(")
         SAL_Out_Ident(Id)
         WriteFile(", ")
	 -- the map type: (1)
	 SAL_Out_Type_from_Tid(ArrayTid)
	 WriteFile(", ")
	 -- map non-nav constructor: (2)
	 ArrayTid'Constructor -> vid(ArrayConst)
	 SAL_Out_Value_from_Vid(ArrayConst)
	 WriteFile(", ")
	 -- map non-nav value accessor: (3)
	 ArrayTid'Lifted_fields -> ArrayFields
         SAL_Find_Accesor_in_Fields(ArrayFields, ArrayConst -> ArrayAccesorVid)
	 SAL_Out_Value_from_Vid(ArrayAccesorVid)
	 WriteFile(", ")
	 -- map nav constructor: (4)
	 ArrayTid'DefaultNav -> vid(ArrayNavConst)
	 SAL_Out_Value_from_Vid(ArrayNavConst)
	 WriteFile(", ")
	 -- map nav value accessor: (5)
	 SAL_Find_Accesor_in_Fields(ArrayFields, ArrayNavConst -> ArrayNavAccesorVid)
	 SAL_Out_Value_from_Vid(ArrayNavAccesorVid)
	 WriteFile(", ")
	 -- domain type: (6)
	 SAL_Out_Type_from_Tid(DomTid)
	 WriteFile(", ")
	 -- Domain type non-nav constructor: (7)
	 DomTid'Constructor -> vid(DomConst)
	 SAL_Out_Value_from_Vid(DomConst)
	 WriteFile(", ")
	 -- Domain type nav constructor: (8)
	 DomTid'DefaultNav -> vid(DomNavConst)
	 SAL_Out_Value_from_Vid(DomNavConst)
	 WriteFile(", ")
	 -- Domain type nav value accesor: (9)
	 DomTid'Lifted_fields -> DomFields
	 SAL_Find_Accesor_in_Fields(DomFields, DomNavConst -> DomNavAccesorVid)
	 SAL_Out_Value_from_Vid(DomNavAccesorVid)
	 WriteFile(", ")
	 -- Range type (10):
	 SAL_Out_Type_from_Tid(RngTid)
	 WriteFile(", ")
	 -- Range type non-nav constructor (11):
	 RngTid'Constructor -> vid(RngConst)
	 SAL_Out_Value_from_Vid(RngConst)
	 WriteFile(", ")
	 -- Range type nav constructor: (12)
	 RngTid'DefaultNav -> vid(RngNavConst)
	 SAL_Out_Value_from_Vid(RngNavConst)
	 WriteFile(", ")
	 -- Range type nav value accesor: (13)
	 RngTid'Lifted_fields -> RngFields
	 SAL_Find_Accesor_in_Fields(RngFields, RngNavConst -> RngNavAccesorVid)
	 SAL_Out_Value_from_Vid(RngNavAccesorVid)
	 WriteFile(", ")
	 -- Invalid application nav value: (14)
	 SAL_Out_Value_from_Vid(InvApplVid)
	 WriteFile(", ")
	 -- Dom-set type: (15)
	 SAL_Out_Type_from_Tid(DomSetTid)
	 WriteFile(", ")
	 -- Dom-set nav constructor (16)
	 DomSetTid'DefaultNav -> vid(DomSetNavConst)
	 SAL_Out_Value_from_Vid(DomSetNavConst)
	 WriteFile(", ")
	 -- Dom-set nav value accesor: (17)
	 DomSetTid'Lifted_fields -> DomSetFields
	 SAL_Find_Accesor_in_Fields(DomSetFields, DomSetNavConst -> DomSetNavAccesorVid)
	 SAL_Out_Value_from_Vid(DomSetNavAccesorVid)
	 WriteFile(", ")
	 -- Dom-set operation context (18)
	 DomSetTid'OperationsCid -> cid(DomSetOpsCid)
	 DomSetOpsCid'Ident -> DomOpsCidIdent
	 SAL_Out_Ident(DomOpsCidIdent)
	 WriteFile(", ")
	 -- Bool OPS context:
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 LBTid'OperationsCid -> cid(BoolOpsCid)
	 BoolOpsCid'Ident -> BoolOpsCidIdent
	 SAL_Out_Ident(BoolOpsCidIdent)
	 WriteFile(", ")
	 -- Rng-set type: (20)
	 SAL_Out_Type_from_Tid(RngSetTid)
	 WriteFile(", ")
	 -- Rng-set non-nav constructor: (21)
	 RngSetTid'Constructor -> vid(RngSetConst)
	 SAL_Out_Value_from_Vid(RngSetConst)
	 WriteFile(", ")
	 -- Rng-set nav constructor (22)
	 RngSetTid'DefaultNav -> vid(RngSetNavConst)
	 SAL_Out_Value_from_Vid(RngSetNavConst)
	 WriteFile(", ")
	 -- Bool non nav constructor (23):
	 LBTid'Constructor -> vid(BoolConst)
	 SAL_Out_Value_from_Vid(BoolConst)
	 WriteFile(", ")
	 -- Dom-set non-nav constructor: (24)
	 DomSetTid'Constructor -> vid(DomSetConst)
	 SAL_Out_Value_from_Vid(DomSetConst)
	 WriteFile(", ")
	 -- Bool type (25)
	 SAL_Out_Type_from_Tid(LBTid)
	 WriteFile(", ")
	 -- Bool nav constructor: (26)
	 LBTid'DefaultNav -> vid(BoolNavConst)
	 SAL_Out_Value_from_Vid(BoolNavConst)
	 WriteFile(", ")
	 -- non-lifted domain type (27)
	 SAL_Out_Type_Expr(D)
	 WriteFile(", ")
	 -- domain type non-nav accessor (28)
	 SAL_Find_Accesor_in_Fields(DomFields, DomConst -> DomAccesorVid)
	 SAL_Out_Value_from_Vid(DomAccesorVid)
	 WriteFile(", ")
	 -- range type non-nav accessor (29)
	 SAL_Find_Accesor_in_Fields(RngFields, RngConst -> RngAccesorVid)
	 SAL_Out_Value_from_Vid(RngAccesorVid)
	 WriteFile(", ")
	 -- Non-lifted range-type (30)
         SAL_Out_Type_Expr(R)
         WriteFile(", ")
         -- maximal non-lifted range types (31)
	 SAL_Out_Type_Expr(MR)
	 WriteFile(", ")
	 -- maximal non-lifted domain type (32)
	 SAL_Out_Type_Expr(MD)
         WriteFile(")")

           

    'rule' SAL_Process_Macro_Constant(Id, T)
	   Putmsg("Debugging predicate activated in SAL_Process_Macro_Constant\n")
	   print(T)
---------------------------------------------------------------------
-- SAL_Modify_Bindings
---------------------------------------------------------------------
-- This function will generate a modified version of each
-- bounded var in the binding
---------------------------------------------------------------------

'action' SAL_Modify_Bindings(SAL_BINDINGS -> SAL_BINDINGS)

  'rule' SAL_Modify_Bindings(list(H, T) -> list(MH, MT))
         SAL_Modify_Binding(H -> MH)
         SAL_Modify_Bindings(T -> MT)

  'rule' SAL_Modify_Bindings(nil -> nil)

'action' SAL_Modify_Binding(SAL_BINDING -> SAL_BINDING)

  'rule' SAL_Modify_Binding(sal_prod_binding(P, BS) -> sal_prod_binding(P, MBS))
         SAL_Modify_Bindings(BS -> MBS)

  'rule' SAL_Modify_Binding(sal_typed_prod(P, BS, T) -> sal_typed_prod(P, MBS, T))
         SAL_Modify_Bindings(BS -> MBS)

  'rule' SAL_Modify_Binding(sal_typed_id(P, IdOp, T) -> sal_typed_id(P, MIdOp,T))
         (|
             where(IdOp -> id(Ident))
             id_to_string(Ident -> Str)
             Concatenate(Str, "_" -> MStr)
             string_to_id(MStr -> MIdent)
             where(SAL_ID_OP'id(MIdent) -> MIdOp)
         ||
             Putmsg("Internal error: Can not modify name in binding to generate exists1 operator\n")
             where(IdOp -> MIdOp)
         |)

-------------------------------
'action' SAL_Modify_Expr(SAL_BINDINGS, SAL_VALUE_EXPR -> SAL_VALUE_EXPR)

 'rule' SAL_Modify_Expr(BS, sal_product(ValueExprs) -> sal_product(MExprs))
        SAL_Modify_Exprs(BS, ValueExprs -> MExprs)

 'rule' SAL_Modify_Expr(BS, sal_ranged_set(L,R, T) -> sal_ranged_set(ML, MR, T))
        SAL_Modify_Expr(BS, L -> ML)
        SAL_Modify_Expr(BS, R -> MR)

 'rule' SAL_Modify_Expr(BS, sal_enum_set(Tid, T, ES)-> sal_enum_set(Tid, T, MES))
        SAL_Modify_Exprs(BS, ES -> MES)

 'rule' SAL_Modify_Expr(BS, sal_comp_simp_set(SB, E) -> sal_comp_simp_set(SB, ME))
        where(SB -> bindings(BS1))
        SAL_Restrict_Bindings(BS, BS1 -> MBS)
        SAL_Modify_Expr(MBS, E -> ME)

 'rule' SAL_Modify_Expr(BS, sal_comp_set(E, T, SB, Restr) -> sal_comp_set(ME,T,SB,MRestr))
        SAL_Modify_Expr(BS, E -> ME)
        where(SB -> bindings(BS1))
        SAL_Restrict_Bindings(BS, BS1 -> MBS)
        SAL_Modify_Expr(MBS, Restr -> MRestr)

 'rule' SAL_Modify_Expr(BS,sal_ranged_list(D,R) -> sal_ranged_list(MD,MR))
        SAL_Modify_Expr(BS, D -> MD)
        SAL_Modify_Expr(BS, R -> MR)

 'rule' SAL_Modify_Expr(BS, sal_enum_list(ES) -> sal_enum_list(MES))
        SAL_Modify_Exprs(BS, ES -> MES)
--sal_comp_list
 'rule' SAL_Modify_Expr(BS,sal_enum_map(Tid,D,R,EPs) -> sal_enum_map(Tid,D,R,MEPs))
        SAL_Modify_Expr_Pairs(BS, EPs -> MEPs)

 'rule' SAL_Modify_Expr(BS, sal_comp_rng_map(E,Vid,Nid,SB,Restr)-> sal_comp_rng_map(ME,Vid,Nid,SB,MRestr))
        SAL_Modify_Expr(BS, E -> ME)
        where(SB -> bindings(BS1))
        SAL_Restrict_Bindings(BS, BS1 -> MBS)
        SAL_Modify_Expr(MBS, Restr -> MRestr)

--sal_comp_map
 'rule' SAL_Modify_Expr(BS, sal_function(LBS, E) -> sal_function(LBS, ME))
        SAL_Restrict_Bindings_with_Lambda(BS, LBS -> MBS)
        SAL_Modify_Expr(MBS, E -> ME)   

 'rule' SAL_Modify_Expr(BS, sal_list_applic(E, sal_argument(ES)) -> sal_list_applic(ME, sal_argument(MES)))
        SAL_Modify_Expr(BS, E -> ME)
        SAL_Modify_Exprs(BS, ES -> MES)

 'rule' SAL_Modify_Expr(BS, sal_map_applic(Tid, E, sal_argument(ES)) -> sal_map_applic(Tid, ME, sal_argument(MES)))
        SAL_Modify_Expr(BS, E -> ME)
        SAL_Modify_Exprs(BS, ES -> MES)

 'rule' SAL_Modify_Expr(BS, sal_funct_applic(E, sal_argument(ES)) -> sal_funct_applic(ME, sal_argument(MES)))
        SAL_Modify_Expr(BS, E -> ME)
        SAL_Modify_Exprs(BS, ES -> MES)

 'rule' SAL_Modify_Expr(BS, sal_destr_applic(E,E1) -> sal_destr_applic(ME,ME1))
        SAL_Modify_Expr(BS, E -> ME)
        SAL_Modify_Expr(BS, E1 -> ME1)

 'rule' SAL_Modify_Expr(BS, sal_quantified(BO, SB, Restr) -> sal_quantified(BO,SB,MRestr))
        where(SB -> bindings(BS1))
        SAL_Restrict_Bindings(BS, BS1 -> MBS)
        SAL_Modify_Expr(MBS, Restr -> MRestr)

 'rule' SAL_Modify_Expr(BS, sal_ranged_set_quantified(BO, SB, Restr) -> sal_ranged_set_quantified(BO,SB,MRestr))
        where(SB -> bindings(BS1))
        SAL_Restrict_Bindings(BS, BS1 -> MBS)
        SAL_Modify_Expr(MBS, Restr -> MRestr)

 'rule' SAL_Modify_Expr(BS, sal_equivalence(L,R,Pre) -> sal_equivalence(ML,MR,MPre))
        SAL_Modify_Expr(BS, L -> ML)
        SAL_Modify_Expr(BS, R -> MR)
        SAL_Modify_Expr(BS, Pre -> MPre)

 'rule' SAL_Modify_Expr(BS, sal_bracket(E) -> sal_bracket(ME))
        SAL_Modify_Expr(BS, E -> ME)

 'rule' SAL_Modify_Expr(BS, sal_funct_expr(Op,Q,E1,E2) -> sal_funct_expr(Op,Q,ME1,ME2))
        SAL_Modify_Expr(BS, E1 -> ME1)
        SAL_Modify_Expr(BS, E2 -> ME2)

 'rule' SAL_Modify_Expr(BS, sal_ax_infix(L,IdOp,R) -> sal_ax_infix(ML,IdOp,MR))
        SAL_Modify_Expr(BS, L -> ML)
        SAL_Modify_Expr(BS, R -> MR)

 'rule' SAL_Modify_Expr(BS, sal_ax_prefix(Conn, E) -> sal_ax_prefix(Conn, ME))
        SAL_Modify_Expr(BS, E -> ME)

 'rule' SAL_Modify_Expr(BS, sal_let_expr(Id,T,NameSpace,LBS,Init,Expr) -> sal_let_expr(Id,T,NameSpace,LBS,MInit,MExpr))
        -- As the namespace features are not descriptive enough 
        -- (they are only used where the let must be unfolded), they are, in general, not complete...
        -- Using the let binding instead:
        SAL_Get_Bindings_from_Let_Bindings(LBS -> NewBindings)
--      SAL_Restrict_Bindings_with_Namespace(BS, NameSpace -> MBS)      
        SAL_Restrict_Bindings(BS, NewBindings -> MBS)
        SAL_Modify_Expr(MBS, Init -> MInit)
        SAL_Modify_Expr(MBS, Expr -> MExpr)


 'rule' SAL_Modify_Expr(BS, sal_if_expr(E, Then, Eif, else(Else)) -> sal_if_expr(ME, MThen, MEif, else(MElse)))
        SAL_Modify_Expr(BS, E -> ME)
        SAL_Modify_Expr(BS, Then -> MThen)
        SAL_Modify_Elsif_Expr(BS, Eif -> MEif)
        SAL_Modify_Expr(BS, Else -> MElse)
        
 'rule' SAL_Modify_Expr(BS, sal_infix_occ(L,IdOp,R) -> sal_infix_occ(ML,MIdOp,MR))
        SAL_Modify_Value(BS,IdOp -> MIdOp)
        SAL_Modify_Expr(BS, L -> ML)
        SAL_Modify_Expr(BS, R -> MR)

 'rule' SAL_Modify_Expr(BS, sal_esp_prefix_occ(L,IdOp,R) -> sal_esp_prefix_occ(ML,MIdOp,MR))
        SAL_Modify_Value(BS, L -> ML)
        SAL_Modify_Expr(BS, IdOp -> MIdOp)
        SAL_Modify_Expr(BS, R -> MR)

 'rule' SAL_Modify_Expr(BS, sal_prefix_occ(IdOp,Qual,E) -> sal_prefix_occ(MIdOp,Qual,ME))
        SAL_Modify_Value(BS, IdOp -> MIdOp)
        SAL_Modify_Expr(BS, E -> ME)

 'rule' SAL_Modify_Expr(BS, sal_assignment(Id, E) -> sal_assignment(Id, ME))
        SAL_Modify_Expr(BS, E -> ME)

 'rule' SAL_Modify_Expr(BS, sal_value_occ(ValId,Qual) -> sal_value_occ(NewValId,Qual))

        SAL_Modify_Value(BS, ValId -> NewValId)

 'rule' SAL_Modify_Expr(BS, sal_array_expr(Sub, Type, Val) -> sal_array_expr(Sub, Type, Val2))
        SAL_Modify_Expr(BS, Val -> Val2)

 'rule' SAL_Modify_Expr(BS, sal_array_access(Name, Index) -> sal_array_access(Name2, Index2))
        SAL_Modify_Expr(BS, Name -> Name2)
        SAL_Modify_Expr(BS, Index -> Index2)

 'rule' SAL_Modify_Expr(BS, sal_cc_array_access(Name, Index, Tid) -> sal_cc_array_access(Name2, Index2, Tid))
        SAL_Modify_Expr(BS, Name -> Name2)
        SAL_Modify_Expr(BS, Index -> Index2)

 'rule' SAL_Modify_Expr(BS, sal_array_var_occ(P, VarId, Indexes) -> sal_array_var_occ(P, VarId, Indexes2))
        SAL_Modify_Exprs(BS, Indexes -> Indexes2)

 'rule' SAL_Modify_Expr(BS, sal_cc_array_set(P, Ar, Ty, Indexes, Val) -> sal_cc_array_set(P, Ar2, Ty, Indexes2, Val2))
        SAL_Modify_Expr(BS, Val -> Val2)
        SAL_Modify_Expr(BS, Ar -> Ar2)
        SAL_Modify_Exprs(BS, Indexes -> Indexes2)


  -- The rest of the value expressions are untouched:
 'rule' SAL_Modify_Expr(BS, E -> E)
----------------------------
'condition' Match_IdOp_in_Bindings(SAL_ID_OP, SAL_BINDINGS)

  'rule' Match_IdOp_in_Bindings(IdOp, list(B,BS))
         (|
             Match_IdOp_in_Binding(IdOp, B)
         ||
             Match_IdOp_in_Bindings(IdOp, BS)
         |)

'condition' Match_IdOp_in_Binding(SAL_ID_OP, SAL_BINDING)

  'rule' Match_IdOp_in_Binding(IdOp, sal_prod_binding(_, BS))
         Match_IdOp_in_Bindings(IdOp, BS)

  'rule' Match_IdOp_in_Binding(IdOp, sal_typed_prod(_,BS,_))
         Match_IdOp_in_Bindings(IdOp, BS)

  'rule' Match_IdOp_in_Binding(IdOp, sal_typed_id(_,IdOp1,_))
         eq(IdOp, IdOp1)

----------------------------
'action' SAL_Modify_Exprs(SAL_BINDINGS, SAL_VALUE_EXPRS -> SAL_VALUE_EXPRS)

  'rule' SAL_Modify_Exprs(BS, list(E, ES) -> list(ME,MES))
         SAL_Modify_Expr(BS, E -> ME)
         SAL_Modify_Exprs(BS, ES -> MES)

  'rule' SAL_Modify_Exprs(_, nil -> nil)

---------------------------

'action' SAL_Modify_Expr_Pairs(SAL_BINDINGS, SAL_VALUE_EXPR_PAIRS -> SAL_VALUE_EXPR_PAIRS)

  'rule' SAL_Modify_Expr_Pairs(BS, list(pair(L,R), EPS) -> list(pair(ML,MR), MEPS))
         SAL_Modify_Expr(BS, L -> ML)
         SAL_Modify_Expr(BS, R -> MR)
         SAL_Modify_Expr_Pairs(BS, EPS -> MEPS)

  'rule' SAL_Modify_Expr_Pairs(_, nil -> nil)
---------------------------
'action' SAL_Modify_Elsif_Expr(SAL_BINDINGS, SAL_ELSIF_BRANCHES -> SAL_ELSIF_BRANCHES)

  'rule' SAL_Modify_Elsif_Expr(BS, list(elsif(If, Then), Rest) -> list(elsif(MIf, MThen), MRest))
         SAL_Modify_Expr(BS, If -> MIf)
         SAL_Modify_Expr(BS, Then -> MThen)
         SAL_Modify_Elsif_Expr(BS, Rest -> MRest)

  'rule' SAL_Modify_Elsif_Expr(_, nil -> nil)
---------------------------

'action' SAL_Restrict_Bindings(SAL_BINDINGS, SAL_BINDINGS -> SAL_BINDINGS)

  'rule' SAL_Restrict_Bindings(list(B,BS), Binds -> Bindings)
         SAL_Restrict_Bindings(BS, Binds -> NewBinds)
         (|
             where(B -> sal_prod_binding(P,BS1))
             SAL_Restrict_Bindings(BS1, BS -> BS11)
             (|
                 eq(BS11, nil)
                 -- This binding is empty... remove it:
                 where(NewBinds -> Bindings)
             ||
                 -- The binding is not empty, add the rest of it:
                 where(SAL_BINDINGS'list(sal_prod_binding(P,BS11), NewBinds) -> Bindings)
             |)
         ||
             where(B -> sal_typed_prod(P,BS1,T))
             SAL_Restrict_Bindings(BS1, BS -> BS11)
             (|
                 eq(BS11, nil)
                 -- This binding is empty... remove it:
                 where(NewBinds -> Bindings)
             ||
                 -- The binding is not empty, add the rest of it:
                 where(SAL_BINDINGS'list(sal_typed_prod(P,BS11,T), NewBinds) -> Bindings)
             |)
         ||
             -- It is a sal_typed_id... (single binding)
             Binding_in_Bindings(B, Binds)
             where(NewBinds -> Bindings)                   
         ||
             where(SAL_BINDINGS'list(B, NewBinds) -> Bindings)
         |)

  'rule' SAL_Restrict_Bindings(nil, _ -> nil)

----------------------------
'condition' Binding_in_Bindings(SAL_BINDING, SAL_BINDINGS)

  'rule' Binding_in_Bindings(sal_typed_id(P,IdOp,T1), list(B,BS))
         (|
             where(B -> sal_prod_binding(_,BS1))
             Binding_in_Bindings(sal_typed_id(P, IdOp,T1), BS1)
         ||
             where(B -> sal_typed_prod(_,BS1,T))
             Binding_in_Bindings(sal_typed_id(P, IdOp,T1), BS1)
         ||
             where(B -> sal_typed_id(_, IdOp1,_))
             eq(IdOp, IdOp1)
         ||
             Binding_in_Bindings(B, BS)
         |)
-----------------------------------------------
'action' SAL_Restrict_Bindings_with_Lambda(SAL_BINDINGS, SAL_LAMBDA_BINDINGS -> SAL_BINDINGS)

  'rule' SAL_Restrict_Bindings_with_Lambda(BS, list(bindings(BS1), LBS) -> NewBS)
         SAL_Restrict_Bindings(BS, BS1 -> Restricted1)
         SAL_Restrict_Bindings_with_Lambda(Restricted1, LBS -> NewBS)

  'rule' SAL_Restrict_Bindings_with_Lambda(BS, nil -> BS)

-----------------------------------------------

'action' SAL_Restrict_Bindings_with_Namespace(SAL_BINDINGS, BINDING_NAMESPACE -> SAL_BINDINGS)

  'rule' SAL_Restrict_Bindings_with_Namespace(list(B,BS), NameSpace -> Bindings)
         SAL_Restrict_Bindings_with_Namespace(BS, NameSpace-> NewBinds)
         (|
             where(B -> sal_prod_binding(P, BS1))
             SAL_Restrict_Bindings_with_Namespace(BS1, NameSpace -> BS11)
             (|
                 eq(BS11, nil)
                 -- This binding is empty... remove it:
                 where(NewBinds -> Bindings)
             ||
                 -- The binding is not empty, add the rest of it:
                 where(SAL_BINDINGS'list(sal_prod_binding(P, BS11), NewBinds) -> Bindings)
             |)
         ||
             where(B -> sal_typed_prod(P, BS1,T))
             SAL_Restrict_Bindings_with_Namespace(BS1, NameSpace -> BS11)
             (|
                 eq(BS11, nil)
                 -- This binding is empty... remove it:
                 where(NewBinds -> Bindings)
             ||
                 -- The binding is not empty, add the rest of it:
                 where(SAL_BINDINGS'list(sal_typed_prod(P, BS11,T), NewBinds) -> Bindings)
             |)
         ||
             -- It is a sal_typed_id... (single binding)
             Binding_in_NameSpace(B, NameSpace)
             where(NewBinds -> Bindings)                   
         ||
             where(SAL_BINDINGS'list(B, NewBinds) -> Bindings)
         |)

  'rule' SAL_Restrict_Bindings_with_Namespace(nil, _ -> nil)

--------------------------------------------
'condition' Binding_in_NameSpace(SAL_BINDING, BINDING_NAMESPACE)

  'rule' Binding_in_NameSpace(Binding, list(BE,BES))
         (|
             Binding_in_Binding_Elem(Binding, BE)
         ||
             Binding_in_NameSpace(Binding, BES)
         |)

'condition' Binding_in_Binding_Elem(SAL_BINDING, BINDING_ELEM)

  'rule' Binding_in_Binding_Elem(sal_typed_id(_, IdOp,_),binding_elem(_,_,Name))
         where(Name -> id_op(IdOp1))
         eq(IdOp,IdOp1)

  'rule' Binding_in_Binding_Elem(sal_typed_id(P,IdOp,T),nested_elem(_,Name, BE))
         (|
              where(Name -> id_op(IdOp1))
              eq(IdOp,IdOp1)
         ||
              Binding_in_Binding_Elem(sal_typed_id(P,IdOp,T),BE)
         |)

----------------------------------------------------------------------
'action' SAL_Out_Bound_Ineq_vars(SAL_BINDINGS)

  'rule' SAL_Out_Bound_Ineq_vars(list(B, BS))
         SAL_Out_Bound_Ineq_var(B)
         [|
             ne(BS, nil)
             WriteFile(" AND ")
             SAL_Out_Bound_Ineq_vars(BS)
         |]

  'rule' SAL_Out_Bound_Ineq_vars(nil)

'action' SAL_Out_Bound_Ineq_var(SAL_BINDING)

  'rule' SAL_Out_Bound_Ineq_var(sal_prod_binding(_,BS))
         Putmsg("Prod binding found\n")

  'rule' SAL_Out_Bound_Ineq_var(sal_typed_prod(_,BS, T))
         WriteFile("(")
         SAL_Out_Binding_Vars(BS)
         WriteFile(") = (")
         SAL_Out_Modified_Binding_Vars(BS)
         WriteFile(")")

  'rule' SAL_Out_Bound_Ineq_var(sal_typed_id(P, IdOp,T))
         SAL_Out_Binding_Vars(list(sal_typed_id(P, IdOp,T), nil))
         WriteFile(" = ")
         SAL_Out_Modified_Binding_Vars(list(sal_typed_id(P, IdOp,T), nil))

'action' SAL_Out_Binding_Vars(SAL_BINDINGS)

  'rule' SAL_Out_Binding_Vars(list(B,BS))
         SAL_Out_Binding_Var(B)
         [|
             ne(BS, nil)
             WriteFile(", ")
             SAL_Out_Binding_Vars(BS)
         |]

'action' SAL_Out_Binding_Var(SAL_BINDING)

  'rule' SAL_Out_Binding_Var(sal_prod_binding(_, BS))
         WriteFile("(")
         SAL_Out_Binding_Vars(BS)
         WriteFile(")")

  'rule' SAL_Out_Binding_Var(sal_typed_prod(_, BS, T))
         WriteFile("(")
         SAL_Out_Binding_Vars(BS)
         WriteFile(")")

  'rule' SAL_Out_Binding_Var(sal_typed_id(_, IdOp,T))
         SAL_Out_IdOp(IdOp)

--------------------------------------------------------------

'action' SAL_Out_Modified_Binding_Vars(SAL_BINDINGS)

  'rule' SAL_Out_Modified_Binding_Vars(list(B,BS))
         SAL_Out_Modified_Binding_Var(B)
         [|
             ne(BS, nil)
             WriteFile(", ")
             SAL_Out_Modified_Binding_Vars(BS)
         |]

'action' SAL_Out_Modified_Binding_Var(SAL_BINDING)

  'rule' SAL_Out_Modified_Binding_Var(sal_prod_binding(_, BS))
         WriteFile("(")
         SAL_Out_Modified_Binding_Vars(BS)
         WriteFile(")")

  'rule' SAL_Out_Modified_Binding_Var(sal_typed_prod(_, BS, T))
         WriteFile("(")
         SAL_Out_Modified_Binding_Vars(BS)
         WriteFile(")")

  'rule' SAL_Out_Modified_Binding_Var(sal_typed_id(Pos, IdOp,T))
         (|
             where(IdOp -> id(Ident))
             id_to_string(Ident -> Str)
             Concatenate(Str, "_" -> MStr)
             WriteFile(MStr)
        ||
             Puterror(Pos)
             Putmsg("Internal error: Can not modify name in binding to generate exists1 operator\n")
             where(IdOp -> MIdOp)
        |)


--------------------------------------------------------------

'action' SAL_Modify_Value(SAL_BINDINGS, SAL_VALUE_ID -> SAL_VALUE_ID)

  'rule' SAL_Modify_Value(BS, val_id(IdOp) -> val_id(MIdOp))
         Match_IdOp_in_Bindings(IdOp, BS)
         (|
             where(IdOp -> id(Ident))
             id_to_string(Ident -> Str)
             Concatenate(Str, "_" -> MStr)
             string_to_id(MStr -> MIdent)
             where(SAL_ID_OP'id(MIdent) -> MIdOp)
        ||
             Putmsg("Internal error: Can not modify name in binding to generate exists1 operator\n")
             where(IdOp -> MIdOp)
        |)

  'rule' SAL_Modify_Value(BS, record_val_id(Pos, IdOp, I) -> record_val_id(Pos, MIdOp, I))
         Match_IdOp_in_Bindings(IdOp, BS)
         (|
             where(IdOp -> id(Ident))
             id_to_string(Ident -> Str)
             Concatenate(Str, "_" -> MStr)
             string_to_id(MStr -> MIdent)
             where(SAL_ID_OP'id(MIdent) -> MIdOp)
        ||
             Putmsg("Internal error: Can not modify name in binding to generate exists1 operator\n")
             where(IdOp -> MIdOp)
        |)

  'rule' SAL_Modify_Value(_, V -> V)

--------------------------------------------------------------------------------
'action' SAL_Get_Bindings_from_Let_Bindings(SAL_LET_BINDINGS -> SAL_BINDINGS)

  'rule' SAL_Get_Bindings_from_Let_Bindings(list(sal_let_bind(LB,_), Rest) -> Bindings)
         SAL_Get_Bindings_from_Bind(LB -> BS1)
         SAL_Get_Bindings_from_Let_Bindings(Rest -> BS2)
         SAL_Concatenate_Bindings(BS1,BS2 -> Bindings)

  'rule' SAL_Get_Bindings_from_Let_Bindings(list(sal_let_binds(SLBinds,_), Rest) -> Bindings)
         SAL_Get_Bindings_from_Binds(SLBinds -> BS1)
         SAL_Get_Bindings_from_Let_Bindings(Rest -> BS2)
         SAL_Concatenate_Bindings(BS1,BS2 -> Bindings)

  'rule' SAL_Get_Bindings_from_Let_Bindings(nil -> nil)

'action' SAL_Get_Bindings_from_Binds(SAL_LETBINDS -> SAL_BINDINGS)

  'rule' SAL_Get_Bindings_from_Binds(list(Bind, Binds) -> Bindings)
         SAL_Get_Bindings_from_Bind(Bind -> BS1)
         SAL_Get_Bindings_from_Binds(Binds -> BS2)
         SAL_Concatenate_Bindings(BS1,BS2 -> Bindings)

  'rule' SAL_Get_Bindings_from_Binds(nil -> nil)

'action' SAL_Get_Bindings_from_Bind(SAL_LETBIND -> SAL_BINDINGS)

  'rule' SAL_Get_Bindings_from_Bind(sal_let_idop(_,BS,_) -> BS)

'action' SAL_Remove_Brackets(SAL_TYPE_EXPR -> SAL_TYPE_EXPR)

  'rule' SAL_Remove_Brackets(type_refs(sal_defined(_,Id,Tid)) -> Res)
         Tid'TExpr -> T
         SAL_Remove_Brackets(T -> Res)

  'rule' SAL_Remove_Brackets(T -> T)


------------------------------------------------

