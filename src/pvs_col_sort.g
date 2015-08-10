-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the sort for RSL Declares
-- to comply with PVS define before use rule

-- Also defines the actions to get the types and
-- values (Type_ids and Value_ids) to be sorted


'module' pvs_col_sort

'use' ast print ext env objects values types pp cc cpp
      pvs pvs_ast pvs_aux

'export' 
         -- Actions
         Gen_Declareds
         Sort_Declareds




--------------------------------------------------
-- Get Type_ids and Value_ids to be sorted
--------------------------------------------------


--------------------------------------------------
'action' Gen_Declareds(DECLS, DECLAREDS -> DECLAREDS)

         -- end of recursion
  'rule' Gen_Declareds(nil, Declareds -> Declareds1):
         where(Declareds -> Declareds1)

          -- Decl is Type
  'rule' Gen_Declareds(list(type_decl(Pos, TypeDefs), DeclsTail), Declareds -> Declareds1):
         Get_Type_Defs(TypeDefs, Declareds -> Declareds2)
         Gen_Declareds(DeclsTail, Declareds2 -> Declareds1)

          -- Decl is Value
  'rule' Gen_Declareds(list(value_decl(Pos, ValueDefs), DeclsTail), Declareds -> Declareds1):
         Get_current_top_values(-> Valueids)
         Get_Value_Defs(Valueids, ValueDefs, Declareds -> Declareds2)
         Gen_Declareds(DeclsTail, Declareds2 -> Declareds1)

          -- Decl is Variable: not supported
  'rule' Gen_Declareds(list(variable_decl(Pos, _), DeclsTail), Declareds -> Declareds1):
         Puterror(Pos)
         Putmsg("Variable declarations not supported")
         Putnl()
         Gen_Declareds(DeclsTail, Declareds -> Declareds1)

          -- Decl is Channel: not supported
  'rule' Gen_Declareds(list(channel_decl(Pos,  _), DeclsTail), Declareds -> Declareds1):
         Puterror(Pos)
         Putmsg("Channel declarations not supported")
         Putnl()
         Gen_Declareds(DeclsTail, Declareds -> Declareds1)

          -- Decl is Object: ignore
  'rule' Gen_Declareds(list(object_decl(Pos, ObjectDefs), DeclsTail),
                       Declareds -> Declareds1):
         Gen_Declareds(DeclsTail, Declareds -> Declareds1)

          -- Decl is Axiom
  'rule' Gen_Declareds(list(axiom_decl(Pos, AxiomDefs), DeclsTail),
                              Declareds -> Declaredsout):
         Get_current_axioms(-> AxiomEnv)
         Process_Axiom_Env(AxiomEnv, nil -> DeclaredsAxioms)
--print("***********DeclaredsAxioms************")
--PrintDeclareds(DeclaredsAxioms)
	 Rev_Declareds(DeclaredsAxioms, nil -> DeclaredsAxioms2)
	 Conc_Declareds(Declareds, DeclaredsAxioms2 -> Declareds1)
         Gen_Declareds(DeclsTail, Declareds1 -> Declaredsout)

          -- Decl is Test_case: not supported
  'rule' Gen_Declareds(list(test_case_decl(Pos, _), DeclsTail), Declareds -> Declareds1):
         Putwarning(Pos)
         Putmsg("Test cases are ignored")
         Putnl()
         Gen_Declareds(DeclsTail, Declareds -> Declareds1)

  'rule' Gen_Declareds(list(trans_system_decl(Pos, _), DeclsTail), Declareds -> Declareds1):
         Putwarning(Pos)
         Putmsg("Transition systems are ignored")
         Putnl()
         Gen_Declareds(DeclsTail, Declareds -> Declareds1)

  'rule' Gen_Declareds(list(property_decl(Pos, _), DeclsTail), Declareds -> Declareds1):
         Putwarning(Pos)
         Putmsg("LTL assertions are ignored")
         Putnl()
         Gen_Declareds(DeclsTail, Declareds -> Declareds1)


--------------------------------------------------
'action' Get_Type_Defs(TYPE_DEFS, DECLAREDS -> DECLAREDS)

  'rule' Get_Type_Defs(list(TypeDef, TypeDefsTail), Declareds -> Declareds1):
         (|
           Get_Type_Def(TypeDef -> type_id(Typeid))
           where(type_item(Typeid) -> Declared)
--           Insert_u_Declared(Declared, Declareds -> Declareds2)
           Insert_Declared(Declared, Declareds -> Declareds2)
           Get_Type_Defs(TypeDefsTail, Declareds2 -> Declareds1)
         ||
           Get_Type_Defs(TypeDefsTail, Declareds -> Declareds1)
         |)

         -- no more Type_Defs
  'rule' Get_Type_Defs(nil, Declareds -> Declareds):



--------------------------------------------------
'action' Get_Type_Def(TYPE_DEF -> OPT_TYPE_ID)

  'rule' Get_Type_Def(abbrev(Pos, Id, _) -> type_id(Typeid)):
         Get_current_types(-> TE)
         (|
           Lookup_env(Id, TE -> type_id(Typeid))
         || -- may be local: try with localised name
           Localise_id(Pos, Id -> LId)
           Lookup_env(LId, TE -> type_id(Typeid))
         |)

  'rule' Get_Type_Def(sort(Pos, Id) -> type_id(Typeid)):
         Get_current_types(-> TE)
         (|
           Lookup_env(Id, TE -> type_id(Typeid))
         || -- may be local: try with localised name
           Localise_id(Pos, Id -> LId)
           Lookup_env(LId, TE -> type_id(Typeid))
         |)

  'rule' Get_Type_Def(variant(Pos, Id, CS) -> type_id(Typeid)):
         Get_current_types(-> TE)
         (|
           Lookup_env(Id, TE -> type_id(Typeid))
         || -- may be local: try with localised name
           Localise_id(Pos, Id -> LId)
           Lookup_env(LId, TE -> type_id(Typeid))
         |)

  'rule' Get_Type_Def(record(Pos, Id, _) -> type_id(Typeid)):
         Get_current_types(-> TE)
         (|
           Lookup_env(Id, TE -> type_id(Typeid))
         || -- may be local: try with localised name
           Localise_id(Pos, Id -> LId)
           Lookup_env(LId, TE -> type_id(Typeid))
         |)

  'rule' Get_Type_Def(union(Pos, Id, CS) -> nil):
         Puterror(Pos)
         Putmsg("Cannot translate union types: ignored")
         Putnl()


--------------------------------------------------
'action' Get_Value_Defs(Value_ids, VALUE_DEFS, DECLAREDS -> DECLAREDS)

  'rule' Get_Value_Defs(Valueids, list(ValueDef, ValueDefsTail), Declareds -> Declareds3):
         Get_Value_Def(Valueids, ValueDef -> Declareds1)
         Conc_Declareds(Declareds, Declareds1 -> Declareds2)
         Get_Value_Defs(Valueids, ValueDefsTail, Declareds2 -> Declareds3)

         -- no more Value_Defs
  'rule' Get_Value_Defs(Valueids, nil, Declareds -> Declareds):



--------------------------------------------------
'action' Get_Value_Def(Value_ids, VALUE_DEF -> DECLAREDS)

  'rule' Get_Value_Def(Valueids, typing(_, single(_, B, _)) -> Declrds):
         Get_Value_binding(Valueids, B -> Declrds)

  'rule' Get_Value_Def(Valueids, typing(_, multiple(_, Bs, _)) -> Declrds):
         Get_Value_bindings(Valueids, Bs -> Declrds)
         
  'rule' Get_Value_Def(Valueids, exp_val(_, single(_, B, _), _) -> Declrds):
         Get_Value_binding(Valueids, B -> Declrds)

  'rule' Get_Value_Def(Valueids, exp_fun(_, single(_, B, _), _, _, _, _, _) -> Declrds):
         Get_Value_binding(Valueids, B -> Declrds)

  'rule' Get_Value_Def(Valueids, imp_val(_, single(_, B, _), _) -> Declrds):
         Get_Value_binding(Valueids, B -> Declrds)

  'rule' Get_Value_Def(Valueids, imp_fun(_, single(_, B,_), _, _, _) -> Declrds):
         Get_Value_binding(Valueids, B -> Declrds)



--------------------------------------------------
'action' Get_Value_binding(Value_ids, BINDING -> DECLAREDS)

  'rule' Get_Value_binding(Valueids, single(P, _) -> list(Declrd, nil)):
         Select_id_by_pos(P, Valueids -> value_id(Valueid))
         where(value_item(Valueid) -> Declrd)

  'rule' Get_Value_binding(Valueids, product(_, Bs) -> Declrds):
         Get_Value_bindings(Valueids, Bs -> Declrds)

  'rule' Get_Value_binding(Valueids, single(P, _) -> nil):


--------------------------------------------------
'action' Get_Value_bindings(Value_ids, BINDINGS -> DECLAREDS)

  'rule' Get_Value_bindings(Valueids, list(B, Bs) -> Declrds):
         Get_Value_bindings(Valueids, Bs -> Declrds1)
         (|
           where(B -> single(P, _))
           Select_id_by_pos(P, Valueids -> value_id(Valueid))
           where(DECLAREDS'list(value_item(Valueid), Declrds1) -> Declrds)
         ||
           where(B -> product(P, Bs1))
           Get_Value_bindings(Valueids, Bs1 -> Declrds2)
           Conc_Declareds(Declrds1, Declrds2 -> Declrds)
         |)

  'rule' Get_Value_bindings(_, nil -> nil):



--------------------------------------------------
'action' Get_Axiom_Defs(AXIOM_DEFS, DECLAREDS -> DECLAREDS)

  'rule' Get_Axiom_Defs(list(AxiomDef, AxiomDefsTail),
                        Declareds -> Declaredsout):
         Get_Axiom_Def(AxiomDef -> Declareds1)
         Conc_Declareds(Declareds, Declareds1 -> Declareds2)
         Get_Axiom_Defs(AxiomDefsTail, Declareds2 -> Declaredsout)

         -- no more Axiom_Defs
  'rule' Get_Axiom_Defs(nil, Declareds -> Declareds):


--------------------------------------------------
'action' Get_Axiom_Def(AXIOM_DEF -> DECLAREDS)

  'rule' Get_Axiom_Def(AxiomDef -> Declaredsout):
         Get_current_axioms(-> AxiomEnv)
         Process_Axiom_Env(AxiomEnv, nil -> Declaredsout)


--------------------------------------------------
'action' Process_Axiom_Env(AXIOM_ENV, DECLAREDS -> DECLAREDS)

  'rule' Process_Axiom_Env(axiom_env(Axiomid, AxiomEnv),
                           Declareds -> Declaredsout):
         Axiomid'Axiom -> ValueExpr
	 (| -- if theory generate lemma 
	   IsTheory
           where(lemma_item(Axiomid) -> Declared)
	 || -- not a theory: generate axiom
           where(axiom_item(Axiomid) -> Declared)
	 |)	 	

         Insert_u_Declared(Declared, Declareds -> Declareds1)
--         Insert_Declared(Declared, Declareds -> Declareds1)
         Process_Axiom_Env(AxiomEnv, Declareds1 -> Declaredsout)

  'rule' Process_Axiom_Env(nil, Declareds -> Declareds):



--------------------------------------------------
-- Sorts the declares in RSL
--------------------------------------------------


--------------------------------------------------
'action' Sort_Declareds(DECLAREDS,      -- ToDo 
                        DECLAREDS,      -- Waiting
                        DECLAREDS,      -- Done
                        FOUND
                     -> DECLAREDS)      -- SortedDeclareds

         -- end of recursion
  'rule' Sort_Declareds(nil, nil, Done, _ -> Done):

          -- found, some waiting  ==> another pass
  'rule' Sort_Declareds(nil, Waiting, Done, found -> DoneOut):
	 Sort_Declareds(Waiting, nil, Done, nil -> DoneOut)

          -- found  ==> another pass trying waiting first
          -- (slow but keeps original order as much as possible)
  'rule' Sort_Declareds(Declrds, Waiting, Done, found -> DoneOut):
         Conc_Declareds(Waiting, Declrds -> Declrds1)
         Sort_Declareds(Declrds1, nil, Done, nil -> DoneOut)

          -- not found, some waiting  ==> 
	  -- split functions into signatures and axioms and try again
  'rule' Sort_Declareds(nil, Waiting, Done, nil -> Doneout):
	 (| -- Are there any defined functions waiting?
	   Are_Functions(Waiting, nil -> FunDecls)
	   -- YES
	   -- Remove the functions from waiting
           Substract_Declareds(Waiting, FunDecls -> Waiting1)
	   -- Make all signatures in FunDecls as
	   -- value decl, no_def (function signature)
	   -- only id + TypeExpr
	   -- This makes a suitable copy of each Value_id
	   -- but with no definition, puts that in SignFunDecls
	   -- and the original in FunDecls2
	   Gen_Sign_Decls(FunDecls, nil, nil -> SignFunDecls, FunDecls2)
	   -- put the function signatures as done
	   Conc_Declareds(Done, SignFunDecls -> Done1)
	   Sort_Declareds(Waiting1, nil, Done1, found -> Done2)
	   -- Make all definitions in FunDecls as
	   -- mutually recursive functions
	   -- to be inserted in Done so after
	   -- only their axioms need to be generated
           where(rec_item(FunDecls2) -> Decl)
           Insert_Declared(Decl, Done2 -> Doneout)
	   Add_Declared(Decl)  -- to TotalDeclareds
	 ||
	   -- no functions left: mutually recursive types
	   where(Waiting -> DECLAREDS'list(Decl, Decls))
	   (|
	     where(Decl -> type_item(Typeid))
	     Typeid'Pos -> Pos
	     Typeid'Ident -> Ident
	     Puterror(Pos)
	     Print_id(Ident)
	     Putmsg(" seems to be involved in mutual recursion")
	     Putnl()
	   ||
	     DefaultPos(-> Pos)
	     Puterror(Pos)
	     Putmsg("Internal error for declaration ")
--PrintDeclared(Decl)
--PrintDeclareds(Decls)
	     print(Decl)
	     Putnl()
	   |)
	   where(Done -> Doneout)
	 |)


          -- Decl is Type
  'rule' Sort_Declareds(list(type_item(Typeid), DeclrdsTail),
                        Waiting, Done, Found -> DoneOut):
         Sort_Type_id(Typeid, Waiting, Done, Found
                      -> Waiting1, Done1, Found1)
         Sort_Declareds(DeclrdsTail, Waiting1, Done1, Found1
                        -> DoneOut)

          -- Decl is Value
  'rule' Sort_Declareds(list(value_item(Valueid), DeclrdsTail),
                        Waiting, Done, Found -> DoneOut):
         Sort_Value_id(Valueid, Waiting, Done, Found
                       -> Waiting1, Done1, Found1)
         Sort_Declareds(DeclrdsTail, Waiting1, Done1, Found1
                        -> DoneOut)

          -- Decl is Axiom
  'rule' Sort_Declareds(list(axiom_item(Axiomid), DeclrdsTail),
                        Waiting, Done, Found
                        -> DoneOut):
         Sort_Axiom_id(Axiomid, Waiting, Done, Found
                       -> Waiting1, Done1, Found1)
         Sort_Declareds(DeclrdsTail, Waiting1, Done1, Found1
                        -> DoneOut)

          -- Decl is lemma
  'rule' Sort_Declareds(list(lemma_item(Axiomid), DeclrdsTail),
                        Waiting, Done, Found
                        -> DoneOut):
         Sort_Lemma_id(Axiomid, Waiting, Done, Found
                       -> Waiting1, Done1, Found1)
         Sort_Declareds(DeclrdsTail, Waiting1, Done1, Found1
                        -> DoneOut)




--------------------------------------------------
'action' Sort_Type_id(Type_id, DECLAREDS, DECLAREDS, FOUND
                      -> DECLAREDS, DECLAREDS, FOUND)

  'rule' Sort_Type_id(Typeid, Waiting, Done, Found
                      -> WaitingOut, DoneOut, FoundOut):
         Typeid'Type -> Type
         Typeid'Ident -> Ident
         Typeid'Pos -> Pos

         Collect_Type_ids(Type, nil -> Declareds1)
-- debug
-- Print_id(Ident)
-- Putmsg(" uses types ")
-- PrintDeclareds(Declareds1)
-- Putnl()

         (|  -- is subtype?
           where(Type -> abbrev(_))
           Typeid'Def -> TypeDef
           where(TypeDef -> abbreviation(TypeExpr))
           where(TypeExpr -> subtype(Typing, restriction(_, ValueExpr)))
           Process_Subtype(Typing, ValueExpr, Declareds1 -> Declareds2)
         || -- is sort kind?
           where(Type -> sort(SortKind))
           (| -- is record?
             where(SortKind -> record(Components))
             Collect_Type_ids(Components, Declareds1 -> DeclaredsVaT)
	     -- get the Value_ids in Components for TotalDeclareds
	     Collect_Value_id_Variant(Components, nil -> DeclrdsValueid1)
	     -- get the mk_ Value_id for TotalDeclareds
	     Get_current_top_values(-> Valueids)
	     Select_id_by_pos(Pos, Valueids -> value_id(Valueid))
	     Insert_Declared(value_item(Valueid), DeclrdsValueid1
                             -> DeclrdsValueid)
	     -- add them to TotalDeclareds
	     Add_Declareds(DeclrdsValueid)
             Process_Record_Type(Components, DeclaredsVaT -> Declareds2)
           || -- is variant?
             where(SortKind -> variant(Variants))
             Collect_Type_ids(Variants, Declareds1 -> DeclaredsVaT)
	     Collect_Value_id_Variant(Variants, nil -> DeclrdsValueid)
	     Add_Declareds(DeclrdsValueid)
             Process_Variant_Type(Pos, Ident, DeclaredsVaT -> Declareds2)
           || -- is union or abstract?
             -- union not supported: ignored
             -- abstract: no need to look for anything further 
             where(Declareds1 -> Declareds2)
           |)
         ||
           where(Declareds1 -> Declareds2)
         |)

	 Get_TotalDeclareds(-> TotalDone)
         Substract_Declareds_s(Declareds2, TotalDone -> Declareds3)
-- debug
-- Putmsg("Type ")
-- Print_id(Ident)
         (|
            -- can be translated
           eq(Declareds3, nil)
-- Putmsg(" done\n")
           where(type_item(Typeid) -> Declared)
           where(Waiting -> WaitingOut)
           Insert_u_Declared(Declared, Done -> DoneOut)
--           Insert_u_Declared(Declared, TotalDone -> TotalDoneOut)
	   Add_Declared(Declared)  -- to TotalDeclareds
           where(found -> FoundOut)
         ||
-- Putmsg(" waiting for ")
-- PrintDeclareds(Declareds3)
-- Putnl()
            -- can NOT be translated
           where(type_item(Typeid) -> Declared)
           Insert_u_Declared(Declared, Waiting -> WaitingOut)
--           where(TotalDone -> TotalDoneOut)
           where(Done -> DoneOut)
           where(Found -> FoundOut)
         |)


--------------------------------------------------
'action' Sort_Value_id(Value_id, DECLAREDS, DECLAREDS, FOUND
                       -> DECLAREDS, DECLAREDS, FOUND)

  'rule' Sort_Value_id(Valueid, Waiting, Done, Found
                       -> WaitingOut, DoneOut, FoundOut):
         Valueid'Type -> Type
         Valueid'Pos -> Pos
         Valueid'Ident -> IdOp
         Collect_Type_ids(Type, nil -> Declareds1)
-- debug
-- Print_id_or_op(IdOp)
-- Putmsg(" uses types ")
-- PrintDeclareds(Declareds1)
-- Putnl()
         Valueid'Def -> ValueDef

         (| -- No Definition
           where(ValueDef -> no_def)
           where(Declareds1 -> Declareds2)

         || -- Explicit Value
           where(ValueDef -> expl_val(ValueExpr, _))
           Process_Expl_Val(ValueExpr, Declareds1 -> Declareds2)

         || -- Implicit Value
           where(ValueDef -> impl_val(ValueExpr))
           Process_Impl_Val(ValueExpr, Pos, IdOp, Declareds1 -> Declareds2)

         || -- Explicit Function
           where(ValueDef -> expl_fun(Params, ValueExpr, Post, Pre, OptCond, _))
           -- Value Expresion
           Process_Expl_Fun_ValExpr(Valueid, Declareds1 -> DeclaredsVE1)
           -- Post Expresion
           Process_Expl_Fun_PostExpr(Valueid, DeclaredsVE1 -> DeclaredsVE2)
           -- Pre Condition Expresion
           Process_Expl_Fun_PreExpr(Valueid, DeclaredsVE2 -> Declareds2)

         || -- Implicit Function
           where(ValueDef -> impl_fun(Params, Post, Pre, OptCond))
           -- Post Expresion
           Process_Impl_Fun_PostExpr(Valueid, Declareds1 -> DeclaredsPE)
           -- Pre Condition Expresion
           Process_Impl_Fun_PreExpr(Valueid, DeclaredsPE -> Declareds2)
         |)

	 Get_TotalDeclareds(-> TotalDone)
         Substract_Declareds_s(Declareds2, TotalDone -> Declareds3)
-- debug
-- Putmsg("Value ")
-- Print_id_or_op(IdOp)
         (|
            -- can be translated
           eq(Declareds3, nil)
-- Putmsg(" done\n")
           where(value_item(Valueid) -> Declared)
           where(Waiting -> WaitingOut)
           Insert_u_Declared(Declared, Done -> DoneOut)
--           Insert_u_Declared(Declared, TotalDone -> TotalDoneOut)
	   Add_Declared(Declared)  -- to TotalDeclareds
           where(found -> FoundOut)
         ||
            -- can NOT be translated
-- Putmsg(" waiting for ")
-- PrintDeclareds(Declareds3)
-- Putnl()
           where(value_item(Valueid) -> Declared)
           Insert_u_Declared(Declared, Waiting -> WaitingOut)
           where(Done -> DoneOut)
           where(TotalDone -> TotalDoneOut)
           where(Found -> FoundOut)
         |)


--------------------------------------------------
'action' Sort_Axiom_id(Axiom_id, DECLAREDS, DECLAREDS, FOUND
                       -> DECLAREDS, DECLAREDS, FOUND)

  'rule' Sort_Axiom_id(Axiomid, Waiting, Done, Found
                       -> WaitingOut, DoneOut, FoundOut):
         Axiomid'Axiom -> ValueExpr
         Axiomid'Pos -> Pos
         Axiomid'Ident -> Ident
	 -- sweep for types
	 Collect_Type_ids(ValueExpr, nil -> DeclaredsTypeids)
	 -- sweep for values
         Collect_Value_ids(ValueExpr, DeclaredsTypeids -> DeclaredsValueids)
	 -- sweep for operators now part of Collect_Value_ids
         -- Collect_Redef_Opers(ValueExpr, DeclaredsValueids -> Decls2)


         Collect_Pos(ValueExpr, nil -> Bindings)
         Substract_Declareds_in_Bindings(DeclaredsValueids, Bindings -> Declareds2)

	 Get_TotalDeclareds(-> TotalDone)
         Substract_Declareds_s(Declareds2, TotalDone -> Declareds3)
         (|
            -- can be translated
           eq(Declareds3, nil)
           where(axiom_item(Axiomid) -> Declared)
           where(Waiting -> WaitingOut)
           Insert_u_Declared(Declared, Done -> DoneOut)
--           Insert_u_Declared(Declared, TotalDone -> TotalDoneOut)
	   Add_Declared(Declared)  -- to TotalDeclareds
           where(found -> FoundOut)
         ||
            -- can NOT be translated
           where(axiom_item(Axiomid) -> Declared)
-- Putmsg("All declareds:\n")
-- PrintDeclareds_s(TotalDone)
-- Putnl()
-- Putmsg("Types:\n")
-- PrintDeclareds(DeclaredsTypeids)
-- Putnl()
-- [|
--   Axiomid'Ident -> ident(Id)
--   Putmsg("[")
--   Print_id(Id)
--   Putmsg("] ")
-- |]
-- Print_expr(ValueExpr)
-- Putmsg(" waiting for\n")
-- PrintDeclareds(Declareds3)
-- Putnl()
           Insert_u_Declared(Declared, Waiting -> WaitingOut)
           where(Done -> DoneOut)
--           where(TotalDone -> TotalDoneOut)
           where(Found -> FoundOut)
         |)


--------------------------------------------------
'action' Sort_Lemma_id(Axiom_id, DECLAREDS, DECLAREDS, FOUND
                       -> DECLAREDS, DECLAREDS, FOUND)

  'rule' Sort_Lemma_id(Lemmaid, Waiting, Done, Found
                       -> WaitingOut, DoneOut, FoundOut):
         Lemmaid'Axiom -> ValueExpr
         Lemmaid'Pos -> Pos
         Lemmaid'Ident -> Ident
	 -- sweep for types
	 Collect_Type_ids(ValueExpr, nil -> DeclaredsTypeids)
	 -- sweep for values
         Collect_Value_ids(ValueExpr, DeclaredsTypeids -> DeclaredsValueids)
	 -- sweep for operators now part of Collect_Value_ids
         -- Collect_Redef_Opers(ValueExpr, DeclaredsValueids -> Decls2)

         Collect_Pos(ValueExpr, nil -> Bindings)
         Substract_Declareds_in_Bindings(DeclaredsValueids, Bindings -> Declareds2)

	 Get_TotalDeclareds(-> TotalDone)
         Substract_Declareds_s(Declareds2, TotalDone -> Declareds3)
 
         (|
            -- can be translated
           eq(Declareds3, nil)
           where(lemma_item(Lemmaid) -> Declared)
           where(Waiting -> WaitingOut)
           Insert_u_Declared(Declared, Done -> DoneOut)
--           Insert_u_Declared(Declared, TotalDone -> TotalDoneOut)
	   Add_Declared(Declared)  -- to TotalDeclareds
           where(found -> FoundOut)
         ||
            -- can NOT be translated
           where(lemma_item(Lemmaid) -> Declared)
           Insert_u_Declared(Declared, Waiting -> WaitingOut)
           where(Done -> DoneOut)
--           where(TotalDone -> TotalDoneOut)
           where(Found -> FoundOut)
         |)


--------------------------------------------------

'action' Gen_Sign_Decls(DECLAREDS, DECLAREDS, DECLAREDS
                        -> DECLAREDS, DECLAREDS)

  'rule' Gen_Sign_Decls(list(Decl, DeclsTail),
                             SignDecls1, SignDecls2
                             -> SignDeclsOut1, SignDeclsOut2):
         where(Decl -> value_item(Valueid))
	 Copy_value_id(Valueid -> Valueid2)
	 Valueid'Def -> Def
        (|
           where(Def -> expl_fun(Parms, _, _, Pre, _, _))
           Valueid2'Def <- expl_fun(Parms, no_val, nil, Pre, nil, nil)
           where(value_item(Valueid2) -> Decl1)
           Insert_Declared(Decl1, SignDecls1 -> SignDecls11)
        ||
           where(Def -> impl_fun(Parms, _, Pre, _))
	   -- slight kludge to use explicit as no "nil" for POST_CONDITION
           Valueid2'Def <- expl_fun(Parms, no_val, nil, Pre, nil, nil)
           where(value_item(Valueid2) -> Decl1)
           Insert_Declared(Decl1, SignDecls1 -> SignDecls11)
        |)

         where(value_item(Valueid) -> Decl2)
         Insert_Declared(Decl2, SignDecls2 -> SignDecls22)
         Gen_Sign_Decls(DeclsTail, SignDecls11, SignDecls22
                        -> SignDeclsOut1, SignDeclsOut2)

  'rule' Gen_Sign_Decls(nil, SignDecls1, SignDecls2
                        -> SignDecls1, SignDecls2):

--------------------------------------------------
--  Process Different Types Ids
--  to prepare for sorting
--  Subtype, Record and Variant
--------------------------------------------------

--------------------------------------------------
'action' Process_Subtype(TYPING, VALUE_EXPR, DECLAREDS -> DECLAREDS)

  'rule' Process_Subtype(Typing, ValueExpr, DeclaredsIn -> DeclaredsOut):
         Collect_Value_ids(ValueExpr, nil -> DeclaredsVal)
	 -- sweep for operators now part of Collect_Value_ids
         -- Collect_Redef_Opers(ValueExpr, DeclaredsVal -> DeclaredsOpers)
         Collect_Pos(Typing, nil -> Bindings1)
         Collect_Pos(ValueExpr, Bindings1 -> Bindings2)
         Substract_Declareds_in_Bindings(DeclaredsVal, Bindings2 -> Declareds2)
         Conc_Declareds(DeclaredsIn, Declareds2 -> DeclaredsOut)


--------------------------------------------------
'action' Process_Record_Type(COMPONENTS, DECLAREDS -> DECLAREDS)

  'rule' Process_Record_Type(Components, Declareds1 -> Declareds2):
         where(Declareds1 -> Declareds2)


--------------------------------------------------
'action' Process_Variant_Type(POS, IDENT, DECLAREDS -> DECLAREDS)

  'rule' Process_Variant_Type(Pos, Ident, Declareds -> Declaredsout):
         -- avoid recursion of the variant type
         Insert_Binding(single(Pos, id_op(Ident)), nil -> Bindings)
         Substract_Declareds_in_Bindings(Declareds, Bindings -> Declaredsout)


--------------------------------------------------
--  Process Different Value Ids
--  to prepare for sorting
--  Explicit and Implicit Values
--  Explicit and Implicit Functions
--------------------------------------------------


--------------------------------------------------
-- Treat Explicit Value
'action' Process_Expl_Val(VALUE_EXPR, DECLAREDS -> DECLAREDS)

  'rule' Process_Expl_Val(ValueExpr, Declareds -> Declaredsout):
         Collect_Value_ids(ValueExpr, nil -> DeclaredsVal)
	 -- sweep for operators now part of Collect_Value_ids
         -- Collect_Redef_Opers(ValueExpr, DeclaredsVal -> DeclaredsOpers)
         Collect_Pos(ValueExpr, nil -> Bindings)
         Collect_IdsInPattern(ValueExpr, Bindings -> Bindings2)
         Substract_Declareds_in_Bindings(DeclaredsVal, Bindings2 -> Declareds2)
         Conc_Declareds(Declareds, Declareds2 -> Declaredsout)

--------------------------------------------------
-- Treat Implicit Value
'action' Process_Impl_Val(VALUE_EXPR, POS, ID_OR_OP,
                          DECLAREDS -> DECLAREDS)

  'rule' Process_Impl_Val(ValueExpr, Pos, IdOp, DeclaredsIn -> DeclaredsOut):
         Collect_Value_ids(ValueExpr, nil -> DeclaredsVal)
	 -- sweep for operators now part of Collect_Value_ids
         -- Collect_Redef_Opers(ValueExpr, DeclaredsVal -> DeclaredsOpers)
         Collect_Pos(ValueExpr, nil -> Bindings)
         Collect_IdsInPattern(ValueExpr, Bindings -> Bindings2)
--         Insert_u_Binding(single(Pos, IdOp), Bindings -> Bindings1)
         Insert_Binding(single(Pos, IdOp), Bindings2 -> Bindings1)
         Substract_Declareds_in_Bindings(DeclaredsVal, Bindings1 -> Declareds2)
         Conc_Declareds(DeclaredsIn, Declareds2 -> DeclaredsOut)


--------------------------------------------------
-- Treat Explicit Function Expression
'action' Process_Expl_Fun_ValExpr(Value_id, DECLAREDS -> DECLAREDS)

  'rule' Process_Expl_Fun_ValExpr(Valueid, DeclaredsIn
                                  -> DeclaredsOut):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> IdOp
	 Valueid'Def -> Def
	 where(Def -> expl_fun(Params, ValueExpr, Post, Pre, OptCond, _))
	 -- sweep for valueids
         Collect_Value_ids(ValueExpr, nil -> DeclaredsValVE)
         -- To allow detecting simple recursive functions,
         -- toghether with mutual recursive functions,
         -- do NOT substract their Valueid ==> comment line:
         -- Substract_Valueid(...) and uncomment: where(,...).
         -- To detect simple recursive functions after
         -- leave Substract_Valueid(...) uncommented.
	 Substract_Valueid(DeclaredsValVE, Valueid -> DeclaredsOpersVE)
         -- where(DeclaredsValVE -> DeclaredsOpersVE)

	 -- sweep for operators now part of Collect_Value_ids
	 -- Collect_Redef_Opers(ValueExpr, DeclaredsVid -> DeclaredsOpersVE)
         Collect_Pos(Params, nil -> BindingsPar)
         Collect_Pos(ValueExpr, BindingsPar -> BindingsVE)
         Collect_IdsInPattern(ValueExpr, BindingsVE -> BindingsVE2)
         Substract_Declareds_in_Bindings(DeclaredsOpersVE,
                                    BindingsVE2 -> DeclaredsValVE1)
         Conc_Declareds(DeclaredsIn, DeclaredsValVE1 -> DeclaredsOut)


--------------------------------------------------
-- Treat explicit Function Post Expression
'action' Process_Expl_Fun_PostExpr(Value_id, DECLAREDS
                                    -> DECLAREDS)

  'rule' Process_Expl_Fun_PostExpr(Valueid, DeclaredsIn
                                    -> DeclaredsOut):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> IdOp
	 Valueid'Def -> Def
	 where(Def -> expl_fun(Params, ValueExpr, Post, Pre, OptCond, _))

         Collect_Value_ids(Post, nil -> DeclaredsValPE)

         -- To allow detecting simple recursive functions,
         -- toghether with mutual recursive functions,
         -- do NOT substract their Valueid ==> comment line:
         -- Substract_Valueid(...) and uncomment: where(,...).
         -- To detect simple recursive functions, when
         -- outputting them, leave Substract_Valueid(...)
	 -- uncommented.
	 Substract_Valueid(DeclaredsValPE, Valueid -> DeclaredsOpers)
	 -- where(DeclaredsValPE -> DeclaredsOpers)

	 -- sweep for operators now part of Collect_Value_ids
	 -- Collect_Redef_Opers(ValueExpr, DeclaredsVid -> DeclaredsOpers)
         Collect_Pos(Params, nil -> BindingsPE)
         Collect_Pos(Post, BindingsPE -> BindingsPE1)
         Collect_IdsInPattern(Post, BindingsPE1 -> BindingsPE2)
         Substract_Declareds_in_Bindings(DeclaredsOpers, BindingsPE2 -> DeclaredsValPE1)
         Conc_Declareds(DeclaredsIn, DeclaredsValPE1 -> DeclaredsOut)


--------------------------------------------------
-- Treat Explicit Function Pre Condition
'action' Process_Expl_Fun_PreExpr(Value_id, DECLAREDS
                                   -> DECLAREDS)

  'rule' Process_Expl_Fun_PreExpr(Valueid, DeclaredsIn
                                   -> DeclaredsOut):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> IdOp
	 Valueid'Def -> Def
	 where(Def -> expl_fun(Params, ValueExpr, Post, Pre, OptCond, _))
         Collect_Value_ids(Pre, nil -> DeclaredsValPre)
         -- To allow detecting simple recursive functions,
         -- toghether with mutual recursive functions,
         -- do NOT substract their Valueid ==> comment line:
         -- Substract_Valueid(...) and uncomment: where(,...).
         -- To detect simple recursive functions after
         -- leave Substract_Valueid(...) uncommented.
	 Substract_Valueid(DeclaredsValPre, Valueid -> DeclaredsOpers)
         -- where(DeclaredsValPre -> DeclaredsOpers)

	 -- sweep for operators now part of Collect_Value_ids
	 -- Collect_Redef_Opers(ValueExpr, DeclaredsVid -> DeclaredsOpers)
         Collect_Pos(Params, nil -> BindingsPre)
         Collect_Pos(Pre, BindingsPre -> BindingsPre1)
         Collect_IdsInPattern(ValueExpr, BindingsPre1 -> BindingsPre2)
         Substract_Declareds_in_Bindings(DeclaredsOpers,
                              BindingsPre2 -> DeclaredsValPre1)
         Conc_Declareds(DeclaredsIn, DeclaredsValPre1 -> DeclaredsOut)


--------------------------------------------------
-- Treat Implicit Function Post Expression
'action' Process_Impl_Fun_PostExpr(Value_id, DECLAREDS
                                    -> DECLAREDS)

  'rule' Process_Impl_Fun_PostExpr(Valueid, DeclaredsIn
                                    -> DeclaredsOut):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> IdOp
	 Valueid'Def -> Def
	 where(Def -> impl_fun(Params, Post, Pre, OptCond))

         Collect_Value_ids(Post, nil -> DeclaredsValPE)

         -- To allow detecting simple recursive functions,
         -- toghether with mutual recursive functions,
         -- do NOT substract their Valueid ==> comment line:
         -- Substract_Valueid(...) and uncomment: where(,...).
         -- To detect simple recursive functions, when
         -- outputting them, leave Substract_Valueid(...)
	 -- uncommented.
	 Substract_Valueid(DeclaredsValPE, Valueid -> DeclaredsOpers)
	 -- where(DeclaredsValPE -> DeclaredsOpers)

	 -- sweep for operators now part of Collect_Value_ids
	 -- Collect_Redef_Opers(ValueExpr, DeclaredsVid -> DeclaredsOpers)
         Collect_Pos(Params, nil -> BindingsPE)
         Collect_Pos(Post, BindingsPE -> BindingsPE1)
         Collect_IdsInPattern(Post, BindingsPE1 -> BindingsPE2)
         Substract_Declareds_in_Bindings(DeclaredsOpers, BindingsPE2 -> DeclaredsValPE1)
         Conc_Declareds(DeclaredsIn, DeclaredsValPE1 -> DeclaredsOut)


--------------------------------------------------
-- Treat Implicit Function Pre Condition
'action' Process_Impl_Fun_PreExpr(Value_id, DECLAREDS
                                   -> DECLAREDS)

  'rule' Process_Impl_Fun_PreExpr(Valueid, DeclaredsIn
                                   -> DeclaredsOut):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> IdOp
	 Valueid'Def -> Def
	 where(Def -> impl_fun(Params, Post, Pre, OptCond))

         Collect_Value_ids(Pre, nil -> DeclaredsValPre)
         -- To allow detecting simple recursive functions,
         -- toghether with mutual recursive functions,
         -- do NOT substract their Valueid ==> comment line:
         -- Substract_Valueid(...) and uncomment: where(,...).
         -- To detect simple recursive functions, when
         -- outputting them, leave Substract_Valueid(...)
	 -- uncommented.
	 Substract_Valueid(DeclaredsValPre, Valueid -> DeclaredsOpers)
         -- where(DeclaredsValPre -> DeclaredsOpers)

	 -- sweep for operators now part of Collect_Value_ids
	 -- Collect_Redef_Opers(ValueExpr, DeclaredsVid -> DeclaredsOpers)
         Collect_Pos(Params, nil -> BindingsPre)
         Collect_Pos(Pre, BindingsPre -> BindingsPre1)
         Collect_IdsInPattern(Pre, BindingsPre1 -> BindingsPre2)

         Substract_Declareds_in_Bindings(DeclaredsOpers, BindingsPre2
                                  -> DeclaredsValPre1)
         Conc_Declareds(DeclaredsIn, DeclaredsValPre1 -> DeclaredsOut)


