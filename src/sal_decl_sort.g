-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the sort for RSL Declares
-- to comply with PVS define before use rule

-- Also defines the actions to get the types and
-- values (Type_ids and Value_ids) to be sorted


'module' sal_decl_sort

'use' ast print ext env objects values types pp cc cpp
      pvs pvs_ast pvs_aux sal_ast
      sal_print sal_global_vars
     

'export' 
         -- Actions
	 SAL_Init_TotalDeclareds
         SAL_Gen_Declareds
         SAL_Sort_Declareds
	 

'var' SAL_TotalDeclareds	 : SORTED_DECLS_S



--------------------------------------------------
-- Get Type_ids and Value_ids to be sorted
--------------------------------------------------


--------------------------------------------------
'action' SAL_Gen_Declareds(DECLS, SORTED_DECLS -> SORTED_DECLS)

         -- end of recursion
  'rule' SAL_Gen_Declareds(nil, Declareds -> Declareds1):
         where(Declareds -> Declareds1)

          -- Decl is Type
  'rule' SAL_Gen_Declareds(list(type_decl(Pos, TypeDefs), DeclsTail), Declareds -> Declareds1):
         SAL_Get_Type_Defs(TypeDefs, Declareds -> Declareds2)
         SAL_Gen_Declareds(DeclsTail, Declareds2 -> Declareds1)

          -- Decl is Value
  'rule' SAL_Gen_Declareds(list(value_decl(Pos, ValueDefs), DeclsTail), Declareds -> Declareds1):
         Get_current_top_values(-> Valueids)
         SAL_Get_Value_Defs(Valueids, ValueDefs, Declareds -> Declareds2)
         SAL_Gen_Declareds(DeclsTail, Declareds2 -> Declareds1)

          -- Decl is Variable: not supported
  'rule' SAL_Gen_Declareds(list(variable_decl(Pos, _), DeclsTail), Declareds -> Declareds1):
         Puterror(Pos)
         Putmsg("Variable declarations not supported")
         Putnl()
         SAL_Gen_Declareds(DeclsTail, Declareds -> Declareds1)

          -- Decl is Channel: not supported
  'rule' SAL_Gen_Declareds(list(channel_decl(Pos,  _), DeclsTail), Declareds -> Declareds1):
         Puterror(Pos)
         Putmsg("Channel declarations not supported")
         Putnl()
         SAL_Gen_Declareds(DeclsTail, Declareds -> Declareds1)

          -- Decl is Object: ignore
  'rule' SAL_Gen_Declareds(list(object_decl(Pos, ObjectDefs), DeclsTail),
                       Declareds -> DeclaredsOut):
	 SAL_Get_Object_Decls(ObjectDefs, Declareds -> Declareds2)
         SAL_Gen_Declareds(DeclsTail, Declareds2 -> DeclaredsOut)       


          -- Decl is Axiom
  'rule' SAL_Gen_Declareds(list(axiom_decl(Pos, AxiomDefs), DeclsTail),
                              Declareds -> Declaredsout):
         Get_current_axioms(-> AxiomEnv)
         SAL_Process_Axiom_Env(AxiomEnv, nil -> DeclaredsAxioms)
--print("***********DeclaredsAxioms************")
--PrintDeclareds(DeclaredsAxioms)
	 SAL_Rev_Declareds(DeclaredsAxioms, nil -> DeclaredsAxioms2)
	 SAL_Conc_Declareds(Declareds, DeclaredsAxioms2 -> Declareds1)
         SAL_Gen_Declareds(DeclsTail, Declareds1 -> Declaredsout)

          -- Decl is Test_case: not supported
  'rule' SAL_Gen_Declareds(list(test_case_decl(Pos, _), DeclsTail), Declareds -> Declareds1):
         Putwarning(Pos)
         Putmsg("Test case declarations are ignored")
         Putnl()
         SAL_Gen_Declareds(DeclsTail, Declareds -> Declareds1)

  'rule' SAL_Gen_Declareds(list(trans_system_decl(Pos, Defs), DeclsTail), Declareds -> DeclaredsOut):
	 Get_current_transition_systems(top -> TSEnv)
	 SAL_Process_TS_Env(TSEnv, nil -> DeclaredsTS)
	 SAL_Rev_Declareds(DeclaredsTS, nil -> DeclaredsTS2)
	 SAL_Conc_Declareds(Declareds, DeclaredsTS2 -> Declareds1)
         SAL_Gen_Declareds(DeclsTail, Declareds1 -> DeclaredsOut)

  'rule' SAL_Gen_Declareds(list(property_decl(Pos, Defs), DeclsTail), Declareds -> DeclaredsOut):
	 Get_current_properties(top -> TSEnv)
	 SAL_Process_property_Env(TSEnv, nil -> DeclaredsTS)
	 SAL_Rev_Declareds(DeclaredsTS, nil -> DeclaredsTS2)
	 SAL_Conc_Declareds(Declareds, DeclaredsTS2 -> Declareds1)
         SAL_Gen_Declareds(DeclsTail, Declareds1 -> DeclaredsOut)
--------------------------------------------------
'action' SAL_Get_Type_Defs(TYPE_DEFS, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Get_Type_Defs(list(TypeDef, TypeDefsTail), Declareds -> Declareds1):
         (|
           SAL_Get_Type_Def(TypeDef -> type_id(Typeid))
           where(SORTED_DECL_ITEM'type_item(Typeid) -> Declared)
--           SAL_Insert_u_Declared(Declared, Declareds -> Declareds2)
           SAL_Insert_Declared(Declared, Declareds -> Declareds2)
           SAL_Get_Type_Defs(TypeDefsTail, Declareds2 -> Declareds1)
         ||
           SAL_Get_Type_Defs(TypeDefsTail, Declareds -> Declareds1)
         |)

         -- no more Type_Defs
  'rule' SAL_Get_Type_Defs(nil, Declareds -> Declareds):



--------------------------------------------------
'action' SAL_Get_Type_Def(TYPE_DEF -> OPT_TYPE_ID)

  'rule' SAL_Get_Type_Def(abbrev(Pos, Id, _) -> type_id(Typeid)):
         Get_current_types(-> TE)
         (|
           Lookup_env(Id, TE -> type_id(Typeid))
         || -- may be local: try with localised name
           Localise_id(Pos, Id -> LId)
           Lookup_env(LId, TE -> type_id(Typeid))
         |)

  'rule' SAL_Get_Type_Def(sort(Pos, Id) -> type_id(Typeid)):
         Get_current_types(-> TE)
         (|
           Lookup_env(Id, TE -> type_id(Typeid))
         || -- may be local: try with localised name
           Localise_id(Pos, Id -> LId)
           Lookup_env(LId, TE -> type_id(Typeid))
         |)

  'rule' SAL_Get_Type_Def(variant(Pos, Id, CS) -> type_id(Typeid)):
         Get_current_types(-> TE)
         (|
           Lookup_env(Id, TE -> type_id(Typeid))
         || -- may be local: try with localised name
           Localise_id(Pos, Id -> LId)
           Lookup_env(LId, TE -> type_id(Typeid))
         |)

  'rule' SAL_Get_Type_Def(record(Pos, Id, _) -> type_id(Typeid)):
         Get_current_types(-> TE)
         (|
           Lookup_env(Id, TE -> type_id(Typeid))
         || -- may be local: try with localised name
           Localise_id(Pos, Id -> LId)
           Lookup_env(LId, TE -> type_id(Typeid))
         |)

  'rule' SAL_Get_Type_Def(union(Pos, Id, CS) -> nil):
         Puterror(Pos)
         Putmsg("Cannot translate union types: ignored")
         Putnl()
--------------------------------------------------
'action' SAL_Get_Object_Decls(OBJECT_DEFS, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Get_Object_Decls(list(ObjectDef, ObjectDefsTail), Declareds -> Declareds1):
         where(ObjectDef -> odef(Pos,Iden,Params,Class))
         where(SORTED_DECL_ITEM'object_item(Pos,Iden,Params,Class) -> Declared)
         SAL_Insert_Declared(Declared, Declareds -> Declareds2)
         SAL_Get_Object_Decls(ObjectDefsTail, Declareds2 -> Declareds1)

         -- no more Object_Defs
  'rule' SAL_Get_Object_Decls(nil, Declareds -> Declareds):

--------------------------------------------------
'action' SAL_Get_Value_Defs(Value_ids, VALUE_DEFS, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Get_Value_Defs(Valueids, list(ValueDef, ValueDefsTail), Declareds -> Declareds3):
         SAL_Get_Value_Def(Valueids, ValueDef -> Declareds1)
         SAL_Conc_Declareds(Declareds, Declareds1 -> Declareds2)
         SAL_Get_Value_Defs(Valueids, ValueDefsTail, Declareds2 -> Declareds3)

         -- no more Value_Defs
  'rule' SAL_Get_Value_Defs(Valueids, nil, Declareds -> Declareds):



--------------------------------------------------
'action' SAL_Get_Value_Def(Value_ids, VALUE_DEF -> SORTED_DECLS)

  'rule' SAL_Get_Value_Def(Valueids, typing(_, single(_, B, _)) -> Declrds):
         SAL_Get_Value_binding(Valueids, B -> Declrds)

  'rule' SAL_Get_Value_Def(Valueids, typing(_, multiple(_, Bs, _)) -> Declrds):
         SAL_Get_Value_bindings(Valueids, Bs -> Declrds)
         
  'rule' SAL_Get_Value_Def(Valueids, exp_val(_, single(_, B, _), _) -> Declrds):
         SAL_Get_Value_binding(Valueids, B -> Declrds)

  'rule' SAL_Get_Value_Def(Valueids, exp_fun(_, single(_, B, _), _, _, _, _, _) -> Declrds):
         SAL_Get_Value_binding(Valueids, B -> Declrds)

  'rule' SAL_Get_Value_Def(Valueids, imp_val(_, single(_, B, _), _) -> Declrds):
         SAL_Get_Value_binding(Valueids, B -> Declrds)

  'rule' SAL_Get_Value_Def(Valueids, imp_fun(_, single(_, B,_), _, _, _) -> Declrds):
         SAL_Get_Value_binding(Valueids, B -> Declrds)



--------------------------------------------------
'action' SAL_Get_Value_binding(Value_ids, BINDING -> SORTED_DECLS)

  'rule' SAL_Get_Value_binding(Valueids, single(P, _) -> list(Declrd, nil)):
         Select_id_by_pos(P, Valueids -> value_id(Valueid))
         where(SORTED_DECL_ITEM'value_item(Valueid) -> Declrd)

  'rule' SAL_Get_Value_binding(Valueids, product(_, Bs) -> Declrds):
         SAL_Get_Value_bindings(Valueids, Bs -> Declrds)

  'rule' SAL_Get_Value_binding(Valueids, single(P, _) -> nil):


--------------------------------------------------
'action' SAL_Get_Value_bindings(Value_ids, BINDINGS -> SORTED_DECLS)

  'rule' SAL_Get_Value_bindings(Valueids, list(B, Bs) -> Declrds):
         SAL_Get_Value_bindings(Valueids, Bs -> Declrds1)
         (|
           where(B -> single(P, _))
           Select_id_by_pos(P, Valueids -> value_id(Valueid))
           where(SORTED_DECLS'list(SORTED_DECL_ITEM'value_item(Valueid), Declrds1) -> Declrds)
         ||
           where(B -> product(P, Bs1))
           SAL_Get_Value_bindings(Valueids, Bs1 -> Declrds2)
           SAL_Conc_Declareds(Declrds1, Declrds2 -> Declrds)
         |)

  'rule' SAL_Get_Value_bindings(_, nil -> nil):



--------------------------------------------------
'action' SAL_Get_Axiom_Defs(AXIOM_DEFS, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Get_Axiom_Defs(list(AxiomDef, AxiomDefsTail),
                        Declareds -> Declaredsout):
         SAL_Get_Axiom_Def(AxiomDef -> Declareds1)
         SAL_Conc_Declareds(Declareds, Declareds1 -> Declareds2)
         SAL_Get_Axiom_Defs(AxiomDefsTail, Declareds2 -> Declaredsout)

         -- no more Axiom_Defs
  'rule' SAL_Get_Axiom_Defs(nil, Declareds -> Declareds):


--------------------------------------------------
'action' SAL_Get_Axiom_Def(AXIOM_DEF -> SORTED_DECLS)

  'rule' SAL_Get_Axiom_Def(AxiomDef -> Declaredsout):
         Get_current_axioms(-> AxiomEnv)
         SAL_Process_Axiom_Env(AxiomEnv, nil -> Declaredsout)


--------------------------------------------------
'action' SAL_Process_Axiom_Env(AXIOM_ENV, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Process_Axiom_Env(axiom_env(Axiomid, AxiomEnv),
                           Declareds -> Declaredsout):
--         Axiomid'Axiom -> ValueExpr
--	 (| -- if theory generate lemma 
--	   IsTheory
           where(SORTED_DECL_ITEM'lemma_item(Axiomid) -> Declared)
--	 || -- not a theory: generate axiom
 --          where(SORTED_DECL_ITEM'axiom_item(Axiomid) -> Declared)
--	 |)	 	

         SAL_Insert_u_Declared(Declared, Declareds -> Declareds1)
--         Insert_Declared(Declared, Declareds -> Declareds1)
         SAL_Process_Axiom_Env(AxiomEnv, Declareds1 -> Declaredsout)

  'rule' SAL_Process_Axiom_Env(nil, Declareds -> Declareds):

--------------------------------------------------
'action' SAL_Process_TS_Env(TRANS_SYS_ENV, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Process_TS_Env(trans_sys_env(TSid, TSEnv),
                           Declareds -> Declaredsout):
         where(SORTED_DECL_ITEM'ts_item(TSid) -> Declared)
         SAL_Insert_u_Declared(Declared, Declareds -> Declareds1)
         SAL_Process_TS_Env(TSEnv, Declareds1 -> Declaredsout)

  'rule' SAL_Process_TS_Env(nil, Declareds -> Declareds):

---------------------------------------------------
'action' SAL_Process_property_Env(PROPERTY_ENV, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Process_property_Env(prop_env(Pid, Env), Declareds -> Declaredsout):
         where(prop_item(Pid) -> Declared)
         SAL_Insert_u_Declared(Declared, Declareds -> Declareds1)
         SAL_Process_property_Env(Env, Declareds1 -> Declaredsout)

  'rule' SAL_Process_property_Env(nil, Declareds -> Declareds):
--------------------------------------------------
-- Sorts the declares in RSL
--------------------------------------------------


--------------------------------------------------
'action' SAL_Sort_Declareds(SORTED_DECLS,      -- ToDo 
                        SORTED_DECLS,      -- Waiting
                        SORTED_DECLS,      -- Done
                        FOUND
                     -> SORTED_DECLS)      -- SortedDeclareds

         -- end of recursion
  'rule' SAL_Sort_Declareds(nil, nil, Done, _ -> Done):

          -- found, some waiting  ==> another pass
  'rule' SAL_Sort_Declareds(nil, Waiting, Done, found -> DoneOut):
	 SAL_Sort_Declareds(Waiting, nil, Done, nil -> DoneOut)

          -- found  ==> another pass trying waiting first
          -- (slow but keeps original order as much as possible)

  'rule' SAL_Sort_Declareds(Declrds, Waiting, Done, found -> DoneOut):
         SAL_Conc_Declareds(Waiting, Declrds -> Declrds1)
         SAL_Sort_Declareds(Declrds1, nil, Done, nil -> DoneOut)
          -- not found, some waiting  ==> 
	  -- split functions into signatures and axioms and try again
  'rule' SAL_Sort_Declareds(nil, Waiting, Done, nil -> Doneout):
	 (| -- Are there any defined functions waiting?
	   SAL_Are_Functions(Waiting, nil -> FunDecls)
	   -- YES
	   -- Remove the functions from waiting
           SAL_Substract_Declareds(Waiting, FunDecls -> Waiting1)
	   -- Make all signatures in FunDecls as
	   -- value decl, no_def (function signature)
	   -- only id + TypeExpr
	   -- This makes a suitable copy of each Value_id
	   -- but with no definition, puts that in SignFunDecls
	   -- and the original in FunDecls2
	   SAL_Gen_Sign_Decls(FunDecls, nil, nil -> SignFunDecls, FunDecls2)
	   -- put the function signatures as done
	   SAL_Conc_Declareds(Done, SignFunDecls -> Done1)
	   SAL_Sort_Declareds(Waiting1, nil, Done1, found -> Done2)
	   -- Make all definitions in FunDecls as
	   -- mutually recursive functions
	   -- to be inserted in Done so after
	   -- only their axioms need to be generated
           where(SORTED_DECL_ITEM'rec_item(FunDecls2) -> Decl)
           SAL_Insert_Declared(Decl, Done2 -> Doneout)
	   SAL_Add_Declared(Decl)  -- to TotalDeclareds
	 ||
	   -- no functions left: mutually recursive types
	   where(Waiting -> SORTED_DECLS'list(Decl, Decls))
	   (|
	     where(Decl -> type_item(Typeid))
	     Typeid'Pos -> Pos
	     Typeid'Ident -> Ident
	     Puterror(Pos)
	     Print_id(Ident)
	     Putmsg(" seems to be involved in mutual recursion")
	     Putnl()
	   ||
	     where(Decl -> lemma_item(AxiomId))
	     AxiomId'Pos -> Pos
	     Puterror(Pos)
	     Putmsg("The axiom declaration seems to be involved in mutual recursion\n")
	     print(Decls)
	   ||
	     DefaultPos(-> Pos)
	     Puterror(Pos)
	     Putmsg("Internal error for declaration ")
	     print(Decl)
	     Putnl()
	   |)
	   where(Done -> Doneout)
	 |)


          -- Decl is Type
  'rule' SAL_Sort_Declareds(list(type_item(Typeid), DeclrdsTail),
                        Waiting, Done, Found -> DoneOut):
         SAL_Sort_Type_id(Typeid, Waiting, Done, Found
                      -> Waiting1, Done1, Found1)
         SAL_Sort_Declareds(DeclrdsTail, Waiting1, Done1, Found1
                        -> DoneOut)

          -- Decl is Value
  'rule' SAL_Sort_Declareds(list(SORTED_DECL_ITEM'value_item(Valueid), DeclrdsTail),
                        Waiting, Done, Found -> DoneOut):
         SAL_Sort_Value_id(Valueid, Waiting, Done, Found
                       -> Waiting1, Done1, Found1)
         SAL_Sort_Declareds(DeclrdsTail, Waiting1, Done1, Found1
                        -> DoneOut)


          -- Decl is Object
  'rule' SAL_Sort_Declareds(list(SORTED_DECL_ITEM'object_item(P,Id,Params,Class), DeclrdsTail),
                        Waiting, Done, Found -> DoneOut):
         SAL_Sort_Object_Decl(object_item(P,Id,Params,Class), Waiting, Done, Found
                       -> Waiting1, Done1, Found1)
         SAL_Sort_Declareds(DeclrdsTail, Waiting1, Done1, Found1
                        -> DoneOut)

          -- Decl is Axiom
  'rule' SAL_Sort_Declareds(list(SORTED_DECL_ITEM'axiom_item(Axiomid), DeclrdsTail),
                        Waiting, Done, Found
                        -> DoneOut):
         SAL_Sort_Axiom_id(Axiomid, Waiting, Done, Found
                       -> Waiting1, Done1, Found1)
         SAL_Sort_Declareds(DeclrdsTail, Waiting1, Done1, Found1
                        -> DoneOut)

          -- Decl is lemma
  'rule' SAL_Sort_Declareds(list(SORTED_DECL_ITEM'lemma_item(Axiomid), DeclrdsTail),
                        Waiting, Done, Found
                        -> DoneOut):
         SAL_Sort_Lemma_id(Axiomid, Waiting, Done, Found
                       -> Waiting1, Done1, Found1)
         SAL_Sort_Declareds(DeclrdsTail, Waiting1, Done1, Found1
                        -> DoneOut)


  'rule' SAL_Sort_Declareds(list(SORTED_DECL_ITEM'ts_item(TSid), DeclrdsTail),
                        Waiting, Done, Found
                        -> DoneOut):
         SAL_Sort_TS_id(TSid, Waiting, Done, Found
                       -> Waiting1, Done1, Found1)
         SAL_Sort_Declareds(DeclrdsTail, Waiting1, Done1, Found1
                        -> DoneOut)

  'rule' SAL_Sort_Declareds(list(SORTED_DECL_ITEM'prop_item(Pid), DeclrdsTail),
                        Waiting, Done, Found
                        -> DoneOut):
         SAL_Sort_Prop_id(Pid, Waiting, Done, Found
                       -> Waiting1, Done1, Found1)
         SAL_Sort_Declareds(DeclrdsTail, Waiting1, Done1, Found1
                        -> DoneOut)

--------------------------------------------------
'action' SAL_Sort_Type_id(Type_id, SORTED_DECLS, SORTED_DECLS, FOUND
                      -> SORTED_DECLS, SORTED_DECLS, FOUND)

  'rule' SAL_Sort_Type_id(Typeid, Waiting, Done, Found
                      -> WaitingOut, DoneOut, FoundOut):
         Typeid'Type -> Type
         Typeid'Ident -> Ident
         Typeid'Pos -> Pos
         SAL_Collect_Type_ids(Type, nil -> Declareds1)
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
           SAL_Process_Subtype(Typing, ValueExpr, Declareds1 -> Declareds2)
         || -- is sort kind?
           where(Type -> sort(SortKind))
           (| -- is record?
             where(SortKind -> record(Components))
             SAL_Collect_Type_ids(Components, Declareds1 -> DeclaredsVaT)
	     -- get the Value_ids in Components for TotalDeclareds
	     SAL_Collect_Value_id_Variant(Components, nil -> DeclrdsValueid1)
	     -- get the mk_ Value_id for TotalDeclareds
	     Get_current_top_values(-> Valueids)
	     Select_id_by_pos(Pos, Valueids -> value_id(Valueid))
	     SAL_Insert_Declared(SORTED_DECL_ITEM'value_item(Valueid), DeclrdsValueid1
                             -> DeclrdsValueid)
	     -- add them to TotalDeclareds
	     SAL_Add_Declareds(DeclrdsValueid)
             SAL_Process_Record_Type(Components, DeclaredsVaT -> Declareds2)
           || -- is variant?
             where(SortKind -> variant(Variants))
             SAL_Collect_Type_ids(Variants, Declareds1 -> DeclaredsVaT)
	     SAL_Collect_Value_id_Variant(Variants, nil -> DeclrdsValueid)
	     SAL_Add_Declareds(DeclrdsValueid)
             SAL_Process_Variant_Type(Pos, Ident, DeclaredsVaT -> Declareds2)
           || -- is union or abstract?
             -- union not supported: ignored
             -- abstract: no need to look for anything further 
             where(Declareds1 -> Declareds2)
           |)
         ||
           where(Declareds1 -> Declareds2)
         |)

	 SAL_Get_TotalDeclareds(-> TotalDone)
         SAL_Substract_Declareds_s(Declareds2, TotalDone -> Declareds3)
-- debug
--Putmsg("Type ")
--Print_id(Ident)
         (|
            -- can be translated
           eq(Declareds3, nil)
--Putmsg(" done\n")
           where(SORTED_DECL_ITEM'type_item(Typeid) -> Declared)
           where(Waiting -> WaitingOut)
           SAL_Insert_u_Declared(Declared, Done -> DoneOut)
--           SAL_Insert_u_Declared(Declared, TotalDone -> TotalDoneOut)
	   SAL_Add_Declared(Declared)  -- to TotalDeclareds
           where(found -> FoundOut)
         ||
-- Putmsg(" waiting for ")
-- PrintDeclareds(Declareds3)
-- Putnl()
            -- can NOT be translated
           where(SORTED_DECL_ITEM'type_item(Typeid) -> Declared)
           SAL_Insert_u_Declared(Declared, Waiting -> WaitingOut)
--           where(TotalDone -> TotalDoneOut)
           where(Done -> DoneOut)
           where(Found -> FoundOut)
         |)


--------------------------------------------------
'action' SAL_Sort_Value_id(Value_id, SORTED_DECLS, SORTED_DECLS, FOUND
                       -> SORTED_DECLS, SORTED_DECLS, FOUND)

  'rule' SAL_Sort_Value_id(Valueid, Waiting, Done, Found
                       -> WaitingOut, DoneOut, FoundOut):
         Valueid'Type -> Type
         Valueid'Pos -> Pos
         Valueid'Ident -> IdOp
         SAL_Collect_Type_ids(Type, nil -> Declareds1)
         Valueid'Def -> ValueDef

         (| -- No Definition
           where(ValueDef -> no_def)
           where(Declareds1 -> Declareds2)

         || -- Explicit Value
           where(ValueDef -> expl_val(ValueExpr, _))
           SAL_Process_Expl_Val(ValueExpr, Declareds1 -> Declareds2)

         || -- Implicit Value
           where(ValueDef -> impl_val(ValueExpr))
           SAL_Process_Impl_Val(ValueExpr, Pos, IdOp, Declareds1 -> Declareds2)

         || -- Explicit Function
           where(ValueDef -> expl_fun(Params, ValueExpr, Post, Pre, OptCond, _))
           -- Value Expresion
           SAL_Process_Expl_Fun_ValExpr(Valueid, Declareds1 -> DeclaredsVE1)
           -- Post Expresion
           SAL_Process_Expl_Fun_PostExpr(Valueid, DeclaredsVE1 -> DeclaredsVE2)
           -- Pre Condition Expresion
           SAL_Process_Expl_Fun_PreExpr(Valueid, DeclaredsVE2 -> Declareds2)

         || -- Implicit Function
           where(ValueDef -> impl_fun(Params, Post, Pre, OptCond))
           -- Post Expresion
           SAL_Process_Impl_Fun_PostExpr(Valueid, Declareds1 -> DeclaredsPE)
           -- Pre Condition Expresion
           SAL_Process_Impl_Fun_PreExpr(Valueid, DeclaredsPE -> Declareds2)
         |)

	 SAL_Get_TotalDeclareds(-> TotalDone)
         SAL_Substract_Declareds_s(Declareds2, TotalDone -> Declareds3)
-- debug
-- Putmsg("Value ")
-- Print_id_or_op(IdOp)
         (|
            -- can be translated
           eq(Declareds3, nil)
-- Putmsg(" done\n")
           where(SORTED_DECL_ITEM'value_item(Valueid) -> Declared)
           where(Waiting -> WaitingOut)
           SAL_Insert_u_Declared(Declared, Done -> DoneOut)
--           SAL_Insert_u_Declared(Declared, TotalDone -> TotalDoneOut)
	   SAL_Add_Declared(Declared)  -- to TotalDeclareds
           where(found -> FoundOut)
         ||
            -- can NOT be translated
-- Putmsg(" waiting for ")
-- PrintDeclareds(Declareds3)
-- Putnl()
           where(SORTED_DECL_ITEM'value_item(Valueid) -> Declared)
           SAL_Insert_u_Declared(Declared, Waiting -> WaitingOut)
           where(Done -> DoneOut)
           where(TotalDone -> TotalDoneOut)
           where(Found -> FoundOut)
         |)

--------------------------------------------------------------------------
'action' SAL_Sort_Object_Decl(SORTED_DECL_ITEM, SORTED_DECLS, SORTED_DECLS, FOUND
                       -> SORTED_DECLS, SORTED_DECLS, FOUND)

  'rule' SAL_Sort_Object_Decl(object_item(Pos,Id,Params,Class), Waiting, Done, Found
                       -> WaitingOut, DoneOut, FoundOut):
	 -- No sorting...
         where(Waiting -> WaitingOut)
         SAL_Insert_u_Declared(object_item(Pos,Id,Params,Class), Done -> DoneOut)
	 SAL_Add_Declared(object_item(Pos,Id,Params,Class))
	 where(Found -> FoundOut)

--------------------------------------------------
'action' SAL_Sort_Axiom_id(Axiom_id, SORTED_DECLS, SORTED_DECLS, FOUND
                       -> SORTED_DECLS, SORTED_DECLS, FOUND)

  'rule' SAL_Sort_Axiom_id(Axiomid, Waiting, Done, Found
                       -> WaitingOut, DoneOut, FoundOut):
         Axiomid'Axiom -> ValueExpr
         Axiomid'Pos -> Pos
         Axiomid'Ident -> Ident
	 -- sweep for types
	 SAL_Collect_Type_ids(ValueExpr, nil -> DeclaredsTypeids)
	 -- sweep for values
         SAL_Collect_Value_ids(ValueExpr, DeclaredsTypeids -> DeclaredsValueids)
	 -- sweep for operators now part of SAL_Collect_Value_ids
         -- Collect_Redef_Opers(ValueExpr, DeclaredsValueids -> Decls2)


         Collect_Pos(ValueExpr, nil -> Bindings)
         SAL_Substract_Declareds_in_Bindings(DeclaredsValueids, Bindings -> Declareds2)

	 SAL_Get_TotalDeclareds(-> TotalDone)
         SAL_Substract_Declareds_s(Declareds2, TotalDone -> Declareds3)
         (|
            -- can be translated
           eq(Declareds3, nil)
           where(SORTED_DECL_ITEM'axiom_item(Axiomid) -> Declared)
           where(Waiting -> WaitingOut)
           SAL_Insert_u_Declared(Declared, Done -> DoneOut)
--           SAL_Insert_u_Declared(Declared, TotalDone -> TotalDoneOut)
	   SAL_Add_Declared(Declared)  -- to TotalDeclareds
           where(found -> FoundOut)
         ||
            -- can NOT be translated
           where(SORTED_DECL_ITEM'axiom_item(Axiomid) -> Declared)
           SAL_Insert_u_Declared(Declared, Waiting -> WaitingOut)
           where(Done -> DoneOut)
--           where(TotalDone -> TotalDoneOut)
           where(Found -> FoundOut)
         |)


--------------------------------------------------
'action' SAL_Sort_Lemma_id(Axiom_id, SORTED_DECLS, SORTED_DECLS, FOUND
                       -> SORTED_DECLS, SORTED_DECLS, FOUND)

  'rule' SAL_Sort_Lemma_id(Lemmaid, Waiting, Done, Found
                       -> WaitingOut, DoneOut, FoundOut):
         Lemmaid'Axiom -> ValueExpr
         Lemmaid'Pos -> Pos
         Lemmaid'Ident -> Ident
	 -- sweep for types
	 SAL_Collect_Type_ids(ValueExpr, nil -> DeclaredsTypeids)
	 -- sweep for values
         SAL_Collect_Value_ids(ValueExpr, DeclaredsTypeids -> DeclaredsValueids)
	 -- sweep for operators now part of SAL_Collect_Value_ids
         -- Collect_Redef_Opers(ValueExpr, DeclaredsValueids -> Decls2)

         Collect_Pos(ValueExpr, nil -> Bindings)
         SAL_Substract_Declareds_in_Bindings(DeclaredsValueids, Bindings -> Declareds2)

	 SAL_Get_TotalDeclareds(-> TotalDone)
         SAL_Substract_Declareds_s(Declareds2, TotalDone -> Declareds3)
 
         (|
            -- can be translated
           eq(Declareds3, nil)
           where(SORTED_DECL_ITEM'lemma_item(Lemmaid) -> Declared)
           where(Waiting -> WaitingOut)
           SAL_Insert_u_Declared(Declared, Done -> DoneOut)
--           SAL_Insert_u_Declared(Declared, TotalDone -> TotalDoneOut)
	   SAL_Add_Declared(Declared)  -- to TotalDeclareds
           where(found -> FoundOut)
         ||
            -- can NOT be translated
           where(SORTED_DECL_ITEM'lemma_item(Lemmaid) -> Declared)
           SAL_Insert_u_Declared(Declared, Waiting -> WaitingOut)
           where(Done -> DoneOut)
--           where(TotalDone -> TotalDoneOut)
           where(Found -> FoundOut)
         |)

--------------------------------------------------
'action' SAL_Sort_TS_id(Transition_system_id, SORTED_DECLS, SORTED_DECLS, FOUND
                       -> SORTED_DECLS, SORTED_DECLS, FOUND)

  'rule' SAL_Sort_TS_id(TSid, Waiting, Done, Found
                       -> WaitingOut, DoneOut, FoundOut):
         TSid'Trans_sys -> SysDesc
         TSid'Pos -> Pos
         TSid'Ident -> Ident
	 -- Multiple invocations to sweep for types
	 SAL_Collect_Type_Ids_from_TS(SysDesc, nil -> DeclaredsTypeids)
	 -- Idem for sweep for values
	 SAL_Collect_Value_Ids_from_TS(SysDesc, DeclaredsTypeids -> DeclaredsValueids)

	 SAL_Collect_Pos_from_TS(SysDesc, nil -> Bindings)
         SAL_Substract_Declareds_in_Bindings(DeclaredsValueids, Bindings -> Declareds2)

	 SAL_Get_TotalDeclareds(-> TotalDone)
         SAL_Substract_Declareds_s(Declareds2, TotalDone -> Declareds3)
--Putmsg("Sorting declaration of TS: ")
--Print_id(Ident)
--Putnl()
         (|
--Putmsg("Transition system (")
--Print_id(Ident)
--Putmsg(") translated\n")
            -- can be translated
           eq(Declareds3, nil)
           where(SORTED_DECL_ITEM'ts_item(TSid) -> Declared)
           where(Waiting -> WaitingOut)
           SAL_Insert_u_Declared(Declared, Done -> DoneOut)
	   SAL_Add_Declared(Declared)  -- to TotalDeclareds
           where(found -> FoundOut)
         ||
--Putmsg("Transition system (")
--Print_id(Ident)
--Putmsg(") can't be translated\n")
--SAL_Print_Declareds(Declareds3)
            -- can NOT be translated
           where(SORTED_DECL_ITEM'ts_item(TSid) -> Declared)
           SAL_Insert_u_Declared(Declared, Waiting -> WaitingOut)
           where(Done -> DoneOut)
           where(Found -> FoundOut)
         |)


--------------------------------------------------
'action' SAL_Sort_Prop_id(Property_id, SORTED_DECLS, SORTED_DECLS, FOUND
                       -> SORTED_DECLS, SORTED_DECLS, FOUND)

  'rule' SAL_Sort_Prop_id(Pid, Waiting, Done, Found
                       -> WaitingOut, DoneOut, FoundOut):
         Pid'Resolved_Prop -> Prop
         Pid'Pos -> Pos
         Pid'Ident -> Ident
	 where(Prop -> r_prop(_,_,TSid, Expr))
	 -- Enable the use of LTL functions:
	 Set_LTL_Wanted()
	 -- Multiple invocations to sweep for types
	 SAL_Collect_Type_ids(Expr, nil -> DeclaredsTypeids)
	 -- Idem for sweep for values
	 SAL_Collect_Value_ids(Expr, DeclaredsTypeids -> DeclaredsValueids1) --DeclaredsValueids1
	 
	 where(SORTED_DECLS'list(SORTED_DECL_ITEM'ts_item(TSid), DeclaredsValueids1) -> DeclaredsValueids)
	 -- Process the TS:
--	 TSid'Trans_sys -> SysDesc
	 -- Multiple invocations to sweep for types
--	 SAL_Collect_Type_Ids_from_TS(SysDesc, DeclaredsValueids1 -> DeclaredsTypeids1)
	 -- Idem for sweep for values
--	 SAL_Collect_Value_Ids_from_TS(SysDesc, DeclaredsTypeids1 -> DeclaredsValueids)	 

	 -- Disable the use of LTL functions:
	 Clear_LTL_Wanted()
	 
	 Collect_Pos(Expr, nil -> Bindings)
         SAL_Substract_Declareds_in_Bindings(DeclaredsValueids, Bindings -> Declareds2)

	 SAL_Get_TotalDeclareds(-> TotalDone)

         SAL_Substract_Declareds_s(Declareds2, TotalDone -> Declareds3)
	 
	 -- subtract G, F, X, U, R, and W functions, plus Delta constant
	 Id_of_X -> I1
	 Id_of_F -> I2
	 Id_of_G -> I3
	 Id_of_U -> I4
	 Id_of_R -> I5
	 Id_of_W -> I6
	 where(SORTED_DECLS'list(value_item(I6),list(value_item(I5),list(value_item(I4),list(value_item(I3),list(value_item(I2),list(value_item(I1),nil)))))) -> GFX)
	 SAL_Substract_Declareds(Declareds3, GFX -> Declareds4)

         (|
            -- can be translated
           eq(Declareds4, nil)
           where(SORTED_DECL_ITEM'prop_item(Pid) -> Declared)
           where(Waiting -> WaitingOut)
           SAL_Insert_u_Declared(Declared, Done -> DoneOut)
	   SAL_Add_Declared(Declared)  -- to TotalDeclareds
           where(found -> FoundOut)
--Putmsg("Property (")
--Print_id(Ident)
--Putmsg(") can be translated\n")
         ||
            -- can NOT be translated
--Putmsg("Property (")
--Print_id(Ident)
--Putmsg(") can't be translated\n")
--SAL_Print_Declareds(Declareds3)
           where(SORTED_DECL_ITEM'prop_item(Pid) -> Declared)
           SAL_Insert_u_Declared(Declared, Waiting -> WaitingOut)
           where(Done -> DoneOut)
           where(Found -> FoundOut)
         |)
--------------------------------------------------

'action' SAL_Gen_Sign_Decls(SORTED_DECLS, SORTED_DECLS, SORTED_DECLS
                        -> SORTED_DECLS, SORTED_DECLS)

  'rule' SAL_Gen_Sign_Decls(list(Decl, DeclsTail),
                             SignDecls1, SignDecls2
                             -> SignDeclsOut1, SignDeclsOut2):
         where(Decl -> SORTED_DECL_ITEM'value_item(Valueid))
	 Copy_value_id(Valueid -> Valueid2)
	 Valueid'Def -> Def
        (|
           where(Def -> expl_fun(Parms, _, _, Pre, _, _))
           Valueid2'Def <- expl_fun(Parms, no_val, nil, Pre, nil, nil)
           where(SORTED_DECL_ITEM'value_item(Valueid2) -> Decl1)
           SAL_Insert_Declared(Decl1, SignDecls1 -> SignDecls11)
        ||
           where(Def -> impl_fun(Parms, _, Pre, _))
	   -- slight kludge to use explicit as no "nil" for POST_CONDITION
           Valueid2'Def <- expl_fun(Parms, no_val, nil, Pre, nil, nil)
           where(SORTED_DECL_ITEM'value_item(Valueid2) -> Decl1)
           SAL_Insert_Declared(Decl1, SignDecls1 -> SignDecls11)
        |)

         where(SORTED_DECL_ITEM'value_item(Valueid) -> Decl2)
         SAL_Insert_Declared(Decl2, SignDecls2 -> SignDecls22)
         SAL_Gen_Sign_Decls(DeclsTail, SignDecls11, SignDecls22
                        -> SignDeclsOut1, SignDeclsOut2)

  'rule' SAL_Gen_Sign_Decls(nil, SignDecls1, SignDecls2
                        -> SignDecls1, SignDecls2):

--------------------------------------------------
--  Process Different Types Ids
--  to prepare for sorting
--  Subtype, Record and Variant
--------------------------------------------------

--------------------------------------------------
'action' SAL_Process_Subtype(TYPING, VALUE_EXPR, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Process_Subtype(Typing, ValueExpr, DeclaredsIn -> DeclaredsOut):
         SAL_Collect_Value_ids(ValueExpr, nil -> DeclaredsVal)
	 -- sweep for operators now part of SAL_Collect_Value_ids
         -- Collect_Redef_Opers(ValueExpr, DeclaredsVal -> DeclaredsOpers)
         Collect_Pos(Typing, nil -> Bindings1)
         Collect_Pos(ValueExpr, Bindings1 -> Bindings2)
         SAL_Substract_Declareds_in_Bindings(DeclaredsVal, Bindings2 -> Declareds2)
         SAL_Conc_Declareds(DeclaredsIn, Declareds2 -> DeclaredsOut)


--------------------------------------------------
'action' SAL_Process_Record_Type(COMPONENTS, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Process_Record_Type(Components, Declareds1 -> Declareds2):
         where(Declareds1 -> Declareds2)


--------------------------------------------------
'action' SAL_Process_Variant_Type(POS, IDENT, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Process_Variant_Type(Pos, Ident, Declareds -> Declaredsout):
         -- avoid recursion of the variant type
         Insert_Binding(single(Pos, id_op(Ident)), nil -> Bindings)
         SAL_Substract_Declareds_in_Bindings(Declareds, Bindings -> Declaredsout)


--------------------------------------------------
--  Process Different Value Ids
--  to prepare for sorting
--  Explicit and Implicit Values
--  Explicit and Implicit Functions
--------------------------------------------------


--------------------------------------------------
-- Treat Explicit Value
'action' SAL_Process_Expl_Val(VALUE_EXPR, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Process_Expl_Val(ValueExpr, Declareds -> Declaredsout):
         SAL_Collect_Value_ids(ValueExpr, nil -> DeclaredsVal)
	 -- sweep for operators now part of SAL_Collect_Value_ids
         -- Collect_Redef_Opers(ValueExpr, DeclaredsVal -> DeclaredsOpers)
         Collect_Pos(ValueExpr, nil -> Bindings)
         Collect_IdsInPattern(ValueExpr, Bindings -> Bindings2)
         SAL_Substract_Declareds_in_Bindings(DeclaredsVal, Bindings2 -> Declareds2)
         SAL_Conc_Declareds(Declareds, Declareds2 -> Declaredsout)

--------------------------------------------------
-- Treat Implicit Value
'action' SAL_Process_Impl_Val(VALUE_EXPR, POS, ID_OR_OP,
                          SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Process_Impl_Val(ValueExpr, Pos, IdOp, DeclaredsIn -> DeclaredsOut):
         SAL_Collect_Value_ids(ValueExpr, nil -> DeclaredsVal)
	 -- sweep for operators now part of SAL_Collect_Value_ids
         -- Collect_Redef_Opers(ValueExpr, DeclaredsVal -> DeclaredsOpers)
         Collect_Pos(ValueExpr, nil -> Bindings)
         Collect_IdsInPattern(ValueExpr, Bindings -> Bindings2)
--         Insert_u_Binding(single(Pos, IdOp), Bindings -> Bindings1)
         Insert_Binding(single(Pos, IdOp), Bindings2 -> Bindings1)
         SAL_Substract_Declareds_in_Bindings(DeclaredsVal, Bindings1 -> Declareds2)
         SAL_Conc_Declareds(DeclaredsIn, Declareds2 -> DeclaredsOut)


--------------------------------------------------
-- Treat Explicit Function Expression
'action' SAL_Process_Expl_Fun_ValExpr(Value_id, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Process_Expl_Fun_ValExpr(Valueid, DeclaredsIn
                                  -> DeclaredsOut):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> IdOp
	 Valueid'Def -> Def
	 where(Def -> expl_fun(Params, ValueExpr, Post, Pre, OptCond, _))
	 -- sweep for valueids
         SAL_Collect_Value_ids(ValueExpr, nil -> DeclaredsValVE)
         -- To allow detecting simple recursive functions,
         -- toghether with mutual recursive functions,
         -- do NOT substract their Valueid ==> comment line:
         -- SAL_Substract_Valueid(...) and uncomment: where(,...).
         -- To detect simple recursive functions after
         -- leave SAL_Substract_Valueid(...) uncommented.
	 SAL_Substract_Valueid(DeclaredsValVE, Valueid -> DeclaredsOpersVE)
         -- where(DeclaredsValVE -> DeclaredsOpersVE)

	 -- sweep for operators now part of SAL_Collect_Value_ids
	 -- Collect_Redef_Opers(ValueExpr, DeclaredsVid -> DeclaredsOpersVE)
         Collect_Pos(Params, nil -> BindingsPar)
         Collect_Pos(ValueExpr, BindingsPar -> BindingsVE)
         Collect_IdsInPattern(ValueExpr, BindingsVE -> BindingsVE2)
         SAL_Substract_Declareds_in_Bindings(DeclaredsOpersVE,
                                    BindingsVE2 -> DeclaredsValVE1)
         SAL_Conc_Declareds(DeclaredsIn, DeclaredsValVE1 -> DeclaredsOut)


--------------------------------------------------
-- Treat explicit Function Post Expression
'action' SAL_Process_Expl_Fun_PostExpr(Value_id, SORTED_DECLS
                                    -> SORTED_DECLS)

  'rule' SAL_Process_Expl_Fun_PostExpr(Valueid, DeclaredsIn
                                    -> DeclaredsOut):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> IdOp
	 Valueid'Def -> Def
	 where(Def -> expl_fun(Params, ValueExpr, Post, Pre, OptCond, _))

         SAL_Collect_Value_ids(Post, nil -> DeclaredsValPE)

         -- To allow detecting simple recursive functions,
         -- toghether with mutual recursive functions,
         -- do NOT substract their Valueid ==> comment line:
         -- SAL_Substract_Valueid(...) and uncomment: where(,...).
         -- To detect simple recursive functions, when
         -- outputting them, leave SAL_Substract_Valueid(...)
	 -- uncommented.
	 SAL_Substract_Valueid(DeclaredsValPE, Valueid -> DeclaredsOpers)
	 -- where(DeclaredsValPE -> DeclaredsOpers)

	 -- sweep for operators now part of SAL_Collect_Value_ids
	 -- Collect_Redef_Opers(ValueExpr, DeclaredsVid -> DeclaredsOpers)
         Collect_Pos(Params, nil -> BindingsPE)
         Collect_Pos(Post, BindingsPE -> BindingsPE1)
         Collect_IdsInPattern(Post, BindingsPE1 -> BindingsPE2)
         SAL_Substract_Declareds_in_Bindings(DeclaredsOpers, BindingsPE2 -> DeclaredsValPE1)
         SAL_Conc_Declareds(DeclaredsIn, DeclaredsValPE1 -> DeclaredsOut)


--------------------------------------------------
-- Treat Explicit Function Pre Condition
'action' SAL_Process_Expl_Fun_PreExpr(Value_id, SORTED_DECLS
                                   -> SORTED_DECLS)

  'rule' SAL_Process_Expl_Fun_PreExpr(Valueid, DeclaredsIn
                                   -> DeclaredsOut):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> IdOp
	 Valueid'Def -> Def
	 where(Def -> expl_fun(Params, ValueExpr, Post, Pre, OptCond, _))
         SAL_Collect_Value_ids(Pre, nil -> DeclaredsValPre)
         -- To allow detecting simple recursive functions,
         -- toghether with mutual recursive functions,
         -- do NOT substract their Valueid ==> comment line:
         -- SAL_Substract_Valueid(...) and uncomment: where(,...).
         -- To detect simple recursive functions after
         -- leave SAL_Substract_Valueid(...) uncommented.
	 SAL_Substract_Valueid(DeclaredsValPre, Valueid -> DeclaredsOpers)
         -- where(DeclaredsValPre -> DeclaredsOpers)

	 -- sweep for operators now part of SAL_Collect_Value_ids
	 -- Collect_Redef_Opers(ValueExpr, DeclaredsVid -> DeclaredsOpers)
         Collect_Pos(Params, nil -> BindingsPre)
         Collect_Pos(Pre, BindingsPre -> BindingsPre1)
         Collect_IdsInPattern(ValueExpr, BindingsPre1 -> BindingsPre2)
         SAL_Substract_Declareds_in_Bindings(DeclaredsOpers,
                              BindingsPre2 -> DeclaredsValPre1)
         SAL_Conc_Declareds(DeclaredsIn, DeclaredsValPre1 -> DeclaredsOut)


--------------------------------------------------
-- Treat Implicit Function Post Expression
'action' SAL_Process_Impl_Fun_PostExpr(Value_id, SORTED_DECLS
                                    -> SORTED_DECLS)

  'rule' SAL_Process_Impl_Fun_PostExpr(Valueid, DeclaredsIn
                                    -> DeclaredsOut):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> IdOp
	 Valueid'Def -> Def
	 where(Def -> impl_fun(Params, Post, Pre, OptCond))

         SAL_Collect_Value_ids(Post, nil -> DeclaredsValPE)

         -- To allow detecting simple recursive functions,
         -- toghether with mutual recursive functions,
         -- do NOT substract their Valueid ==> comment line:
         -- SAL_Substract_Valueid(...) and uncomment: where(,...).
         -- To detect simple recursive functions, when
         -- outputting them, leave SAL_Substract_Valueid(...)
	 -- uncommented.
	 SAL_Substract_Valueid(DeclaredsValPE, Valueid -> DeclaredsOpers)
	 -- where(DeclaredsValPE -> DeclaredsOpers)

	 -- sweep for operators now part of SAL_Collect_Value_ids
	 -- Collect_Redef_Opers(ValueExpr, DeclaredsVid -> DeclaredsOpers)
         Collect_Pos(Params, nil -> BindingsPE)
         Collect_Pos(Post, BindingsPE -> BindingsPE1)
         Collect_IdsInPattern(Post, BindingsPE1 -> BindingsPE2)
         SAL_Substract_Declareds_in_Bindings(DeclaredsOpers, BindingsPE2 -> DeclaredsValPE1)
         SAL_Conc_Declareds(DeclaredsIn, DeclaredsValPE1 -> DeclaredsOut)


--------------------------------------------------
-- Treat Implicit Function Pre Condition
'action' SAL_Process_Impl_Fun_PreExpr(Value_id, SORTED_DECLS
                                   -> SORTED_DECLS)

  'rule' SAL_Process_Impl_Fun_PreExpr(Valueid, DeclaredsIn
                                   -> DeclaredsOut):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> IdOp
	 Valueid'Def -> Def
	 where(Def -> impl_fun(Params, Post, Pre, OptCond))

         SAL_Collect_Value_ids(Pre, nil -> DeclaredsValPre)
         -- To allow detecting simple recursive functions,
         -- toghether with mutual recursive functions,
         -- do NOT substract their Valueid ==> comment line:
         -- SAL_Substract_Valueid(...) and uncomment: where(,...).
         -- To detect simple recursive functions, when
         -- outputting them, leave SAL_Substract_Valueid(...)
	 -- uncommented.
	 SAL_Substract_Valueid(DeclaredsValPre, Valueid -> DeclaredsOpers)
         -- where(DeclaredsValPre -> DeclaredsOpers)

	 -- sweep for operators now part of SAL_Collect_Value_ids
	 -- Collect_Redef_Opers(ValueExpr, DeclaredsVid -> DeclaredsOpers)
         Collect_Pos(Params, nil -> BindingsPre)
         Collect_Pos(Pre, BindingsPre -> BindingsPre1)
         Collect_IdsInPattern(Pre, BindingsPre1 -> BindingsPre2)

         SAL_Substract_Declareds_in_Bindings(DeclaredsOpers, BindingsPre2
                                  -> DeclaredsValPre1)
         SAL_Conc_Declareds(DeclaredsIn, DeclaredsValPre1 -> DeclaredsOut)


--------------------------------------------------
--  Reverse lists
--------------------------------------------------

--------------------------------------------------
-- Reverses a list of Declareds
'action' SAL_Rev_Declareds(SORTED_DECLS, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Rev_Declareds(ListIn, ListAux -> ListOut):
         (|
           where(ListIn -> list(Elem, ListTail))
           SAL_Rev_Declareds(ListTail, list(Elem, ListAux) -> ListOut)
         ||
           where(ListIn -> nil)
           where(ListAux -> ListOut)
         |)



--------------------------------------------------
-- SAL_Conc_Declareds(Ds, Ds1 -> Ds ^ Ds1)
'action' SAL_Conc_Declareds(SORTED_DECLS, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Conc_Declareds(list(Declared, Declareds), Declareds1 -> list(Declared, Declareds2)):
         SAL_Conc_Declareds(Declareds, Declareds1 -> Declareds2)

  'rule' SAL_Conc_Declareds(nil, Declareds -> Declareds):


-- SAL_Insert_Declared(Elem, Elems -> Elems ^ <Elem>)
'action' SAL_Insert_Declared(SORTED_DECL_ITEM, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Insert_Declared(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 SAL_Insert_Declared(Elem, ElemsTail -> Elems1)

  'rule' SAL_Insert_Declared(Elem, nil -> list(Elem, nil)):

-- SAL_Insert_u_Declared(Decled, Decleds -> if Decled is not in then Decls ^ <Decled>)
'action' SAL_Insert_u_Declared(SORTED_DECL_ITEM, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Insert_u_Declared(Decled, list(Decled1, DecledsTail) -> list(Decled1, Decleds1)):
         (|
           eq(Decled, Decled1)
           where(DecledsTail -> Decleds1)
         ||
           SAL_Insert_u_Declared(Decled, DecledsTail -> Decleds1)
         |) 

  'rule' SAL_Insert_u_Declared(Decled, nil -> list(Decled, nil)):

'condition' SAL_Are_Functions(SORTED_DECLS, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Are_Functions(Declsin, Decls -> FunDeclsout):
         SAL_Get_Decls_Funct(Declsin, Decls -> FunDeclsout)
	 ne(FunDeclsout, nil)

--  'rule' SAL_Are_Functions(nil, Decls -> Decls):


'action' SAL_Substract_Valueid(SORTED_DECLS, Value_id -> SORTED_DECLS)

  'rule' SAL_Substract_Valueid(list(value_item(Valueid1), DeclrdsTail),
                                        Valueid
                                         -> Declaredsout):
         SAL_Substract_Valueid(DeclrdsTail, Valueid -> Declareds1)
         (|
           ne(Valueid, Valueid1)
           where(SORTED_DECLS'list(value_item(Valueid1), Declareds1)
	         -> Declaredsout)
         ||
           where(Declareds1 -> Declaredsout)
         |)
 
  'rule' SAL_Substract_Valueid(list(type_item(Typeid), Tail), Valueid
                                         -> Declaredsout):
         SAL_Substract_Valueid(Tail, Valueid -> Declaredsout)
 
  'rule' SAL_Substract_Valueid(list(axiom_item(A), Tail), Valueid
                                         -> Declaredsout):
         SAL_Substract_Valueid(Tail, Valueid -> Declaredsout)
         
  'rule' SAL_Substract_Valueid(nil, Valueid -> nil):

-- Subtract(D, B -> {x in D | x'id not in B})
'action' SAL_Substract_Declareds_in_Bindings(SORTED_DECLS, BINDINGS -> SORTED_DECLS)

  'rule' SAL_Substract_Declareds_in_Bindings(list(value_item(Valueid), DeclrdsTail),
                                         Bindings
                                         -> Declaredsout):
         SAL_Substract_Declareds_in_Bindings(DeclrdsTail, Bindings -> Declareds1)
         (|
           Valueid'Pos -> PosValueid
           Not_in_Bindings(PosValueid, Bindings)
           where(SORTED_DECLS'list(value_item(Valueid), Declareds1) -> Declaredsout)
         ||
           where(Declareds1 -> Declaredsout)
         |)
 
  'rule' SAL_Substract_Declareds_in_Bindings(list(SORTED_DECL_ITEM'type_item(Typeid), Tail), Bindings
                                         -> Declaredsout):
         SAL_Substract_Declareds_in_Bindings(Tail, Bindings -> Declareds1)
         (|
           Typeid'Pos -> PosTypeid
           Not_in_Bindings(PosTypeid, Bindings)
           where(SORTED_DECLS'list(SORTED_DECL_ITEM'type_item(Typeid), Declareds1) -> Declaredsout)
         ||
           where(Declareds1 -> Declaredsout)
         |)
 
  'rule' SAL_Substract_Declareds_in_Bindings(list(axiom_item(A), Tail), Bindings
                                         -> Declaredsout):
         SAL_Substract_Declareds_in_Bindings(Tail, Bindings -> Declaredsout)

  'rule' SAL_Substract_Declareds_in_Bindings(list(ts_item(TSid), Tail), Bindings
                                         -> Declaredsout):
         SAL_Substract_Declareds_in_Bindings(Tail, Bindings -> Declaredsout1)
	 where(SORTED_DECLS'list(ts_item(TSid), Declaredsout1) -> Declaredsout)
         
  'rule' SAL_Substract_Declareds_in_Bindings(nil, Bindings -> nil):


--------------------------------------------------
-- Subtract(A, B -> A\B)
'action' SAL_Substract_Declareds_s(SORTED_DECLS, SORTED_DECLS_S -> SORTED_DECLS)

  'rule' SAL_Substract_Declareds_s(DecledsIn,
                               list(Decleds, Decleds_sTail)
                               -> DecledsOut):

         SAL_Substract_Declareds_by_Pos(DecledsIn, Decleds
                                    -> DecledsOut1)
         (|
           eq(DecledsOut1, nil)
           where(DecledsOut1 -> DecledsOut)
         ||
           SAL_Substract_Declareds_s(DecledsOut1, Decleds_sTail
                                 -> DecledsOut)
         |)

  'rule' SAL_Substract_Declareds_s(nil, _ -> nil):

  'rule' SAL_Substract_Declareds_s(DecledsIn, nil
                               -> DecledsIn):


--------------------------------------------------
-- Subtract(A, B -> A\B)
'action' SAL_Substract_Declareds(SORTED_DECLS, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Substract_Declareds(list(A_Decled, A_Tail), B -> C):

         SAL_Substract_Declareds(A_Tail, B -> C1)
         (|
           SAL_Not_in_Declareds(A_Decled, B)
           where(SORTED_DECLS'list(A_Decled, C1) -> C)
         ||
           where(C1 -> C)
         |)

  'rule' SAL_Substract_Declareds(nil, _ -> nil):


--------------------------------------------------
-- Subtract(A, B -> A\B)
'action' SAL_Substract_Declareds_by_Pos(SORTED_DECLS, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Substract_Declareds_by_Pos(list(A_Decled, A_Tail), B -> C):

         SAL_Substract_Declareds_by_Pos(A_Tail, B -> C1)
         (|
           SAL_Is_in_Declareds_by_Pos(A_Decled, B)
           where(C1 -> C)
         ||
           where(SORTED_DECLS'list(A_Decled, C1) -> C)
         |)

  'rule' SAL_Substract_Declareds_by_Pos(nil, _ -> nil):


'action' SAL_Add_Declareds(SORTED_DECLS)

  'rule' SAL_Add_Declareds(Declrds):
	 (|
	   SAL_TotalDeclareds -> list(Declrds1, Declrds_s)
	   SAL_Conc_Declareds(Declrds1, Declrds -> Declrds2)
	   SAL_TotalDeclareds <- list(Declrds2, Declrds_s)
         ||
	   SAL_TotalDeclareds -> nil
	   SAL_TotalDeclareds <- list(Declrds, nil)
         |)


--------------------------------------------------
'action' SAL_Add_Declared(SORTED_DECL_ITEM)

  'rule' SAL_Add_Declared(Declrd):
	 (|
	   SAL_TotalDeclareds -> list(Declrds, Declrds_s)
	   SAL_TotalDeclareds <- list(list(Declrd, Declrds), Declrds_s)
         ||
	   SAL_TotalDeclareds -> nil
	   SAL_TotalDeclareds <- list(list(Declrd, nil), nil)
         |)


'action' SAL_Init_TotalDeclareds

  'rule' SAL_Init_TotalDeclareds
	 SAL_TotalDeclareds <- nil


'action' SAL_Open_TotalDeclareds

  'rule' SAL_Open_TotalDeclareds
	 SAL_TotalDeclareds -> X
	 SAL_TotalDeclareds <- list(nil, X)

--------------------------------------------------
'action' SAL_Close_TotalDeclareds

  'rule' SAL_Close_TotalDeclareds
	 SAL_TotalDeclareds -> list(_, X)
	 SAL_TotalDeclareds <- X

--------------------------------------------------
'action' SAL_Get_TotalDeclareds(-> SORTED_DECLS_S)

  'rule' SAL_Get_TotalDeclareds(-> TotalDeclds):
	 SAL_TotalDeclareds -> TotalDeclds

--------------------------------------------------
'condition' SAL_Find_Declared(SORTED_DECL_ITEM)

  'rule' SAL_Find_Declared(Declrd):
	 SAL_TotalDeclareds -> Declrds_s
	 SAL_Find_Declared_s(Declrd, Declrds_s)


--------------------------------------------------
'condition' SAL_Find_Declared_s(SORTED_DECL_ITEM, SORTED_DECLS_S)

  'rule' SAL_Find_Declared_s(Declrd, list(Declrds, Declrds_s)):
	 (|
	   SAL_Find_Declared_s(Declrd, list(Declrds, nil))
	 ||
	   SAL_Find_Declared_s(Declrd, Declrds_s)
	 |)

-------------------------------------------------------
'action'  SAL_Collect_Type_Ids_from_TS(RESOLVED_SYSTEM_DESCRIPTION, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Collect_Type_Ids_from_TS(desc(Input,Local,_,_,Cmds,_), Decls -> NewDecls)
	 SAL_Collect_Type_ids(Input, Decls -> Decls1)
	 SAL_Collect_Type_ids(Local, Decls1 -> Decls2)
	 SAL_Collect_Type_ids(Cmds, Decls2 -> NewDecls)

  'rule' SAL_Collect_Type_Ids_from_TS(no_input(Local,_,Cmds,_), Decls -> NewDecls)
	 SAL_Collect_Type_ids(Local, Decls -> NewDecls)

  'rule' SAL_Collect_Type_Ids_from_TS(nil, Decls -> Decls)

'action'  SAL_Collect_Value_Ids_from_TS(RESOLVED_SYSTEM_DESCRIPTION, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Collect_Value_Ids_from_TS(desc(Input,Local,_,_,Cmds,_), Decls -> NewDecls)
	 SAL_Collect_Value_ids(Input, Decls -> Decls1)
	 SAL_Collect_Value_ids(Local, Decls1 -> Decls2)
	 SAL_Collect_Value_ids(Cmds, Decls2 -> NewDecls)

  'rule' SAL_Collect_Value_Ids_from_TS(no_input(Local,_,Cmds,_), Decls -> NewDecls)
	 SAL_Collect_Value_ids(Local, Decls -> NewDecls)


  'rule' SAL_Collect_Value_Ids_from_TS(nil, Decls -> Decls)

'action' SAL_Collect_Pos_from_TS(RESOLVED_SYSTEM_DESCRIPTION, BINDINGS -> BINDINGS)

  'rule' SAL_Collect_Pos_from_TS(desc(Input,Local,_,_,Cmds,_), BS -> NewBS)
	 Collect_Pos(Input, BS -> BS1)
	 Collect_Pos(Local, BS1 -> BS2)
	 Collect_Pos(Cmds, BS2 -> NewBS)

  'rule' SAL_Collect_Pos_from_TS(no_input(Local,_,Cmds,_), BS -> NewBS)
	 Collect_Pos(Local, BS -> NewBS)

  'rule' SAL_Collect_Pos_from_TS(nil, BS -> BS)

--------------------------------------------------
--  Sweeps
--------------------------------------------------

--------------------------------------------------
'sweep' SAL_Collect_Type_ids(ANY, SORTED_DECLS -> SORTED_DECLS)

-- ignore disambiguations (can be inserted during resolving)
  'rule' SAL_Collect_Type_ids(VALUE_EXPR'disamb(_, V, _), Declareds -> Declareds1):
	 SAL_Collect_Type_ids(V, Declareds -> Declareds1)
  
  'rule' SAL_Collect_Type_ids(TYPE_EXPR'defined(Typeid, nil), Declareds -> Declareds1):
	 (| -- may be affected by WITH
	   Check_type_defined(defined(Typeid, nil) -> defined(Typeid1, nil))
           SAL_Insert_Declared(SORTED_DECL_ITEM'type_item(Typeid1), Declareds -> Declareds1)
	 ||
	   where(Declareds -> Declareds1)
	 |)

  'rule' SAL_Collect_Type_ids(TYPE_EXPR'named_type(Name), Declareds -> Declareds1):
	 Resolve_type(named_type(Name) -> TRes)
	 SAL_Collect_Type_ids(TRes, Declareds -> Declareds1)

--------------------------------------------------
'sweep' SAL_Collect_Value_ids(ANY, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Collect_Value_ids(VALUE_EXPR'val_occ(_, Valueid, nil), Declareds -> Declareds1):
         SAL_Insert_Declared(value_item(Valueid), Declareds -> Declareds1)

  'rule' SAL_Collect_Value_ids(VALUE_EXPR'infix_occ(_, L, I, Q, R), Declareds -> Declareds3):
	 SAL_Collect_Value_ids(L, Declareds -> Declareds1)
	 (|
	   I'Ident -> op_op(Op)
	   (| Built_in(Op, I) || ne(Q, nil) |)
	   where(Declareds1 -> Declareds2)
	 ||
	   SAL_Insert_Declared(value_item(I), Declareds1 -> Declareds2)
	 |)
	 SAL_Collect_Value_ids(R, Declareds2 -> Declareds3)

  'rule' SAL_Collect_Value_ids(VALUE_EXPR'prefix_occ(_, I, Q, V), Declareds -> Declareds2):
	 (|
	   I'Ident -> op_op(Op)
	   (| Built_in(Op, I) || ne(Q, nil) |)
	   where(Declareds -> Declareds1)
	 ||
	   SAL_Insert_Declared(value_item(I), Declareds -> Declareds1)
	 |)
	 SAL_Collect_Value_ids(V, Declareds1 -> Declareds2)
  
--------------------------------------------------
'sweep' SAL_Collect_Value_id_Variant(ANY, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Collect_Value_id_Variant(VARIANT'record(Pos, con_ref(Valueid),
                                                 Components),
                                  DeclaredsIn -> DeclaredsOut):
         SAL_Insert_Declared(value_item(Valueid), DeclaredsIn -> Declareds1)
	 SAL_Collect_Value_id_Variant(Components, Declareds1 -> DeclaredsOut)

  'rule' SAL_Collect_Value_id_Variant(COMPONENT'component(Pos,
                                                      dest_ref(Valueid),
                                                      TypeExpr,
                                                      Reconstructor),
                                  DeclaredsIn -> DeclaredsOut):
         SAL_Insert_Declared(value_item(Valueid), DeclaredsIn -> Declareds1)
	 (|
	   where(Reconstructor -> recon_ref(Rid))
	   SAL_Insert_Declared(value_item(Rid), Declareds1 -> DeclaredsOut)
	 ||
	   where(Declareds1 -> DeclaredsOut)
	 |)  


-- auxiliary for action Are_Functions
--------------------------------------------------
'action' SAL_Get_Decls_Funct(SORTED_DECLS, SORTED_DECLS -> SORTED_DECLS)

  'rule' SAL_Get_Decls_Funct(list(Decl, DeclsTail),
                       Decls -> FunDeclsout):
         where(Decl -> value_item(Valueid))
         Valueid'Def -> ValueDef
         (|
           where(ValueDef -> expl_fun(_, _, _, _, _, _))
           SAL_Insert_Declared(Decl, Decls -> Decls1)
           SAL_Get_Decls_Funct(DeclsTail, Decls1 -> FunDeclsout)
         ||
           where(ValueDef -> impl_fun(_, _, _, _))
           SAL_Insert_Declared(Decl, Decls -> Decls1)
           SAL_Get_Decls_Funct(DeclsTail, Decls1 -> FunDeclsout)
         ||
           SAL_Get_Decls_Funct(DeclsTail, Decls -> FunDeclsout)
         |)

  'rule' SAL_Get_Decls_Funct(list(Decl, DeclsTail),
                       Decls -> NoFunDeclsout):
         SAL_Get_Decls_Funct(DeclsTail, Decls -> NoFunDeclsout)

  'rule' SAL_Get_Decls_Funct(nil, FunDecls -> FunDecls):

----------------------------------
'condition' SAL_Not_in_Declareds(SORTED_DECL_ITEM, SORTED_DECLS)

  'rule' SAL_Not_in_Declareds(Decled, list(Decled2, DecledsTail)):
         ne(Decled, Decled2)
         SAL_Not_in_Declareds(Decled, DecledsTail)

  'rule' SAL_Not_in_Declareds(Decled, nil):

---------------------------------

'condition' SAL_Is_in_Declareds_by_Pos(SORTED_DECL_ITEM, SORTED_DECLS)

  'rule' SAL_Is_in_Declareds_by_Pos(Declrd1, list(Declrd2, DeclrdsTail)):
         (|
	   SAL_Eq_Declared_by_Pos(Declrd1, Declrd2)
         ||
	   SAL_Is_in_Declareds_by_Pos(Declrd1, DeclrdsTail)
         |)

--------------------------------------------------

'condition' SAL_Eq_Declared_by_Pos(SORTED_DECL_ITEM, SORTED_DECL_ITEM)

  'rule' SAL_Eq_Declared_by_Pos(type_item(Typeid), type_item(Typeid2)):
	 Typeid'Pos -> Pos
	 Typeid2'Pos -> Pos2
	 eq(Pos, Pos2)

  'rule' SAL_Eq_Declared_by_Pos(value_item(Valueid), value_item(Valueid2)):
	 Valueid'Pos -> Pos
	 Valueid2'Pos -> Pos2
	 eq(Pos, Pos2)

  'rule' SAL_Eq_Declared_by_Pos(axiom_item(Axiomid), axiom_item(Axiomid2)):
	 Axiomid'Pos -> Pos
	 Axiomid2'Pos -> Pos2
	 eq(Pos, Pos2)

  'rule' SAL_Eq_Declared_by_Pos(lemma_item(Axiomid), lemma_item(Axiomid2)):
	 Axiomid'Pos -> Pos
	 Axiomid2'Pos -> Pos2
	 eq(Pos, Pos2)

  'rule' SAL_Eq_Declared_by_Pos(rec_fun_item(Valueid), rec_fun_item(Valueid2)):
	 Valueid'Pos -> Pos
	 Valueid2'Pos -> Pos2
	 eq(Pos, Pos2)

  'rule' SAL_Eq_Declared_by_Pos(mut_rec_fun_item(Valueid), mut_rec_fun_item(Valueid2)):
	 Valueid'Pos -> Pos
	 Valueid2'Pos -> Pos2
	 eq(Pos, Pos2)

  'rule' SAL_Eq_Declared_by_Pos(rec_item(Declareds), rec_item(Declareds2)):
         SAL_Eq_Declareds_by_Pos(Declareds, Declareds2)

  'rule' SAL_Eq_Declared_by_Pos(mark_item(String), mark_item(String2)):
	 eq(String, String2)

  'rule' SAL_Eq_Declared_by_Pos(ts_item(Pid1), ts_item(Pid2))
	 Pid1'Pos -> Pos1
	 Pid2'Pos -> Pos2
	 eq(Pos1,Pos2)


  'rule' SAL_Eq_Declared_by_Pos(nil, nil):

--------------------------------------------------

'condition' SAL_Eq_Declareds_by_Pos(SORTED_DECLS, SORTED_DECLS)

  'rule' SAL_Eq_Declareds_by_Pos(list(Declrd, DeclrdsTail), list(Declrd2, DeclrdsTail2)):
	 SAL_Eq_Declared_by_Pos(Declrd, Declrd2)
	 SAL_Eq_Declareds_by_Pos(DeclrdsTail, DeclrdsTail2)

  'rule' SAL_Eq_Declareds_by_Pos(nil, nil):


