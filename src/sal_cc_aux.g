-- RSL Type Checker
-- Copyright (C) 1998 - 2005 UNU/IIST

-- raise@iist.unu.edu

-- This module contains the auxiliary functions for the cc version

'module' sal_cc_aux

'use' ast print ext env objects values 
      types	   
      pp 
      cc	   
      cpp	   
      sml	   
      sal_ast	   -- AST for SAL language
      sal_global_vars
      sal_print
      sal_aux

      sal_gen_ast	-- SAL_Generate_Context
'export'
      
      SAL_Gen_CC_id
      
      -- Type lifting
      SAL_join_CCs

      SAL_Gen_Lifted_Decls
      Select_CC_Result_Type
      Extend_Nav_Type
      SAL_Generate_Result_for_Violation

      find_nils
      SAL_Modify_Contexts_for_type_WFC

      SAL_Add_is_Type_functions

      SAL_Generate_CC_BuiltIn_Context

      Collect_Reconstructor_Decls
      Collect_Is_Type_Function
      Collect_Lifted_Constructor
      Collect_Lifted_Destructor

      SAL_Remove_Decls_From_Contexts

      SAL_Replace_Vars_in_Expr
      SAL_Replace_Vars_in_Exprs
      SAL_Replace_Ident      

      SAL_Gen_Nav_Transitions

      Get_Invalid_Insertion_Nav
      Get_Swap_Nav

      -- Utilities for the simple cc version
      SAL_Update_Names
      SAL_Generate_Simple_CC_BuiltIn_Context

-- This rule extends the Ident of a declaration into its
-- corresponding cc equivalent

'action' SAL_Gen_CC_id(IDENT -> IDENT)

  'rule' SAL_Gen_CC_id(Id -> CC_Id)
	 id_to_string(Id -> StrId)
	 Concatenate(StrId, "_cc" -> CC_Str)
	 string_to_id(CC_Str -> CC_Id)


------------------------
'action' SAL_join_CCs(POS, VALUE_EXPR, VALUE_EXPR -> VALUE_EXPR)

  'rule' SAL_join_CCs(_, no_val, Cc2 ->  Cc2)
	 
  'rule' SAL_join_CCs(_, Cc1, no_val -> Cc1)

  'rule' SAL_join_CCs(Pos, Cc1, Cc2 -> CcOut)
	 where(ax_infix(Pos, Cc1, and, Cc2, Pos) -> CcOut)

------------------------------------------------------------------------
-- SAL_Gen_Lifted_Decls
------------------------------------------------------------------------
-- This functions takes the global colection of types and will extract
-- the tids of their lifted versions. With that, proper type declarations
-- will be created in order to include the declarations in the SAL_TYPES
-- context...
-- The 'Restriction ' field in the Tids for the lifted types is also 
-- filled with the proper value...
-------------------------------------------------------------------------

'action' SAL_Gen_Lifted_Decls(-> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Gen_Lifted_Decls(-> LiftedDeclarations)
	 Global_Tid_Table -> TidList1
	 Global_CC_Tid_Table -> CollectionTids
	 SAL_Concatenate_Type_Ids(TidList1, CollectionTids -> TidList)
	 -- Adding to the list to be processed:
	 SAL_Gen_Lifted_Decls_(TidList -> LiftedDeclarations)


'action' SAL_Gen_Lifted_Decls_(SAL_TYPE_IDS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Gen_Lifted_Decls_(list(Tid, Rest) -> list(Decl, RestDecl))
	 SAL_Gen_Lifted_Decl(Tid -> Decl)
	 ne(Decl, nil)
	 SAL_Gen_Lifted_Decls_(Rest -> RestDecl)

	 -- As it is implemented, if a Tid of a lifted type is found,
	 -- the result of SAL_Gen_Lifted_Decl will be nil and it is not
	 -- convinient to store nils in the list of declarations...
  'rule' SAL_Gen_Lifted_Decls_(list(Tid, Rest) -> RestDecl)
	 Default_Int_Tid -> ITid
	 ITid'Lifted_Tid -> tid(LITid)
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 Default_Nat_Tid -> NTid
	 (| 
            eq(Tid, ITid) || eq(Tid, LITid) || eq(Tid, BTid) || eq(Tid, LBTid) || eq(Tid, NTid) 
         ||
	    Tid'Lifted_Tid -> tid(LTid)
	    (| eq(LTid, ITid) || eq(LTid, LITid) || eq(LTid, BTid) || eq(LTid, LBTid) || eq(LTid, NTid) |)
	 |) 
	 SAL_Gen_Lifted_Decls_(Rest -> RestDecl)


  'rule' SAL_Gen_Lifted_Decls_(list(_, Rest) -> RestDecl)
	 SAL_Gen_Lifted_Decls_(Rest -> RestDecl)

  'rule' SAL_Gen_Lifted_Decls_(nil -> nil)

'action' SAL_Gen_Lifted_Decl(SAL_type_id -> SAL_CONTEXT_CONSTANT)

  'rule' SAL_Gen_Lifted_Decl(Tid -> LiftedDecl)
	 Tid'Lifted_Tid -> tid(LiftedTid)
	 LiftedTid'Ident -> Id
	 LiftedTid'Lifted_fields -> DataParts
	 where(user_defined(sal_variant_type(DataParts)) -> TypeExpr)
	 where(sal_type_decl(Id, LiftedTid, TypeExpr) -> LiftedDecl)
	 LiftedTid'Declaration <- LiftedDecl

  'rule' SAL_Gen_Lifted_Decl(Tid -> nil)
	 Putmsg("Debugging activated in SAL_Gen_Lifted_Decl when processing: ")
	 SAL_Print_Tid(Tid)
	 
-----------------------------
'condition' find_nils(SAL_CONTEXT_CONSTANTS)

  'rule' find_nils(list(nil, Rest))

  'rule' find_nils(list(_, Rest))
	 find_nils(Rest)

------------------------------------------
'action' Select_CC_Result_Type(SAL_TYPE_EXPR -> SAL_type_id)

  'rule' Select_CC_Result_Type(rsl_built_in(boolean(Tid)) -> Tid)

  'rule' Select_CC_Result_Type(rsl_built_in(integer(Tid)) -> Tid)

  'rule' Select_CC_Result_Type(rsl_built_in(natural(Tid)) -> Tid)

  'rule' Select_CC_Result_Type(rsl_built_in(sal_finite_set(Tid,_)) -> Tid)

  'rule' Select_CC_Result_Type(rsl_built_in(sal_list_type(Tid,_)) -> Tid)

  'rule' Select_CC_Result_Type(rsl_built_in(sal_finite_map(Tid,_,_)) -> Tid)

  'rule' Select_CC_Result_Type(user_defined(sal_bracket_type(T)) -> Tid):
         Select_CC_Result_Type(T -> Tid)

  'rule' Select_CC_Result_Type(user_defined(sal_tuple_type(
		list(sal_tuple(TExpr),_))) -> Tid)
	 Select_CC_Result_Type(TExpr -> Tid)

  'rule' Select_CC_Result_Type(type_refs(sal_defined(_,_,Tid)) -> Tid)

  'rule' Select_CC_Result_Type(user_defined(sal_cc_type(LTE, _)) -> Tid)
	 Select_CC_Result_Type(LTE -> Tid)

  'rule' Select_CC_Result_Type(rsl_built_in(sal_array(Tid,_,_)) -> Tid)

/*  'rule' Select_CC_Result_Type(rsl_built_in(sal_array(_,T)) -> Tid) 
         Select_CC_Result_Type(T -> Tid)
         print(Tid)*/
         --TODO: Maybe change this

  'rule' Select_CC_Result_Type(T -> Tid)
         Default_Int_Tid -> Tid
         print(T)
----------------------------------------
'action' Extend_Nav_Type(POS, STRING -> SAL_value_id)

  'rule' Extend_Nav_Type(Pos, Str -> ConstructorVid)
	 SAL_Nav_Tid -> Tid
	 string_to_id(Str -> ConstrId)
	 Tid'Cid -> cid(Cid)
	 Tid'Pos -> P
	 Tid'Ident -> Id
	 Tid'Lifted_fields -> DataParts
	 Find_Constructor_in_Parts(ConstrId, DataParts -> OptVid)
	 (|
	   where(OptVid -> vid(ConstructorVid))
	 ||
	   New_SAL_value_id(Pos, id(ConstrId), Cid, type_refs(sal_defined(P, Id, Tid)), constructor_value -> ConstructorVid)
	   where(sal_construc(id(ConstrId), ConstructorVid, nil,nil) -> Constructor)
	   where(SAL_DATA_TYPE_PARTS'list(sal_part(Constructor,type_refs(sal_defined(P, Id, Tid))), DataParts) -> NewPart)
	   Tid'Lifted_fields <- NewPart
	 |)

'action' Find_Constructor_in_Parts(IDENT, SAL_DATA_TYPE_PARTS -> OPT_SAL_VALUE_ID)

  'rule' Find_Constructor_in_Parts(Id, list(sal_part(Constr, _), Parts) -> Res):
  	 (|
	   where(Constr -> sal_construc(id(Id1), Vid, _, _))
	   eq(Id, Id1)
	   where(vid(Vid) -> Res)
	 ||
	   Find_Constructor_in_Parts(Id, Parts -> Res)
	 |)

  'rule' Find_Constructor_in_Parts(_, nil -> nil):
------------------------------------------------------------------
-- SAL_Gen_Non_Nav_Condition
------------------------------------------------------------------
-- This function generates a nav-value check for a given type expression.
-- It is meant to take care recursively if a product was found.
------------------------------------------------------------------
'action' SAL_Gen_Non_Nav_Condition(IDENT, SAL_TYPE_EXPR -> SAL_VALUE_EXPR)

  'rule' SAL_Gen_Non_Nav_Condition(Ident, user_defined(sal_cc_type(LTE, TE)) -> NonNavCond)
	 SAL_Gen_Non_Nav_Condition(Ident, LTE -> NonNavCond)

  'rule' SAL_Gen_Non_Nav_Condition(Ident, rsl_built_in(integer(Tid)) -> NonNavCondition)
	 Tid'Constructor -> vid(ConsVid)
	 where(sal_recogniser(ConsVid,
		sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Ident)),nil),nil))) -> NonNavCondition)
  
  'rule' SAL_Gen_Non_Nav_Condition(Ident, rsl_built_in(natural(Tid)) -> NonNavCondition)
	 Tid'Constructor -> vid(ConsVid)
	 where(sal_recogniser(ConsVid, 
		sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Ident)),nil),nil))) -> NonNavCondition)
  
  'rule' SAL_Gen_Non_Nav_Condition(Ident, rsl_built_in(boolean(Tid)) -> NonNavCondition)
	 Tid'Constructor -> vid(ConsVid)
	 where(sal_recogniser(ConsVid, 
		sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Ident)),nil),nil))) -> NonNavCondition)
  
  'rule' SAL_Gen_Non_Nav_Condition(Ident, rsl_built_in(sal_finite_set(Tid,_)) -> NonNavCondition)
	 Tid'Constructor -> vid(ConsVid)
	 where(sal_recogniser(ConsVid, 
		sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Ident)),nil),nil))) -> NonNavCondition)
  
  'rule' SAL_Gen_Non_Nav_Condition(Ident, rsl_built_in(sal_finite_map(Tid,_,_)) -> NonNavCondition)
	 Tid'Constructor -> vid(ConsVid)
	 where(sal_recogniser(ConsVid, 
		sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Ident)),nil),nil))) -> NonNavCondition)
  
  'rule' SAL_Gen_Non_Nav_Condition(Ident, type_refs(sal_defined(_,_,Tid)) -> NonNavCondition)
	 Tid'Constructor -> vid(ConsVid)
	 where(sal_recogniser(ConsVid, 
		sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Ident)),nil),nil))) -> NonNavCondition)
  
   -- Nothing else should be possible as a lifted type...
   -- The lifting of the type system should turn other type expressions (such as products, variants or records into
   -- a reference to a properly defined lifted variant (with an associated TID)
  

----------------------------------------
'action' SAL_Generate_Result_for_Violation(SAL_TYPE_EXPR, SAL_VALUE_EXPR -> SAL_VALUE_EXPR)

  'rule' SAL_Generate_Result_for_Violation(user_defined(sal_tuple_type(Product)), V -> VE)
	 Generate_Result_for_Product(V, Product -> VExprs)
	 where(sal_product(VExprs) -> VE)

	 -- the result is a single result... No need to generate a tuple...
	 -- just generate a value_occ with the vid...
  'rule' SAL_Generate_Result_for_Violation(Type, V -> Expr)
	 Select_CC_Result_Type(Type -> Tid)
	 Get_Lifted_Default_value(Tid -> NavConst)
	 DefaultPos(-> P)
	 where(sal_funct_applic(sal_esp_value_occ(NavConst), sal_argument(SAL_VALUE_EXPRS'list(V, nil))) -> Expr)

----------------------------------------
'action' Generate_Result_for_Product(SAL_VALUE_EXPR, SAL_TUPLE_ELEMS -> SAL_VALUE_EXPRS)

  'rule' Generate_Result_for_Product(V, list(sal_tuple(TE), Rest) -> list(VE, VRest))
	 SAL_Generate_Result_for_Violation(TE, V -> VE)
	 Generate_Result_for_Product(V, Rest -> VRest)

  'rule' Generate_Result_for_Product(_, nil -> nil)

-----------------------------------------

'action' Get_Lifted_Default_value(SAL_type_id -> SAL_value_id)

  'rule' Get_Lifted_Default_value(Tid -> Vid)
	 Tid'DefaultNav -> vid(Vid)

  'rule' Get_Lifted_Default_value(Tid -> Vid)
	 Putmsg("Debugging predicate activated in Get_Lifted_Default_value: ")
	 SAL_Print_Tid(Tid)
	 DefaultPos(-> P)
	 string_to_id("fake" -> Id)
	 where(SAL_ID_OP'id(Id) -> IdOp)
	 SAL_Current_Cid -> Cid
	 New_SAL_value_id(P, IdOp, Cid, nil, regular_value -> Vid)  

--------------------------------------------------------------------------
-- SAL_Modify_functions_for_type_WFC
--------------------------------------------------------------------------
-- This function will add the non-nav checkings to all function's bodies
--------------------------------------------------------------------------

'action' SAL_Modify_Contexts_for_type_WFC(SAL_CONTEXTS -> SAL_CONTEXTS)

  'rule' SAL_Modify_Contexts_for_type_WFC(list(Context, Rest) -> list(MContext, MRest))
	 SAL_Modify_Context_for_type_WFC(Context -> MContext)
	 SAL_Modify_Contexts_for_type_WFC(Rest -> MRest)

  'rule' SAL_Modify_Contexts_for_type_WFC(nil -> nil)

--------------------

'action' SAL_Modify_Context_for_type_WFC(SAL_CONTEXT -> SAL_CONTEXT)

  'rule' SAL_Modify_Context_for_type_WFC(context(Id, Cid, Constants) -> 
	              context(Id, Cid, MConstants))
	 SAL_Modify_Constants_for_type_WFC(Constants -> MConstants)

	 -- skipping macro contexts...
  'rule' SAL_Modify_Context_for_type_WFC(MacroContext -> 
	              MacroContext)

--------------------

'action' SAL_Modify_Constants_for_type_WFC(SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Modify_Constants_for_type_WFC(list(sal_const_decl(
		sal_fun_const(IdOp, Vid, Rec, Params, ResultType, Namespace, Body, vid(WFCviolationVid))), Rest) ->
		list(sal_const_decl(MConstant), MRest))
	 where(IdOp -> id(Ident1))
	 SAL_Build_WFC_Condition_from_Params(Ident1, Params, ResultType, Body, WFCviolationVid -> NewBody)
         where(sal_fun_const(IdOp, Vid, Rec, Params, ResultType, Namespace, NewBody, vid(WFCviolationVid)) -> MConstant)
	 -- Processing the rest:
	 SAL_Modify_Constants_for_type_WFC(Rest -> MRest)

  'rule' SAL_Modify_Constants_for_type_WFC(list(Constant, Rest) -> list(Constant, MRest))
	 SAL_Modify_Constants_for_type_WFC(Rest -> MRest)

  'rule' SAL_Modify_Constants_for_type_WFC(list(Constant, Rest) -> list(Constant, MRest))
	 SAL_Modify_Constants_for_type_WFC(Rest -> MRest)

  'rule' SAL_Modify_Constants_for_type_WFC(nil -> nil)

-----------------------
'action' SAL_Build_WFC_Condition_from_Params(IDENT, SAL_FORMAL_FUN_PARAMETERS, SAL_TYPE_EXPR, SAL_VALUE_EXPR, SAL_value_id  -> SAL_VALUE_EXPR)

  'rule' SAL_Build_WFC_Condition_from_Params(Ident1, list(formal_param(Id, TE, _), Rest), ResultType, Body, WFCviolationVid -> FinalBody)
	 SAL_Gen_Non_Nav_Condition(Id, TE -> Non_Nav_Condition)
	 ne(Non_Nav_Condition, nil)
	 -- Processes the rest:
	 SAL_Build_WFC_Condition_from_Params(Ident1, Rest, ResultType, Body, WFCviolationVid -> NewBody)

	 -- Generating the if to propagate the nav is the argument was nav:
	 -- A Tid is needed here to obtain the lifted type constructor for the nav...
	 -- The type SHOULD BE a lifted one, so the following function SHOULD WORK without problems:
	 Select_CC_Result_Type(TE -> Tid) -- it fails if the expression is a subtype, for example, but will work with a lifted subtype...
	 Tid'DefaultNav -> vid(NavVid)
	 Tid'Lifted_fields -> Fields
 	 -- Using the proper destructor (to acces the nav value in the argument:
	 SAL_Find_Accesor_in_Fields(Fields, NavVid -> AccesorVid)
	 where(sal_funct_applic(sal_esp_value_occ(AccesorVid), sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Id)), nil),nil))) -> Appl)
	 SAL_Generate_Result_for_Violation(ResultType, Appl -> ArgNavExpr)
	 where(sal_if_expr(Non_Nav_Condition, NewBody, nil, else(ArgNavExpr)) -> FinalBody)

/*
  'rule' SAL_Build_WFC_Condition_from_Params(Ident, list(Formal, Rest), ResultType, Body, WFCviolationVid -> NewBody)
	 -- The Current Formal param does not generate a Non-nav condition... (WEIRD?)
	 SAL_Build_WFC_Condition_from_Params(Ident, Rest, ResultType, Body, WFCviolationVid -> NewBody)
*/

  'rule' SAL_Build_WFC_Condition_from_Params(_, nil, ResultType, Body, _ -> Body)

---------------------------------------------
'action' SAL_Get_Tids(SAL_LIST_TYPES -> SAL_TYPE_IDS)

  'rule' SAL_Get_Tids(list(Head, Rest) -> list(Tid, Tids))
	 (|
	    where(Head -> list_type(_, Tid))
	 ||
	    where(Head -> map_type(_,_,Tid))
	 |)
	 SAL_Get_Tids(Rest -> Tids)

  'rule' SAL_Get_Tids(nil -> nil)

----------------------------------------------
'action' SAL_Add_is_Type_functions(SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Add_is_Type_functions(Constants -> ExtendedConstants)
	 SAL_RSL_is_Int_Vid -> Is_Int_Vid
	 Is_Int_Vid'Declaration -> Is_Int_Decl
	 SAL_RSL_is_Nat_Vid -> Is_Nat_Vid
	 Is_Nat_Vid'Declaration -> Is_Nat_Decl
	 where(SAL_CONTEXT_CONSTANTS'list(Is_Int_Decl, list(Is_Nat_Decl,Constants)) -> ExtendedConstants)

----------------------------------------------
'action' SAL_Generate_CC_BuiltIn_Context(-> SAL_CONTEXT)

  'rule' SAL_Generate_CC_BuiltIn_Context(-> CC_BuiltIns)
	 -- Processing the basic types:
	 Default_Int_Tid -> IntTid
	 SAL_Gen_Lifted_Decl(IntTid -> LiftedIntDecl)
	 IntTid'Lifted_Tid -> tid(LIntTid)
	 LIntTid'Declaration <- LiftedIntDecl
	 -- Nat is not added because there is no Nat type (as it is a subtype of Int)
	 -- in the lifted version (that works with maximal types only)
	 -- Bool...
	 Default_Bool_Tid -> BoolTid
	 SAL_Gen_Lifted_Decl(BoolTid -> LiftedBoolDecl)
	 BoolTid'Lifted_Tid -> tid(LBoolTid)
	 LBoolTid'Declaration <- LiftedBoolDecl
	 -- Adding the Not_a_value_type
	 SAL_Nav_Tid -> NavTid
	 SAL_Gen_Lifted_Decl(NavTid -> LiftedNavDecl)
	 NavTid'Declaration <- LiftedNavDecl
	 -- Generating the new context:
	 string_to_id("L_BUILTIN" -> Ident)
	 -- Generate the Cid:
	 New_SAL_context_id(Ident,0 -> LBuiltIns)
	 SAL_Generate_Context(LBuiltIns, SAL_CONTEXT_CONSTANTS'list(LiftedNavDecl, list(LiftedBoolDecl, list(LiftedIntDecl, nil))) -> CC_BuiltIns)
-----------------------------------------------
'action' Collect_Reconstructor_Decls(SAL_CONTEXT_CONSTANTS)

  'rule' Collect_Reconstructor_Decls(Decls)
	 Collected_Reconstructors -> CDecls
	 -- cwg changed to only collect reconstructors
	 Collect_Reconstructor_Decls1(Decls, CDecls -> NDecls)
	 Collected_Reconstructors <- NDecls

'action' Collect_Reconstructor_Decls1(SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' Collect_Reconstructor_Decls1(list(H, T), CDecls -> NDecls):
	 Collect_Reconstructor_Decls1(T, CDecls -> NDecls1)
	 (|
	   where(H -> sal_const_decl(sal_fun_const(_, Vid, _, _, _, _, _, _)))
	   Vid'VType -> reconstructor_value
	   Add_Decl(H, NDecls1 -> NDecls)
	 ||
	   where(NDecls1 -> NDecls)
	 |)

  'rule' Collect_Reconstructor_Decls1(nil, CDecls -> CDecls):

'action' Add_Decl(SAL_CONTEXT_CONSTANT, SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)
-- only add decl if not already there
  'rule' Add_Decl(D0, list(D, DS)  -> list(D, DS1)):
	 (|
	   eq(D0, D)
	   where(DS -> DS1)
         ||
	   Add_Decl(D0, DS -> DS1)
	 |)

  'rule' Add_Decl(D0, nil -> list(D0, nil)):

-----------------------------------------------

'action' SAL_Remove_Decls_From_Contexts(SAL_CONTEXT_CONSTANTS, SAL_context_id, SAL_CONTEXTS -> SAL_CONTEXTS)

  'rule' SAL_Remove_Decls_From_Contexts(Decls, Cid, list(H, T) -> Res):
	 (|
	   where(H -> context(Id, cid(Cid1), SCCs))
	   eq(Cid, Cid1)
	   SAL_Remove_Decls_From_Context_Constants(Decls, SCCs -> SCCs1)
--Putmsg("Removing from ")
--Print_id(Id)
--Putnl()
	   where(context(Id, cid(Cid1), SCCs1) -> H1)
	   where(SAL_CONTEXTS'list(H1, T) -> Res)
	 ||
	   SAL_Remove_Decls_From_Contexts(Decls, Cid, T -> T1)
	   where(SAL_CONTEXTS'list(H, T1) -> Res)
	 |)

  'rule' SAL_Remove_Decls_From_Contexts(_, _, nil -> nil):

'action' SAL_Remove_Decls_From_Context_Constants(SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Remove_Decls_From_Context_Constants(list(D, Ds), SCCs -> SCCs2):
	 SAL_Remove_Decl_From_Context_Constants(D, SCCs -> SCCs1)
	 SAL_Remove_Decls_From_Context_Constants(Ds, SCCs1 -> SCCs2)

  'rule' SAL_Remove_Decls_From_Context_Constants(nil, SCCs -> SCCs):

'action' SAL_Remove_Decl_From_Context_Constants(SAL_CONTEXT_CONSTANT, SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Remove_Decl_From_Context_Constants(D, list(H, T) -> Res):
	 -- allow for duplicates in list
	 SAL_Remove_Decl_From_Context_Constants(D, T -> T1)
	 (|
	   eq(D, H)
	   where(T1 -> Res)
	 ||
	   where(SAL_CONTEXT_CONSTANTS'list(H, T1) -> Res)
	 |)

  'rule' SAL_Remove_Decl_From_Context_Constants(_, nil -> nil):


-----------------------------------------------

'action' Collect_Is_Type_Function(SAL_CONTEXT_CONSTANTS)

  'rule' Collect_Is_Type_Function(Decls)
	 Collected_Is_Type_Functions -> CDecls
	 SAL_Concatenate_Context_Constants(CDecls, Decls -> NDecls)
	 Collected_Is_Type_Functions <- NDecls

'action' Collect_Lifted_Constructor(SAL_CONTEXT_CONSTANTS)

  'rule' Collect_Lifted_Constructor(Decls)
	 Collected_Lifted_Constructors -> CDecls
	 SAL_Concatenate_Context_Constants(CDecls, Decls -> NDecls)
	 Collected_Lifted_Constructors <- NDecls

'action' Collect_Lifted_Destructor(SAL_CONTEXT_CONSTANTS)

  'rule' Collect_Lifted_Destructor(Decls)
	 Collected_Lifted_Destructors -> CDecls
	 SAL_Concatenate_Context_Constants(CDecls, Decls -> NDecls)
	 Collected_Lifted_Destructors <- NDecls

----------------------------------------------------------------------------------------
'action' SAL_Replace_Vars_in_Exprs(SAL_VAR_DECLS, SAL_VALUE_EXPRS -> SAL_VALUE_EXPRS)

  'rule' SAL_Replace_Vars_in_Exprs(Vars, list(E1, Rest) -> list(ME1, MRest))
	 SAL_Replace_Vars_in_Expr(Vars, E1 -> ME1)
	 SAL_Replace_Vars_in_Exprs(Vars, Rest -> MRest)

  'rule' SAL_Replace_Vars_in_Exprs(_, nil -> nil)

'action' SAL_Replace_Vars_in_Expr(SAL_VAR_DECLS, SAL_VALUE_EXPR -> SAL_VALUE_EXPR)

  'rule' SAL_Replace_Vars_in_Expr(list(var_decl(_, Id, _, CC_Type), Rest), VE -> Result)
	 where(CC_Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)), _)))
	 Tid'Constructor -> vid(ConstVid)
	 DefaultPos(-> P)
	 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Id)), nil), nil))) -> ValOcc)
	 SAL_Replace_Ident(Id, ValOcc, VE -> Res1)
	 SAL_Replace_Vars_in_Expr(Rest, Res1 -> Result)

  'rule' SAL_Replace_Vars_in_Expr(list(var_decl(_, Id, _, CC_Type), Rest), VE -> Result)
	 where(CC_Type -> type_refs(sal_defined(_,_,Tid)))
	 Tid'Lifted_Tid -> tid(LTid)
	 LTid'Constructor -> vid(ConstVid)
	 DefaultPos(-> P)
	 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Id)), nil), nil))) -> ValOcc)
	 SAL_Replace_Ident(Id, ValOcc, VE -> Res1)
	 SAL_Replace_Vars_in_Expr(Rest, Res1 -> Result)

  'rule' SAL_Replace_Vars_in_Expr(nil, Expr -> Expr)

-------------------------------------------------------------------------------------

'action' SAL_Replace_Ident(IDENT, SAL_VALUE_EXPR, SAL_VALUE_EXPR -> SAL_VALUE_EXPR)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_product(ValueExprs) -> sal_product(MExprs))
	SAL_Replace_Idents(Ident, ValOcc, ValueExprs -> MExprs)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_ranged_set(L,R,T) -> sal_ranged_set(ML, MR, T))
	SAL_Replace_Ident(Ident, ValOcc, L -> ML)
	SAL_Replace_Ident(Ident, ValOcc, R -> MR)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_enum_set(Tid, T, ES)-> sal_enum_set(Tid, T, MES))
	SAL_Replace_Idents(Ident, ValOcc, ES -> MES)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_comp_simp_set(SB, E) -> sal_comp_simp_set(SB, ME))
	-- We are trying to replace a name from an outer scope (i.e. input/comprehended guarded cmd)
	-- the same name shouldn't be introduced inside the set...
	SAL_Replace_Ident(Ident, ValOcc, E -> ME)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_comp_set(E, T, SB, Restr) -> sal_comp_set(ME,T,SB,MRestr))
	SAL_Replace_Ident(Ident, ValOcc, E -> ME)
	-- Here again, the binding is used to introduce new names into the expression... we are looking for
	-- a name in a specially created expression that is globally accesible in the expression... 
	SAL_Replace_Ident(Ident, ValOcc, Restr -> MRestr)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_ranged_list(D,R) -> sal_ranged_list(MD,MR))
	SAL_Replace_Ident(Ident, ValOcc, D -> MD)
	SAL_Replace_Ident(Ident, ValOcc, R -> MR)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_enum_list(ES) -> sal_enum_list(MES))
	SAL_Replace_Idents(Ident, ValOcc, ES -> MES)
--sal_comp_list
 'rule' SAL_Replace_Ident(Ident, ValOcc,sal_enum_map(Tid,D,R,EPs) -> sal_enum_map(Tid,D,R,MEPs))
	SAL_Replace_Ident_Pairs(Ident, ValOcc, EPs -> MEPs)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_comp_rng_map(E,Vid,Nid,SB,Restr)-> sal_comp_rng_map(ME,Vid,Nid,SB,MRestr))
	SAL_Replace_Ident(Ident, ValOcc, E -> ME)
	-- Again here, skipping the bindings...
	SAL_Replace_Ident(Ident, ValOcc, Restr -> MRestr)

--sal_comp_map
 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_function(LB, E) -> sal_function(LB, ME))
	-- Again here... skipping the names in the lambda function...
	SAL_Replace_Ident(Ident, ValOcc, E -> ME)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_map_applic(Tid, E, sal_argument(ES)) -> sal_map_applic(Tid, ME, sal_argument(MES)))
	SAL_Replace_Ident(Ident, ValOcc, E -> ME)
	SAL_Replace_Idents(Ident, ValOcc, ES -> MES)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_funct_applic(E, sal_argument(ES)) -> sal_funct_applic(ME, sal_argument(MES)))
	SAL_Replace_Ident(Ident, ValOcc, E -> ME)
	SAL_Replace_Idents(Ident, ValOcc, ES -> MES)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_destr_applic(E,E1) -> sal_destr_applic(ME,ME1))
	SAL_Replace_Ident(Ident, ValOcc, E -> ME)
	SAL_Replace_Ident(Ident, ValOcc, E1 -> ME1)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_quantified(BO, SB, Restr) -> sal_quantified(BO,SB,MRestr))
	-- Skipping the bindings again...
	SAL_Replace_Ident(Ident, ValOcc, Restr -> MRestr)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_equivalence(L,R,Pre) -> sal_equivalence(ML,MR,MPre))
	SAL_Replace_Ident(Ident, ValOcc, L -> ML)
	SAL_Replace_Ident(Ident, ValOcc, R -> MR)
	SAL_Replace_Ident(Ident, ValOcc, Pre -> MPre)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_bracket(E) -> sal_bracket(ME))
	SAL_Replace_Ident(Ident, ValOcc, E -> ME)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_funct_expr(Op,Q,E1,E2) -> sal_funct_expr(Op,Q,ME1,ME2))
	SAL_Replace_Ident(Ident, ValOcc, E1 -> ME1)
	SAL_Replace_Ident(Ident, ValOcc, E2 -> ME2)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_ax_infix(L,IdOp,R) -> sal_ax_infix(ML,IdOp,MR))
	SAL_Replace_Ident(Ident, ValOcc, L -> ML)
	SAL_Replace_Ident(Ident, ValOcc, R -> MR)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_ax_prefix(Conn, E) -> sal_ax_prefix(Conn, ME))
	SAL_Replace_Ident(Ident, ValOcc, E -> ME)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_let_expr(Id,T,NameSpace, ValOcc1,Init,Expr) 
					 -> sal_let_expr(Id,T,NameSpace, ValOcc1,MInit,MExpr))
	-- Skipping the bindings...
	SAL_Replace_Ident(Ident, ValOcc, Init -> MInit)
	SAL_Replace_Ident(Ident, ValOcc, Expr -> MExpr)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_if_expr(E, Then, Eif, else(Else)) -> sal_if_expr(ME, MThen, MEif, else(MElse)))
	SAL_Replace_Ident(Ident, ValOcc, E -> ME)
	SAL_Replace_Ident(Ident, ValOcc, Then -> MThen)
	SAL_Replace_Ident_in_Elsif_Expr(Ident, ValOcc, Eif -> MEif)
	SAL_Replace_Ident(Ident, ValOcc, Else -> MElse)
	
 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_infix_occ(L,IdOp,R) -> sal_infix_occ(ML,IdOp,MR))
	SAL_Replace_Ident(Ident, ValOcc, L -> ML)
	SAL_Replace_Ident(Ident, ValOcc, R -> MR)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_esp_prefix_occ(IdOp,L,R) -> sal_esp_prefix_occ(IdOp,ML,MR))
	SAL_Replace_Ident(Ident, ValOcc, L -> ML)
	SAL_Replace_Ident(Ident, ValOcc, R -> MR)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_prefix_occ(IdOp,Qual,E) -> sal_prefix_occ(IdOp,Qual,ME))
	SAL_Replace_Ident(Ident, ValOcc, E -> ME)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_assignment(Id, E) -> sal_assignment(Id, ME))
	SAL_Replace_Ident(Ident, ValOcc, E -> ME)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_recogniser(Vid, sal_argument(Exprs)) -> 
					sal_recogniser(Vid, sal_argument(MExprs)))
	SAL_Replace_Idents(Ident, ValOcc, Exprs -> MExprs)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_var_occ(_, VarId) -> ValOcc)
	VarId'Ident -> Id
	eq(Id, Ident)	

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_esp_unary_prefix_occ(Op, E) -> sal_esp_unary_prefix_occ(Op, ME))
	SAL_Replace_Ident(Ident, ValOcc, E -> ME)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_esp_ternary_occ(Op, A1, A2, A3) -> sal_esp_ternary_occ(Op, MA1, MA2, MA3))
	SAL_Replace_Ident(Ident, ValOcc, A1 -> MA1)
	SAL_Replace_Ident(Ident, ValOcc, A2 -> MA2)
	SAL_Replace_Ident(Ident, ValOcc, A3 -> MA3)

 'rule' SAL_Replace_Ident(Ident, ValOcc, sal_value_occ(ValId,Qual) -> Result)
	(|
	    where(ValId -> val_id(id(Id)))
	    eq(Id, Ident)
	    where(ValOcc -> Result)
	||
	    where(ValId -> record_val_id(P, id(Id), Field))
	    eq(Id, Ident)
	    where(sal_value_occ(complex_val_id(P, ValOcc, Field),Qual) -> Result)
	||
	    where(sal_value_occ(ValId,Qual) -> Result)
	|)

  -- The rest of the value expressions are untouched:
 'rule' SAL_Replace_Ident(Ident, ValOcc, E -> E)

---------------------------------------------------------------------------------------------
'action' SAL_Replace_Ident_Pairs(IDENT, SAL_VALUE_EXPR, SAL_VALUE_EXPR_PAIRS -> SAL_VALUE_EXPR_PAIRS)

  'rule' SAL_Replace_Ident_Pairs(Ident, ValOcc, list(pair(LE,RE), Rest) -> list(pair(MLE, MRE), MRest))
	 SAL_Replace_Ident(Ident, ValOcc, LE -> MLE)
	 SAL_Replace_Ident(Ident, ValOcc, RE -> MRE)
	 SAL_Replace_Ident_Pairs(Ident, ValOcc, Rest -> MRest)

  'rule' SAL_Replace_Ident_Pairs(_, _, nil -> nil)
	 
---------------------------------------------------------------------------------------------
'action' SAL_Replace_Idents(IDENT, SAL_VALUE_EXPR, SAL_VALUE_EXPRS -> SAL_VALUE_EXPRS)

  'rule' SAL_Replace_Idents(Ident, ValOcc, list(Expr, Rest) -> list(MExpr, MRest))
	 SAL_Replace_Ident(Ident, ValOcc, Expr -> MExpr)
	 SAL_Replace_Idents(Ident, ValOcc, Rest -> MRest)

  'rule' SAL_Replace_Idents(_,_, nil -> nil)
---------------------------------------------------------------------------------------------
'action' SAL_Replace_Ident_in_Elsif_Expr(IDENT, SAL_VALUE_EXPR, SAL_ELSIF_BRANCHES -> SAL_ELSIF_BRANCHES)

  'rule' SAL_Replace_Ident_in_Elsif_Expr(Ident, ValOcc, list(elsif(If, Then), Rest) -> list(elsif(MIf, MThen), MRest))
	 SAL_Replace_Ident(Ident, ValOcc, If -> MIf)
	 SAL_Replace_Ident(Ident, ValOcc, Then -> MThen)
	 SAL_Replace_Ident_in_Elsif_Expr(Ident, ValOcc, Rest -> MRest)

  'rule' SAL_Replace_Ident_in_Elsif_Expr(_,_, nil -> nil)

------------------------------------------------------------------------------------------
-- SAL_Gen_Nav_Transitions
------------------------------------------------------------------------------------------
-- This function generates the additional guarded transitions that will be triggered 
-- when any of the state variables is set to a nav value.
------------------------------------------------------------------------------------------
'action' SAL_Gen_Nav_Transitions(SAL_VAR_DECLS, SAL_VAR_DECLS -> SAL_TRANSITIONS)

  'rule' SAL_Gen_Nav_Transitions(list(var_decl(_,Id, VarId, Type),  Rest), Vars -> list(transition(nil, Guard, Commands), TransRest))
	 SAL_Gen_Nav_Transitions(Rest, Vars -> TransRest)
	 where(Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 Tid'DefaultNav -> vid(NavVid)
	 where(sal_recogniser(NavVid,
		sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Id)),nil),nil))) -> Guard)
         Tid'Lifted_fields -> Fields
	 SAL_Find_Accesor_in_Fields(Fields, NavVid -> AccesorVid)
	 where(sal_funct_applic(sal_esp_value_occ(AccesorVid), sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Id)), nil),nil))) -> NavValue)
	 SAL_Generate_Commands(Vars, NavValue -> Commands)

  'rule' SAL_Gen_Nav_Transitions(nil,_ -> nil)

'action' SAL_Generate_Commands(SAL_VAR_DECLS, SAL_VALUE_EXPR -> SAL_VALUE_EXPRS)

  'rule' SAL_Generate_Commands(list(var_decl(_,Id, VarId, Type),  Rest), NavValue -> 
                list(sal_funct_expr(val_id(sal_op_symb(sal_infix_op(eq))), nil,
				      sal_var_occ(Pos, PrimedVarId), AssignValue), AssignRest))
	 VarId'Pos -> Pos
	 IncreaseCol(Pos -> PrimedPos)
	 look_up_variable_id(PrimedPos -> var(PrimedVarId))
	 where(Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 Tid'DefaultNav -> vid(NavVid)
	 where(sal_funct_applic(sal_esp_value_occ(NavVid), sal_argument(SAL_VALUE_EXPRS'list(NavValue, nil))) -> AssignValue)
	 SAL_Generate_Commands(Rest, NavValue -> AssignRest)

  'rule' SAL_Generate_Commands(nil, _ -> nil)
--------------------------------------------------------------------------
'action' Get_Invalid_Insertion_Nav(-> SAL_value_id)

  'rule' Get_Invalid_Insertion_Nav(-> NavVid)
	 (|
	    InvalidCollectionInsertionNav -> nil
            DefaultPos(-> P)
	    Extend_Nav_Type(P, "Argument_being_inserted_in_collection_out_of_subtype" -> NavVid) 
	    where(vid(NavVid) -> NavVid1)
	    InvalidCollectionInsertionNav <- NavVid1
         ||
	    InvalidCollectionInsertionNav -> vid(NavVid)
	 |)
--------------------------------------------------------------------------------
'action' Get_Swap_Nav(-> SAL_value_id)

  'rule' Get_Swap_Nav(-> NavVid):
	 (|
	    SwapNav -> nil
            DefaultPos(-> P)
	    Extend_Nav_Type(P, "Cases_not_exhaustive" -> NavVid) 
	    where(vid(NavVid) -> NavVid1)
	    SwapNav <- NavVid1
         ||
	    SwapNav -> vid(NavVid)
	 |)
-------------------------------------------------------
'action' SAL_Update_Names(IDENT, SAL_context_id -> IDENT)

  'rule' SAL_Update_Names(Id, Cid -> NewId)
	 SAL_Update_Id(Id -> NewId)
	 Cid'Ident <- NewId

'action' SAL_Update_Id(IDENT -> IDENT)

  'rule' SAL_Update_Id(Id -> NewId)
	 id_to_string(Id -> Str)
	 Concatenate(Str, "_simple" -> NewStr)
	 string_to_id(NewStr -> NewId)

'action' SAL_Generate_Simple_CC_BuiltIn_Context(-> SAL_CONTEXT)

  'rule' SAL_Generate_Simple_CC_BuiltIn_Context(-> CC_BuiltIns)
	 -- Processing the basic types:
	 Default_Int_Tid -> IntTid
	 SAL_Gen_Lifted_Decl(IntTid -> LiftedIntDecl)
	 IntTid'Lifted_Tid -> tid(LIntTid)
	 LIntTid'Declaration <- LiftedIntDecl
	 -- Nat is not added because there is no Nat type (as it is a subtype of Int)
	 -- in the lifted version (that works with maximal types only)
	 -- Bool...
	 Default_Bool_Tid -> BoolTid
	 SAL_Gen_Lifted_Decl(BoolTid -> LiftedBoolDecl)
	 BoolTid'Lifted_Tid -> tid(LBoolTid)
	 LBoolTid'Declaration <- LiftedBoolDecl
	 -- Adding the Not_a_value_type
	 SAL_Nav_Tid -> NavTid
	 SAL_Gen_Lifted_Decl(NavTid -> LiftedNavDecl)
	 -- Generating the new context:
	 string_to_id("L_BUILTIN_simple" -> Ident)
	 -- Generate the Cid:
	 New_SAL_context_id(Ident,0 -> LBuiltIns)
	 -- Doing the trick with the nav value now:
	 -- Updating the context information first to get the proper qualification:
	 Update_Reference_Information(LBuiltIns, SAL_CONTEXT_CONSTANTS'list(LiftedNavDecl, nil))
	 SAL_Symplify_Nav_Type
	 -- Obtaining the new declaration for the nav type:
	 SAL_Gen_Lifted_Decl(NavTid -> LiftedNavDecl1)
	 NavTid'Declaration <- LiftedNavDecl1
	 SAL_Generate_Context(LBuiltIns, SAL_CONTEXT_CONSTANTS'list(LiftedNavDecl1, list(LiftedBoolDecl, list(LiftedIntDecl, nil))) -> CC_BuiltIns)

-------------------------------------------------------------------------------------
-- SAL_Symplify_Nav_Type
-------------------------------------------------------------------------------------
-- This function will modify all the value_ids inside the Not_a_value_type into the same
-- nav id (so, when outputted, it will be like only one nav) and then will remove all of them
-------------------------------------------------------------------------------------
'action' SAL_Symplify_Nav_Type

  'rule' SAL_Symplify_Nav_Type
	 SAL_Nav_Tid -> NavTid
	 NavTid'Lifted_fields -> Fields
	 SAL_Simplify_Vids_in_Fields(Fields -> NewFields)
	 where(NewFields -> list(H,_))
	 NavTid'Lifted_fields <- list(H,nil)

'action' SAL_Simplify_Vids_in_Fields(SAL_DATA_TYPE_PARTS -> SAL_DATA_TYPE_PARTS)

  'rule' SAL_Simplify_Vids_in_Fields(list(sal_part(Const, T), Rest) -> list(sal_part(NewConst,T), NewRest))
	 where(Const -> sal_construc(id(NavConstId), NavConstVid, NavAccesor,nil))
	 string_to_id("nav" -> NavId)
	 NavConstVid'IdOp <- id(NavId)
	 where(sal_construc(id(NavId), NavConstVid, NavAccesor,nil) -> NewConst)
	 SAL_Simplify_Vids_in_Fields(Rest -> NewRest)

  'rule' SAL_Simplify_Vids_in_Fields(nil -> nil)

---------------------------------------------
