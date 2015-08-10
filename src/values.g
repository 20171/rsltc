-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the third pass of the type checker: Make_value_env
-- plus the fourth and final pass: Check_value_env
-- plus lookup for variables and channels
-- plus Lookup_value_name for value names 
-- (which returns types rather than identifiers)
-- Expressions statically have types plus accesses (read, write, in out)
-- A RESULT is a type plus accesses in each category
-- In general expressions have sets of possible RESULTS

'module' values

'export' Check_value_env Make_value_env
--	 Make_variable_env_defs Make_channel_env_defs
	 Define_value_typing Define_value_typings
	 Define_value_binding Define_pattern
	 Lookup_value_name Lookup_current_value_name
	 Lookup_env_value_name Lookup_id_or_op1
	 Lookup_variable_name Lookup_current_variable_name
	 Lookup_env_variable_name Lookup_env_variable_id
	 Lookup_channel_name Lookup_current_channel_name
	 Lookup_env_channel_name Lookup_env_channel_id
	 Make_results Make_pure_results Type_check Isin
	 Make_single_typing Openenv Closeenv
	 Make_set_element_type Make_list_element_type Make_map_element_types Make_array_element_types
	 Make_products Mult Intersection_result Union_ids
	 Lub_coercions Is_in_coercion Is_in_coercions
	 No_more_accesses Concat_accs
	 Flatten_access Result_type
	 Type_of_typings_as_product
	 Defined_type_of_typing Defined_type_of_typings
	 Select_id_by_pos 
	 Contains_poly Contains_polynum Collect_polynums
	 Intersect_polynums Increment_polynums
	 Poly_disambiguate_args Contains_any_or_poly
	 Intersection

	 -- For reuse in cc.g (when resolving transition systems)
	 Generate_Primes

'use' ast print ext env types objects cc sal_global_vars

--------------------------------------------------------------
-- Environments
--------------------------------------------------------------

'action' Openenv
-- open inner scope

  'rule' Openenv:
	 Get_current_values(-> ES)
	 Set_current_values(list(nil,ES))

'action' Closeenv
-- close inner scope

  'rule' Closeenv:
	 Get_current_values(-> ES)
	 where(ES -> list(E,ES1))
	 Set_current_values(ES1)

'action' Make_value_env(CLASS)

  'rule' Make_value_env(basic(DS)):
	 Define_value_decls(DS)

  'rule' Make_value_env(instantiation(N, Objs)):
	 (|
	   where(N -> name(P,id_op(Id)))
	 || -- error of using qualified scheme name already reporte
	    -- in Make_basic_env
	   where(N -> qual_name(P, _, id_op(Id)))
	 |)
	 [| -- allow for failure to find scheme (already reported)
	   Get_id_of_scheme(Id -> scheme_id(I))	 
	   I'With -> W	 
	   Set_current_with(W)
	   I'Params -> PARMS
	   I'Class -> CL
	   Make_value_env(CL)
	 |]

  'rule' Make_value_env(extend(CL1, CL2)):
	 In_left 
	 Make_value_env(CL1)
	 Left_right
	 Make_value_env(CL2)
	 Out_right
	 
  'rule' Make_value_env(hide(H, C)):
	 Make_value_env(C)
	 -- hides put in environment by Make_basic_env
	 [|
	   (| where(H -> list(def_name(P,_),_)) || where(H -> list(disamb(P,_,_),_)) |)
	   Check_hide(P)
	 |]  

  'rule' Make_value_env(rename(R, C)):
	 Make_value_env(C)
	 -- renames put in environment by Make_basic_env
	 [|
	   (| where(R -> list(rename(def_name(P,_),_),_))
	   || where(R -> list(rename(disamb(P,_,_),_),_)) |)
	   Check_rename(P)
	 |]  

  'rule' Make_value_env(with(P,Obj, C))
	 Make_value_env(C)

'action' Define_value_decls(DECLS)

  'rule' Define_value_decls(list(D,DS)):
	 Define_value_decl(D)
	 Define_value_decls(DS)

  'rule' Define_value_decls(nil):
-- debug
-- Get_current_values(-> VES)
-- Print_value_envs(VES)

'action' Define_value_decl(DECL)

  'rule' Define_value_decl(type_decl(P,Defs)):
	 Define_value_from_type_defs(Defs)

  'rule' Define_value_decl(value_decl(P,Defs)):
	 Define_value_defs(Defs)

  'rule' Define_value_decl(variable_decl(P,Defs)):
	 Define_variable_defs(Defs) 

  'rule' Define_value_decl(channel_decl(P,Defs)):
	 Define_channel_defs(Defs) 

  'rule' Define_value_decl(object_decl(P,Defs)):
	 Define_value_object_defs(Defs)

  'rule' Define_value_decl(axiom_decl(P,Defs)):
	 Define_axiom_defs(Defs)

  'rule' Define_value_decl(test_case_decl(P,Defs)):
	 Define_test_case_defs(Defs)

  -- Added for SAL (Model checking)
  'rule' Define_value_decl(trans_system_decl(P, Defs)):
	 Define_trans_sys_defs(Defs)

  'rule' Define_value_decl(property_decl(P, Defs)):
	 Define_property_defs(Defs)

'action' Define_value_defs(VALUE_DEFS)

  'rule' Define_value_defs(list(H,T)):
	 Define_value_def(H)
	 Define_value_defs(T)

  'rule' Define_value_defs(nil):

'action' Define_value_def(VALUE_DEF)

  'rule' Define_value_def(typing(P,T)):
	 Define_value_typing(T)

  'rule' Define_value_def(exp_val(P,T,V)):
	 Define_value_typing(T)

  'rule' Define_value_def(imp_val(P,T,V)):
	 Define_value_typing(T)

  'rule' Define_value_def(exp_fun(P,T,A,E,POST,PRE,_)):
	 Define_value_typing(T)

  'rule' Define_value_def(imp_fun(P,T,A,C,PRE)):
	 Define_value_typing(T)

'action' Define_value_typing(TYPING)

  'rule' Define_value_typing(single(P,B,T)):
	 Define_value_binding(B,T)

  'rule' Define_value_typing(multiple(P,BS,T)):
	 Define_value_mult_bindings(BS,T)

'action' Define_value_typings(TYPINGS)

  'rule' Define_value_typings(list(T, TS)):
	 Define_value_typing(T)
	 Define_value_typings(TS)

  'rule' Define_value_typings(nil):

'action' Define_value_mult_bindings(BINDINGS, TYPE_EXPR)

  'rule' Define_value_mult_bindings(list(B,BS), T):
	 Check_type_defined(T -> T1)
	 Define_value_binding2(B,T1)
	 Define_value_mult_bindings(BS,T1)

  'rule' Define_value_mult_bindings(nil, T):

'action' Define_value_binding(BINDING, TYPE_EXPR)

  'rule' Define_value_binding(B, T)
	 Check_type_defined(T -> T1)
	 Define_value_binding2(B, T1)

'action' Define_value_binding2(BINDING, TYPE_EXPR)

  'rule' Define_value_binding2(single(P,Id_or_op), T):
	 Define_id_or_op(P, Id_or_op, T -> _)

  'rule' Define_value_binding2(product(P,BS), T):
	 Define_value_bindings(P, BS, T)

'action' Define_value_bindings(POS, BINDINGS, TYPE_EXPR)

  'rule' Define_value_bindings(P, list(H,nil), T):
	 Define_value_binding2(H,T)

  'rule' Define_value_bindings(P, BS, T)
	 Length_bs(BS -> N1)
	 Make_product_type(T, N1 -> T1)
	 (|
	   where(T1 -> product(PR))
	   Length_pr(PR -> N2)
	   eq(N1,N2)
	   Define_value_bindings_prod(BS, PR)
	 ||
	   Puterror(P)
	   Putmsg("Structure of product binding (")
	   Print_bindings(BS)
	   Putmsg(") does not match structure of type ")
	   Print_type(T)
	   Putnl()
	   Define_bindings_any(BS)
	 |)

'action' Define_value_bindings_prod(BINDINGS, PRODUCT_TYPE)

  'rule' Define_value_bindings_prod(list(B,nil),list(T,nil)):
	 Define_value_binding2(B,T)

  'rule' Define_value_bindings_prod(list(B,BS),list(T,PR)):
	 Define_value_binding2(B,T)
	 Define_value_bindings_prod(BS,PR)

'action' Define_bindings_any(BINDINGS)

  'rule' Define_bindings_any(list(B,BS)):
	 Define_binding_any(B)
	 Define_bindings_any(BS)

  'rule' Define_bindings_any(nil):

'action' Define_binding_any(BINDING)

  'rule' Define_binding_any(single(P,Id_or_op)):
	 Define_id_or_op(P, Id_or_op, any -> _)

  'rule' Define_binding_any(product(P,BS)):
	 Define_bindings_any(BS)

'action' Define_id_or_op(POS, ID_OR_OP, TYPE_EXPR -> OPT_VALUE_ID)

  'rule' Define_id_or_op(P, Id_or_op, T -> nil):
	 ne(T,any)  -- type already checked, so error already reported
	 (|
	   Is_defined_value(Id_or_op, T)
	   Puterror(P)
	   Putmsg("Value identifier ")
	   Print_id_or_op(Id_or_op)
	   Putmsg(" already defined with type ")
	   Print_type(T)
	   Putnl()
	 ||
	   where(Id_or_op -> id_op(Id))
	   -- only check for variable of same name if not in inner scope
	   Get_current_values(-> list(VE, nil))
	   Get_current_variables(-> VARS)
	   Lookup_env_variable_id1(Id, VARS -> variable_id(I))
	   I'Pos -> P1
	   Puterror(P)
	   Putmsg("Identifier ")
	   Print_id(Id)
	   Putmsg(" also defined as a variable at ")
	   PrintPos(P1)
	   Putnl()
	 ||
	   where(Id_or_op -> op_op(Op))
	   Predefined_type(Op, T -> T1)
	   ne(T1, none)
	   Puterror(P)
	   Putmsg("Operator `")
	   Print_op(Op)
	   Putmsg("' predefined with type ")
	   Print_type(T1)
	   Putnl()
	 |)

  'rule' Define_id_or_op(P, Id_or_op, T -> value_id(I)):
	 Get_current_values(-> list(VE,VES))
	 New_value_id(P, Id_or_op -> I)
	 I'Type <- T
	 Set_current_values(list(list(I, VE), VES))

'condition' Is_defined_value(ID_OR_OP, TYPE_EXPR)

  'rule' Is_defined_value(Id_or_op, T):
	 Get_current_values(-> list(VE,VES))
	 Lookup_id_or_op1(Id_or_op, VE -> Ids)
	 Type_isin_ids(T, nil, Ids)

'action' Predefined_type(OP, TYPE_EXPR -> TYPE_EXPR)

  'rule' Predefined_type(Op, T -> T1)
	 Lookup_op_types(Op -> Ids)
	 Intersection(T, Ids -> Ids1)
	 (|
	   where(Ids1 -> list(I, _))
	   I'Type -> T1
	 ||
	   where(TYPE_EXPR'none -> T1)
	 |)

--------------------------------------------------------------------------
-- Hides and renames
-------------------------------------------------------------------------

'action' Check_hide(POS)

  'rule' Check_hide(P):
	 Get_current_adapts( -> ADS)
	 Check_duplicate_hides(P, ADS -> ADS1)
	 Set_current_adapts(ADAPTS'nil)
	 Check_all_hides_found(P, ADS1)
	 Set_current_adapts(ADS1)

'action' Check_duplicate_hides(POS, ADAPTS -> ADAPTS)

  'rule' Check_duplicate_hides(P, hide(Id, ADS) -> ADS1):
	 (|
	   Is_hidden(Id, ADS)
	   Puterror(P)
	   Putmsg("Hidden item ")
	   Print_id_or_op(Id)
	   Putmsg(" duplicated: ignored")
	   Putnl()
	   Check_duplicate_hides(P, ADS -> ADS1)
	 ||
	   Old_is_in_renames(Id, ADS)
	   Puterror(P)
	   Putmsg("Hidden item ")
	   Print_id_or_op(Id)
	   Putmsg(" renamed: ignored")
	   Putnl()
	   Check_duplicate_hides(P, ADS -> ADS1)
	 ||
	   Check_duplicate_hides(P, ADS -> ADS2)
	   where(ADAPTS'hide(Id, ADS2) -> ADS1)
	 |)

  'rule' Check_duplicate_hides(P, rename(Nid, Oid, ADS) -> rename(Nid, Oid, ADS1)):
	 Check_duplicate_hides(P, ADS -> ADS1)

  'rule' Check_duplicate_hides(P, nil -> nil):

'condition' Is_hidden(ID_OR_OP, ADAPTS)

  'rule' Is_hidden(Id, hide(Id1, ADS)):
	 (| eq(Id, Id1) || Is_hidden(Id, ADS) |)

  'rule' Is_hidden(Id, rename(Nid, Oid, ADS)):
	 (|
	   Equal_id_or_op(Id, Nid)
	   Is_hidden(Oid, ADS)
	 ||
	   Is_hidden(Id, ADS)
	 |)

'action' Check_all_hides_found(POS, ADAPTS)

  'rule' Check_all_hides_found(P, hide(Id, ADS)):
	 Adapt(Id, ADS -> id(Id1))
	 Get_current_env(-> CE)
	 Find_id_or_op(P, Id1, CE -> Found)
	 [|
	   ne(Found, found)
	   Puterror(P)
	   Putmsg("Hidden item ")
	   Print_id_or_op(Id)
	   Putmsg(" not defined")
	   Putnl()
	 |]
	 Check_all_hides_found(P, ADS)

  'rule' Check_all_hides_found(P, rename(Nid, Oid, ADS)):
	 Check_all_hides_found(P, ADS)

  'rule' Check_all_hides_found(P, nil):

'action' Find_id_or_op(POS, ID_OR_OP, CLASS_ENV -> FOUND)

  'rule' Find_id_or_op(P, Id, basic_env(TYP, list(VE, VES), VAR, CH, ME, _, _, _, _, _, ADS) -> Found)
	 Adapt(Id, ADS -> id(Id1))
	 (|
	   where(Id1 -> id_op(Id2))
-- debug
-- Putmsg("Looking for ")
-- Print_id_or_op(Id)
-- print(CE)
-- Putmsg(" as an object")
	   Lookup_object_in_module(Id2, ME -> Oid)
	   (|
	     eq(Oid, nil)
-- Putmsg(" as a type")
	     Lookup_env(Id2, TYP -> Oid1)
	     (|
	       eq(Oid1, nil)
-- Putmsg(" as a variable")
	       Lookup_env_variable_id(Id2, nil, VAR -> Oid2)
	       (|
		 eq(Oid2, nil)
-- Putmsg(" as a channel")
		 Lookup_env_channel_id(Id2, CH -> Oid3)
		 (|
		   eq(Oid3, nil)
-- Putmsg(" as a value")
		   Lookup_id_or_op1(Id1, VE -> Ids)
		   (|
		     eq(Ids, nil)
		     where(FOUND'nil -> Found)
		   ||
		     where(found -> Found)
		   |)
		 ||
		   where(found -> Found)
		 |)
	       ||
		 where(found -> Found)
	       |)
	     ||
	       where(found -> Found)
	     |)
	   ||
	     where(found -> Found)
	   |)
-- debug
-- (| 
-- eq(Found, found)
-- Putmsg(": found")
-- ||
-- Putmsg(": not found")
-- |)
-- Putnl()
	 ||
	   Lookup_id_or_op1(Id1, VE -> Ids)
	   (|
	     eq(Ids, nil)
	     where(FOUND'nil -> Found)
	   ||
	     where(found -> Found)
	   |)
	 |)

  'rule' Find_id_or_op(P, Id, extend_env(CE1, CE2, _, ADS) -> Found):
	 Adapt(Id, ADS -> id(Id1))
	 Find_id_or_op(P, Id1, CE1 -> Found1)
	 (|
	   eq(Found1, nil)
	   Find_id_or_op(P, Id1, CE2 -> Found)
	 ||
	   where(found -> Found)
	 |)

  'rule' Find_id_or_op(P, Id, instantiation_env(PF, CE) -> Found):
	 Find_id_or_op(P, Id, CE -> Found)

-- otherwise catch initial Adapts returning nil (for hidden name)
  'rule' Find_id_or_op(P, Id, CE -> nil):

'action' Check_rename(POS)

  'rule' Check_rename(P):
	 Get_current_adapts( -> ADS)
	 Check_duplicate_renames(P, ADS -> ADS1)
	 Set_current_adapts(ADAPTS'nil)
 	 Check_all_renames_found(P, ADS1)
	 Set_current_adapts(ADS1)


'action' Check_duplicate_renames(POS, ADAPTS -> ADAPTS)

  'rule' Check_duplicate_renames(P, hide(Id, ADS) -> hide(Id, ADS1)):
	 Check_duplicate_renames(P, ADS -> ADS1)


  'rule' Check_duplicate_renames(P, rename(Nid, Oid, ADS) -> ADS1):
	 (|
	   New_is_in_renames(Nid, ADS)
	   Puterror(P)
	   Putmsg("New item ")
	   Print_id_or_op(Nid)
	   Putmsg(" duplicated: ignored")
	   Putnl()
	   Check_duplicate_renames(P, ADS -> ADS1)
	 ||
	   Old_is_in_renames(Oid, ADS)
	   Puterror(P)
	   Putmsg("Old item ")
	   Print_id_or_op(Oid)
	   Putmsg(" duplicated: ignored")
	   Putnl()
	   Check_duplicate_renames(P, ADS -> ADS1)
	 ||
	   Is_hidden(Oid, ADS)
	   Puterror(P)
	   Putmsg("Old item ")
	   Print_id_or_op(Oid)
	   Putmsg(" hidden: ignored")
	   Putnl()
	   Check_duplicate_renames(P, ADS -> ADS1)
	 ||
	   Check_duplicate_renames(P, ADS -> ADS2)
	   where(ADAPTS'rename(Nid,Oid,ADS2) -> ADS1)
	 |)

  'rule' Check_duplicate_renames(P, nil -> nil):

'condition' New_is_in_renames(ID_OR_OP, ADAPTS)

  'rule' New_is_in_renames(Id, rename(Nid, Oid, ADS)):
	 (| eq(Id, Nid) || New_is_in_renames(Id, ADS) |)

  'rule' New_is_in_renames(Id, hide(Id1, ADS)):
	 New_is_in_renames(Id, ADS)

'condition' Old_is_in_renames(ID_OR_OP, ADAPTS)

  'rule' Old_is_in_renames(Id, rename(Nid, Oid, ADS)):
	 (| eq(Id, Oid) || Old_is_in_renames(Id, ADS) |)

  'rule' Old_is_in_renames(Id, hide(Id1, ADS)):
	 Old_is_in_renames(Id, ADS)

'action' Check_all_renames_found(POS, ADAPTS)

  'rule' Check_all_renames_found(P, rename(Nid, Oid, ADS)):
	 Adapt(Oid, ADS -> id(Id1))
	 Get_current_env(-> CE)
	 Find_id_or_op(P, Id1, CE -> Found)
	 [|
	   ne(Found, found)
	   Puterror(P)
	   Putmsg("Renamed item ")
	   Print_id_or_op(Oid)
	   Putmsg(" not defined")
	   Putnl()
	 |]
	 Check_all_renames_found(P, ADS)

  'rule' Check_all_renames_found(P, hide(Id, ADS)):
	 Check_all_renames_found(P, ADS)

  'rule' Check_all_renames_found(P, nil):


--------------------------------------------------------------------------
-- Value declarations from variant, record, and union type defs
--------------------------------------------------------------------------

'action' Define_value_from_type_defs(TYPE_DEFS)

  'rule' Define_value_from_type_defs(list(D, DS)):
	 Define_value_from_type_def(D)
	 Define_value_from_type_defs(DS)

  'rule' Define_value_from_type_defs(nil):

'action' Define_value_from_type_def(TYPE_DEF)

  'rule' Define_value_from_type_def(abbrev(P, Id, _)):
	 Lookup_type_id(P, Id -> type_id(I))
	 Type_of(I -> T)
         where(T -> subtype(single(_, B, T1), restriction(_, E)))
	 id_to_string(Id -> S)
	 Concatenate("RSL_is_", S -> S1)
	 string_to_id(S1 -> Id1)
	 Define_id_or_op(P, id_op(Id1), fun(T1,total,result(bool,nil,nil,nil,nil)) -> value_id(I1))
	 I'Qualifier -> Q
	 I1'Qualifier <- Q
	 I1'Def <- expl_fun(list(form_parm(P,list(B,nil)),nil), E, nil, nil, nil, nil)
	 I'Subtype <- funct(I1)

  'rule' Define_value_from_type_def(variant(P, Id, VARS)):
	 Lookup_type_id(P, Id -> type_id(I))
	 Type_of(I -> T)
	 (|
	   -- identify variants of form a | b(...)
	   -- when " ~= a" can be used as precondition
	   -- of destructors and reconstructors of b
	   where(VARS -> VARIANTS'list(V1, list(V2, nil)))
	   (|
	     where(V1 -> record(_, constructor(_, CId), nil))
	     where(V2 -> record(_, _, list(_,_)))
	     where(VARS -> VARS1)
	     where(CONSTANT_CONSTRUCTOR'cons(CId) -> Ccid)
	   ||
	     where(V2 -> record(_, constructor(_, CId), nil))
	     where(V1 -> record(_, _, list(_,_)))
	     where(VARIANTS'list(V2, list(V1, nil)) -> VARS1)
	     where(CONSTANT_CONSTRUCTOR'cons(CId) -> Ccid)
	   ||
	     where(VARS -> VARS1)
	     where(CONSTANT_CONSTRUCTOR'nil -> Ccid)
           |)
	 ||
	   where(VARS -> VARS1)
	   where(CONSTANT_CONSTRUCTOR'nil -> Ccid)
	 |)
	 Define_value_variants(T, total, VARS1, Ccid)

  'rule' Define_value_from_type_def(record(P, Id, COMPS)):
	 Lookup_type_id(P, Id -> type_id(I))
	 Type_of(I -> T)
	 id_to_string(Id -> S)
	 Make_mk_name(S -> S1)
	 string_to_id(S1 -> Id1)
	 Collect_components_type(COMPS -> DS)
	 (|
	   where(DS -> list(D, nil))
	 ||
	   where(TYPE_EXPR'product(DS) -> D)
	 |)
	 Define_id_or_op(P, id_op(Id1), fun(D,total,result(T,nil,nil,nil,nil)) -> value_id(I1))
	 Define_value_components(T, value_id(I1), total, COMPS, DS, nil)

  'rule' Define_value_from_type_def(union(P, Id, CHS)):
	 Check_distinguishable(CHS)
	 Lookup_type_id(P, Id -> type_id(I))
	 Check_non_circular(I, CHS)
	 Type_of(I -> T)
	 Define_value_choices(I, Id, T, CHS)

  'rule' Define_value_from_type_def(D):

'action' Define_value_variants(TYPE_EXPR, FUNCTION_ARROW, VARIANTS, CONSTANT_CONSTRUCTOR)

  'rule' Define_value_variants(T, ARR, list(V,nil), Ccid):
	 Define_value_variant(T, ARR, V, Ccid -> _)

  'rule' Define_value_variants(T, ARR, list(V,VS), Ccid):
	 Define_value_variant(T, partial, V, Ccid -> Ccid1)
	 Define_value_variants(T, partial, VS, Ccid1)

'action' Define_value_variant(TYPE_EXPR, FUNCTION_ARROW, VARIANT, CONSTANT_CONSTRUCTOR -> CONSTANT_CONSTRUCTOR)

  'rule' Define_value_variant(T, ARR, record(P, Cons, nil), Ccid -> Ccid1):
	 (|
	   where(Cons -> constructor(P1, Id_or_op))
	   Define_id_or_op(P1, Id_or_op, T -> value_id(I))
	   where(Ccid -> cons(Id_or_op1))
	   Equal_id_or_op(Id_or_op, Id_or_op1)
	   where(cons_id(I) -> Ccid1)
	 ||
	   where(Ccid -> Ccid1)
	 |)

  'rule' Define_value_variant(T, ARR, record(P, Cons, Comps), Ccid -> Ccid):
	 Collect_components_type(Comps -> DS)
	 (|
	   where(DS -> list(D, nil))
	 ||
	   where(TYPE_EXPR'product(DS) -> D)
	 |)
	 (|
	   where(Cons -> constructor(P1, Id))
	   Define_id_or_op(P1, Id, fun(D,total,result(T,nil,nil,nil,nil)) -> Oid)
	 ||
	   where(OPT_VALUE_ID'nil -> Oid)
	 |)
	 Define_value_components(T, Oid, ARR, Comps, DS, Ccid)


'action' Define_value_components(TYPE_EXPR, OPT_VALUE_ID,
FUNCTION_ARROW, COMPONENTS, PRODUCT_TYPE, CONSTANT_CONSTRUCTOR)

  'rule' Define_value_components(T, Oid, ARR, Comps, DS, Ccid)
	 DefaultPos(-> P)
	 Make_x_ids(P, 1, DS -> Ids)
	 Define_value_components1(T, Oid, ARR, Comps, DS, 1, Ids, Ccid)
	 
'action' Define_value_components1(TYPE_EXPR, OPT_VALUE_ID,
FUNCTION_ARROW, COMPONENTS, PRODUCT_TYPE, INT, Value_ids, CONSTANT_CONSTRUCTOR)

  'rule' Define_value_components1(T, Oid, ARR, list(C,CS), list(T1, TS1), J, Ids, Ccid):
	 Define_value_component(T, Oid, ARR, C, T1, J, Ids, Ccid)	 
	 Define_value_components1(T, Oid, ARR, CS, TS1, J+1, Ids, Ccid)

  'rule' Define_value_components1(_, _, _, nil, _, _, _, _):

'action' Define_value_component(TYPE_EXPR, OPT_VALUE_ID, FUNCTION_ARROW, COMPONENT, TYPE_EXPR, INT, Value_ids, CONSTANT_CONSTRUCTOR)

  'rule' Define_value_component(T, Oid, ARR, component(P, D, _, R), T1, J, Ids, Ccid):
	 [|
	   (|
	     where(D -> destructor(P1, Id_or_op))
	   ||
	     -- CWG 12/4/08 add missing destructors for SAL
	     SALWanted()
	     where(Oid -> value_id(I))
	     I'Ident -> id_op(Id)
	     id_to_string(Id -> Idstr)
	     Int_to_string(J -> S)
	     Concatenate3(Idstr, "_acc_", S -> S1)
	     Concatenate(S1, "_" -> S2)
	     where(P -> P1)
	     string_to_id(S2 -> AccId)
	     where(id_op(AccId) -> Id_or_op)
	   |)
	   Define_id_or_op(P1, Id_or_op, fun(T, ARR, result(T1,nil,nil,nil,nil)) -> ODid)
	   [|
	     where(Oid -> value_id(I))
	     where(ODid -> value_id(Did))
	     Make_destructor_definition(I, J, Ids, ARR, Ccid -> DEF)
	     Did'Def <- DEF
	   |]
	 |]
	 [|
	   where(R -> reconstructor(P1, Id_or_op))
	   Define_id_or_op(P1, Id_or_op, fun(product(list(T1,list(T,nil))), ARR, result(T,nil,nil,nil,nil)) -> ORid)
	   [|
	     where(Oid -> value_id(I))
	     where(ORid -> value_id(Rid))
	     Make_reconstructor_definition(I, J, Ids, ARR, T1, Ccid -> DEF)
	     Rid'Def <- DEF
	   |]
	 |]

'action' Collect_components_type(COMPONENTS -> PRODUCT_TYPE)

  'rule' Collect_components_type(list(component(_, _, T, _), CS) -> list(T1, TS)):
	 Check_type_defined(T -> T1)
	 Collect_components_type(CS -> TS)

  'rule' Collect_components_type(nil -> nil):

'action' Make_x_ids(POS, INT, PRODUCT_TYPE -> Value_ids)

  'rule' Make_x_ids(_, _, nil -> nil):

  'rule' Make_x_ids(P, J, list(T, TS) -> list(I, Ids)):
	 Make_concatenation("x", J -> S)
         string_to_id(S -> Id)
	 New_value_id(P, id_op(Id) -> I)
	 I'Type <- T
	 Make_x_ids(P, J+1, TS -> Ids)

'action' Check_distinguishable(CHOICES)

  'rule' Check_distinguishable(list(nil, CHS)):
	 Check_distinguishable(CHS)

  'rule' Check_distinguishable(list(choice(P,N), CHS)):
	 [| -- allow for name not to be found (error reported already)
	   Lookup_type_name(N -> type_id(I))
	   Type_of(I -> T)
	   Check_distinguishable1(I, T, CHS)
	 |]
	 Check_distinguishable(CHS)

  'rule' Check_distinguishable(nil):

'action' Check_distinguishable1(Type_id, TYPE_EXPR, CHOICES)

  'rule' Check_distinguishable1(I, T, list(nil, CHS)):
	 Check_distinguishable1(I, T, CHS)

  'rule' Check_distinguishable1(I, T, list(choice(P,N), CHS)):
	 Lookup_type_name(N -> type_id(I1))
	 Type_of(I1 -> T1)
	 [|
	   Match(T, nil, T1)
	   Puterror(P)
	   Putmsg("Types of ")
	   I'Ident -> Id
	   I'Qualifier -> Q
	   Print_qualifier(Q)
	   Print_id(Id)
	   Putmsg(" and ")
	   I1'Ident -> Id1
	   I1'Qualifier -> Q1
	   Print_qualifier(Q1)
	   Print_id(Id1)
	   Putmsg(" are not distinguishable")
	   Putnl()
	 |]
	 Check_distinguishable1(I, T, CHS)

  'rule' Check_distinguishable1(I, T, nil):

'action' Check_non_circular(Type_id, CHOICES)

  'rule' Check_non_circular(I, list(choice(_, N), CHS)):
	 Lookup_type_name(N -> type_id(I1))
	 [|
	   Reachable(list(I, nil), I1)
	   I'Pos -> P1
	   I'Ident -> Id
	   Puterror(P1)
	   Putmsg("Type ")
	   Print_id(Id)
	   Putmsg(" is involved in a circularity through union component ")
	   I1'Ident -> Id1
	   Print_id(Id1)
	   Putnl()
	     -- remove coercions and definitions to avoid
             -- circularities in unification
	   I'Coercions_down <- nil
	   I1'Coercions_up <- nil
	   I1'Type <- abbrev(none)
	   I'Type <- abbrev(none)
	 |]
	 Check_non_circular(I, CHS)

  'rule' Check_non_circular(I, list(nil, CHS)):
	 Check_non_circular(I, CHS)

  'rule' Check_non_circular(_, nil):

'condition' Reachable(Type_ids, Type_id)
-- succeeds if any id in the first parameter is reachable from the
-- second:
-- (a) present directly
-- (b) through a union definition
-- (c) through an abbreviation
  'rule' Reachable(Is, I):
	 Isin_type_ids(I, Is)

  'rule' Reachable(Is, I):
	 I'Type -> abbrev(T)
	 Reachable_from_type(list(I,Is), T)

  'rule' Reachable(Is, I):
	 I'Type -> sort(S)
	 where(S -> union(CS))
	 Reachable_from_choices(list(I,Is), CS) 

'condition' Isin_type_ids(Type_id, Type_ids)

  'rule' Isin_type_ids(I1, list(I, Is)):
	 (| eq(I1, I) || Isin_type_ids(I1, Is) |)

'condition' Reachable_from_type(Type_ids, TYPE_EXPR)

  'rule' Reachable_from_type(Is, defined(I, _)):
	 Reachable(Is, I)

  'rule' Reachable_from_type(Is, named_type(N)):
	 Lookup_type_name(N -> type_id(I))
	 Reachable(Is, I)

  'rule' Reachable_from_type(Is, subtype(single(_,_,T), _)):
	 Reachable_from_type(Is, T)

  'rule' Reachable_from_type(Is, bracket(T)):
	 Reachable_from_type(Is, T)

'condition' Reachable_from_choices(Type_ids, CHOICES)

  'rule' Reachable_from_choices(Is, list(C, CS))
	 where(C -> choice(_, N))
	 Lookup_type_name(N -> type_id(I))
	 (|
	   Reachable(Is, I)
	 ||
	   Reachable_from_choices(list(I,Is), CS)
	 |)


'action' Define_value_choices(Type_id, IDENT, TYPE_EXPR, CHOICES)

  'rule' Define_value_choices(I, Id, T, list(CH, CHS)):
	 Define_value_choice(I, Id, T, CH)
	 Define_value_choices(I, Id, T, CHS)

  'rule' Define_value_choices(I, Id, T, nil):

'action' Define_value_choice(Type_id, IDENT, TYPE_EXPR, CHOICE)

  'rule' Define_value_choice(I, Id, T, choice(P,N)):
	 Lookup_type_name(N -> type_id(I1))
	 ne(I,I1)
	 Type_of(I1 -> T1)
	 id_to_string(Id -> S)
	 I1'Ident -> Id1
	 id_to_string(Id1 -> S1)
	 Make_from_name(S, S1 -> From)
	 string_to_id(From -> Fid)
	 Make_to_name(S, S1 -> To)
	 string_to_id(To -> Tid)
	 Define_id_or_op(P, id_op(Fid), fun(T1, total, result(T,nil,nil,nil,nil)) -> value_id(FI))
	 Define_id_or_op(P, id_op(Tid), fun(T, partial, result(T1,nil,nil,nil,nil)) -> value_id(TI))
	 Make_x_ids(P, 1, list(T1, nil) -> Ids)
	 Make_destructor_definition(FI, 1, Ids, partial, nil -> Def)
	 TI'Def <- Def
	 I1'Coercions_up -> CS1
	 Remove_coercion(I, CS1 -> CS2)
	 Extend_coercion(coercion(I,nil), up -> CS3)
	 Concat_coercions(CS2, CS3, up -> CS4)
	 I1'Coercions_up <- CS4
-- debug
-- Putmsg("Coercions up for ")
-- Print_id(Id1)
-- Putnl()
-- Print_coercions(CS4)
	 I'Coercions_down -> CS5
	 Remove_coercion(I1, CS5 -> CS6)
	 Extend_coercion(coercion(I1,nil), down -> CS7)
	 Concat_coercions(CS6, CS7, down -> CS8)
	 I'Coercions_down <- CS8
-- debug
-- Putmsg("Coercions down for ")
-- Print_id(Id)
-- Putnl()
-- Print_coercions(CS8)

  'rule' Define_value_choice(I, Id, T, choice(P,N)):
	 -- type name N undefined or immediately circular
	 -- reported earlier

  'rule' Define_value_choice(I, Id, T, nil):

'action' Remove_coercion(Type_id, COERCIONS -> COERCIONS)

  'rule' Remove_coercion(I, coercions(coercion(I1,C),CS) -> CS2):
	 (|
	   eq(I,I1)
	   where(CS -> CS2)
	 ||
	   Remove_coercion(I, CS -> CS1)
	   where(coercions(coercion(I1,C),CS1) -> CS2) 
	 |)

  'rule' Remove_coercion(I, nil -> nil)

'action' Extend_coercions(COERCIONS, DIRECTION -> COERCIONS)

  'rule' Extend_coercions(coercions(C, CS), Dir -> CS3)
	 Extend_coercion(C, Dir -> CS1)
	 Extend_coercions(CS, Dir -> CS2)
	 Concat_coercions(CS1, CS2, Dir -> CS3)

  'rule' Extend_coercions(nil, Dir -> nil):

'action' Extend_coercion(COERCION, DIRECTION -> COERCIONS)

-- ignore all but first element and build complete
-- since don't know if this node is yet complete

  'rule' Extend_coercion(coercion(I,C), Dir -> CS3)
	 (|
	   eq(Dir,up)
	   I'Coercions_up -> CS1
	 ||
	   I'Coercions_down -> CS1
	 |)
	 (|
	   eq(CS1,nil)
	   where(coercions(coercion(I,C),nil) -> CS3)
	 ||
	   Extend_coercions(CS1, Dir -> CS2)
	   Prefix_coercions(I, CS2, Dir -> CS3)
	 |)

'action' Prefix_coercions(Type_id, COERCIONS, DIRECTION -> COERCIONS)

  'rule' Prefix_coercions(I, coercions(C, CS), Dir -> coercions(C1, CS1)):
	 Prefix_coercion(I, C, Dir -> C1)
	 Prefix_coercions(I, CS, Dir -> CS1)

  'rule' Prefix_coercions(I, nil, Dir -> nil):

'action' Prefix_coercion(Type_id, COERCION, DIRECTION -> COERCION)

  'rule' Prefix_coercion(I, C, Dir -> C1)
	 (|
	   Is_in_coercion(I, C)
	   [|
	     eq(Dir, up)
	     I'Pos -> P
	     Puterror(P)
	     I'Ident -> Id
	     Putmsg("Circular union type ")
	     Print_id(Id)
	     Putnl()
	   |]
	   where(C -> C1)
	 ||
	   where(coercion(I,C) -> C1)
	 |)

'condition' Is_in_coercion(Type_id, COERCION)

  'rule' Is_in_coercion(I, coercion(I1, C)):
	 (| eq(I, I1) || Is_in_coercion(I, C) |)

'condition' Is_in_coercions(Type_id, COERCIONS)

  'rule' Is_in_coercions(I, coercions(C, CS)):
	 (| Is_in_coercion(I, C) || Is_in_coercions(I, CS) |)

'action' Concat_coercions(COERCIONS, COERCIONS, DIRECTION -> COERCIONS)

  'rule' Concat_coercions(coercions(C,CS), CS2, Dir -> CS3):
	 (|
	   Overlap(C, CS2)
	   where(C -> coercion(I,C1))
	   I'Pos -> P
	   I'Ident -> Id
	   Puterror(P)
	   (|
	     eq(Dir,up)
	     Putmsg("Upward")
	   ||
	     Putmsg("Downward")
	   |)
	   Putmsg(" coercion for type ")
	   Print_id(Id)
	   Putmsg(" is ambiguous")
	   Putnl()
	   Concat_coercions(CS, CS2, Dir -> CS3)
	 ||
	   Concat_coercions(CS, CS2, Dir -> CS4)
	   where(coercions(C, CS4) -> CS3)
	 |)

  'rule' Concat_coercions(nil, CS, Dir -> CS)

'condition' Overlap(COERCION, COERCIONS)

  'rule' Overlap(C, coercions(C1, CS)):
	 (|
	   Lub_coercion(C, C1 -> Oid)
	   ne(Oid, nil)
	 ||
	   Overlap(C, CS)
	 |)

'action' Lub_coercions(COERCIONS, COERCIONS -> OPT_TYPE_ID)
-- we know that coercions in each set may have common prefixes, but
-- are then disjoint, so if a type appears in more than one it will
-- appear in the same place in all
-- So first found occurrence will do.

  'rule' Lub_coercions(coercions(C1, CS1), coercions(C2, CS2) -> Oid):
	 (|
	   Lub_coercion(C1, C2 -> type_id(I))
	   where(type_id(I) -> Oid)
	 ||
	   Lub_coercions(coercions(C1, CS1), CS2 -> type_id(I))
	   where(type_id(I) -> Oid)
	 ||
	   Lub_coercions(CS1, coercions(C2, CS2) -> Oid) 
	 |)

  'rule' Lub_coercions(nil, CS -> nil):

  'rule' Lub_coercions(CS, nil -> nil):

'action' Lub_coercion(COERCION, COERCION -> OPT_TYPE_ID)

-- returns first Type_id in both coercions

  'rule' Lub_coercion(coercion(I, C), C2 -> Oid):
	 (|
	   Is_in_coercion(I, C2)
	   where(type_id(I) -> Oid)
	 ||
	   Lub_coercion(C, C2 -> Oid)
	 |)

  'rule' Lub_coercion(nil, C -> nil)

--------------------------------------------------------------------------
-- Axiom declarations from variant, record, and union type defs
--------------------------------------------------------------------------

'action' Define_axiom_from_type_defs(TYPE_DEFS)

  'rule' Define_axiom_from_type_defs(list(D, DS)):
	 Define_axiom_from_type_def(D)
	 Define_axiom_from_type_defs(DS)

  'rule' Define_axiom_from_type_defs(nil):

'action' Define_axiom_from_type_def(TYPE_DEF)

  'rule' Define_axiom_from_type_def(variant(P, Id, VARS)):
	 Lookup_type_id(P, Id -> type_id(I))
	 Type_of(I -> T)
	 Make_x_idents(1, VARS -> Ids)
	 Make_variant_types(VARS -> TS)
	 Zip_to_typings(P, Ids, TS -> TPS)
	 Get_current_axioms(-> AXS)
	 id_to_string(Id -> S)
	 Make_disjointness_name(S -> S1)
	 string_to_id(S1 -> Diff_id)
	 New_axiom_id(P, ident(Diff_id) -> I1)
	 Make_disjointness_axiom(P, Ids, TS, VARS -> E111)
	 (|
	   eq(TPS, nil)
	   where(E111 -> E11)
	 ||
	   where(quantified(P, all, TPS, restriction(P, E111)) -> E11)
	 |)
	 Resolve(E11, bool -> E12)
	 Simplify(E12 -> E1)
	 I1'Axiom <- E1
-- debug
-- Print_expr(E1)
-- Putnl()
	 (|
	   Has_wildcard_constructor(VARS)
	   Set_current_axioms(axiom_env(I1,AXS))
	 ||
	   -- avoid second axiom having same position as first
	   -- (else causes problems in emacs compile mode)
	   where(VARS -> list(record(P1, _, _), _))
	   Make_induction_name(S -> S2)
	   string_to_id(S2 -> Ind_id)
	   New_axiom_id(P1, ident(Ind_id) -> I2)
	   string_to_id("p_" -> Pid)
	   where(TYPINGS'list(single(P, single(P, id_op(Pid)),
				  fun(T, total, result(bool,nil,nil,nil,nil))),
			      nil) -> PTPS)
	   where(named_val(P, name(P, id_op(Pid))) -> Papp)
	   Induction_conditions(P, I, Papp, VARS -> Ic)
	   string_to_id("x_" -> Xid)
	   where(TYPINGS'list(single(P, single(P, id_op(Xid)), T), nil) -> XTPS)
	   where(named_val(P, name(P, id_op(Xid))) -> X)
	   where(ACTUAL_FUNCTION_PARAMETERS'list(fun_arg(P, list(X,nil)), nil) -> Xargs)
	   where(quantified(P, all, XTPS,
			    restriction(P, application(P, Papp, Xargs))) -> Res)
	   where(ax_infix(P, Ic, implies, Res, P) -> E21)
	   where(quantified(P, all, PTPS, restriction(P, E21)) -> E22)
	   Resolve(E22, bool -> E23)
	   Simplify(E23 -> E2)
	   I2'Axiom <- E2
-- debug
-- Print_expr(E2)
-- Putnl()
	   Set_current_axioms(axiom_env(I1,axiom_env(I2,AXS)))
	 |)

  'rule' Define_axiom_from_type_def(record(P, Id, Comps)):
	 id_to_string(Id -> S)
	 Make_mk_name(S -> MKS)
	 string_to_id(MKS -> Mkid)
	 where(VARIANT'record(P, constructor(P, id_op(Mkid)), Comps) -> R)
	 Define_axiom_from_type_def(variant(P, Id, list(R, nil)))

  'rule' Define_axiom_from_type_def(union(P, Id, CHS)):
	 id_to_string(Id -> S)
	 Choices_to_variants(P, S, CHS -> VARS)
	 Define_axiom_from_type_def(variant(P, Id, VARS)) 

--otherwise nothing to do
  'rule' Define_axiom_from_type_def(_):

'action' Make_x_idents(INT, VARIANTS -> IDENTS)

  'rule' Make_x_idents(J, list(H, T) -> list(Id, Ids)):
	 Make_concatenation("x", J -> S)
         string_to_id(S -> Id)
	 Make_x_idents(J+1, T -> Ids)

  'rule' Make_x_idents(_, nil -> nil):

'action' Make_variant_types(VARIANTS -> PRODUCT_TYPE)

  'rule' Make_variant_types(list(record(P, _, nil), VARS) -> list(none, TS)):
	 Make_variant_types(VARS -> TS)

  'rule' Make_variant_types(list(record(P, wildcard, _), VARS) -> list(none, TS)):
	 Make_variant_types(VARS -> TS)

  'rule' Make_variant_types(list(record(P, _, Comps), VARS) -> list(T, TS)): 
	 Collect_components_type(Comps -> CTS)
	 (|
	   where(CTS -> list(T, nil))
	 ||
	   where(TYPE_EXPR'product(CTS) -> T)
	 |)
	 Make_variant_types(VARS -> TS)

  'rule' Make_variant_types(nil -> nil):

'condition' Has_wildcard_constructor(VARIANTS)

  'rule' Has_wildcard_constructor(list(record(_, C, _), VARS)):
	 (|
	   eq(C, wildcard)
	 ||
	   Has_wildcard_constructor(VARS)
	 |)

'action' Zip_to_typings(POS, IDENTS, PRODUCT_TYPE -> TYPINGS)

  'rule' Zip_to_typings(P, list(Id, Ids), list(none, TS) -> TPS):
	 Zip_to_typings(P, Ids, TS -> TPS)

  'rule' Zip_to_typings(P, list(Id, Ids), list(T, TS) -> list(single(P, single(P, id_op(Id)), T), TPS)):
	 Zip_to_typings(P, Ids, TS -> TPS)

  'rule' Zip_to_typings(_, nil, _ -> nil):


'action' Make_disjointness_axiom(POS, IDENTS, PRODUCT_TYPE, VARIANTS -> VALUE_EXPR)

  'rule' Make_disjointness_axiom(P, list(_, Ids), list(_, TS), list(record(_, wildcard, _), VARS) -> E):
	 Make_disjointness_axiom(P, Ids, TS, VARS -> E)

  'rule' Make_disjointness_axiom(P, list(Id, Ids), list(T, TS),
  list(record(_, constructor(_,Cid), _), VARS) -> ax_infix(P, E1, and, E2, P)):
	 where(named_val(P, name(P, Cid)) -> Cons)
	 (|
	   eq(T, none)
	   where(Cons -> E)
	 ||
	   where(ACTUAL_FUNCTION_PARAMETERS'list(fun_arg(P, list(named_val(P, name(P, id_op(Id))), nil)), nil) -> Args)
	   where(application(P, Cons, Args) -> E) 
	 |)
	 Make_disjointness_axiom1(P, E, Ids, TS, VARS -> E1)
	 Make_disjointness_axiom(P, Ids, TS, VARS -> E2)

  'rule' Make_disjointness_axiom(P, nil, _, _ -> literal_expr(P, bool_true))

'action' Make_disjointness_axiom1(POS, VALUE_EXPR, IDENTS, PRODUCT_TYPE, VARIANTS -> VALUE_EXPR)

  'rule' Make_disjointness_axiom1(P, E, list(_, Ids), list(_, TS), list(record(_, wildcard, _), VARS) -> E1):
	 Make_disjointness_axiom1(P, E, Ids, TS, VARS -> E1)

  'rule' Make_disjointness_axiom1(P, L, list(Id, Ids), list(T, TS),
  list(record(_, constructor(_,Cid), _), VARS) -> ax_infix(P, E1, and, E2, P)):
	 where(named_val(P, name(P, Cid)) -> Cons)
	 (|
	   eq(T, none)
	   where(Cons -> R)
	 ||
	   where(ACTUAL_FUNCTION_PARAMETERS'list(fun_arg(P, list(named_val(P, name(P, id_op(Id))), nil)), nil) -> Args)
	   where(application(P, Cons, Args) -> R) 
	 |)
	 where(val_infix(P, L, neq, R) -> E1)
	 Make_disjointness_axiom1(P, L, Ids, TS, VARS -> E2)

  'rule' Make_disjointness_axiom1(P, _, nil, _, _ -> literal_expr(P, bool_true)):


'action' Induction_conditions(POS, Type_id, VALUE_EXPR, VARIANTS -> VALUE_EXPR)

  'rule' Induction_conditions(P, TI, Papp, list(record(_, constructor(_, Id), nil), VARS) -> ax_infix(P, E1, and, E2, P)):
	 where(application(P, Papp, list(fun_arg(P, list(named_val(P, name(P, Id)),nil)), nil)) -> E1)
	 Induction_conditions(P, TI, Papp, VARS -> E2)

  'rule' Induction_conditions(P, TI, Papp, list(record(_, constructor(_, Id), Comps), VARS) -> ax_infix(P, E1, and, E2, P)):
	 Induction_condition(P, TI, Papp, Id, Comps -> E1)
	 Induction_conditions(P, TI, Papp, VARS -> E2)

  'rule' Induction_conditions(P, _, _, nil -> literal_expr(P, bool_true)):

'action' Induction_condition(POS, Type_id, VALUE_EXPR, ID_OR_OP, COMPONENTS -> VALUE_EXPR)

  'rule' Induction_condition(P, TI, Papp, Id, Comps -> E):
	 Make_x_comp_idents(1, Comps -> Ids)
	 Collect_components_type(Comps -> CTS)
	 Zip_to_typings(P, Ids, CTS -> TPS)
	 Idents_to_exprs(P, Ids -> ES)
	 Make_assumptions(P, TI, Papp, ES, CTS -> L)
	 where(application(P, named_val(P, name(P, Id)), list(fun_arg(P, ES),nil)) -> App1)
	 where(application(P, Papp, list(fun_arg(P, list(App1,nil)),nil)) -> App)
	 where(quantified(P, all, TPS, restriction(P, ax_infix(P, L, implies, App, P))) -> E)

'action' Make_x_comp_idents(INT, COMPONENTS -> IDENTS)

  'rule' Make_x_comp_idents(J, list(H, T) -> list(Id, Ids)):
	 Make_concatenation("x", J -> S)
         string_to_id(S -> Id)
	 Make_x_comp_idents(J+1, T -> Ids)

  'rule' Make_x_comp_idents(_, nil -> nil):


'action' Make_assumptions(POS, Type_id, VALUE_EXPR, VALUE_EXPRS, PRODUCT_TYPE -> VALUE_EXPR)

  'rule' Make_assumptions(P, TI, Papp, list(X, XS), list(T, TS) -> E):
	 Make_assumptions(P, TI, Papp, XS, TS -> E2)
         -- only detects immediate recursion, not, e.g., within a product
	 -- also does not deal with mutual recursion 
	 (|
	   Same_type(defined(TI, nil), T, imp_fit(nil,nil,nil,nil,nil))
	   where(application(P, Papp, list(fun_arg(P, list(X,nil)),nil)) -> E1)
	   where(ax_infix(P, E1, and, E2, P) -> E)
	 ||
	   where(E2 -> E)
	 |)

  'rule' Make_assumptions(P, _, _, nil, _ -> literal_expr(P, bool_true)):

'action' Idents_to_exprs(POS, IDENTS -> VALUE_EXPRS)

  'rule' Idents_to_exprs(P, list(Id, Ids) -> list(named_val(P, name(P, id_op(Id))), ES)):
	 Idents_to_exprs(P, Ids -> ES)

  'rule' Idents_to_exprs(_, nil -> nil):

'action' Choices_to_variants(POS, STRING, CHOICES -> VARIANTS)

  'rule' Choices_to_variants(P, S, list(CH, CHS) -> list(V, VS)):
	 Choice_to_variant(P, S, CH -> V)
	 Choices_to_variants(P, S, CHS -> VS)

  'rule' Choices_to_variants(_, _, nil -> nil):

'action' Choice_to_variant(POS, STRING, CHOICE -> VARIANT)

  'rule' Choice_to_variant(P, _, nil -> record(P, wildcard, nil)):

  'rule' Choice_to_variant(P, S, choice(_, N) -> record(P, Cons, list(Comp,nil))):
	 Lookup_type_name(N -> type_id(I1))
	 Type_of(I1 -> T1)
	 I1'Ident -> Id1
	 id_to_string(Id1 -> S1)
	 Make_from_name(S, S1 -> From)
	 string_to_id(From -> Fid)
	 Make_to_name(S, S1 -> To)
	 string_to_id(To -> Tid)
	 where(constructor(P, id_op(Fid)) -> Cons)
	 where(component(P, destructor(P, id_op(Tid)), T1, nil) -> Comp)
  



----------------------------------------------------------------
-- Object definitions
----------------------------------------------------------------

'action' Define_value_object_defs(OBJECT_DEFS)

  'rule' Define_value_object_defs(list(H,T)):
	 Define_value_object_def(H)
	 Define_value_object_defs(T)

  'rule' Define_value_object_defs(nil):

'action' Define_value_object_def(OBJECT_DEF)

  'rule' Define_value_object_def(odef(P, Id, TS, CL)):
	 [| -- hidden or missing object reported earlier
	    -- in Make_object_type_env_def
	   Get_current_modules(-> ME)
	   Lookup_object_in_module(Id, ME -> object_id(I))
	   Current -> C
	   I'Env -> CE
	   Get_current_with(-> W)
	   Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,W,nil),C)
	   Extend_paths -> Paths
	   Extend_paths <- list(nil,Paths)
	   [|
	     ne(TS, nil)
	     Make_single_typing(TS -> TP)
	     Define_value_typing(TP)
-- debug
-- Print_typing(TP)
-- Putnl()
	     where(TP -> single(_,_,T))
-- moved to Complete_type_env
--	     I'Params <- param_type(T)
	   |]
	   Current -> current_env(PCE, C1)
	   I'Param_env <- PCE
	   Current <- current_env(CE,current_env(PCE, C1))
	   Extend_paths -> Paths1
	   Extend_paths <- list(nil,Paths1)
	   Make_value_env(CL)
	   Extend_paths <- Paths
	   Current -> current_env(CE1,current_env(PCE1, C2))
	   I'Env <- CE1
	   Current <- C2
	 |]  

'action' Make_single_typing(TYPINGS -> TYPING)

  'rule' Make_single_typing(list(single(P,B,T),nil) -> single(P,B,T)):

  'rule' Make_single_typing(list(multiple(P,BS,T),nil) -> single(P,product(P,BS),product(TS))):
	 Multiply_type(BS, T -> TS)

  'rule' Make_single_typing(TS -> single(P, B, T)):
	 (| where(TS -> list(single(P,_,_),_))
	 || where(TS -> list(multiple(P,_,_),_)) |)
	 Make_product_binding(TS -> B)
	 Make_product_type_from_typings(TS -> T)

'action' Make_product_binding(TYPINGS -> BINDING)

  'rule' Make_product_binding(list(single(P,B,T), nil) -> product(P, list(B, nil))):

  'rule' Make_product_binding(list(single(P,B,T), TS) -> product(P, list(B, BS))):
	 Make_product_binding(TS -> product(P1, BS))

  'rule' Make_product_binding(list(multiple(P, BS, T),nil) -> product(P, list(product(P,BS),nil))):

  'rule' Make_product_binding(list(multiple(P, BS, T),TS) -> product(P, list(product(P, BS), BS1))):
	 Make_product_binding(TS -> product(P1, BS1))

'action' Make_product_type_from_typings(TYPINGS -> TYPE_EXPR)

  'rule' Make_product_type_from_typings(list(single(P,B,T), nil) -> product(list(T,nil))):

  'rule' Make_product_type_from_typings(list(single(P,B,T), TS) -> product(list(T, TS1))):
	 Make_product_type_from_typings(TS -> product(TS1))

  'rule' Make_product_type_from_typings(list(multiple(P, BS, T),nil) -> product(list(product(TS),nil))):
	 Multiply_type(BS, T -> TS)

  'rule' Make_product_type_from_typings(list(multiple(P, BS, T),TS) -> product(list(product(TS1), TS2))):
	 Multiply_type(BS, T -> TS1)
	 Make_product_type_from_typings(TS -> product(TS2))

	 	 
'action' Multiply_type(BINDINGS, TYPE_EXPR -> PRODUCT_TYPE)

  'rule' Multiply_type(list(B, BS), T -> list(T, TS)):
	 Multiply_type(BS, T -> TS)

  'rule' Multiply_type(nil, T -> nil):

----------------------------------------------------------------
-- Variables
----------------------------------------------------------------


'action' Define_variable_defs(VARIABLE_DEFS)

  'rule' Define_variable_defs(list(D, DS)):
	 Define_variable_def(D)
	 Define_variable_defs(DS)

  'rule' Define_variable_defs(nil):

'action' Define_variable_def(VARIABLE_DEF)

  'rule' Define_variable_def(single(P, Id, T, E)):
	 Check_type_defined(T -> T1)
	 Define_variable_id(P, Id, T1)

  'rule' Define_variable_def(multiple(P, Ids, T)):
	 Check_type_defined(T -> T1)
	 Define_variable_ids(P, Ids, T1)

'action' Define_variable_ids(POS, IDENTS, TYPE_EXPR)

  'rule' Define_variable_ids(P, list(Id, Ids), T):
	 Define_variable_id(P, Id, T)
	 Define_variable_ids(P, Ids, T)  

  'rule' Define_variable_ids(P, nil, T):

'action' Define_variable_id(POS, IDENT, TYPE_EXPR)

  'rule' Define_variable_id(P, Id, T)
   --print(Id)
   --print("\n")
-- debug
-- Putmsg("Defining variable ")
-- Print_id(Id)
-- Putmsg(" with type ")
-- Print_type(T)
-- print(T)
	 Current -> C
	 Extend_paths -> Paths
	 [|
	   Lookup_current_value_name(name(P, id_op(Id)), C, Paths,
			             ownenv, ownclass -> list(_,_))
	   Puterror(P)
	   Putmsg("Value or variable ")
	   Print_id(Id)
	   Putmsg(" already defined")
	   Putnl()
	 |]
	 Get_current_variables(-> VARS)
-- debug         
--print("VArs")
--print(VARS)
	 Get_current_values(-> VES)
	 (|
	   Lookup_env_variable_id(Id, VES, VARS -> variable_id(I))
	   I'Type <- T
	 ||
	   Puterror(P)
	   Putmsg("Variable name ")
	   Print_id(Id)
	   Putmsg(" not visible")
	   Putnl()
	 |)
	 

----------------------------------------------------------------
-- Channels
----------------------------------------------------------------

'action' Define_channel_defs(CHANNEL_DEFS)

  'rule' Define_channel_defs(list(D, DS)):
	 Define_channel_def(D)
	 Define_channel_defs(DS)

  'rule' Define_channel_defs(nil):

'action' Define_channel_def(CHANNEL_DEF)

  'rule' Define_channel_def(single(P, Id, T)):
	 Check_type_defined(T -> T1)
	 Define_channel_id(P, Id, T1)

  'rule' Define_channel_def(multiple(P, Ids, T)):
	 Check_type_defined(T -> T1)
	 Define_channel_ids(P, Ids, T1)

'action' Define_channel_ids(POS, IDENTS, TYPE_EXPR)

  'rule' Define_channel_ids(P, list(Id, Ids), T):
	 Define_channel_id(P, Id, T)
	 Define_channel_ids(P, Ids, T)  

  'rule' Define_channel_ids(P, nil, T):

'action' Define_channel_id(POS, IDENT, TYPE_EXPR)

  'rule' Define_channel_id(P, Id, T)
	 Get_current_channels( -> CHS)
	 (|
	   Lookup_env_channel_id(Id, CHS -> channel_id(I))
	   I'Type <- T
	 ||
	   Puterror(P)
	   Putmsg("Channel name ")
	   Print_id(Id)
	   Putmsg(" not visible")
	   Putnl()
	 |)


----------------------------------------------------------------
-- Axioms
----------------------------------------------------------------

'action' Define_axiom_defs(AXIOM_DEFS)

  'rule' Define_axiom_defs(list(D, DS)):
	 Define_axiom_def(D)
	 Define_axiom_defs(DS)

  'rule' Define_axiom_defs(nil):

'action' Define_axiom_def(AXIOM_DEF)

  'rule' Define_axiom_def(axiom_def(P, Oid, E)):
	 Get_current_axioms(-> AXS)
	 New_axiom_id(P, Oid -> I)
	 [|
	   where(Oid -> ident(Id))
	   Is_defined_axiom(Id, AXS)
	   Puterror(P)
	   Putmsg("Axiom name ")
	   Print_id(Id)
	   Putmsg(" used twice")
	   Putnl()
	 |]
	 Set_current_axioms(axiom_env(I,AXS))

'condition' Is_defined_axiom(IDENT, AXIOM_ENV)

  'rule' Is_defined_axiom(Id, axiom_env(I,AXS)):
	 (|
	   I'Ident -> ident(Id1)
	   eq(Id, Id1)
	 ||
	   Is_defined_axiom(Id, AXS)
	 |)


----------------------------------------------------------------
-- Test_cases
----------------------------------------------------------------

'action' Define_test_case_defs(TEST_CASE_DEFS)

  'rule' Define_test_case_defs(list(D, DS)):
	 Define_test_case_def(D)
	 Define_test_case_defs(DS)

  'rule' Define_test_case_defs(nil):

'action' Define_test_case_def(TEST_CASE_DEF)

  'rule' Define_test_case_def(test_case_def(P, Oid, E)):
	 Get_current_test_cases(top -> TCS)
	 -- store extend paths so can be processed from top
	 Extend_paths -> Paths
	 New_test_case_id(P, Oid, Paths -> I)
	 [|
	   where(Oid -> ident(Id))
	   Is_defined_test_case(Id, TCS)
	   Puterror(P)
	   Putmsg("Test case name ")
	   Print_id(Id)
	   Putmsg(" used twice")
	   Putnl()
	 |]
	 Set_current_test_cases(test_case_env(I,TCS))

'condition' Is_defined_test_case(IDENT, TEST_CASE_ENV)

  'rule' Is_defined_test_case(Id, test_case_env(I,TCS)):
	 (|
	   I'Ident -> ident(Id1)
	   eq(Id, Id1)
	 ||
	   Is_defined_test_case(Id, TCS)
	 |)

----------------------------------------------------------------
-- Transition_systems (SAL)
----------------------------------------------------------------

'action' Define_trans_sys_defs(TRANSITION_SYS_DEFS)

  'rule' Define_trans_sys_defs(list(D, DS)):
	 Define_trans_sys_def(D)
	 Define_trans_sys_defs(DS)

  'rule' Define_trans_sys_defs(nil):

'action' Define_trans_sys_def(TRANSITION_SYS_DEF)

  'rule' Define_trans_sys_def(trans_sys_def(P, Id,Desc)):
	 Get_current_transition_systems(top -> TCS)
	 -- store extend paths so can be processed from top
	 Extend_paths -> Paths
	 New_transition_system_id(P, Id, Paths -> I)
	 I'System <- Desc
	 [|
	   Is_defined_trans_sys(Id, TCS)
	   Puterror(P)
	   Putmsg("Transition system name ")
	   Print_id(Id)
	   Putmsg(" used twice")
	   Putnl()
	 |]
	 Set_current_transition_system(trans_sys_env(I,TCS))

'condition' Is_defined_trans_sys(IDENT, TRANS_SYS_ENV)

  'rule' Is_defined_trans_sys(Id, trans_sys_env(I,TCS)):
	 (|
	   I'Ident -> Id1
	   eq(Id, Id1)
	 ||
	   Is_defined_trans_sys(Id, TCS)
	 |)

----------------------------------------------------------------
-- LTL properties:
----------------------------------------------------------------
'action' Define_property_defs(PROPERTY_DECLS)

  'rule' Define_property_defs(list(D, DS)):
	 Define_property_def(D)
	 Define_property_defs(DS)

  'rule' Define_property_defs(nil):

'action' Define_property_def(PROPERTY_DECL)

  'rule' Define_property_def(property_def(P, Id, _, _)):
	 Get_current_properties(top -> TCS)
	 -- store extend paths so can be processed from top
	 Extend_paths -> Paths
	 New_property_id(P, Id, Paths -> I)
	 [|
	   Is_defined_property(Id, TCS)
	   Puterror(P)
	   Putmsg("Property name ")
	   Print_id(Id)
	   Putmsg(" used twice")
	   Putnl()
	 |]
	 Set_current_property(prop_env(I,TCS))

'condition' Is_defined_property(IDENT, PROPERTY_ENV)

  'rule' Is_defined_property(Id, prop_env(I,TCS)):
	 (|
	   I'Ident -> Id1
	   eq(Id, Id1)
	 ||
	   Is_defined_property(Id, TCS)
	 |)

----------------------------------------------------------------
-- Type synthesis
----------------------------------------------------------------
'action' Make_results(VALUE_EXPR -> RESULTS)

  'rule' Make_results(literal_expr(P, L) -> RS):
	 Make_literal_results(L -> RS)

  'rule' Make_results(named_val(P, N) -> RS):
	 (|
	   Is_LTL_Wanted()
	   FDRWanted()
	   -- channel name can be used as a boolean variable
	   (| where(N -> name(_,id_op(Id))) ||
	      where(N -> qual_name(_,_,id_op(Id))) |)
	   Lookup_channel_name(N -> channel_id(I))
	   where(RESULTS'list(result(bool,nil,nil,nil,nil), nil) -> RS)
	 ||
	   (| where(N -> name(_,id_op(Id))) ||
	      where(N -> qual_name(_,_,id_op(Id))) |)
	   Lookup_variable_name(N -> variable_id(I))
	   I'Type -> T
	   where(RESULTS'list(result(T,list(variable(P,I,nil),nil),nil,nil,nil), nil) -> RS)
	 ||
	   Lookup_value_name(P, N -> Ids)
	   Make_pure_results(Ids -> RS)
	 |)

  'rule' Make_results(pre_name(P, N) -> list(R,nil)):
	 (|
	   Lookup_variable_name(N -> variable_id(I))
	   I'Type -> T
	   where(RESULT'result(T,list(variable(P,I,nil),nil),nil,nil,nil) -> R)
	 ||
	   Puterror(P)
	   Putmsg("Variable name ")
	   Print_name(N)
	   Putmsg(" hidden, renamed, or not defined")
	   Putnl()
	   where(RESULT'result(any,nil,nil,nil,nil) -> R)
	 |)

  'rule' Make_results(chaos(P) -> list(result(any,nil,nil,nil,nil),nil)):

  'rule' Make_results(skip(P) -> list(result(unit,nil,nil,nil,nil),nil)):

  'rule' Make_results(stop(P) -> list(result(any,nil,nil,nil,nil),nil)):

  'rule' Make_results(swap(P) -> list(result(any,nil,nil,nil,nil),nil)):

  'rule' Make_results(product(P, VS) -> RS):
	 Make_results_as_product(VS -> RS)

  'rule' Make_results(ranged_set(P,L,R) -> list(result(fin_set(int),RD,nil,nil,nil),nil)):
	 Make_results(L -> LRS)
	 Type_check(P, result(int,list(free,nil),nil,nil,nil), LRS -> LRS1)
	 Make_results(R -> RRS)
	 Type_check(P, result(int,list(free,nil),nil,nil,nil), RRS -> RRS1)
	 Merge_reads(LRS1, RRS1 -> RD)

  'rule' Make_results(enum_set(P, nil) -> list(result(fin_set(any),nil,nil,nil,nil),nil)):

  'rule' Make_results(enum_set(P, VS) -> RS):
	 Make_results_as_list(P, VS -> RS1)
	 Make_fin_set_results(RS1 -> RS)
	 Check_all_readonly(P, RS)

  'rule' Make_results(comp_set(P, V, set_limit(P1, TS, R)) -> RS4):
	 Type_check_typings(TS)
	 Openenv()
	 Define_value_typings(TS)
	 (|
	   where(R -> restriction(P2,V2))
	   Make_results(V2 -> RS2)
	   Type_check(P2, result(bool,list(free,nil),nil,nil,nil), RS2 -> RS21)
	   Get_reads(RS21 -> RD)
	 ||
	   where(ACCESSES'nil -> RD)
	 |)
	 Make_results(V -> RS1)
	 Make_infin_set_results(RS1 -> RS3)
	 Add_reads(RD, RS3 -> RS4)
	 Check_all_readonly(P, RS4)
	 Closeenv()

  'rule' Make_results(ranged_list(P,L,R) -> list(result(fin_list(int),RD,WR,IN,OUT),nil)):
	 Make_results(L -> LRS)
	 Type_check(P, result(int,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), LRS -> LRS1)
	 Make_results(R -> RRS)
	 Type_check(P, result(int,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RRS -> RRS1)
	 Merge_reads(LRS1, RRS1 -> RD)
	 Merge_writes(LRS1, RRS1 -> WR)
	 Merge_ins(LRS1, RRS1 -> IN)
	 Merge_outs(LRS1, RRS1 -> OUT)

  'rule' Make_results(enum_list(P, nil) -> list(result(fin_list(any),nil,nil,nil,nil),nil)):

  'rule' Make_results(enum_list(P, VS) -> RS):
	 Make_results_as_list(P, VS -> RS1)
	 Make_fin_list_results(RS1 -> RS)

  'rule' Make_results(comp_list(P, V, list_limit(P1, B, V1, R)) -> RS):
	 Make_unique_result(P1, V1 -> Res)
	 Check_readonly(P1, Res)
	 where(Res -> result(T,RD,_,_,_))
	 Make_list_element_type(P1, T -> T1)
	 Openenv()
	 Define_value_typing(single(P1, B, T1))
	 (|
	   where(R -> restriction(P2,V2))
	   Make_results(V2 -> RS2)
	   Type_check(P2, result(bool,list(free,nil),nil,nil,nil), RS2 -> RS21)
	   Get_reads(RS21 -> RD2)
	   Concat_accs(RD, RD2 -> RD1)
	 ||
	   where(RD -> RD1)
	 |)
	 Make_results(V -> RS1)
	 Make_infin_list_results(RS1 -> RS2)
	 Add_reads(RD1, RS2 -> RS)
	 Closeenv()

  'rule' Make_results(enum_map(P, nil) -> list(result(fin_map(any,any),nil,nil,nil,nil),nil)):

  'rule' Make_results(enum_map(P, PAIRS) -> RS):
	 Make_map_results_as_list(P, PAIRS -> RS)
	 Check_all_readonly(P, RS)

  'rule' Make_results(comp_map(P, PAIR, set_limit(P1, TS, R)) -> RS):
	 Type_check_typings(TS)
	 Openenv()
	 Define_value_typings(TS)
	 (|
	   where(R -> restriction(P2,V2))
	   Make_results(V2 -> RS2)
	   Type_check(P2, result(bool,list(free,nil),nil,nil,nil), RS2 -> RS21)
	   Get_reads(RS21 -> RD)
	 ||
	   where(ACCESSES'nil -> RD)
	 |)
	 Make_pair_results(PAIR -> RS3)
	 Add_reads(RD, RS3 -> RS)
	 Closeenv()

  'rule' Make_results(function(P, LP, V) -> RS):
	 Make_function_results(P, LP, V -> RS)

  'rule' Make_results(application(P,F,ARGS) -> RS):
	 Make_results(F -> RS1)
	 Make_application_results(P, RS1, ARGS -> RS) 

  'rule' Make_results(quantified(P,Q,TPS,R) -> list(result(bool,RD,nil,nil,nil),nil)):
	 Type_check_typings(TPS)
	 Openenv()
	 Define_value_typings(TPS)
	 (|
	   where(R -> restriction(P2,V2))
	   Make_results(V2 -> RS2)
	   Type_check(P2, result(bool,list(free,nil),nil,nil,nil), RS2 -> RS21)
	   Get_reads(RS21 -> RD)
	 ||
	   where(ACCESSES'nil -> RD)
	 |)
	 Closeenv()

  'rule' Make_results(equivalence(P,V1,V2,PRE) -> list(result(bool,RD3,nil,nil,nil),nil)):
-- debug
-- Putmsg("Comparing ")
-- Print_expr(V1)
-- Putmsg(" and ")
-- Print_expr(V2)
-- Putnl()
	 (|
	   where(PRE -> pre_cond(P2,V3))
	   Make_results(V3 -> RS2)
	   Type_check(P2, result(bool,list(free,nil),nil,nil,nil), RS2 -> RS21)
	   Get_reads(RS21 -> RD)
	 ||
	   where(ACCESSES'nil -> RD)
	 |)
	 Make_results(V1 -> RS1)
	 Make_results(V2 -> RS2)
	 Make_products(RS2 -> PRS)
	 Mult(RS1, PRS -> ARS)
-- Print_results(ARS)
-- Putnl()
	 Poly_disambiguate_args(ARS -> ARS1)
	 Function_intersection(P,
	   list(result(fun(product(list(poly(1),list(poly(1),nil))),total,result(bool,nil,nil,nil,nil)),nil,nil,nil,nil),nil), ARS1 -> RS)
-- Print_results(ARS1)
-- Putnl()
	 [| eq(RS, nil)
	    ne(RS1, nil)  -- can assume some error already reported?
	    ne(RS2, nil)
	    Puterror(P)
	    Putmsg("Values of type ")
	    Print_results(RS1)
	    Putnl()
	    Putmsg("and type ")
	    Print_results(RS2)
	    Putnl()
	    Putmsg("cannot be compared")
	    Putnl() |]
	 Get_reads(RS -> RD1)
	 Concat_accs(RD, RD1 -> RD2)
	 Get_writes(RS -> WR)
	 Concat_accs(RD2, WR -> RD3)

  'rule' Make_results(post(P, V, post_cond(P1, R, C), PRE) -> list(result(bool,RD2,nil,nil,nil),nil)):
	 (|
	   where(PRE -> pre_cond(P3,V3))
	   Make_results(V3 -> RS2)
	   Type_check(P3, result(bool,list(free,nil),nil,nil,nil), RS2 -> RS21)
	   Get_reads(RS21 -> RD)
	 ||
	   where(ACCESSES'nil -> RD)
	 |)
	 Make_unique_result(P, V -> result(T,_,_,_,_))
	 (|
	   where(R -> result(P2, B))
	   Openenv()
	   Define_value_binding(B, T)
	   Make_results(C -> CRS)
	   Type_check(P1, result(bool,list(free,nil),nil,nil,nil), CRS -> CRS1)
	   Closeenv()
	 ||
	   Make_results(C -> CRS)
	   Type_check(P1, result(bool,list(free,nil),nil,nil,nil), CRS -> CRS1)
	 |)	 
	 Get_reads(CRS1 -> RD1)
	 Concat_accs(RD, RD1 -> RD2)

  'rule' Make_results(disamb(P,V,T) -> RS):
	 Type_check_type(T)
	 Check_type_defined(T -> T1)
	 Make_results(V -> RS1)
-- debug
-- Putmsg("Possible results ")
-- Print_results(RS1)
	 Match_results(RS1, T1 -> RS)
-- Putmsg("\nmatched up to ")
-- Print_results(RS)
-- Putnl()
	 (|
	   where(RS -> list(_, nil))
	 ||
	   ne(RS, nil)
	   Puterror(P)
	   Putmsg("Disambiguation does not distinguish\nbetween expression types ")
	   Print_results(RS)
	   Putnl()
	 ||
	   [|
	     ne(RS1, nil)  -- can assume some error already reported?
	     Puterror(P)
	     Putmsg("Type ")
	     Print_type(T1)
	     Putnl()
	     Putmsg("incompatible with type ")
	     Print_results(RS1)
	     Putnl()
	   |]
	 |) 

  'rule' Make_results(bracket(P,V) -> RS):
	 Make_results(V -> RS)

  'rule' Make_results(ax_infix(P,L,C,R,_) -> list(result(bool,RD,WR,IN,OUT),nil)):
         Make_results(L -> LRS)
	 Type_check(P, result(bool,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), LRS -> LRS1)
	 Make_results(R -> RRS)
	 Type_check(P, result(bool,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RRS -> RRS1)
	 Merge_reads(LRS1, RRS1 -> RD)
	 Merge_writes(LRS1, RRS1 -> WR)
	 Merge_ins(LRS1, RRS1 -> IN)
	 Merge_outs(LRS1, RRS1 -> OUT)

  'rule' Make_results(val_infix(P,L,Op,R) -> RS):
         Make_results(L -> LRS)
--print(LRS)
	 Make_results(R -> RRS)
--print(RRS)
	 Make_products(RRS -> PRRS)
	 Mult(LRS, PRRS -> ARS)
	 Lookup_value_name(P, name(P,op_op(Op)) -> Ids)
	 Make_pure_results(Ids -> FRS)
         Poly_disambiguate_args(ARS -> ARS1)
         --(|
         --  Match_Results(ARS1,FRS)
         --  where(RESULTS'list(result(unit,nil,nil,nil,nil),nil) -> RS)
         --||
           Resolve_Types_In_Results(ARS1 -> ARS2)
	   Function_intersection(P, FRS, ARS2 -> RS)
	   [| eq(RS,nil)
	      ne(ARS1, nil)  -- can assume some error already reported?
	      ne(FRS, nil)
	      Puterror(P)
              --print(L)
              --print(R)
	      Putmsg("Argument types ")
	      Print_product_results_as_list(ARS1)
	      Putnl()
	      Putmsg("incompatible with `")
	      Print_op(Op)
	      Putmsg("' type ")
	      Print_id_types(Ids)
	      Putnl()
	   |]
          --|)

  'rule' Make_results(stmt_infix(P, L, Comb, R) -> RS):
	 Make_results(L -> LRS)
	 Make_results(R -> RRS)
	 (|
	   (| eq(Comb, parallel) || eq(Comb, interlock) |)
	   Type_check(P, result(unit,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), LRS -> LRS1)
	   Type_check(P, result(unit,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RRS -> RRS1)
	   Add_accesses(LRS1, RRS1 -> RS)
	 ||
	   (|
	     eq(Comb, sequence)
	     Type_check(P, result(unit,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), LRS -> LRS1)
	     Add_accesses(LRS1, RRS -> RS)
	   ||
	     -- internal or external choice
	     Intersection_results(LRS, RRS -> RS)
	     [|
	       eq(RS, nil)
	       ne(LRS, nil)  -- can assume some error already reported?
	       ne(RRS, nil)
	       Puterror(P)
	       Putmsg("Types ")
	       Print_results(LRS)
	       Putnl()
	       Putmsg("and ")
	       Print_results(RRS)
	       Putmsg(" are not compatible")
	       Putnl()
	     |]
	   |)
	 |)
	 
  'rule' Make_results(always(P, V) -> list(result(bool,nil,nil,nil,nil), nil)):
	 Make_results(V -> RS)
	 Type_check(P, result(bool,list(free,nil),nil,nil,nil), RS -> RS1)

  'rule' Make_results(ax_prefix(P, C, V) -> list(result(bool,RD,WR,IN,OUT), nil)):
	 Make_results(V -> RS)
	 Type_check(P, result(bool,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RS -> RS1)
	 Get_reads(RS1 -> RD)
	 Get_writes(RS1 -> WR)
	 Get_ins(RS1 -> IN)
	 Get_outs(RS1 -> OUT)

  'rule' Make_results(val_prefix(P,Op,V) -> RS):
	 Make_results(V -> ARS)
	 Lookup_value_name(P, name(P,op_op(Op)) -> Ids)
	 Make_pure_results(Ids -> FRS)
	 Poly_disambiguate_args(ARS -> ARS1)
	 Function_intersection(P, FRS, ARS1 -> RS)
	 [| eq(RS,nil)
	    ne(ARS1, nil)  -- can assume some error already reported?
	    ne(FRS, nil)
	    Puterror(P)
	    Putmsg("Argument type ")
	    Print_results(ARS1)
	    Putnl()
	    Putmsg("incompatible with `")
	    Print_op(Op)
	    Putmsg("' type ")
	    Print_id_types(Ids)
	    Putnl()
	 |]

  'rule' Make_results(comprehended(P, Comb, V, set_limit(P1, TPS, R)) -> RS3):
	 [|
	   (| eq(Comb, interlock) || eq(Comb, sequence) |)
	   Puterror(P)
	   Putmsg("Only combinators ||, |=|, and |^| may be used in a comprehended expression")
	   Putnl()
	 |]
	 Type_check_typings(TPS)
	 Openenv()
	 Define_value_typings(TPS)
	 (|
	   where(R -> restriction(P2,V2))
	   Make_results(V2 -> RS2)
	   Type_check(P2, result(bool,list(free,nil),nil,nil,nil), RS2 -> RS21)
	   Get_reads(RS21 -> RD)
	 ||
	   where(ACCESSES'nil -> RD)
	 |)
	 Make_results(V -> RS1)
	 (|
	   eq(Comb, parallel)
	   Type_check(P, result(unit,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RS1 -> RS11)
	 ||
	   where(RS1 -> RS11)
	 |)
	 Add_reads(RD, RS11 -> RS3)
	 Closeenv()

  'rule' Make_results(initialise(P, OQ) -> list(result(unit,nil,WR,nil,nil), nil)):
	 (|
	   where(OQ -> qualification(Obj))
	   (|
	     Get_object_id(Obj -> object_id(I), _)
	     where(ACCESSES'list(completed_access(P,qualification(obj_occ(P, I))), nil) -> WR)
	   ||
	     Puterror(P)
	     Putmsg("Object ")
	     Print_object(Obj)
	     Putmsg(" hidden, renamed, or not defined")
	     Putnl()
	     where(ACCESSES'nil -> WR)
	   |)
	 ||
	   where(ACCESSES'list(completed_access(P, nil), nil) -> WR)
	 |)
	 
  'rule' Make_results(assignment(P, N, V) -> RS2):
	 (|
	   Lookup_variable_name(N -> variable_id(I))
	   I'Type -> T
	   Make_results(V -> RS)
	   Type_check(P, result(T,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RS -> RS1)
	   Add_accesses(RS1, list(result(unit,nil,list(variable(P,I,nil),nil),nil,nil),nil) -> RS2)
	 ||
	   Puterror(P)
	   Putmsg("Variable name ")
	   Print_name(N)
	   Putmsg(" hidden, renamed, or not defined")
	   Putnl()
	   Make_results(V -> RS)
	   Add_accesses(RS, list(result(unit,nil,nil,nil,nil),nil) -> RS2)
	 |)

  'rule' Make_results(input(P, N) -> RS):
	 (|
	   Lookup_channel_name(N -> channel_id(I))
	   I'Type -> T
	   where(ACCESSES'list(channel(P,I,nil), nil) -> IN)
	   (|
	     IsTimed()
	     where(RESULTS'list(result(T,nil,nil,IN,nil),
	           list(result(product(list(T,list(time,nil))),nil,nil,IN,nil), nil)) -> RS)
	   ||
	     where(RESULTS'list(result(T,nil,nil,IN,nil), nil) -> RS)
	   |)
	 ||
	   Puterror(P)
	   Putmsg("Channel name ")
	   Print_name(N)
	   Putmsg(" hidden, renamed, or not defined")
	   Putnl()
	   where(TYPE_EXPR'any -> T)
	   where(ACCESSES'nil -> IN)
	   where(RESULTS'list(result(T,nil,nil,IN,nil), nil) -> RS)
	 |)

  'rule' Make_results(output(P, N, V) -> RS3):
	 (|
	   Lookup_channel_name(N -> channel_id(I))
	   I'Type -> T
	   Make_results(V -> RS)
	   Type_check(P, result(T,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RS -> RS1)
	   where(ACCESSES'list(channel(P,I,nil), nil) -> OUT)
	   (|
	     IsTimed()
	     where(RESULTS'list(result(unit,nil,nil,nil,OUT),
	           list(result(time,nil,nil,nil,OUT), nil)) -> RS2)
	   ||
	     where(RESULTS'list(result(unit,nil,nil,nil,OUT),nil) -> RS2)
	   |)
	   Add_accesses(RS1, RS2 -> RS3)
	 ||
	   Puterror(P)
	   Putmsg("Channel name ")
	   Print_name(N)
	   Putmsg(" hidden, renamed, or not defined")
	   Putnl()
	   Make_results(V -> RS1)
	   (|
	     IsTimed()
	     where(RESULTS'list(result(unit,nil,nil,nil,nil),
		   list(result(time,nil,nil,nil,nil),nil)) -> RS2)
	   ||
	     where(RESULTS'list(result(unit,nil,nil,nil,nil),nil) -> RS2)
	   |)
	   Add_accesses(RS1, RS2 -> RS3)
	 |)

  'rule' Make_results(local_expr(P, DS, V) -> RS)
	 Get_current_with(-> WITH)
	 Current -> C
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 Make_basic_env(basic(DS))
	 Complete_type_env(basic(DS))
	 Make_value_env(basic(DS))
	 Check_value_env(basic(DS))
	 Make_results(V -> RS1)
	 Current -> current_env(CE, C1)
	 Current <- C1
	 Extend_paths <- Paths
	 Remove_accesses(RS1, CE -> RS)

  'rule' Make_results(class_scope_expr(P, CL, V) -> RS):
	 Get_current_with(-> WITH)
	 Current -> C
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 Make_basic_env(CL)
	 Complete_type_env(CL)
	 Make_value_env(CL)
	 Check_value_env(CL)
	 Current -> C1
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C1)
	 Extend_paths -> Paths1
	 Extend_paths <- list(nil,Paths1)
	 Make_results(V -> RS)
	 Current <- C
	 Extend_paths <- Paths
	 
  'rule' Make_results(implementation_relation(P, CL1, CL2) -> RS):
	 Get_current_with(-> WITH)
	 Current -> C
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 Make_basic_env(CL1)
	 Complete_type_env(CL1)
	 Make_value_env(CL1)
	 Check_value_env(CL1)
	 Current -> current_env(Newenv, C1)
	 Dummy_id1 -> Id1
	 New_object_id(P, Id1 -> I1)
	 Qualify_class_env(I1, Newenv -> Newenv1)
	 I1'Env <- Newenv1
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths <- list(nil,Paths)
	 Make_basic_env(CL2)
	 Complete_type_env(CL2)
	 Make_value_env(CL2)
	 Check_value_env(CL2)
	 Current -> current_env(Oldenv, C2)
	 Dummy_id2 -> Id2
	 New_object_id(P, Id2 -> I2)
	 Qualify_class_env(I2, Oldenv -> Oldenv1)
	 I2'Env <- Oldenv1
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,object_env(I1,object_env(I2,nil)),nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths <- list(nil,Paths)
	 Make_results(implementation_expr(P, obj_name(name(P, id_op(Id1))), obj_name(name(P, id_op(Id2)))) -> RS)
	 Current <- C
	 Extend_paths <- Paths
	 
  'rule' Make_results(implementation_expr(P, Obj1, Obj2) -> list(result(bool,nil,nil,nil,nil),nil)):
	 (|
	   Get_object_id(Obj1 -> object_id(I1), _)
	   I1'Env -> Newenv
	   Object_param_type(Obj1, I1 -> PT1)
	   (|
	     Get_object_id(Obj2 -> object_id(I2), _)
	     I2'Env -> Oldenv
	     Object_param_type(Obj2, I2 -> PT2)
	     Check_object_params(P, PT2, PT1)
	     Current -> C
	     Extend_paths -> Paths
	     Current <- current_env(Newenv, nil)
	     Extend_paths <- list(nil,nil)
	     Type_numbers -> TF
	     Type_numbers <- list(nil, TF)
-- debug
-- Get_env_top_values(Oldenv -> VS)
-- Print_value_env(VS)
	     Unfold_types(Oldenv, Oldenv, nil, nil -> Oldenv1)
-- Putmsg(" which unfolds to ")
-- Get_env_top_values(Oldenv1 -> VS1)
-- Print_value_env(VS1)
	     Check_implementation(P, nil, Oldenv1, Oldenv1, nil, nil)
	     Current <- C
	     Extend_paths <- Paths
	     Type_numbers <- TF
	   ||
	     Object_pos(Obj2 -> P2)
	     Puterror(P2)
	     Putmsg("Implemented object ")
	     Print_object(Obj2)
	     Putmsg(" hidden, renamed, or not defined")
	     Putnl()
	   |)
	 ||
	   Object_pos(Obj1 -> P1)
	   Puterror(P1)
	   Putmsg("Implementing object ")
	   Print_object(Obj1)
	   Putmsg(" hidden, renamed, or not defined")
	   Putnl()
	 |)

  'rule' Make_results(let_expr(P,DEFS,V) -> RS):
	 Make_let_results(P, DEFS, V -> RS)

  'rule' Make_results(if_expr(P, V, THEN, _, ELSIF, ELSE) -> RS):
	 Make_results(V -> VRS)
	 Type_check(P, result(bool,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), VRS -> VRS1)
	 Make_results(THEN -> RS1)
	 (| eq(ELSIF, nil)
	    where(RS1 -> RS2)
	    where(RS1 -> RS3)
	 || Make_elsif_results(ELSIF -> RS2)
	    Intersection_results(RS1, RS2 -> RS3)
	 |)
	 (| where(ELSE -> else(P1, EV))
	    Make_results(EV -> RS4)
	 || where(RESULTS'list(result(unit,nil,nil,nil,nil), nil) -> RS4)
	 |)
	 Intersection_results(RS3, RS4 -> RS5)
	 [| eq(RS5, nil)
	    ne(RS1, nil)  -- can assume some error already reported?
	    ne(RS4, nil)
	    Puterror(P)
	    Putmsg("then type ")
	    Print_results(RS1)
	    Putnl()
	    [| ne(ELSIF, nil)
	       ne(RS2, nil)  -- checked in Make_elsif_types
	       Putmsg("and elsif type ")
	       Print_results(RS2)
	       Putnl() |]
	    Putmsg("and else type ")
	    Print_results(RS4)
	    Putnl()
	    Putmsg("are not compatible")
	    Putnl() |]
	 Add_accesses(VRS1, RS5 -> RS)

  'rule' Make_results(case_expr(P, V, PE, BRANCHES) -> RS):
	 Make_case_results(PE, V, BRANCHES -> RS)

  'rule' Make_results(while_expr(P, V1, V2) -> list(result(unit,RD,WR,IN,OUT), nil)):
	 Make_results(V1 -> RS1)
	 Type_check(P, result(bool,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RS1 -> RS11)
	 Make_results(V2 -> RS2)
	 Type_check(P, result(unit,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RS2 -> RS21)
	 Merge_reads(RS11, RS21 -> RD)
	 Merge_writes(RS11, RS21 -> WR)
	 Merge_ins(RS11, RS21 -> IN)
	 Merge_outs(RS11, RS21 -> OUT)
	 
  'rule' Make_results(until_expr(P, V1, V2) -> list(result(unit,RD,WR,IN,OUT), nil)):
	 Make_results(V1 -> RS1)
	 Type_check(P, result(unit,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RS1 -> RS11)
	 Make_results(V2 -> RS2)
	 Type_check(P, result(bool,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RS2 -> RS21)
	 Merge_reads(RS11, RS21 -> RD)
	 Merge_writes(RS11, RS21 -> WR)
	 Merge_ins(RS11, RS21 -> IN)
	 Merge_outs(RS11, RS21 -> OUT)

  'rule' Make_results(for_expr(P, list_limit(P1, B, V1, R), V) -> RS):
	 Make_unique_result(P1, V1 -> Res)
	 Check_readonly(P1, Res)
	 where(Res -> result(T,RD,_,_,_))
	 Make_list_element_type(P1, T -> T1)
	 Openenv()
	 Define_value_typing(single(P1, B, T1))
	 (|
	   where(R -> restriction(P2,V2))
	   Make_results(V2 -> RS2)
	   Type_check(P2, result(bool,list(free,nil),nil,nil,nil), RS2 -> RS21)
	   Get_reads(RS21 -> RD2)
	 ||
	   where(ACCESSES'nil -> RD2)
	 |)
	 Make_results(V -> RS1)
	 Type_check(P, result(unit,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RS1 -> RS11)
	 Add_reads(RD, RS11 -> RS3)
	 Add_reads(RD2, RS3 -> RS)
	 Closeenv()

-- allow Make_results with resolved expressions
  'rule' Make_results(val_occ(_, I, _) -> list(result(T,nil,nil,nil,nil),nil)):
	 I'Type -> T

  'rule' Make_results(var_occ(P, I, Q) -> list(result(T,list(variable(P,I,Q),nil),nil,nil,nil), nil)):
	 I'Type -> T

-- this is a channel occurrence as a predicate in an LTL expression
-- make it pure, and of type Bool
  'rule' Make_results(chan_occ(P, I, Q) -> list(result(bool,nil,nil,nil,nil), nil)):

  'rule' Make_results(pre_occ(P, I, Q) -> list(result(T,list(variable(P,I,Q),nil),nil,nil,nil), nil)):
	 I'Type -> T

  'rule' Make_results(infix_occ(P, L, I, _, R) -> RS):
	 Make_results(L -> LRS)
	 Make_results(R -> RRS)
	 Make_products(RRS -> PRRS)
	 Mult(LRS, PRRS -> ARS)
	 I'Type -> T
	 where(RESULTS'list(result(T,nil,nil,nil,nil),nil) -> FRS)
	 Poly_disambiguate_args(ARS -> ARS1)
	 Function_intersection(P, FRS, ARS1 -> RS)

  'rule' Make_results(prefix_occ(P, I, _, V) -> RS):
	 Make_results(V -> ARS)
	 I'Type -> T
	 where(RESULTS'list(result(T,nil,nil,nil,nil),nil) -> FRS)
	 Poly_disambiguate_args(ARS -> ARS1)
	 Function_intersection(P, FRS, ARS1 -> RS)

  'rule' Make_results(ass_occ(P, I, Q, V) -> RS):
	 Make_results(V -> RS1)
	 I'Type -> T
	 Add_accesses(RS1, list(result(unit,nil,list(variable(P,I,Q),nil),nil,nil),nil) -> RS)

  'rule' Make_results(input_occ(P, I, Q) -> RS):
	 I'Type -> T
	 where(ACCESSES'list(channel(P,I,Q), nil) -> IN)
	 (|
	   IsTimed()
	   where(RESULTS'list(result(T,nil,nil,IN,nil),
		 list(result(product(list(T,list(time,nil))),nil,nil,IN,nil), nil)) -> RS)
	 ||
	   where(RESULTS'list(result(T,nil,nil,IN,nil), nil) -> RS)
	 |)

  'rule' Make_results(output_occ(P, I, Q, V) -> RS):
	 I'Type -> T
	 Make_results(V -> RS1)
	 where(ACCESSES'list(channel(P,I,Q), nil) -> OUT)
	 (|
	   IsTimed()
	   where(RESULTS'list(result(unit,nil,nil,nil,OUT),
		 list(result(time,nil,nil,nil,OUT), nil)) -> RS2)
	 ||
	   where(RESULTS'list(result(unit,nil,nil,nil,OUT),nil) -> RS2)
	 |)
	 Add_accesses(RS1, RS2 -> RS)

  'rule' Make_results(env_local(P, DS, _, V) -> RS):
	 Make_results(local_expr(P, DS, V) -> RS)
	 
  'rule' Make_results(env_class_scope(P, CL, _, V) -> RS):
	 Make_results(class_scope_expr(P, CL, V) -> RS)

  'rule' Make_results(array_access(P, N, I) -> RS):
         Make_results(I -> RS1)
         Make_results(N -> RS2)
         Type_check(P, result(array(any,any),list(free,nil), list(free,nil), list(free,nil), list(free,nil)), RS2 -> _)
         where(RS2 -> list(Res,_))
         where(Res -> result(T,_,_,_,_))
         (|
           Remove_Brackets(T -> array(TI,TV))
           Add_accesses(RS2, list(result(TI,nil,nil,nil,nil),nil) -> list(Res2,_))
           Type_check(P, Res2, RS1 -> RS3)
           Add_accesses(RS2, list(result(TV,nil,nil,nil,nil),nil) -> RS)
         ||
           /*Puterror(P)
           Print_expr(N)
           Putmsg(" was expected to be of array type, but found: ")
           Print_result(Res)
           Putnl()*/
           where(RESULTS'nil -> RS)
         |)

  'rule' Make_results(array_expr(P, Sub, Val) -> list(R,nil)):
         Make_array_expr_results(array_expr(P,Sub,Val) -> R)


  'rule' Make_results(local_val_occ(P, V, Q) -> Res)
         Make_results(val_occ(P,V,Q) -> Res)

	 
-- debug
--   'rule' Make_results(V -> nil):
-- 	 print(V)

'action' Make_results_for_array_occ(TYPE_EXPR, VALUE_EXPRS, POS -> RESULTS)
  'rule' Make_results_for_array_occ(Type, list(H,nil), P -> RS)
         Make_results(H -> RS1)
         Type_check(P, result(array(any,any), list(free,nil), list(free,nil), list(free,nil), list(free,nil)), list(result(Type, list(free,nil), list(free,nil), list(free,nil), list(free,nil)),nil) -> _)
         (|
           Remove_Brackets(Type -> array(IT,VT))
           Type_check(P, result(IT, list(free,nil), list(free,nil), list(free,nil), list(free,nil)), RS1 -> RS2)
           where(RESULTS'list(result(VT,nil, nil, nil, nil),nil) -> RS3)
           Add_accesses(RS2, RS3 -> RS)
         ||
           where(RESULTS'nil -> RS)
         |)
         
  'rule' Make_results_for_array_occ(Type, list(H,T), P -> RS)
         Make_results(H -> RS1)
         Type_check(P, result(array(any,any), list(free,nil), list(free,nil), list(free,nil), list(free,nil)), list(result(Type, list(free,nil), list(free,nil), list(free,nil), list(free,nil)),nil) -> _)
         (|
           Remove_Brackets(Type -> array(IT,VT))
           Type_check(P, result(IT, list(free,nil), list(free,nil), list(free,nil), list(free,nil)), RS1 -> RS2)
           Make_results_for_array_occ(VT, T, P -> RSTemp1)
           Add_accesses(RS2, RSTemp1 -> RS)
         ||
           where(RESULTS'nil -> RS)
         |)




'action' GetTypeFromTyping(TYPING -> TYPE_EXPR)
  'rule' GetTypeFromTyping(single(_,_,T) -> T)
  'rule' GetTypeFromTyping(multiple(_,_,T) -> T)

'action' Make_array_expr_results(VALUE_EXPR -> RESULT)
  'rule' Make_array_expr_results(array_expr(P,Typing,Val) -> result(array(IndexType,ValType),A1,A2,A3,A4))
         Type_check_typing(Typing)
         Openenv()
         Define_value_typing(Typing)
         GetTypeFromTyping(Typing -> IndexType)
         Make_results(Val -> list(result(ValType,A1,A2,A3,A4),REST))
         Closeenv


'action' Make_unique_result(POS, VALUE_EXPR -> RESULT)

  'rule' Make_unique_result(P, V -> result(T,RD,WR,IN,OUT))
	 Make_results(V -> RS1)
	 Remove_duplicates(RS1 -> RS)
-- debug
-- print(RS1)
-- print(RS)
	 (|
	   where(RS -> list(result(T,RD,WR,IN,OUT), nil))
	   Contains_any_or_poly(T, nil -> Found)
	   [|
	     eq(Found, found)
	     Puterror(P)
	     Putmsg("Disambiguation needed")
	     Putnl()
	   |]
	 ||
	   where(RESULT'result(any,nil,nil,nil,nil) -> result(T,RD,WR,IN,OUT))
	   [|
	     ne(RS, nil)  -- can assume some error already reported?
	     Puterror(P)
	     Putmsg("Unresolvable overloading between types ")
	     Print_results(RS)
-- debug
-- print(RS)
	     Putnl()
	   |]
	 |)

'action' Remove_duplicates(RESULTS -> RESULTS)

  'rule' Remove_duplicates(list(R, nil) -> list(R, nil)):

  'rule' Remove_duplicates(list(result(T1,RD1,WR1,IN1,OUT1),list(result(T2,RD2,WR2,IN2,OUT2),RS3)) -> RS):
	 -- no coercions allowed; must be same maximal type
	 (|
	   Match(T1, nil, T2)
	   -- we know there are at least two:
	   -- no point trying to remove others
	   Remove_duplicates(list(result(T1,RD1,WR1,IN1,OUT1),RS3) -> RS)
	 ||
	   where(RESULTS'list(result(T1,RD1,WR1,IN1,OUT1),list(result(T2,RD2,WR2,IN2,OUT2),RS3)) -> RS)
	 |)

  'rule' Remove_duplicates(nil -> nil):

'sweep' Contains_any_or_poly(ANY, FOUND -> FOUND)

  'rule' Contains_any_or_poly(TYPE_EXPR'any, F -> found)

  'rule' Contains_any_or_poly(TYPE_EXPR'poly(_), F -> found)

'sweep' Contains_poly(ANY, FOUND -> FOUND)

  'rule' Contains_poly(TYPE_EXPR'poly(_), F -> found)

'action' Make_infin_set_results(RESULTS -> RESULTS)

  'rule' Make_infin_set_results(list(result(T,RD,WR,IN,OUT), TS) -> list(result(infin_set(T),RD,WR,IN,OUT),TS1)):
	 Make_infin_set_results(TS -> TS1)

  'rule' Make_infin_set_results(nil -> nil):

'action' Make_fin_set_results(RESULTS -> RESULTS)

  'rule' Make_fin_set_results(list(result(T,RD,WR,IN,OUT), TS) -> list(result(fin_set(T),RD,WR,IN,OUT),TS1)):
	 Make_fin_set_results(TS -> TS1)

  'rule' Make_fin_set_results(nil -> nil):

'action' Make_infin_list_results(RESULTS -> RESULTS)

  'rule' Make_infin_list_results(list(result(T,RD,WR,IN,OUT), TS) -> list(result(infin_list(T),RD,WR,IN,OUT),TS1)):
	 Make_infin_list_results(TS -> TS1)

  'rule' Make_infin_list_results(nil -> nil):

'action' Make_fin_list_results(RESULTS -> RESULTS)

  'rule' Make_fin_list_results(list(result(T,RD,WR,IN,OUT), TS) -> list(result(fin_list(T),RD,WR,IN,OUT),TS1)):
	 Make_fin_list_results(TS -> TS1)

  'rule' Make_fin_list_results(nil -> nil):

'action' Make_set_element_type(POS, TYPE_EXPR -> TYPE_EXPR)

  'rule' Make_set_element_type(P, fin_set(T) -> T):

  'rule' Make_set_element_type(P, infin_set(T) -> T):

  'rule' Make_set_element_type(P, T -> T1):
	 Make_set_type(T -> T2)
	 (| where(T2 -> fin_set(T1)) || where(T2 -> infin_set(T1)) |)

  'rule' Make_set_element_type(P, T -> any):
	 Puterror(P)
	 Putmsg("Expected set type; found ")
	 Print_type(T)
	 Putnl()

'action' Make_list_element_type(POS, TYPE_EXPR -> TYPE_EXPR)

  'rule' Make_list_element_type(P, fin_list(T) -> T):

  'rule' Make_list_element_type(P, infin_list(T) -> T):

  'rule' Make_list_element_type(P, T -> T1):
	 Make_list_type(T -> T2)
	 (| where(T2 -> fin_list(T1)) || where(T2 -> infin_list(T1)) |)

  'rule' Make_list_element_type(P, T -> any):
	 Puterror(P)
	 Putmsg("Expected list type; found ")
	 Print_type(T)
	 Putnl()

'action' Make_map_element_types(POS, TYPE_EXPR -> TYPE_EXPR, TYPE_EXPR)

  'rule' Make_map_element_types(P, T -> D, R):
	 Make_map_type(T -> T2)
	 (| where(T2 -> fin_map(D, R)) || where(T2 -> infin_map(D, R)) |)

  'rule' Make_map_element_types(P, T -> any, any):
	 Puterror(P)
	 Putmsg("Expected map type; found ")
	 Print_type(T)
	 Putnl()

'action' Make_array_element_types(POS, TYPE_EXPR -> TYPE_EXPR, TYPE_EXPR)

  'rule' Make_array_element_types(P, T -> D, R):
	 Make_array_type(T -> T2)
	 where(T2 -> array(D, R))

  'rule' Make_array_element_types(P, T -> any, any):
	 Puterror(P)
	 Putmsg("Expected array type; found ")
	 Print_type(T)
	 Putnl()

'action' Make_map_results_as_list(POS, VALUE_EXPR_PAIRS  -> RESULTS)

  'rule' Make_map_results_as_list(P, list(PAIR, nil) -> RS):
	 Make_pair_results(PAIR -> RS)

  'rule' Make_map_results_as_list(P, list(PAIR, PAIRS) -> RS):
	 Make_pair_results(PAIR -> RS1)
	 Make_map_results_as_list(P, PAIRS -> RS2)
	 Intersection_results(RS1, RS2 -> RS)
	 [|
	   eq(RS, nil)
	   ne(RS1, nil)  -- can assume some error already reported?
	   ne(RS2, nil)
	   Puterror(P)
	   Putmsg("Type ")
	   Print_results(RS1)
	   Putnl()
	   Putmsg("and type ")
	   Print_results(RS2)
	   Putnl()
	   Putmsg("are not compatible")
	   Putnl() |]

'action' Make_pair_results(VALUE_EXPR_PAIR -> RESULTS)

  'rule' Make_pair_results(pair(L, R) -> RS):
	 Make_results(L -> LRS)
	 Make_results(R -> RRS)
         Make_pairs(LRS, RRS -> RS)

'action' Make_pairs(RESULTS, RESULTS -> RESULTS)
	 
  'rule' Make_pairs(list(R1, RS1), RS2 -> RS):
	 Make_pair(R1, RS2 -> RS3)
	 Make_pairs(RS1, RS2 -> RS4)
	 Concat(RS3, RS4 -> RS)

  'rule' Make_pairs(nil, RS -> nil):

'action' Make_pair(RESULT, RESULTS -> RESULTS)

  'rule' Make_pair(result(T1,RD1,WR1,IN1,OUT1), list(result(T2,RD2,WR2,IN2,OUT2), RS2) -> list(result(infin_map(T1, T2),RD,WR,IN,OUT), RS3)):
	 Make_pair(result(T1,RD1,WR1,IN1,OUT1), RS2 -> RS3)
	 Concat_accs(RD1, RD2 -> RD)
	 Concat_accs(WR1, WR2 -> WR)
	 Concat_accs(IN1, IN2 -> IN)
	 Concat_accs(OUT1, OUT2 -> OUT)

  'rule' Make_pair(R, nil -> nil)

'action' Make_function_results(POS, LAMBDA_PARAMETER, VALUE_EXPR -> RESULTS)

  'rule' Make_function_results(P, l_typing(P1, TPS), V -> RS)
	 Type_check_typings(TPS)
	 Openenv()
	 Define_value_typings(TPS)
	 Make_results(V -> RS1)
	 Make_fun_results(TPS, RS1 -> RS)
	 Closeenv()

  'rule' Make_function_results(P, s_typing(P1, TP), V -> RS)
	 Type_check_typing(TP)
	 Openenv()
	 Define_value_typing(TP)
	 Make_results(V -> RS1)
	 Type_of_typing_as_product(TP -> T)
	 Make_param_fun_results(T, RS1 -> RS)
	 Closeenv()

'action' Make_fun_results(TYPINGS, RESULTS -> RESULTS)

  'rule' Make_fun_results(nil, RS -> RS1):
	 Make_param_fun_results(unit, RS -> RS1)

  'rule' Make_fun_results(TPS, RS -> RS1):
	 Type_of_typings_as_product(TPS -> T)
	 Make_param_fun_results(T, RS -> RS1)

'action' Make_param_fun_results(TYPE_EXPR, RESULTS -> RESULTS)

  'rule' Make_param_fun_results(T, list(R1, RS1) -> list(result(fun(T,partial,R1),nil,nil,nil,nil), RS2)):
         Make_param_fun_results(T, RS1 -> RS2)

  'rule' Make_param_fun_results(T, nil -> nil):

'action' Make_application_results(POS, RESULTS, ACTUAL_FUNCTION_PARAMETERS -> RESULTS)

  'rule' Make_application_results(P, FRS, list(fun_arg(P2,VS), ARGS) -> RS):
	 (|
	   eq(VS, nil)
	   where(RESULTS'list(result(unit,nil,nil,nil,nil),nil) -> ARS)
	 ||
	   where(VS -> list(V,nil))
	   Make_results(V -> ARS)
	 ||
	   Make_results_as_product(VS -> ARS)
	 |)
	 Poly_disambiguate_args(ARS -> ARS1)
Resolve_Types_In_Results(FRS -> FRS1)
Resolve_Types_In_Results(ARS1 -> ARS2)
	 Function_intersection(P, FRS1, ARS2 -> FRS2)
	 [| eq(FRS2,nil)
	    ne(ARS1, nil)  -- can assume some error already reported?
	    ne(FRS, nil)
	    Puterror(P)
	    (|
	      (| eq(VS, nil) || where(VS -> list(V,nil)) |)
	      Print_results(ARS1)
	    ||
	      Print_product_results_as_list(ARS1)
	    |)
	    Putnl()
	    Putmsg("cannot be argument type for ")
	    Print_results(FRS)
	    Putnl()
	 |]
	 Make_application_results(P, FRS2, ARGS -> RS)

  'rule' Make_application_results(P, FRS, nil -> FRS):

'action' Make_results_as_list(POS, VALUE_EXPRS -> RESULTS)

  'rule' Make_results_as_list(P, list(V,nil) -> RS1):
	 Make_results(V -> RS1)

  'rule' Make_results_as_list(P, list(V,VS) -> RS):
	 Make_results(V -> RS1)
	 Make_results_as_list(P, VS -> RS2)
	 Intersection_results(RS1, RS2 -> RS)
	 [|
	   eq(RS, nil)
	   ne(RS1, nil)  -- can assume some error already reported?
	   ne(RS2, nil)
	   Puterror(P)
	   Putmsg("Type ")
	   Print_results(RS1)
	   Putnl()
	   Putmsg("and type ")
	   Print_results(RS2)
	   Putnl()
	   Putmsg("are not compatible")
	   Putnl() |]

'action' Make_results_as_product(VALUE_EXPRS -> RESULTS)

  'rule' Make_results_as_product(list(V,nil) -> RS):
	 Make_results(V -> RS1)
	 Make_products(RS1 -> RS)

  'rule' Make_results_as_product(list(V,VS) -> RS):
	 Make_results(V -> RS1)
	 Make_results_as_product(VS -> RS2)
	 Mult(RS1, RS2 -> RS)

'action' Mult(RESULTS, RESULTS -> RESULTS)

  'rule' Mult(list(R1, RS1), RS2 -> RS):
	 Mult1(R1, RS2 -> RS3)
	 Mult(RS1, RS2 -> RS4)
	 Concat(RS3, RS4 -> RS)

  'rule' Mult(nil, R2 -> nil):

'action' Mult1(RESULT, RESULTS -> RESULTS)

  'rule' Mult1(result(bracket(T),RD,WR,IN,OUT), RS -> RS1):
	 Mult1(result(T,RD,WR,IN,OUT), RS -> RS1)

  'rule' Mult1(result(subtype(single(P,B,T),R),RD,WR,IN,OUT), RS -> RS1):
	 Mult1(result(T,RD,WR,IN,OUT), RS -> RS1)

  'rule' Mult1(result(T1,RD1,WR1,IN1,OUT1), list(result(product(T2PR),RD2,WR2,IN2,OUT2), RS2) -> list(result(product(list(T1,T2PR)),RD,WR,IN,OUT), RS3)):
	 Mult1(result(T1,RD1,WR1,IN1,OUT1), RS2 -> RS3)
	 Concat_accs(RD1, RD2 -> RD)
	 Concat_accs(WR1, WR2 -> WR)
	 Concat_accs(IN1, IN2 -> IN)
	 Concat_accs(OUT1, OUT2 -> OUT)
	 
  'rule' Mult1(R, nil -> nil)

'action' Concat(RESULTS, RESULTS -> RESULTS)

  'rule' Concat(list(R1,RS1), RS2 -> list(R1,RS)):
	 Concat(RS1, RS2 -> RS)

  'rule' Concat(nil, RS -> RS)

'action' Make_products(RESULTS -> RESULTS)

  'rule' Make_products(list(result(T,RD,WR,IN,OUT), RS) -> list(result(product(list(T,nil)),RD,WR,IN,OUT), RS1)):
	 Make_products(RS -> RS1)

  'rule' Make_products(nil -> nil):

'action' Make_let_results(POS, LET_DEFS, VALUE_EXPR -> RESULTS)

  'rule' Make_let_results(P, DEFS, V -> RS4)
	 Open_let_envs(DEFS -> RD,WR,IN,OUT)
	 Make_results(V -> RS)
	 Add_reads(RD, RS -> RS1)
	 Add_writes(WR, RS1 -> RS2)
	 Add_ins(IN, RS2 -> RS3)
	 Add_outs(OUT, RS3 -> RS4)
         Close_let_envs(DEFS)

'action' Open_let_envs(LET_DEFS -> ACCESSES, ACCESSES, ACCESSES, ACCESSES)

  'rule' Open_let_envs(list(explicit(P,binding(P1,B),V), DEFS) -> RD,WR,IN,OUT):
	 Make_unique_result(P, V -> result(T,RD1,WR1,IN1,OUT1))
	 Openenv()
	 Define_value_typing(single(P, B, T))
	 Open_let_envs(DEFS -> RD2,WR2,IN2,OUT2)
	 Concat_accs(RD1, RD2 -> RD)
	 Concat_accs(WR1, WR2 -> WR)
	 Concat_accs(IN1, IN2 -> IN)
	 Concat_accs(OUT1, OUT2 -> OUT)

  'rule' Open_let_envs(list(explicit(P,pattern(P1,PATT),V), DEFS) -> RD,WR,IN,OUT):
	 Make_unique_result(P, V -> result(T,RD1,WR1,IN1,OUT1))
	 Openenv()
	 Define_pattern(P, T, PATT)
	 Open_let_envs(DEFS -> RD2,WR2,IN2,OUT2)
	 Concat_accs(RD1, RD2 -> RD)
	 Concat_accs(WR1, WR2 -> WR)
	 Concat_accs(IN1, IN2 -> IN)
	 Concat_accs(OUT1, OUT2 -> OUT)

  'rule' Open_let_envs(list(implicit(P,T,R), DEFS) -> RD,WR,IN,OUT):
	 Openenv()
	 Define_value_typing(T)
	 (|
	   where(R -> restriction(P2,V))
	   Make_results(V -> RS)
	   Type_check(P2, result(bool,list(free,nil),nil,nil,nil), RS -> RS1)
	   Get_reads(RS1 -> RD1)
	 ||
	   where(ACCESSES'nil -> RD1)
	 |)
	 Open_let_envs(DEFS -> RD2,WR,IN,OUT)
	 Concat_accs(RD1, RD2 -> RD)

  'rule' Open_let_envs(nil -> nil,nil,nil,nil):

'action' Close_let_envs(LET_DEFS)

  'rule' Close_let_envs(list(D,DS)):
	 Closeenv()
	 Close_let_envs(DS)

  'rule' Close_let_envs(nil):

'action' Make_elsif_results(ELSIF_BRANCHES -> RESULTS)

  'rule' Make_elsif_results(list(elsif(P,V,THEN,_), nil) -> RS):
	 Make_results(V -> RS1)
	 Type_check(P, result(bool,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RS1 -> RS11)
	 Make_results(THEN -> RS2)
	 Add_accesses(RS11, RS2 -> RS)   	 

  'rule' Make_elsif_results(list(elsif(P,V,THEN,_), BRS) -> RS):
	 Make_results(V -> RS1)
	 Type_check(P, result(bool,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RS1 -> RS11)
	 Make_results(THEN -> RS2)
	 Make_elsif_results(BRS -> RS3)
	 Intersection_results(RS2, RS3 -> RS4)
	 [| eq(RS4, nil)
	    ne(RS2, nil)  -- can assume some error already reported?
	    ne(RS3, nil)
	    Puterror(P)
	    Putmsg("Type ")
	    Print_results(RS2)
	    Putnl()
	    Putmsg("and type ")
	    Print_results(RS3)
	    Putnl()
	    Putmsg("are not compatible")
	    Putnl() |]
	 Add_accesses(RS11, RS4 -> RS)

'action' Make_case_results(POS, VALUE_EXPR, CASE_BRANCHES -> RESULTS)

  'rule' Make_case_results(P, V, BRS -> RS):
	 Make_unique_result(P, V -> R)
	 Make_branches_results(R, BRS -> RS1)
	 Add_accesses(list(R,nil), RS1 -> RS)

'action' Make_branches_results(RESULT, CASE_BRANCHES -> RESULTS)

  'rule' Make_branches_results(result(bracket(T),RD,WR,IN,OUT), BRS -> RS):
	 Make_branches_results(result(T,RD,WR,IN,OUT), BRS -> RS)

  'rule' Make_branches_results(result(subtype(single(P, B, T), R),RD,WR,IN,OUT), BRS -> RS):
	 Make_branches_results(result(T,RD,WR,IN,OUT), BRS -> RS)

  'rule' Make_branches_results(T, list(BR, nil) -> RS):
	 Make_branch_results(T, BR -> RS)

  'rule' Make_branches_results(T, list(BR, BRS) -> RS):
	 Make_branch_results(T, BR -> RS1)
	 Make_branches_results(T, BRS -> RS2)
	 Intersection_results(RS1, RS2 -> RS)
	 [| eq(RS, nil)
	    ne(RS1, nil)  -- can assume some error already reported?
	    ne(RS2, nil)
	    where(BR -> case(P, PATT, V, _))
	    Puterror(P)
	    Putmsg("type ")
	    Print_results(RS1)
	    Putnl()
	    Putmsg("and type ")
	    Print_results(RS2)
	    Putnl()
	    Putmsg("are not compatible")
	    Putnl() |]

'action' Make_branch_results(RESULT, CASE_BRANCH -> RESULTS)

  'rule' Make_branch_results(R, case(P, literal_pattern(P1, L), V, _) -> RS):
	 Make_literal_results(L -> RS1)
	 Type_check(P, R, RS1 -> RS2)
	 Make_results(V -> RS)

  'rule' Make_branch_results(R, case(P, name_pattern(P1, N), V, _) -> RS):
	 Make_results(named_val(P1,N) -> RS1)
	 Check_all_pure(P1, RS1)
	 Type_check(P, R, RS1 -> RS2)
	 Make_results(V -> RS)

  'rule' Make_branch_results(R, case(P, wildcard_pattern(P1), V, _) -> RS):
	 Make_results(V -> RS)

  'rule' Make_branch_results(result(T,_,_,_,_), case(P, PATT, V, _) -> RS):
	 Openenv()
	 Define_pattern(P, T, PATT)
	 Make_results(V -> RS)
	 Closeenv()

'action' Define_pattern(POS, TYPE_EXPR, PATTERN)

  'rule' Define_pattern(P, T, literal_pattern(P1, L)):
	 Make_literal_results(L -> RS1)
	 Type_check(P, result(T,nil,nil,nil,nil), RS1 -> RS2)

  'rule' Define_pattern(P, T, name_pattern(P1, N)):
	 Make_results(named_val(P1,N) -> RS1)
	 Check_all_pure(P1, RS1)
	 Type_check(P, result(T,nil,nil,nil,nil), RS1 -> RS2)

  'rule' Define_pattern(P, T, record_pattern(P1, N, PATTS)):
	 Make_results(named_val(P1, N) -> RS)
	 Functions_with_result(RS, T -> RS1)
	 (|
	   where(RS1 -> list(result(fun(D,AR,R),RD,WR,IN,OUT),RS2))
	   (|
	     eq(RS2, nil)
	     Check_pure(P, result(fun(D,AR,R),RD,WR,IN,OUT))
	     Type_check(P1, result(T,nil,nil,nil,nil), list(R,nil) -> RS3)
	     (|
	       where(PATTS -> list(PATT,nil))
	       Define_pattern(P1, D, PATT)
	     ||
	       Length_ps(PATTS -> N1)
	       Make_product_type(D, N1 -> D1)
	       (|
		 where(D1 -> product(PR))
		 Define_pattern(P1, product(PR), product_pattern(P1, PATTS))
	       ||
		 Puterror(P1)
		 Putmsg("Structure of pattern does not match structure of argument type ")
		 Print_type(D)
		 Putnl()
		 -- avoid consequent error message
		 Make_any_product(N1 -> PR1)
	         Define_pattern(P1, product(PR1), product_pattern(P1, PATTS))
	       |)
	     |)
	   ||
	     Puterror(P1)
	     Putmsg("Unresolvable overloading between types ")
	     Print_results(RS1)
	     Putnl()
	     -- avoid consequent error message
	     (|
	       where(PATTS -> list(PATT,nil))
	       Define_pattern(P1, any, PATT)
	     ||
	       Length_ps(PATTS -> N1)
	       Make_any_product(N1 -> PR)
	       Define_pattern(P1, product(PR), product_pattern(P1, PATTS))
	     |)
	   |)
	 ||
	   [|
	     ne(RS, nil)  -- can assume some error already reported?
	     Puterror(P1)
	     Print_name(N)
	     Putmsg(" with possible type(s) ")
	     Print_results(RS)
	     Putnl()
	     Putmsg("cannot give result type ")
	     Print_type(T)
	     Putnl()
	     -- avoid consequent error message
	     (|
	       where(PATTS -> list(PATT,nil))
	       Define_pattern(P1, any, PATT)
	     ||
	       Length_ps(PATTS -> N1)
	       Make_any_product(N1 -> PR)
	       Define_pattern(P1, product(PR), product_pattern(P1, PATTS))
	     |)
	   |]
	 |)
	 
  'rule' Define_pattern(P, T, id_pattern(P1, I)):
	 Define_id_or_op(P1, I ,T -> _)

  'rule' Define_pattern(P, T, wildcard_pattern(P1)):

  'rule' Define_pattern(P, T, product_pattern(P1, list(PATT,nil))):
	 Define_pattern(P, T, PATT)

  'rule' Define_pattern(P, T, product_pattern(P1, PATTS)):
	 Length_ps(PATTS -> N2)
	 Make_product_type(T, N2 -> T1)
	 where(T1 -> product(PR))
	 Length_pr(PR -> N1)
	 eq(N1, N2)
	 Define_patterns_as_product(P, PR, PATTS)

  'rule' Define_pattern(P, T, enum_list(P1, PATTS)):
	 Make_list_element_type(P1, T -> T1)
	 Define_patterns_as_list(P1, T1, PATTS)

  'rule' Define_pattern(P, T, conc_list(P1,L,R)):
	 Make_list_element_type(P1, T -> T1)
	 Define_patterns_as_list(P1, T1, L)
	 Define_pattern(P, T, R)

-- allow use with resolved patterns
  'rule' Define_pattern(_, _, name_occ_pattern(_, _, _)):

  'rule' Define_pattern(_, _, record_occ_pattern(P, I, _, PATTS)):
	 I'Type -> fun(D,_,_)
	 Define_pattern(P, D, product_pattern(P, PATTS))

  'rule' Define_pattern(P, T, PATT):
	 Puterror(P)
	 Putmsg("Structure of pattern does not match structure of type ")
	 Print_type(T)
	 Putnl()

'action' Define_patterns_as_product(POS, PRODUCT_TYPE, PATTERNS)

  'rule' Define_patterns_as_product(P, list(T, TS), list(PATT, PATTS)):
	 Define_pattern(P, T, PATT)
	 Define_patterns_as_product(P, TS, PATTS)

  'rule' Define_patterns_as_product(P, nil, nil):

'action' Define_patterns_as_list(POS, TYPE_EXPR, PATTERNS)

  'rule' Define_patterns_as_list(P, T, list(PATT, PATTS)):
	 Define_pattern(P, T, PATT)
	 Define_patterns_as_list(P, T, PATTS)

  'rule' Define_patterns_as_list(P, T, nil):


--------------------------------------------------------------------
-- Lookup value name types
--------------------------------------------------------------------

-- Lookup throughout scope
'action' Lookup_value_name(POS, NAME -> Value_ids)

  'rule' Lookup_value_name(P, N -> Ids):
         --print(N)
	 Current -> C
	 Extend_paths -> Paths
-- debug
-- print(C)
--print(Paths)
	 Lookup_current_value_name(N, C, Paths, ownenv, ownclass -> Ids1)
	 (|
	   where(N -> name(_,op_op(Op)))
	   Lookup_op_types(Op -> Ids2)
	 ||
	   where(N -> name(_,id_op(Ident)))
           --print("debug: Looking up id types")
	   Lookup_id_types(Ident -> Ids2)
	 ||
	   where(Value_ids'nil -> Ids2)
	 |)
	 Union_ids(Ids2, Ids1 -> Ids) 
	 [|
	   eq(Ids, nil)
	   Puterror(P)
	   Putmsg("Value name ")
	   Print_name(N)
	   Putmsg(" hidden, renamed, or not defined")
	   Putnl()
	 |]

'action' Lookup_current_value_name(NAME, CURRENT_ENV, PATHS, OWNENV, OWNCLASS -> Value_ids)

  'rule' Lookup_current_value_name(N, C, Paths, Ownenv, Ownclass -> Ids):
	 where(C -> current_env(CE, C1))
	 where(Paths -> list(Path, Paths1))
	 Get_current_path_env(CE, Path -> CE1)
	 (|
	   where(CE1 -> instantiation_env(PF, CE2))
	 ||
	   where(PARAM_FIT'nil -> PF)
	   where(CE1 -> CE2)
	 |)
	 Lookup_env_value_name(N, CE2, Ownenv, Ownclass -> Ids1)
	 (|
	   -- do not look outside own scheme instantiation 
	   eq(Ownclass, ownclass)
	   ne(PF, nil)
	   where(Value_ids'nil -> Ids2)
	 ||
	   Lookup_current_value_name1(N, C, Paths, Ownenv, Ownclass -> Ids2)
	 |)
	 -- inner ones in Ids1 hide outer in Ids2
	 Union_ids(Ids2, Ids1 -> Ids)

  'rule' Lookup_current_value_name(N, nil, Paths, Ownenv, Ownclass -> nil):

'action' Lookup_current_value_name1(NAME, CURRENT_ENV, PATHS, OWNENV, OWNCLASS -> Value_ids)

  'rule' Lookup_current_value_name1(N, C, Paths, Ownenv, Ownclass -> Ids):
	 where(C -> current_env(CE, C1))
	 where(Paths -> list(Path, Paths1))
	 (|
	   eq(Path, nil)
	   Lookup_current_value_name(N, C1, Paths1, Ownenv, Ownclass -> Ids)
	 ||
	   Up1(Path -> Up_path, Up_step)
	   -- check left branch if any before moving up
	   (|
	     where(Up_step -> right(nil))
	     Out_scope(Path -> Path1)
	     Get_current_path_env(CE, Path1 -> CE3)
	     DefaultPos(-> P)
	     Lookup_env_value_name(N, CE3, nil, Ownclass -> Ids1)
	   ||
	     where(Value_ids'nil -> Ids1)
	   |)
	   Get_current_path_env(CE, Up_path -> CE1)
	   (|
	     where(CE1 -> instantiation_env(PF1, _))
	   ||
	     where(PARAM_FIT'nil -> PF1)
	   |)
	   (|
	     eq(Ownclass, ownclass)
	     ne(PF1, nil)
	     where(Value_ids'nil -> Ids2)
	   ||
	     Lookup_current_value_name1(N, C, list(Up_path, Paths1), Ownenv, Ownclass -> Ids2)
	   |)
	   -- inner ones in Ids1 hide outer in Ids2
	   Union_ids(Ids2, Ids1 -> Ids)
	 |)

'action' Lookup_env_value_name(NAME, CLASS_ENV, OWNENV, OWNCLASS -> Value_ids)

  'rule' Lookup_env_value_name(N, nil, Ownenv, Ownclass -> nil):

  'rule' Lookup_env_value_name(N, instantiation_env(PF, CE), Ownenv, Ownclass -> Ids):
	 Lookup_env_value_name(N, CE, OWNENV'nil, OWNCLASS'nil -> Ids)

  'rule' Lookup_env_value_name(N, CE, Ownenv, Ownclass -> Ids):
	 (|
	   -- if not top environment and an unqualified name
	   -- need to adapt
	   ne(Ownenv,ownenv)
	   where(N -> name(P, Id_or_op))
	   Get_env_adapts(CE -> Ad)
	   Adapt(Id_or_op, Ad -> Oid)
	   (|
	     where(Oid -> id(Id_or_op1))
	     where(name(P, Id_or_op1) -> N1)
	   ||
	     where(N -> N1)
	   |)
	 ||
	   (| where(N -> name(P, Id_or_op)) || where(N -> qual_name(P, Obj, Id_or_op)) |)
	   where(id(Id_or_op) -> Oid)
	   where(N -> N1)
         |)
	 (|
	   ne(Oid,nil)
	   (|
	     where(CE -> basic_env(_,VES,_,_,_,_,_,_,_,Objs,_))
	     -- only use withs if own environment
	     (|
	       eq(Ownenv,ownenv)
	       Lookup_value_name1(N1, N1, VES, Objs, ownenv, Ownclass -> Ids)
	     ||
	       Lookup_value_name1(N1, N1, VES, nil, nil, Ownclass -> Ids)
	     |)
	   ||
	     where(CE -> extend_env(CE1, CE2, _, _))
	     Lookup_env_value_name(N1, CE2, Ownenv, Ownclass -> Ids2)
	     Lookup_env_value_name(N1, CE1, Ownenv, Ownclass -> Ids1)
	     -- inner ones in Ids2 hide outer in Ids1
	     Union_ids(Ids1, Ids2 -> Ids)
	   |)
	 ||
	   where(Value_ids'nil -> Ids)
	 |)

'action' Lookup_value_name1(NAME, NAME, VALUE_ENVS, OBJECT_EXPRS, OWNENV, OWNCLASS -> Value_ids)

  'rule' Lookup_value_name1(Base, N, VES, nil, Ownenv, Ownclass -> Ids)
	 Lookup_value_name2(N, VES, Ownenv, Ownclass -> Ids)

  'rule' Lookup_value_name1(Base, N, VES, list(Obj, Objs), Ownenv, Ownclass -> Ids):
	 Lookup_value_name2(N, VES, Ownenv, Ownclass -> Ids1)
	 Qualify_name(Obj, Base -> N1)
	 Lookup_value_name1(Base, N1, VES, Objs, Ownenv, Ownclass -> Ids2)
	 -- inner ones in Ids1 hide outer in Ids2
	 Union_ids(Ids2, Ids1 -> Ids)
	 
'action' Lookup_value_name2(NAME, VALUE_ENVS, OWNENV, OWNCLASS -> Value_ids)

  'rule' Lookup_value_name2(name(P, Id_or_op), VES, Ownenv, Ownclass -> Ids):
	 Lookup_id_or_op(Id_or_op, VES -> Ids)

  'rule' Lookup_value_name2(qual_name(P, Obj, Id_or_op), VES, Ownenv, Ownclass -> Ids):
	 Get_object_id1(Obj, Ownenv, Ownclass -> Oid, PF)
	 (|
	   where(Oid -> object_id(OI))
	   [| -- if object found in fitting don't try to check
	     eq(PF, nil)
	     Object_type_check(Obj, OI)
	   |]
	   OI'Env -> CE
	   (|
	     ne(PF, nil)
	     Fit_name(name(P, Id_or_op), OI, PF -> N1)
	   ||
	     where(name(P, Id_or_op) -> N1)
	   |)
	   Lookup_env_value_name(N1, CE, nil, nil -> Ids)
	 ||
	   -- tempting to give "missing object" error
	   -- but may be result of a with
	   where(Value_ids'nil -> Ids)
	 |)

-- Like Lookup_env_value_name but does not expand withs again
-- Also know not in own environment, so need to adapt
'action' Lookup_env_value_name2(ID_OR_OP, CLASS_ENV -> Value_ids)

  'rule' Lookup_env_value_name2(Id_or_op, nil -> nil):

  'rule' Lookup_env_value_name2(Id_or_op, instantiation_env(PF, CE) -> Ids):
	 Lookup_env_value_name2(Id_or_op, CE -> Ids)

  'rule' Lookup_env_value_name2(Id_or_op, CE -> Ids):
	 Get_env_adapts(CE -> Ad)
	 Adapt(Id_or_op, Ad -> Oid)
	 (|
	   where(Oid -> id(Id_or_op1))
	 ||
	   where(Id_or_op -> Id_or_op1)
	 |)
	 (|
	   ne(Oid,nil)
	   (|
	     where(CE -> basic_env(_,VES,_,_,_,_,_,_,_,_,_))
	     Lookup_id_or_op(Id_or_op1, VES -> Ids)
	   ||
	     where(CE -> extend_env(CE1, CE2, _, _))
	     Lookup_env_value_name2(Id_or_op1, CE2 -> Ids2)
	     Lookup_env_value_name2(Id_or_op1, CE1 -> Ids1)
	     -- inner ones in Ids2 hide outer in Ids1
	     Union_ids(Ids1, Ids2 -> Ids)
	   |)
	 ||
	   where(Value_ids'nil -> Ids)
	 |)

-- lookup only in current environment
'action' Lookup_id_or_op(ID_OR_OP, VALUE_ENVS -> Value_ids)

  'rule' Lookup_id_or_op(Id, list(E,ES) -> Ids):
	 Lookup_id_or_op1(Id, E -> Ids1)
	 Lookup_id_or_op(Id, ES -> Ids2)
	 -- inner ones in Ids1 hide outer in Ids2
	 Union_ids(Ids2, Ids1 -> Ids)

  'rule' Lookup_id_or_op(Id, nil -> nil):
	 
'action' Lookup_id_or_op1(ID_OR_OP, Value_ids -> Value_ids)

  'rule' Lookup_id_or_op1(Id, list(I2, E) -> Ids):
	 I2'Ident -> Id2
	 Equal_id_or_op(Id, Id2)
	 Lookup_id_or_op1(Id, E -> Ids1)
	 Union_ids(list(I2, nil), Ids1 -> Ids) 

  'rule' Lookup_id_or_op1(Id, list(I2, E) -> Ids):
	 Lookup_id_or_op1(Id, E -> Ids) 

  'rule' Lookup_id_or_op1(Id, nil -> nil):

--------------------------------------------------------------------
-- Utilities for sets of type expressions
--------------------------------------------------------------------
-- First parameter contains Ids from outer scopes
-- which can be hidden by those in second parameter from inner scopes
'action' Union_ids(Value_ids, Value_ids -> Value_ids)

  'rule' Union_ids(nil, Ids -> Ids):

  'rule' Union_ids(Ids, nil -> Ids):

  'rule' Union_ids(list(I,Ids), Ids1 -> Ids3):
	 Union_ids(Ids, Ids1 -> Ids2)
	 I'Type -> T
	 (|
	   Type_isin_ids(T, nil, Ids1)
	   where(Ids2 -> Ids3)
	 ||
	   where(Value_ids'list(I, Ids2) -> Ids3)
	 |)

'action' Intersection(TYPE_EXPR, Value_ids -> Value_ids)

  'rule' Intersection(T, list(I, Ids) -> Ids1):
	 Intersection(T, Ids -> Ids2)
	 I'Type -> T1
	 (|
	   Match(T, nil, T1)
	   where(Value_ids'list(I, Ids2) -> Ids1)
	 ||
	   where(Ids2 -> Ids1)
	 |)

  'rule' Intersection(T, nil -> nil):

'action' Intersection_results(RESULTS, RESULTS -> RESULTS)

  'rule' Intersection_results(nil, RS -> nil):

  'rule' Intersection_results(RS, nil -> nil):

  'rule' Intersection_results(list(R,RS), RS1 -> RS4):
	 Intersection_results(RS, RS1 -> RS2)
	 Intersection_result(R, RS1 -> RS3)
	 (|
	   where(RS3 -> list(R1, nil))
	   where(RESULTS'list(R1, RS2) -> RS4)
	 ||
	   where(RS2 -> RS4)
	 |)

'action' Intersection_result(RESULT, RESULTS -> RESULTS)

  'rule' Intersection_result(result(T1,RD1,WR1,IN1,OUT1), list(result(T2,RD2,WR2,IN2,OUT2), RS2) -> RS)
	 (|
	   Match_up(T1, T2 -> T)
-- debug
-- Putmsg("Types ")
-- Print_type(T1)
-- Putmsg(" (")
-- print(T1)
-- Putmsg(") and ")
-- Print_type(T2)
-- Putmsg(" (")
-- print(T2)
-- Putmsg(") match up to ")
-- Print_type(T)
-- Putnl()
	   ne(T, none)
	   Concat_accs(RD1, RD2 -> RD)
	   Concat_accs(WR1, WR2 -> WR)
	   Concat_accs(IN1, IN2 -> IN)
	   Concat_accs(OUT1, OUT2 -> OUT)
	   where(RESULTS'list(result(T,RD,WR,IN,OUT),nil) -> RS)
	 ||
	   Intersection_result(result(T1,RD1,WR1,IN1,OUT1), RS2 -> RS)
	 |)

  'rule' Intersection_result(R, nil -> nil)


'action' Function_intersection(POS, RESULTS, RESULTS -> RESULTS)
-- First argument is set of function, list or map results
-- Second is set of argument results
-- Produces set of possible results of applying a result in the first
-- set to one in the second set

  'rule' Function_intersection(P, nil, RS -> nil):

  'rule' Function_intersection(P, RS, nil -> nil):

  'rule' Function_intersection(P, list(result(T,RD,WR,IN,OUT),RS), RS1 -> RS2):
	 Make_function_type(T -> T1)
	 (|
	   ne(T1,none)
	   Function_intersection1(P, list(result(T1,RD,WR,IN,OUT),RS), RS1 -> RS2)
	 ||
	   Make_map_type(T -> T2)
	   (|
	     ne(T2, none)
	     Function_intersection1(P, list(result(T2,RD,WR,IN,OUT),RS), RS1 -> RS2)
	   ||
	     Make_list_type(T -> T3)
	     (|
	       ne(T3,none)
	       Function_intersection1(P, list(result(T3,RD,WR,IN,OUT),RS), RS1 -> RS2)
	     ||
	       Make_array_type(T -> T4)
               (|
                 ne(T4,none)
                 Function_intersection1(P, list(result(T4,RD,WR,IN,OUT),RS), RS1 -> RS2)
               ||
	       Function_intersection(P, RS, RS1 -> RS2)
               |)
	     |)
	   |)
	 |)

'action' Function_intersection1(POS, RESULTS, RESULTS -> RESULTS)

  'rule' Function_intersection1(P, list(result(fun(T,ARR,R),RD1,WR1,IN1,OUT1),RS), RS1 -> RS2):
	 Make_single_result_types(P, T, RS1, R -> RS3)
	 Add_reads(RD1, RS3 -> RS4)
	 Add_writes(WR1, RS4 -> RS5)
	 Add_ins(IN1, RS5 -> RS6)
	 Add_outs(OUT1, RS6 -> RS7)
	 Function_intersection(P, RS, RS1 -> RS8)
	 Check_ambiguity(P, RS7, RS8)
	 Concat_results(RS7, RS8 -> RS2)

  'rule' Function_intersection1(P, list(result(fin_map(D,R),RD1,WR1,IN1,OUT1),RS), RS1 -> RS2):
	 Make_single_result_types(P, D, RS1, result(R,nil,nil,nil,nil) -> RS3)
	 Add_reads(RD1, RS3 -> RS4)
	 Add_writes(WR1, RS4 -> RS5)
	 Add_ins(IN1, RS5 -> RS6)
	 Add_outs(OUT1, RS6 -> RS7)
	 Function_intersection(P, RS, RS1 -> RS8)
	 Check_ambiguity(P, RS7, RS8)
	 Concat_results(RS7, RS8 -> RS2)

  'rule' Function_intersection1(P, list(result(infin_map(D,R),RD1,WR1,IN1,OUT1),RS), RS1 -> RS2):
	 Make_single_result_types(P, D, RS1, result(R,nil,nil,nil,nil) -> RS3)
	 Add_reads(RD1, RS3 -> RS4)
	 Add_writes(WR1, RS4 -> RS5)
	 Add_ins(IN1, RS5 -> RS6)
	 Add_outs(OUT1, RS6 -> RS7)
	 Function_intersection(P, RS, RS1 -> RS8)
	 Check_ambiguity(P, RS7, RS8)
	 Concat_results(RS7, RS8 -> RS2)

  'rule' Function_intersection1(P, list(result(fin_list(T),RD1,WR1,IN1,OUT1),RS), RS1 -> RS2):
	 Make_single_result_types(P, nat, RS1, result(T,nil,nil,nil,nil) -> RS3)
	 Add_reads(RD1, RS3 -> RS4)
	 Add_writes(WR1, RS4 -> RS5)
	 Add_ins(IN1, RS5 -> RS6)
	 Add_outs(OUT1, RS6 -> RS7)
	 Function_intersection(P, RS, RS1 -> RS8)
	 Check_ambiguity(P, RS7, RS8)
	 Concat_results(RS7, RS8 -> RS2)

  'rule' Function_intersection1(P, list(result(infin_list(T),RD1,WR1,IN1,OUT1),RS), RS1 -> RS2):
	 Make_single_result_types(P, nat, RS1, result(T,nil,nil,nil,nil) -> RS3)
	 Add_reads(RD1, RS3 -> RS4)
	 Add_writes(WR1, RS4 -> RS5)
	 Add_ins(IN1, RS5 -> RS6)
	 Add_outs(OUT1, RS6 -> RS7)
	 Function_intersection(P, RS, RS1 -> RS8)
	 Check_ambiguity(P, RS7, RS8)
	 Concat_results(RS7, RS8 -> RS2)

  'rule' Function_intersection1(P, list(result(array(I,V),RD1,WR1,IN1,OUT1),RS), RS1 -> RS2):
	 Make_single_result_types(P, nat, RS1, result(V,nil,nil,nil,nil) -> RS3)
	 Add_reads(RD1, RS3 -> RS4)
	 Add_writes(WR1, RS4 -> RS5)
	 Add_ins(IN1, RS5 -> RS6)
	 Add_outs(OUT1, RS6 -> RS7)
	 Function_intersection(P, RS, RS1 -> RS8)
	 Check_ambiguity(P, RS7, RS8)
	 Concat_results(RS7, RS8 -> RS2)


  'rule' Function_intersection1(P, list(R,RS), RS1 -> RS2):
-- debug
-- Putmsg("Function types ")
-- Print_results(list(R,RS))
-- Putnl()
-- Putmsg("Argument types ")
-- Print_results(RS1)
-- Putnl()
	 Function_intersection(P, RS, RS1 -> RS2)

'action' Make_single_result_types(POS, TYPE_EXPR, RESULTS, RESULT -> RESULTS)

  'rule' Make_single_result_types(P, T, RS, R -> RS1):
	 Make_result_types(T, RS, R -> RS1)
	 Check_repeated_results(P, RS1)

'action' Check_repeated_results(POS, RESULTS)

  'rule' Check_repeated_results(_, nil):

  'rule' Check_repeated_results(_, list(_, nil)):

  'rule' Check_repeated_results(P, list(R, RS)):
	 Check_ambiguity(P, list(R,nil), RS)
	 Check_repeated_results(P, RS)

'action' Check_ambiguity(POS, RESULTS, RESULTS)

  'rule' Check_ambiguity(P, list(result(T,_,_,_,_), RS), RS1):
	 [|
	   Type_in_results(T, RS1)
	   Puterror(P)
	   Putmsg("Ambiguous application: more than one way to obtain result ")
	   Print_type(T)
	   Putnl()
	 |]
	 Check_ambiguity(P, RS, RS1)

  'rule' Check_ambiguity(_, nil, _):

'condition' Type_in_results(TYPE_EXPR, RESULTS)

  'rule' Type_in_results(T, list(result(T1,_,_,_,_),RS)):
	 (|
	   Match(T, nil, T1)
	 ||
	   Type_in_results(T, RS)
	 |)

'action' Concat_results(RESULTS, RESULTS -> RESULTS)

  'rule' Concat_results(nil, RS -> RS):

  'rule' Concat_results(RS, nil -> RS):

  'rule' Concat_results(list(R, RS), RS1 -> list(R, RS2)):
	 Concat_results(RS, RS1 -> RS2)

'condition' Isin(TYPE_EXPR, DIRECTION, TYPE_EXPRS)

  'rule' Isin(T, Dir, list(T1, TS1)):
	 (| Match(T, Dir, T1) || Isin(T, Dir, TS1) |)

  'rule' Isin(T, Dir, nil):
	 eq(T, any)

'condition' Type_isin_ids(TYPE_EXPR, DIRECTION, Value_ids)

  'rule' Type_isin_ids(T, Dir, list(I, Ids)):
	 I'Type -> T1
	 (| Match(T, Dir, T1) || Type_isin_ids(T, Dir, Ids) |)

  'rule' Type_isin_ids(T, Dir, nil):
	 eq(T, any)

'action' Functions_with_result(RESULTS, TYPE_EXPR -> RESULTS)
-- prunes first argument to those that are functions with
-- result types matching second argument

  'rule' Functions_with_result(list(result(FT,RD,WR,IN,OUT), RS), T -> RS1):
	 Functions_with_result(RS, T -> RS2)
	 (|
	   Make_function_type(FT -> fun(D,AR,RES))
	   where(RES -> result(R,_,_,_,_))
	   Match(R, up, T)
	   where(RESULTS'list(result(fun(D,AR,RES),RD,WR,IN,OUT), RS2) -> RS1)
	 ||
	   where(RS2 -> RS1)
	 |)

  'rule' Functions_with_result(nil, _ -> nil):

'action' Match_results(RESULTS, TYPE_EXPR -> RESULTS)

  'rule' Match_results(list(result(T,RD,WR,IN,OUT),RS), T1 -> RS1):
	 Match_results(RS, T1 -> RS2)
	 (|
	   Match(T, up, T1)
	   where(RESULTS'list(result(T1,RD,WR,IN,OUT),RS2) -> RS1)
	 ||
	   where(RS2 -> RS1)
	 |)

  'rule' Match_results(nil, _ -> nil):

'action' Poly_disambiguate_args(RESULTS -> RESULTS)
-- If the same poly numbers occur in two different parameters in the
-- same argument, they are differentiated by adding 3 to the poly numbers
-- in one parameter as many times as necessary.
-- 3 is chosen for convenience because it is the maximum range
-- occurring in the type of any operator: 1 would do but would
-- probably be slower

  'rule' Poly_disambiguate_args(list(result(product(TS),RD,WR,IN,OUT),RS) -> list(result(product(TS1),RD,WR,IN,OUT),RS1)):
	 where(TS -> list(_,list(_,_)))
	 Poly_disambiguate_prod(nil, TS -> TS1)
-- debug
-- Putmsg("Argument types ")
-- Print_type(product(TS))
-- Putmsg(" changed to ")
-- Print_type(product(TS1))
-- Putnl()
	 Poly_disambiguate_args(RS -> RS1)

  'rule' Poly_disambiguate_args(list(R, RS) -> list(R, RS1)):
	 Poly_disambiguate_args(RS -> RS1)

  'rule' Poly_disambiguate_args(nil -> nil)

'action' Poly_disambiguate_prod(INTS, PRODUCT_TYPE -> PRODUCT_TYPE)

  'rule' Poly_disambiguate_prod(NS, list(T, TS) -> TS1):
	 Collect_polynums(T, nil -> NT)
	 (|
	   ne(NT, nil)
	   (|
	     Intersect_polynums(NT, NS)
	     Increment_polynums(T -> T2)
	     Poly_disambiguate_prod(NS, list(T2, TS) -> TS1)
	   ||
	     Union_polynums(NT, NS -> NS1)
	     Poly_disambiguate_prod(NS1, TS -> TS2)
	     where(PRODUCT_TYPE'list(T, TS2) -> TS1)
	   |)
	 ||
	   Poly_disambiguate_prod(NS, TS -> TS2)
	   where(PRODUCT_TYPE'list(T, TS2) -> TS1)
	 |)

  'rule' Poly_disambiguate_prod(_, nil -> nil)

'sweep' Collect_polynums(ANY, INTS -> INTS)

  'rule' Collect_polynums(TYPE_EXPR'poly(N), NS -> NS1):
	 (|
	   Int_isin(N, NS)
	   where(NS -> NS1)
	 ||
	   where(INTS'list(N, NS) -> NS1)
	 |)

'condition' Contains_polynum(TYPE_EXPR, INT)

  'rule' Contains_polynum(T, N):
	 Collect_polynums(T, nil -> NS)
	 Int_isin(N, NS)

'condition' Intersect_polynums(INTS, INTS)

  'rule' Intersect_polynums(list(N, NS), NS1):
	 (| Int_isin(N, NS1) || Intersect_polynums(NS, NS1) |)

'condition' Int_isin(INT, INTS)

  'rule' Int_isin(N, list(N1, NS)):
	 (| eq(N, N1) || Int_isin(N, NS) |)

'action' Union_polynums(INTS, INTS -> INTS)

  'rule' Union_polynums(list(N, NS), NS1 -> NS2):
	 Union_polynums(NS, NS1 -> NS3)
	 (|
	   Int_isin(N, NS1)
	   where(NS3 -> NS2)
	 ||
	   where(INTS'list(N, NS3) -> NS2)
	 |)

  'rule' Union_polynums(nil, NS -> NS):

'action' Increment_polynums(TYPE_EXPR -> TYPE_EXPR)

  'rule' Increment_polynums(poly(N) -> poly(N+3)):
-- debug
-- Putmsg("Incrementing\n")

  'rule' Increment_polynums(product(TS) -> product(TS1)):
	 Increment_polynums_prod(TS -> TS1)

  'rule' Increment_polynums(fin_set(T) -> fin_set(T1)):
	 Increment_polynums(T -> T1)

  'rule' Increment_polynums(infin_set(T) -> infin_set(T1)):
	 Increment_polynums(T -> T1)

  'rule' Increment_polynums(fin_list(T) -> fin_list(T1)):
	 Increment_polynums(T -> T1)

  'rule' Increment_polynums(infin_list(T) -> infin_list(T1)):
	 Increment_polynums(T -> T1)

  'rule' Increment_polynums(fin_map(D, R) -> fin_map(D1, R1)):
	 Increment_polynums(D -> D1)
	 Increment_polynums(R -> R1)

  'rule' Increment_polynums(infin_map(D, R) -> infin_map(D1, R1)):
	 Increment_polynums(D -> D1)
	 Increment_polynums(R -> R1)

  'rule' Increment_polynums(function(D, A, result(ACCS,R)) -> function(D1, A, result(ACCS,R1))):
	 Increment_polynums(D -> D1)
	 Increment_polynums(R -> R1)

  'rule' Increment_polynums(fun(D, A, result(R,RD,WR,IN,OUT)) -> fun(D1, A, result(R1,RD,WR,IN,OUT))):
	 Increment_polynums(D -> D1)
	 Increment_polynums(R -> R1)

  'rule' Increment_polynums(subtype(single(P,B,T), R) -> subtype(single(P,B,T1), R)):
	 Increment_polynums(T -> T1)

  'rule' Increment_polynums(bracket(T) -> bracket(T1)):
	 Increment_polynums(T -> T1)

  'rule' Increment_polynums(T -> T):

'action' Increment_polynums_prod(PRODUCT_TYPE -> PRODUCT_TYPE)

  'rule' Increment_polynums_prod(list(T, TS) -> list(T1, TS1)):
	 Increment_polynums(T -> T1)
	 Increment_polynums_prod(TS -> TS1)

  'rule' Increment_polynums_prod(nil -> nil):


-------------------------------------------------------------------
-- Results of value literals
-------------------------------------------------------------------

'action' Make_literal_results(VALUE_LITERAL -> RESULTS)

  'rule' Make_literal_results(unit -> list(result(unit,nil,nil,nil,nil),nil)):

  'rule' Make_literal_results(bool_true -> list(result(bool,nil,nil,nil,nil),nil)):

  'rule' Make_literal_results(bool_false -> list(result(bool,nil,nil,nil,nil),nil)):

  'rule' Make_literal_results(int(_) -> list(result(int,nil,nil,nil,nil),nil)):

  'rule' Make_literal_results(real(_) -> list(result(real,nil,nil,nil,nil),nil)):

  'rule' Make_literal_results(text(_) -> list(result(text,nil,nil,nil,nil),nil)):

  'rule' Make_literal_results(char(_) -> list(result(char,nil,nil,nil,nil),nil)):

---------------------------------------------------------------
-- Lookup variable names
---------------------------------------------------------------

'action' Lookup_variable_id(POS, IDENT -> OPT_VARIABLE_ID)
	 
  'rule' Lookup_variable_id(P, Id -> I):
	 Lookup_variable_name(name(P, id_op(Id)) -> I)

'action' Lookup_variable_name(NAME -> OPT_VARIABLE_ID)

  'rule' Lookup_variable_name(N -> I):
	 Current -> C
	 Extend_paths -> Paths
	 Lookup_current_variable_name(N, C, Paths, ownenv, ownclass -> I)

'action' Lookup_current_variable_name(NAME, CURRENT_ENV, PATHS, OWNENV, OWNCLASS -> OPT_VARIABLE_ID)

  'rule' Lookup_current_variable_name(N, C, Paths, Ownenv, Ownclass -> I):
	 where(C -> current_env(CE, C1))
	 where(Paths -> list(Path, Paths1))
	 Get_current_path_env(CE, Path -> CE1)
	 (|
	   where(CE1 -> instantiation_env(PF, CE2))
	 ||
	   where(PARAM_FIT'nil -> PF)
	   where(CE1 -> CE2)
	 |)
	 Lookup_env_variable_name(N, CE2, Ownenv, Ownclass -> Oid)
	 (|
	   ne(Oid,nil)
	   where(Oid -> I)
	 ||
	   (|
	     -- do not look outside own scheme instantiation 
	     eq(Ownclass, ownclass)
	     ne(PF, nil)
	     where(OPT_VARIABLE_ID'nil -> I)
	   ||
	     Lookup_current_variable_name1(N, C, Paths, Ownenv, Ownclass -> I)
	   |)
	 |)

  'rule' Lookup_current_variable_name(N, nil, Paths, Ownenv, Ownclass -> nil)

'action' Lookup_current_variable_name1(NAME, CURRENT_ENV, PATHS, OWNENV, OWNCLASS -> OPT_VARIABLE_ID)

  'rule' Lookup_current_variable_name1(N, C, Paths, Ownenv, Ownclass -> I):
	 where(C -> current_env(CE, C1))
	 where(Paths -> list(Path, Paths1))
	 (|
	   eq(Path, nil)
	   Lookup_current_variable_name(N, C1, Paths1, Ownenv, Ownclass -> I)
	 ||
	   Up1(Path -> Up_path, Up_step)
	   -- check left branch if any before moving up
	   (|
	     where(Up_step -> right(nil))
	     Out_scope(Path -> Path1)
	     Get_current_path_env(CE, Path1 -> CE3)
	     DefaultPos(-> P)
	     Lookup_env_variable_name(N, CE3, nil, Ownclass -> Oid3)
	   ||
	     where(OPT_VARIABLE_ID'nil -> Oid3)
	   |)
	   (|
	     ne(Oid3, nil)
	     where(Oid3 -> I)
	   ||
	     Get_current_path_env(CE, Up_path -> CE1)
	     (|
	       where(CE1 -> instantiation_env(PF1, _))
	     ||
	       where(PARAM_FIT'nil -> PF1)
	     |)
	     (|
	       eq(Ownclass, ownclass)
	       ne(PF1, nil)
	       where(OPT_VARIABLE_ID'nil -> I)
	     ||
	       Lookup_current_variable_name1(N, C, list(Up_path, Paths1), Ownenv, Ownclass -> I)
	     |)
	   |)
	 |)

'action' Lookup_env_variable_name(NAME, CLASS_ENV, OWNENV, OWNCLASS  -> OPT_VARIABLE_ID)

  'rule' Lookup_env_variable_name(N, nil, Ownenv, Ownclass -> nil):

  'rule' Lookup_env_variable_name(N, instantiation_env(PF, CE), Ownenv, Ownclass -> I):
	 Lookup_env_variable_name(N, CE, OWNENV'nil, OWNCLASS'nil -> I)

  'rule' Lookup_env_variable_name(N, CE, Ownenv, Ownclass -> I):
	 (|
	   -- if not own environment and an unqualified name
	   -- need to adapt
	   ne(Ownenv,ownenv)
	   where(N -> name(P, Id_or_op))
	   Get_env_adapts(CE -> Ad)
	   Adapt(Id_or_op, Ad -> Oid)
	   (|
	     where(Oid -> id(Id_or_op1))
	     where(name(P, Id_or_op1) -> N1)
	   ||
	     where(N -> N1)
	   |)
	 ||
	   (| where(N -> name(P, Id_or_op)) || where(N -> qual_name(P, Obj, Id_or_op)) |)
	   where(id(Id_or_op) -> Oid)
	   where(N -> N1)
         |)
	 (|
	   ne(Oid,nil)
	   (|
	     where(CE -> basic_env(_,VES,VARS,_,_,_,_,_,_,Objs,_))
	     -- only use withs if own environment
	     (|
	       eq(Ownenv,ownenv)
	       Lookup_variable_name1(N1, N1, VES, VARS, Objs, ownenv, Ownclass -> I)
	     ||
	       Lookup_variable_name1(N1, N1, VES, VARS, nil, nil, Ownclass -> I)
	     |)
	   ||
	     where(CE -> extend_env(CE1, CE2, _, _))
	     Lookup_env_variable_name(N1, CE2, Ownenv, Ownclass -> I2)
	     (|
	       ne(I2,nil)
	       where(I2 -> I)
	     ||
	       Lookup_env_variable_name(N1, CE1, Ownenv, Ownclass -> I)
	     |)
	   |)
	 ||
	   where(OPT_VARIABLE_ID'nil -> I)
	 |)


'action' Lookup_variable_name1(NAME, NAME, VALUE_ENVS, VARIABLE_ENV, OBJECT_EXPRS, OWNENV, OWNCLASS -> OPT_VARIABLE_ID)

  'rule' Lookup_variable_name1(Base, N, VES, VARS, Objs, Ownenv, Ownclass -> I):
-- debug
-- Putmsg("Looking for variable ")
-- Print_name(N)
-- Putmsg(" with ")
-- Print_objects(Objs)
-- Putnl()
	 Lookup_variable_name2(N, VES, VARS, Ownenv, Ownclass -> I1)
	 (|
	   eq(I1, nil)
	   (|
	     where(Objs -> list(Obj, Objs1))
	     Qualify_name(Obj, Base -> N1)
	     Lookup_variable_name1(Base, N1, VES, VARS, Objs1, Ownenv, Ownclass -> I)
	   ||
	     where(OPT_VARIABLE_ID'nil -> I)
	   |)
	 ||
	   where(I1 -> I)
	 |)

'action' Lookup_variable_name2(NAME, VALUE_ENVS, VARIABLE_ENV, OWNENV, OWNCLASS -> OPT_VARIABLE_ID)

  'rule' Lookup_variable_name2(name(P, id_op(Id)), VES, VARS, Ownenv, Ownclass -> I):
	 Lookup_env_variable_id(Id, VES, VARS -> I)

  'rule' Lookup_variable_name2(name(P, op_op(Id)), _, _, _, _ -> nil):

  'rule' Lookup_variable_name2(qual_name(P, Obj, id_op(Id)), VES, VARS, Ownenv, Ownclass -> I):
	 Get_object_id1(Obj, Ownenv, Ownclass -> Oid, PF)
	 (|
	   where(Oid -> object_id(OI))
	   [| -- if object found in fitting don't try to check
	     eq(PF, nil)
	     Object_type_check(Obj, OI)
	   |]
	   OI'Env -> CE
	   (|
	     ne(PF, nil)
	     Fit_name(name(P, id_op(Id)), OI, PF -> N1)
	   ||
	     where(name(P, id_op(Id)) -> N1)
	   |)
	   Lookup_env_variable_name(N1, CE, nil, nil -> I)
	 ||
	   -- tempting to give "missing object" error
	   -- but may be result of a with
	   where(OPT_VARIABLE_ID'nil -> I)
	 |)

  'rule' Lookup_variable_name2(qual_name(P, _, op_op(Id)), _, _, _, _ -> nil):

-- Like Lookup_env_variable_name but does not expand withs again
-- Also know not in own environment, so need to adapt
'action' Lookup_env_variable_name2(IDENT, CLASS_ENV  -> OPT_VARIABLE_ID)

  'rule' Lookup_env_variable_name2(Id, nil -> nil):

  'rule' Lookup_env_variable_name2(Id, instantiation_env(PF, CE) -> I):
	 Lookup_env_variable_name2(Id, CE -> I)

  'rule' Lookup_env_variable_name2(Id, CE -> I):
	 Get_env_adapts(CE -> Ad)
	 Adapt(id_op(Id), Ad -> Oid)
	 (|
	   where(Oid -> id(id_op(Id1)))
	 ||
	   where(Id -> Id1)
	 |)
	 (|
	   ne(Oid,nil)
	   (|
	     where(CE -> basic_env(_,VES,VARS,_,_,_,_,_,_,_,_))
	     Lookup_env_variable_id(Id1, VES, VARS -> I)
	   ||
	     where(CE -> extend_env(CE1, CE2, _, _))
	     Lookup_env_variable_name2(Id1, CE2 -> I2)
	     (|
	       ne(I2,nil)
	       where(I2 -> I)
	     ||
	       Lookup_env_variable_name2(Id1, CE1 -> I)
	     |)
	   |)
	 ||
	   where(OPT_VARIABLE_ID'nil -> I)
	 |)


-- lookup only in current environment
'action' Lookup_env_variable_id(IDENT, VALUE_ENVS, VARIABLE_ENV -> OPT_VARIABLE_ID)

  'rule' Lookup_env_variable_id(Id, VES, VARS -> I):
	 (|
	   -- inner values hide outer variables
	   Defined_as_inner_value(Id, VES)
	   where(OPT_VARIABLE_ID'nil -> I)
	 ||
	   Lookup_env_variable_id1(Id, VARS -> I)
	 |)

'action' Lookup_env_variable_id1(IDENT, VARIABLE_ENV -> OPT_VARIABLE_ID)

  'rule' Lookup_env_variable_id1(Id, variable_env(I2, E) -> I):
	 I2'Ident -> Id2
	 (|
	   ne(Id,Id2)
	   Lookup_env_variable_id1(Id, E -> I)
	 ||
	   where(variable_id(I2) -> I)
	 |)

  'rule' Lookup_env_variable_id1(Id, nil -> nil):

'condition' Defined_as_inner_value(IDENT, VALUE_ENVS)

  'rule' Defined_as_inner_value(Id, list(VE, list(VE1, VES))):
	 (|
	   Lookup_id_or_op1(id_op(Id), VE -> list(I, Ids))
	 ||
	   Defined_as_inner_value(Id, list(VE1, VES))
	 |)


---------------------------------------------------------------
-- Lookup channel names
---------------------------------------------------------------

'action' Lookup_channel_id(POS, IDENT -> OPT_CHANNEL_ID)
	 
  'rule' Lookup_channel_id(P, Id -> I):
	 Lookup_channel_name(name(P, id_op(Id)) -> I)

'action' Lookup_channel_name(NAME -> OPT_CHANNEL_ID)

  'rule' Lookup_channel_name(N -> I):
	 Current -> C
	 Extend_paths -> Paths
	 Lookup_current_channel_name(N, C, Paths, ownenv, ownclass -> I)

'action' Lookup_current_channel_name(NAME, CURRENT_ENV, PATHS, OWNENV, OWNCLASS -> OPT_CHANNEL_ID)

  'rule' Lookup_current_channel_name(N, C, Paths, Ownenv, Ownclass -> I):
	 where(C -> current_env(CE, C1))
	 where(Paths -> list(Path, Paths1))
	 Get_current_path_env(CE, Path -> CE1)
	 (|
	   where(CE1 -> instantiation_env(PF, CE2))
	 ||
	   where(PARAM_FIT'nil -> PF)
	   where(CE1 -> CE2)
	 |)
	 Lookup_env_channel_name(N, CE2, Ownenv, Ownclass -> Oid)
	 (|
	   ne(Oid,nil)
	   where(Oid -> I)
	 ||
	   (|
	     -- do not look outside own scheme instantiation 
	     eq(Ownclass, ownclass)
	     ne(PF, nil)
	     where(OPT_CHANNEL_ID'nil -> I)
	   ||
	     Lookup_current_channel_name1(N, C, Paths, Ownenv, Ownclass -> I)
	   |)
	 |)

  'rule' Lookup_current_channel_name(N, nil, Paths, Ownenv, Ownclass -> nil)

'action' Lookup_current_channel_name1(NAME, CURRENT_ENV, PATHS, OWNENV, OWNCLASS -> OPT_CHANNEL_ID)

  'rule' Lookup_current_channel_name1(N, C, Paths, Ownenv, Ownclass -> I):
	 where(C -> current_env(CE, C1))
	 where(Paths -> list(Path, Paths1))
	 (|
	   eq(Path, nil)
	   Lookup_current_channel_name(N, C1, Paths1, Ownenv, Ownclass -> I)
	 ||
	   Up1(Path -> Up_path, Up_step)
	   -- check left branch if any before moving up
	   (|
	     where(Up_step -> right(nil))
	     Out_scope(Path -> Path1)
	     Get_current_path_env(CE, Path1 -> CE3)
	     DefaultPos(-> P)
	     Lookup_env_channel_name(N, CE3, nil, Ownclass -> Oid3)
	   ||
	     where(OPT_CHANNEL_ID'nil -> Oid3)
	   |)
	   (|
	     ne(Oid3, nil)
	     where(Oid3 -> I)
	   ||
	     Get_current_path_env(CE, Up_path -> CE1)
	     (|
	       where(CE1 -> instantiation_env(PF1, _))
	     ||
	       where(PARAM_FIT'nil -> PF1)
	     |)
	     (|
	       eq(Ownclass, ownclass)
	       ne(PF1, nil)
	       where(OPT_CHANNEL_ID'nil -> I)
	     ||
	       Lookup_current_channel_name1(N, C, list(Up_path, Paths1), Ownenv, Ownclass -> I)
	     |)
	   |)
	 |)

'action' Lookup_env_channel_name(NAME, CLASS_ENV, OWNENV, OWNCLASS  -> OPT_CHANNEL_ID)

  'rule' Lookup_env_channel_name(N, nil, Ownenv, Ownclass -> nil):

  'rule' Lookup_env_channel_name(N, instantiation_env(PF, CE), Ownenv, Ownclass -> I):
	 Lookup_env_channel_name(N, CE, OWNENV'nil, OWNCLASS'nil -> I)

  'rule' Lookup_env_channel_name(N, CE, Ownenv, Ownclass -> I):
	 (|
	   -- if not own environment and an unqualified name
	   -- need to adapt
	   ne(Ownenv,ownenv)
	   where(N -> name(P, Id_or_op))
	   Get_env_adapts(CE -> Ad)
	   Adapt(Id_or_op, Ad -> Oid)
	   (|
	     where(Oid -> id(Id_or_op1))
	     where(name(P, Id_or_op1) -> N1)
	   ||
	     where(N -> N1)
	   |)
	 ||
	   (| where(N -> name(P, Id_or_op)) || where(N -> qual_name(P, Obj, Id_or_op)) |)
	   where(id(Id_or_op) -> Oid)
	   where(N -> N1)
         |)
	 (|
	   ne(Oid,nil)
	   (|
	     where(CE -> basic_env(_,_,_,CHS,_,_,_,_,_,Objs,_))
	     -- only use withs if own environment
	     (|
	       eq(Ownenv,ownenv)
	       Lookup_channel_name1(N1, N1, CHS, Objs, ownenv, Ownclass -> I)
	     ||
	       Lookup_channel_name1(N1, N1, CHS, nil, nil, Ownclass -> I)
	     |)
	   ||
	     where(CE -> extend_env(CE1, CE2, _, _))
	     Lookup_env_channel_name(N1, CE2, Ownenv, Ownclass -> I2)
	     (|
	       ne(I2,nil)
	       where(I2 -> I)
	     ||
	       Lookup_env_channel_name(N1, CE1, Ownenv, Ownclass -> I)
	     |)
	   |)
	 ||
	   where(OPT_CHANNEL_ID'nil -> I)
	 |)


'action' Lookup_channel_name1(NAME, NAME, CHANNEL_ENV, OBJECT_EXPRS, OWNENV, OWNCLASS -> OPT_CHANNEL_ID)

  'rule' Lookup_channel_name1(Base, N, CHS, Objs, Ownenv, Ownclass -> I):
	 Lookup_channel_name2(N, CHS, Ownenv, Ownclass -> I1)
	 (|
	   eq(I1, nil)
	   (|
	     where(Objs -> list(Obj, Objs1))
	     Qualify_name(Obj, Base -> N1)
	     Lookup_channel_name1(Base, N1, CHS, Objs1, Ownenv, Ownclass -> I)
	   ||
	     where(OPT_CHANNEL_ID'nil -> I)
	   |)
	 ||
	   where(I1 -> I)
	 |)

'action' Lookup_channel_name2(NAME, CHANNEL_ENV, OWNENV, OWNCLASS -> OPT_CHANNEL_ID)

  'rule' Lookup_channel_name2(name(P, id_op(Id)), CHS, Ownenv, Ownclass -> I):
	 Lookup_env_channel_id(Id, CHS -> I)

  'rule' Lookup_channel_name2(qual_name(P, Obj, id_op(Id)), CHS, Ownenv, Ownclass -> I):
	 Get_object_id1(Obj, Ownenv, Ownclass -> Oid, PF)
	 (|
	   where(Oid -> object_id(OI))
	   [| -- if object found in fitting don't try to check
	     eq(PF, nil)
	     Object_type_check(Obj, OI)
	   |]
	   OI'Env -> CE
	   (|
	     ne(PF, nil)
	     Fit_name(name(P, id_op(Id)), OI, PF -> N1)
	   ||
	     where(name(P, id_op(Id)) -> N1)
	   |)
	   Lookup_env_channel_name(N1, CE, nil, nil -> I)
	 ||
	   -- tempting to give "missing object" error
	   -- but may be result of a with
	   where(OPT_CHANNEL_ID'nil -> I)
	 |)

-- Like Lookup_env_channel_name but does not expand withs again
-- Also know not in own environment, so need to adapt
'action' Lookup_env_channel_name2(IDENT, CLASS_ENV  -> OPT_CHANNEL_ID)

  'rule' Lookup_env_channel_name2(Id, nil -> nil):

  'rule' Lookup_env_channel_name2(Id, instantiation_env(PF, CE) -> I):
	 Lookup_env_channel_name2(Id, CE -> I)

  'rule' Lookup_env_channel_name2(Id, CE -> I):
	 Get_env_adapts(CE -> Ad)
	 Adapt(id_op(Id), Ad -> Oid)
	 (|
	   where(Oid -> id(id_op(Id1)))
	 ||
	   where(Id -> Id1)
	 |)
	 (|
	   ne(Oid,nil)
	   (|
	     where(CE -> basic_env(_,_,_,CHS,_,_,_,_,_,_,_))
	     Lookup_env_channel_id(Id1, CHS -> I)
	   ||
	     where(CE -> extend_env(CE1, CE2, _, _))
	     Lookup_env_channel_name2(Id1, CE2 -> I2)
	     (|
	       ne(I2,nil)
	       where(I2 -> I)
	     ||
	       Lookup_env_channel_name2(Id1, CE1 -> I)
	     |)
	   |)
	 ||
	   where(OPT_CHANNEL_ID'nil -> I)
	 |)


-- lookup only in current environment
'action' Lookup_env_channel_id(IDENT, CHANNEL_ENV -> OPT_CHANNEL_ID)

  'rule' Lookup_env_channel_id(Id, channel_env(I2, E) -> I):
	 I2'Ident -> Id2
	 (|
	   ne(Id,Id2)
	   Lookup_env_channel_id(Id, E -> I)
	 ||
	   where(channel_id(I2) -> I)
	 |)

  'rule' Lookup_env_channel_id(Id, nil -> nil):




----------------------------------------------------------------
-- Type check
----------------------------------------------------------------
'action' Check_value_env(CLASS)

  'rule' Check_value_env(CL)
	 Type_check_class(CL)

'action' Type_check_decls(DECLS)

  'rule' Type_check_decls(list(D,DS)):
	 Type_check_decl(D)
	 Type_check_decls(DS)

  'rule' Type_check_decls(nil):

'action' Type_check_class(CLASS)

  'rule' Type_check_class(basic(DS)):
	 Type_check_decls(DS)

  'rule' Type_check_class(instantiation(N, Objs)):
	 (|
	   where(N -> name(P,id_op(Id)))
	 || -- error of using qualified scheme name already reported
	    -- in Make_basic_env
	   where(N -> qual_name(P, _, id_op(Id)))
	 |)
	 [| -- allow for failure to find scheme (already reported)
	   Get_id_of_scheme(Id -> scheme_id(I))
	   I'With -> W	 
	   Set_current_with(W)
	   I'Params -> PARMS
	   I'Class -> CL
	   -- check actuals implement formals
	   Get_current_env(-> instantiation_env(PF, _))
	   Check_implementations(PF, PF)
           -- already checked when loaded, but objects in it may need resolving
	   -- and translators require full qualification of names
	   [|
	     (| CcWanted() || CPPWanted() || SMLWanted() ||FDRWanted() ||
	        PVSWanted() || SALWanted() |)
	     (|
	       HasErrors()
	     ||
	       Type_check_class(CL)
	     |)
	   |]
	 |]

  'rule' Type_check_class(extend(CL1, CL2)):
	 In_left
	 Type_check_class(CL1)
	 Left_right
	 Type_check_class(CL2)
	 Out_right
	 Get_current_env( -> CE)
	 Check_duplicate_defs(CE)
	 
  'rule' Type_check_class(hide(H, C)):
	 Type_check_class(C)

  'rule' Type_check_class(rename(R, C)):
	 Type_check_class(C)

  'rule' Type_check_class(with(P,Obj, C))
	 Type_check_class(C)

'action' Type_check_decl(DECL)

  'rule' Type_check_decl(type_decl(P, Defs)):
	 Type_check_type_defs(Defs)
	 [|
	   CcWanted()
	   Define_axiom_from_type_defs(Defs)
	 |]

  'rule' Type_check_decl(value_decl(P,Defs)):
	 Type_check_value_defs(Defs)

  'rule' Type_check_decl(variable_decl(P,Defs)):
	 Type_check_variable_defs(Defs)

  'rule' Type_check_decl(channel_decl(P,Defs)):
	 Type_check_channel_defs(Defs)

  'rule' Type_check_decl(object_decl(P,Defs)):
	 Type_check_object_defs(Defs)

  'rule' Type_check_decl(axiom_decl(P,Defs)):
	 Type_check_axiom_defs(Defs)

  'rule' Type_check_decl(test_case_decl(P,Defs)):
	 Type_check_test_case_defs(Defs)

  'rule' Type_check_decl(trans_system_decl(P,Defs)):
	 Type_check_trans_sys_defs(Defs)

  'rule' Type_check_decl(property_decl(P, Defs)):
	 Type_check_properties(Defs)

'action' Type_check_type_defs(TYPE_DEFS)

  'rule' Type_check_type_defs(list(D, DS)):
	 Type_check_type_def(D)
	 Type_check_type_defs(DS)

  'rule' Type_check_type_defs(nil):

'action' Type_check_type_def(TYPE_DEF)

  'rule' Type_check_type_def(sort(_,_)):

  'rule' Type_check_type_def(abbrev(_,_,T)):
	 Type_check_type(T)

  'rule' Type_check_type_def(variant(_,_,VS)):
	 Type_check_variants(VS)

  'rule' Type_check_type_def(record(_,_,CS)):
	 Type_check_components(CS)

  'rule' Type_check_type_def(union(_,_,_)):

'action' Type_check_variants(VARIANTS)

  'rule' Type_check_variants(list(V, VS)):
	 Type_check_variant(V)
	 Type_check_variants(VS)

  'rule' Type_check_variants(nil):

'action' Type_check_variant(VARIANT)

  'rule' Type_check_variant(record(_,_,CS)):
	 Type_check_components(CS)

'action' Type_check_components(COMPONENTS)

  'rule' Type_check_components(list(C,CS)):
	 Type_check_component(C)
	 Type_check_components(CS)

  'rule' Type_check_components(nil):

'action' Type_check_component(COMPONENT)

  'rule' Type_check_component(component(_,_,T,_)):
	 Type_check_type(T)

'action' Type_check_type(TYPE_EXPR)

  'rule' Type_check_type(named_type(qual_name(_, Obj, _))):
	 -- existence of object checked elsewhere
	 [|
	   Get_object_id(Obj -> object_id(OI), PF)
	   -- if object found in fitting don't try to check
	   eq(PF, nil)
	   Object_type_check(Obj, OI)
	 |]

  'rule' Type_check_type(product(PR)):
	 Type_check_product_subtypes(PR)

  'rule' Type_check_type(fin_set(T)):
	 Type_check_type(T)

  'rule' Type_check_type(infin_set(T)):
	 Type_check_type(T)

  'rule' Type_check_type(fin_list(T)):
	 Type_check_type(T)

  'rule' Type_check_type(infin_list(T)):
	 Type_check_type(T)

  'rule' Type_check_type(fin_map(D, R)):
	 Type_check_type(D)
	 Type_check_type(R)

  'rule' Type_check_type(infin_map(D, R)):
	 Type_check_type(D)
	 Type_check_type(R)

  'rule' Type_check_type(function(D,_,result(ACC,R))):
	 Type_check_type(D)
	 Type_check_type(R)
	 -- needed again (done in types module)
	 -- since array objects now have their type parameters
	 Check_access_defined(ACC, nil, nil, nil, nil -> _,_,_,_)

  'rule' Type_check_type(fun(D,_,result(R,RD,WR,IN,OUT))):
	 Type_check_type(D)
	 Type_check_type(R)

  'rule' Type_check_type(subtype(single(P,B,T),restriction(P1,V))):
	 Type_check_type(T)
	 Openenv()
	 Define_value_binding(B, T)
	 Make_results(V -> RS)
	 Type_check(P1, result(bool,nil,nil,nil,nil), RS -> RS1)
	 Closeenv()

  'rule' Type_check_type(bracket(T)):
	 Type_check_type(T)

  'rule' Type_check_type(array(D,R)):
         Type_check_type(D)
         Type_check_type(R)

-- otherwise
  'rule' Type_check_type(T):
-- debug
         --print(T)

'action' Type_check_product_subtypes(PRODUCT_TYPE)

  'rule' Type_check_product_subtypes(list(T, PR)):
	 Type_check_type(T)
	 Type_check_product_subtypes(PR)

  'rule' Type_check_product_subtypes(nil):

'action' Type_check_accs(ACCESSES)

  'rule' Type_check_accs(list(A, AS)):
	 Type_check_acc(A)
	 Type_check_accs(AS)

  'rule' Type_check_accs(nil):

'action' Type_check_acc(ACCESS)

  'rule' Type_check_acc(free):

  'rule' Type_check_acc(enumerated_access(_, AS)):
	 Type_check_accs(AS)

  'rule' Type_check_acc(completed_access(_, nil)):

  'rule' Type_check_acc(completed_access(_, qualification(Obj))):
	 Type_check_object(Obj)

  'rule' Type_check_acc(comprehended_access(_, A, set_limit(P1, TS, R))):
	 Type_check_typings(TS)
	 Openenv()
	 Define_value_typings(TS)
	 Type_check_acc(A)
	 [|
	   where(R -> restriction(P2,V2))
	   Make_results(V2 -> RS2)
	   Type_check(P2, result(bool,list(free,nil),nil,nil,nil), RS2 -> _)
	 |]
	 Closeenv()
	 

  'rule' Type_check_acc(variable(_, _, Q))
	 Type_check_opt_qual(Q)

  'rule' Type_check_acc(channel(_, _, Q))
	 Type_check_opt_qual(Q)

'action' Type_check_object(OBJECT_EXPR)

  'rule' Type_check_object(Obj):
	 -- existence of object checked elsewhere
	 [|
	   Get_object_id(Obj -> object_id(I), PF)
	   -- if object found in fitting don't try to check
	   eq(PF, nil)
	   Object_type_check(Obj, I)
	 |]

'action' Type_check_opt_qual(OPT_QUALIFICATION)

  'rule' Type_check_opt_qual(qualification(Obj)):
	 Type_check_object(Obj)

  'rule' Type_check_opt_qual(nil):

'action' Type_check_typings(TYPINGS)

  'rule' Type_check_typings(list(TP, TPS)):
	 Type_check_typing(TP)
	 Type_check_typings(TPS)

  'rule' Type_check_typings(nil):

'action' Type_check_typing(TYPING)

  'rule' Type_check_typing(single(_,_,T)):
	 Type_check_type(T)

  'rule' Type_check_typing(multiple(_,_,T)):
	 Type_check_type(T)


'action' Type_check_value_defs(VALUE_DEFS)

  'rule' Type_check_value_defs(list(H,T)):
	 Type_check_value_def(H)
	 Type_check_value_defs(T)

  'rule' Type_check_value_defs(nil)

'action' Type_check_variable_defs(VARIABLE_DEFS)

  'rule' Type_check_variable_defs(list(H,T)):
	 Type_check_variable_def(H)
	 Type_check_variable_defs(T)

  'rule' Type_check_variable_defs(nil):

'action' Type_check_variable_def(VARIABLE_DEF)

  'rule' Type_check_variable_def(single(P, Id, T, Init)):
	 Type_check_type(T)
	 Get_current_variables(-> VARS)
	 Lookup_env_variable_id(Id, nil, VARS -> variable_id(I))
	 I'Type -> T1
	 [|
	   where(Init -> initial(V))
	   Make_results(V -> RS)
	   Type_check(P, result(T1,nil,nil,nil,nil), RS -> RS1)
	 |]
	 Check_self_read_or_write_access(T1, I)

  'rule' Type_check_variable_def(multiple(P, Ids, T)):
	 Type_check_type(T)
	 Check_self_read_or_write_accesses(Ids)

'action' Check_self_read_or_write_accesses(IDENTS)

  'rule' Check_self_read_or_write_accesses(list(Id, Ids)):
	 Get_current_variables(-> VARS)
	 Lookup_env_variable_id(Id, nil, VARS -> variable_id(I))
	 I'Type -> T
	 Check_self_read_or_write_access(T, I)
	 Check_self_read_or_write_accesses(Ids)

  'rule' Check_self_read_or_write_accesses(nil):

'sweep' Check_self_read_or_write_access(ANY, Variable_id)

  'rule' Check_self_read_or_write_access(fun(T, Arr, result(R, RD, WR, IN, OUT)), I):
	 I'Pos -> P
	 [|
	   (| Included1(variable(P,I,nil), RD) || Included1(variable(P,I,nil), WR) |)
	   I'Ident -> Id
	   I'Type -> T1
	   Puterror(P)
	   Putmsg("Type of variable ")
	   Print_type(T1)
	   Putmsg(" depends on ")
	   Print_id(Id)
	   Putnl()
	 |]

'action' Type_check_channel_defs(CHANNEL_DEFS)

  'rule' Type_check_channel_defs(list(H,T)):
	 Type_check_channel_def(H)
	 Type_check_channel_defs(T)

  'rule' Type_check_channel_defs(nil):

'action' Type_check_channel_def(CHANNEL_DEF)

  'rule' Type_check_channel_def(single(P, Id, T)):
	 Type_check_type(T)
	 Get_current_channels(-> CHS)
	 Lookup_env_channel_id(Id, CHS -> channel_id(I))
	 I'Type -> T1
	 Check_self_in_or_out_access(T1, I)

  'rule' Type_check_channel_def(multiple(P, Ids, T)):
	 Type_check_type(T)
	 Check_self_in_or_out_accesses(Ids)

'action' Check_self_in_or_out_accesses(IDENTS)

  'rule' Check_self_in_or_out_accesses(list(Id, Ids)):
	 Get_current_channels(-> CHS)
	 Lookup_env_channel_id(Id, CHS -> channel_id(I))
	 I'Type -> T
	 Check_self_in_or_out_access(T, I)
	 Check_self_in_or_out_accesses(Ids)

  'rule' Check_self_in_or_out_accesses(nil):

'sweep' Check_self_in_or_out_access(ANY, Channel_id)

  'rule' Check_self_in_or_out_access(fun(T, Arr, result(R, RD, WR, IN, OUT)), I):
	 I'Pos -> P
	 [|
	   (| Included1(channel(P,I,nil), IN) || Included1(channel(P,I,nil), OUT) |)
	   I'Ident -> Id
	   I'Type -> T1
	   Puterror(P)
	   Putmsg("Type of channel ")
	   Print_type(T1)
	   Putmsg(" depends on ")
	   Print_id(Id)
	 |]

'action' Type_check_object_defs(OBJECT_DEFS)

  'rule' Type_check_object_defs(list(H,T)):
	 Type_check_object_def(H)
	 Type_check_object_defs(T)

  'rule' Type_check_object_defs(nil)

'action' Type_check_object_def(OBJECT_DEF)

  'rule' Type_check_object_def(odef(P, Id, TS, CL)):
	 [| -- hidden or missing object reported earlier
	    -- in Make_object_type_env_def
	   Type_check_typings(TS)
	   Get_current_modules(-> ME)
	   Lookup_object_in_module(Id, ME -> object_id(I))
	   Current -> C
	   I'Param_env -> PCE
	   I'Env -> CE
	   Current <- current_env(CE,current_env(PCE,C))
	   Extend_paths -> Paths
	   Extend_paths <- list(nil,list(nil,Paths))
	   Check_value_env(CL)
	   Current -> current_env(CE1,current_env(PCE1,C1))
	   Qualify_class_env(I, CE1 -> CE2)
	   Current <- current_env(CE2,current_env(PCE1,C1))
	   I'Env <- CE2
	   Extend_paths <- Paths
	   Current <- C1
	 |]

'action' Type_check_axiom_defs(AXIOM_DEFS)

  'rule' Type_check_axiom_defs(list(H,T)):
	 Type_check_axiom_def(H)
	 Type_check_axiom_defs(T)

  'rule' Type_check_axiom_defs(nil)

'action' Type_check_test_case_defs(TEST_CASE_DEFS)

  'rule' Type_check_test_case_defs(list(H,T)):
	 Type_check_test_case_def(H)
	 Type_check_test_case_defs(T)

  'rule' Type_check_test_case_defs(nil)

'action' Type_check_trans_sys_defs(TRANSITION_SYS_DEFS)

  'rule' Type_check_trans_sys_defs(list(H,T)):
	 Type_check_trans_sys_def(H)
	 Type_check_trans_sys_defs(T)

  'rule' Type_check_trans_sys_defs(nil)

'action' Type_check_properties(PROPERTY_DECLS)

  'rule' Type_check_properties(list(H,T)):
	 Type_check_property_def(H)
	 Type_check_properties(T)

  'rule' Type_check_properties(nil)

'action' Type_check_value_def(VALUE_DEF)

  'rule' Type_check_value_def(typing(P,TP)):
	 Type_check_typing(TP)

  'rule' Type_check_value_def(exp_val(P,TP,V))
	 Defined_type_of_typing(TP -> T)
	 Type_check_type(T)
	 Make_results(V -> RS)
	 Type_check(P, result(T,nil,nil,nil,nil), RS -> RS1)
	 Remove_duplicates(RS1 -> RS2)
	 [|
	   where(RS2 -> list(_, list(_, _)))
	   Puterror(P)
	   Putmsg("Unresolvable overloading between types ")
	   Print_results(RS2)
	   Putnl()
	 |]

  'rule' Type_check_value_def(imp_val(P,TP,R))
	 Type_check_typing(TP)
	 [|
	   where(R -> restriction(P3,V))
	   Make_results(V -> RS)
	   Type_check(P, result(bool,nil,nil,nil,nil), RS -> RS1)
	 |]

  'rule' Type_check_value_def(exp_fun(P, T, A, E, POST, PRE, _)):
	 Check_fun_name(P, T, A)
	 -- make type defined and in fun(...) form
	 Defined_type_of_typing(T -> T2)
	 Type_check_type(T2)
	 Openenv()
	 where(A -> form_appl(P2, Id_or_op, PARS))
	 Result_type(P, T2, PARS -> T3)
	 [|
	   where(POST -> post(PC))
	   where(T3 -> result(T4,_,_,_,_))
	   Type_check_post_cond(T4, PC)
	 |]
	 Type_check_pre_cond(PRE)
	 Make_results(E -> RS)
	 Type_check(P, T3, RS -> RS1)
         Closeenv()

  'rule' Type_check_value_def(imp_fun(P, T, A, POST, PRE)):
	 Check_fun_name(P, T, A)
	 -- make type defined and in fun(...) form
	 Defined_type_of_typing(T -> T2)
	 Type_check_type(T2)
	 Openenv()
	 where(A -> form_appl(P4, Id_or_op, PARS))
	 Result_type(P, T2, PARS -> result(T3,_,_,_,_))
	 Type_check_post_cond(T3, POST)
	 Type_check_pre_cond(PRE)
         Closeenv()

-- debug
--   'rule' Type_check_value_def(D):
-- print(D)

'action' Type_check_post_cond(TYPE_EXPR, POST_CONDITION)

  'rule' Type_check_post_cond(T, post_cond(P, R, C)):
	 (|
	   where(R -> result(_, B))
	   Openenv()
	   Define_value_binding(B, T)
	   Make_results(C -> CTS)
	   Type_check(P, result(bool,list(free,nil),nil,nil,nil), CTS -> _)
           Closeenv()
	 ||
	   Make_results(C -> CTS)
	   Type_check(P, result(bool,list(free,nil),nil,nil,nil), CTS -> _)
	 |)
	 
'action' Type_check_pre_cond(PRE_CONDITION)

  'rule' Type_check_pre_cond(pre_cond(PP, PV)):
	 Make_results(PV -> PRS)
	 Type_check(PP, result(bool,list(free,nil),nil,nil,nil), PRS -> _)

  'rule' Type_check_pre_cond(nil):

'action' Check_duplicate_defs(CLASS_ENV)

  'rule' Check_duplicate_defs(instantiation_env(_,CE)):
	 Check_duplicate_defs(CE)

  'rule' Check_duplicate_defs(extend_env(CE1, CE2, W, AD)):
	 Get_env_top_values(CE2 -> VE)
	 Check_duplicate_values(VE, CE1)
	 Get_env_variables(CE2 -> VARS)
	 Check_duplicate_variables(VARS, CE1)
	 Get_env_channels(CE2 -> CHS)
	 Check_duplicate_channels(CHS, CE1)
	 Get_env_axioms(CE2 -> AXS)
	 Get_env_axioms(CE1 -> AXS1)
	 Check_duplicate_axioms(AXS, AXS1)
	 Get_env_test_cases(CE2, top -> TCS)
	 (|
	   where(CE1 -> instantiation_env(_,_))
	   where(TEST_CASE_ENV'nil -> TCS1)
	 ||
	   Get_env_test_cases(CE1, top -> TCS1)
	 |)
	 Check_duplicate_test_cases(TCS, TCS1)

'action' Check_duplicate_values(Value_ids, CLASS_ENV)

  'rule' Check_duplicate_values(list(I, VE), CE):
	 I'Ident -> Id
	 I'Pos -> P
	 I'Type -> T
	 Lookup_env_value_name2(Id, CE -> Ids)
	 [|
	   Type_isin_ids(T, nil, Ids)
	   ne(T, any) -- error reported elsewhere
	   Puterror(P)
	   Putmsg("Value identifier ")
	   Print_id_or_op(Id)
	   Putmsg(" defined twice with type ")
	   Print_type(T)
	   Putnl()
	 |]
	 Check_duplicate_values(VE, CE)

  'rule' Check_duplicate_values(nil, CE):

'action' Check_duplicate_variables(VARIABLE_ENV, CLASS_ENV)

  'rule' Check_duplicate_variables(variable_env(I, VARS), CE):
	 I'Ident -> Id
	 I'Pos -> P
	 [|
	   Lookup_env_variable_name2(Id, CE -> variable_id(I1))
	   I1'Pos -> P1
	   Puterror(P)
	   Putmsg("Variable identifier ")
	   Print_id(Id)
	   Putmsg(" already defined at ")
	   PrintPos(P1)
	   Putnl()
	 |]
	 Check_duplicate_variables(VARS, CE)

  'rule' Check_duplicate_variables(nil, CE):

'action' Check_duplicate_channels(CHANNEL_ENV, CLASS_ENV)

  'rule' Check_duplicate_channels(channel_env(I, CHS), CE):
	 I'Ident -> Id
	 I'Pos -> P
	 [|
	   Lookup_env_channel_name2(Id, CE -> channel_id(I1))
	   I1'Pos -> P1
	   Puterror(P)
	   Putmsg("Channel identifier ")
	   Print_id(Id)
	   Putmsg(" already defined at ")
	   PrintPos(P1)
	   Putnl()
	 |]
	 Check_duplicate_channels(CHS, CE)

  'rule' Check_duplicate_channels(nil, CE):

'action' Check_duplicate_axioms(AXIOM_ENV, AXIOM_ENV)

  'rule' Check_duplicate_axioms(axiom_env(I, AXS), AXS1):
	 [|
	   I'Ident -> ident(Id)
	   Is_defined_axiom(Id, AXS1)
	   I'Pos -> P
	   Puterror(P)
	   Putmsg("Axiom name ")
	   Print_id(Id)
	   Putmsg(" used twice")
	   Putnl()
	 |]
	 Check_duplicate_axioms(AXS, AXS1)

  'rule' Check_duplicate_axioms(nil, AXS1):

'action' Check_duplicate_test_cases(TEST_CASE_ENV, TEST_CASE_ENV)

  'rule' Check_duplicate_test_cases(test_case_env(I, TCS), TCS1):
	 [|
	   I'Ident -> ident(Id)
	   Is_defined_test_case(Id, TCS1)
	   I'Pos -> P
	   Puterror(P)
	   Putmsg("Test case name ")
	   Print_id(Id)
	   Putmsg(" used twice")
	   Putnl()
	 |]
	 Check_duplicate_test_cases(TCS, TCS1)

  'rule' Check_duplicate_test_cases(nil, TCS1):

'action' Remove(TYPE_EXPR, TYPE_EXPRS -> TYPE_EXPRS)

  'rule' Remove(T, list(T1, TS) -> TS1):
	 (|
	   eq(T, T1)
	   where(TS -> TS1)
	 ||
	   Remove(T, TS -> TS2)
	   where(TYPE_EXPRS'list(T1, TS2) -> TS1)
	 |)

  'rule' Remove(T, nil -> nil):
	 
  
'action' Check_fun_name(POS, TYPING, FORMAL_FUNCTION_APPLICATION)

  'rule' Check_fun_name(P, single(P1,single(P2,I1),T), form_appl(P3, I2, PS)):
	 Equal_id_or_op(I1, I2)
	 
  'rule' Check_fun_name(P, T, A):
	 Puterror(P)
	 Putmsg("Formal function name does not match signature")
	 Putnl()

'action' Result_type(POS, TYPE_EXPR, FORMAL_FUNCTION_PARAMETERS -> RESULT)

  'rule' Result_type(P, bracket(T), PARS -> T2):
	 Result_type(P, T, PARS -> T2)

  'rule' Result_type(P, subtype(single(P2,B,T),R), PARS -> T2):
	 Result_type(P, T, PARS -> T2)

  'rule' Result_type(P, fun(T, A, R), list(form_parm(P2,nil), nil) -> R):
	 Match(T, nil, unit)  

  'rule' Result_type(P, fun(T, A, R), list(form_parm(P2,BS), nil) -> R):
	 Define_value_bindings(P, BS, T)

  'rule' Result_type(P, fun(T, A, R), list(form_parm(P2,nil), PARS) -> result(T2,RD,WR,IN,OUT)):
	 Match(T, nil, unit)  
	 where(R -> result(T1,RD1,WR1,IN1,OUT1))
	 Result_type(P, T1, PARS -> result(T2,RD2,WR2,IN2,OUT2))
	 Concat_accs(RD1, RD2 -> RD)
	 Concat_accs(WR1, WR2 -> WR)
	 Concat_accs(IN1, IN2 -> IN)
	 Concat_accs(OUT1, OUT2 -> OUT)
	 

  'rule' Result_type(P, fun(T, A, R), list(form_parm(P2,BS), PARS) -> result(T2,RD,WR,IN,OUT)):
	 Define_value_bindings(P, BS, T)
	 where(R -> result(T1,RD1,WR1,IN1,OUT1))
	 Result_type(P, T1, PARS -> result(T2,RD2,WR2,IN2,OUT2))
	 Concat_accs(RD1, RD2 -> RD)
	 Concat_accs(WR1, WR2 -> WR)
	 Concat_accs(IN1, IN2 -> IN)
	 Concat_accs(OUT1, OUT2 -> OUT)

  'rule' Result_type(P, T, PARS -> result(any,nil,nil,nil,nil)):
	 Puterror(P)
	 Putmsg("More parameters than arrows in signature")
	 Putnl()
  
'action' Type_check_axiom_def(AXIOM_DEF)

  'rule' Type_check_axiom_def(axiom_def(P,N,V)):
         Make_results(V -> RS)
	 Type_check(P, result(bool,list(free,nil),nil,nil,nil), RS -> RS1)

'action' Type_check_test_case_def(TEST_CASE_DEF)

  'rule' Type_check_test_case_def(test_case_def(P,N,V)):
	 Make_unique_result(P, V -> _)

'action' Type_check_trans_sys_def(TRANSITION_SYS_DEF)

  'rule' Type_check_trans_sys_def(trans_sys_def(P,_,Defs)):
	 where(Defs -> desc(Input, Local, Transitions))
-----------------
	 Get_current_with(-> WITH)
	 Current -> C
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 -- Add implicitely the 'primed variables' (future state vars in SAL)
	 where(Input -> variable_decl(PI, InputDecl))
	 Generate_Primes(InputDecl -> InputPrimes)
	 where(Local -> variable_decl(PL, LocalDecl))
	 Generate_Primes(LocalDecl -> LocalPrimes)
	 -- Collect the input and local declarations
	 where(DECLS'list(Input,list(variable_decl(PI, InputPrimes), list(Local,list(variable_decl(PL, LocalPrimes), nil)))) -> DS)
	 Make_basic_env(basic(DS))
	 Complete_type_env(basic(DS))
	 Make_value_env(basic(DS))
	 Check_value_env(basic(DS))
	 Type_check_transitions(P, Transitions)
----------------------------
	 Current -> current_env(CE, C1)
	 Current <- C1
	 Extend_paths <- Paths

  'rule' Type_check_trans_sys_def(trans_sys_def(P,_,Defs)):
	 where(Defs -> no_input(Local, Transitions))
-----------------
	 Get_current_with(-> WITH)
	 Current -> C
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 -- Add implicitely the 'primed variables' (future state vars in SAL)
	 where(Local -> variable_decl(PL, LocalDecl))
	 Generate_Primes(LocalDecl -> LocalPrimes)
	 -- Collect the input and local declarations
	 where(DECLS'list(Local,list(variable_decl(PL, LocalPrimes), nil)) -> DS)
	 Make_basic_env(basic(DS))
	 Complete_type_env(basic(DS))
	 Make_value_env(basic(DS))
	 Check_value_env(basic(DS))
	 Type_check_transitions(P, Transitions)
----------------------------
	 Current -> current_env(CE, C1)
	 Current <- C1
	 Extend_paths <- Paths

/*'action' Type_check_transitions(POS, TRANSITION_SETS)

  'rule' Type_check_transitions(P, list(H, nil)):
         Type_check_transitionset(P, H)

  'rule' Type_check_transitions(P, list(H, Rest)):
         Type_check_transitionset(P, H)
         Type_check_transitions(P, Rest)*/

'action' Type_check_transitions(POS, TRANSITION_OPERATOR)
  'rule' Type_check_transitions(P, equal_priority(LEFT,RIGHT,GUARD)):
         Type_check_transitions_else_not_allowed(P, LEFT)
         Type_check_transitions(P, RIGHT)

  'rule' Type_check_transitions(P, greater_priority(LEFT, RIGHT,GUARD)):
         Type_check_transitions_else_not_allowed(P, LEFT)
         Type_check_transitions(P, RIGHT)

  'rule' Type_check_transitions(P, bracketed(O,GUARD)):
         Type_check_transitions(P, O)

  'rule' Type_check_transitions(P, guarded_command(CM,GUARD)):
         Type_check_transition(P, CM)

'action' Type_check_transitions_else_not_allowed(POS, TRANSITION_OPERATOR)
  'rule' Type_check_transitions_else_not_allowed(P, equal_priority(LEFT,RIGHT,GUARD)):
         Type_check_transitions_else_not_allowed(P, LEFT)
         Type_check_transitions_else_not_allowed(P, RIGHT)

  'rule' Type_check_transitions_else_not_allowed(P, greater_priority(LEFT, RIGHT,GUARD)):
         Type_check_transitions_else_not_allowed(P, LEFT)
         Type_check_transitions_else_not_allowed(P, RIGHT)

  'rule' Type_check_transitions_else_not_allowed(P, bracketed(O,GUARD)):
         Type_check_transitions_else_not_allowed(P, O)

  'rule' Type_check_transitions_else_not_allowed(P, guarded_command(CM,_)):
	 where(CM -> else_cmd(_, _))
	 Puterror(P)
	 Putmsg("No guarded command allowed after the default action (else guarded transition).\n") 

  'rule' Type_check_transitions_else_not_allowed(P, guarded_command(CM,GUARD)):
         Type_check_transition(P, CM)



'action' Type_check_transition(POS, GUARDED_COMMAND)

  'rule' Type_check_transition(P, guarded_cmd(_,Guard,Cmds)):
	 Make_unique_result(P, Guard -> GuardResult)
         Type_check(P, result(bool,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), list(GuardResult,nil) -> _)
	 Type_check_commands(Cmds)

  'rule' Type_check_transition(P, comprehended_cmd(TPS, Pos, Cmd)):
	 Type_check_typings(TPS)
	 Openenv()
	 Define_value_typings(TPS)
	 Type_check_transition(Pos, Cmd)
	 Closeenv()

  'rule' Type_check_transition(P, else_cmd(_, Cmds)):
	 Type_check_commands(Cmds)

---------------------------------------------------------------------------------------

'action' Type_check_commands(COMMANDS)

  'rule' Type_check_commands(list(cmd(P,N,V),Cmds))
--------------	 
         (|
	   Lookup_variable_name(N -> variable_id(I))
	   I'Type -> T
	   Make_results(V -> RS)
	   Type_check(P, result(T,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RS -> RS1)
	   Add_accesses(RS1, list(result(unit,nil,list(variable(P,I,nil),nil),nil,nil),nil) -> RS2)
	   (|
	       Is_primed_Name(N)
	   ||
	       Puterror(P)
	       Putmsg("Only next state variables allowed in the left hand side part of the guarded commands\n")
	   |)
	 ||
	   Puterror(P)
	   Putmsg("Variable name ")
	   Print_name(N)
	   Putmsg(" hidden, renamed, or not defined")
	   Putnl()
	   Make_results(V -> RS)
	   Add_accesses(RS, list(result(unit,nil,nil,nil,nil),nil) -> RS2)
	 |)

------------
--	 Make_unique_result(P, E -> _)
	 Type_check_commands(Cmds)

  'rule' Type_check_commands(list(array_cmd(P,N,In,V),Cmds))
--------------	 
         (|
	   Lookup_variable_name(N -> variable_id(I))
           I'Type -> Type
	   Make_results(V -> RSA)
           Make_results_for_array_occ(Type, In, P -> RSB)
           (|
             where(RSB -> list(R1,_))
             where(R1 -> result(T,_,_,_,_))
	     Type_check(P, result(T,list(free,nil),list(free,nil),list(free,nil),list(free,nil)), RSA -> RSA1)           
	     (|
	         Is_primed_Name(N)
	     ||
	         Puterror(P)
	         Putmsg("Only next state variables allowed in the left hand side part of the guarded commands\n")
	     |)
           ||
             where(RSB -> nil)
           |)
	 ||
	   Puterror(P)
	   Putmsg("Variable name ")
	   Print_name(N)
	   Putmsg(" hidden, renamed, or not defined")
	   Putnl()
	   Make_results(V -> RS)
	   Add_accesses(RS, list(result(unit,nil,nil,nil,nil),nil) -> RS2)
	 |)

------------
--	 Make_unique_result(P, E -> _)
	 Type_check_commands(Cmds)


  'rule' Type_check_commands(nil)

  'rule' Type_check_commands(list(H,T))
         print("Missing rule for: ")
         print(H)
         print("\n")
         Type_check_commands(T)

'condition' Is_primed_Name(NAME)

  'rule' Is_primed_Name(name(_,id_op(Ident)))
	 id_to_string(Ident -> Str)
	 Is_primed(Str)

  'rule' Is_primed_Name(qual_name(_,_,id_op(Ident)))
	 id_to_string(Ident -> Str)
	 Is_primed(Str)


---------------------------------------------------------------------------------------------------------
-- Type checking for LTL properties:
---------------------------------------------------------------------------------------------------------
'action' Type_check_property_def(PROPERTY_DECL)

  'rule' Type_check_property_def(property_def(Pos, Name, Ident, LTL_prop)):
	 FDRWanted()
	 Set_Has_LTL()
	 (|
	   Lookup_value_name(Pos, name(Pos, id_op(Ident)) -> list(_, nil))
	 ||
	   Puterror(Pos)
	   Putmsg("Cannot find process ")
	   Print_id(Ident)
	   Putnl()
	 |)
	 -- Enable the use of LTL operators:
	 Set_LTL_Wanted()
	 Make_results(LTL_prop -> PRS)
	 Type_check(Pos, result(bool,list(free,nil),nil,nil,nil), PRS -> _)
	 -- Disable the use of LTL operators:
	 Clear_LTL_Wanted()

  'rule' Type_check_property_def(property_def(Pos, Name, TS, LTL_prop)):
	 Get_current_transition_systems(all -> TS_env)
	 Get_Transition_System(TS, TS_env -> OptTSId)
	 where(OptTSId -> ts_id(TSId))
	 TSId'System -> TS_Decls

	  ---------------------------------------------------------
	 where(TS_Decls -> desc(Input, Local, Transitions))
	 -- Puth the valid variables (from the TS) in the current new env:
	 Get_current_with(-> WITH)
	 Current -> C
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 -- Add implicitely the 'primed variables' (future state vars in SAL)
	 where(Input -> variable_decl(PI, InputDecl))
	 Generate_Primes(InputDecl -> InputPrimes)
	 where(Local -> variable_decl(PL, LocalDecl))
	 Generate_Primes(LocalDecl -> LocalPrimes)
	 -- Collect the input and local declarations
	 where(DECLS'list(Input,list(variable_decl(PI, InputPrimes), list(Local,list(variable_decl(PL, LocalPrimes), nil)))) -> DS)
	 Make_basic_env(basic(DS))
	 Complete_type_env(basic(DS))
	 Make_value_env(basic(DS))
	 -- Enable the use of LTL operators:
	 Set_LTL_Wanted()
	 -- Now check the property (inside the new env):
	 Make_results(LTL_prop -> PRS)
	 Type_check(Pos, result(bool,list(free,nil),nil,nil,nil), PRS -> _)
	 -- Disable the use of LTL operators:
	 Clear_LTL_Wanted()
	 -- Removing this "fake" environment
	 Current -> current_env(CE, C1)
	 Current <- C1
	 Extend_paths <- Paths

  'rule' Type_check_property_def(property_def(Pos, Name, TS, LTL_prop)):
	 Get_current_transition_systems(all -> TS_env)
	 Get_Transition_System(TS, TS_env -> OptTSId)
	 (|
	     where(OptTSId -> ts_id(TSId))
	     TSId'System -> TS_Decls
	  ---------------------------------------------------------
	     where(TS_Decls -> no_input(Local, Transitions))
	     -- Puth the valid variables (from the TS) in the current new env:
	     Get_current_with(-> WITH)
	     Current -> C
	     Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	     Extend_paths -> Paths
	     Extend_paths <- list(nil,Paths)
	     -- Add implicitely the 'primed variables' (future state vars in SAL)
	     where(Local -> variable_decl(PL, LocalDecl))
	     Generate_Primes(LocalDecl -> LocalPrimes)
	     -- Collect the input and local declarations
	     where(DECLS'list(Local,list(variable_decl(PL, LocalPrimes), nil)) -> DS)
	     Make_basic_env(basic(DS))
	     Complete_type_env(basic(DS))
	     Make_value_env(basic(DS))
	     -- Enable the use of LTL operators:
	     Set_LTL_Wanted()
	     -- Now check the property (inside the new env):
	     Make_results(LTL_prop -> PRS)
	     Type_check(Pos, result(bool,list(free,nil),nil,nil,nil), PRS -> _)
	     -- Disable the use of LTL operators:
	     Clear_LTL_Wanted()
	     -- Removing this "fake" environment
	     Current -> current_env(CE, C1)
	     Current <- C1
	     Extend_paths <- Paths
	  ---------------------------------------------------------   
	 ||
	     Puterror(Pos)
	     Putmsg("No transition system with the name mentioned in the property found in the current environment\n")
	 |)
---------------------------------------------------------------------------------------------------------

'action' Type_check(POS, RESULT, RESULTS -> RESULTS)

  'rule' Type_check(P, result(T,RD,WR,IN,OUT), RS -> RS1):
	 (|
	   eq(RS, nil)  -- can assume some error already reported?
	   where(RESULTS'nil -> RS1)
	 ||
	   Isin_results(T, down, RS -> RS1)
	   ne(RS1, nil)
	   No_more_accesses(RS1, RD, WR, IN, OUT)
         ||
	   Puterror(P)
	   Putmsg("Expected type ")
           Print_result(result(T,RD,WR,IN,OUT))
--	   [|
--	     where(T -> defined(I, _))
--	     I'Type -> abbrev(_)
--	     Unfold_type_id(I -> T1)
--	     Putmsg(" (i.e. ")
--	     Print_type(T1)
--	     Putmsg(")")
--	   |]
	   Putnl()
-- debug
-- print(RESULT'result(T,RD,WR,IN,OUT))
	   Putmsg("found type ")
	   Print_results(RS)
	   Putnl()
-- debug
-- print(RS)
	   where(RESULTS'nil -> RS1)
	 |)

'action' type_check_array(TYPE_EXPR -> TYPE_EXPR)
  'rule' type_check_array(array(_,T) -> T)
  'rule' type_check_array(T -> T)

'action' Isin_results(TYPE_EXPR, DIRECTION, RESULTS -> RESULTS)

  'rule' Isin_results(T, Dir, list(result(T1,RD,WR,IN,OUT), RS) -> RS1):
	 Isin_results(T, Dir, RS -> RS2)
	 (|
	   Match(T, Dir, T1)
	   where(RESULTS'list(result(T1,RD,WR,IN,OUT), RS2) -> RS1)
	 ||
	   where(RS2 -> RS1)
	 |)

  'rule' Isin_results(T, Dir, nil -> nil)
---------------------------------------------------------------
-- Accesses
--------------------------------------------------------------

'action' Make_pure_results(Value_ids -> RESULTS)

  'rule' Make_pure_results(list(I, Ids) -> list(result(T,nil,nil,nil,nil),RS)):
	 I'Type -> T
	 Make_pure_results(Ids -> RS)

  'rule' Make_pure_results(nil -> nil)

'action' Make_pure(TYPE_EXPRS -> RESULTS)

  'rule' Make_pure(list(T, TS) -> list(result(T,nil,nil,nil,nil),RS)):
	 Make_pure(TS -> RS)

  'rule' Make_pure(nil -> nil):

'action' Get_reads(RESULTS -> ACCESSES)

  'rule' Get_reads(list(result(T,RD,WR,IN,OUT),RS) -> AS)
	 Get_reads(RS -> AS1)
	 Concat_accs(RD, AS1 -> AS)

  'rule' Get_reads(nil -> nil)
	 
'action' Get_writes(RESULTS -> ACCESSES)

  'rule' Get_writes(list(result(T,RD,WR,IN,OUT),RS) -> AS)
	 Get_writes(RS -> AS1)
	 Concat_accs(WR, AS1 -> AS)

  'rule' Get_writes(nil -> nil)
	 
'action' Get_ins(RESULTS -> ACCESSES)

  'rule' Get_ins(list(result(T,RD,WR,IN,OUT),RS) -> AS)
	 Get_ins(RS -> AS1)
	 Concat_accs(IN, AS1 -> AS)

  'rule' Get_ins(nil -> nil)
	 
'action' Get_outs(RESULTS -> ACCESSES)

  'rule' Get_outs(list(result(T,RD,WR,IN,OUT),RS) -> AS)
	 Get_outs(RS -> AS1)
	 Concat_accs(OUT, AS1 -> AS)

  'rule' Get_outs(nil -> nil)

'action' Add_reads(ACCESSES, RESULTS -> RESULTS)

  'rule' Add_reads(nil, RS -> RS):

  'rule' Add_reads(AS, list(result(T,RD,WR,IN,OUT),RS) -> list(result(T,RD1,WR,IN,OUT),RS1)):
	 Concat_accs(AS, RD -> RD1)
	 Add_reads(AS, RS -> RS1)

  'rule' Add_reads(AS, nil -> nil):

'action' Add_writes(ACCESSES, RESULTS -> RESULTS)

  'rule' Add_writes(nil, RS -> RS):

  'rule' Add_writes(AS, list(result(T,RD,WR,IN,OUT),RS) -> list(result(T,RD,WR1,IN,OUT),RS1)):
	 Concat_accs(AS, WR -> WR1)
	 Add_writes(AS, RS -> RS1)

  'rule' Add_writes(AS, nil -> nil):

'action' Add_ins(ACCESSES, RESULTS -> RESULTS)

  'rule' Add_ins(nil, RS -> RS):

  'rule' Add_ins(AS, list(result(T,RD,WR,IN,OUT),RS) -> list(result(T,RD,WR,IN1,OUT),RS1)):
	 Concat_accs(AS, IN -> IN1)
	 Add_ins(AS, RS -> RS1)

  'rule' Add_ins(AS, nil -> nil):

'action' Add_outs(ACCESSES, RESULTS -> RESULTS)

  'rule' Add_outs(nil, RS -> RS):

  'rule' Add_outs(AS, list(result(T,RD,WR,IN,OUT),RS) -> list(result(T,RD,WR,IN,OUT1),RS1)):
	 Concat_accs(AS, OUT -> OUT1)
	 Add_outs(AS, RS -> RS1)

  'rule' Add_outs(AS, nil -> nil):

'action' Merge_reads(RESULTS, RESULTS -> ACCESSES)

  'rule' Merge_reads(RS1, RS2 -> AS):
	 Get_reads(RS1 -> AS1)
	 Get_reads(RS2 -> AS2)
	 Concat_accs(AS1, AS2 -> AS)
	 
'action' Merge_writes(RESULTS, RESULTS -> ACCESSES)

  'rule' Merge_writes(RS1, RS2 -> AS):
	 Get_writes(RS1 -> AS1)
	 Get_writes(RS2 -> AS2)
	 Concat_accs(AS1, AS2 -> AS)
	 
'action' Merge_ins(RESULTS, RESULTS -> ACCESSES)

  'rule' Merge_ins(RS1, RS2 -> AS):
	 Get_ins(RS1 -> AS1)
	 Get_ins(RS2 -> AS2)
	 Concat_accs(AS1, AS2 -> AS)
	 
'action' Merge_outs(RESULTS, RESULTS -> ACCESSES)

  'rule' Merge_outs(RS1, RS2 -> AS):
	 Get_outs(RS1 -> AS1)
	 Get_outs(RS2 -> AS2)
	 Concat_accs(AS1, AS2 -> AS)

'action' Add_accesses(RESULTS, RESULTS -> RESULTS)

  'rule' Add_accesses(RS, RS1 -> RS2)
	 Get_reads(RS -> RD)
	 Add_reads(RD, RS1 -> RS11)
	 Get_writes(RS -> WR)
	 Add_writes(WR, RS11 -> RS111)
	 Get_ins(RS -> IN)
	 Add_ins(IN, RS111 -> RS1111)
	 Get_outs(RS -> OUT)
	 Add_outs(OUT, RS1111 -> RS2)
	 

'condition' No_more_accesses(RESULTS, ACCESSES, ACCESSES, ACCESSES, ACCESSES)
-- succeeds if each result has no more read, write, in and out
-- accesses than in other parameters (2nd is read, etc)

  'rule' No_more_accesses(list(result(T, RD, WR, IN, OUT), RS),
					 RD1, WR1, IN1, OUT1): 
	 (|
	   Concat_accs(RD1, WR1 -> RD2)
	   Included(RD, RD2)
	   Included(WR, WR1)
	   Included(IN, IN1)
	   Included(OUT, OUT1)
	 ||
	   No_more_accesses(RS, RD1, WR1, IN1, OUT1)
	 |)

'action' Concat_accs(ACCESSES, ACCESSES -> ACCESSES)

-- tempting to have following rule but we want to ensure first
-- argument is flattened
--  'rule' Concat_accs(AS, nil -> AS):

  'rule' Concat_accs(list(A, AS), AS1 -> AS2):
	 Concat_accs(AS, AS1 -> AS11)
	 Flatten_access(A -> AS10)
	 (|
	   where(AS10 -> list(A1, nil))
	   where(ACCESSES'list(A1, AS11) -> AS2)
	 ||
	   Concat_accs(AS10, AS11 -> AS2)
	 |)

  'rule' Concat_accs(nil, AS -> AS):

-- remove enumerated accesses
'action' Flatten_access(ACCESS -> ACCESSES)

  'rule' Flatten_access(enumerated_access(P, nil) -> nil):

  'rule' Flatten_access(enumerated_access(P, list(A, AS)) -> AS3):
	 Flatten_access(A -> AS1)
	 Flatten_access(enumerated_access(P, AS) -> AS2)
	 Concat_accs(AS1, AS2 -> AS3)

  'rule' Flatten_access(comprehended_access(P, A, L) -> AS):
	 Flatten_access(A -> AS1)
	 Comprehend_accesses(P, AS1, L -> AS)

-- other cases
  'rule' Flatten_access(A -> list(A, nil)):

'action' Comprehend_accesses(POS, ACCESSES, SET_LIMITATION -> ACCESSES)

  'rule' Comprehend_accesses(P, list(A, AS), L -> list(comprehended_access(P, A, L), AS1)):
	 Comprehend_accesses(P, AS, L -> AS1)

  'rule' Comprehend_accesses(_, nil, _ -> nil):

'condition' Included(ACCESSES, ACCESSES)

  'rule' Included(list(A, AS), AS1):
	 Included1(A, AS1)
	 Included(AS, AS1)

  'rule' Included(nil, AS1):

'condition' Included1(ACCESS, ACCESSES)

  'rule' Included1(A, list(A1, AS1)):
	 (|
	   Included2(A, A1)
	 ||
	   Included1(A, AS1)
	 |)

'condition' Included2(ACCESS, ACCESS)

  'rule' Included2(A, free):

  'rule' Included2(enumerated_access(_, AS), A):
	 Included(AS, list(A,nil))

  'rule' Included2(A, enumerated_access(_, AS)):
	 Included1(A, AS)

  'rule' Included2(completed_access(_, nil), completed_access(_, nil)):

  'rule' Included2(completed_access(P, qualification(Obj)), A):
	 Is_dummy(Obj)
	 Included2(completed_access(P, nil), A)

  'rule' Included2(completed_access(_, qualification(Obj)), completed_access(_, nil)):
	 Current -> C
	 Id_of_object(Obj -> I)
	 Object_is_defined_in_current_env(I, C)

  'rule' Included2(completed_access(_, qualification(Obj)), completed_access(_, qualification(Obj1))):
	 Id_of_object(Obj -> I)
	 Id_of_object(Obj1 -> I1)
	 (|
	   eq(I,I1)
	 ||
	   I1'Env -> CE
	   Object_is_defined_in_class_env(I, CE)
	 |)

  'rule' Included2(comprehended_access(_, A, _), A1):
	 Included2(A, A1)

  'rule' Included2(A, comprehended_access(_, A1, _)):
	 Included2(A, A1)

  'rule' Included2(variable(_, I, _), completed_access(_, nil)):
	 Current -> C
	 Variable_is_defined_in_current_env(I, C)

  'rule' Included2(A, completed_access(P, qualification(Obj))):
	 Is_dummy(Obj)
	 Included2(A, completed_access(P, nil))

  'rule' Included2(variable(_, I, _), completed_access(_, qualification(Obj1))):
	 Id_of_object(Obj1 -> I1)
	 I1'Env -> CE
	 Variable_is_defined_in_class_env(I, CE)
	 
  'rule' Included2(variable(_, I, _), variable(_, I1, _)):
	 eq(I,I1)

  'rule' Included2(channel(_, I, _), completed_access(_, nil)):
	 Current -> C
	 Channel_is_defined_in_current_env(I, C)

  'rule' Included2(channel(_, I, _), completed_access(_, qualification(Obj1))):
	 Id_of_object(Obj1 -> I1)
	 I1'Env -> CE
	 Channel_is_defined_in_class_env(I, CE)
	 
  'rule' Included2(channel(_, I, _), channel(_, I1, _)):
	 eq(I,I1)

'action' Check_all_readonly(POS, RESULTS)

  'rule' Check_all_readonly(P, list(R, RS)):
	 Check_readonly(P, R)
	 Check_all_readonly(P, RS)

  'rule' Check_all_readonly(P, nil):

'action' Check_readonly(POS, RESULT)

  'rule' Check_readonly(P, result(T,RD,WR,IN,OUT)):
	 (|
	   eq(WR,nil)
	   eq(IN,nil)
	   eq(OUT,nil)
	 ||
	   Puterror(P)
	   Putmsg("Result type ")
	   Print_result(result(T,RD,WR,IN,OUT))
	   Putmsg(" not readonly")
	   Putnl()
	 |)

'action' Check_all_pure(POS, RESULTS)

  'rule' Check_all_pure(P, list(R, RS)):
	 Check_pure(P, R)
	 Check_all_pure(P, RS)

  'rule' Check_all_pure(P, nil):

'action' Check_pure(POS, RESULT)

  'rule' Check_pure(P, result(T,RD,WR,IN,OUT)):
	 (|
	   eq(RD,nil)
	   eq(WR,nil)
	   eq(IN,nil)
	   eq(OUT,nil)
	 ||
	   Puterror(P)
	   Putmsg("Result type ")
	   Print_result(result(T,RD,WR,IN,OUT))
	   Putmsg(" not pure")
	   Putnl()
	 |)

'action' Remove_accesses(RESULTS, CLASS_ENV -> RESULTS)

  'rule' Remove_accesses(list(result(T,RD,WR,IN,OUT),RS), CE -> list(result(T,RD1,WR1,IN1,OUT1),RS1)):
	 Remove_accesses1(RD, CE -> RD1)
	 Remove_accesses1(WR, CE -> WR1)
	 Remove_accesses1(IN, CE -> IN1)
	 Remove_accesses1(OUT, CE -> OUT1)
	 Remove_accesses(RS, CE -> RS1)

  'rule' Remove_accesses(nil, CE -> nil):

'action' Remove_accesses1(ACCESSES, CLASS_ENV -> ACCESSES)

  'rule' Remove_accesses1(nil, CE -> nil):

  'rule' Remove_accesses1(list(enumerated_access(P, AS2), AS), CE -> AS4):
	 Remove_accesses1(AS, CE -> AS1)
	 (|
	   Remove_accesses1(AS2, CE -> list(A3, AS3))
	   where(ACCESSES'list(enumerated_access(P, list(A3, AS3)), AS1) -> AS4)
	 ||
	   where(AS1 -> AS4)
	 |)

  'rule' Remove_accesses1(list(completed_access(P, nil),AS), CE -> list(completed_access(P, nil),AS1)):
	 Remove_accesses1(AS, CE -> AS1)

  'rule' Remove_accesses1(list(completed_access(P, qualification(Obj)),AS), CE -> AS2):
	 Remove_accesses1(AS, CE -> AS1)
	 Id_of_object(Obj -> I)
	 (|
	   Object_is_defined_in_class_env(I, CE)
	   where(AS1 -> AS2)
	 ||
	   where(ACCESSES'list(completed_access(P, qualification(Obj)),AS1) -> AS2)
	 |)

  'rule' Remove_accesses1(list(comprehended_access(P, A, L), AS), CE -> AS2):
	 Remove_accesses1(AS, CE -> AS1)
	 (|
	   Remove_accesses1(list(A, nil), CE -> list(A1, nil))
	   where(ACCESSES'list(comprehended_access(P, A1, L), AS1) -> AS2)
	 ||
	   where(AS1 -> AS2)
	 |)

  'rule' Remove_accesses1(list(variable(P, I, Q),AS), CE -> AS2):
	 Remove_accesses1(AS, CE -> AS1)
	 (|
	   Variable_is_defined_in_class_env(I, CE)
	   where(AS1 -> AS2)
	 ||
	   where(ACCESSES'list(variable(P, I, Q),AS1) -> AS2)
	 |)

  'rule' Remove_accesses1(list(channel(P, I, Q),AS), CE -> AS2):
	 Remove_accesses1(AS, CE -> AS1)
	 (|
	   Channel_is_defined_in_class_env(I, CE)
	   where(AS1 -> AS2)
	 ||
	   where(ACCESSES'list(channel(P, I, Q),AS1) -> AS2)
	 |)




-----------------------------------------------------------------
-- Utilities
-----------------------------------------------------------------
'action' Type_of_typing_as_product(TYPING -> TYPE_EXPR)

  'rule' Type_of_typing_as_product(single(P,B,T) -> T):

  'rule' Type_of_typing_as_product(multiple(P,BS,T) -> product(TS)):
	 Type_of_multiple(BS, T -> TS)

'action' Type_of_multiple(BINDINGS, TYPE_EXPR -> PRODUCT_TYPE)

  'rule' Type_of_multiple(list(B,BS), T -> list(T, TS)):
	 Type_of_multiple(BS, T -> TS)

  'rule' Type_of_multiple(nil, T -> nil):

'action' Type_of_typings_as_product(TYPINGS -> TYPE_EXPR)

  'rule' Type_of_typings_as_product(TPS -> product(TS)):
	 Type_of_typings_as_product1(TPS -> TS)

'action' Type_of_typings_as_product1(TYPINGS -> PRODUCT_TYPE)

  'rule' Type_of_typings_as_product1(list(TP, TPS) -> list(T, TS)):
	 Type_of_typing_as_product(TP -> T)
	 Type_of_typings_as_product1(TPS -> TS)

  'rule' Type_of_typings_as_product1(nil -> nil):

'action' Defined_type_of_typings(TYPINGS -> PRODUCT_TYPE)

  'rule' Defined_type_of_typings(list(TP, TPS) -> list(T, TS)):
	 Defined_type_of_typing(TP -> T)
	 Defined_type_of_typings(TPS -> TS)

  'rule' Defined_type_of_typings(nil -> nil):

'action' Defined_type_of_typing(TYPING -> TYPE_EXPR)

  'rule' Defined_type_of_typing(single(_,B,_) -> T):
	 Defined_type_of_binding(B -> T)

  'rule' Defined_type_of_typing(multiple(_,list(B, _),_) -> T):
	 Defined_type_of_binding(B -> T)

'action' Defined_type_of_binding(BINDING -> TYPE_EXPR)

  'rule' Defined_type_of_binding(single(P, _) -> T)
	 Get_current_top_values(-> VE)
	 (| 
	   Select_id_by_pos(P, VE -> value_id(I))
	   I'Type -> T
	 || -- may not be in environment due to earlier error
	   where(TYPE_EXPR'any -> T)
	 |)

  'rule' Defined_type_of_binding(product(_, BS) -> product(TS)):
	 Defined_type_of_bindings(BS -> TS)

'action' Defined_type_of_bindings(BINDINGS -> PRODUCT_TYPE)

  'rule' Defined_type_of_bindings(list(B, BS) -> list(T, TS)):
	 Defined_type_of_binding(B -> T)
	 Defined_type_of_bindings(BS -> TS)

  'rule' Defined_type_of_bindings(nil -> nil):
	 
'action' Select_id_by_pos(POS, Value_ids -> OPT_VALUE_ID)

  'rule' Select_id_by_pos(P, list(I, Ids) -> Oid):
	 I'Pos -> P1
	 (|
	   eq(P, P1)
	   where(value_id(I) -> Oid)
	 ||
	   Select_id_by_pos(P, Ids -> Oid)
	 |)

  'rule' Select_id_by_pos(P, nil -> nil):

---------------------------------------------------
'action' Generate_Primes(VARIABLE_DEFS -> VARIABLE_DEFS)

  'rule' Generate_Primes(list(H, Rest) -> list(H_prime, Rest_prime))
	 (|
		where(H -> VARIABLE_DEF'single(Pos, Ident, Type, Init))
		id_to_string(Ident -> IdStr)
		IncreaseCol(Pos -> NewPos)
		Concatenate(IdStr,"'" -> NewIdStr)
		string_to_id(NewIdStr -> NewIdent)
		where(VARIABLE_DEF'single(NewPos, NewIdent, Type, Init) -> H_prime)
	 ||
		-- Ignore multiple definitions...
		where(H -> H_prime)
	 |)
	 Generate_Primes(Rest -> Rest_prime)

  'rule' Generate_Primes(nil -> nil)

'condition' Match_Results(RESULTS, RESULTS)
  'rule' Match_Results(nil, nil)

  'rule' Match_Results(list(result(Ty1,_,_,_,_),T1), list(result(Ty2,_,_,_,_),T2))
         Match(Ty1,down,Ty2)
         Match_Results(T1,T2)

'action' Resolve_Types_In_Results(RESULTS -> RESULTS)
  'rule' Resolve_Types_In_Results(nil -> nil)

  'rule' Resolve_Types_In_Results(list(result(T,READ,WRITE,IN,OUT),RS) -> list(result(T1,READ,WRITE,IN,OUT),RS1))
         Resolve_type(T -> T1)
         Resolve_Types_In_Results(RS -> RS1)

