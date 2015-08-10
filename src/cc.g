-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the confidence condition generator

'module' cc

'use' ast print ext env objects values types pp sml cpp

'export' Generate_confidence_conditions
	 Resolve_class Resolve Simplify Same_type
	 Resolve_type Built_in Object_to_string
	 Maxtype Maximal Isin_subtype Isin_subtype_array_indexes Type_of_val Static_subtype
	 Lookup_test_case
     	 Lookup_property
	 Localise_id Split_fun_type
	 Isin_value_ids
	 Typing_to_expr
	 Parms_to_typings

	 Generate CCGenerate CCGenerate_type GetCcVar InitCcVar
	 CCNEEDED CCVALUEDEF
	 ASSUMPTION ASSUMPTIONS
	 Pattern_match
	 Lookup_axiom
	 Resolve_value_typings
	 Resolve_value_typing
         Concat_Extra_Guards
	 GetGuardValueExpression
-----------------------------------------------------------------------
-- Generate confidence conditions
-----------------------------------------------------------------------

'action' Generate_confidence_conditions(CLASS, MODULE_CATEGORY)

  'rule' Generate_confidence_conditions(CL, Cat):
	 [|
	   CcWanted()
	   (|
	     HasErrors()
	     Putmsg("Errors found, so confidence conditions cannot be generated")
	     Putnl()
	   ||
	     Resolve_class(CL)
	     [|
	       (| eq(Cat, top) || AllCcWanted() |)
	       CCGenerate_class(CL, nil)
	     |]
	   |)
	 |]

-- for making new identifiers
'var' CcCount : INT

-- for storing expanded conditions for PVS translator
'var' CcVar : VALUE_EXPR

'action' InitCcVar

  'rule' InitCcVar:
	 CcCount <- 0
	 CcVar <- no_val

'action' NewCcCount(-> INT)

  'rule' NewCcCount(-> N+1):
	 CcCount -> N
	 CcCount <- N+1 

'action' GetCcVar(-> VALUE_EXPR)

  'rule' GetCcVar(-> V):
	 CcVar -> V
	 CcVar <- no_val

'action' AddCcVar(VALUE_EXPR)

  'rule' AddCcVar(V2)
	 (|
	   (| eq(V2, no_val) || where(V2 -> literal_expr(_,bool_true)) |)
	 ||
	   CcVar -> V1
	   (|
	     eq(V1, no_val)
	     CcVar <- V2
	   ||
	     DefaultPos(->P)
	     CcVar <- ax_infix(P, V1, and, V2, P)
	   |)
	 |)
	 
-----------------------------------------------------------------------
-- Resolve values by replacing names with occurrences of identifiers
-----------------------------------------------------------------------

'action' Resolve_class(CLASS)

  'rule' Resolve_class(basic(DS)):
	 Resolve_decls(DS)
-- Get_current_top_values(-> VE)
-- Print_value_env(VE)

  'rule' Resolve_class(instantiation(name(P,id_op(Id)), Objs)):
	 [|
	 (|
	   CcWanted()
	   Get_id_of_scheme(Id -> scheme_id(I))
	   I'With -> W	 
	   Set_current_with(W)
	   I'Class -> CL
	   Resolve_class(CL)
	   -- confidence conditions generated at loading
	 ||
	   (| SMLWanted() || PVSWanted()|| SALWanted()||FDRWanted() |)
	   Get_id_of_scheme(Id -> scheme_id(I))
	   I'With -> W	 
	   Set_current_with(W)
	   I'Class -> CL
	   Resolve_class(CL)
	 |)
	 |]

  'rule' Resolve_class(extend(CL1, CL2)):
	 In_left
	 Resolve_class(CL1)
	 Left_right
	 Resolve_class(CL2)
	 Out_right

  'rule' Resolve_class(hide(H, C)):
	 Resolve_class(C)

  'rule' Resolve_class(rename(R, C)):
	 Resolve_class(C)

  'rule' Resolve_class(with(P,Obj, C)):
	 Resolve_class(C)

'action' Resolve_decls(DECLS)

  'rule' Resolve_decls(list(D, DS)):
	 Resolve_decl(D)
	 Resolve_decls(DS)

  'rule' Resolve_decls(nil):

'action' Resolve_decl(DECL)

  'rule' Resolve_decl(type_decl(P, Defs)):
	 Resolve_type_defs(Defs)

  'rule' Resolve_decl(value_decl(P,Defs)):
	 Resolve_value_defs(Defs)

  'rule' Resolve_decl(variable_decl(P,Defs)):
	 Resolve_variable_defs(Defs)

  'rule' Resolve_decl(channel_decl(P,Defs)):
	 Resolve_channel_defs(Defs)

  'rule' Resolve_decl(object_decl(P,Defs)):
	 Resolve_object_defs(Defs)

  'rule' Resolve_decl(axiom_decl(P,Defs)):
	 Resolve_axiom_defs(Defs)

  'rule' Resolve_decl(test_case_decl(P,Defs)):
	 Resolve_test_case_defs(Defs)

  'rule' Resolve_decl(trans_system_decl(P, Defs)):
	 Resolve_trans_sys_defs(Defs)

  'rule' Resolve_decl(property_decl(P, Defs)):
	 Resolve_property_defs(Defs)

'action' Resolve_type_defs(TYPE_DEFS)

  'rule' Resolve_type_defs(list(H,T)):
	 Resolve_type_def(H)
	 Resolve_type_defs(T)

  'rule' Resolve_type_defs(nil):

'action' Resolve_type_def(TYPE_DEF)

  'rule' Resolve_type_def(sort(_,_)):

  'rule' Resolve_type_def(abbrev(_,Id,_)):
	 Get_current_types(-> TE)
	 Lookup_env(Id, TE -> type_id(I))
	 (|
	   I'Def -> abbreviation(_) -- already done
	 ||
	   I'Type -> abbrev(T)
	   Resolve_type(T -> T1)
	   I'Def <- abbreviation(T1)
	   [|
	     I'Subtype -> funct(I1)
	     I1'Type -> T2
	     Resolve_type(T2 -> T3)
	     I1'Type <- T3
	     I1'Def -> expl_fun(PARMS, V, _, _, _, _)
	     I1'Pos -> P
	     Openenv()
	     Result_type(P, T3, PARMS -> _)
	     Resolve(V, bool -> V1)
	     (|
	       (| SMLWanted() || CPPWanted() || SALWanted()||FDRWanted() |)
	       Args_in_subtypes(PARMS, T3 -> COND1)
	       Simplify(COND1 -> COND2)
	       (|
		 (| where(COND2 -> literal_expr(_,bool_true))
		    || where(COND2 -> no_val) |)
		 where(OPT_CONDITION'nil -> COND)
	       ||
		 where(OPT_CONDITION'condition(COND2) -> COND)
	       |)
	     ||
	       where(OPT_CONDITION'nil -> COND)
	     |)
	     (|
	       where(COND -> condition(V2))
	       where(ax_infix(P, V2, and, V1, P) -> V3)
	     ||
	       where(V1 -> V3)
	     |)
	     I1'Def <- expl_fun(PARMS, V3, nil, nil, nil, nil)
	     [|
	       CPPWanted()
	       Localise_value_env()
	     |]
	     Closeenv()
	   |]
	 |)

  'rule' Resolve_type_def(variant(_, Id, VS)):
	 Get_current_types(-> TE)
	 Lookup_env(Id, TE -> type_id(I))
	 Resolve_variants(VS -> VS1)
	 I'Type <- sort(variant(VS1))


  'rule' Resolve_type_def(record(P, Id, CS)):
	 Get_current_types(-> TE)
	 Lookup_env(Id, TE -> type_id(I))
	 Resolve_components(CS -> CS1)
	 I'Type <- sort(record(CS1))
	 -- now resolve mk_ function
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(P, VE -> value_id(I1))
	 I1'Type -> T
	 Resolve_type(T -> T1)
	 I1'Type <- T1
	 -- add condition for subtypes in arguments
	 Make_function_type(T1 -> fun(D, _, _))
	 (|
	   where(D -> product(Ts))
	 ||
	   where(PRODUCT_TYPE'list(D, nil) -> Ts)
	 |)
	 IncreaseCol(P -> NewPos)
	 Make_parm_bindings(NewPos, 1, Ts -> Bs)
	 where(FORMAL_FUNCTION_PARAMETERS'list(form_parm(P, Bs), nil) -> PARMS)
	 Args_in_subtypes(PARMS, T1 -> COND1)
	 Simplify(COND1 -> COND2)
	 (|
	   (| where(COND2 -> literal_expr(_,bool_true))
	      || where(COND2 -> no_val) |)
	   where(OPT_CONDITION'nil -> COND)
	 ||
	   where(OPT_CONDITION'condition(COND2) -> COND)
	 |)
	 I1'Def <- expl_fun(PARMS, no_val, nil, nil, COND, nil)
	 
  'rule' Resolve_type_def(union(_, Id, CS)):
	 Get_current_types(-> TE)
	 Lookup_env(Id, TE -> type_id(I))
	 Resolve_choices(CS -> CS1)
	 I'Type <- sort(union(CS1))

'action' Resolve_variants(VARIANTS -> VARIANTS)

  'rule' Resolve_variants(list(V, VS) -> list(V1, VS1)):
	 Resolve_variant(V -> V1)
	 Resolve_variants(VS -> VS1)

  'rule' Resolve_variants(nil -> nil):

'action' Resolve_variant(VARIANT -> VARIANT)

  'rule' Resolve_variant(record(P, Cons, Comps) -> record(P, Cons1, Comps1)):
	 Resolve_constructor(Cons -> Cons1)
	 Resolve_components(Comps -> Comps1)

'action' Resolve_constructor(CONSTRUCTOR -> CONSTRUCTOR)

  'rule' Resolve_constructor(constructor(P, Id) -> con_ref(I)):
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(P, VE -> value_id(I))
	 I'Type -> T
	 Resolve_type(T -> T1)
	 I'Type <- T1
	 -- add condition for subtypes in arguments
	 -- provided constructor is a function
	 [|
	   Make_function_type(T1 -> fun(D, _, _))
	   (|
	     where(D -> product(Ts))
	   ||
	     where(PRODUCT_TYPE'list(D, nil) -> Ts)
	   |)
	   IncreaseCol(P -> NewPos)
	   Make_parm_bindings(NewPos, 1, Ts -> Bs)
	   where(FORMAL_FUNCTION_PARAMETERS'list(form_parm(P, Bs), nil) -> PARMS)
	   Args_in_subtypes(PARMS, T1 -> COND1)
	   Simplify(COND1 -> COND2)
	   (|
	     (| where(COND2 -> literal_expr(_,bool_true))
		|| where(COND2 -> no_val) |)
	     where(OPT_CONDITION'nil -> COND)
	   ||
	     where(OPT_CONDITION'condition(COND2) -> COND)
	   |)
	   I'Def <- expl_fun(PARMS, no_val, nil, nil, COND, nil)
	 |]

  'rule' Resolve_constructor(wildcard -> wildcard):

'action' Resolve_components(COMPONENTS -> COMPONENTS)

  'rule' Resolve_components(list(C, CS) -> list(C1, CS1)):
	 Resolve_component(C -> C1)
	 Resolve_components(CS -> CS1)

  'rule' Resolve_components(nil -> nil):

'action' Resolve_component(COMPONENT -> COMPONENT)

  'rule' Resolve_component(component(P, D, T, R) -> component(P, D1, T1, R1)):
	 Resolve_destructor(P, D -> D1)
	 Resolve_type(T -> T1)
	 Resolve_reconstructor(R -> R1)

'action' Resolve_destructor(POS, DESTRUCTOR -> DESTRUCTOR)

  'rule' Resolve_destructor(_, destructor(P, Id) -> dest_ref(I)):
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(P, VE -> value_id(I))
	 I'Type -> T
	 Resolve_type(T -> T1)
	 I'Type <- T1

  'rule' Resolve_destructor(P, nil -> dest_ref(I)):
  	 -- added CWG 12/4/08
	 -- For SAL, missing destructors are added with the position
  	 -- of the component
	 SALWanted()
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(P, VE -> value_id(I))
	 I'Type -> T
	 Resolve_type(T -> T1)
	 I'Type <- T1
 
  'rule' Resolve_destructor(_, D -> D)

'action' Resolve_reconstructor(RECONSTRUCTOR -> RECONSTRUCTOR)

  'rule' Resolve_reconstructor(reconstructor(P, Id) -> recon_ref(I)):
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(P, VE -> value_id(I))
	 I'Type -> T
	 Resolve_type(T -> T1)
	 I'Type <- T1
	 -- add condition for subtypes in arguments
	 I'Def -> expl_fun(PARMS, DEF, POST, PREC, _, RES)
	 Args_in_subtypes(PARMS, T1 -> COND1)
	 Simplify(COND1 -> COND2)
	 (|
	   (| where(COND2 -> literal_expr(_,bool_true))
	      || where(COND2 -> no_val) |)
	   where(OPT_CONDITION'nil -> COND)
	 ||
	   where(OPT_CONDITION'condition(COND2) -> COND)
	 |)
	 I'Def <- expl_fun(PARMS, DEF, POST, PREC, COND, RES)

  'rule' Resolve_reconstructor(R -> R)

'action' Resolve_choices(CHOICES -> CHOICES)

  'rule' Resolve_choices(list(C, CS) -> list(C1, CS1)):
	 Resolve_choice(C -> C1)
	 Resolve_choices(CS -> CS1)

  'rule' Resolve_choices(nil -> nil):

'action' Resolve_choice(CHOICE -> CHOICE)

  'rule' Resolve_choice(choice(_, N) -> choice_ref(I, Q)):
	 Resolve_type(named_type(N) -> defined(I, Q))

  'rule' Resolve_choice(C -> C):

'action' Resolve_object_defs(OBJECT_DEFS)

  'rule' Resolve_object_defs(list(H,T)):
	 Resolve_object_def(H)
	 Resolve_object_defs(T)

  'rule' Resolve_object_defs(nil):

'action' Resolve_object_def(OBJECT_DEF)

  'rule' Resolve_object_def(odef(P, Id, TS, CL)):
	 Get_current_modules(-> ME)
	 Lookup_object_in_module(Id, ME -> object_id(I))
	 [|
	   I'Params -> param_type(T)
	   Resolve_type(T -> T1)
	   I'Params <- param_type(T1)
	 |]
	 Current -> C
	 I'Param_env -> PCE
	 I'Env -> CE
	 Current <- current_env(CE,current_env(PCE, C))
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,list(nil,Paths))
	 Resolve_class(CL)
	 Current -> current_env(CE1,current_env(PCE1,C1))
	 Current <- C1
	 Extend_paths <- Paths

'action' Resolve_value_defs(VALUE_DEFS)

  'rule' Resolve_value_defs(list(D, DS)):
	 Resolve_value_def(D)
	 Resolve_value_defs(DS)

  'rule' Resolve_value_defs(nil):

'action' Resolve_value_def(VALUE_DEF)

  'rule' Resolve_value_def(typing(P, TP)):
	 [| -- multiple typing TODO (seems very unlikely to occur) 
	   where(TP -> single(P1, single(P2, Id),_))
	   Get_current_top_values(-> VE)
	   Select_id_by_pos(P2, VE -> value_id(I))
	   I'Type -> T1
	   Resolve_type(T1 -> T2)
	   I'Type <- T2
	 |]

  'rule' Resolve_value_def(exp_val(P, TP, V)):
         Defined_type_of_typing(TP -> T)
         Resolve_type(T -> TT)       
         (|
           where(TP -> single(P1, single(P2, Id),_))
           Get_current_top_values(-> VE)
           Get_current_top_values(-> VE2)
           Select_id_by_pos(P2, VE -> value_id(I))
           I'Type -> T1
           Resolve_type(T1 -> T2)
           I'Type <- T2
           Resolve(V, TT -> V1)
           Maxtype(T2 -> Tm)
           -- get best type
           Type_of_val(V1, Tm -> T3)
           string_to_id("RSL_res_" -> Z)
           New_value_id(P, id_op(Z) -> Ip)
           Ip'Type <- T3
           Isin_subtype(val_occ(P,Ip,nil), T2 -> Pred)
           Simplify(Pred -> Pred1)
           (|
             ne(Pred1, no_val)
             I'Def <- expl_val(disamb(P,V1,TT), nil) --condition(Pred1)) 
           ||
             I'Def <- expl_val(disamb(P,V1,TT), nil)
           |)
-- debug
--Putmsg("Definition of ")
--Print_id_or_op(Id)
--Putmsg(": = ")
--Print_expr(V1)
--Putnl()
	 ||
	   where(TP -> single(P1, product(P2, BS),_))
	   -- note disamb used for cc generation 
	   -- but not C++ translator or sml translator
	   (|
	     CcWanted()
	     where(VALUE_EXPR'disamb(P,V,TT) -> V2)
	   ||
	     where(V -> V2)
	   |)
	   Store_multiple_expl_value_def(product(P2, BS), list(explicit(P1, binding(P1, product(P2, BS)), V2), nil))
	 |)

  'rule' Resolve_value_def(imp_val(P, TP, restriction(_, V))):
	 Resolve(V, bool -> V1)
	 (|
	   where(TP -> single(P1,single(P2,Id),_))
	   Get_current_top_values(-> VE)
	   Select_id_by_pos(P2, VE -> value_id(I))
	   I'Def <- impl_val(V1)
	   I'Type -> T1
	   Resolve_type(T1 -> T2)
	   I'Type <- T2
-- debug
-- Putmsg("Definition of ")
-- Print_id_or_op(Id)
-- Putmsg(": :- ")
-- Print_expr(V1)
-- Putnl()

	 ||
	   where(TP -> single(P1,product(P2,BS),_))
	   Store_multiple_impl_value_def(product(P2, BS), V1)
	 |)

  'rule' Resolve_value_def(exp_fun(P, single(_,single(P1,F),_), form_appl(_,_,PARMS), V, POST, PRE, _)):
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(P1, VE -> value_id(I))
	 I'Type -> T		   -- defined version of type
	 Resolve_type(T -> T1)
	 I'Type <- T1
	 Openenv()
	 Result_type(P, T1, PARMS -> result(T2,_,_,_,_))
	 Resolve(V, T2 -> V1)
	 (|
	   where(POST -> post(post_cond(PP, RP, EP)))
	   (|
	     where(RP -> result(_, B))
	     Openenv()
	     Define_value_binding(B, T2)
             Resolve(EP, bool -> EP1)
	     Closeenv()
	   ||
	     Resolve(EP, bool -> EP1)
	   |)
	   where(OPT_POST_CONDITION'post(post_cond(PP, RP, EP1)) -> POST1)
	 ||
	   where(OPT_POST_CONDITION'nil -> POST1)
	 |)
	 (|
	   where(PRE -> pre_cond(P2, C))
	   Resolve(C, bool -> C1)
	   where(pre_cond(P2, C1) -> PRE1)
	 ||
	   where(PRE_CONDITION'nil -> PRE1)
	 |)
	 (|
	   (| SMLWanted() || CPPWanted() || SALWanted()||FDRWanted() |)
	   Args_in_subtypes(PARMS, T1 -> COND1)
	   Simplify(COND1 -> COND2)
	   (|
	     (| where(COND2 -> literal_expr(_,bool_true))
		|| where(COND2 -> no_val) |)
	     where(OPT_CONDITION'nil -> COND)
	   ||
	     where(OPT_CONDITION'condition(COND2) -> COND)
	   |)
	   Maxtype(T2 -> Tm)
	   Type_of_val(V1, Tm -> T3)
	   string_to_id("RSL_res_" -> Id)
	   -- must be give same position as function binding
	   -- (for SML translator)
	   (| 
	      SALWanted() -- jiperna: Changed the Position because it was shared with the position stored in the
			  -- value_id for the function. In the translator to SAL, the resolution of value occurrences
			  -- is by POSITION. If the position is not unique, the translator gets confused.
	      IncreaseCol(P1 -> IncP1)
	      New_value_id(IncP1, id_op(Id) -> RI)
	   ||
	      New_value_id(P1, id_op(Id) -> RI)   
	   |)
	   RI'Type <- T3
	   Isin_subtype(val_occ(P1, RI, nil), T2 -> PCOND1)
	   Simplify(PCOND1 -> PCOND2)
	   (|
	     (| where(PCOND2 -> literal_expr(_,bool_true))
		|| where(PCOND2 -> no_val) |)
	     where(OPT_CONDITION'nil -> PCOND)
	   ||
	     where(OPT_CONDITION'condition(PCOND2) -> PCOND)
	   |)
	 ||
	   where(OPT_CONDITION'nil -> COND)
	   where(OPT_CONDITION'nil -> PCOND)
	 |)
	 I'Def <- expl_fun(PARMS, V1, POST1, PRE1, COND, PCOND)
	 [|
	   CPPWanted()
	   Localise_value_env()
	 |]
	 Closeenv()
(|
Get_current_top_values(-> VE2)
where(VE2 -> list(_,nil)) -- TODO: Hack
Closeenv()
||
|)


-- debug
-- Putmsg("Definition of ")
-- Print_id_or_op(F)
-- Putmsg(": is ")
-- Print_expr(V1)
-- Putnl()
-- [|
-- where(PRE1 -> pre_cond(_, X))
-- Putmsg("pre ")
-- Print_expr(X)
-- Putnl()
-- |]


  'rule' Resolve_value_def(imp_fun(P, single(_,single(PF,F),_), form_appl(_,_,PARMS), post_cond(P1,R,E), PRE)):
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(PF, VE -> value_id(I))
	 Openenv()
	 I'Type -> T		   -- defined version of type
	 Resolve_type(T -> T1)
	 I'Type <- T1
	 Result_type(P, T1, PARMS -> result(T2,_,_,_,_))
	 (|
	   where(R -> result(_, B))
	   Openenv()
	   Define_value_binding(B, T2)
	   Resolve(E, bool -> E1)
	   Closeenv()
	 ||
	   Resolve(E, bool -> E1)
	 |) 
	 (|
	   where(PRE -> pre_cond(P2, C))
	   Resolve(C, bool -> C1)
	   where(pre_cond(P2, C1) -> PRE1)
	 ||
	   where(PRE_CONDITION'nil -> PRE1)
	 |)
	 (|
	   -- SMLWanted()
	   -- withdrawn for now because implicit functions not translated
	   eq(0,1)
	   Maxtype(T1 -> Tm)  -- must be maximal or conditions might not be generated
	   Args_in_subtypes(PARMS, Tm -> COND1)
	   Simplify(COND1 -> COND2)
	   (|
	     (| where(COND2 -> literal_expr(_,bool_true))
		|| where(COND2 -> no_val) |)
	     where(OPT_CONDITION'nil -> COND)
	   ||
	     where(OPT_CONDITION'condition(COND2) -> COND)
	   |)
	 ||
	   where(OPT_CONDITION'nil -> COND)
	 |)
	 I'Def <- impl_fun(PARMS, post_cond(P1,R,E1), PRE1, COND)
	 [|
	   CPPWanted()
	   Localise_value_env()
	 |]
	 Closeenv()
-- debug
-- Putmsg("Definition of ")
-- Print_id_or_op(F)
-- Putmsg(":  ")
-- Print_post_condition(post_cond(P1,R,E1))
-- Putnl()
-- [|
--   where(PRE1 -> pre_cond(_, X))
--   Putmsg("pre ")
--   Print_expr(X)
--   Putnl()
-- |]


-- debug
/*  'rule' Resolve_value_def(X)
 print("Debug - Value-def")
 print(X)*/

'action' Make_parm_bindings(POS, INT, PRODUCT_TYPE -> BINDINGS)

  'rule' Make_parm_bindings(P, N, list(T, Ts) ->  list(B, Bs)):
	 IncreaseCol(P -> NewP) -- Added by jiperna: Unique positions required all the time...
	 Make_binding(NewP, N -> B)
	 Make_parm_bindings(NewP, N+1, Ts -> Bs)

  'rule' Make_parm_bindings(_, _, nil -> nil):

'action' Args_in_subtypes(FORMAL_FUNCTION_PARAMETERS, TYPE_EXPR -> VALUE_EXPR)

  'rule' Args_in_subtypes(list(form_parm(Pos, BL), Tail), T -> V):
	 Make_function_type(T -> fun(T0, _, result(T1,_,_,_,_)))
	 Bindings_to_act_expr(Pos, BL, T0 -> E0)
	 Isin_subtype(E0, T0 -> V0)
	 Args_in_subtypes(Tail, T1 -> V1)
	 where(ax_infix(Pos, V0, and, V1, Pos) -> V)

  'rule' Args_in_subtypes(nil, _ -> no_val):

'action' Bindings_to_act_expr(POS, BINDINGS, TYPE_EXPR -> VALUE_EXPR)

  'rule' Bindings_to_act_expr(Pos, nil, _ -> skip(Pos))

  'rule' Bindings_to_act_expr(Pos, BL:list(B, Tail), T -> V):
	 (|
	   where(Tail -> nil)
	   Binding_to_act_expr(B, T -> V)
	 ||
	   Length_bs(BL -> N)
	   Make_product_type(T, N -> product(TL))
	   Bindings_to_act_exprs(BL, TL -> VL)
	   where(VALUE_EXPR'product(Pos, VL) -> V)
	 |)

'action' Bindings_to_act_exprs(BINDINGS, PRODUCT_TYPE -> VALUE_EXPRS)

  'rule' Bindings_to_act_exprs(list(B, BL), list(T, TL) -> list(V, VL)):
	 Binding_to_act_expr(B, T -> V)
	 Bindings_to_act_exprs(BL, TL -> VL)

  'rule' Bindings_to_act_exprs(nil, _ -> nil):

'action' Binding_to_act_expr(BINDING, TYPE_EXPR -> VALUE_EXPR)

  'rule' Binding_to_act_expr(B, bracket(T) -> V):
	 Binding_to_act_expr(B, T -> V)

  'rule' Binding_to_act_expr(single(Pos, Id), T -> val_occ(Pos, I, nil)):
	 New_value_id(Pos, Id -> I)
	 [|
	   CPPWanted()
	   Localise_value_id(I)
	 |]
	 Maxtype(T -> Tm)  -- must be maximal or conditions might not be generated
	 I'Type <- Tm

  'rule' Binding_to_act_expr(B, defined(I, _) -> V):
	 I'Type -> abbrev(T)
	 Binding_to_act_expr(B, T -> V)

  'rule' Binding_to_act_expr(product(Pos, BL), product(TL) -> product(Pos, VL)):
	 Bindings_to_act_exprs(BL, TL -> VL)

-- debug
--  'rule' Binding_to_act_expr(B, T -> no_val):
-- print(B)
-- print(T)

'action' Store_multiple_expl_value_def(BINDING, LET_DEFS)

  'rule' Store_multiple_expl_value_def(single(P, Id), LDS):
         Get_current_top_values(-> VE)
         Select_id_by_pos(P, VE -> value_id(I))
         -- avoid clashes in C++ translation between different
         -- values sharing the same let expression
         -- BUT no longer needed
--       where(LDS -> list(explicit(P1, binding(P2, product(P3, Bs)), E), nil))
--       Re_position_bindings(P, Bs -> Bs1)
--       where(LET_DEFS'list(explicit(P1, binding(P2, product(P3, Bs1)), E), nil) -> LDS1)
         where(let_expr(P, LDS, named_val(P, name(P, Id))) -> V)
         I'Type -> T
         Resolve_type(T -> T1)
         I'Type <- T1
         Resolve(V, T1 -> V1)
         Maxtype(T1 -> Tm)
         -- get best type: ignoring disambiguation
         Type_of_val(V1, Tm -> T2)
         string_to_id("RSL_res_" -> Z)
         New_value_id(P, id_op(Z) -> Ip)
         Ip'Type <- T2
         Isin_subtype(val_occ(P,Ip,nil), T1 -> Pred)
         Simplify(Pred -> Pred1)
         (|
           ne(Pred1, no_val)
           I'Def <- expl_val(V1, condition(Pred1))
         ||
           I'Def <- expl_val(V1, nil) 
         |)
-- debug
-- Putmsg("Definition of ")
-- Print_id_or_op(Id)
-- Putmsg(": = ")
-- Print_expr(let_expr(P, LDS, named_val(P, name(P, Id))))
-- Putnl()

  'rule' Store_multiple_expl_value_def(product(P, list(B, BS)), LDS):
	 Store_multiple_expl_value_def(B, LDS)
	 Store_multiple_expl_value_def(product(P, BS), LDS)

  'rule' Store_multiple_expl_value_def(product(_, nil), _):

'action' Re_position_bindings(POS, BINDINGS -> BINDINGS)

  'rule' Re_position_bindings(P, list(B, Bs) -> list(B1, Bs1)):
	 Re_position_binding(P, B -> B1)
	 Re_position_bindings(P, Bs -> Bs1)

  'rule' Re_position_bindings(_, nil -> nil):

'action' Re_position_binding(POS, BINDING -> BINDING)

  'rule' Re_position_binding(P, single(_, Id) -> single(P, Id)):

  'rule' Re_position_binding(P, product(P1, Bs) -> product(P1, Bs1)):
	 Re_position_bindings(P, Bs -> Bs1)

'action' Store_multiple_impl_value_def(BINDING, VALUE_EXPR)

  'rule' Store_multiple_impl_value_def(single(P, Id), V):
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(P, VE -> value_id(I))
	 I'Def <- impl_val(V)
	 I'Type -> T
	 Resolve_type(T -> T1)
	 I'Type <- T1
-- debug
-- Putmsg("Definition of ")
-- Print_id_or_op(Id)
-- Putmsg(": :- ")
-- Print_expr(V)
-- Putnl()

  'rule' Store_multiple_impl_value_def(product(P, list(B, BS)), V):
	 Store_multiple_impl_value_def(B, V)
	 Store_multiple_impl_value_def(product(P, BS), V)

  'rule' Store_multiple_impl_value_def(product(_, nil), _)

-- replace idents with ident plus pos
'action' Localise_env

  'rule' Localise_env:
	 Localise_module_env
	 Localise_type_env
	 Localise_value_env
	 Localise_variable_env

'action' Localise_module_env

  'rule' Localise_module_env:
	 Get_current_modules(-> ME)
	 Localise_module_env1(ME)

'action' Localise_module_env1(MODULE_ENV)

  'rule' Localise_module_env1(object_env(I, ME)):
	 Localise_object_id(I)
	 Localise_module_env1(ME)

  'rule' Localise_module_env1(nil):

'action' Localise_object_id(Object_id)

  'rule' Localise_object_id(I):
	 I'Ident -> Id
	 I'Pos -> Pos
	 Localise_id(Pos, Id -> Id1)
	 I'Ident <- Id1

'action' Localise_value_env

  'rule' Localise_value_env:
	 Get_current_top_values(-> Ids)
	 Localise_value_ids(Ids)

'action' Localise_value_ids(Value_ids)

  'rule' Localise_value_ids(list(I, Ids)):
	 Localise_value_id(I)
	 Localise_value_ids(Ids)

  'rule' Localise_value_ids(nil):

'action' Localise_value_id(Value_id)

  'rule' Localise_value_id(I):
	 [|
	   I'Ident -> id_op(Id)
	   I'Pos -> Pos
	   Localise_id(Pos, Id -> Id1)
	   I'Ident <- id_op(Id1)
	 |]

'action' Localise_type_env

  'rule' Localise_type_env:
	 Get_current_types(-> TE)
	 Localise_type_ids(TE)

'action' Localise_type_ids(TYPE_ENV)

  'rule' Localise_type_ids(type_env(I, TE)):
	 I'Pos -> Pos
	 I'Ident -> Id
	 Localise_id(Pos, Id -> Id1)
	 I'Ident <- Id1
	 Localise_type_ids(TE)

  'rule' Localise_type_ids(nil):

'action' Localise_variable_env

  'rule' Localise_variable_env:
	 Get_current_variables(-> VE)
	 Localise_variable_ids(VE)

'action' Localise_variable_ids(VARIABLE_ENV)

  'rule' Localise_variable_ids(variable_env(I, VE)):
	 I'Pos -> Pos
	 I'Ident -> Id
	 Localise_id(Pos, Id -> Id1)
	 I'Ident <- Id1
	 Localise_variable_ids(VE)

  'rule' Localise_variable_ids(nil):

'action' Localise_id(POS, IDENT -> IDENT)

  'rule' Localise_id(Pos, Id -> Id1):
	 id_to_string(Id -> S1)
	 Pos_to_string(Pos -> S2)
	 Concatenate3(S1, "_", S2 -> S)
	 string_to_id(S -> Id1)



'action' Resolve_variable_defs(VARIABLE_DEFS)

  'rule' Resolve_variable_defs(list(D, DS)):
	 Resolve_variable_def(D)
	 Resolve_variable_defs(DS)

  'rule' Resolve_variable_defs(nil):

'action' Resolve_variable_def(VARIABLE_DEF)

  'rule' Resolve_variable_def(single(P, Id, _, Init)):
	 Get_current_variables(-> VARS)
	 Lookup_env_variable_id(Id, nil, VARS -> variable_id(I))
	 I'Type -> T
	 Resolve_type(T -> T1)
	 I'Type <- T1
	 [|
	   where(Init -> initial(V))
	   Resolve(V, T1 -> V1)
	   I'Init <- initial(V1)
	   (| -- ignore any disambiguation
	     where(V1 -> disamb(_, V2, _))
	   ||
	     where(V1 -> V2)
	   |)
	   Maxtype(T1 -> Tm)
	   -- get best type
	   Type_of_val(V2, Tm -> T2)
	   string_to_id("z__" -> Z)
	   New_value_id(P, id_op(Z) -> Ip)
	   Ip'Type <- T2
	   Isin_subtype(val_occ(P,Ip,nil), T1 -> Pred)
	   Simplify(Pred -> Pred1)
	   ne(Pred1, no_val)
	   where(VALUE_EXPR'function(
			P,
			s_typing(P, single(P, single(P, id_op(Z)), T2)),
			Pred1) -> Cond)
	   I'Subtype <- condition(Cond)
	 |]
	 [|
	   SQLWanted()
	   Add_to_table_types(T)
	 |]

  'rule' Resolve_variable_def(multiple(P, list(Id,Ids), _)):
	 Get_current_variables(-> VARS)
	 Lookup_env_variable_id(Id, nil, VARS -> variable_id(I))
	 I'Type -> T
	 Resolve_type(T -> T1)
	 I'Type <- T1
	 [|
	   SQLWanted()
	   Add_to_table_types(T)
	 |]
	 Store_variable_types(Ids, VARS, T1)


'action' Store_variable_types(IDENTS, VARIABLE_ENV, TYPE_EXPR)

  'rule' Store_variable_types(list(Id, Ids), VARS, T):
	 Lookup_env_variable_id(Id, nil, VARS -> variable_id(I))
	 I'Type <- T
	 [|
	   SQLWanted()
	   Add_to_table_types(T)
	 |]
	 Store_variable_types(Ids, VARS, T)

  'rule' Store_variable_types(nil,_,_):

'action' Resolve_channel_defs(CHANNEL_DEFS)

  'rule' Resolve_channel_defs(list(D, DS)):
	 Resolve_channel_def(D)
	 Resolve_channel_defs(DS)

  'rule' Resolve_channel_defs(nil):

'action' Resolve_channel_def(CHANNEL_DEF)

  'rule' Resolve_channel_def(single(P, Id, _)):
	 Get_current_channels(-> CHS)
	 Lookup_env_channel_id(Id, CHS -> channel_id(I))
	 I'Type -> T
	 Resolve_type(T -> T1)
	 I'Type <- T1

  'rule' Resolve_channel_def(multiple(P, list(Id,Ids), _)):
	 Get_current_channels(-> CHS)
	 Lookup_env_channel_id(Id, CHS -> channel_id(I))
	 I'Type -> T
	 Resolve_type(T -> T1)
	 I'Type <- T1
	 Store_channel_types(Ids, CHS, T1)

'action' Store_channel_types(IDENTS, CHANNEL_ENV, TYPE_EXPR)

  'rule' Store_channel_types(list(Id, Ids), CHS, T):
	 Lookup_env_channel_id(Id, CHS -> channel_id(I))
	 I'Type <- T
	 Store_channel_types(Ids, CHS, T)

  'rule' Store_channel_types(nil,_,_):



'action' Resolve_axiom_defs(AXIOM_DEFS)

  'rule' Resolve_axiom_defs(list(D, DS)):
	 Resolve_axiom_def(D)
	 Resolve_axiom_defs(DS)

  'rule' Resolve_axiom_defs(nil):

'action' Resolve_axiom_def(AXIOM_DEF)

  'rule' Resolve_axiom_def(axiom_def(P, Oid, V)):
	 Get_current_axioms(-> AXS)
	 Lookup_axiom(P, AXS -> I)
	 Resolve(V, bool -> V1)
	 I'Axiom <- V1

'action' Lookup_axiom(POS, AXIOM_ENV -> Axiom_id)

-- Lookup must be by POS
-- assumes all checked ok, so search bound to succeed
  'rule' Lookup_axiom(P, axiom_env(I, AXS) -> I1):
	 I'Pos -> P1
	 (|
	   eq(P, P1)
	   where(I -> I1)
	 ||
	   Lookup_axiom(P, AXS -> I1)
	 |)

'action' Resolve_test_case_defs(TEST_CASE_DEFS)

  'rule' Resolve_test_case_defs(list(D, DS)):
	 Resolve_test_case_def(D)
	 Resolve_test_case_defs(DS)

  'rule' Resolve_test_case_defs(nil):

'action' Resolve_test_case_def(TEST_CASE_DEF)

  'rule' Resolve_test_case_def(test_case_def(P, Oid, V)):
	 Get_current_test_cases(all -> TCS)
	 Lookup_test_case(P, TCS -> I)
	 Make_results(V -> list(result(T,_,_,_,_),_))
	 Resolve(V, T -> V1)
	 I'Test_case <- V1
	 I'Type <- T

'condition' Lookup_test_case(POS, TEST_CASE_ENV -> Test_case_id)

-- Lookup must be by POS
-- assumes all checked ok, so search bound to succeed
-- but in cpp.g, may fail if test_case is not in top class
  'rule' Lookup_test_case(P, test_case_env(I, AXS) -> I1):
	 I'Pos -> P1
	 (|
	   eq(P, P1)
	   where(I -> I1)
	 ||
	   Lookup_test_case(P, AXS -> I1)
	 |)

-----------------------------------------------------------
-- Transition systems declarations:
-----------------------------------------------------------

'action' Resolve_trans_sys_defs(TRANSITION_SYS_DEFS)

  'rule' Resolve_trans_sys_defs(list(D, DS)):
	 Resolve_trans_sys_def(D)
	 Resolve_trans_sys_defs(DS)

  'rule' Resolve_trans_sys_defs(nil):

'action' Concat_Vars(VARIABLE_DEFS, VARIABLE_DEFS -> VARIABLE_DEFS)
  'rule' Concat_Vars(nil, Vars -> Vars)
  'rule' Concat_Vars(Vars, nil -> Vars)

  'rule' Concat_Vars(list(Var1,Vars1), Vars2 -> list(Var1,Vars3))
         Concat_Vars(Vars1, Vars2 -> Vars3)

'action' Get_priority_vars(TRANSITION_OPERATOR, INT, POS -> VARIABLE_DEFS, INT, POS)
  'rule' Get_priority_vars(equal_priority(L, R, _), Count, P -> Vars, Count3, P3)
         Get_priority_vars(L, Count, P -> Vars1, Count2, P2)
         Get_priority_vars(R, Count2, P2 -> Vars2, Count3, P3)
         Concat_Vars(Vars1, Vars2 -> Vars)

  'rule' Get_priority_vars(greater_priority(L, R, _), Count, P -> Vars, Count4, P5)
         --DefaultPos(-> P)
         Get_priority_vars(L, Count, P -> Vars1, Count2, P2)
         IncreaseCol(P2 -> P3)
         IncreaseCol(P3 -> P4)
         Make_concatenation("possible_", Count2 -> S)
	 string_to_id(S -> ID)
         where(Count2 + 1 -> Count3)
         where(VARIABLE_DEF'single(P4, ID, bool, initial(literal_expr(P,bool_true))) -> VarDecl)
         Get_priority_vars(R, Count3, P4 -> Vars2, Count4, P5)
         Concat_Vars(list(VarDecl,nil), Vars1 -> Vars3)
         Concat_Vars(Vars3, Vars2 -> Vars)

  'rule' Get_priority_vars(bracketed(TO,_), Count, P -> Vars, Count2, P2)
         Get_priority_vars(TO, Count, P -> Vars, Count2, P2)

  'rule' Get_priority_vars(guarded_command(_,_), Count, P -> nil, Count, P)



'action' Resolve_trans_sys_def(TRANSITION_SYS_DEF)

  'rule' Resolve_trans_sys_def(trans_sys_def(P, TS, Defs)):
	 Get_current_transition_systems(all -> TCS)
	 where(Defs -> desc(Input, Local,Transitions))
	 Lookup_trans_sys(P, TCS -> I)

	 Get_current_with(-> WITH)
	 Current -> C
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 -- Add implicitely the 'primed variables' (future state vars in SAL)
	 where(Input -> variable_decl(PI, InputDecl))
	 Generate_Primes(InputDecl -> InputPrimes)
	 where(Local -> variable_decl(PL, LocalDecl))
         Get_priority_vars(Transitions, 1, PL -> PossibleDecl, _, _)
         Concat_Vars(LocalDecl, PossibleDecl -> NewLocalDecl)
         where(variable_decl(PL, NewLocalDecl) -> NewLocal)
	 Generate_Primes(NewLocalDecl -> LocalPrimes)
	 -- Collect the input and local declarations
	 where(DECLS'list(Input,list(variable_decl(PI, InputPrimes), list(Local,list(variable_decl(PL, LocalPrimes), 
list(variable_decl(PL, PossibleDecl),
nil))))) -> DS)

	 Make_basic_env(basic(DS))
	 Complete_type_env(basic(DS))
	 Make_value_env(basic(DS))
	 Check_value_env(basic(DS))
	 Resolve_class(basic(DS))
GetExtraCommands(PossibleDecl, nil -> EU)
	 Resolve_transitions(Transitions, 1, nil, EU, TS -> RTrans, _, _, ExtraProps)

         (|
           where(ExtraProps -> assertion(V))
           Resolve(V, bool -> VRes)
           where(assertion(VRes) -> ExtraPropsRes)
         ||
           where(ExtraProps -> nil)
           where(ExtraProps -> ExtraPropsRes)
         |)

	 -- Extract the resolved version from the Resolution:
	 Extract_Resolved(Input -> RInput)
	 Extract_Resolved(NewLocal -> RLocal)
	 Extract_Resolved(variable_decl(PI, InputPrimes) -> RInputPrimes)
	 Extract_Resolved(variable_decl(PL, LocalPrimes) -> RLocalPrimes)
	 -- Update the information in the TS-id
	 where(RESOLVED_SYSTEM_DESCRIPTION'desc(RInput, RLocal, RInputPrimes, RLocalPrimes, RTrans, ExtraPropsRes) -> Resolved)
	 I'Trans_sys <- Resolved
	 -- Restoring the state:
	 Current -> current_env(CE, C1)
	 Current <- C1
	 Extend_paths <- Paths
         --Resolve_property_defs(ExtraProps)


  'rule' Resolve_trans_sys_def(trans_sys_def(P, TS, Defs)):
	 Get_current_transition_systems(all -> TCS)
	 where(Defs -> no_input(Local,Transitions))
	 Lookup_trans_sys(P, TCS -> I)

	 Get_current_with(-> WITH)
	 Current -> C
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 -- Add implicitely the 'primed variables' (future state vars in SAL)
	 where(Local -> variable_decl(PL, LocalDecl))
         Get_priority_vars(Transitions, 1, PL -> PossibleDecl, _, _)
         Concat_Vars(LocalDecl, PossibleDecl -> NewLocalDecl)
         where(variable_decl(PL, NewLocalDecl) -> NewLocal)
	 Generate_Primes(NewLocalDecl -> LocalPrimes)
         Concat_Vars(LocalPrimes, PossibleDecl -> NewLocalVars)
	 -- Collect the input and local declarations
	 where(DECLS'list(Local,list(variable_decl(PL, NewLocalVars), nil)) -> DS)

	 Make_basic_env(basic(DS))
	 Complete_type_env(basic(DS))
	 Make_value_env(basic(DS))
	 Check_value_env(basic(DS))
	 Resolve_class(basic(DS))
GetExtraCommands(PossibleDecl, nil -> EU)
	 Resolve_transitions(Transitions, 1, nil, EU, TS -> RTrans, _, _, ExtraProps)

         --Resolve_property_defs(ExtraProps)
         /*(|
           where(ExtraProps -> assertion(V))
           Resolve(V, bool -> VRes)
           where(assertion(VRes) -> ExtraPropsRes)
         ||
           where(ExtraProps -> nil)
           where(ExtraProps -> ExtraPropsRes)
         |)*/
where(ExtraProps -> ExtraPropsRes)

	 -- Extract the resolved version from the Resolution:
	 Extract_Resolved(NewLocal -> RLocal)
	 Extract_Resolved(variable_decl(PL, LocalPrimes) -> RLocalPrimes)
	 -- Update the information in the TS-id
	 where(RESOLVED_SYSTEM_DESCRIPTION'no_input(RLocal, RLocalPrimes, RTrans, ExtraPropsRes) -> Resolved)
	 I'Trans_sys <- Resolved

	 -- Restoring the state:
	 Current -> current_env(CE, C1)
	 Current <- C1
	 Extend_paths <- Paths

--         Resolve_property_defs(ExtraProps)



'action' Concat_Extra_Guards(EXTRA_GUARD, EXTRA_GUARD -> EXTRA_GUARD)

  'rule' Concat_Extra_Guards(nil, nil -> nil)
  'rule' Concat_Extra_Guards(A, nil -> A)
  'rule' Concat_Extra_Guards(nil, B -> B)

  'rule' Concat_Extra_Guards(guard(Val1,P1), guard(Val2,P2) -> guard(ax_infix(P1,Val1,or,Val2,P2),P1))

'action' GetGuardValueExpression(VALUE_EXPR, EXTRA_GUARD -> VALUE_EXPR)

  'rule' GetGuardValueExpression(Val, nil -> Val)

  'rule' GetGuardValueExpression(Val1, guard(Val2,P) -> ax_infix(P,ax_prefix(P,not,Val2),and,Val1,P))

'action' Concat_Commands(COMMANDS, COMMANDS -> COMMANDS)
  'rule' Concat_Commands(nil, U -> U)
  'rule' Concat_Commands(U, nil -> U)

  'rule' Concat_Commands(list(H,Rest), List -> list(H,List2))
         Concat_Commands(Rest, List -> List2)

'action' GetExtraCommands(VARIABLE_DEFS, COMMANDS -> COMMANDS)
  'rule' GetExtraCommands(nil, Commands -> Commands)

  'rule' GetExtraCommands(list(VarDecl,Tail),  EU -> Commands)
         where(VarDecl -> single(P1, ID, bool, initial(literal_expr(P2,bool_true))))
         id_to_string(ID -> S)
	 Concatenate(S, "'" -> S2)
	 string_to_id(S2 -> IDPrime)
         where(COMMANDS'list(cmd(P1,name(P1,id_op(IDPrime)),literal_expr(P1,bool_true)),nil) -> NewUpdateCommand)
	 Concat_Commands(EU, NewUpdateCommand -> NewUpdateCommands)
         GetExtraCommands(Tail, NewUpdateCommands -> Commands)
         


'action' SetPos(EXTRA_GUARD, POS -> EXTRA_GUARD, POS)
  'rule' SetPos(nil, P -> nil, P)
  'rule' SetPos(guard(Val,_),P -> guard(Val,P), P2)
         IncreaseCol(P -> P2)

'action' Concat_Property_Decls(PROPERTY_DECLS, PROPERTY_DECLS -> PROPERTY_DECLS)
  'rule' Concat_Property_Decls(nil, Props -> Props)

  'rule' Concat_Property_Decls(Props, nil -> Props)

  'rule' Concat_Property_Decls(list(H,Tail), Props -> list(H,Props2))
         Concat_Property_Decls(Tail, Props -> Props2)

'action' Concat_Extra_Assertion(EXTRA_ASSERTION, EXTRA_ASSERTION -> EXTRA_ASSERTION)
  'rule' Concat_Extra_Assertion(V1, nil -> V1)

  'rule' Concat_Extra_Assertion(nil, V2 -> V2)

  'rule' Concat_Extra_Assertion(assertion(V1), assertion(V2) -> assertion(ax_infix(P,V1,and,V2,P)))
         DefaultPos(-> P)         

'action' Concat_Value_Exprs(VALUE_EXPRS, VALUE_EXPRS -> VALUE_EXPRS)

  'rule' Concat_Value_Exprs(Vals, nil -> Vals)

  'rule' Concat_Value_Exprs(nil, Vals -> Vals)

  'rule' Concat_Value_Exprs(list(H,T), Vals -> list(H, Tail))
         Concat_Value_Exprs(T, Vals -> Tail)

'action' Resolve_transitions(TRANSITION_OPERATOR, INT, EXTRA_GUARD, COMMANDS, IDENT -> TRANSITION_OPERATOR, INT, EXTRA_GUARD, EXTRA_ASSERTION)

  'rule' Resolve_transitions(equal_priority(L,R,G), Count, EG, EU, TS -> equal_priority(LRes,RRes,GRes), Count3, G, Props)
         Resolve_transitions(L, Count, EG, EU, TS -> LRes, Count2, _, Props1)
         Resolve_transitions(R, Count2, EG, EU, TS -> RRes, Count3, _, Props2)
         Concat_Extra_Assertion(Props1, Props2 -> Props)
	 Resolve_extraguard(G -> GRes)

  'rule' Resolve_transitions(greater_priority(L,R,G), Count, EG, EU, TS -> Res, Count5, G, Props)
         Resolve_transitions(L, Count, EG, EU, TS -> LRes, Count2, EG2, Props1)
         Concat_Extra_Guards(EG, EG2 -> EGRes)
         Make_concatenation("possible_", Count2 -> S)
	 string_to_id(S -> ID)

         where(EGRes -> guard(Val, P))
	 Concatenate(S, "'" -> S2)
	 string_to_id(S2 -> IDPrime)
         where(guarded_command(guarded_cmd(
nil,
ax_prefix(P,not,Val),
list(cmd(P,name(P,id_op(IDPrime)),literal_expr(P, bool_false)),nil)),nil) -> ExtraTrans)
         where(guard(named_val(P,name(P,id_op(ID))),P) -> EG3)
         Concat_Extra_Guards(EG, EG3 -> NewEG)
         where(Count2+1 -> Count3)

         Resolve(ax_infix(P,ax_prefix(P,not,named_val(P,name(P,id_op(ID)))),implies,ax_prefix(P,not,Val),P), bool -> ResExpr)

         where(ResExpr -> PropExpr)

         Resolve_transitions(ExtraTrans, Count3, nil, nil, TS -> ExtraTransRes, Count4, _, _)
         Resolve_transitions(R, Count4, NewEG, EU, TS -> RRes, Count5, _, Props2)
 
         Concat_Extra_Assertion(Props1, assertion(PropExpr) -> PropsTemp)
         Concat_Extra_Assertion(PropsTemp, Props2 -> Props)

	 Resolve_extraguard(G -> GRes)
         where(equal_priority(LRes,ExtraTransRes,nil) -> Res1)
         where(equal_priority(Res1, RRes, nil) -> Res)

  'rule' Resolve_transitions(bracketed(TO,G), Count, EG, EU, TS -> bracketed(TORes,GRes), Count2, G, Props)
         Resolve_transitions(TO, Count, EG, EU, TS -> TORes, Count2, _, Props)
	 Resolve_extraguard(G -> GRes)

  'rule' Resolve_transitions(guarded_command(CM,G), Count, EG, EU, _ -> guarded_command(CMRes,GRes), Count, G, nil)
         Resolve_transition(CM, EG, EU -> CMRes)
--print(CMRes)
	 Resolve_extraguard(G -> GRes)

'action' Resolve_extraguard(EXTRA_GUARD -> EXTRA_GUARD)
  'rule' Resolve_extraguard(nil -> nil)

  'rule' Resolve_extraguard(guard(Val,P) -> guard(ValRes,P))
         Resolve(Val, bool -> ValRes)

'action' Resolve_transition(GUARDED_COMMAND, EXTRA_GUARD, COMMANDS -> GUARDED_COMMAND)

  'rule' Resolve_transition(guarded_cmd(Desc, Guard, Commands), EG, EU -> ResolvedCmd)
         GetGuardValueExpression(Guard, EG -> NewGuard)
	 Resolve(NewGuard, bool -> ResolvedGuard)
         Concat_Commands(Commands, EU -> NewCommands)
	 Resolve_Commands(NewCommands -> ResolvedCommands)
	 where(guarded_cmd(Desc, ResolvedGuard, ResolvedCommands) -> ResolvedCmd)


  'rule' Resolve_transition(else_cmd(Desc, Commands), _, EU -> ResolvedCmd)
         Concat_Commands(Commands, EU -> NewCommands)
	 Resolve_Commands(NewCommands -> ResolvedCommands)
	 where(else_cmd(Desc, ResolvedCommands) -> ResolvedCmd)

  'rule' Resolve_transition(comprehended_cmd(TPS, Pos, Cmd), EG, EU -> comprehended_cmd(TPS1, Pos, RCmd))
         --check_typings(TPS -> )
	 Resolve_value_typings(TPS -> TPS1)
         --check_typings(TPS1 ->)
	 Openenv()
	 Define_value_typings(TPS1)
	 Resolve_transition(Cmd, EG, EU -> RCmd)
	 Closeenv()

'action' Resolve_Commands(COMMANDS -> COMMANDS)

  'rule' Resolve_Commands(list(cmd(P,N,E), ES) -> list(r_cmd(RE),RES))
	 where(assignment(P, N, E) -> NewExpr)
	 Resolve(NewExpr, unit -> RE)
	 Resolve_Commands(ES -> RES)

  'rule' Resolve_Commands(list(array_cmd(P,N,I,E), ES) -> list(r_cmd(RE),RES))
         where(array_assignment(P,N,I,E) -> NewExpr)
         Resolve(NewExpr, unit -> RE)
         Resolve_Commands(ES -> RES)

  'rule' Resolve_Commands(nil -> nil)

'condition' Lookup_trans_sys(POS, TRANS_SYS_ENV -> Transition_system_id)

-- Lookup must be by POS
-- assumes all checked ok, so search bound to succeed
-- but in cpp.g, may fail if trans_sys is not in top class
  'rule' Lookup_trans_sys(P, trans_sys_env(I, AXS) -> I1):
	 I'Pos -> P1
	 (|
	   eq(P, P1)
	   where(I -> I1)
	 ||
	   Lookup_trans_sys(P, AXS -> I1)
	 |)

'action' Extract_Resolved(DECL -> DECL)

  'rule' Extract_Resolved(variable_decl(Pos, Decls) -> variable_decl(Pos, RDecls))
	 Internal_Extract_Resolved(Decls -> RDecls)

'action' Internal_Extract_Resolved(VARIABLE_DEFS -> VARIABLE_DEFS)

  'rule' Internal_Extract_Resolved(list(H, Rest) -> list(RH, RRest))
	 where(H -> single(Pos, Id, Type, Init))
	 Get_current_variables(-> VARS)
	 Lookup_env_variable_id(Id, nil, VARS -> variable_id(I))
	 I'Type -> ResolvedType
	 I'Init -> ResolvedInit
	 where(VARIABLE_DEF'single(Pos,Id,ResolvedType,ResolvedInit) -> RH)
	 Internal_Extract_Resolved(Rest -> RRest)

  'rule' Internal_Extract_Resolved(list(H, Rest) -> list(H, RRest))
	 where(H -> multiple(_,_,_))
	 -- don't waste time resolving it (this functionality is for SAL translation and
	 -- SAL doesn't translate multiple var decls...
	 Internal_Extract_Resolved(Rest -> RRest)

  'rule' Internal_Extract_Resolved(nil -> nil)

-----------------------------------------------------------------
-- Resolve LTL properties
-----------------------------------------------------------------
'action' Resolve_property_defs(PROPERTY_DECLS)

  'rule' Resolve_property_defs(list(Prop,Props))
	 Resolve_property_def(Prop)
	 Resolve_property_defs(Props)

  'rule' Resolve_property_defs(nil)

'action' Resolve_property_def(PROPERTY_DECL)

  'rule' Resolve_property_def(property_def(Pos, PropIdent, Ident, Prop)):
         FDRWanted()
	 Get_current_properties(all -> Prop_env)
	 Lookup_property(Pos, Prop_env -> PropId)
         (|
           Lookup_value_name(Pos, name(Pos, id_op(Ident)) -> list(I, nil))
	   -- Enable the use of LTL operators:
	   Set_LTL_Wanted()
	   -- Now Resolve the property:
	   Resolve(Prop, bool -> ResolvedProp)
	   -- Updating the resolved information:
	   where(r_prop_csp(Pos, PropIdent, I, ResolvedProp) -> Resolved)
	   PropId'Resolved_Prop <- Resolved
	   -- Disable the use of LTL operators:
	   Clear_LTL_Wanted()
         ||
           Puterror(Pos)
           Putmsg("Cannot find process ")
           Print_id(Ident)
           Putnl()
         |)

  'rule' Resolve_property_def(property_def(Pos, Ident, TS_Ident, Prop))
	 Get_current_transition_systems(all -> TS_env)
	 Get_Transition_System(TS_Ident, TS_env -> OptTSId)
	     where(OptTSId -> ts_id(TSId))
	     Get_current_properties(all -> Prop_env)
	     -- Updating the information about the TS in the property_id:
	     Lookup_property(Pos, Prop_env -> PropId)
	     TSId'System -> TS_Decls
	  ---------------------------------------------------------
	     where(TS_Decls -> desc(Input, Local, Transitions))
	     -- Put the valid variables (from the TS) in the current new env:
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
	     -- Now Resolve the property:
	     Resolve(Prop, bool -> ResolvedProp)
	     -- Updating the resolved information:
	     where(r_prop(Pos, Ident, TSId, ResolvedProp) -> Resolved)
	     PropId'Resolved_Prop <- Resolved
	     -- Disable the use of LTL operators:
	     Clear_LTL_Wanted()
	     -- Removing this "fake" environment
	     Current -> current_env(CE, C1)
	     Current <- C1
	     Extend_paths <- Paths

  'rule' Resolve_property_def(property_def(Pos, Ident, TS_Ident, Prop))
	 Get_current_transition_systems(all -> TS_env)
	 Get_Transition_System(TS_Ident, TS_env -> OptTSId)
	 (|
	     where(OptTSId -> ts_id(TSId))
	     Get_current_properties(all -> Prop_env)
	     -- Updating the information about the TS in the property_id:
	     Lookup_property(Pos, Prop_env -> PropId)
	     TSId'System -> TS_Decls
	  ---------------------------------------------------------
	     where(TS_Decls -> no_input(Local, Transitions))
	     -- Put the valid variables (from the TS) in the current new env:
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
	     -- Now Resolve the property:
	     Resolve(Prop, bool -> ResolvedProp)
	     -- Updating the resolved information:
	     where(r_prop(Pos, Ident, TSId, ResolvedProp) -> Resolved)
	     PropId'Resolved_Prop <- Resolved
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
Print_id(TS_Ident)
	 |)

'condition' Lookup_property(POS, PROPERTY_ENV -> Property_id)

-- Lookup must be by POS
-- assumes all checked ok, so search bound to succeed
-- but in cpp.g, may fail if property is not in top class
  'rule' Lookup_property(P, prop_env(I, AXS) -> I1):
	 I'Pos -> P1
	 (|
	   eq(P, P1)
	   where(I -> I1)
	 ||
	   Lookup_property(P, AXS -> I1)
	 |)
	 
-----------------------------------------------------------------
-- Resolve type expressions
-----------------------------------------------------------------

'action' Resolve_type(TYPE_EXPR -> TYPE_EXPR)

  'rule' Resolve_type(named_type(N) -> defined(I,Q)):
	 Lookup_type_name(N -> type_id(I))
	 (|
	   where(N -> name(_,_))
	   (|  -- may be affected by WITH
	     I'Qualifier -> list(Id, _)
	     I'Pos -> P
	     Qualify_by_with(P, Id -> Q)
	   ||
	     where(OPT_QUALIFICATION'nil -> Q)
	   |)
	 ||
	   where(N -> qual_name(_, Obj, _))
--	   I'Qualifier -> Ids
	   Resolve_object(Obj -> Obj1)
	   where(qualification(Obj1) -> Q)
	 |)
/*         (|
           --I'Type -> abbrev(TypeExpr)
           --Resolve_type(TypeExpr -> ResTypeExpr)
           --I'Type <- abbrev(ResTypeExpr)
           I'Type -> abbrev(TypeExprTemp)
           Remove_Brackets(TypeExprTemp -> TypeExpr)
           where(TypeExpr -> array(IT,VT))
           (|
             where(IT -> named_type(_))
             Resolve_type(IT -> IT2)
           ||
             where(IT -> IT2)
           |)
           (|
             where(VT -> named_type(_))
             Resolve_type(VT -> VT2)
           ||
             where(VT -> VT2)
           |)
           where(array(IT2, VT2) -> TypeExpr2)
           I'Type <- abbrev(TypeExpr2)
           where(defined(I,Q) -> Res)
         ||
           where(defined(I,Q) -> Res)
         |)*/


  'rule' Resolve_type(product(PR) -> product(PR1)):
	 Resolve_product_type(PR -> PR1)

  'rule' Resolve_type(fin_set(T) -> fin_set(T1)):
	 Resolve_type(T -> T1)

  'rule' Resolve_type(infin_set(T) -> infin_set(T1)):
	 Resolve_type(T -> T1)

  'rule' Resolve_type(fin_list(T) -> fin_list(T1)):
	 Resolve_type(T -> T1)

  'rule' Resolve_type(infin_list(T) -> infin_list(T1)):
	 Resolve_type(T -> T1)

  'rule' Resolve_type(fin_map(D, R) -> fin_map(D1, R1)):
	 Resolve_type(D -> D1)
	 Resolve_type(R -> R1)

  'rule' Resolve_type(infin_map(D, R) -> infin_map(D1, R1)):
	 Resolve_type(D -> D1)
	 Resolve_type(R -> R1)

  'rule' Resolve_type(function(D,A,result(ACC,R)) -> T):
	 Check_access_defined(ACC, nil, nil, nil, nil -> RD,WR,IN,OUT)
	 Resolve_type(fun(D,A,result(R,RD,WR,IN,OUT)) -> T)

  'rule' Resolve_type(fun(D, A, result(R,RD,WR,IN,OUT)) -> fun(D1, A, result(R1,RD1,WR1,IN1,OUT1))):
	 Resolve_type(D -> D1)
	 Resolve_type(R -> R1)
	 Resolve_accs(RD -> RD1)
	 Resolve_accs(WR -> WR1)
	 Resolve_accs(IN -> IN1)
	 Resolve_accs(OUT -> OUT1)

  'rule' Resolve_type(subtype(TP, restriction(P, E)) -> subtype(TP1, restriction(P, E1))):
	 Resolve_value_typing(TP -> TP1)
	 Openenv()
	 Define_value_typing(TP1)
	 Resolve(E, bool -> E1)
	 [|
	   CPPWanted()
	   Localise_value_env()
	 |]
	 Closeenv()  

  'rule' Resolve_type(bracket(T) -> bracket(T1)):
	 Resolve_type(T -> T1)

  'rule' Resolve_type(defined(I, nil) -> Res) -- defined(I, Q)):
         (| -- may be affected by WITH
	   I'Qualifier -> list(Id, _)
	   I'Pos -> P
	   Qualify_by_with(P, Id -> Q)
	 ||
	   where(OPT_QUALIFICATION'nil -> Q)
	 |)
	 (|
           I'Type -> abbrev(TypeExprTemp)
           Remove_Brackets(TypeExprTemp -> TypeExpr)
	   where(TypeExpr -> array(T1,T2))
	   (|
             where(T1 -> named_type(_))
             Resolve_type(T1 -> T1Res)
           ||
	     where(T1 -> T1Res)
           |)
	   (|
             where(T2 -> named_type(_))
             Resolve_type(T2 -> T2Res)
           ||
	     where(T2 -> T2Res)
           |)
           --Resolve_type(TypeExpr -> TypeExpr2)
           I'Type <- abbrev(array(T1Res,T2Res))
           where(defined(I,Q) -> Res)
	 ||
	   where(defined(I,Q) -> Res)
	 |)

/*  'rule' Resolve_type(defined(I,Q) -> defined(I,Q)):
         I'Type -> abbrev(TypeExpr)
         Resolve_type(TypeExpr -> TypeExpr2)
         I'Type <- abbrev(TypeExpr2)*/

  'rule' Resolve_type(array(T1, T2) -> array(T3,T4)):
         Resolve_type(T1 -> T3)
         Resolve_type(T2 -> T4)

  
-- all other cases
  'rule' Resolve_type(T -> T):

'action' Resolve_product_type(PRODUCT_TYPE -> PRODUCT_TYPE)

  'rule' Resolve_product_type(list(T, PR) -> list(T1, PR1)):
	 Resolve_type(T -> T1)
	 Resolve_product_type(PR -> PR1)

  'rule' Resolve_product_type(nil -> nil):

'action' Resolve_accs(ACCESSES -> ACCESSES)

  'rule' Resolve_accs(list(A, AS) -> list(A1, AS1)):
	 Resolve_acc(A -> A1)
	 Resolve_accs(AS -> AS1)

  'rule' Resolve_accs(nil -> nil):

'action' Resolve_acc(ACCESS -> ACCESS)

  'rule' Resolve_acc(enumerated_access(P, AS) -> enumerated_access(P, AS1)):
	 Resolve_accs(AS -> AS1)

  'rule' Resolve_acc(completed_access(P, qualification(Obj)) -> completed_access(P, qualification(Obj1))):
	 Resolve_object(Obj -> Obj1)

  'rule' Resolve_acc(comprehended_access(P, A, set_limit(P1, TS, R))
		  -> comprehended_access(P, A1, set_limit(P1, TS1, R1))):
	 Resolve_value_typings(TS -> TS1)
	 Openenv()
	 Define_value_typings(TS1)
	 (|
	   where(R -> restriction(P2,V2))
	   Resolve(V2, bool -> V3)
	   where(restriction(P2,V3) -> R1)
	 ||
	   where(RESTRICTION'nil -> R1)
	 |)
	 Resolve_acc(A -> A1)
	 Closeenv()

  'rule' Resolve_acc(variable(P, I, nil) -> variable(P, I, nil)):

  'rule' Resolve_acc(variable(P, I, qualification(Obj)) -> variable(P, I, qualification(Obj1))):
--	 I'Qualifier -> Ids
	 Resolve_object(Obj -> Obj1)


  'rule' Resolve_acc(channel(P, I, nil) -> channel(P, I, nil)):

  'rule' Resolve_acc(channel(P, I, qualification(Obj)) -> channel(P, I, qualification(Obj1))):
--	 I'Qualifier -> Ids
	 Resolve_object(Obj -> Obj1)

-- other cases unchanged
  'rule' Resolve_acc(A -> A):


-----------------------------------------------------------------
-- Resolve object expressions
-----------------------------------------------------------------

'action' Resolve_object(OBJECT_EXPR -> OBJECT_EXPR)

  'rule' Resolve_object(Obj -> Obj2):
	 Check_object_defined(Obj -> Obj1, _)
-- debug
-- Print_object(Obj)
-- Putnl()
-- Print_object(Obj1)
-- Putnl()
-- print(Obj1)
	 Resolve_defined_object(Obj1 -> Obj2)

'action' Resolve_defined_object(OBJECT_EXPR -> OBJECT_EXPR)

  'rule' Resolve_defined_object(obj_appl(Obj, Parms) -> obj_appl(Obj1, Parms1)):
	 Defined_object_param_type(Obj -> T)
	 (|
	   where(Parms -> VALUE_EXPRS'list(Parm, nil))
	   Resolve(Parm, T -> Parm1)
	   where(VALUE_EXPRS'list(Parm1, nil) -> Parms1)
	 ||
	   Length_vs(Parms -> N)
	   Make_product_type(T, N -> product(TS))
	   Resolve_product(Parms, TS -> Parms1)
	 |)
	 Resolve_defined_object(Obj -> Obj1)

  'rule' Resolve_defined_object(obj_array(TPS, Obj) -> obj_array(TPS1, Obj1)):
	 Resolve_value_typings(TPS -> TPS1)
	 Openenv()
	 Define_value_typings(TPS1)
	 Resolve_defined_object(Obj -> Obj1)
	 Closeenv()

  'rule' Resolve_defined_object(obj_fit(Obj, RNS) -> obj_fit(Obj1, RNS)):
	 Resolve_defined_object(Obj -> Obj1)

  'rule' Resolve_defined_object(obj_occ(P, I) -> obj_occ(P, I)):

  'rule' Resolve_defined_object(qual_occ(P, Obj, I) -> qual_occ(P, Obj1, I)):
	 Resolve_defined_object(Obj -> Obj1)

'action' Defined_object_param_type(OBJECT_EXPR -> TYPE_EXPR)

  'rule' Defined_object_param_type(obj_array(TPS, Obj) -> T)
	 Resolve_value_typings(TPS -> TPS1)
	 Openenv()
	 Define_value_typings(TPS1)
	 Defined_type_of_typings(TPS1 -> TS)
	 (|
	   where(TS -> list(T, nil))
	 ||
	   where(TYPE_EXPR'product(TS) -> T)
	 |)
	 Closeenv()

  'rule' Defined_object_param_type(obj_fit(Obj, _) -> T):
	 Defined_object_param_type(Obj -> T)

  'rule' Defined_object_param_type(obj_occ(_, I) -> T)
	 I'Params -> param_type(T)

  'rule' Defined_object_param_type(qual_occ(_, _, I) -> T)
	 I'Params -> param_type(T)

--------------------------------------old--------------------------------
-- assumes Object_ids are at least as long as depth of object

-- only resolves one level down TODO (needed?) Yes - see imp.rsl

--'action' Resolve_object(OBJECT_EXPR, Object_ids -> OBJECT_EXPR)

--  'rule' Resolve_object(obj_name(name(P, _)), Ids -> obj_occ(P, I)):
--	 Split_object_ids(Ids -> _, I)

--  'rule' Resolve_object(obj_name(qual_name(P, Obj, _)),  Ids -> qual_occ(P, Obj1, I)):
--	 Split_object_ids(Ids -> Ids1, I)
--	 Resolve_object(Obj, Ids1 -> Obj1)

--  'rule' Resolve_object(obj_appl(Obj, Parms), Ids -> obj_appl(Obj1, Parms1)):
--	 Split_object_ids(Ids -> _, I)
--	 I'Params -> param_type(T)
--	 (|
--	   where(Parms -> VALUE_EXPRS'list(Parm, nil))
--	   Resolve(Parm, T -> Parm1)
--	   where(VALUE_EXPRS'list(Parm1, nil) -> Parms1)
--	 ||
--	   Length_vs(Parms -> N)
--	   Make_product_type(T, N -> product(TS))
--	   Resolve_product(Parms, TS -> Parms1)
--	 |)
--	 Resolve_object(Obj, Ids -> Obj1)

--  'rule' Resolve_object(obj_array(TPS, Obj), Ids -> obj_array(TPS1, Obj1)):
--	 Resolve_value_typings(TPS -> TPS1)
--	 Openenv()
--	 Define_value_typings(TPS1)
--	 Resolve_object(Obj, Ids -> Obj1)
--	 Closeenv()

--  'rule' Resolve_object(obj_fit(Obj, RNS), Ids -> obj_fit(Obj1, RNS)):
--	 Resolve_object(Obj, Ids -> Obj1)

--  'rule' Resolve_object(obj_occ(P, I), _ -> obj_occ(P, I)):

--  'rule' Resolve_object(qual_occ(P, Q, I), _ -> qual_occ(P, Q, I)):


--'action' Split_object_ids(Object_ids -> Object_ids, Object_id)

--  'rule' Split_object_ids(list(I, nil) -> nil, I):

--  'rule' Split_object_ids(list(I, Ids) -> list(I, Ids1), I1):
--	 Split_object_ids(Ids -> Ids1, I1)

--'action' Append_object_id(Object_ids, Object_id -> Object_ids)

--  'rule' Append_object_id(list(I, Ids), I1 -> list(I, Ids1)):
--	 Append_object_id(Ids, I1 -> Ids1)

--  'rule' Append_object_id(nil, I -> list(I, nil)):


-----------------------------------------------------------------
-- Resolve value expressions
-----------------------------------------------------------------

-- WARNING: Resolve assumes that type checking has generated no errors
-- and its behaviour in other circumstances is not defined
'action' Resolve(VALUE_EXPR, TYPE_EXPR -> VALUE_EXPR)

  'rule' Resolve(literal_expr(P, L), T -> literal_expr(P, L)):

  'rule' Resolve(named_val(P, N), T -> V):
-- debug
-- Putmsg("Looking for ")
-- Print_name(N)
-- Putmsg(" of type ")
-- Print_type(T)
-- Putnl()
	 (|
	   Is_LTL_Wanted()
	   FDRWanted()
	   -- we can accept channel names as (boolean) expressions
	   Lookup_channel_name(N -> channel_id(IV))
	   (|
	     where(N -> qual_name(_,Obj,_))
--	     IV'Qualifier -> Ids
-- debug
--ne(Ids, nil)
	     Resolve_object(Obj -> Obj1)
	     where(qualification(Obj1) -> Q)
	   ||
	     (| -- may be affected by WITH
	       IV'Qualifier -> list(Iv, _)
	       Qualify_by_with(P, Iv -> Q)
	     ||
	       where(OPT_QUALIFICATION'nil -> Q)
	     |)
	   |)
	   where(chan_occ(P, IV, Q) -> V)
	 ||
	   Lookup_variable_name(N -> variable_id(IV))
	   (|
	     where(N -> qual_name(_,Obj,_))
--	     IV'Qualifier -> Ids
-- debug
--ne(Ids, nil)
	     Resolve_object(Obj -> Obj1)
	     where(qualification(Obj1) -> Q)
	   ||
	     (| -- may be affected by WITH
	       IV'Qualifier -> list(Iv, _)
	       Qualify_by_with(P, Iv -> Q)
	     ||
	       where(OPT_QUALIFICATION'nil -> Q)
	     |)
	   |)
	   where(var_occ(P, IV, Q) -> V)
	 ||
	   Lookup_value_name(P, N -> Ids)
	   (|
	     where(Ids -> list(I, nil))
	   ||
	     Select_id_by_type(Ids, T -> value_id(I))
	   |)
	   (|
	     where(N -> qual_name(_,Obj,_))
--	     I'Qualifier -> Ids1
	     Resolve_object(Obj -> Obj1)
	     where(qualification(Obj1) -> Q)
-- debug
-- Print_expr(named_val(P, N))
-- Putnl()
-- print(N)
-- Putmsg(" resolved to ")
-- Print_expr(val_occ(P, I, Q))
-- Putnl()
-- print(val_occ(P, I, Q))
-- Putmsg(" of type ")
-- I'Type -> T1
-- Print_type(T1)
-- Putnl()
	   ||
	     (| -- may be affected by WITH
	       I'Qualifier -> list(Id, _)
	       Qualify_by_with(P, Id -> Q)
	     ||
	       where(OPT_QUALIFICATION'nil -> Q)
	     |)
-- debug
-- Print_expr(named_val(P, N))
-- Putnl()
-- print(N)
-- Putmsg(" resolved to ")
-- Print_expr(val_occ(P, I, Q))
-- Putnl()
-- print(val_occ(P, I, Q))
-- Putmsg(" of type ")
-- I'Type -> T1
-- Print_type(T1)
-- Putnl()
	   |)
	   where(val_occ(P, I, Q) -> V)
	 |)

  'rule' Resolve(pre_name(P, N), T -> V):
	 Lookup_variable_name(N -> variable_id(I))
	 (|
	   where(N -> qual_name(_,Obj,_))
--	   I'Qualifier -> Ids
	   Resolve_object(Obj -> Obj1)
	   where(qualification(Obj1) -> Q)
	 ||
	   (| -- may be affected by WITH
	     I'Qualifier -> list(Id, _)
	     Qualify_by_with(P, Id -> Q)
	   ||
	     where(OPT_QUALIFICATION'nil -> Q)
	   |)
	 |)
	 where(pre_occ(P, I, Q) -> V)

  'rule' Resolve(chaos(P), T -> chaos(P)):  

  'rule' Resolve(skip(P), T -> skip(P)):  

  'rule' Resolve(stop(P), T -> stop(P)):  

  'rule' Resolve(swap(P), T -> swap(P)):

  'rule' Resolve(ranged_set(P,L,R), T -> ranged_set(P,L1,R1)):
	 Resolve(L, int -> L1)
	 Resolve(R, int -> R1)

  'rule' Resolve(product(P, nil), T -> product(P, nil)):

  'rule' Resolve(product(P, VS), T -> product(P, VS1)):
	 Length_vs(VS -> N)
	 Make_product_type(T, N -> product(TS))
	 Resolve_product(VS, TS -> VS1)

  'rule' Resolve(enum_set(P, nil), T -> enum_set(P, nil)):
	 CcWanted()

-- useful for translation to know type
  'rule' Resolve(enum_set(P, nil), T -> V):
-- debug
-- Putmsg("Type of empty set is ")
-- Print_type(T)
-- Putnl
	 Contains_any_or_poly(T, nil -> Found)
	 (|
	   eq(Found,found)
	   where(enum_set(P, nil) -> V)
	   Puterror(P)
	   Putmsg("Empty set needs disambiguation")
	   Putnl()
	 ||
	   Make_set_type(T -> T1)
	   (| where(T1 -> fin_set(T2)) || where(T1 -> infin_set(T2)) |)
	   where(VALUE_EXPR'disamb(P, enum_set(P, nil), fin_set(T2)) -> V)
	 |)

  'rule' Resolve(enum_set(P, VS), T -> enum_set(P, VS1)):
	 Make_set_type(T -> T1)
	 (| where(T1 -> fin_set(T2)) || where(T1 -> infin_set(T2)) |)
	 Resolve_list(VS, T2 -> VS1)

  'rule' Resolve(comp_set(P, V, set_limit(P1, TS, R)), T -> comp_set(P, V1, set_limit(P1, TS1, R1))):
	 Resolve_value_typings(TS -> TS1)
	 Openenv()
	 Define_value_typings(TS1)
	 (|
	   where(R -> restriction(P2,V2))
	   Resolve(V2, bool -> V3)
	   where(restriction(P2,V3) -> R1)
	 ||
	   where(RESTRICTION'nil -> R1)
	 |)
	 Make_set_element_type(P, T -> T1)
	 Resolve(V, T1 -> V1)
	 [|
	   CPPWanted()
	   Localise_value_env()
	 |]
	 Closeenv()

  'rule' Resolve(ranged_list(P,L,R), T -> ranged_list(P,L1,R1)):
	 Resolve(L, int -> L1)
	 Resolve(R, int -> R1)

  'rule' Resolve(enum_list(P, nil), T -> enum_list(P, nil)):
	 CcWanted()

-- useful for translation to know type
 'rule' Resolve(enum_list(P, nil), T -> V):
	 Contains_any_or_poly(T, nil -> Found)
	 (|
	   eq(Found,found)
	   where(VALUE_EXPR'enum_list(P, nil) -> V)
	   Puterror(P)
	   Putmsg("Empty list needs disambiguation")
	   Putnl()
	 ||
	   Make_list_type(T -> T1)
	   (| where(T1 -> fin_list(T2)) || where(T1 -> infin_list(T2)) |)
	   where(VALUE_EXPR'disamb(P, enum_list(P, nil), fin_list(T2)) -> V)
	 |)

  'rule' Resolve(enum_list(P, VS), T -> enum_list(P, VS1)):
	 Make_list_type(T -> T1)
	 (| where(T1 -> fin_list(T2)) || where(T1 -> infin_list(T2)) |)
	 Resolve_list(VS, T2 -> VS1)

  'rule' Resolve(comp_list(P, V, list_limit(P1, B, V1, R)), T -> comp_list(P, V0, list_limit(P1, B, V11, R1))):
	 Make_results(V1 -> list(result(T1,_,_,_,_),_))
	 Resolve(V1, T1 -> V11)
	 Make_list_element_type(P1, T1 -> T2)
	 Openenv()
	 Define_value_typing(single(P1, B, T2))
	 (|
	   where(R -> restriction(P2,V2))
	   Resolve(V2, bool -> V3)
	   where(restriction(P2,V3) -> R1)
	 ||
	   where(RESTRICTION'nil -> R1)
	 |)
	 Make_list_element_type(P, T -> T3)
	 Resolve(V, T3 -> V0)
	 [|
	   CPPWanted()
	   Localise_value_env()
	 |]
	 Closeenv()

  'rule' Resolve(enum_map(P, nil), T -> enum_map(P, nil)):
	 CcWanted()

-- useful for translation to know type
  'rule' Resolve(enum_map(P, nil), T -> V):
	 Contains_any_or_poly(T, nil -> Found)
	 (|
	   eq(Found,found)
	   where(VALUE_EXPR'enum_map(P, nil) -> V)
	   Puterror(P)
	   Putmsg("Empty map needs disambiguation")
	   Putnl()
	 ||
	   Make_map_element_types(P, T -> D, R)
	   where(VALUE_EXPR'disamb(P, enum_map(P, nil), fin_map(D,R)) -> V)
	 |)

  'rule' Resolve(enum_map(P, PAIRS), T -> enum_map(P, PAIRS1)):
	 Make_map_element_types(P, T -> D, R)
	 Resolve_pairs(PAIRS, D, R -> PAIRS1)

  'rule' Resolve(comp_map(P, PAIR, set_limit(P1, TS, R)), T -> comp_map(P, PAIR0, set_limit(P1, TS1, R0))):
	 Resolve_value_typings(TS -> TS1)
	 Openenv()
	 Define_value_typings(TS1)
	 (|
	   where(R -> restriction(P2,V2))
	   Resolve(V2, bool -> V3)
	   where(restriction(P2,V3) -> R0)
	 ||
	   where(RESTRICTION'nil -> R0)
	 |)
	 Make_map_element_types(P, T -> DT, RT)
	 Resolve_pair(PAIR, DT, RT -> PAIR0)
	 [|
	   CPPWanted()
	   Localise_value_env()
	 |]
	 Closeenv()

  'rule' Resolve(function(P, LP, V), T -> function(P, LP1, V0)):
	 (|
	   where(LP -> l_typing(P1,TPS))
	   Resolve_value_typings(TPS -> TPS1)
	   where(l_typing(P1,TPS1) -> LP1)
	 ||
	   where(LP -> s_typing(P1,TP))
	   Resolve_value_typing(TP -> TP1)
	   where(s_typing(P1,TP1) -> LP1)
	 |)
	 Resolve_function(LP1, V, T -> V0)

  'rule' Resolve(application(P, F, ARGS), T -> application(P, F0, ARGS0)):
	 Resolve_application(F, ARGS, T -> F0, ARGS0)

  'rule' Resolve(quantified(P,Q,TPS,R), T -> quantified(P,Q,TPS1,R0)):
	 Resolve_value_typings(TPS -> TPS1)
	 Openenv()
	 Define_value_typings(TPS1)
	 (|
	   where(R -> restriction(P2,V2))
	   Resolve(V2, bool -> V3)
	   where(restriction(P2,V3) -> R0)
	 ||
	   where(RESTRICTION'nil -> R0)
	 |)
	 [|
	   CPPWanted()
	   Localise_value_env()
	 |]
	 Closeenv()

  'rule' Resolve(equivalence(P,V1,V2,PRE), T -> equivalence(P,V3,V4,PRE1)):
	 (|
	   where(PRE -> pre_cond(P2,V5))
	   Resolve(V5, bool -> V6)
	   where(pre_cond(P2,V6) -> PRE1)
	 ||
	   where(PRE_CONDITION'nil -> PRE1)
	 |)
	 Make_results(V1 -> RS1)
	 (|
	   where(RS1 -> list(result(T1,_,_,_,_), nil))
	 ||
	   Make_results(V2 -> RS2)
	   (|
	     where(RS2 -> list(result(T1,_,_,_,_), nil))
	   ||
	     Make_products(RS2 -> PRS)
	     Mult(RS1, PRS -> ARS)
	     Intersection_result(result(product(list(poly(52),list(poly(52),nil))),nil,nil,nil,nil), ARS -> list(result(T1,_,_,_,_), _))
	   |)
	 |)
	 Resolve(V1, T1 -> V3)
	 Resolve(V2, T1 -> V4)

  'rule' Resolve(post(P, V, post_cond(P1, R, C), PRE), T -> post(P, V1, post_cond(P1, R, C1), PRE1)):
	 (|
	   where(PRE -> pre_cond(P2,V2))
	   Resolve(V2, bool -> V3)
	   where(pre_cond(P2,V3) -> PRE1)
	 ||
	   where(PRE_CONDITION'nil -> PRE1)
	 |)
	 Make_results(V -> list(result(T1,_,_,_,_),_))
	 Resolve(V, T1 -> V1)
	 (|
	   where(R -> result(P3, B))
	   Openenv()
	   Define_value_binding(B, T1)
	   Resolve(C, bool -> C1)
	   Closeenv()
	 ||
	   Resolve(C, bool -> C1)
	 |)


  'rule' Resolve(disamb(P,V,T1), T -> disamb(P,V1,T3)):
	 Resolve(V, T -> V1)
	 Check_type_defined(T1 -> T2)
	 Resolve_type(T1 -> T3)

  'rule' Resolve(bracket(P,V), T -> bracket(P,V1)):
	 Resolve(V, T -> V1)

  'rule' Resolve(ax_infix(P,L,C,R,P1), T -> ax_infix(P,L1,C,R1,P1)):
	 Resolve(L, bool -> L1)
	 Resolve(R, bool -> R1)

  'rule' Resolve(val_infix(P,L,Op,R), T -> infix_occ(P,L1,I,Q,R1)):
-- debug
--Putmsg("Resolving ")
--Print_expr(val_infix(P,L,Op,R))
--Putmsg(" of type ")
--Print_type(T)
--Putnl()
	 Lookup_value_name(P, name(P,op_op(Op)) -> Ids)
	 Make_pure_results(Ids -> FRS)
	 Prune_by_result_type(FRS, T, list(fun_arg(P,list(L,list(R,nil))),nil) -> FRS1)
	 where(FRS1 -> list(result(fun(DT1,_,_),_,_,_,_), REST)) 
	 Contains_any_or_poly(DT1, nil -> Found)
	 (|
	   eq(REST, nil)
	   eq(Found, nil)
	   where(DT1 -> DT)
	 ||
	   Make_results(L -> LRS)
	   Make_results(R -> RRS)
	   Make_products(RRS -> PRRS)
	   Mult(LRS, PRRS -> ARS)
	   Poly_disambiguate_args(ARS -> ARS1)
-- debug
-- Print_results(ARS1)
-- Putnl
	   Prune_by_argument(FRS1, ARS1 -> list(result(fun(DT2,_,_),_,_,_,_), _))
	   (|
	     eq(Found, nil)
	     where(DT2 -> DT)
	   ||
	     Prune_by_argument_resolution(DT2, ARS1 -> DT3)
	     where(DT3 -> DT)
	   |)
	 |)
-- debug
-- Print_type(DT)
-- Putnl
	 Make_product_type(DT, 2 -> product(list(LT, list(RT, nil))))
	 Resolve(L, LT -> L1)
	 Resolve(R, RT -> R1)
	 (|
	   where(Ids -> list(I, nil))
	 ||
	   -- avoid confusion through same polymorphic numbers
	   Poly_disambiguate_type(T, DT -> T1)
	   Select_id_by_type(Ids, fun(DT, partial, result(T1,nil,nil,nil,nil)) -> value_id(I))
	 |)
	 (| -- may be affected by WITH
	   I'Qualifier -> list(OId, _)
	   Qualify_by_with(P, OId -> Q)
	 ||
	   where(OPT_QUALIFICATION'nil -> Q)
	 |)

  'rule' Resolve(stmt_infix(P, L, Comb, R), T -> stmt_infix(P, L1, Comb, R1)):
	 (|
	   (| eq(Comb, ext_choice) || eq(Comb, int_choice) |)
	   Resolve(L, T -> L1)
	 ||
	   -- parallel, interlock or sequence
	   Resolve(L, unit -> L1)
	 |)
	 Resolve(R, T -> R1)

  'rule' Resolve(always(P, V), T -> V1):
	 Resolve(V, bool -> V1)

  'rule' Resolve(ax_prefix(P, C, V), T -> ax_prefix(P, C, V1)):
	 Resolve(V, bool -> V1)

  'rule' Resolve(val_prefix(P,Op,V), T -> prefix_occ(P,I,Q,V1)):
	 Lookup_value_name(P, name(P,op_op(Op)) -> Ids)
	 Make_pure_results(Ids -> FRS)
	 Prune_by_result_type(FRS, T, list(fun_arg(P,list(V,nil)),nil) -> FRS1)
	 where(FRS1 -> list(result(fun(T1,_,_),_,_,_,_), REST)) 
	 Contains_any_or_poly(T1, nil -> Found)
	 (|
	   eq(REST, nil)
	   eq(Found, nil)
	   where(T1 -> T11)
	 ||
	   Make_results(V -> ARS)
	   Prune_by_argument(FRS1, ARS -> list(result(fun(T2,_,_),_,_,_,_), _))
	   (|
	     eq(Found, nil)
	     where(T2 -> T11)
	   ||
	     Prune_by_argument_resolution(T2, ARS -> T11)
	   |)
	 |)
	 Resolve(V, T11 -> V1)
	 (|
	   where(Ids -> list(I, nil))
	 ||
	   -- avoid confusion through same polymorphic numbers
	   Poly_disambiguate_type(T, T11 -> TR)
	   Select_id_by_type(Ids, fun(T11, partial, result(TR,nil,nil,nil,nil)) -> value_id(I))
	 |)
	 (| -- may be affected by WITH
	   I'Qualifier -> list(OId, _)
	   Qualify_by_with(P, OId -> Q)
	 ||
	   where(OPT_QUALIFICATION'nil -> Q)
	 |)

  'rule' Resolve(comprehended(P, Comb, V, set_limit(P1, TS, R)), T -> comprehended(P, Comb, V0, set_limit(P1, TS1, R0))):
	 Resolve_value_typings(TS -> TS1)
	 Openenv()
	 Define_value_typings(TS1)
	 (|
	   where(R -> restriction(P2,V2))
	   Resolve(V2, bool -> V3)
	   where(restriction(P2,V3) -> R0)
	 ||
	   where(RESTRICTION'nil -> R0)
	 |)
	 Resolve(V, T -> V0)
	 [|
	   CPPWanted()
	   Localise_value_env()
	 |]
	 Closeenv()

  'rule' Resolve(initialise(P, nil), T -> initialise(P, nil)):

  'rule' Resolve(initialise(P, qualification(Obj)), T -> initialise(P, qualification(Obj1))):
--	 Get_object_id(Obj -> object_id(I), _)
--	 I'Qualifier -> Ids
--	 Append_object_id(Ids, I -> Ids1)
	 Resolve_object(Obj -> Obj1)

  'rule' Resolve(assignment(P, N, V), T -> ass_occ(P, I, Q, V1)):
	 Lookup_variable_name(N -> variable_id(I))
	 (|
	   where(N -> qual_name(_,Obj,_))
--	   I'Qualifier -> Ids
	   Resolve_object(Obj -> Obj1)
	   where(qualification(Obj1) -> Q)
	 ||
	   (| -- may be affected by WITH
	     I'Qualifier -> list(Id, _)
	     Qualify_by_with(P, Id -> Q)
	   ||
	     where(OPT_QUALIFICATION'nil -> Q)
	   |)
	 |)
	 I'Type -> T1
	 Resolve(V, T1 -> V1)

  'rule' Resolve(array_assignment(P, N, Index, V), T -> array_ass_occ(P, I, Q, Index1, V1)):
	 Lookup_variable_name(N -> variable_id(I))
	 (|
	   where(N -> qual_name(_,Obj,_))
--	   I'Qualifier -> Ids
	   Resolve_object(Obj -> Obj1)
	   where(qualification(Obj1) -> Q)
	 ||
	   (| -- may be affected by WITH
	     I'Qualifier -> list(Id, _)
	     Qualify_by_with(P, Id -> Q)
	   ||
	     where(OPT_QUALIFICATION'nil -> Q)
	   |)
	 |)
	 I'Type -> Temp
         --Remove_Brackets(Temp -> array(T1,T2))
         Resolve_array_indexes(Index, Temp -> Index1, T2)
	 Resolve(V, T2 -> V1)
         Resolve_type(Temp -> TempResolved)
         I'Type <- TempResolved


  'rule' Resolve(input(P, N), T -> input_occ(P, I, Q)):
	 Lookup_channel_name(N -> channel_id(I))
	 (|
	   where(N -> qual_name(_,Obj,_))
--	   I'Qualifier -> Ids
	   Resolve_object(Obj -> Obj1)
	   where(qualification(Obj1) -> Q)
	 ||
	   (| -- may be affected by WITH
	     I'Qualifier -> list(Id, _)
	     Qualify_by_with(P, Id -> Q)
	   ||
	     where(OPT_QUALIFICATION'nil -> Q)
	   |)
	 |)

  'rule' Resolve(output(P, N, V), T -> output_occ(P, I, Q, V1)):
	 Lookup_channel_name(N -> channel_id(I))
	 (|
	   where(N -> qual_name(_,Obj,_))
--	   I'Qualifier -> Ids
	   Resolve_object(Obj -> Obj1)
	   where(qualification(Obj1) -> Q)
	 ||
	   (| -- may be affected by WITH
	     I'Qualifier -> list(Id, _)
	     Qualify_by_with(P, Id -> Q)
	   ||
	     where(OPT_QUALIFICATION'nil -> Q)
	   |)
	 |)
	 I'Type -> T1
	 Resolve(V, T1 -> V1)


  'rule' Resolve(local_expr(P, DS, V), T -> env_local(P, DS, CE, V1)):
	 -- needs to keep environment; otherwise lost on exit 
	 Get_current_with(-> WITH)
	 Current -> C
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 Make_basic_env(basic(DS))
	 Complete_type_env(basic(DS))
	 Make_value_env(basic(DS))
	 Check_value_env(basic(DS))
	 Resolve_class(basic(DS))
	 Resolve(V, T -> V1)
	 [|
	   CPPWanted()
	   Localise_env()
	 |]
	 Current -> current_env(CE, C1)
	 Current <- C1
	 Extend_paths <- Paths

  'rule' Resolve(class_scope_expr(P, CL, V), T -> class_scope_expr(P, CL, V)): 
	 CcWanted()
	 -- resolving done as part of CC generation

  'rule' Resolve(class_scope_expr(P, CL:instantiation(name(_,id_op(Id)), nil), V), T -> env_class_scope(P, CL, CE, V1)):
	 -- parameterless scheme instantiation:
	 -- try to reuse environment.
	 -- Important when many class scope expressions with same scheme
	 Establish_resolved_scheme_env(Id)
	 Get_current_with(-> WITH)
	 Current -> current_env(CE, C)
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), current_env(CE, C))
	 Extend_paths -> list(Path,Paths)
	 Extend_paths <- list(nil,list(Path,Paths))
	 Resolve(V, bool -> V1)
	 Current <- C
	 Extend_paths <- Paths

  'rule' Resolve(class_scope_expr(P, CL, V), T -> env_class_scope(P, CL, CE, V1)): 
	 -- keep environment for CL for use in translation
	 Get_current_with(-> WITH)
	 Current -> C
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 Make_basic_env(CL)
	 Complete_type_env(CL)
	 Make_value_env(CL)
	 Check_value_env(CL)
	 Resolve_class(CL)
	 Current -> current_env(CE, C1)
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), current_env(CE, C1))
	 Extend_paths -> Paths1
	 Extend_paths <- list(nil,Paths1)
	 Resolve(V, bool -> V1)
	 Current <- C
	 Extend_paths <- Paths

  'rule' Resolve(implementation_relation(P,
				instantiation(name(_,id_op(Id)), OS),
				instantiation(name(_,id_op(Id1)), OS1)),
				T -> E):
	 PVSWanted()
	 eq(Id, Id1)
	 Expand_scheme_args_implementation(P, OS, OS1 -> E0)
	 Simplify(E0 -> E)

  'rule' Resolve(implementation_relation(P, CL1, CL2), T ->
					    env_class_scope(P, CL1, E11, VE)):
	 PVSWanted()
	 Current -> C
	 Extend_paths -> Paths
	 Get_current_with(-> WITH)
	 (|
	   where(CL1 -> instantiation(name(_,id_op(Id1)), nil))
	   Establish_resolved_scheme_env(Id1)
	 ||  
	   Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	   Extend_paths <- list(nil,Paths)
	   Make_basic_env(CL1)
	   Complete_type_env(CL1)
	   Make_value_env(CL1)
	   Check_value_env(CL1)
	   Resolve_class(CL1)
	 |)
	 Get_current_env(-> E1)
	 Get_env_adapts(E1 -> AD)
	 Remove_hides(AD -> AD1)
	 Set_env_adapts(E1, AD1 -> E11)
	 (|
	   Current <- C
	   Extend_paths <- Paths
	   where(CL2 -> instantiation(name(_,id_op(Id2)), nil))
	   Establish_resolved_scheme_env(Id2)
	 ||
	   Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	   Extend_paths <- list(nil,Paths)
	   Make_basic_env(CL2)
	   Complete_type_env(CL2)
	   Make_value_env(CL2)
	   Check_value_env(CL2)
	   Resolve_class(CL2)
	 |)
	 Get_current_env(-> E2)
	 Current <- C
	 Extend_paths <- Paths
	 Make_type_fits(E2, E11, nil -> TYPF)
	 Make_imp_fit(E2, E11, nil, TYPF, nil -> IF)
	 Get_env_axioms(E2 -> OLDAX)
	 Get_env_axioms(E11 -> NEWAX)
	 CCImplementation(P, IF, IF, OLDAX, NEWAX -> VE0)
	 Simplify(VE0 -> VE)

  'rule' Resolve(implementation_relation(P, CL1, CL2), T -> implementation_relation(P, CL1, CL2)):
	 -- resolving done as part of CC generation

  'rule' Resolve(implementation_expr(P, Obj1, Obj2), T -> VE)
	 PVSWanted()
	 Resolve_object(Obj1 -> Obj11)
	 Resolve_object(Obj2 -> Obj21)
	 (|
	   Same_object(Obj11, Obj21, imp_fit(nil,nil,nil,nil,nil))
	   where(literal_expr(P, bool_true) -> VE)
	 ||
	   Env_of_defined_object(Obj11 -> E1)
	   Get_env_adapts(E1 -> AD)
	   Remove_hides(AD -> AD1)
	   Set_env_adapts(E1, AD1 -> E11)
	   Env_of_defined_object(Obj21 -> E2)
	   Make_type_fits(E2, E11, nil -> TYPF)
	   Make_imp_fit(E2, E11, nil, TYPF, nil -> IF)
	   Get_env_axioms(E2 -> OLDAX)
	   Get_env_axioms(E11 -> NEWAX)
	   CCImplementation(P, IF, IF, OLDAX, NEWAX -> VE0)
	   Simplify(VE0 -> VE)
	 |)

  'rule' Resolve(implementation_expr(P, Obj1, Obj2), T -> implementation_expr(P, Obj1, Obj2)):
	 -- nothing to do; objects already resolved

  'rule' Resolve(let_expr(P,DEFS,V), T -> let_expr(P,DEFS1,V1)):
	 Resolve_let(DEFS, V, T -> DEFS1, V1)	 

  'rule' Resolve(if_expr(P, V, THEN, RT, ELSIF, ELSE), T -> if_expr(P, V1, THEN1, RT, ELSIF1, ELSE1)):
	 Resolve(V, bool -> V1)
	 Resolve(THEN, T -> THEN1)
	 Resolve_elsif(ELSIF, T -> ELSIF1)
	 (|
	   where(ELSE -> else(P1, E))
	   Resolve(E, T -> E1)
	   where(else(P1, E1) -> ELSE1)
	 ||
	   where(ELSE_BRANCH'nil -> ELSE1)
	 |)

  'rule' Resolve(case_expr(P, V, PE, BRANCHES), T -> case_expr(P, V2, PE, BRANCHES1)):
	 Make_results(V -> list(result(T1,_,_,_,_),_))
	 Resolve(V, T1 -> V1)
	 (|
	   (| CcWanted() || where(V1 -> disamb(_,_,_)) |)
	   where(V1 -> V2)
	 ||  -- for translators, include type
	   where(VALUE_EXPR'disamb(P, V1, T1) -> V2)
	 |)
	 Resolve_case_branches(BRANCHES, T1, T -> BRANCHES1)

  'rule' Resolve(while_expr(P, C, V), T -> while_expr(P, C1, V1)):
	 Resolve(C, bool -> C1)
	 Resolve(V, unit -> V1)

  'rule' Resolve(until_expr(P, V, C), T -> until_expr(P, V1, C1)):
	 Resolve(V, unit -> V1)
	 Resolve(C, bool -> C1)

  'rule' Resolve(array_access(P,N,In), T -> array_access(P, N1, In1))
         Resolve(N, array(any,T) -> N1)
         Resolve(In, any -> In1)

  'rule' Resolve(array_expr(P, S, V), T -> array_expr(P, S1, V1)):
         Resolve_value_typing(S -> S1)
         Openenv()
         Define_value_typing(S1)
         Make_array_element_types(P, T -> IT, VT)
         Resolve(V, VT -> V1)
	 [|
	   CPPWanted()
	   Localise_value_env()
	 |]
         Closeenv()

  'rule' Resolve(for_expr(P, list_limit(P1, B, LV, R), V), T -> for_expr(P, list_limit(P1, B, LV1, R1), V1)):
	 Make_results(LV -> list(result(LT,_,_,_,_),_))
	 Resolve(LV, LT -> LV2)
	 (|
	   (| CcWanted() || where(LV2 -> disamb(_,_,_)) |)
	   where(LV2 -> LV1)
	 ||
	   -- add type information for translators
	   where(VALUE_EXPR'disamb(P1, LV2, LT) -> LV1)
	 |)
	 Make_list_element_type(P1, LT -> T1)
	 Openenv()
	 Define_value_typing(single(P1, B, T1))
	 (|
	   where(R -> restriction(P2,V2))
	    Resolve(V2, bool -> V3)
	   where(restriction(P2,V3) -> R1)
	 ||
	   where(RESTRICTION'nil -> R1)
	 |)
	 Resolve(V, unit -> V1)
	 [|
	   CPPWanted()
	   Localise_value_env()
	 |]
	 Closeenv()

-- catch all errors
  'rule' Resolve(V, T -> V):
-- debug
	Putmsg("Internal error: cannot resolve ")
	Print_expr(V)
	Putmsg(" of type ")
	Print_type(T)
	Putnl()
print(V)
print(T)
--print(V)
--[|
--  where(V -> val_occ(P, _, _))
--  PrintPos(P)
--  Putnl()
--|]
--print(T)


'action' Resolve_array_indexes(VALUE_EXPRS, TYPE_EXPR -> VALUE_EXPRS, TYPE_EXPR)
  'rule' Resolve_array_indexes(list(H,nil), Type -> list(HRes,nil), TV)
         Remove_Brackets(Type -> Type2)
         where(Type2 -> array(TI, TV))
         Resolve(H, TI -> HRes)
         
  'rule' Resolve_array_indexes(list(H,T), Type -> list(HRes, TRes), TypeRes)
         Remove_Brackets(Type -> Type2)
         where(Type2 -> array(TI, TV))
         Resolve(H, TI -> HRes)
         Resolve_array_indexes(T, TV -> TRes, TypeRes)

'action' Resolve_product(VALUE_EXPRS, PRODUCT_TYPE -> VALUE_EXPRS)

  'rule' Resolve_product(list(V, VS), list(T, TS) -> list(V1, VS1)):
	 Resolve(V, T -> V1)
	 Resolve_product(VS, TS -> VS1)

  'rule' Resolve_product(nil, nil -> nil): 

'action' Resolve_list(VALUE_EXPRS, TYPE_EXPR -> VALUE_EXPRS)

  'rule' Resolve_list(list(V, VS), T -> list(V1, VS1)):
	 Resolve(V, T -> V1)
	 Resolve_list(VS, T -> VS1)

  'rule' Resolve_list(nil, T -> nil):

'action' Resolve_pairs(VALUE_EXPR_PAIRS, TYPE_EXPR, TYPE_EXPR -> VALUE_EXPR_PAIRS)

  'rule' Resolve_pairs(list(H,T), D, R -> list(H1,T1)):
	 Resolve_pair(H, D, R -> H1)
	 Resolve_pairs(T, D, R -> T1)

  'rule' Resolve_pairs(nil, D, R -> nil):

'action' Resolve_pair(VALUE_EXPR_PAIR, TYPE_EXPR, TYPE_EXPR -> VALUE_EXPR_PAIR)

  'rule' Resolve_pair(pair(L, R), D, RT -> pair(L1, R1)):
	 Resolve(L, D -> L1) 
	 Resolve(R, RT -> R1) 

'action' Resolve_function(LAMBDA_PARAMETER, VALUE_EXPR, TYPE_EXPR -> VALUE_EXPR)

  'rule' Resolve_function(l_typing(P, TPS), V, T -> V1):
	 Openenv()
	 Define_value_typings(TPS)
	 Make_function_type(T -> fun(_, _, result(T1,_,_,_,_)))
	 Resolve(V, T1 -> V1)
	 Closeenv()

  'rule' Resolve_function(s_typing(P, TP), V, T -> V1):
	 Openenv()
	 Define_value_typing(TP)
	 Make_function_type(T -> fun(_, _, result(T1,_,_,_,_)))
	 Resolve(V, T1 -> V1)
	 Closeenv()

'action' Resolve_application(VALUE_EXPR, ACTUAL_FUNCTION_PARAMETERS, TYPE_EXPR -> VALUE_EXPR, ACTUAL_FUNCTION_PARAMETERS)

  'rule' Resolve_application(V, ARGS, T -> V0, ARGS0):
	 Make_results(V -> RS)
	 (|
	   where(RS -> list(result(FT,_,_,_,_), nil))
	   where(RS -> RS1)
	 ||
	   Prune_by_result_type(RS, T, ARGS -> RS1)
	 |)
	 (|
	   where(RS1 -> list(result(FT1,_,_,_,_), nil))
	 ||
	   Prune_by_arguments(RS1, ARGS -> list(result(FT1,_,_,_,_), _))
	 |)
	 Resolve(V, FT1 -> V0)
	 Resolve_args(ARGS, FT1 -> ARGS0)

'action' Resolve_args(ACTUAL_FUNCTION_PARAMETERS, TYPE_EXPR -> ACTUAL_FUNCTION_PARAMETERS)

  'rule' Resolve_args(list(fun_arg(P, VS), ARGS), T -> list(fun_arg(P, VS1), ARGS1)):
	 Split_fun_type(T -> T1, T2)
-- debug
-- [|
--   ne(ARGS,nil)
--   Print_type(T)
--   Putmsg(" split into ")
--   Print_type(T1)
--   Putmsg(" and ")
--   Print_type(T2)
--   Putnl()
--   print(ARGS)
-- |]
	 Resolve_args(ARGS, T2 -> ARGS1)
	 (|
	   where(VS -> list(V, nil))
	   Resolve(V, T1 -> V1)
	   where(VALUE_EXPRS'list(V1, nil) -> VS1)
	 ||
	   Resolve(product(P, VS), T1 -> product(_, VS1))
	 |)

  'rule' Resolve_args(nil, T -> nil):

-- debug
--   'rule' Resolve_args(ARGS, T -> nil):
-- where(ARGS -> list(fun_arg(P, _), _))
-- Puterror(P)
-- Putmsg("Cannot resolve args ")
-- print(ARGS)
-- Putmsg(" of type ")
-- print(T)

'action' Resolve_let(LET_DEFS, VALUE_EXPR, TYPE_EXPR -> LET_DEFS, VALUE_EXPR)

  'rule' Resolve_let(list(D, DS), V, T -> list(D1, DS1), V1):
	 Openenv()
	 Resolve_let_def(D -> D1)
	 Resolve_let(DS, V, T -> DS1, V1)
	 [|
	   CPPWanted()
	   Localise_value_env()
	 |]
	 Closeenv()

  'rule' Resolve_let(nil, V, T -> nil, V1)
	 Resolve(V, T -> V1)

'action' Resolve_let_def(LET_DEF -> LET_DEF)

  'rule' Resolve_let_def(explicit(P, LB, V) -> explicit(P, LB1, V2)):
	 Make_results(V -> list(result(T,_,_,_,_),_))
	 Resolve(V, T -> V1)
	 -- Try to improve on type
	 Type_of_val(V1, T -> T1)
	 (|
	   where(LB -> binding(P1,B))
	   Define_value_typing(single(P, B, T1))
	   where(LB -> LB1)
	 ||
	   where(LB -> pattern(P1,PATT))
	   Define_pattern(P, T1, PATT)
	   Resolve_pattern(PATT, T1 -> PATT1)
	   where(pattern(P1,PATT1) -> LB1)
	 |)
	 (|
	   (| CcWanted() || where(V1 -> disamb(_,_,_)) |)
	   where(V1 -> V2)
	 ||
	   -- add type information for translators
	   where(VALUE_EXPR'disamb(P, V1, T1) -> V2)	   
	 |)

  'rule' Resolve_let_def(implicit(P, TP, R) -> implicit(P, TP1, R1)):
	 Resolve_value_typing(TP -> TP1)
	 Define_value_typing(TP1)
	 (|
	   where(R -> restriction(P1, V))
	   Resolve(V, bool -> V1)
	   where(restriction(P1, V1) -> R1)
	 ||
	   where(RESTRICTION'nil -> R1)
	 |)

'action' Resolve_elsif(ELSIF_BRANCHES, TYPE_EXPR -> ELSIF_BRANCHES)

  'rule' Resolve_elsif(list(elsif(P, V, E, PE), ES), T -> list(elsif(P, V1, E1, PE), ES1)):
	 Resolve(V, bool -> V1)
	 Resolve(E, T -> E1)
	 Resolve_elsif(ES, T -> ES1)

  'rule' Resolve_elsif(nil, T -> nil):

'action' Resolve_case_branches(CASE_BRANCHES, TYPE_EXPR, TYPE_EXPR -> CASE_BRANCHES)

  'rule' Resolve_case_branches(list(case(P,PATT,V,PE),BRS), PT, T -> list(case(P,PATT1,V1,PE),BRS1)):
	 Openenv()
	 Define_pattern(P, PT, PATT)
	 Resolve_pattern(PATT, PT -> PATT1)
	 Resolve(V, T -> V1)
	 [|
	   CPPWanted()
	   Localise_value_env()
	 |]
	 Closeenv()
	 Resolve_case_branches(BRS, PT, T -> BRS1)

  'rule' Resolve_case_branches(nil, PT, T -> nil):

'action' Split_fun_type(TYPE_EXPR -> TYPE_EXPR, TYPE_EXPR)

  'rule' Split_fun_type(T -> T1, T2):
	 (|
	   Make_function_type(T -> fun(T1,_,result(T2,_,_,_,_)))
	 ||
	   Make_map_type(T -> fin_map(T1,T2))
	 ||
	   Make_list_type(T -> fin_list(T2))
	   where(nat -> T1)
	 ||
	   Make_map_type(T -> infin_map(T1,T2))
	 ||
	   Make_list_type(T -> infin_list(T2))
	   where(nat -> T1)
	 ||
	   -- not a type that can be applied
	   where(none -> T1)
	   where(none -> T2)
	 |)

'action' Prune_by_result_type(RESULTS, TYPE_EXPR, ACTUAL_FUNCTION_PARAMETERS -> RESULTS)

  'rule' Prune_by_result_type(list(result(T,RD,WR,IN,OUT), RS), T1, ARGS -> RS1):
	 Prune_by_result_type(RS, T1, ARGS -> RS2)
	 Get_result_type(T, ARGS -> T2)
	 (|
	   ne(T2, none)
	   Unify_by_result(T1, T2, T -> T3)
	   ne(T3, none)
	   where(RESULTS'list(result(T3,RD,WR,IN,OUT), RS2) -> RS1)
	 ||
	   where(RS2 -> RS1)
	 |)

  'rule' Prune_by_result_type(nil, T, ARGS -> nil):

'action' Get_result_type(TYPE_EXPR, ACTUAL_FUNCTION_PARAMETERS -> TYPE_EXPR)

  'rule' Get_result_type(T, list(ARG,ARGS) -> T1):
	 Split_fun_type(T -> _, T2)
	 Get_result_type(T2, ARGS -> T1)

  'rule' Get_result_type(T, nil -> T):

'action' Prune_by_arguments(RESULTS, ACTUAL_FUNCTION_PARAMETERS -> RESULTS)

-- first argument must suffice
  'rule' Prune_by_arguments(RS, list(fun_arg(P,VS), _) -> RS1):
	 (|
	   eq(VS, nil)
	   where(RESULTS'list(result(unit,nil,nil,nil,nil), nil) -> RS2) 
	 ||
	   where(VS -> list(V, nil))
	   Make_results(V -> RS2)
	 ||
	   Make_results(product(P,VS) -> RS2)
	 |)
	 Prune_by_argument(RS, RS2 -> RS1)

'action' Prune_by_argument(RESULTS, RESULTS -> RESULTS)

  'rule' Prune_by_argument(list(result(T,RD,WR,IN,OUT), FRS), ARGRS -> FRS1):
	 Prune_by_argument(FRS, ARGRS -> FRS2)
	 Split_fun_type(T -> D, _)
	 (|
	   ne(D, none)
	   Isin_domain_results(D, ARGRS)
	   where(RESULTS'list(result(T,RD,WR,IN,OUT), FRS2) -> FRS1)
	 ||
	   where(FRS2 -> FRS1)
	 |)

  'rule' Prune_by_argument(nil, ARGRS -> nil):

'condition' Isin_domain_results(TYPE_EXPR, RESULTS)

  'rule' Isin_domain_results(T, list(result(T1,_,_,_,_), RS)):
	 (| Match(T1, up, T) || Isin_domain_results(T, RS) |)

'action' Select_id_by_type(Value_ids, TYPE_EXPR -> OPT_VALUE_ID)

  'rule' Select_id_by_type(list(I, Ids), T -> Oid):
	 I'Type -> T1
	 (|
	   Match(T1, up, T)
	   where(value_id(I) -> Oid)
	 ||
	   Select_id_by_type(Ids, T -> Oid)
	 |)

  'rule' Select_id_by_type(nil, T -> nil):

'action' Prune_by_argument_resolution(TYPE_EXPR, RESULTS -> TYPE_EXPR)

  'rule' Prune_by_argument_resolution(T, list(result(T1,_,_,_,_), REST) -> T2):
	 (|
	   Unify_to_resolve(T, T1 -> T3)
	   ne(T3, none)
	   where(T3 -> T2)
	 ||
	   Prune_by_argument_resolution(T, REST -> T2)
	 |)

  'rule' Prune_by_argument_resolution(_, nil -> none):

'action' Expand_scheme_args_implementation(POS, OBJECT_EXPRS, OBJECT_EXPRS -> VALUE_EXPR)

  'rule' Expand_scheme_args_implementation(P, list(O1, OS1), list(O2, OS2) -> ax_infix(P, C1, and, C2, P)):
	 Resolve(implementation_expr(P, O1, O2), bool -> C1)
	 Expand_scheme_args_implementation(P, OS1, OS2 -> C2)

  'rule' Expand_scheme_args_implementation(_, nil, _ -> no_val):


'action' Establish_resolved_scheme_env(IDENT)
-- For use with non-parameterized schemes.
-- Reuses environment to save generating it afresh,
-- or saves it if this is the first time.
-- As side effect, raises curent environment by one level;
-- the top level is the scheme environment.
-- Similarly adds one level to Extend_paths.

  'rule' Establish_resolved_scheme_env(Id):
	 Get_id_of_scheme(Id -> scheme_id(I))
	 Current -> C
	 Extend_paths -> Paths
	 Get_current_with(-> WITH)
	 I'Class -> CL
	 (|
	   I'Env -> nil
	   Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	   Extend_paths <- list(nil,Paths)
	   Make_basic_env(CL)
	   Complete_type_env(CL)
	   Make_value_env(CL)
	   Check_value_env(CL)
	   Resolve_class(CL)
	   Current -> current_env(CE, C1)
	   I'Env <- CE
	 ||
	   I'Env -> CE
	   Current <- current_env(CE, C)
	   Extend_paths <- list(nil,Paths)
	 |)

----------------------------------------------------------------
-- Resolve typings
----------------------------------------------------------------

'action' Resolve_value_typings(TYPINGS -> TYPINGS)

  'rule' Resolve_value_typings(list(T, TS) -> list(T1, TS1)):
	 Resolve_value_typing(T -> T1)
	 Resolve_value_typings(TS -> TS1)

  'rule' Resolve_value_typings(nil -> nil):

'action' Resolve_value_typing(TYPING -> TYPING)

  'rule' Resolve_value_typing(single(P, B, T) -> single(P, B, T1)):
	 Resolve_type(T -> T1)


  'rule' Resolve_value_typing(multiple(P, BS, T) -> multiple(P, BS, T1)):
	 Resolve_type(T -> T1)


----------------------------------------------------------------
-- Resolve patterns
----------------------------------------------------------------

'action' Resolve_pattern(PATTERN, TYPE_EXPR -> PATTERN)

  'rule' Resolve_pattern(name_pattern(P, N), T -> name_occ_pattern(P, I, Q)):
	 Lookup_value_name(P, N -> Ids)
	 (|
	   where(Ids -> list(I, nil))
	 ||
	   Select_id_by_type(Ids, T -> value_id(I))
	 |)
	 (|
	   where(N -> qual_name(_,Obj,_))
--	   I'Qualifier -> Ids1
	   Resolve_object(Obj -> Obj1)
	   where(qualification(Obj1) -> Q)
	 ||
	   where(OPT_QUALIFICATION'nil -> Q)
	 |)

  'rule' Resolve_pattern(record_pattern(P, N, AS), T -> record_occ_pattern(P, I, Q, AS1)):
	 Lookup_value_name(P, N -> Ids)
	 (|
	   where(Ids -> list(I, nil))
	 ||
	   Select_id_by_type(Ids, fun(any,partial,result(T,nil,nil,nil,nil)) -> value_id(I))
	 |)
	 (|
	   where(N -> qual_name(_,Obj,_))
--	   I'Qualifier -> Ids1
	   Resolve_object(Obj -> Obj1)
	   where(qualification(Obj1) -> Q)
	 ||
	   where(OPT_QUALIFICATION'nil -> Q)
	 |)
	 I'Type -> T1
	 Make_function_type(T1 -> fun(D,A,R))
	 (|
	   where(AS -> PATTERNS'list(PATT, nil))
	   Resolve_pattern(PATT, D -> PATT1)
	   where(PATTERNS'list(PATT1, nil) -> AS1)
	 ||
	   Length_ps(AS -> Num)
	   Make_product_type(D, Num -> product(TS)) 
	   Resolve_product_patterns(AS, TS -> AS1)
	 |)

  'rule' Resolve_pattern(product_pattern(P, PATTS), T -> product_pattern(P, PATTS1)):
	 Length_ps(PATTS -> N)
	 Make_product_type(T, N -> product(TS)) 
	 Resolve_product_patterns(PATTS, TS -> PATTS1)

  'rule' Resolve_pattern(enum_list(P, PATTS), T -> enum_list(P, PATTS1)):
	 Make_list_type(T -> VT1) 
	 (| where(VT1 -> fin_list(T1)) || where(VT1 -> infin_list(T1)) |)
	 Resolve_list_patterns(PATTS, T1 -> PATTS1)

  'rule' Resolve_pattern(conc_list(P, PATTS, R), T -> conc_list(P, PATTS1, R1)):
	 Make_list_type(T -> VT1) 
	 (| where(VT1 -> fin_list(T1)) || where(VT1 -> infin_list(T1)) |) 
	 Resolve_list_patterns(PATTS, T1 -> PATTS1)
	 Resolve_pattern(R, T -> R1)

-- other cases
  'rule' Resolve_pattern(PATT, _ -> PATT):

'action' Resolve_product_patterns(PATTERNS, PRODUCT_TYPE -> PATTERNS)

  'rule' Resolve_product_patterns(list(PATT,PATTS), list(T, TS) -> list(PATT1,PATTS1)):
	 Resolve_pattern(PATT, T -> PATT1)
	 Resolve_product_patterns(PATTS, TS -> PATTS1)

  'rule' Resolve_product_patterns(nil, _ -> nil):

'action' Resolve_list_patterns(PATTERNS, TYPE_EXPR -> PATTERNS)

  'rule' Resolve_list_patterns(list(PATT,PATTS), T -> list(PATT1,PATTS1)):
	 Resolve_pattern(PATT, T -> PATT1)
	 Resolve_list_patterns(PATTS, T -> PATTS1)

  'rule' Resolve_list_patterns(nil, _ -> nil):


----------------------------------------------------------------
-- Where confidence conditions needed
----------------------------------------------------------------

'type' CCNEEDED

       ccsubtype      (CCSUBTYPE)
       ccvaluedef     (CCVALUEDEF)
       ccprecond      (CCPRECOND)
       ccvariabledef  (CCVARIABLEDEF)
       ccassignment   (CCASSIGNMENT)
       ccoutput	      (CCOUTPUT)
       ccapplication  (CCAPPLICATION)
       ccconcurrent   (CCCONCURRENT)
       ccdisamb	      (CCDISAMB)
       ccenummap      (CCENUMMAP)
       ccobjappl      (CCOBJAPPL)
       ccpatternmatch (CCPATTERNMATCH)
       cccases	      (CCCASES)
       ccimplementation (CCIMPLEMENTATION)

'type' CCSUBTYPE

	subtype		(typing :	TYPING,
			 restr	:	RESTRICTION)

'type' CCVALUEDEF
	exp_val		(pos	:	POS,
			 typing :	TYPING,
			 expr	:	VALUE_EXPR)
	imp_val		(pos	:	POS,
			 typing :	TYPING,
			 cond	:	RESTRICTION)
	exp_fun		(pos	:	POS,
			 typing :	TYPING,
			 appl	:	FORMAL_FUNCTION_APPLICATION,
			 expr	:	VALUE_EXPR,
			 post	:	OPT_POST_CONDITION,
			 pre	:	PRE_CONDITION)
	imp_fun		(pos	:	POS,
			 typing :	TYPING,
			 appl	:	FORMAL_FUNCTION_APPLICATION,
			 post	:	POST_CONDITION,
			 pre	:	PRE_CONDITION)

'type' CCPRECOND
	precond		(pos	:	POS,
			 type	:	TYPE_EXPR,
			 parms	:	FORMAL_FUNCTION_PARAMETERS,
			 pre	:	PRE_CONDITION)

'type' CCVARIABLEDEF

	single		(pos	:	POS,
			 id	:	IDENT,
			 type	:	TYPE_EXPR,
			 init	:	INITIALISATION)

'type' CCASSIGNMENT 

	ass_occ		(pos	:	POS,
			 id	:	Variable_id,
			 qual	:	OPT_QUALIFICATION,
			 expr	:	VALUE_EXPR)

'type' CCOUTPUT

	output_occ	(pos	:	POS,
			 id	:	Channel_id,
			 qual	:	OPT_QUALIFICATION,
			 expr	:	VALUE_EXPR)

'type' CCAPPLICATION

	application	(pos	:	POS,
			 fun	:	VALUE_EXPR,
			 args	:	ACTUAL_FUNCTION_PARAMETERS)

	prefix_occ	(pos	:	POS,
			 op	:	Value_id,
			 qual	:	OPT_QUALIFICATION,
			 expr	:	VALUE_EXPR)

	infix_occ	(pos	:	POS,
			 left	:	VALUE_EXPR,
			 op	:	Value_id,
			 qual	:	OPT_QUALIFICATION,
			 right	:	VALUE_EXPR) 

'type' CCCONCURRENT

       concurrent	(pos	:	POS,
			 left	:	VALUE_EXPR,
			 right	:	VALUE_EXPR)

'type' CCDISAMB

	disamb		(pos	:	POS,
			 expr	:	VALUE_EXPR,
			 type	:	TYPE_EXPR)

'type' CCENUMMAP

	enum_map	(pos	:	POS,
			 exprs	:	VALUE_EXPR_PAIRS)

'type' CCOBJAPPL

	obj_appl	(pos	:	POS,
			 parms	:	VALUE_EXPRS,
			 type	:	TYPE_EXPR)

'type' CCPATTERNMATCH

	pattern_match	(pos	:	POS,
			 cond	:	VALUE_EXPR)

'type' CCCASES

	cases		(pos	:	POS,
			 cond	:	VALUE_EXPR)

'type' CCIMPLEMENTATION

	scoped_conditions(pos	:	POS,
			 class	:	CLASS,
			 expr	:	VALUE_EXPR)

	conditions	(pos	:	POS,
			 expr	:	VALUE_EXPR)

	formal_actual_conditions
			(pos	:	POS,
			 expr	:	VALUE_EXPR)

'type' ASSUMPTION

	typings		(TYPINGS)
	lets		(LET_DEFS)
	assumption	(VALUE_EXPR)
	post_ass	(VALUE_EXPR)
	class		(CLASS, CLASS_ENV)

'type' ASSUMPTIONS

	list		(ASSUMPTION,
			 ASSUMPTIONS)
	nil


----------------------------------------------------------------
-- Maximal types
----------------------------------------------------------------

'CONDITION' Maximal(TYPE_EXPR) 

     'rule' Maximal(unit):

     'rule' Maximal(bool):

     'rule' Maximal(int):

     'rule' Maximal(real):

     'rule' Maximal(char):

     'rule' Maximal(defined(Id, _)):
	    Id'Type->sort(_)

     'rule' Maximal(defined(Id, _)):
	    Id'Type->abbrev(T)
	    Maximal(T)

     'rule' Maximal(product(list(HD,TL))):
	    Maximal(HD)
	    Maximal(product(TL))

     'rule' Maximal(product(nil)):

     'rule' Maximal(fin_set(T)):
	    (| PVSWanted() || SALWanted() |)
	    Maximal(T)

     'rule' Maximal(infin_set(T)):
	    Maximal(T)

     'rule' Maximal(fin_list(T)):
	    (| PVSWanted() || SALWanted() |)
	    Maximal(T)

     'rule' Maximal(infin_list(T)):
	    Maximal(T)

     'rule' Maximal(fin_map(T1,T2)):
	    (| PVSWanted() || SALWanted() |)
	    Maximal(T1)
	    Maximal(T2)

     'rule' Maximal(infin_map(T1,T2)):
	    Maximal(T1)
	    Maximal(T2)

     'rule' Maximal(fun(T1,total,result(T2,_,_,_,_))):
	    (| PVSWanted() || SALWanted() |)
	    Maximal(T1)
	    Maximal(T2)

     'rule' Maximal(fun(T1,partial,result(T2,_,_,_,_))):
	    Maximal(T1)
	    Maximal(T2)

     'rule' Maximal(bracket(T)):
	    Maximal(T)

     'rule' Maximal(poly(_)):

----------------------------------------------------------------
-- Make maximal types
----------------------------------------------------------------

'action' Maxtype(TYPE_EXPR -> TYPE_EXPR) 

     'rule' Maxtype(unit -> unit):

     'rule' Maxtype(bool -> bool):

     'rule' Maxtype(int -> int):

     'rule' Maxtype(nat -> int):

     'rule' Maxtype(real -> real):

     'rule' Maxtype(time -> real):
	    IsTimed()

     'rule' Maxtype(text -> fin_list(char)):
	    (| PVSWanted() || SALWanted() |)

     'rule' Maxtype(text -> infin_list(char)):

     'rule' Maxtype(char -> char):

     'rule' Maxtype(defined(Id, Q) -> defined(Id, Q)):
	    Id'Type->sort(_)

     'rule' Maxtype(defined(Id, _) -> T1):
	    Id'Type->abbrev(T)
	    Maxtype(T -> T1)

     'rule' Maxtype(product(PR) -> product(PR1)):
	    Maxtype_product(PR -> PR1)

/*     'rule' Maxtype(fin_set(T) -> fin_set(T1)):
	    (| PVSWanted() || SALWanted() |)
	    Maxtype(T -> T1)

     'rule' Maxtype(fin_set(T) -> infin_set(T1)):
	    Maxtype(T -> T1)

     'rule' Maxtype(infin_set(T) -> infin_set(T1)):
	    Maxtype(T -> T1)*/

     'rule' Maxtype(fin_set(T) -> fin_set(T)):
	    (| PVSWanted() || SALWanted() |)
	    Maxtype(T -> T1)

     'rule' Maxtype(fin_set(T) -> infin_set(T)):
	    Maxtype(T -> T1)

     'rule' Maxtype(infin_set(T) -> infin_set(T)):
	    Maxtype(T -> T1)


     'rule' Maxtype(fin_list(T) -> fin_list(T1)):
	    (| PVSWanted() || SALWanted() |)
	    Maxtype(T -> T1)

     'rule' Maxtype(fin_list(T) -> infin_list(T1)):
	    Maxtype(T -> T1)

     'rule' Maxtype(infin_list(T) -> infin_list(T1)):
	    Maxtype(T -> T1)

     'rule' Maxtype(fin_map(T1,T2) -> fin_map(T3,T4)):
	    (| PVSWanted() || SALWanted() |)
	    Maxtype(T1 -> T3)
	    Maxtype(T2 -> T4)

     'rule' Maxtype(fin_map(T1,T2) -> infin_map(T3,T4)):
	    Maxtype(T1 -> T3)
	    Maxtype(T2 -> T4)

     'rule' Maxtype(infin_map(T1,T2) -> infin_map(T3,T4)):
	    Maxtype(T1 -> T3)
	    Maxtype(T2 -> T4)

     'rule' Maxtype(fun(T1,total,result(T2,R,W,I,O)) -> fun(T3,total,result(T4,R,W,I,O))):
	    (| PVSWanted() || SALWanted() |)
	    Maxtype(T1 -> T3)
	    Maxtype(T2 -> T4)

     'rule' Maxtype(fun(T1,total,result(T2,R,W,I,O)) -> fun(T3,partial,result(T4,R,W,I,O))):
	    Maxtype(T1 -> T3)
	    Maxtype(T2 -> T4)

     'rule' Maxtype(fun(T1,partial,result(T2,R,W,I,O)) -> fun(T3,partial,result(T4,R,W,I,O))):
	    Maxtype(T1 -> T3)
	    Maxtype(T2 -> T4)

     'rule' Maxtype(subtype(TP,_) -> T1):
	    (| where(TP -> single(_,_,T)) || where(TP -> multiple(_,_,T)) |)
	    Maxtype(T -> T1)

     'rule' Maxtype(bracket(T) -> bracket(T1)):
	    Maxtype(T -> T1)

     'rule' Maxtype(array(T1,T2) -> array(T1,T2)):
            --Maxtype(T1 -> T3)
            --Maxtype(T2 -> T4)

   'rule' Maxtype(T -> T1):
	 Maxtype1(T -> T1)

'action' Maxtype1(TYPE_EXPR -> TYPE_EXPR)

  'rule' Maxtype1(T -> T)
	 Putmsg("Internal error: need maxtype of: ")
	 Print_type(T)
	 Putnl()
print(T)

'action' Maxtype_product(PRODUCT_TYPE -> PRODUCT_TYPE)

  'rule' Maxtype_product(list(T, TS) -> list(T1, TS1)):
	 Maxtype(T -> T1)
	 Maxtype_product(TS -> TS1)

  'rule' Maxtype_product(nil -> nil)


----------------------------------------------------------------
-- Values are in subtypes
----------------------------------------------------------------

'action' Isin_subtype(VALUE_EXPR, TYPE_EXPR -> VALUE_EXPR)

  'rule' Isin_subtype(product(_, list(V, nil)), T -> Val_expr):
	 Isin_subtype(V, T -> Val_expr)

  'rule' Isin_subtype(V, product(list(T, nil)) -> Val_expr):
	 Isin_subtype(V, T -> Val_expr)

  'rule' Isin_subtype(VAL, bracket(T) -> Val_expr):
	 Isin_subtype(VAL, T -> Val_expr)

  'rule' Isin_subtype(VAL, defined(Tid, _) -> Val_expr):
	 SALWanted()
	 Tid'Def->abbreviation(T)
	 Tid'Subtype -> nil
	 Isin_subtype(VAL, T -> Val_expr)

  'rule' Isin_subtype(VAL, int -> application(P,val_occ(P, I, nil), list(fun_arg(P,list(VAL,nil)),nil))):
	 SALWanted()
	 Id_of_rsl_is_int -> I
	 DefaultPos(->P)

  'rule' Isin_subtype(VAL, T -> no_val):
	 Maximal(T)

  'rule' Isin_subtype(VAL, nat -> application(P,val_occ(P, I, nil), list(fun_arg(P,list(VAL,nil)),nil))):
	 SALWanted()
	 Id_of_rsl_is_nat -> I
	 DefaultPos(->P)

  'rule' Isin_subtype(VAL, T:defined(Tid, Q) -> Val_expr):
         SALWanted()
         Tid'Subtype -> funct(I)
         I'Pos -> P
         I'Type -> fun(T1,_,_)
         where(VALUE_EXPR'application(P, val_occ(P, I, Q), list(fun_arg(P,list(VAL,nil)),nil)) -> Val_expr)

  'rule' Isin_subtype(VAL, T -> no_val):
	 Maxtype(T -> Tm)
	 Type_of_val(VAL, Tm -> T1)
-- debug
-- Putmsg("Checking ")
-- Print_expr(VAL)
-- Putmsg(" of type ")
-- Print_type(T1)
-- Putmsg(" in type ")
-- Print_type(T)
-- Putnl()
	 Static_subtype(T1, T)
-- Putmsg("OK\n")

  'rule' Isin_subtype(VAL, nat -> application(P,val_occ(P, I, nil), list(fun_arg(P,list(VAL,nil)),nil))):
	 CPPWanted()
	 Id_of_rsl_is_nat -> I
	 DefaultPos(->P)

  'rule' Isin_subtype(VAL, nat -> infix_occ(P,VAL,I,nil,literal_expr(P,int(Zero)))):
	 DefaultPos(->P)
	 string_to_id("0" -> Zero)
	 Id_of_ge_int -> I

  'rule' Isin_subtype(VAL, time -> infix_occ(P,VAL,I,nil,literal_expr(P,real(Zero)))):
	 IsTimed()
	 DefaultPos(->P)
	 string_to_id("0.0" -> Zero)
	 Id_of_ge_real -> I

  'rule' Isin_subtype(VAL, text -> no_val):
	 (| SMLWanted() || CPPWanted() |)

  'rule' Isin_subtype(VAL, text -> 
		      post(P,prefix_occ(P,I,nil,VAL),post_cond(P,nil,literal_expr(P, bool_true)),nil)):
	 DefaultPos(->P)
	 Id_of_len -> I

  'rule' Isin_subtype(VAL, T:defined(Tid, Q) -> Val_expr):
         (| SMLWanted() || CPPWanted() |)
         Tid'Subtype -> funct(I)
         I'Pos -> P
         I'Type -> fun(T1,_,_)
         where(VALUE_EXPR'application(P, val_occ(P, I, Q), list(fun_arg(P,list(VAL,nil)),nil)) -> Val_expr)
-- debug
-- Putmsg("Condition for ")
-- Print_type(T)
-- Putmsg(" is ")
-- Print_expr(Val_expr)
-- Putnl()

  'rule' Isin_subtype(VAL, defined(Tid, _) -> Val_expr):
	 Tid'Def->abbreviation(T)
	 Isin_subtype(VAL, T -> Val_expr)

-- seems possible to get here from cpp.g before resolved to abbreviation TODO
  'rule' Isin_subtype(VAL, defined(Tid, _) -> Val_expr):
	 Tid'Type -> abbrev(T)
	 Resolve_type(T -> T1)
	 Isin_subtype(VAL, T1 -> Val_expr)

  'rule' Isin_subtype(product(P,list(VH,VT)), product(list(HD,TL)) -> Val_expr):
	 Isin_subtype(VH, HD -> Val_expr1)
	 Isin_subtype(product(P,VT), product(TL) -> Val_expr2)
	 where(ax_infix(P,Val_expr1,and,Val_expr2,P) -> Val_expr)

  'rule' Isin_subtype(VAL, product(list(HD,TL)) -> Val_expr):
	 Maxtype(product(list(HD,TL)) -> Tm)
	 -- get best type
	 Type_of_val(VAL, Tm -> T1)
	 (|
	   where(T1 -> product(list(HD1,TL1)))
	 ||
	   Length_pr(list(HD,TL) -> N)
	   Make_product_type(T1, N -> product(list(HD1,TL1)))
	 |)
	 Make_product_expression_and_binding(product(list(HD1,TL1)) -> Val_expr1, B)
	 Isin_subtype(Val_expr1, product(list(HD,TL)) -> Val_expr2)
	 DefaultPos(->P)
	 (|
	   (| SMLWanted() || CPPWanted() || PVSWanted() || SALWanted()||FDRWanted() |)
	   where(VALUE_EXPR'disamb(P, VAL, T1) -> VAL1)
	 ||
	   where(VAL -> VAL1)
	 |)
	 where(let_expr(P,
			list(explicit(P, binding(P, B), VAL1), nil),
			Val_expr2)
	       -> Val_expr)

  'rule' Isin_subtype(VAL, fin_set(_) -> no_val):
	 Is_empty_set(VAL)

  'rule' Isin_subtype(VAL, fin_set(T) -> Val_expr):
	 (| SMLWanted() || CPPWanted() || PVSWanted()|| SALWanted()||FDRWanted() |)
	 Isin_subtype(VAL, infin_set(T) -> Val_expr)

  'rule' Isin_subtype(VAL, fin_set(T) -> Val_expr):
	 DefaultPos(->P)
	 Maxtype(T -> Tm)
	 -- get best type
	 Type_of_val(VAL, infin_set(Tm) -> VT)
	 Make_set_type(VT -> VT1)
	 (| -- see if known to be finite
	   where(VT1 -> fin_set(T1))
	   where(no_val ->  Val_expr1)
	 ||
	   where(VT1 -> infin_set(T1))
	   Id_of_card -> I
	   where(VALUE_EXPR'post(P,prefix_occ(P,I,nil,VAL),post_cond(P,nil,literal_expr(P, bool_true)),nil)
	       -> Val_expr1)
	 |)
	 (|
	   Static_subtype(T1, T)
	   where(no_val ->  Val_expr4)
	 ||
	   string_to_id("x_" -> X)
	   New_value_id(P, id_op(X) -> I)
	   I'Type <- T1
	   Isin_subtype(val_occ(P,I,nil), T -> Val_expr2)
	   Id_of_isin_set -> I1
	   where(ax_infix(P,infix_occ(P,val_occ(P,I,nil),I1,nil,VAL),implies,Val_expr2,P)
		 -> Val_expr3)
	   where(quantified(P,all,list(single(P,single(P,id_op(X)),T1),nil),restriction(P,Val_expr3)) 
		 -> Val_expr4)
	 |)
	 where(ax_infix(P,Val_expr1,and,Val_expr4,P) -> Val_expr)

  'rule' Isin_subtype(VAL, infin_set(_) -> no_val):
	 Is_empty_set(VAL)

  'rule' Isin_subtype(VAL, infin_set(_) -> no_val):
-- SAL checks subtype correctness of sets during creation
         SALWanted()

  'rule' Isin_subtype(VAL, infin_set(T) -> Val_expr):
	 DefaultPos(->P)
	 Maxtype(T -> Tm)
	 -- get best type
	 Type_of_val(VAL, infin_set(Tm) -> VT)
	 Make_set_type(VT -> VT1)
	 (| where(VT1 -> fin_set(T1)) || where(VT1 -> infin_set(T1)) |)
	 string_to_id("x_" -> X)
	 New_value_id(P, id_op(X) -> I)
	 [|
	   CPPWanted()
	   Localise_value_id(I)
	 |]
	 I'Type <- T1
	 Isin_subtype(val_occ(P,I,nil),T -> Val_expr2)
	 Id_of_isin_set -> I1
	 where(ax_infix(P,infix_occ(P,val_occ(P,I,nil),I1,nil,VAL),implies,Val_expr2,P)
	       -> Val_expr3)
	 where(quantified(P,all,list(single(P,single(P,id_op(X)),T1),nil),restriction(P,Val_expr3)) 
	       -> Val_expr)

  'rule' Isin_subtype(VAL, fin_list(_) -> no_val):
	 Is_empty_list(VAL)

  'rule' Isin_subtype(VAL, fin_list(T) -> Val_expr):
	 (| SMLWanted() || CPPWanted() |)
	 Isin_subtype(VAL, infin_list(T) -> Val_expr)

  'rule' Isin_subtype(VAL, fin_list(T) -> Val_expr):
	 DefaultPos(->P)
	 Maxtype(T -> Tm)
	 -- get b-est type
	 Type_of_val(VAL, infin_list(Tm) -> VT)
	 Make_list_type(VT -> VT1)
	 (| -- see if known to be finite
	   where(VT1 -> fin_list(T1))
	   where(no_val ->  Val_expr1)
	 ||
	   where(VT1 -> infin_list(T1))
	   Id_of_len -> I
	   where(VALUE_EXPR'post(P,prefix_occ(P,I,nil,VAL),post_cond(P,nil,literal_expr(P, bool_true)),nil)
	       -> Val_expr1)
	 |)
	 (|
	   Static_subtype(T1, T)
	   where(no_val ->  Val_expr4)
	 ||
	   string_to_id("x_" -> X)
	   New_value_id(P, id_op(X) -> I)
	   I'Type <- T1
	   Isin_subtype(val_occ(P,I,nil), T -> Val_expr2)
	   Id_of_isin_map -> I1
	   where(ax_infix(P,
			  infix_occ(P,val_occ(P,I,nil),I1,nil,VAL),
			  implies,
			  Val_expr2,P)
		 -> Val_expr3)
	   where(quantified(P,all,list(single(P,single(P,id_op(X)),T1),nil),restriction(P,Val_expr3)) 
		   -> Val_expr4)
	 |)
	 where(ax_infix(P,Val_expr1,and,Val_expr4,P) -> Val_expr)

  'rule' Isin_subtype(VAL, infin_list(_) -> no_val):
	 Is_empty_list(VAL)

  'rule' Isin_subtype(VAL, infin_list(T) -> Val_expr):
	 DefaultPos(->P)
	 Maxtype(T -> Tm)
	 -- get best type
	 Type_of_val(VAL, infin_list(Tm) -> VT)
	 Make_list_type(VT -> VT1)
	 (| where(VT1 -> fin_list(T1)) || where(VT1 -> infin_list(T1)) |)
	 string_to_id("x_" -> X)
	 New_value_id(P, id_op(X) -> I)
	 [|
	   CPPWanted()
	   Localise_value_id(I)
	 |]
	 I'Type <- T1
	 Isin_subtype(val_occ(P,I,nil), T -> Val_expr2)
	 Id_of_isin_list -> I1
	 where(ax_infix(P,
			infix_occ(P,val_occ(P,I,nil),I1,nil,VAL),
			implies,
			Val_expr2,P)
		-> Val_expr3)
	 where(quantified(P,all,list(single(P,single(P,id_op(X)),T1),nil),restriction(P,Val_expr3)) 
	       -> Val_expr)

  'rule' Isin_subtype(VAL, fin_map(_,_) -> no_val):
	 Is_empty_map(VAL)

  'rule' Isin_subtype(VAL, fin_map(D,R) -> Val_expr):
	 (| SMLWanted() || CPPWanted() || PVSWanted() || SALWanted()||FDRWanted() |)
	 Isin_subtype(VAL, infin_map(D,R) -> Val_expr)

  'rule' Isin_subtype(VAL, fin_map(D,R) -> Val_expr):
-- we use the following sub predicates
-- 1fin : Isin_subtype(dom VAL, D-set)
-- 1inf : Isin_subtype(dom VAL, D-infset)
-- 2	: Isin_subtype(rng VAL, R-infset)
-- 3	: all x : D :- x isin dom VAL => (exists! y : R :- y = VAL(x))

	 DefaultPos(->P)
	 Maxtype(D -> Dm)
	 Maxtype(R -> Rm)
	 -- get best type
	 Type_of_val(VAL, infin_map(Dm,Rm) -> VT)
	 Make_map_type(VT -> VT1)
	 (|
	   where(VT1 -> fin_map(D1, R1))
	   (|
	     Static_subtype(D1, D)
	     -- generate 2
	     Apply_rng(P, VAL -> Rngval)
	     Isin_subtype(Rngval, infin_set(R) -> Val_expr)
	   ||
	     Apply_dom(P, VAL -> Domval)
	     Isin_subtype(Domval, infin_set(D) -> V1inf)
	     (|
	       Static_subtype(R1, R)
	       -- generate 1inf
	       where(V1inf -> Val_expr)
	     ||
	       -- generate 1inf /\ 2
	     Apply_rng(P, VAL -> Rngval)
	     Isin_subtype(Rngval, infin_set(R) -> V2)
	     where(ax_infix(P,V1inf,and,V2,P) -> Val_expr)
	     |)
	   |)
	 ||
	   -- not known to be finite
	   -- generate 1fin /\ 2 /\ 3
	   Apply_dom(P, VAL -> Domval)
	   Isin_subtype(Domval, fin_set(D) -> V1fin)
	   Apply_rng(P, VAL -> Rngval)
	   Isin_subtype(Rngval, infin_set(R) -> V2)
	   string_to_id("x_" -> X)
	   New_value_id(P, id_op(X) -> Ix)
	   Ix'Type <- D
	   string_to_id("y_" -> Y)
	   New_value_id(P, id_op(Y) -> Iy)
	   Iy'Type <- R
	   Id_of_eq -> Ieq
	   where(quantified(P,exists1,list(single(P,single(P,id_op(Y)),R),nil),
			    restriction(P,
					infix_occ(P,
						  val_occ(P,Iy,nil),
						  Ieq, nil,
						  application(P,VAL,
							      list(fun_arg(P,list(val_occ(P,Ix,nil),nil)),nil)))
					)
			    )
		   -> V31)
	   Id_of_isin_set -> Iisin
	   where(ax_infix(P,
			  infix_occ(P,val_occ(P,Ix,nil),Iisin,nil,Domval),
			  implies,
			  V31,P)
		 -> V32)
	   where(quantified(P,all,list(single(P,single(P,id_op(X)),D),nil),restriction(P,V32)) 
		 -> V3)
	   where(ax_infix(P,V1fin,and,V2,P) -> V12)
	   where(ax_infix(P,V12,and,V3,P) -> Val_expr)
	 |)

  'rule' Isin_subtype(VAL, infin_map(_,_) -> no_val):
         Is_empty_map(VAL)

  'rule' Isin_subtype(VAL, infin_map(D,R) -> no_val):
	 -- SAL checks subtype correctness of maps during creation
         SALWanted()

  'rule' Isin_subtype(VAL, infin_map(D,R) -> Val_expr):
	 DefaultPos(->P)
	 Maxtype(D -> Dm)
	 Maxtype(R -> Rm)
	 -- get best type
	 Type_of_val(VAL, infin_map(Dm,Rm) -> VT)
	 Make_map_type(VT -> VT1)
	 (| where(VT1 -> fin_map(D1,R1)) || where(VT1 -> infin_map(D1,R1)) |)
	 (|
	   Static_subtype(D1, D)
	   where(no_val -> Val_expr1)
	 ||
	   Apply_dom(P, VAL -> Domval)
	   Isin_subtype(Domval, infin_set(D) -> Val_expr1)
	 |)
	 (|
	   Static_subtype(R1, R)
	   where(no_val -> Val_expr2)
	 ||
	   Apply_rng(P, VAL -> Rngval)
	   Isin_subtype(Rngval, infin_set(R) -> Val_expr2)
	 |)
	 where(ax_infix(P,Val_expr1,and,Val_expr2,P) -> Val_expr)

  'rule' Isin_subtype(VAL, fun(T1,_,result(T2,RD,WR,IN,OUT)) -> no_val):
	 (| SMLWanted() || CPPWanted() |)

  'rule' Isin_subtype(VAL, fun(T1,total,result(T2,_,_,_,_)) -> Val_expr):
	 DefaultPos(->P)
	 string_to_id("x_" -> X)
	 New_value_id(P, id_op(X) -> Ix)
	 Ix'Type <- T1
	 string_to_id("y_" -> Y)
	 New_value_id(P, id_op(Y) -> Iy)
	 Iy'Type <- T2
	 Id_of_eq -> Ieq
	 where(quantified(P,exists1,list(single(P,single(P,id_op(Y)),T2),nil),
			  restriction(P,
				      infix_occ(P,
						val_occ(P,Iy,nil),
						Ieq, nil,
						application(P,VAL,
							    list(fun_arg(P,list(val_occ(P,Ix,nil),nil)),nil)))
				      )
			  )
		 -> Val_expr1)
	 where(quantified(P,all,list(single(P,single(P,id_op(X)),T1),nil),restriction(P,Val_expr1)) 
	       -> Val_expr)

  'rule' Isin_subtype(VAL, fun(T1,partial,result(T2,R,W,I,O)) -> Val_expr):
	 DefaultPos(->P)
	 string_to_id("x_" -> X)
	 New_value_id(P, id_op(X) -> Ix)
	 Ix'Type <- T1
	 where(VALUE_EXPR'post(P,
		    application(P,
				VAL,
				list(fun_arg(P,list(val_occ(P,Ix,nil),nil)),nil)),
		    post_cond(P,nil,literal_expr(P, bool_true)),
		    nil)
	       -> Val_expr1)
	 Isin_subtype(application(P,
				  VAL,
				  list(fun_arg(P,list(val_occ(P,Ix,nil),nil)),nil)),
		      T2 -> Val_expr2)
	 where(ax_infix(P,Val_expr1,implies,Val_expr2,P) -> Val_expr3)
	 where(quantified(P,all,list(single(P,single(P,id_op(X)),T1),nil),restriction(P,Val_expr3)) 
	       -> Val_expr)

  'rule' Isin_subtype(VAL, subtype(single(P,B,T),restriction(_,Val_expr3)) -> Val_expr):
	 Isin_subtype(VAL, T -> Val_expr1)
	 (|
	   (| PVSWanted() || SALWanted() |)
	   (| Is_empty_set(VAL) || Is_empty_list(VAL) || Is_empty_map(VAL) |)
	   where(VALUE_EXPR'disamb(P, VAL, T) -> VAL1)
	 ||
	   where(VAL -> VAL1)
	 |)
	 where(let_expr(P,list(explicit(P,binding(P,B),VAL1),nil),Val_expr3) 
	       -> Val_expr2) 
	 where(ax_infix(P,Val_expr1,and,Val_expr2,P) -> Val_expr)


  'rule' Isin_subtype(VAL, array(T1,T2) -> no_val) -- TODO: Is this correct
         /*Maxtype(T1 -> T3)
         Maxtype(T2 -> T4)
         Type_of_val(VAL, array(T3,T4) -> VR)*/


-- debug
--   'rule' Isin_subtype(VAL, T -> no_val):
-- Putmsg("Cannot decide if ")
-- print(VAL)
-- Print_expr(VAL)
-- Putmsg(" is in ")
-- print(T)
-- Print_type(T)
-- Putnl()

'action' Isin_subtype_array_indexes(VALUE_EXPRS, TYPE_EXPR -> VALUE_EXPR)

  'rule' Isin_subtype_array_indexes(nil, _ -> no_val)

  'rule' Isin_subtype_array_indexes(list(H,T), Type -> Res)
         DefaultPos(->P)
         Remove_Brackets(Type -> array(IT,VT))
         Isin_subtype(H, IT -> Cond1)
         Isin_subtype_array_indexes(T, VT -> Cond2)
         (|
           where(Cond2 -> no_val)
           where(Cond1 -> Res)
         ||
           where(Cond1 -> no_val)
           where(Cond2 -> Res)
         ||
           where(ax_infix(P, Cond1, and, Cond2, P) -> Res)
         |)

'action' Make_product_expression_and_binding(TYPE_EXPR -> 
						    VALUE_EXPR, BINDING)

     'rule' Make_product_expression_and_binding(product(list(HD,TL)) -> 
		   product(P,list(V,Vs)), product(P,list(B, Bs))):
	    NewCcCount(-> N)
	    Make_concatenation("x", N -> S)
	    string_to_id(S -> ID)
	    Make_product_expression_and_binding(product(TL) -> 
		   product(P,Vs), product(_, Bs))
	    New_value_id(P, id_op(ID) -> I)
	    [|
	      CPPWanted()
	      Localise_value_id(I)
	    |]
	    I'Type <- HD
	    where(val_occ(P, I, nil) -> V)
	    -- binding id not localised as done later in cpp.g
	    where(BINDING'single(P,id_op(ID)) -> B)

     'rule' Make_product_expression_and_binding(product(nil) -> 
		   product(P,nil), product(P,nil)):
	    DefaultPos(->P)

'condition' Is_empty_set(VALUE_EXPR)

  'rule' Is_empty_set(enum_set(_, nil)):

  'rule' Is_empty_set(disamb(_, V, _)):
	 Is_empty_set(V)

  'rule' Is_empty_set(bracket(_, V)):
	 Is_empty_set(V)

  'rule' Is_empty_set(prefix_occ(_, I, _, V)):
	 I'Ident -> op_op(Op)
	 Built_in(Op, I)
	 (|
	   (| eq(Op, dom) || eq(Op, rng) |)
	   Is_empty_map(V)
	 ||
	   (| eq(Op, elems) || eq(Op, inds) |)
	   Is_empty_list(V)
	 |)

'condition' Is_empty_map(VALUE_EXPR)

  'rule' Is_empty_map(enum_map(_, nil)):

  'rule' Is_empty_map(disamb(_, V, _)):
	 Is_empty_map(V)

  'rule' Is_empty_map(bracket(_, V)):
	 Is_empty_map(V)

'condition' Is_empty_list(VALUE_EXPR)

  'rule' Is_empty_list(enum_list(_, nil)):

  'rule' Is_empty_list(disamb(_, V, _)):
	 Is_empty_list(V)

  'rule' Is_empty_list(bracket(_, V)):
	 Is_empty_list(V)


----------------------------------------------------------------
-- Subtypes are not empty
----------------------------------------------------------------

'action' Not_empty(CCSUBTYPE -> VALUE_EXPR)

  'rule' Not_empty(subtype(single(P,B,T), Restriction) ->
		   quantified(P,exists,list(single(P,B,T),nil),Restriction)):

----------------------------------------------------------------
-- Simplify logical value expressions
----------------------------------------------------------------

'condition' Simplify(VALUE_EXPR -> VALUE_EXPR)

     'rule' Simplify(literal_expr(P,bool_true) -> literal_expr(P,bool_true)):

     'rule' Simplify(literal_expr(P,bool_false) -> literal_expr(P,bool_false)):

     'rule' Simplify(ax_prefix(P,not,LVE) -> Value_expr):
	    Simplify(LVE -> LVE1)
	    (|
	      where(LVE1-> literal_expr(P1,bool_true))
	      where(literal_expr(P,bool_false) -> Value_expr)
	    ||
	      where(LVE1-> literal_expr(P1,bool_false))
	      where(literal_expr(P,bool_true) -> Value_expr)
	    ||
	      where(ax_prefix(P,not,LVE1) -> Value_expr)
	    |)

     'rule' Simplify(ax_infix(P,LVE1,or,LVE2,PE) -> Value_expr):
	      Simplify(LVE1 -> LVE3)
	      Simplify(LVE2 -> LVE4)
	    (|
	      where(LVE3-> literal_expr(P1,bool_true))
	      where(literal_expr(P,bool_true) -> Value_expr)
	    ||
	      where(LVE3-> literal_expr(P1,bool_false))
	      Simplify(LVE4 -> Value_expr)
	    ||
	      where(LVE3-> no_val)
	      where(no_val -> Value_expr)
	    ||
	      where(LVE4-> literal_expr(P1,bool_true))
	      where(literal_expr(P,bool_true) -> Value_expr)
	    ||
	      where(LVE4-> literal_expr(P1,bool_false))
	      Simplify(LVE3 -> Value_expr)
	    ||
	      where(LVE4-> no_val)
	      where(no_val -> Value_expr)
	    ||
	      where(ax_infix(P,LVE3,or,LVE4,PE) -> Value_expr)
	    |)

     'rule' Simplify(ax_infix(P,LVE1,and,LVE2,PE) -> Value_expr):
	    Simplify(LVE1 -> LVE3)
	    Simplify(LVE2 -> LVE4)
	    (|
	      where(LVE3-> literal_expr(P1,bool_true))
	      Simplify(LVE4 -> Value_expr)
	    ||
	      where(LVE3-> literal_expr(P1,bool_false))
	      where(literal_expr(P,bool_false) -> Value_expr)
	    ||
	      where(LVE3-> no_val)
	      where(LVE4 -> Value_expr)
	    ||
	      where(LVE4-> literal_expr(P1,bool_true))
	      Simplify(LVE3 -> Value_expr)
	    ||
	      where(LVE4-> literal_expr(P1,bool_false))
	      where(literal_expr(P,bool_false) -> Value_expr)
	    ||
	      where(LVE4-> no_val)
	      where(LVE3 -> Value_expr)
	    ||
	      where(ax_infix(P,LVE3,and,LVE4,PE) -> Value_expr)
	    |)

     'rule' Simplify(ax_infix(P,LVE1,implies,LVE2,PE) -> Value_expr):
	    Simplify(LVE1 -> LVE3)
	    Simplify(LVE2 -> LVE4)
	    (|
	      where(LVE3-> literal_expr(P1,bool_true))
	      Simplify(LVE4 -> Value_expr)
	    ||
	      where(LVE3-> literal_expr(P1,bool_false))
	      where(literal_expr(P,bool_true) -> Value_expr)
	    ||
	      where(LVE4-> literal_expr(P1,bool_true))
	      where(literal_expr(P,bool_true) -> Value_expr)
	    ||
	      where(LVE4-> literal_expr(P1,bool_false))
	      Simplify(ax_prefix(P,not,LVE3) -> Value_expr)
	    ||
	      where(LVE4-> no_val)
	      where(no_val -> Value_expr)
	    ||
	      where(ax_infix(P,LVE3,implies,LVE4,PE) -> Value_expr)
	    |)

     'rule' Simplify(equivalence(P,LVE1,LVE2,nil) -> Value_expr):
	    Simplify(LVE1 -> LVE3)
	    Simplify(LVE2 -> LVE4)
	    (|
	      eq(LVE3, LVE4)
	      where(literal_expr(P,bool_true) -> Value_expr)
	    ||
	      where(LVE3-> literal_expr(P1,bool_true))
	      where(LVE4-> literal_expr(P2,bool_false))
	      where(literal_expr(P,bool_false) -> Value_expr)
	    ||
	      where(LVE3-> literal_expr(P1,bool_false))
	      where(LVE4-> literal_expr(P2,bool_true))
	      where(literal_expr(P,bool_false) -> Value_expr)
	    ||
	      (| where(LVE3 -> no_val) || where(LVE4 -> no_val) |)
	      where(no_val -> Value_expr)
	    ||
	      where(equivalence(P,LVE3,LVE4,nil) -> Value_expr)
	    |)

     'rule' Simplify(quantified(P,all,Typings,restriction(_,LVE)) -> Value_expr):
	    Simplify(LVE -> LVE1)
	    (|
	      where(LVE1-> literal_expr(P1,bool_true))
	      where(literal_expr(P,bool_true) -> Value_expr)
	    ||
	      where(LVE1 -> no_val)
	      where(no_val -> Value_expr)
	    ||
	      where(quantified(P,all,Typings,restriction(P,LVE1)) -> Value_expr)
	    |)

     'rule' Simplify(quantified(P,exists,Typings,restriction(_,LVE)) -> Value_expr):
	    Simplify(LVE -> LVE1)
	    (|
	      where(LVE1-> literal_expr(P1,bool_false))
	      where(literal_expr(P,bool_false) -> Value_expr)
	    ||
	      where(LVE1 -> no_val)
	      where(no_val -> Value_expr)
	    ||
	      where(quantified(P,exists,Typings,restriction(P,LVE1)) -> Value_expr)
	    |)

     'rule' Simplify(quantified(P,exists1,Typings,restriction(_,LVE)) -> Value_expr):
	    Simplify(LVE -> LVE1)
	    (|
	      where(LVE1-> literal_expr(P1,bool_false))
	      where(literal_expr(P,bool_false) -> Value_expr)
	    ||
	      where(LVE1 -> no_val)
	      where(no_val -> Value_expr)
	    ||
	      where(quantified(P,exists1,Typings,restriction(P,LVE1)) -> Value_expr)
	    |)

     'rule' Simplify(always(P, VE) -> Value_expr):
	    Simplify(VE -> VE1)
	    (|
	      (| where(VE1 -> no_val) ||
		 where(VE1 -> literal_expr(P1,bool_true)) |)
	      where(no_val -> Value_expr)
	    ||
	      where(always(P,VE1) -> Value_expr)
	    |)

     'rule' Simplify(let_expr(P,Defs,LVE) -> Value_expr):
	    Simplify(LVE -> LVE1)
	    (|
	      where(LVE1-> no_val)
	      where(no_val -> Value_expr)
	    ||
	      where(let_expr(P,Defs,LVE1) -> Value_expr)
	    |)

     'rule' Simplify(class_scope_expr(P,C,VE) -> Value_expr):
	    Simplify(VE -> VE1)
	    (|
	      (| where(VE1 -> no_val) ||
		 where(VE1 -> literal_expr(P1,bool_true)) |)
	      where(no_val -> Value_expr)
	    ||
	      where(class_scope_expr(P,C,VE1) -> Value_expr)
	    |)

     'rule' Simplify(bracket(_, bracket(P, LVE)) -> Value_expr):
	    Simplify(bracket(P, LVE) -> Value_expr)

     'rule' Simplify(bracket(_, let_expr(P,Defs,LVE)) -> Value_expr):
	    Simplify(let_expr(P,Defs,LVE) -> Value_expr) 

     'rule' Simplify(bracket(P,LVE) -> Value_expr):
	    Simplify(LVE -> LVE1)
	    (|
	      where(LVE1-> literal_expr(P1,bool_true))
	      where(literal_expr(P,bool_true) -> Value_expr)
	    ||
	      where(LVE1-> literal_expr(P1,bool_false))
	      where(literal_expr(P,bool_false) -> Value_expr)
	    ||
	      where(LVE1 -> no_val)
	      where(no_val -> Value_expr)
	    ||
	      (|
		(| where(LVE1 -> bracket(_,_)) ||
		   where(LVE1 -> let_expr(_,_,_)) |)
		where(LVE1 -> Value_expr)
	      ||
		where(VALUE_EXPR'bracket(P,LVE1) -> Value_expr)
	      |)
	    |)

     'rule' Simplify(cc_expr(_,_,_,no_val) -> no_val):

     'rule' Simplify(LVE -> LVE):


----------------------------------------------------------------
-- Generate confidence conditions
----------------------------------------------------------------

'action' Generate(CCNEEDED, POS, VALUE_DEFINITION, ASSUMPTIONS)

  'rule' Generate(CCneeded, P, VALDEF, As):
	 (|
	   where(CCneeded -> ccsubtype(subtype(Typing,Restriction)))
	   Not_empty(subtype(Typing,Restriction) -> Val_expr1)
	   where("subtype not empty" -> STR)	     
	 ||
	   where(CCneeded -> ccvaluedef(Val_def))
	   Def_value(Val_def -> Val_expr1, STR)
	 ||
	   where(CCneeded -> ccprecond(PC))
	   Check_precond_wanted(PC -> Val_expr1, STR)
	 ||
	   where(CCneeded -> ccvariabledef(single(P1,Id,T,initial(Val))))
	   Isin_subtype(Val, T -> Val_expr1)
	   where("initial value in subtype" -> STR)
	 ||
	   where(CCneeded -> ccassignment(ass_occ(P1,Id,Q,Val)))
	   Id'Type -> T	  
	   Isin_subtype(Val, T -> Val_expr1)
	   where("assigned value in subtype" -> STR)
	 ||
	   where(CCneeded -> ccoutput(output_occ(P1,Id,Q,Val)))
	   Id'Type -> T	  
	   Isin_subtype(Val, T -> Val_expr1)
	   where("output value in subtype" -> STR)
	 ||
	   where(CCneeded -> ccdisamb(disamb(P1,Val,T)))
	   Isin_subtype(Val, T -> Val_expr1)
	   where("value in subtype" -> STR)
	 ||
	   where(CCneeded -> ccapplication(Appl))
	   Application(Appl, VALDEF -> Val_expr1)	  
	   where("application arguments and/or precondition" -> STR)
	 ||
	   where(CCneeded -> ccconcurrent(concurrent(P1, L, R)))
	   Assignment_disjoint(P1, L, R -> Val_expr1)	      
	   where("concurrent expressions should be assignment-disjoint" -> STR)
	 ||
	   where(CCneeded -> ccenummap(enum_map(P1,Pairs)))
	   Map_pairs(P1, Pairs -> Val_expr1)	     
	   where("domain values different" -> STR)
	 ||
	   where(CCneeded -> ccobjappl(obj_appl(P1, Parms, T)))
	   Isin_subtype(product(P1, Parms), T -> Val_expr1)
	   where("object array arguments" -> STR)
	 ||
	   where(CCneeded -> ccimplementation(scoped_conditions(P1,C,V)))
	   where(class_scope_expr(P1,C,V) -> Val_expr1)
	   where("implementation conditions:" -> STR)
	 ||
	   where(CCneeded -> ccimplementation(conditions(P1,V)))
	   where(V -> Val_expr1)
	   where("implementation conditions:" -> STR)
	 ||
	   where(CCneeded -> ccimplementation(formal_actual_conditions(P1,V)))
	   where(V -> Val_expr1)
	   where("actual parameter class implements formal parameter class:" -> STR)
	 ||
	   where(CCneeded -> ccpatternmatch(pattern_match(P1,V)))
	   where(V -> Val_expr1)
	   where("pattern matches expression:" -> STR)
	 ||
	   where(CCneeded -> cccases(cases(P1,V)))
	   where(V -> Val_expr1)
	   where("cases complete:" -> STR)
	 ||
	   where(no_val -> Val_expr1)
	   where("" -> STR)
	 |)
	 Simplify(Val_expr1 -> Val_expr2)
	 (|
	   where(Val_expr2 -> literal_expr(P3,bool_true))
	 ||
	   where(Val_expr2 -> no_val)
	 ||
	   CcWanted()
	   [|
	     PccWanted()
	     Putstdmsg("-- ")
	   |]
	   Putcc(P)
	   Putstdmsg("-- ")
	   Putstdmsg(STR)
	   -- no need for Putstdnl as pretty printer generates initial
	   -- new line for a value expression
	   PpLength(-> N)
	   (|
	     PccWanted()
	     -- just print for now TODO
	     Insert_assumptions(As, Val_expr2 -> Val_expr3)
	     Pretty_print_value(Val_expr3, N)
	     Putstdnl()
	   ||
	     Pretty_print_value(Val_expr2, N)
	     -- insert a blank line
	     Putstdnl()
	   |)
	 ||
	   Insert_assumptions(As, Val_expr2 -> Val_expr3)
	   AddCcVar(Val_expr3) -- store for PVS translation
	 |)

'action' Insert_assumptions(ASSUMPTIONS, VALUE_EXPR -> VALUE_EXPR)

  'rule' Insert_assumptions(list(A, As), V -> V2):
	 -- first assumption is innermost
	 Insert_assumption(A, V -> V1)
	 Insert_assumptions(As, V1 -> V2)

  'rule' Insert_assumptions(nil, V -> V):

'action' Insert_assumption(ASSUMPTION, VALUE_EXPR -> VALUE_EXPR)

  'rule' Insert_assumption(typings(nil), V -> V):

  'rule' Insert_assumption(typings(TPS), V -> quantified(P, all, TPS, restriction(P, V))):
	 DefaultPos(-> P)

  'rule' Insert_assumption(lets(nil), V -> V):

  'rule' Insert_assumption(lets(DS), V -> let_expr(P, DS, V)):
	 DefaultPos(-> P)

  'rule' Insert_assumption(assumption(C), V -> V1):
	 Simplify(C -> C1)
	 (|
	   (| eq(C1,no_val) || where(C1 -> literal_expr(_,bool_true)) |)
	   where(V -> V1)
	 ||
	   DefaultPos(-> P)
	   where(ax_infix(P,C1,implies,V,P) -> V1)
	 |)

  'rule' Insert_assumption(post_ass(E), V -> V1):
	 DefaultPos(-> P)
	 where(VALUE_EXPR'post(P, E, post_cond(P, nil, V), nil) -> V1)

  'rule' Insert_assumption(class(CL,CE), V -> env_class_scope(P, CL, CE, V)):
	 DefaultPos(-> P)

----------------------------------------------------------------
-- Confidence conditions for value definitions
----------------------------------------------------------------

'action' Def_value(CCVALUEDEF -> VALUE_EXPR, STRING)

  'rule' Def_value(exp_val(P,TP,_) -> Value_expr, ""):
-- not used. instead, resolve exp_val(P,single(_,B,T),V) to some form
-- of disamb(P,V,T), then generate confidence condition for
-- disambiguation expression.
	 -- first alternative deals with single binding 
	 -- (for multiple bindings the definitions are repeated
	 --  so only need to check first one)
	 (|
	   where(TP -> single(_,single(P1,Id),_))
	   Get_current_top_values(-> VE)
	   Select_id_by_pos(P1, VE -> value_id(I))
	   I'Def -> expl_val(disamb(_,Val,T1), _)	  
	   Isin_subtype(Val,T1 -> Value_expr)
	 ||
	   where(TP -> single(_, product(_, list(single(P1,Id),BS)),_))	  
	   Get_current_top_values(-> VE)
	   Select_id_by_pos(P1, VE -> value_id(I))
	   I'Def -> expl_val(let_expr(P3, LDS, val_occ(P4, ID, _)), _)
	   where(LDS -> list(explicit(_, binding(_, product(_, BS1)), disamb(_,V1,T1)), nil))
	   Isin_subtype(V1,T1 -> Value_expr)
	 |)

  'rule' Def_value(imp_val(P,TP,Restric) -> Value_expr, "possible value in subtype"):
	 where(quantified(P,exists,list(TP,nil),Restric) -> Value_expr) 

  'rule' Def_value(exp_fun(P,single(_,single(PF,F),_), _, _, _, _) 
		   -> Value_expr, Str):
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(PF, VE -> value_id(I))
	 I'Type -> T				-- resolved version of type
	 I'Def -> expl_fun(PARMS, V, POST, PRE, _, _)	-- resolved definition
	 Make_typings(PARMS, T, readonly -> TPS, T2, Readonly)
	 (|
	   Maximal(T2)
	   where(no_val -> Value_expr4)
	 ||
	   Isin_subtype(V,T2 -> Cond)
	   Simplify(Cond -> Cond1)
	   (|
	     (| eq(Cond1,no_val) ||
		where(Cond1 -> literal_expr(_,bool_true)) |)
	     where(no_val -> Value_expr4)
	   ||
	     (|
	       eq(Readonly, readonly)
	       where(Cond1 -> Value_expr1)
	     ||
	       string_to_id("x_" -> X)
	       -- get best type for V
	       Type_of_val(V, T2 -> T3)
	       New_value_id(P, id_op(X) -> I1)
	       I1'Type <- T3
	       Isin_subtype(val_occ(P, I1, nil), T2 -> Value_expr0)
	       where(
		 equivalence(
		   P,
		   let_expr(
		     P,
		     list(explicit(P, binding(P,single(P,id_op(X))),V), nil),
		     Value_expr0),
		   let_expr(
		     P,
		     list(explicit(P, binding(P,single(P,id_op(X))),V), nil),
		     literal_expr(P,bool_true)),
		   nil)
		 -> Value_expr1)
	     |)
	     (|
	       where(PRE -> pre_cond(_,Value_expr2))
	       where(ax_infix(P,
			     equivalence(P,Value_expr2,literal_expr(P,bool_true),nil),
			     implies,
			     Value_expr1,P)
		    -> Value_expr3) 
	     ||
	       where(Value_expr1 -> Value_expr3)
	     |)
	     (|
	       eq(TPS, nil)
	       where(Value_expr3 -> Value_expr4)
	     ||
	       where(quantified(P,all,TPS,restriction(P,Value_expr3))
		   -> Value_expr4)
	     |)
	   |)
	 |)
	 (|
	   where(POST -> post(VP))
	   Formals_to_actuals(PARMS, T -> ACTS)
	   Make_application(P, I, ACTS -> APP)
	   where(VALUE_EXPR'post(P, APP, VP, PRE) -> Value_expr5)
	   (|
	     eq(Value_expr4,no_val)
	     where(Value_expr5 -> Value_expr)
	     where("function satisfies postcondition" -> Str)
	   ||
	     where(ax_infix(P, bracket(P, Value_expr4),
			       and,
			       bracket(P, Value_expr5), P) -> Value_expr)
	     where("function result in subtype and satisfies postcondition" -> Str)
	   |)
	 ||
	   (|
	     eq(Value_expr4,no_val)
	     where(no_val -> Value_expr)
	     where("" -> Str)
	   ||
	     where(Value_expr4 -> Value_expr)
	     where("function result in subtype" -> Str)
	   |)
	 |)

  'rule' Def_value(imp_fun(P, single(_,single(PF,F),_), _, _, _)
		   -> Value_expr, "possible function result in subtype"):
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(PF, VE -> value_id(I))
	 I'Type -> T				-- resolved version of type
	 I'Def -> impl_fun(PARMS, post_cond(_,R,VE1), PRE, _)
						       -- resolved definition
	 Make_typings(PARMS, T, readonly -> TPS, T2, Readonly)
	 (|
	   eq(Readonly, nil)
	   -- TODO (complicated by variables, esp pre_names)
	   where(no_val -> Value_expr)
	 ||
	   where(R -> result(_,B))
	   where(
	     quantified(
	       P,
	       exists,
	       list(single(P,B,T2),nil),
	       restriction(P,VE1))
	     -> Value_expr1)
	   (|
	     where(PRE -> pre_cond(_,Value_expr2))
	     where(ax_infix(P,
			    equivalence(P,Value_expr2,literal_expr(P,bool_true),nil),
			    implies,
			    Value_expr1,P)
		   -> Value_expr3) 
	   ||
	     where(Value_expr1 -> Value_expr3)
	   |)
	   (|
	     eq(TPS, nil)
	     where(Value_expr3 -> Value_expr)
	   ||
	     where(quantified(P,all,TPS,restriction(P,Value_expr3))
		 -> Value_expr)
	   |)
	 ||
	   -- eq(R, nil): nothing to do in readonly case
	   where(no_val -> Value_expr)
	 |)

'action' Make_typings(FORMAL_FUNCTION_PARAMETERS, TYPE_EXPR, READONLY
		     -> TYPINGS, TYPE_EXPR, READONLY)

 'rule' Make_typings(list(form_parm(P,BS),PARMS), FT, RO -> TPS, T, RO1):
	Make_function_type(FT -> fun(D,_,result(R,_,WR,IN,OUT)))
	(|
	  where(BS -> list(B, nil))
	  where(TYPING'single(P, B, D) -> TP)
	||
	  where(TYPING'single(P, product(P, BS), D) -> TP)
	|)
	(|
	  Read_only(RO, WR, IN, OUT)
	  where(readonly -> RO2)
	||
	  where(READONLY'nil -> RO2)
	|)
	Make_typings(PARMS, R, RO2 -> TPS1, T, RO1)
	(|
	  eq(BS, nil)
	  -- Unit type binding - ignore
	  where(TPS1 -> TPS)
	||
	  where(TYPINGS'list(TP, TPS1) -> TPS)
	|)

 'rule' Make_typings(nil, T, RO -> nil, T, RO):

-- debug
--   'rule' Make_typings(PARMS, T, RO -> nil, T, RO):
-- print(PARMS)
-- print(T)
-- print(RO)

'condition' Read_only(READONLY, ACCESSES, ACCESSES, ACCESSES)

  'rule' Read_only(readonly, nil, nil, nil)

----------------------------------------------------------------
-- Confidence conditions for preconditions
----------------------------------------------------------------

'action' Check_precond_wanted(CCPRECOND -> VALUE_EXPR, STRING)

  'rule' Check_precond_wanted(precond(P, T, PARMS, PRE) -> V, STR):
	 Function_arrow(T, PARMS -> ARR)
	 (|
	   eq(ARR, total)
	   ne(PRE, nil)
	   where(literal_expr(P, bool_false) -> V)
	   where("total function with precondition" -> STR)
	 ||
	   eq(ARR, partial)
	   eq(PRE, nil)
	   where(literal_expr(P, bool_false) -> V)
	   where("partial function without precondition" -> STR)
	 ||
	   where(no_val -> V)
	   where("" -> STR)
	 |)

'action' Function_arrow(TYPE_EXPR, FORMAL_FUNCTION_PARAMETERS -> FUNCTION_ARROW)

  'rule' Function_arrow(T, list(_, PARMS) -> ARR):
	 Make_function_type(T -> fun(_, ARR1, result(R,_,_,_,_)))
	 (|
	   eq(PARMS, nil)
	   where(ARR1 -> ARR)
	 ||
	   Function_arrow(R, PARMS -> ARR)
	 |)

----------------------------------------------------------------
-- Confidence conditions for list, map, function applications
----------------------------------------------------------------

'action' Application(CCAPPLICATION, VALUE_DEFINITION -> VALUE_EXPR)

  'rule' Application(application(P,FUN,ARGS), VALDEF -> Value_expr):
         (|
	   where(FUN -> val_occ(_, I, _))
	   I'Type -> FT
	   Args_in_domains(FUN, FT, ARGS -> Value_expr1)
	   -- generate for precondition
	   (|
	     (| I'Def -> expl_fun(PARMS,_,_,PRE,_,_) ||
		I'Def -> impl_fun(PARMS,_,PRE,_) |)
	     where(PRE -> pre_cond(_,VAL))
	     -- may be more actuals than formals
	     -- but need at least as many
	     Enough_args(PARMS, ARGS)
	     Make_let_defs(PARMS, ARGS -> LDS)
	     (|
	       eq(LDS, nil)
	       where(VAL -> Value_expr2)
	     ||
	       where(let_expr(P, LDS, VAL) -> Value_expr2)
	     |)
	     where(ax_infix(P,Value_expr1,and,Value_expr2,P) -> Value_expr)
	   ||
	     where(Value_expr1 -> Value_expr)
	   |)
	 ||
	   (|
	     where(FUN -> var_occ(_, I1, _))
	     I1'Type -> FT
	   ||
	     where(FUN -> pre_occ(_, I2, _))
	     I2'Type -> FT
	   ||
	     where(FUN -> input_occ(_, I3, _))
	     I3'Type -> FT
	   |)
	   Args_in_domains(FUN, FT, ARGS -> Value_expr)
	 ||
	   where(no_val -> Value_expr)
	 |)

  'rule' Application(prefix_occ(P,I,_,VAL), expl_fun(PARMS,V, _, pre_cond(_,PRE), _, _)
		     -> Value_expr):
	 where(PARMS -> list(form_parm(_,list(single(_,ID),nil)),nil))
	 where(let_expr(P,list(explicit(P,binding(P,single(P,ID)),VAL),nil),PRE) 
	       -> Value_expr) 

  'rule' Application(prefix_occ(P,I,_,VAL), no_def  -> no_val):

  'rule' Application(infix_occ(P,V1,I,_,V2), VALDEF -> Value_expr):
	 (|
	   where(VALDEF -> no_def)   
	   where(no_val -> Value_expr)	    
	 ||
	   where(VALDEF -> expl_fun(PARMS,V,_,pre_cond(_,PRE),_,_))
	   where(PARMS -> list(form_parm(_,list(B1,nil)),list(form_parm(_,list(B2,nil)),nil)))
	   where(let_expr(P,list(explicit(P,binding(P,B1),V1),list(explicit(P,binding(P,B2),V2),nil)),PRE) 
		 -> Value_expr)
	 |) 

'action' Args_in_domains(VALUE_EXPR, TYPE_EXPR, ACTUAL_FUNCTION_PARAMETERS -> VALUE_EXPR)

  'rule' Args_in_domains(V, T, list(fun_arg(P, VS), ARGS) -> Value_expr):
	 (|
	   where(VS -> list(V1, nil))
	 ||
	   where(VALUE_EXPR'product(P, VS) -> V1)
	 |)
	 (| -- list
	   Make_list_type(T -> fin_list(T1))
	   Id_of_isin_set -> Iisin
	   Id_of_inds -> Iinds
	   where(VALUE_EXPR'infix_occ(P,V1,Iisin,nil,prefix_occ(P,Iinds,nil,V)) -> Value_expr1)
	 ||
	   Make_list_type(T -> infin_list(T1))
	   string_to_id("0" -> Zero)
	   Id_of_gt_int -> Igt
	   where(VALUE_EXPR'infix_occ(P,V1,Igt,nil,literal_expr(P,int(Zero))) -> Value_expr1)
	 || -- map
	   (| Make_map_type(T -> fin_map(_,T1)) ||
	      Make_map_type(T -> infin_map(_,T1)) |)
	   Id_of_isin_map -> Iisin
	   where(VALUE_EXPR'infix_occ(P,V1,Iisin,nil,V) -> Value_expr1)
	 || -- function
	   Make_function_type(T -> fun(T0, _, result(T1,_,_,_,_)))
	   Isin_subtype(V1, T0 -> Value_expr1)
	 |)
	 (|
	   ne(ARGS, nil)
	   where(VALUE_EXPR'application(P, V, list(fun_arg(P, VS), nil)) -> V2)
	   Args_in_domains(V2, T1, ARGS -> Value_expr2)
	   where(ax_infix(P,Value_expr1,and,Value_expr2,P) -> Value_expr)
	 ||
	   where(Value_expr1 -> Value_expr)
	 |)

'action' Make_let_defs(FORMAL_FUNCTION_PARAMETERS, ACTUAL_FUNCTION_PARAMETERS -> LET_DEFS)

  'rule' Make_let_defs(list(form_parm(P, nil), PARMS), list(_, ARGS) -> LDS):
	 Make_let_defs(PARMS, ARGS -> LDS)

  'rule' Make_let_defs(list(form_parm(P, BS), PARMS),
		       list(fun_arg(P1, VS), ARGS) -> list(LD, LDS)): 
	 (|
	   where(BS -> list(B, nil))
	 ||
	   where(BINDING'product(P, BS) -> B)
	 |)
	 (|
	   where(VS -> list(V, nil))
	 ||
	   where(VALUE_EXPR'product(P1, VS) -> V)
	 |)
	 where(explicit(P, binding(P, B), V) -> LD)
	 Make_let_defs(PARMS, ARGS -> LDS)

  'rule' Make_let_defs(nil, _ -> nil):

'condition' Enough_args(FORMAL_FUNCTION_PARAMETERS, ACTUAL_FUNCTION_PARAMETERS)

  'rule' Enough_args(list(_,PARMS), list(_, ARGS)):
	 Enough_args(PARMS, ARGS)

  'rule' Enough_args(nil, _):

--------------------------------------------------------------------
-- Disjointness of enumerated map domains
--------------------------------------------------------------------

'action' Map_pairs(POS, VALUE_EXPR_PAIRS -> VALUE_EXPR)

  'rule' Map_pairs(_, list(PR, nil) -> no_val):

  'rule' Map_pairs(P, list(pair(L,_), PRS) -> ax_infix(P, V1, and, V2, P)):
	 Not_in_dom(P, L, PRS -> V1)
	 Map_pairs(P, PRS -> V2)

'action' Not_in_dom(POS, VALUE_EXPR, VALUE_EXPR_PAIRS -> VALUE_EXPR)

  'rule' Not_in_dom(P, V, list(pair(L,_), nil) -> infix_occ(P, V, Ineq, nil, L)):
	 Id_of_neq -> Ineq

  'rule' Not_in_dom(P, V, list(pair(L,_), PRS) -> ax_infix(P, V1, and, V2, P)):
	 Id_of_neq -> Ineq
	 where(VALUE_EXPR'infix_occ(P, V, Ineq, nil, L) -> V1)
	 Not_in_dom(P, V, PRS -> V2)

--------------------------------------------------------------------
-- Assignment_disjointness of concurrent expressions
--------------------------------------------------------------------

'action' Assignment_disjoint(POS, VALUE_EXPR, VALUE_EXPR -> VALUE_EXPR)

  'rule' Assignment_disjoint(P, L, R -> ax_infix(P, V1, and, V2, P)):
	 Make_results(L -> list(result(_,RD1,WR1,_,_),_))
	 Make_results(R -> list(result(_,RD2,WR2,_,_),_))
	 -- Concat_accs will ensure first arguments are flattened
	 -- so call twice to ensure all are
	 Concat_accs(WR1, nil -> WR11)
	 Concat_accs(RD1, WR11 -> ACC1)
	 Concat_accs(WR2, nil -> WR21)
	 Concat_accs(RD2, WR21 -> ACC2)
	 Access_intersection(WR11, ACC2 -> ACCS1)
	 Access_intersection(WR21, ACC1 -> ACCS2)
-- debug
-- Putmsg("Write accesses of first: ")
-- Print_accesses(WR11)
-- Putnl()
-- Putmsg("Read/write accesses of first: ")
-- Print_accesses(ACC1)
-- Putnl()
-- Putmsg("Write accesses of second: ")
-- Print_accesses(WR21)
-- Putnl()
-- Putmsg("Read/write accesses of second: ")
-- Print_accesses(ACC2)
-- Putnl()
-- Putmsg("First-second intersection: ")
-- Print_accesses(ACCS1)
-- Putnl()
-- Putmsg("Second-first intersection: ")
-- Print_accesses(ACCS2)
-- Putnl()
	 (|
	   where(ACCS1 -> list(_,_))
	   Disjoint_condition(P, ACCS1, ACC2 -> V11)
	   Simplify(V11 -> V12)
	   Accesses_to_string(ACCS1 -> S1)
	   Concatenate3("first expression may write to ", S1,
			" which may be accessed by second unless" -> STR1)
	   where(cc_expr(no_pos, STR1, nil, V12) -> V1)
	 ||
	   where(no_val -> V1)
	 |)
	 (|
	   where(ACCS2 -> list(_,_))
	   Disjoint_condition(P, ACCS2, ACC1 -> V21)
	   Simplify(V21 -> V22)
	   Accesses_to_string(ACCS2 -> S2)
	   Concatenate3("second expression may write to ", S2,
			" which may be accessed by first unless" -> STR2)
	   where(cc_expr(no_pos, STR2, nil, V22) -> V2)
	 ||
	   where(no_val -> V2)
	 |)

-- assumes all accesses are flattened: no enumerated accesses
'action' Access_intersection(ACCESSES, ACCESSES -> ACCESSES)

  'rule' Access_intersection(list(ACC, ACCS1), ACCS2 -> ACCS):
	 Access_intersection(ACCS1, ACCS2 -> ACCS3)
	 (|
	   Access_overlaps(ACC, ACCS2)
	   where(ACCESSES'list(ACC, ACCS3) -> ACCS)
	 ||
	   where(ACCS3 -> ACCS)
	 |)

  'rule' Access_intersection(nil, _ -> nil):

-- assumes first parameter has no enumerated accesses 
'condition' Access_overlaps(ACCESS, ACCESSES)

  'rule' Access_overlaps(A, list(A1, AS1)):
	 (| Access_overlaps1(A, A1) || Access_overlaps(A, AS1) |)

'condition' Access_overlaps1(ACCESS, ACCESS)

  'rule' Access_overlaps1(A, enumerated_access(_, AS)):
	 Access_overlaps(A, AS)

  'rule' Access_overlaps1(_, completed_access(_, nil)):

  'rule' Access_overlaps1(completed_access(_, qualification(Obj)), completed_access(_, qualification(Obj1))):
	 Id_of_object(Obj -> I)
	 Id_of_object(Obj1 -> I1)
	 eq(I,I1)

  'rule' Access_overlaps1(comprehended_access(_, A, _), comprehended_access(_, A1, _)):
	 Access_overlaps1(A, A1)

  'rule' Access_overlaps1(variable(_, I, _), variable(_, I1, _)):
	 eq(I,I1)

  'rule' Access_overlaps1(channel(_, I, _), channel(_, I1, _)):
	 eq(I,I1)

  'rule' Access_overlaps1(variable(_, _, qualification(Obj)), completed_access(_, qualification(Obj1))):
	 Id_of_object(Obj -> I)
	 Id_of_object(Obj1 -> I1)
	 eq(I,I1)

  'rule' Access_overlaps1(completed_access(_, qualification(Obj1)), variable(_, _, qualification(Obj))):
	 Id_of_object(Obj -> I)
	 Id_of_object(Obj1 -> I1)
	 eq(I,I1)

  'rule' Access_overlaps1(channel(_, _, qualification(Obj)), completed_access(_, qualification(Obj1))):
	 Id_of_object(Obj -> I)
	 Id_of_object(Obj1 -> I1)
	 eq(I,I1)
	 
  'rule' Access_overlaps1(completed_access(_, qualification(Obj1)), channel(_, _, qualification(Obj))):
	 Id_of_object(Obj -> I)
	 Id_of_object(Obj1 -> I1)
	 eq(I,I1)

-- assumes all accesses are flattened: no enumerated accesses
'action' Disjoint_condition(POS, ACCESSES, ACCESSES -> VALUE_EXPR)
-- TODO
-- nested array objects (only top level ones used at present)

  'rule' Disjoint_condition(P, list(A, AS), AS2 -> ax_infix(P, V1, and, V2, P)):
	 Disjoint_condition1(P, A, AS2 -> V1)
	 Disjoint_condition(P, AS, AS2 -> V2)

  'rule' Disjoint_condition(_, nil, _ -> no_val):

'action' Disjoint_condition1(POS, ACCESS, ACCESSES -> VALUE_EXPR)

  'rule' Disjoint_condition1(P, A1, list(A2, AS2) -> V):
	 Disjoint_condition1(P, A1, AS2 -> V2)	 
	 (|
	   Access_overlaps1(A1, A2)
	   Disjoint_condition2(P, A1, A2 -> V1)
	   where(ax_infix(P, V1, and, V2, P) -> V)
	 ||
	   where(V2 -> V)
	 |)

  'rule' Disjoint_condition1(_, _, nil -> no_val):

'action' Disjoint_condition2(POS, ACCESS, ACCESS -> VALUE_EXPR)

  'rule' Disjoint_condition2(_, completed_access(P, nil), _ -> literal_expr(P, bool_false)):

  'rule' Disjoint_condition2(_, _, completed_access(P, nil) -> literal_expr(P, bool_false)):

  'rule' Disjoint_condition2(P, A1, A2 -> V):
	 Indexes_of_access(P, 0, A1 -> V1)
	 Indexes_of_access(P, 0, A2 -> V2)
	 Disjoint_indexes(P, V1, V2 -> V)

'action' Indexes_of_access(POS, INT, ACCESS -> VALUE_EXPR)

  'rule' Indexes_of_access(_, _, completed_access(P, nil) -> literal_expr(P, bool_true)):

  'rule' Indexes_of_access(_, N, completed_access(P, qualification(Obj)) -> V):
	 Indexes_of_object(P, N, Obj -> V)

  'rule' Indexes_of_access(_, N, comprehended_access(P, A, set_limit(P1, TPS, R)) -> V):
	 Indexes_of_access(P, N+1, A -> V1)
	 (|
	   where(V1 -> literal_expr(_, bool_true))
	   Set_from_limitation(set_limit(P1, TPS, R) -> V)
	 ||
	   where(V1 -> enum_set(_, list(V2, nil)))
	   where(comp_set(P, V2, set_limit(P1, TPS, R)) -> V)
	 ||
	   Make_results(V1 -> RS)
	   (| where(RS -> list(result(fin_set(T1),_,_,_,_),_))
	   || where(RS -> list(result(infin_set(T1),_,_,_,_),_)) |)
	   Make_concatenation("x", N -> S)
	   string_to_id(S -> ID)
	   New_value_id(P, id_op(ID) -> I1)
	   [|
	     CPPWanted()
	     Localise_value_id(I1)
	   |]
	   I1'Type <- T1
	   where(TYPINGS'list(single(P, single(P, id_op(ID)), T1), nil) -> TPS1)
	   Id_of_isin_set -> Iisin
	   where(VALUE_EXPR'infix_occ(P, val_occ(P, I1, nil), Iisin, nil, V1) -> C2)
	   (|
	     where(R -> restriction(_, C1))
	     where(ax_infix(P, C1, and, C2, P) -> C)
	   ||
	     where(C2 -> C)
	   |)
	   where(restriction(P, quantified(P, exists, TPS, restriction(P, C))) -> R1)
	   where(set_limit(P, TPS1, R1) -> L1)
	   where(comp_set(P, val_occ(P, I1, nil), L1) -> V)
	 |) 

  'rule' Indexes_of_access(_, _, variable(P, _, nil) -> literal_expr(P, bool_true)):

  'rule' Indexes_of_access(_, N, variable(P, _, qualification(Obj)) -> V):
	 Indexes_of_object(P, N, Obj -> V)

'action' Indexes_of_accesses(POS, INT, ACCESSES -> VALUE_EXPR)

  'rule' Indexes_of_accesses(P, N, list(A, AS) -> V):
	 Indexes_of_access(P, N, A -> V1)
	 (|
	   where(V1 -> literal_expr(_, bool_true))
	   where(V1 -> V)
	 ||
	   Indexes_of_accesses(P, N, AS -> V2)
	   (|
	     where(V1 -> literal_expr(_, bool_false))
	     where(V2 -> V)
	   ||
	     where(V2 -> literal_expr(_, bool_true))
	     where(V2 -> V)
	   ||
	     where(V2 -> literal_expr(_, bool_false))
	     where(V1 -> V)
	   ||
	     Id_of_union_set -> Iunion
	     where(VALUE_EXPR'infix_occ(P, V1, Iunion, nil, V2) -> V)
	   |)
	 |)

  'rule' Indexes_of_accesses(P, _, nil -> literal_expr(P, bool_false)):

'action' Indexes_of_object(POS, INT, OBJECT_EXPR -> VALUE_EXPR)

  'rule' Indexes_of_object(P, N, obj_appl(Obj, Parms) -> enum_set(P,list(V, nil))):
	 (|
	   where(Parms -> list(V, nil))
	 ||
	   where(VALUE_EXPR'product(P, Parms) -> V)
	 |)

  'rule' Indexes_of_object(P, N, obj_array(TPS, Obj) -> V):
	 Indexes_of_object(P, N+1, Obj -> V1)
	 (|
	   where(V1 -> literal_expr(_, bool_true))
	   Set_from_limitation(set_limit(P, TPS, nil) -> V)
	 ||
	   where(V1 -> enum_set(_, list(V2, nil)))
	   where(comp_set(P, V2, set_limit(P, TPS, nil)) -> V)
	 ||
	   Make_results(V1 -> RS)
	   (| where(RS -> list(result(fin_set(T1),_,_,_,_),_))
	   || where(RS -> list(result(infin_set(T1),_,_,_,_),_)) |)
	   Make_concatenation("x", N -> S)
	   string_to_id(S -> ID)
	   New_value_id(P, id_op(ID) -> I1)
	   [|
	     CPPWanted()
	     Localise_value_id(I1)
	   |]
	   I1'Type <- T1
	   where(TYPINGS'list(single(P, single(P, id_op(ID)), T1), nil) -> TPS1)
	   Id_of_isin_set -> Iisin
	   where(VALUE_EXPR'infix_occ(P, val_occ(P, I1, nil), Iisin, nil, V1) -> C)
	   where(restriction(P, quantified(P, exists, TPS, restriction(P,C))) -> R1)
	   where(set_limit(P, TPS1, R1) -> L1)
	   where(comp_set(P, val_occ(P, I1, nil), L1) -> V)
	 |) 

  'rule' Indexes_of_object(P, N, obj_fit(Obj, _) -> V):
	 Indexes_of_object(P, N, Obj -> V)

  'rule' Indexes_of_object(_, _, obj_occ(P, _) -> literal_expr(P, bool_true)):

  'rule' Indexes_of_object(_, _, qual_occ(P, _, _) -> literal_expr(P, bool_true)):

'action' Set_from_limitation(SET_LIMITATION -> VALUE_EXPR)

  'rule' Set_from_limitation(set_limit(P, TPS, R) -> comp_set(P, V, set_limit(P, TPS, R))):
	 Typings_to_exprs(P, TPS -> VS)
	 (|
	   where(VS -> list(V, nil))
	 ||
	   where(VALUE_EXPR'product(P, VS) -> V)
	 |)

'action' Typings_to_exprs(POS, TYPINGS -> VALUE_EXPRS)

  'rule' Typings_to_exprs(P, list(TP, TPS) -> list(V, VS)):
	 Typing_to_expr(P, TP -> V)
	 Typings_to_exprs(P, TPS -> VS)

  'rule' Typings_to_exprs(_, nil -> nil):

'action' Typing_to_expr(POS, TYPING -> VALUE_EXPR)

  'rule' Typing_to_expr(P, single(_, B, T) -> V):
	 Binding_to_expr(B, T -> V)

  'rule' Typing_to_expr(P, multiple(_, BS, T) -> V):
	 Length_bs(BS -> N)
	 Make_product_type(T, N -> product(TS))
	 Bindings_to_exprs(BS, TS -> VS)
	 (|
	   where(VS -> list(V, nil))
	 ||
	   where(VALUE_EXPR'product(P, VS) -> V)
	 |)

'action' Disjoint_indexes(POS, VALUE_EXPR, VALUE_EXPR -> VALUE_EXPR)

  'rule' Disjoint_indexes(_, literal_expr(P, bool_true), _ -> literal_expr(P, bool_false)):

  'rule' Disjoint_indexes(_, _, literal_expr(P, bool_true) -> literal_expr(P, bool_false)):

  'rule' Disjoint_indexes(P, enum_set(_, list(V1,nil)), enum_set(_, list(V2,nil)) -> infix_occ(P, V1, Ineq, nil, V2)):
	 Id_of_neq -> Ineq

  'rule' Disjoint_indexes(P, enum_set(_, list(V1,nil)), V2 -> infix_occ(P, V1, Inotisin, nil, V2)):
	 Id_of_notisin_set -> Inotisin

  'rule' Disjoint_indexes(P, V2, enum_set(_, list(V1,nil)) -> infix_occ(P, V1, Inotisin, nil, V2)):
	 Id_of_notisin_set -> Inotisin

  'rule' Disjoint_indexes(P, V1, V2 -> infix_occ(P, infix_occ(P, V1, Iunion, nil, V2), Ieq, nil, enum_set(P, nil))):
	 Id_of_union_set -> Iunion
	 Id_of_eq -> Ieq

'action' Accesses_to_string(ACCESSES -> STRING)

  'rule' Accesses_to_string(list(ACC, nil) -> S):
	 Access_to_string(ACC -> S)

  'rule' Accesses_to_string(list(ACC, ACCS) -> S):
	 Access_to_string(ACC -> S1)
	 Accesses_to_string(ACCS -> S2)
	 Concatenate3(S1, ", ", S2 -> S)

'action' Access_to_string(ACCESS -> STRING)

  'rule' Access_to_string(free -> "free"):

  'rule' Access_to_string(enumerated_access(_, ACCS) -> S):
	 Accesses_to_string(ACCS -> S1)
	 Concatenate3("{", S1, "}" -> S)

  'rule' Access_to_string(completed_access(_, nil) -> "any"):

  'rule' Access_to_string(completed_access(_, qualification(Obj)) -> S):
	 Object_to_string(Obj -> S1)
	 Concatenate3(S1, ".any", "" -> S)

  'rule' Access_to_string(comprehended_access(_, ACC, _) -> S):
	 Access_to_string(ACC -> S1)
	 Concatenate3("{", S1, " | ... }" -> S)

  'rule' Access_to_string(variable(_, I, Q) -> S):
	 I'Ident -> Id
	 id_to_string(Id -> S1)
	 Qualify_string(Q, S1 -> S)
	 
  'rule' Access_to_string(channel(_, I, Q) -> S):
	 I'Ident -> Id
	 id_to_string(Id -> S1)
	 Qualify_string(Q, S1 -> S)

'action' Object_to_string(OBJECT_EXPR -> STRING)

  'rule' Object_to_string(obj_name(name(_, Id)) -> S):
	 Id_or_op_to_string(Id -> S)

  'rule' Object_to_string(obj_name(qual_name(_, Obj, Id)) -> S):
	 Object_to_string(Obj -> S1)
	 Id_or_op_to_string(Id -> S2)
	 Concatenate3(S1, ".", S2 -> S)

  'rule' Object_to_string(obj_appl(Obj, _) -> S):
	 Object_to_string(Obj -> S1)
	 Concatenate3(S1, "[.]", "" -> S)
	 
-- ignore arrays
  'rule' Object_to_string(obj_array(_, Obj) -> S):
	 Object_to_string(Obj -> S)

-- ignore fitting
  'rule' Object_to_string(obj_fit(Obj, _) -> S):
	 Object_to_string(Obj -> S)

  'rule' Object_to_string(obj_occ(_, I) -> S):
	 I'Ident -> Id
	 id_to_string(Id -> S)

  'rule' Object_to_string(qual_occ(_, Obj, I) -> S):
	 Object_to_string(Obj -> S1)
	 I'Ident -> Id
	 id_to_string(Id -> S2)
	 Concatenate3(S1, ".", S2 -> S)
	 
'action' Qualify_string(OPT_QUALIFICATION, STRING -> STRING)

  'rule' Qualify_string(qualification(Obj), S -> S1):
	 Object_to_string(Obj -> S2)
	 Concatenate3(S2, ".", S -> S1)

  'rule' Qualify_string(nil, S -> S):

--------------------------------------------------------------------
-- Go through the syntax tree
--------------------------------------------------------------------

'action' CCGenerate_class(CLASS, ASSUMPTIONS)

  'rule' CCGenerate_class(basic(DS), As):
	 CCGenerate_decls(DS, As)

  'rule' CCGenerate_class(instantiation(name(P,id_op(Id)), Objs), As):
	 Get_current_env(-> instantiation_env(PF, _))
	 Param_fit_to_object_fits(PF -> OBJF)
	 Param_fit_to_type_fits(PF -> TYPF)
	 Param_fit_to_imp_fit(PF, TYPF, OBJF -> IF)
-- debug
-- Putmsg("Fitting for ")
-- Print_id(Id)
-- Putmsg(" with params ")
-- Print_objects(Objs)
-- Putmsg(" is\n")
-- print(IF)
	 CCGenerate_instantiation_args(PF, IF)
	 -- class itself checked in Resolve_class

  'rule' CCGenerate_class(extend(CL1, CL2), As):
	 In_left
	 CCGenerate_class(CL1, As)
	 Left_right
	 CCGenerate_class(CL2, As)
	 Out_right

  'rule' CCGenerate_class(hide(H, C), As):
	 CCGenerate_class(C, As)

  'rule' CCGenerate_class(rename(R, C), As):
	 CCGenerate_class(C, As)

  'rule' CCGenerate_class(with(P,Obj, C), As):
	 CCGenerate_class(C, As)

'action' CCGenerate_decls(DECLS, ASSUMPTIONS)

  'rule' CCGenerate_decls(list(D, DS), As):
	 CCGenerate_decl(D, As)
	 CCGenerate_decls(DS, As)

  'rule' CCGenerate_decls(nil, _):

'action' CCGenerate_decl(DECL, ASSUMPTIONS)

  'rule' CCGenerate_decl(type_decl(P, Defs), As):
	 CCGenerate_type_defs(Defs, As)

  'rule' CCGenerate_decl(value_decl(P,Defs), As):
	 CCGenerate_value_defs(Defs, As)

  'rule' CCGenerate_decl(variable_decl(P,Defs), As):
	 CCGenerate_variable_defs(Defs, As)

  'rule' CCGenerate_decl(channel_decl(P,Defs), As):
	 CCGenerate_channel_defs(Defs, As)

  'rule' CCGenerate_decl(object_decl(P,Defs), As):
	 CCGenerate_object_defs(Defs, As)

  'rule' CCGenerate_decl(axiom_decl(P,Defs), As):
	 CCGenerate_axiom_defs(Defs, As)

  'rule' CCGenerate_decl(test_case_decl(P,Defs), As):
	 CCGenerate_test_case_defs(Defs, As)

--TODO
  'rule' CCGenerate_decl(trans_system_decl(_,_), _):

--TODO
  'rule' CCGenerate_decl(property_decl(_,_), _):

'action' CCGenerate_type_defs(TYPE_DEFS, ASSUMPTIONS)

  'rule' CCGenerate_type_defs(list(H,T), As):
	 CCGenerate_type_def(H, As)
	 CCGenerate_type_defs(T, As)

  'rule' CCGenerate_type_defs(nil, _):

'action' CCGenerate_type_def(TYPE_DEF, ASSUMPTIONS)

  'rule' CCGenerate_type_def(abbrev(_,Id,_), As):
	 Get_current_types(-> TE)
	 Lookup_env(Id, TE -> type_id(I))
	 I'Def -> abbreviation(T)
	 CCGenerate_type(T, As)

-- all others; nothing to do
  'rule' CCGenerate_type_def(_, _):

'action' CCGenerate_object_defs(OBJECT_DEFS, ASSUMPTIONS)

  'rule' CCGenerate_object_defs(list(H,T), As):
	 CCGenerate_object_def(H, As)
	 CCGenerate_object_defs(T, As)

  'rule' CCGenerate_object_defs(nil, _):

'action' CCGenerate_object_def(OBJECT_DEF, ASSUMPTIONS)

  'rule' CCGenerate_object_def(odef(P, Id, TS, CL), As):
	 Get_current_modules(-> ME)
	 Lookup_object_in_module(Id, ME -> object_id(I))
	 Current -> C
	 I'Param_env -> PCE
	 I'Env -> CE
	 Current <- current_env(CE,current_env(PCE, C))
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,list(nil,Paths))
	 CCGenerate_class(CL, As)
	 Current -> current_env(CE1,current_env(PCE1,C1))
--	 I'Env <- CE1
	 Current <- C1
	 Extend_paths <- Paths

'action' CCGenerate_value_defs(VALUE_DEFS, ASSUMPTIONS)

  'rule' CCGenerate_value_defs(list(D, DS), As):
	 CCGenerate_value_def(D, As)
	 CCGenerate_value_defs(DS, As)

  'rule' CCGenerate_value_defs(nil, _):

'action' CCGenerate_value_def(VALUE_DEF, ASSUMPTIONS)

  'rule' CCGenerate_value_def(typing(P, TP), As):
	 [| -- multiple typing TODO (seems very unlikely to occur)
	   where(TP -> single(P1, single(P2, Id),_))
	   Get_current_top_values(-> VE)
	   Select_id_by_pos(P2, VE -> value_id(I))
	   I'Type -> T1
	   CCGenerate_type(T1, As)
	 |]

  'rule' CCGenerate_value_def(exp_val(P, TP, V), As):
	 (|
	   where(TP -> single(P1, single(P2, Id),_))
	   Get_current_top_values(-> VE)
	   Select_id_by_pos(P2, VE -> value_id(I))
	   I'Type -> T1
	   -- not needed as explicit values are stored as disambiguations
--	   CCGenerate_type(T1, As)
	   I'Def -> expl_val(V1, _)
	   CCGenerate(V1, As)
	 ||
	   where(TP -> single(P1, product(P2, BS),_))
	   CCGenerate_multiple_expl_value_def(product(P2, BS), nil, As)
	 |)
	   -- not needed as explicit values are stored as disambiguations
-- cc
--	   Generate(ccvaluedef(exp_val(P, TP, V)),P,no_def,As)
-- endcc

  'rule' CCGenerate_value_def(imp_val(P, TP, _), As):
	 Defined_type_of_typing(TP -> T)  
	 Resolve_type(T -> TT)	     
	 (|
	   where(TP -> single(P1,single(P2,Id),_))
	   Get_current_top_values(-> VE)
	   Select_id_by_pos(P2, VE -> value_id(I))
	   I'Type -> T1
	   CCGenerate_type(T1, As)
	   I'Def -> impl_val(V1)
	   CCGenerate(V1, list(typings(list(TP, nil)), As))
	   where(TYPING'single(P1,single(P2,Id),TT) -> TP1)  
	   where(V1 -> V2)	 
	 ||
	   where(TP -> single(P1,product(P2,BS),_))
	   CCGenerate_multiple_impl_value_def(TP, product(P2, BS), nil, As -> V)
	   where(V -> list(V2,_)) 
	   where(TYPING'single(P1,product(P2,BS),TT) -> TP1)
	 |)
-- cc
	 Generate(ccvaluedef(imp_val(P, TP1, restriction(P, V2))),P,no_def,As)
-- endcc

  'rule' CCGenerate_value_def(exp_fun(P, single(_,single(P1,F),_), _, _, _, _, _), As):
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(P1, VE -> value_id(I))
	 I'Type -> T		   
	 CCGenerate_type(T, As)
	 I'Def -> expl_fun(PARMS, V, POST, PRE, _, _)
	 Parms_to_typings(PARMS, T -> TPS)
	 (|
	   where(PRE -> pre_cond(P2, C))
	 ||
	   where(literal_expr(P, bool_true) -> C)
	 |)
	 CCGenerate(V, list(assumption(C), list(typings(TPS), As)))
	 [|
	   where(POST -> post(post_cond(_,R,E)))
	   (|
	     where(R -> result(P3, B))
	     where(T -> fun(_, _, result(T1,_,_,_,_)))
	     where(TYPINGS'list(single(P3, B, T1), nil) -> TPSR)
	   ||
	     where(TYPINGS'nil -> TPSR)
	   |)
	   CCGenerate(E, list(typings(TPSR), list(assumption(C), list(typings(TPS), As))))
	 |]
	 Generate(ccprecond(precond(P, T, PARMS, PRE)),P,no_def,As)
	 [|
	   where(PRE -> pre_cond(_,_))
	   CCGenerate(C, list(typings(TPS), As))
	 |]  
-- cc
	 Generate(ccvaluedef(exp_fun(P, single(P1,single(P1,F),T), form_appl(P1,F,PARMS), V, nil, PRE)),P,no_def,As)
-- endcc

  'rule' CCGenerate_value_def(imp_fun(P, single(_,single(PF,F),_), _, _, _), As):
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(PF, VE -> value_id(I))
	 I'Type -> T		   
	 CCGenerate_type(T, As)
	 I'Def -> impl_fun(PARMS, post_cond(P1,R,E), PRE, _)
	 Parms_to_typings(PARMS, T -> TPS)
	 (|
	   where(PRE -> pre_cond(P2, C))
	 ||
	   where(literal_expr(P, bool_true) -> C)
	 |)
	 (|
	   where(R -> result(P3, B))
	   where(T -> fun(_, _, result(T1,_,_,_,_)))
	   where(TYPINGS'list(single(P3, B, T1), nil) -> TPSR)
	 ||
	   where(TYPINGS'nil -> TPSR)
	 |)
	 CCGenerate(E, list(typings(TPSR), list(assumption(C), list(typings(TPS), As))))
	 Generate(ccprecond(precond(P, T, PARMS, PRE)),P,no_def,As)
	 [|
	   where(PRE -> pre_cond(_,_))
	   CCGenerate(C, list(typings(TPS), As))
	 |]  
-- cc
	 Generate(ccvaluedef(imp_fun(P, single(P1,single(PF,F),T), form_appl(P1,F,PARMS), 
			     post_cond(P1,R,E), PRE)),
		  P,no_def,As)
-- endcc

-- debug
--   'rule' CCGenerate_value_def(V, As):
-- print(V)
-- Get_current_top_values(-> VE)
-- Print_value_envs(list(VE,nil))

'action' CCGenerate_multiple_expl_value_def(BINDING, FOUND, ASSUMPTIONS)

  'rule' CCGenerate_multiple_expl_value_def(single(P, Id), Found, As):
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(P, VE -> value_id(I))
	 I'Type -> T
	 CCGenerate_type(T, As)
	 [|
	   eq(Found, FOUND'nil)
	   I'Def -> expl_val(let_expr(P3, LDS, val_occ(P4, ID, _)), _)
	   where(LDS -> list(explicit(P1, binding(P2, product(P5, BS)), V1), nil))
	   CCGenerate(V1, As)
	 |]

  'rule' CCGenerate_multiple_expl_value_def(product(P, list(B, BS)), Found, As):
	 CCGenerate_multiple_expl_value_def(B, Found, As)
	 CCGenerate_multiple_expl_value_def(product(P, BS), found, As)

  'rule' CCGenerate_multiple_expl_value_def(product(_, nil), _, _)

'action' CCGenerate_multiple_impl_value_def(TYPING, BINDING, FOUND, ASSUMPTIONS -> VALUE_EXPRS)

  'rule' CCGenerate_multiple_impl_value_def(TP, single(P, Id), Found, As -> list(V1,nil)):
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(P, VE -> value_id(I))
	 I'Type -> T
	 CCGenerate_type(T, As)
	 I'Def -> impl_val(V1)
	 [|
	   eq(Found, FOUND'nil)
	   CCGenerate(V1, list(typings(list(TP, nil)), As))
	 |]

  'rule' CCGenerate_multiple_impl_value_def(TP, product(P, list(B, BS)), Found, As -> list(V, VS)):
	 CCGenerate_multiple_impl_value_def(TP, B, Found, As -> list(V,nil))
	 CCGenerate_multiple_impl_value_def(TP, product(P, BS), Found, As -> VS)

  'rule' CCGenerate_multiple_impl_value_def(_, product(_, nil), _, _ -> nil)

'action' CCGenerate_variable_defs(VARIABLE_DEFS, ASSUMPTIONS)

  'rule' CCGenerate_variable_defs(list(D, DS), As):
	 CCGenerate_variable_def(D, As)
	 CCGenerate_variable_defs(DS, As)

  'rule' CCGenerate_variable_defs(nil, _):

'action' CCGenerate_variable_def(VARIABLE_DEF, ASSUMPTIONS)

  'rule' CCGenerate_variable_def(single(P, Id, _, Init), As):
	 Get_current_variables(-> VARS)
	 Lookup_env_variable_id(Id, nil, VARS -> variable_id(I))
	 I'Type -> T
	 CCGenerate_type(T, As)
	 [|
	   I'Init -> initial(V)
	   CCGenerate(V, As)
-- cc
	   Generate(ccvariabledef(single(P, Id, T, initial(V))),P,no_def,As)
-- endcc
	 |]

  'rule' CCGenerate_variable_def(multiple(P, list(Id,Ids), _), As):
	 Get_current_variables(-> VARS)
	 Lookup_env_variable_id(Id, nil, VARS -> variable_id(I))
	 I'Type -> T
	 CCGenerate_type(T, As)

'action' CCGenerate_channel_defs(CHANNEL_DEFS, ASSUMPTIONS)

  'rule' CCGenerate_channel_defs(list(D, DS), As):
	 CCGenerate_channel_def(D, As)
	 CCGenerate_channel_defs(DS, As)

  'rule' CCGenerate_channel_defs(nil, _):

'action' CCGenerate_channel_def(CHANNEL_DEF, ASSUMPTIONS)

  'rule' CCGenerate_channel_def(single(P, Id, _), As):
	 Get_current_channels(-> CHS)
	 Lookup_env_channel_id(Id, CHS -> channel_id(I))
	 I'Type -> T
	 CCGenerate_type(T, As)

  'rule' CCGenerate_channel_def(multiple(P, list(Id,Ids), _), As):
	 Get_current_channels(-> CHS)
	 Lookup_env_channel_id(Id, CHS -> channel_id(I))
	 I'Type -> T
	 CCGenerate_type(T, As)

'action' CCGenerate_axiom_defs(AXIOM_DEFS, ASSUMPTIONS)

  'rule' CCGenerate_axiom_defs(list(D, DS), As):
	 CCGenerate_axiom_def(D, As)
	 CCGenerate_axiom_defs(DS, As)

  'rule' CCGenerate_axiom_defs(nil, _):

'action' CCGenerate_axiom_def(AXIOM_DEF, ASSUMPTIONS)

  'rule' CCGenerate_axiom_def(axiom_def(P, Oid, V), As):
	 Get_current_axioms(-> AXS)
	 Lookup_axiom(P, AXS -> I)
	 I'Axiom -> Expr
	 CCGenerate(Expr, As)

'action' CCGenerate_test_case_defs(TEST_CASE_DEFS, ASSUMPTIONS)

  'rule' CCGenerate_test_case_defs(list(D, DS), As):
	 CCGenerate_test_case_def(D, As)
	 CCGenerate_test_case_defs(DS, As)

  'rule' CCGenerate_test_case_defs(nil, _):

'action' CCGenerate_test_case_def(TEST_CASE_DEF, ASSUMPTIONS)

  'rule' CCGenerate_test_case_def(test_case_def(P, Oid, V), As):
	 Get_current_test_cases(all -> AXS)
	 Lookup_test_case(P, AXS -> I)
	 I'Test_case -> Expr
	 CCGenerate(Expr, As)

-----------------------------------------------------------------
-- CCGenerate type expressions
-----------------------------------------------------------------

'action' CCGenerate_type(TYPE_EXPR, ASSUMPTIONS)

  'rule' CCGenerate_type(product(PR), As):
	 CCGenerate_product_type(PR, As)

  'rule' CCGenerate_type(fin_set(T), As):
	 CCGenerate_type(T, As)

  'rule' CCGenerate_type(infin_set(T), As):
	 CCGenerate_type(T, As)

  'rule' CCGenerate_type(fin_list(T), As):
	 CCGenerate_type(T, As)

  'rule' CCGenerate_type(infin_list(T), As):
	 CCGenerate_type(T, As)

  'rule' CCGenerate_type(fin_map(D, R), As):
	 CCGenerate_type(D, As)
	 CCGenerate_type(R, As)

  'rule' CCGenerate_type(infin_map(D, R), As):
	 CCGenerate_type(D, As)
	 CCGenerate_type(R, As)

  'rule' CCGenerate_type(fun(D, A, result(R,RD,WR,IN,OUT)), As):
	 CCGenerate_type(D, As)
	 CCGenerate_type(R, As)
	 CCGenerate_accs(RD, As)
	 CCGenerate_accs(WR, As)
	 CCGenerate_accs(IN, As)
	 CCGenerate_accs(OUT, As)

  'rule' CCGenerate_type(subtype(TP, restriction(P, E)), As):
	 CCGenerate(E, list(typings(list(TP, nil)), As))
-- cc
	 (|
	   PVSWanted() -- PVS generates this as a TCC
	 ||
	   Generate(ccsubtype(subtype(TP, restriction(P, E))),P,no_def, As)
	 |)
-- endcc

  'rule' CCGenerate_type(bracket(T), As):
	 CCGenerate_type(T, As)

-- all other cases
  'rule' CCGenerate_type(_, _):

'action' CCGenerate_product_type(PRODUCT_TYPE, ASSUMPTIONS)

  'rule' CCGenerate_product_type(list(T, PR), As):
	 CCGenerate_type(T, As)
	 CCGenerate_product_type(PR, As)

  'rule' CCGenerate_product_type(nil, _):

-----------------------------------------------------------------
-- CCGenerate accesses
-----------------------------------------------------------------

'action' CCGenerate_accs(ACCESSES, ASSUMPTIONS)

  'rule' CCGenerate_accs(list(A, AS), As):
	 CCGenerate_acc(A, As)
	 CCGenerate_accs(AS, As)

  'rule' CCGenerate_accs(nil, _):

'action' CCGenerate_acc(ACCESS, ASSUMPTIONS)

  'rule' CCGenerate_acc(enumerated_access(_, AS), As):
	 CCGenerate_accs(AS, As)

  'rule' CCGenerate_acc(completed_access(_, nil), _):

  'rule' CCGenerate_acc(completed_access(_, qualification(Obj)), As):
	 CCGenerate_object(Obj, nil, As)

  'rule' CCGenerate_acc(comprehended_access(_, A, set_limit(_, TS, R)), As):
	 CCGenerate_value_typings(TS, As)
	 [|
	   where(R -> restriction(_,V))
	   CCGenerate(V, list(typings(TS), As))
	 |]
	 CCGenerate_acc(A, As)

  'rule' CCGenerate_acc(variable(_, _, Q), As):
	 CCGenerate_opt_qual(Q, As)

  'rule' CCGenerate_acc(channel(_, _, Q), As):
	 CCGenerate_opt_qual(Q, As)

  'rule' CCGenerate_acc(free, _):

 


-----------------------------------------------------------------
-- CCGenerate value expressions
-----------------------------------------------------------------

-- WARNING: CCGenerate assumes that type checking has generated no errors
-- and its behaviour in other circumstances is not defined

'action' CCGenerate(VALUE_EXPR, ASSUMPTIONS)

  'rule' CCGenerate(literal_expr(P, L), _):

  'rule' CCGenerate(val_occ(P, I, Q), As):
	 CCGenerate_opt_qual(Q, As)

  'rule' CCGenerate(var_occ(P, I, Q), As):
         print("CCGenerate")
	 CCGenerate_opt_qual(Q, As)

  'rule' CCGenerate(pre_occ(P, I, Q), As):
	 CCGenerate_opt_qual(Q, As)

  'rule' CCGenerate(chaos(P), _):	

  'rule' CCGenerate(skip(P), _):  

  'rule' CCGenerate(stop(P), _):  

  'rule' CCGenerate(swap(P), _):

  'rule' CCGenerate(ranged_set(P,L,R), As):
	 CCGenerate(L, As)
	 CCGenerate(R, As)

  'rule' CCGenerate(product(P, nil), _):

  'rule' CCGenerate(product(P, VS), As):
	 CCGenerate_product(VS, As)

  'rule' CCGenerate(enum_set(P, nil), _):

  'rule' CCGenerate(enum_set(P, VS), As):
	 CCGenerate_list(VS, As)

  'rule' CCGenerate(comp_set(P, V, set_limit(P1, TS, R)), As):
	 CCGenerate_value_typings(TS, As)
	 (|
	   where(R -> restriction(P2,V2))
	   CCGenerate(V2, list(typings(TS), As))
	 ||
	   where(literal_expr(P1, bool_true) -> V2)
	 |)
	 CCGenerate(V, list(assumption(V2), list(typings(TS), As)))

  'rule' CCGenerate(ranged_list(P,L,R), As):
	 CCGenerate(L, As)
	 CCGenerate(R, As)

  'rule' CCGenerate(enum_list(P, nil), _):

  'rule' CCGenerate(enum_list(P, VS), As):
	 CCGenerate_list(VS, As)

  'rule' CCGenerate(comp_list(P, V, list_limit(P1, B, V1, R)), As):
	 CCGenerate(V1, As)
	 Make_results(V1 -> list(result(T,_,_,_,_),_))
	 Make_list_type(T -> TL)
	 (| where(TL -> fin_list(TE)) || where(TL -> infin_list(TE)) |)
	 where(TYPINGS'list(single(P1, B, TE), nil) -> TPS)
	 Binding_to_expr(B, TE -> BV)
	 Id_of_isin_list -> I
	 where(VALUE_EXPR'infix_occ(P1, BV, I, nil, V1) -> Cond)
	 (|
	   where(R -> restriction(P2,V2))
	   CCGenerate(V2, list(assumption(Cond), list(typings(TPS), As)))
	 ||
	   where(literal_expr(P1, bool_true) -> V2)
	 |)
	 CCGenerate(V, list(assumption(V2), list(assumption(Cond), list(typings(TPS), As))))

  'rule' CCGenerate(enum_map(P, nil), _):

  'rule' CCGenerate(enum_map(P, PAIRS), As):
	 CCGenerate_pairs(PAIRS, As)
-- cc 
	 Generate(ccenummap(enum_map(P, PAIRS)),P,no_def, As) 
-- endcc

  'rule' CCGenerate(comp_map(P, PAIR, set_limit(P1, TS, R)), As):
	 CCGenerate_value_typings(TS, As)
	 (|
	   where(R -> restriction(P2,V2))
	   CCGenerate(V2, list(typings(TS), As))
	 ||
	   where(literal_expr(P1, bool_true) -> V2)
	 |)
	 CCGenerate_pair(PAIR, list(assumption(V2), list(typings(TS), As)))

  'rule' CCGenerate(function(P, LP, V), As):
	 (|
	   where(LP -> l_typing(P1,TPS))
	   CCGenerate_value_typings(TPS, As)
	 ||
	   where(LP -> s_typing(P1,TP))
	   CCGenerate_value_typing(TP, As)
	 |)
	 CCGenerate_function(LP, V, As)

  'rule' CCGenerate(application(P, F, ARGS), As):
	 CCGenerate_application(F, ARGS, As)
-- cc
	 (|
	   PVSWanted() -- PVS generates this as a TCC
	 ||
	   Generate(ccapplication(application(P, F, ARGS)),P,no_def, As) 
	 |)
-- endcc

  'rule' CCGenerate(quantified(P,Q,TPS,R), As):
	 CCGenerate_value_typings(TPS, As)
	 [|
	   where(R -> restriction(P2,V2))
	   CCGenerate(V2, list(typings(TPS), As))
	 |]

  'rule' CCGenerate(equivalence(P,V1,V2,PRE), As):
	 (|
	   where(PRE -> pre_cond(P2,V5))
	   CCGenerate(V5, As)
	 ||
	   where(literal_expr(P, bool_true) -> V5)
	 |)
	 CCGenerate(V1, list(assumption(V5), As))
	 CCGenerate(V2, list(assumption(V5), As))

  'rule' CCGenerate(post(P, V, post_cond(P1, R, C), PRE), As):
	 (|
	   where(PRE -> pre_cond(P2,V2))
	   CCGenerate(V2, As)
	 ||
	   where(literal_expr(P1, bool_true) -> V2)
	 |)
	 (|
	   where(R -> result(P3, B))
	   Make_results(V -> list(result(T,_,_,_,_), _))
	   where(TYPINGS'list(single(P3, B, T), nil) -> TPSR)
	 ||
	   where(TYPINGS'nil -> TPSR)
	 |)
	 CCGenerate(V, list(assumption(V2), As))
	 CCGenerate(C, list(typings(TPSR), list(assumption(V2), As))) 

  'rule' CCGenerate(disamb(P,V,T), As):
	 CCGenerate(V, As)
	 CCGenerate_type(T, As)
-- cc
	 (|
	   PVSWanted() -- PVS generates this as a TCC
	 ||
	   Generate(ccdisamb(disamb(P,V,T)),P,no_def, As)
	 |)
-- endcc

  'rule' CCGenerate(bracket(P,V), As):
	 CCGenerate(V, As)

  'rule' CCGenerate(ax_infix(P,L,C,R,_), As):
	 CCGenerate(L, As)
	 (|
	   eq(C, or)
	   CCGenerate(R, list(assumption(ax_prefix(P, not, L)), As))
	 || -- and, implies
	   CCGenerate(R, list(assumption(L), As))
	 |)

  'rule' CCGenerate(infix_occ(P,L,I,Q,R), As):
	 CCGenerate_opt_qual(Q, As)
	 CCGenerate(L, As)
	 CCGenerate(R, As)
	 (|
	   PVSWanted() -- PVS generates this as a TCC
	 ||
	   I'Def -> expl_fun(PARMS, V, POST, pre_cond(_, PRE), COND, PCOND)
	   -- generate "let PARMS = (L,R) in PRE end"
	   Generate(ccapplication(infix_occ(P,L,I,Q,R)),P,expl_fun(PARMS, V, POST, pre_cond(P, PRE), COND, PCOND), As)
	 |)

  'rule' CCGenerate(stmt_infix(P, L, Comb, R), As):
	 CCGenerate(L, As)
	 (|
	   eq(Comb, sequence)
	   CCGenerate(R, list(post_ass(L), As))
	 ||
	   CCGenerate(R, As)
	 |)
	 [|
	   (| eq(Comb, parallel) || eq(Comb, interlock) |)
	   Generate(ccconcurrent(concurrent(P, L, R)),P,no_def,As)
	 |]

  'rule' CCGenerate(always(P, V), As):
	 CCGenerate(V, As)

  'rule' CCGenerate(ax_prefix(P, C, V), As):
	 CCGenerate(V, As)

  'rule' CCGenerate(prefix_occ(P,I,Q,V), As):
	 CCGenerate_opt_qual(Q, As)
	 CCGenerate(V, As)
	 (|
	   PVSWanted() -- PVS generates this as a TCC
	 ||
	   I'Def -> expl_fun(PARMS, V2, POST, pre_cond(_, PRE), COND, PCOND)
	   -- generate "let PARMS = V in PRE end"
	   Generate(ccapplication(prefix_occ(P,I,Q,V)),P,expl_fun(PARMS, V2, POST, pre_cond(P, PRE), COND, PCOND), As)
	 |)

  'rule' CCGenerate(comprehended(P, Comb, V, set_limit(P1, TS, R)), As):
	 CCGenerate_value_typings(TS, As)
	 (|
	   where(R -> restriction(P2,V2))
	   CCGenerate(V2, list(typings(TS), As))
	 ||
	   where(literal_expr(P1, bool_true) -> V2)
	 |)
	 CCGenerate(V, list(assumption(V2), list(typings(TS), As)))

  'rule' CCGenerate(initialise(P, Q), As):
	 CCGenerate_opt_qual(Q, As)

  'rule' CCGenerate(ass_occ(P, I, Q, V), As):
	 CCGenerate_opt_qual(Q, As)
	 CCGenerate(V, As)
-- cc
	 Generate(ccassignment(ass_occ(P, I, Q, V)),P,no_def,As)
-- endcc

  'rule' CCGenerate(input_occ(P, I, Q), As):
	 CCGenerate_opt_qual(Q, As)

  'rule' CCGenerate(output_occ(P, I, Q, V), As):
	 CCGenerate_opt_qual(Q, As)
	 CCGenerate(V, As)
-- cc
	 Generate(ccoutput(output_occ(P, I, Q, V)),P,no_def,As)
-- endcc


  'rule' CCGenerate(env_local(P, DS, CE, V), As):
	 Current -> C
	 Current <- current_env(CE, C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 CCGenerate_class(basic(DS), As)
	 CCGenerate(V, list(class(basic(DS),CE), As))
	 Current <- C
	 Extend_paths <- Paths

  'rule' CCGenerate(class_scope_expr(P, CL, V), As):
	 Get_current_with(-> WITH)
	 Current -> C
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 Make_basic_env(CL)
	 Complete_type_env(CL)
	 Make_value_env(CL)
	 Check_value_env(CL)
	 Resolve_class(CL)
	 CCGenerate_class(CL, As)
	 Current -> current_env(CE, C1)
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), current_env(CE, C1))
	 Extend_paths -> Paths1
	 Extend_paths <- list(nil,Paths1)
	 Resolve(V, bool -> V1)
	 CCGenerate(V1, list(class(CL, CE), As))
	 Current <- C
	 Extend_paths <- Paths

  'rule' CCGenerate(implementation_relation(P, instantiation(name(_,id_op(Id)), OS), instantiation(name(_,id_op(Id1)), OS1)), As):
	 eq(Id, Id1)
	 CCGenerate_scheme_args_implementation(P, OS, OS1, As)
  
  'rule' CCGenerate(implementation_relation(P, CL1, CL2), As):
	 Get_current_with(-> WITH)
	 Current -> C
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 Make_basic_env(CL1)
	 Complete_type_env(CL1)
	 Make_value_env(CL1)
	 Check_value_env(CL1)
	 Resolve_class(CL1)
	 CCGenerate_class(CL1, nil)
	 Get_current_env(-> E1)
	 Get_env_adapts(E1 -> AD)
	 Remove_hides(AD -> AD1)
	 Set_env_adapts(E1, AD1 -> E11)
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
	 Extend_paths <- list(nil,Paths)
	 Make_basic_env(CL2)
	 Complete_type_env(CL2)
	 Make_value_env(CL2)
	 Check_value_env(CL2)
	 Resolve_class(CL2)
	 CCGenerate_class(CL2, nil)
	 Get_current_env(-> E2)
	 Current <- C
	 Extend_paths <- Paths
	 Make_type_fits(E2, E11, nil -> TYPF)
	 Make_imp_fit(E2, E11, nil, TYPF, nil -> IF)
	 Get_env_axioms(E2 -> OLDAX)
	 Get_env_axioms(E11 -> NEWAX)
	 CCImplementation(P, IF, IF, OLDAX, NEWAX -> VE)
	 Generate(ccimplementation(scoped_conditions(P, CL1, VE)), P, no_def, As)
	 
  'rule' CCGenerate(implementation_expr(P, Obj1, Obj2), As):
	 Resolve_object(Obj1 -> Obj11)
	 Resolve_object(Obj2 -> Obj21)
	 (|
	   Same_object(Obj11, Obj21, imp_fit(nil,nil,nil,nil,nil))
	 ||
	   Env_of_defined_object(Obj11 -> E1)
	   Get_env_adapts(E1 -> AD)
	   Remove_hides(AD -> AD1)
	   Set_env_adapts(E1, AD1 -> E11)
	   Env_of_defined_object(Obj21 -> E2)
	   Make_type_fits(E2, E11, nil -> TYPF)
	   Make_imp_fit(E2, E11, nil, TYPF, nil -> IF)
	   Get_env_axioms(E2 -> OLDAX)
	   Get_env_axioms(E11 -> NEWAX)
	   CCImplementation(P, IF, IF, OLDAX, NEWAX -> VE)
	   Generate(ccimplementation(conditions(P, VE)), P, no_def, As)
	 |)

  'rule' CCGenerate(let_expr(P,DEFS,V), As):
	 CCGenerate_let(DEFS, As)	 
	 CCGenerate(V, list(lets(DEFS), As))	

  'rule' CCGenerate(if_expr(P, V, THEN, _, ELSIF, ELSE), As):
	 CCGenerate(V, As)
	 CCGenerate(THEN, list(assumption(V), As))
	 CCGenerate_elsif(ELSIF, list(assumption(ax_prefix(P, not, V)), As) -> As1)
	 [|
	   where(ELSE -> else(P1, E))
	   CCGenerate(E, As1)
	 |]

  'rule' CCGenerate(case_expr(P, V, _, BRANCHES), As):
	 CCGenerate(V, As)
	 CCGenerate_case_branches(V, BRANCHES, As)
	 CCGenerate_case(P, V, BRANCHES, As)

  'rule' CCGenerate(while_expr(P, C, V), As):
	 CCGenerate(C, As)
	 CCGenerate(V, list(assumption(C), As))

  'rule' CCGenerate(until_expr(P, V, C), As):
	 CCGenerate(V, As)
	 CCGenerate(C, list(post_ass(V), As))

  'rule' CCGenerate(for_expr(P, list_limit(P1, B, LV, R), V), As):
	 CCGenerate(LV, As)
	 Make_results(LV -> list(result(T,_,_,_,_),_))
	 Make_list_type(T -> TL)
	 (| where(TL -> fin_list(TE)) || where(TL -> infin_list(TE)) |)
	 where(TYPINGS'list(single(P1, B, TE), nil) -> TPS)
	 Binding_to_expr(B, TE -> BV)
	 Id_of_isin_list -> I
	 where(VALUE_EXPR'infix_occ(P1, BV, I, nil, LV) -> Cond)
	 (|
	   where(R -> restriction(P2,V2))
	   CCGenerate(V2, list(assumption(Cond), list(typings(TPS), As)))
	 ||
	   where(literal_expr(P1, bool_true) -> V2)
	 |)
	 CCGenerate(V, list(assumption(V2), list(assumption(Cond), list(typings(TPS), As))))

--  all other cases
  'rule' CCGenerate(V, _):

'action' CCGenerate_product(VALUE_EXPRS, ASSUMPTIONS)

  'rule' CCGenerate_product(list(V, VS), As):
	 CCGenerate(V, As)
	 CCGenerate_product(VS, As)

  'rule' CCGenerate_product(nil, _): 

'action' CCGenerate_list(VALUE_EXPRS, ASSUMPTIONS)

  'rule' CCGenerate_list(list(V, VS), As):
	 CCGenerate(V, As)
	 CCGenerate_list(VS, As)

  'rule' CCGenerate_list(nil, _):

'action' CCGenerate_pairs(VALUE_EXPR_PAIRS, ASSUMPTIONS)

  'rule' CCGenerate_pairs(list(H,T), As):
	 CCGenerate_pair(H, As)
	 CCGenerate_pairs(T, As)

  'rule' CCGenerate_pairs(nil, _):

'action' CCGenerate_pair(VALUE_EXPR_PAIR, ASSUMPTIONS)

  'rule' CCGenerate_pair(pair(L, R), As):
	 CCGenerate(L, As) 
	 CCGenerate(R, As) 

'action' CCGenerate_function(LAMBDA_PARAMETER, VALUE_EXPR, ASSUMPTIONS)

  'rule' CCGenerate_function(l_typing(P, TPS), V, As):
	 CCGenerate(V, list(typings(TPS), As))

  'rule' CCGenerate_function(s_typing(P, TP), V, As):
	 CCGenerate(V, list(typings(list(TP, nil)), As))

'action' CCGenerate_application(VALUE_EXPR, ACTUAL_FUNCTION_PARAMETERS, ASSUMPTIONS)

  'rule' CCGenerate_application(V, ARGS, As):
	 CCGenerate(V, As)
	 CCGenerate_args(ARGS, As)

'action' CCGenerate_args(ACTUAL_FUNCTION_PARAMETERS, ASSUMPTIONS)
	
  'rule' CCGenerate_args(list(fun_arg(P, VS), ARGS), As):
	 CCGenerate_args(ARGS, As)
	 (|
	   where(VS -> list(V, nil))
	   CCGenerate(V, As)
	 ||
	   CCGenerate(product(P, VS), As)
	 |)

  'rule' CCGenerate_args(nil, _):

'action' CCGenerate_let(LET_DEFS, ASSUMPTIONS)

  'rule' CCGenerate_let(list(D, DS), As):
	 CCGenerate_let_def(D, As)
	 CCGenerate_let(DS, list(lets(list(D, nil)), As))

  'rule' CCGenerate_let(nil, _):

'action' CCGenerate_let_def(LET_DEF, ASSUMPTIONS)

  'rule' CCGenerate_let_def(explicit(_, LB, V), As):
	 CCGenerate(V, As)
	 [|
	   where(LB -> pattern(P, Patt))
	   Make_results(V -> list(result(T, _, WR, IN, OUT), _))
	   (|
	     Read_only(readonly, WR, IN, OUT)
	     Pattern_match(V, Patt -> Cond, DS)
	     Generate(ccpatternmatch(pattern_match(P, Cond)), P, no_def, As)
-- debug
-- (|
--   eq(DS, nil)
--   Putmsg("No let from let pattern\n")
-- ||
--   Putmsg("Let from let pattern:\n")
--   Print_expr(let_expr(P, DS, no_val))
--   Putnl()
-- |)
	   ||
	     string_to_id("x_" -> X)
	     New_value_id(P, id_op(X) -> I)
	     I'Type <- T
	     Pattern_match(val_occ(P, I, nil), Patt -> Cond, _)
	     Simplify(Cond -> Cond1)
	     (|
	       (| eq(Cond1,no_val) || where(Cond1 -> literal_expr(_,bool_true)) |)
	     ||
	       where(
	       equivalence(P,
		 let_expr(P,list(explicit(P,binding(P,single(P,id_op(X))),V),nil),
				  Cond1),
		 let_expr(P,list(explicit(P,binding(P,single(P,id_op(X))),V),nil),
				  literal_expr(P,bool_true)),
		 nil) -> Cond2)
	       Generate(ccpatternmatch(pattern_match(P, Cond2)), P, no_def, As)
	     |)
	   |)
	 |]

  'rule' CCGenerate_let_def(implicit(P, TP, R), As):
	 CCGenerate_value_typing(TP, As)
	 [|
	   where(R -> restriction(P1, V))
	   CCGenerate(V, list(typings(list(TP, nil)), As))
	 |]

'action' CCGenerate_elsif(ELSIF_BRANCHES, ASSUMPTIONS -> ASSUMPTIONS)

  'rule' CCGenerate_elsif(list(elsif(P, V, E, _), ES), As -> As1):
	 CCGenerate(V, As)
	 CCGenerate(E, list(assumption(V), As))
	 CCGenerate_elsif(ES, list(assumption(ax_prefix(P,not,V)), As) -> As1)

  'rule' CCGenerate_elsif(nil, As -> As):

'action' CCGenerate_case(POS, VALUE_EXPR, CASE_BRANCHES, ASSUMPTIONS)

  'rule' CCGenerate_case(P, V, BRS, As):
	 Make_results(V -> list(result(T, _, WR, IN, OUT), _))
	 (|
	   Read_only(readonly, WR, IN, OUT)
	   Case_conds(V, BRS -> Conds)
	   Disjoin(P, Conds -> Cond)
	   Generate(cccases(cases(P, Cond)), P, no_def, As)
	 ||
	   string_to_id("x_" -> X)
	   New_value_id(P, id_op(X) -> I)
	   I'Type <- T
	   Case_conds(val_occ(P, I, nil), BRS -> Conds)
	   Disjoin(P, Conds -> Cond)
	   Simplify(Cond -> Cond1)
	   (|
	     (| eq(Cond1,no_val) || where(Cond1 -> literal_expr(_,bool_true)) |)
	   ||
	     where(
	     equivalence(P,
	       let_expr(P,list(explicit(P,binding(P,single(P,id_op(X))),V),nil),
				Cond),
	       let_expr(P,list(explicit(P,binding(P,single(P,id_op(X))),V),nil),
				literal_expr(P,bool_true)),
               nil) -> Cond2)
	     Generate(cccases(cases(P, Cond2)), P, no_def, As)
	   |)
	 |)

'action' Disjoin(POS, VALUE_EXPRS -> VALUE_EXPR)

  'rule' Disjoin(_, list(V, nil) -> V):

  'rule' Disjoin(P, list(V, VS) -> ax_infix(P, V, or, V1, P)):
	 Disjoin(P, VS -> V1)

'action' Case_conds(VALUE_EXPR, CASE_BRANCHES -> VALUE_EXPRS)

  'rule' Case_conds(V, list(case(P, Patt, _, _), nil) -> list(C, nil)):
	 Pattern_match(V, Patt -> C, DS)
-- debug
-- (|
--   eq(DS, nil)
--   Putmsg("No let from case\n")
-- ||
--   Putmsg("Let from case:\n")
--   Print_expr(let_expr(P, DS, no_val))
--   Putnl()
-- |)

  'rule' Case_conds(V, list(case(P, Patt, _, _), PS) -> list(C, CS)):
	 Pattern_match(V, Patt -> C, DS)
-- debug
-- (|
--   eq(DS, nil)
--   Putmsg("No let from case\n")
-- ||
--   Putmsg("Let from case:\n")
--   Print_expr(let_expr(P, DS, no_val))
--   Putnl()
-- |)
	 Case_conds(V, PS -> CS)

'action' CCGenerate_case_branches(VALUE_EXPR, CASE_BRANCHES, ASSUMPTIONS)

  'rule' CCGenerate_case_branches(V0, list(case(P,PATT,V,_),BRS), As):
	 Pattern_match(V0, PATT -> C, DS)
	 CCGenerate(V, list(lets(DS), list(assumption(C), As)))
	 CCGenerate_case_branches(V0, BRS, list(assumption(ax_prefix(P,not,C)), As))
	 
  'rule' CCGenerate_case_branches(_, nil, _):

'action' CCGenerate_opt_qual(OPT_QUALIFICATION, ASSUMPTIONS)

  'rule' CCGenerate_opt_qual(nil, _):

  'rule' CCGenerate_opt_qual(qualification(Obj), As):
	 CCGenerate_object(Obj, nil, As)

'action' CCGenerate_object(OBJECT_EXPR, IN_ARRAY, ASSUMPTIONS)

  'rule' CCGenerate_object(obj_appl(Obj, Parms), In_array, As):
	 (|
	   (| eq(In_array, in_array) || Is_array(Obj) |)
	 ||
	   CCGenerate_object(Obj, nil, As)
	 |)
	 Param_type_of_object(Obj -> T)
	 Object_pos(Obj -> P)
	 Generate(ccobjappl(obj_appl(P, Parms, T)), P, no_def, As)

  'rule' CCGenerate_object(obj_array(_, Obj), _, As):
	 CCGenerate_object(Obj, in_array, As)
	 
  'rule' CCGenerate_object(obj_fit(Obj, _), In_array, As):
	 CCGenerate_object(Obj, In_array, As)

  'rule' CCGenerate_object(obj_occ(_, _), In_array, _):

  'rule' CCGenerate_object(qual_occ(_, Obj, _), In_array, As):
	 (|
	   eq(In_array, in_array)
	 ||
	   CCGenerate_object(Obj, nil, As)
	 |)

'action' CCGenerate_scheme_args_implementation(POS, OBJECT_EXPRS, OBJECT_EXPRS, ASSUMPTIONS)

  'rule' CCGenerate_scheme_args_implementation(P, list(O1, OS1), list(O2, OS2), As):
	 CCGenerate(implementation_expr(P, O1, O2), As)
	 CCGenerate_scheme_args_implementation(P, OS1, OS2, As)

  'rule' CCGenerate_scheme_args_implementation(_, nil, nil, _):

'condition' Is_array(OBJECT_EXPR)

  'rule' Is_array(obj_array(_, _)):

  'rule' Is_array(obj_fit(Obj, _)):
	 Is_array(Obj)

'action' Param_type_of_object(OBJECT_EXPR -> TYPE_EXPR)

  'rule' Param_type_of_object(obj_array(TPS, Obj) -> T):
	 Object_application_condition(Obj -> V)
	 (|
	   eq(V, no_val)
	   Type_of_typings_as_product(TPS -> T)
	 ||
	   Make_single_typing(TPS -> TP)
	   Object_pos(Obj -> P)
	   where(TYPE_EXPR'subtype(TP, restriction(P, V)) -> T)
	 |)

  'rule' Param_type_of_object(obj_fit(Obj, _) -> T):
	 Param_type_of_object(Obj -> T)

  'rule' Param_type_of_object(obj_occ(_, I) -> T):
	 I'Params -> param_type(T)

  'rule' Param_type_of_object(qual_occ(_, _, I) -> T):
	 I'Params -> param_type(T)

'action' Object_application_condition(OBJECT_EXPR -> VALUE_EXPR)

  'rule' Object_application_condition(obj_appl(Obj, Parms) -> ax_infix(P,V1,and,V2,P)):
	 Object_application_condition(Obj -> V1)
	 Param_type_of_object(Obj -> T)
	 Object_pos(Obj -> P)
	 Isin_subtype(product(P, Parms), T -> V2)
	 
  'rule' Object_application_condition(obj_array(_, _) -> no_val):

  'rule' Object_application_condition(obj_fit(Obj, _) -> V):
	 Object_application_condition(Obj -> V)

  'rule' Object_application_condition(obj_occ(_, _) -> no_val):

  'rule' Object_application_condition(qual_occ(_, Obj, _) -> V):
	 Object_application_condition(Obj -> V)

'action' Remove_hides(ADAPTS -> ADAPTS)

  'rule' Remove_hides(hide(_, Ads) -> Ads1):
	 Remove_hides(Ads -> Ads1)

  'rule' Remove_hides(rename(Id1, Id2, Ads) -> rename(Id1, Id2, Ads1)):
	 Remove_hides(Ads -> Ads1)

  'rule' Remove_hides(nil -> nil):
	 
----------------------------------------------------------------
-- CCGenerate typings
----------------------------------------------------------------

'action' CCGenerate_value_typings(TYPINGS, ASSUMPTIONS)

  'rule' CCGenerate_value_typings(list(T, TS), As):
	 CCGenerate_value_typing(T, As)
	 CCGenerate_value_typings(TS, As)

  'rule' CCGenerate_value_typings(nil, _):

'action' CCGenerate_value_typing(TYPING, ASSUMPTIONS)

  'rule' CCGenerate_value_typing(single(P, B, T), As):
	 CCGenerate_type(T, As)

  'rule' CCGenerate_value_typing(multiple(P, BS, T), As):
	 CCGenerate_type(T, As)

----------------------------------------------------------------
-- CCGenerate scheme instantiation arguments
----------------------------------------------------------------

'action' Param_fit_to_object_fits(PARAM_FIT -> OBJECT_FITS)

  'rule' Param_fit_to_object_fits(no_parms -> nil):

  'rule' Param_fit_to_object_fits(param_fit(OI, I, Obj, AD, PF) -> OBJF):
	 eq(OI, I)  -- actual same as formal: nothing to add
	 Param_fit_to_object_fits(PF -> OBJF)

  'rule' Param_fit_to_object_fits(param_fit(OI, I, Obj, AD, PF) -> object_fit(OI, object_id(I), form_act, OBJF)):
	 Param_fit_to_object_fits(PF -> OBJF)

  'rule' Param_fit_to_object_fits(nil -> nil):

'action' Param_fit_to_type_fits(PARAM_FIT -> TYPE_FITS)

  'rule' Param_fit_to_type_fits(no_parms -> nil):

  'rule' Param_fit_to_type_fits(param_fit(OI, I, Obj, AD, PF) -> TYPF):
	 eq(OI, I)  -- actual same as formal: nothing to add
	 Param_fit_to_type_fits(PF -> TYPF)

  'rule' Param_fit_to_type_fits(param_fit(OI, I, Obj, AD, PF) -> TYPF):
	 OI'Env -> E1
	 I'Env -> E2
	 Get_env_adapts(E2 -> AD2)
	 Remove_hides(AD2 -> AD21)
	 Set_env_adapts(E2, AD21 -> E21)
	 Make_type_fits(E1, E21, AD -> TYPF1)
	 Param_fit_to_type_fits(PF -> TYPF2)
	 Concat_type_fits(TYPF1, TYPF2 -> TYPF)

  'rule' Param_fit_to_type_fits(nil -> nil):

'action' Param_fit_to_imp_fit(PARAM_FIT, TYPE_FITS, OBJECT_FITS -> IMP_FIT)

  'rule' Param_fit_to_imp_fit(no_parms, _, _ -> imp_fit(nil,nil,nil,nil,nil)):

  'rule' Param_fit_to_imp_fit(param_fit(OI, I, Obj, AD, PF), TYPF, OBJF -> IF):
	 eq(OI, I)  -- actual same as formal: nothing to add
	 Param_fit_to_imp_fit(PF, TYPF, OBJF -> IF)

  'rule' Param_fit_to_imp_fit(param_fit(OI, I, Obj, AD, PF), TYPF, OBJF -> IF):
	 OI'Env -> E1
	 I'Env -> E2
	 Get_env_adapts(E2 -> AD2)
	 Remove_hides(AD2 -> AD21)
	 Set_env_adapts(E2, AD21 -> E21)
	 Make_imp_fit(E1, E21, AD, TYPF, OBJF -> IF1)
-- debug
-- Putmsg("Fitting ")
-- print(OI)
-- OI'Ident -> Oid
-- Print_id(Oid)
-- Putmsg(" to ")
-- print(I)
-- I'Ident -> Nid
-- Print_id(Nid)
-- Putmsg(" with object fitting ")
-- Putnl()
-- print(OBJF)
-- Putmsg(" with type fitting ")
-- Putnl()
-- print(TYPF)
-- Putmsg("made fitting\n")
-- print(IF1)
	 Param_fit_to_imp_fit(PF, TYPF, OBJF -> IF2)
	 Concat_imp_fits(IF1, IF2 -> IF)

  'rule' Param_fit_to_imp_fit(nil, _, _ -> imp_fit(nil,nil,nil,nil,nil)): 

'action' CCGenerate_instantiation_args(PARAM_FIT, IMP_FIT)

  'rule' CCGenerate_instantiation_args(no_parms, _):

  'rule' CCGenerate_instantiation_args(param_fit(OI, I, Obj, AD, PF), IF):
	 eq(OI, I)  -- actual same as formal: automatically OK
	 CCGenerate_instantiation_args(PF, IF)

  'rule' CCGenerate_instantiation_args(param_fit(OI, I, Obj, AD, PF), IF):
	 Object_pos(Obj -> P)
	 CCGenerate_instantiation_arg(P, OI, I, AD, IF)
	 CCGenerate_instantiation_args(PF, IF)

  'rule' CCGenerate_instantiation_args(nil, _):

'action' CCGenerate_instantiation_arg(POS, Object_id, Object_id, ADAPTS, IMP_FIT)

  'rule' CCGenerate_instantiation_arg(P, I1, I2, AD, IF):
	 I1'Env -> E1
	 I2'Env -> E2
	 Get_env_adapts(E2 -> AD2)
	 Remove_hides(AD2 -> AD21)
	 Set_env_adapts(E2, AD21 -> E21)
	 where(IF -> imp_fit(TYPF,_,_,_,OBJF))
	 Make_imp_fit(E1, E21, AD, TYPF, OBJF -> IF1)
	 Get_env_axioms(E1 -> OLDAX)
	 Get_env_axioms(E21 -> NEWAX)
	 CCImplementation(P, IF1, IF, OLDAX, NEWAX -> VE)
	 Generate(ccimplementation(formal_actual_conditions(P, VE)), P, no_def, nil)








---------------------------------------------------------------
-- Implementation relation
---------------------------------------------------------------

'action' Make_type_fits(CLASS_ENV, CLASS_ENV, ADAPTS -> TYPE_FITS)

  'rule' Make_type_fits(Oldenv, Newenv, AD -> TYPF)
	 Current -> C
	 Extend_paths -> Paths
	 Current <- current_env(Newenv, nil)
	 Extend_paths <- list(nil,nil)
	 Make_type_fits1(Oldenv, AD -> TYPF)
	 Current <- C
	 Extend_paths <- Paths

'action' Make_type_fits1(CLASS_ENV, ADAPTS -> TYPE_FITS)

  'rule' Make_type_fits1(instantiation_env(_, CE), AD -> TYPF):
	 Make_type_fits1(CE, AD -> TYPF)

  'rule' Make_type_fits1(extend_env(CE1, CE2, WITH, AD), AD1 -> TYPF):
	 Concat_adapts(AD1, AD -> AD2)
	 Make_type_fits1(CE1, AD2 -> TYPF1)
	 Make_type_fits1(CE2, AD2 -> TYPF2)
	 Concat_type_fits(TYPF1, TYPF2 -> TYPF)

  'rule' Make_type_fits1(basic_env(TYP, list(VAL,VES), VAR, CH, MOD, AX, TC,_, _,WITH, AD), AD1 -> TYPF):
	 Concat_adapts(AD1, AD -> AD2)
	 Make_type_fits2(TYP, AD2 -> TYPF)

'action' Make_imp_fit(CLASS_ENV, CLASS_ENV, ADAPTS, TYPE_FITS, OBJECT_FITS -> IMP_FIT)

  'rule' Make_imp_fit(Oldenv, Newenv, AD, TYPF, OBJF -> IF)
	 Current -> C
	 Extend_paths -> Paths
	 Current <- current_env(Newenv, nil)
	 Extend_paths <- list(nil,nil)
	 Make_imp_fit1(Oldenv, AD, TYPF, OBJF -> IF)
	 Current <- C
	 Extend_paths <- Paths

'action' Make_imp_fit1(CLASS_ENV, ADAPTS, TYPE_FITS, OBJECT_FITS -> IMP_FIT)

  'rule' Make_imp_fit1(instantiation_env(_, CE), AD, TYPF, OBJF -> IF):
	 Make_imp_fit1(CE, AD, TYPF, OBJF -> IF)

  'rule' Make_imp_fit1(extend_env(CE1, CE2, WITH, AD), AD1, TYPF, OBJF -> IF):
	 Concat_adapts(AD1, AD -> AD2)
	 Make_imp_fit1(CE1, AD2, TYPF, OBJF -> IF1)
	 Make_imp_fit1(CE2, AD2, TYPF, OBJF -> IF2)
	 Concat_imp_fits(IF1, IF2 -> IF)

  'rule' Make_imp_fit1(basic_env(TYP, list(VAL,VES), VAR, CH, MOD, AX, TC, _, _,WITH, AD), AD1, TYPF, OBJF -> IF):
	 Concat_adapts(AD1, AD -> AD2)
	 Make_variable_fits(VAR, AD2 -> VARF)
	 Make_channel_fits(CH, AD2 -> CHF)
	 Make_object_fits(MOD, AD2 -> MODF)
	 Concat_object_fits(MODF, OBJF -> OBJF1)
	 Add_embedded_fittings(MODF, imp_fit(TYPF, nil, VARF, CHF, OBJF1) -> IF1)
	 -- add values last since need to fit types to
	 -- disambiguate overloaded value identifiers
	 Make_value_fits(VAL, AD2, IF1 -> VALF)
	 where(IF1 -> imp_fit(TYPF1, VALF1, VARF1, CHF1, MODF1))
	 Concat_value_fits(VALF, VALF1 -> VALF2)
	 where(imp_fit(TYPF1, VALF2, VARF1, CHF1, MODF1) -> IF)
-- debug
-- Putmsg("Make_imp_fit returns ")
-- print(IF)

'action' Make_type_fits2(TYPE_ENV, ADAPTS -> TYPE_FITS)

  'rule' Make_type_fits2(type_env(I, TE), Ads -> TF):
	 Make_type_fits2(TE, Ads -> TF1)
	 I'Ident -> Id
	 I'Pos -> P
	 (|
	   Unadapt_name(name(P, id_op(Id)), Ads, no_hide -> act_name(N))
	   Current -> C
	   Extend_paths -> Paths
	   Lookup_current_type_name(N, C, Paths, nil, nil -> I1)
	   Nil_or_different_type(I, I1) -- avoid possible circularities
	   where(type_fit(I, I1, TF1) -> TF)
	 ||
	   where(TF1 -> TF)
	 |)

  'rule' Make_type_fits2(nil, _ -> nil):

'action' Make_value_fits(Value_ids, ADAPTS, IMP_FIT -> VALUE_FITS)

  'rule' Make_value_fits(list(I, VE), Ads, IF -> VF):
	 Make_value_fits(VE, Ads, IF -> VF1)
	 I'Ident -> Id
	 I'Pos -> P
	 (|
	   Unadapt_name(name(P, Id), Ads, no_hide -> act_name(name(P1, Id1)))
	   Current -> C
	   Extend_paths -> Paths
	   Lookup_current_value_name(name(P1, Id1), C, Paths, nil, nil -> Ids)
	   (|
	     where(Id1 -> op_op(Op))
	     Lookup_op_types(Op -> Ids1)
	     Union_ids(Ids1, Ids -> Ids2) 
	   ||
	     where(Ids -> Ids2)
	   |)
	   (|
	     where(Ids2 -> list(I2, nil))
	     where(value_id(I2) -> I1)
	   ||
	     I'Type -> T
	     Fit_type(T, IF -> T1)
	     Select_id_by_type(Ids2, T1 -> I1)
-- debug
-- Putmsg("Fitting ")
-- print(I)
-- Putmsg(" named ")
-- Print_id_or_op(Id)
-- Putmsg(" of type ")
-- Print_type(T)
-- Putnl()
-- print(T)
-- Putmsg("Fitted to ")
-- Print_type(T1)
-- Putnl()
-- print(T1)
-- Putmsg("by fitting\n")
-- print(IF)
-- print(Ids2)
-- (|
-- where(I1 -> value_id(I11))
-- Putmsg("Found ")
-- I11'Ident -> Id11
-- Print_id_or_op(Id11)
-- Putmsg(" of type ")
-- I11'Type -> T11
-- Print_type(T11)
-- Putnl()
-- ||
-- Putmsg("None found amongst ")
-- Putnl()
-- Print_val_ids(Ids2)
-- |)
	   |)
	   Nil_or_different_value(I, I1) -- avoid possible circularities
	   where(value_fit(I, I1, VF1) -> VF)
	 ||
	   where(VF1 -> VF)
	 |)

  'rule' Make_value_fits(nil, _, _ -> nil):

-- debug
/*'action' Print_val_ids(Value_ids)

  'rule' Print_val_ids(list(I, Ids)):
	 I'Ident -> Id
	 I'Type -> T
	 Print_id_or_op(Id)
	 Putmsg(" of type ")
	 Print_type(T)
	 Putnl()
	 print(T)
	 Print_val_ids(Ids)

  'rule' Print_val_ids(nil):*/


'action' Make_variable_fits(VARIABLE_ENV, ADAPTS -> VARIABLE_FITS)

  'rule' Make_variable_fits(variable_env(I, VE), Ads -> VF):
	 Make_variable_fits(VE, Ads -> VF1)
	 I'Ident -> Id
	 I'Pos -> P
	 (|
	   Unadapt_name(name(P, id_op(Id)), Ads, no_hide -> act_name(N))
	   Current -> C
	   Extend_paths -> Paths
	   Lookup_current_variable_name(N, C, Paths, nil, nil -> I1)
	   Nil_or_different_variable(I, I1) -- avoid possible circularities
	   where(variable_fit(I, I1, VF1) -> VF)
	 ||
	   where(VF1 -> VF)
	 |)

  'rule' Make_variable_fits(nil, _ -> nil):

'action' Make_channel_fits(CHANNEL_ENV, ADAPTS -> CHANNEL_FITS)

  'rule' Make_channel_fits(channel_env(I, CHE), Ads -> CF):
	 Make_channel_fits(CHE, Ads -> CF1)
	 I'Ident -> Id
	 I'Pos -> P
	 (|
	   Unadapt_name(name(P, id_op(Id)), Ads, no_hide -> act_name(N))
	   Current -> C
	   Extend_paths -> Paths
	   Lookup_current_channel_name(N, C, Paths, nil, nil -> I1)
	   Nil_or_different_channel(I, I1) -- avoid possible circularities
	   where(channel_fit(I, I1, CF1) -> CF)
	 ||
	   where(CF1 -> CF)
	 |)

  'rule' Make_channel_fits(nil, _ -> nil):

'action' Make_object_fits(MODULE_ENV, ADAPTS -> OBJECT_FITS)

  'rule' Make_object_fits(object_env(I, ME), Ads -> OF):
	 Make_object_fits(ME, Ads -> OF1)
	 I'Ident -> Id
-- debug
-- Putmsg("Object is")
-- print(I)
	 I'Pos -> P
	 (|
	   Unadapt_name(name(P, id_op(Id)), Ads, no_hide -> act_name(name(P1, id_op(Id1))))
	   Current -> C
	   Extend_paths -> Paths
	   Lookup_object_in_current_env(Id1, C, Paths, nil, nil -> I1, _)
-- Putmsg("Found object is ")
-- print(I1)
	   Nil_or_different_object(I, I1) -- avoid possible circularities
	   where(object_fit(I, I1, embedded, OF1) -> OF)
	 ||
	   where(OF1 -> OF)
	 |)

  'rule' Make_object_fits(nil, _ -> nil):

'condition' Nil_or_different_type(Type_id, OPT_TYPE_ID)

  'rule' Nil_or_different_type(I, type_id(I1)):
	 ne(I, I1)

  'rule' Nil_or_different_type(_, nil):

'condition' Nil_or_different_value(Value_id, OPT_VALUE_ID)

  'rule' Nil_or_different_value(I, value_id(I1)):
	 ne(I, I1)

  'rule' Nil_or_different_value(_, nil):

'condition' Nil_or_different_variable(Variable_id, OPT_VARIABLE_ID)

  'rule' Nil_or_different_variable(I, variable_id(I1)):
	 ne(I, I1)

  'rule' Nil_or_different_variable(_, nil):

'condition' Nil_or_different_channel(Channel_id, OPT_CHANNEL_ID)

  'rule' Nil_or_different_channel(I, channel_id(I1)):
	 ne(I, I1)

  'rule' Nil_or_different_channel(_, nil):

'condition' Nil_or_different_object(Object_id, OPT_OBJECT_ID)

  'rule' Nil_or_different_object(I, object_id(I1)):
	 ne(I, I1)

  'rule' Nil_or_different_object(_, nil):

'action' Concat_imp_fits(IMP_FIT, IMP_FIT -> IMP_FIT)

  'rule' Concat_imp_fits(imp_fit(TF1, VALF1, VARF1, CHF1, MODF1),
  imp_fit(TF2, VALF2, VARF2, CHF2, MODF2) -> imp_fit(TF, VALF, VARF, CHF, MODF)):
	 Concat_type_fits(TF1, TF2 -> TF)
	 Concat_value_fits(VALF1, VALF2 -> VALF)
	 Concat_variable_fits(VARF1, VARF2 -> VARF)
	 Concat_channel_fits(CHF1, CHF2 -> CHF)
	 Concat_object_fits(MODF1, MODF2 -> MODF)

-- type and object fits get duplicated
'action' Concat_type_fits(TYPE_FITS, TYPE_FITS -> TYPE_FITS)

  'rule' Concat_type_fits(F, nil -> F):

  'rule' Concat_type_fits(type_fit(I, I1, F1), F2 -> F):
	 Concat_type_fits(F1, F2 -> F3)
	 (|
	   Isin_type_fits(I, F3)
	   where(F3 -> F)
	 ||
	   where(type_fit(I, I1, F3) -> F)
	 |)

  'rule' Concat_type_fits(nil, F -> F):

'condition' Isin_type_fits(Type_id, TYPE_FITS)

  'rule' Isin_type_fits(I, type_fit(I1, _, F)):
	 (| eq(I, I1) || Isin_type_fits(I, F) |)

'action' Concat_value_fits(VALUE_FITS, VALUE_FITS -> VALUE_FITS)

  'rule' Concat_value_fits(F, nil -> F):

  'rule' Concat_value_fits(value_fit(I, I1, F1), F2 -> value_fit(I, I1, F)):
	 Concat_value_fits(F1, F2 -> F) 

  'rule' Concat_value_fits(nil, F -> F):

'action' Concat_variable_fits(VARIABLE_FITS, VARIABLE_FITS -> VARIABLE_FITS)

  'rule' Concat_variable_fits(F, nil -> F):

  'rule' Concat_variable_fits(variable_fit(I, I1, F1), F2 -> variable_fit(I, I1, F)):
	 Concat_variable_fits(F1, F2 -> F) 

  'rule' Concat_variable_fits(nil, F -> F):

'action' Concat_channel_fits(CHANNEL_FITS, CHANNEL_FITS -> CHANNEL_FITS)

  'rule' Concat_channel_fits(F, nil -> F):

  'rule' Concat_channel_fits(channel_fit(I, I1, F1), F2 -> channel_fit(I, I1, F)):
	 Concat_channel_fits(F1, F2 -> F) 

  'rule' Concat_channel_fits(nil, F -> F):

'action' Concat_object_fits(OBJECT_FITS, OBJECT_FITS -> OBJECT_FITS)

  'rule' Concat_object_fits(F, nil -> F):

  'rule' Concat_object_fits(object_fit(I, I1, K, F1), F2 -> F):
	 Concat_object_fits(F1, F2 -> F3)
	 (|
	   Isin_object_fits(I, F3)
	   where(F3 -> F)
	 ||
	   where(object_fit(I, I1, K, F3) -> F)
	 |)

  'rule' Concat_object_fits(nil, F -> F):

'condition' Isin_object_fits(Object_id, OBJECT_FITS)

  'rule' Isin_object_fits(I, object_fit(I1, _, _, F)):
	 (| eq(I, I1) || Isin_object_fits(I, F) |)

'action' Add_embedded_fittings(OBJECT_FITS, IMP_FIT -> IMP_FIT)

  'rule' Add_embedded_fittings(object_fit(_, _, form_act, OF), IF -> IF1):
	 Add_embedded_fittings(OF, IF -> IF1)

  'rule' Add_embedded_fittings(object_fit(_, nil, _, OF), IF -> IF1):
	 Add_embedded_fittings(OF, IF -> IF1)

  'rule' Add_embedded_fittings(object_fit(Old, object_id(New), embedded, OF), IF -> IF1): 
-- debug
-- Putmsg("Calling Add_embedded_fittings for object ")
-- Old'Ident -> Id
-- Print_id(Id)
-- Putnl()
	 New'Env -> E1
	 Get_env_adapts(E1 -> AD)
	 Remove_hides(AD -> AD1)
	 Set_env_adapts(E1, AD1 -> E11)
	 Old'Env -> E2
	 where(IF -> imp_fit(TYPF,_,_,_,OBJF))
	 Make_type_fits(E2, E11, nil -> TYPF1)
	 Concat_type_fits(TYPF1, TYPF -> TYPF2)
	 Make_imp_fit(E2, E11, nil, TYPF2, OBJF -> IF2)
	 Add_embedded_fittings(OF, IF -> IF3)
	 Concat_imp_fits(IF2, IF3 -> IF1)
-- debug
-- Putmsg("Add_embedded_fittings returns for object ")
-- Print_id(Id)
-- Putmsg(": ")
-- print(IF1)

  'rule' Add_embedded_fittings(nil, IF -> IF):
	 
'action' Delete_object_fit(Object_id, OBJECT_FITS -> OBJECT_FITS)

  'rule' Delete_object_fit(OI, object_fit(I, I1, K, F1) -> F1):
	 eq(OI, I)

  'rule' Delete_object_fit(OI, object_fit(I, I1, K, F1) -> object_fit(I, I1, K, F2)):
	 Delete_object_fit(OI, F1 -> F2)

-- First fitting is the one used to generate conditions
-- Second is used to fit expressions
'action' CCImplementation(POS, IMP_FIT, IMP_FIT, AXIOM_ENV, AXIOM_ENV -> VALUE_EXPR)

  'rule' CCImplementation(P, IF0, IF, OLDAX, NEWAX -> VE):
	 where(IF0 -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Type_imp(P, TYPF, IF -> VE1L)
	 Reassociate(P, VE1L -> VE1R)
	 Value_imp(P, VALF, IF -> VE2L)
	 Reassociate(P, VE2L -> VE2R)
	 Variable_imp(P, VARF, IF -> VE3L)
	 Reassociate(P, VE3L -> VE3R)
	 Channel_imp(P, CHF, IF -> VE4L)
	 Reassociate(P, VE4L -> VE4R)
	 Object_imp(P, OBJF, IF -> VE5L)
	 Reassociate(P, VE5L -> VE5R)
	 Axiom_imp(P, OLDAX, NEWAX, IF -> VE6L)
	 Reassociate(P, VE6L -> VE6R)
	 Conjoin_conds(P,VE5R,VE6R -> VE56)
	 Conjoin_conds(P,VE4R,VE56 -> VE456)
	 Conjoin_conds(P,VE3R,VE456 -> VE3456)
	 Conjoin_conds(P,VE2R,VE3456 -> VE23456)
	 Conjoin_conds(P,VE1R,VE23456 -> VE)

'action' Type_imp(POS, TYPE_FITS, IMP_FIT -> VALUE_EXPR)

  'rule' Type_imp(P, type_fit(Old, type_id(New), TF), IF -> ax_infix(P, VE2, and, VE1, P)):
	 Old'Def -> T
	 (|
	   where(T -> abbreviation(T1))
-- debug
-- Putmsg("Old type abbreviation for ")
-- Print_type(T1)
-- Putnl()
-- print(T1)
	   Fit_type(T1, IF -> T2)
-- Putmsg("fitted to ")
-- Print_type(T2)
-- Putnl()
-- print(T2)
-- Putmsg("with fitting")
-- Putnl()
-- print(IF)
-- Putmsg("New type ")
-- Print_type(defined(New, nil))
-- Putnl()
-- print(defined(New, nil))
	   (|
	     Same_type(T2, defined(New, nil), IF)
	     where(no_val -> VE1)
	   ||
	     Set_of_type(P, defined(New, nil) -> S1)
	     Set_of_type(P, T2 -> S2)
	     Id_of_eq -> Ieq
	     where(VALUE_EXPR'infix_occ(P, S1, Ieq, nil, S2) -> VE11)
	     New'Pos -> P1
	     where(cc_expr(pos(P1), "IC: type definition changed", nil, VE11) -> VE1) 
	   |)
	 ||
	   where(no_val -> VE1)
	 |)
	 Type_imp(P, TF, IF -> VE2)

  'rule' Type_imp(P, type_fit(Old, nil, TF), IF -> ax_infix(P, VE2, and, VE1, P)):
	 Old'Pos -> P1
	 Old'Ident -> Id
	 id_to_string(Id -> STR)
	 Concatenate3("IC: type ", STR, " hidden and not implemented" -> STR1)
	 where(cc_expr(pos(P1), STR1, nil, literal_expr(P, bool_false)) -> VE1)
	 Type_imp(P, TF, IF -> VE2)

  'rule' Type_imp(P, nil, _ -> no_val):

'action' Value_imp(POS, VALUE_FITS, IMP_FIT -> VALUE_EXPR)

  'rule' Value_imp(P, value_fit(Old, value_id(New), VF), IF -> ax_infix(P, VE2, and, VE1, P)):
	 Old'Type -> T
	 New'Type -> T1
	 Fit_type(T, IF -> T2)
	 New'Pos -> P1
	 (|
	   Static_subtype(T1, T2)
	   where(no_val -> VE11)
	   where(pos(P1) -> P2)
	 ||
	   Isin_subtype(val_occ(P, New, nil), T2 -> VE111)
	   where(cc_expr(pos(P1), "IC: type of value changed", nil, VE111) -> VE11)
	   where(no_pos -> P2)
	 |)
	 Old'Def -> Def
	 New'Def -> Def1
	 Value_implements(P, P2, Old, Def, New, Def1, IF -> VE12)
	 where(ax_infix(P,VE11,and,VE12,P) -> VE1)
	 Value_imp(P, VF, IF -> VE2)

  'rule' Value_imp(P, value_fit(Old, nil, TF), IF -> ax_infix(P, VE2, and, VE1, P)):
	 Old'Pos -> P1
	 Old'Ident -> Id
	 (|
	   where(Id -> id_op(Id1))
	   id_to_string(Id1 -> STR)
	 ||
	   where(Id -> op_op(Op))
	   Op_to_print_string(Op -> STR)
	 |)
	 Concatenate3("IC: value ", STR, " hidden and not implemented" -> STR1)
	 where(cc_expr(pos(P1), STR1, nil, literal_expr(P, bool_false)) -> VE1)
	 Value_imp(P, TF, IF -> VE2)

  'rule' Value_imp(P, nil, _ -> no_val):

'action' Variable_imp(POS, VARIABLE_FITS, IMP_FIT -> VALUE_EXPR)

  'rule' Variable_imp(P, variable_fit(Old, variable_id(New), VF), IF -> ax_infix(P, VE2, and, VE1, P)):
	 Old'Type -> T
	 Fit_type(T, IF -> T2)
	 New'Type -> T1
	 New'Pos -> P1
	 (|
	   Same_type(T2, T1, IF)
	   where(no_val -> VE11)
	   where(pos(P1) -> P2)
	 ||
	   Set_of_type(P, T1 -> S1)
	   Set_of_type(P, T2 -> S2)
	   Id_of_eq -> Ieq
	   where(VALUE_EXPR'infix_occ(P, S1, Ieq, nil, S2) -> VE111) 
	   where(cc_expr(pos(P1), "IC: type of variable changed", nil, VE111) -> VE11)
	   where(no_pos -> P2)
	 |)
	 (|
	   Old'Init -> initial(E)
	   Fit_expr(E, IF -> E2)
	   (|
	     New'Init -> initial(E1)
	     (|
	       Same_expr(E2, E1, IF)
	       where(VE11 -> VE1)
	     ||
	       Id_of_eq -> Ieq
	       where(VALUE_EXPR'infix_occ(P, E2, Ieq, nil, E1) -> VE121)
	       where(cc_expr(P2, "IC: initial value of variable changed", nil, VE121) -> VE12)
	       where(ax_infix(P, VE11, and, VE12, P) -> VE1)
	     |)
	   ||
	     where(stmt_infix(P, initialise(P, nil), sequence, ass_occ(P, New, nil, E2)) -> L)
	     where(initialise(P, nil) -> R)
	     where(always(P,equivalence(P, L, R, nil)) -> VE121)
	     where(cc_expr(P2, "IC: no initialisation of variable", nil, VE121) -> VE12)
	     where(ax_infix(P, VE11, and, VE12, P) -> VE1)
	   |)
	 ||
	   where(VE11 -> VE1)
	 |)
	 Variable_imp(P, VF, IF -> VE2)

  'rule' Variable_imp(P, variable_fit(Old, nil, TF), IF -> ax_infix(P, VE2, and, VE1, P)):
	 Old'Pos -> P1
	 Old'Ident -> Id
	 id_to_string(Id -> STR)
	 Concatenate3("IC: variable ", STR, " hidden and not implemented" -> STR1)
	 where(cc_expr(pos(P1), STR1, nil, literal_expr(P, bool_false)) -> VE1)
	 Variable_imp(P, TF, IF -> VE2)

  'rule' Variable_imp(P, nil, _ -> no_val):

'action' Channel_imp(POS, CHANNEL_FITS, IMP_FIT -> VALUE_EXPR)

  'rule' Channel_imp(P, channel_fit(Old, channel_id(New), CF), IF -> ax_infix(P, VE2, and, VE1, P)):
	 Old'Type -> T
	 Fit_type(T, IF -> T2)
	 New'Type -> T1
	 (|
	   Same_type(T2, T1, IF)
	   where(no_val -> VE1)
	 ||
	   Set_of_type(P, T1 -> S1)
	   Set_of_type(P, T2 -> S2)
	   Id_of_eq -> Ieq
	   where(VALUE_EXPR'infix_occ(P, S1, Ieq, nil, S2) -> VE11) 
	   New'Pos -> P1
	   where(cc_expr(pos(P1), "IC: type of variable changed", nil, VE11) -> VE1) 
	 |)
	 Channel_imp(P, CF, IF -> VE2)

  'rule' Channel_imp(P, channel_fit(Old, nil, TF), IF -> ax_infix(P, VE2, and, VE1, P)):
	 Old'Pos -> P1
	 Old'Ident -> Id
	 id_to_string(Id -> STR)
	 Concatenate3("IC: channel ", STR, " hidden and not implemented" -> STR1)
	 where(cc_expr(pos(P1), STR1, nil, literal_expr(P, bool_false)) -> VE1)
	 Channel_imp(P, TF, IF -> VE2)

  'rule' Channel_imp(P, nil, _ -> no_val):

'action' Object_imp(POS, OBJECT_FITS, IMP_FIT -> VALUE_EXPR)

  'rule' Object_imp(P, object_fit(_, _, form_act, OF), IF -> VE):
	 Object_imp(P, OF, IF -> VE)

  'rule' Object_imp(P, object_fit(Old, object_id(New), embedded, OF), IF -> ax_infix(P, VE0, and, ax_infix(P, VE2, and, VE1, P), P)):
	 New'Pos -> P1
	 New'Env -> E1
	 Old'Env -> E2
	 (|
	   Old'Params -> param_type(T)
	   New'Params -> param_type(T1)
	   Fit_type(T, IF -> T2)
	   (|
	     Static_subtype(T2, T1)
	     where(no_val -> VE0)
	   ||
	     Set_of_type(P, T1 -> S1)
	     Set_of_type(P, T2 -> S2)
	     Id_of_subseteq -> Isubseteq
	     where(VALUE_EXPR'infix_occ(P, S2, Isubseteq, nil, S1) -> VE00)
	     where(cc_expr(pos(P1), "IC: parameter type changed", nil, VE00) -> VE0)
	   |)
	 ||
	   where(no_val -> VE0)
	 |)
	 Get_env_adapts(E1 -> AD)
	 Remove_hides(AD -> AD1)
	 Set_env_adapts(E1, AD1 -> E11)
	 -- types, values, variables, channels done already
	 -- Make_type_fits(E2, E11, nil -> TYPF1)
	 -- Make_imp_fit(E2, E11, nil, lower, TYPF1, nil -> IF1)
	 where(imp_fit(nil,nil,nil,nil,nil) -> IF1)
	 Get_env_axioms(E2 -> OLDAX)
-- debug
-- Putmsg("Checking for object ")
-- Old'Ident -> Id
-- Print_id(Id)
-- Putnl()
-- Putmsg("Axioms: ")
-- Print_axiom_env(OLDAX)
-- Putnl()
	 Get_env_axioms(E11 -> NEWAX)
	 CCImplementation(P, IF1, IF, OLDAX, NEWAX -> VE1)
	 Object_imp(P, OF, IF -> VE2)

  'rule' Object_imp(P, object_fit(Old, nil, _, TF), IF -> ax_infix(P, VE2, and, VE1, P)):
	 Old'Pos -> P1
	 Old'Ident -> Id
	 id_to_string(Id -> STR)
	 Concatenate3("IC: object ", STR, " hidden and not implemented" -> STR1)
	 where(cc_expr(pos(P1), STR1, nil, literal_expr(P, bool_false)) -> VE1)
	 Object_imp(P, TF, IF -> VE2)

  'rule' Object_imp(P, nil, _ -> no_val):

'action' Axiom_imp(POS, AXIOM_ENV, AXIOM_ENV, IMP_FIT -> VALUE_EXPR)

  'rule' Axiom_imp(P, axiom_env(I, OldAx), NewAx, IF -> ax_infix(P, VE2, and, VE1, P)):
	 I'Axiom -> E
	 Fit_expr(E, IF -> E2)
	 (|
	   Axiom_occurs(E2, NewAx, IF)
	   where(no_val -> VE1)
	 ||
	   I'Pos -> P1
	   I'Ident -> Oid
	   (|
	     where(Oid -> ident(Id))
	     Axiom_name_to_string(Id -> STR1)
	     Concatenate3("IC: ", STR1, "" -> STR)
	   ||
	     where("IC: axiom" -> STR)
	   |)
	   where(cc_expr(pos(P1), STR, Oid, E2) -> VE1)
	 |)
	 Axiom_imp(P, OldAx, NewAx, IF -> VE2)

  'rule' Axiom_imp(_, nil, _, _ -> no_val):

'condition' Axiom_occurs(VALUE_EXPR, AXIOM_ENV, IMP_FIT)

  'rule' Axiom_occurs(E, axiom_env(I, Env), IF):
	 (|
	   I'Axiom -> E1
	   Same_expr(E, E1, IF)
	 ||
	   Axiom_occurs(E, Env, IF)
	 |)

'action' Reassociate(POS, VALUE_EXPR -> VALUE_EXPR)

  'rule' Reassociate(P, ax_infix(_, ax_infix(_, E1, and, E2, _), and, E3, PE3) -> E):
	 Reassociate(P, ax_infix(P, E1, and, ax_infix(P, E2, and, E3, PE3), PE3) -> E)

  'rule' Reassociate(_, E -> E):

'action' Conjoin_conds(POS, VALUE_EXPR, VALUE_EXPR -> VALUE_EXPR)

  'rule' Conjoin_conds(P, ax_infix(_, E1, and, E2, PE2), E3 -> ax_infix(P, E1, and, E23, PE2)):
	 Conjoin_conds(P, E2, E3 -> E23)

  'rule' Conjoin_conds(P, E1, E2 -> ax_infix(P, E1, and, E2, P)):

'action' Set_of_type(POS, TYPE_EXPR -> VALUE_EXPR)

  'rule' Set_of_type(P, T -> comp_set(P, val_occ(P, I, nil), set_limit(P, list(single(P,single(P,id_op(X)),T),nil), nil))):
	 string_to_id("x_" -> X)
	 New_value_id(P, id_op(X) -> I)
	 [|
	   CPPWanted()
	   Localise_value_id(I)
	 |]
	 I'Type <- T

'action' Value_implements(POS, OPT_POS, Value_id, VALUE_DEFINITION, Value_id, VALUE_DEFINITION, IMP_FIT -> VALUE_EXPR)

  'rule' Value_implements(_, _, _, no_def, _, _, _ -> no_val):

  'rule' Value_implements(P, OP, I, expl_val(EV,_), I1, Def, IF -> VE):
	 (|
	   where(EV -> disamb(_, E, _))
	 ||
	   where(EV -> E)
	 |)
	 Fit_expr(E, IF -> E2)
	 (|
	   where(Def -> expl_val(E1,_))
	   Same_expr(E2, E1, IF)
	   where(no_val -> VE)
	 ||
-- debug
-- Putmsg("Old value def ")
-- Putnl()
-- print(E)
-- Putmsg("fitted to ")
-- Putnl()
-- print(E2)
-- Putmsg("with fitting")
-- Putnl()
-- print(IF)
-- Putmsg("New def ")
-- Putnl()
-- (|
-- where(Def -> expl_val(E1),_)
-- print(E1)
-- ||
-- print(val_occ(P, I1, nil))
-- |)
	   Id_of_eq -> Ieq
	   where(VALUE_EXPR'infix_occ(P, val_occ(P, I1, nil), Ieq, nil, E2) -> VE1)
	   where(cc_expr(OP, "IC: value definition changed", nil, VE1) -> VE)
	 |)

  'rule' Value_implements(P, OP, I, impl_val(E), I1, Def, IF -> VE):
	 Fit_expr(E, IF -> E2)
	 (|
	   where(Def -> impl_val(E1))
	   Same_expr(E2, E1, IF)
	   where(no_val -> VE)
	 ||
	   where(cc_expr(OP, "IC: value definition changed", nil, E2) -> VE)
	 |)

  'rule' Value_implements(P, OP, I, expl_fun(PARMS, E, POST, PRE, _, _), I1, Def, IF -> VE):
-- POST TODO
	 Fit_expr(E, IF -> E2)
	 (|
	   where(PRE -> pre_cond(P2, VPRE))
	   Fit_expr(VPRE, IF -> VPRE2)
	   where(pre_cond(P2, VPRE2) -> PRE2)
	 ||
	   where(PRE_CONDITION'nil -> PRE2)
	 |)
	 (|
	   where(Def -> expl_fun(PARMS1, E1, POST1, PRE1, _, _))
	   Same_parms(PARMS, PARMS1)
-- debug
-- (|
-- Same_expr(E2, E1, IF)
-- ||
-- Putmsg("Fitting: ")
-- print(IF)
-- Putmsg("Exprs: ")
-- print(E)
-- Putmsg("Fitted to ")
-- print(E2)
-- print(E1)
-- |)
-- (|
-- Same_precond(PRE2, PRE1, IF)
-- ||
-- Putmsg("Preconds: ")
-- print(PRE2)
-- print(PRE1)
-- |)
	   Same_expr(E2, E1, IF)
	   Same_precond(PRE2, PRE1, IF)
	   Nil_or_same_postcond(POST, POST1, IF)
	   where(no_val -> VE)
	 ||
	   I'Type -> T
	   Fit_type(T, IF -> T2)
	   Parms_to_typings(PARMS, T2 -> TPS)
	   Formals_to_actuals(PARMS, T2 -> ACTS)
	   Make_application(P, I1, ACTS -> APP)
	   where(equivalence(P, APP, E2, PRE2) -> COND)
	   (|
	     where(POST -> post(post_cond(_, RN, PC)))
	     Fit_expr(PC, IF -> PC2)
	     where(VALUE_EXPR'post(P, APP, post_cond(P, RN, PC2), PRE2) -> COND2)
	     where(ax_infix(P, bracket(P, COND),
			       and,
			       bracket(P, COND2), P) -> COND1)
	   ||
	     where(COND -> COND1)
	   |)
	   (|
	     eq(TPS, nil)
	     where(COND1 -> VE1)
	   ||
	     where(quantified(P, all, TPS, restriction(P, COND1)) -> VE1)
	   |)
	   where(cc_expr(OP, "IC: value definition changed", nil, VE1) -> VE)
	 |)

  'rule' Value_implements(P, OP, I, impl_fun(PARMS, post_cond(_,RN, E), PRE, _), I1, Def, IF -> VE):
	 Fit_expr(E, IF -> E2)
	 (|
	   where(PRE -> pre_cond(P2, VPRE))
	   Fit_expr(VPRE, IF -> VPRE2)
	   where(pre_cond(P2, VPRE2) -> PRE2)
	 ||
	   where(PRE_CONDITION'nil -> PRE2)
	 |)
	 (|
	   where(Def -> impl_fun(PARMS1, post_cond(_,RN1, E1), PRE1, _))
	   Same_parms(PARMS, PARMS1)
	   Same_result_naming(RN, RN1)
	   Same_expr(E2, E1, IF)
	   Same_precond(PRE2, PRE1, IF)
	   where(no_val -> VE)
	 ||
	   I'Type -> T
	   Fit_type(T, IF -> T2)
	   Parms_to_typings(PARMS, T2 -> TPS)
	   Formals_to_actuals(PARMS, T2 -> ACTS)
	   Make_application(P, I1, ACTS -> APP)
	   where(VALUE_EXPR'post(P, APP, post_cond(P, RN, E2), PRE2) -> COND)
	   (|
	     eq(TPS, nil)
	     where(COND -> VE1)
	   ||
	     where(quantified(P, all, TPS, restriction(P, COND)) -> VE1)
	   |)
	   where(cc_expr(OP, "IC: value definition changed", nil, VE1) -> VE)
	 |)

'action' Parms_to_typings(FORMAL_FUNCTION_PARAMETERS, TYPE_EXPR -> TYPINGS)

  'rule' Parms_to_typings(list(form_parm(P,BS), PS), T -> TPS):
	 Split_fun_type(T -> T1, T2)
	 Bindings_to_typing(P, BS, T1 -> TP)
	 Parms_to_typings(PS, T2 -> TPS1)
	 (|
	   eq(BS, nil)
	   -- Unit type parameter - ignore
	   where(TPS1 -> TPS)
	 ||
	   where(TYPINGS'list(TP, TPS1) -> TPS)
	 |)

  'rule' Parms_to_typings(nil, _ -> nil):

'action' Bindings_to_typing(POS, BINDINGS, TYPE_EXPR -> TYPING)

  'rule' Bindings_to_typing(P, list(B,nil), T -> single(P, B, T)):

  'rule' Bindings_to_typing(P, BS, T -> single(P, product(P, BS), T)):

'action' Formals_to_actuals(FORMAL_FUNCTION_PARAMETERS, TYPE_EXPR -> ACTUAL_FUNCTION_PARAMETERS)

  'rule' Formals_to_actuals(list(F, FS), T -> list(A, AS)):
	 Split_fun_type(T -> T1, T2)
	 Formal_to_actual(F, T1 -> A)
	 Formals_to_actuals(FS, T2 -> AS)

  'rule' Formals_to_actuals(nil, _ -> nil):

'action' Formal_to_actual(FORMAL_FUNCTION_PARAMETER, TYPE_EXPR -> ACTUAL_FUNCTION_PARAMETER)

  'rule' Formal_to_actual(form_parm(P, list(B, nil)), T -> fun_arg(P, list(E, nil))):
	 Binding_to_expr(B, T -> E)

  'rule' Formal_to_actual(form_parm(P, BS), T -> fun_arg(P1, ES)):
	 Binding_to_expr(product(P, BS), T -> product(P1, ES))

'action' Bindings_to_exprs(BINDINGS, PRODUCT_TYPE -> VALUE_EXPRS)

  'rule' Bindings_to_exprs(list(B, BS), list(T, TS) -> list(E, ES)):
	 Binding_to_expr(B, T -> E)
	 Bindings_to_exprs(BS, TS -> ES)

  'rule' Bindings_to_exprs(nil, _ -> nil):

'action' Binding_to_expr(BINDING, TYPE_EXPR -> VALUE_EXPR)

  'rule' Binding_to_expr(single(P, Id), T -> val_occ(P, I, nil)):
	 New_value_id(P, Id -> I)
	 I'Type <- T

  'rule' Binding_to_expr(product(P, BS), T -> product(P, ES)):
	 Length_bs(BS -> N)
	 Make_product_type(T, N -> product(XT))
	 Bindings_to_exprs(BS, XT -> ES)

'action' Make_application(POS, Value_id, ACTUAL_FUNCTION_PARAMETERS -> VALUE_EXPR)

  'rule' Make_application(P, I, ACTS -> APP):
	 I'Ident -> Id_or_op
	 (|
	   where(Id_or_op -> id_op(Id))
	   where(VALUE_EXPR'application(P, val_occ(P, I, nil), ACTS) -> APP)
	 ||
	   where(Id_or_op -> op_op(Op))
	   (|
	     where(ACTS -> list(fun_arg(_, list(E, nil)), nil))
	     where(VALUE_EXPR'prefix_occ(P, I, nil, E) -> APP)
	   ||
	     where(ACTS -> list(fun_arg(_, list(L, list(R, nil))), nil))
	     where(VALUE_EXPR'infix_occ(P, L, I, nil, R) -> APP)
	   |)
	 |)

'action' Fit_type(TYPE_EXPR, IMP_FIT -> TYPE_EXPR)

  'rule' Fit_type(unit, _ -> unit):
	 
  'rule' Fit_type(bool, _ -> bool):
	 
  'rule' Fit_type(int, _ -> int):
	 
  'rule' Fit_type(nat, _ -> nat):
	 
  'rule' Fit_type(real, _ -> real):
	 
  'rule' Fit_type(text, _ -> text):
	 
  'rule' Fit_type(char, _ -> char):
	 
  'rule' Fit_type(time, _ -> time):

  'rule' Fit_type(defined(I, Q), imp_fit(TYPF, VALF, VARF, CHF, OBJF) -> defined(I2, Q2)):
	 Fit_opt_qualification(Q, imp_fit(TYPF, VALF, VARF, CHF, OBJF) -> Q2)
	 Fit_type_id(I, TYPF -> I2)
 

  'rule' Fit_type(product(TS), IF -> product(TS2)):
	 Fit_product_type(TS, IF -> TS2)

  'rule' Fit_type(fin_set(T), IF -> fin_set(T2)):
	 Fit_type(T, IF -> T2)
	 
  'rule' Fit_type(infin_set(T), IF -> infin_set(T2)):
	 Fit_type(T, IF -> T2)
	 
  'rule' Fit_type(fin_list(T), IF -> fin_list(T2)):
	 Fit_type(T, IF -> T2)
	 
  'rule' Fit_type(infin_list(T), IF -> infin_list(T2)):
	 Fit_type(T, IF -> T2)
	 
  'rule' Fit_type(fin_map(D, R), IF -> fin_map(D2, R2)):
	 Fit_type(D, IF -> D2)
	 Fit_type(R, IF -> R2)
	 
  'rule' Fit_type(infin_map(D, R), IF -> infin_map(D2, R2)):
	 Fit_type(D, IF -> D2)
	 Fit_type(R, IF -> R2)

  'rule' Fit_type(fun(D, A, R), IF -> fun(D2, A, R2)):
	 Fit_type(D, IF -> D2)
	 Fit_result(R, IF -> R2)

  'rule' Fit_type(bracket(T), IF -> bracket(T2)):
	 Fit_type(T, IF -> T2)

  'rule' Fit_type(subtype(TP, R), IF -> subtype(TP1, R1))
	 Fit_typing(TP, IF -> TP1)
	 Fit_restriction(R, IF -> R1)
	 
'action' Fit_product_type(PRODUCT_TYPE, IMP_FIT -> PRODUCT_TYPE)

  'rule' Fit_product_type(list(T, TS), IF -> list(T2, TS2)):
	 Fit_type(T, IF -> T2)
	 Fit_product_type(TS, IF -> TS2)

  'rule' Fit_product_type(nil, _ -> nil):

'action' Fit_result(RESULT, IMP_FIT -> RESULT)

  'rule' Fit_result(result(T, RD, WR, IN, OUT), IF -> result(T2, RD2, WR2, IN2, OUT2)):
	 Fit_type(T, IF -> T2)
	 Fit_accs(RD, IF -> RD2)
	 Fit_accs(WR, IF -> WR2)
	 Fit_accs(IN, IF -> IN2)
	 Fit_accs(OUT, IF -> OUT2)

'action' Fit_accs(ACCESSES, IMP_FIT -> ACCESSES)

  'rule' Fit_accs(list(A, AS), IF -> list(A2, AS2)):
	 Fit_acc(A, IF -> A2)
	 Fit_accs(AS, IF -> AS2)

  'rule' Fit_accs(nil, _ -> nil):

'condition' Fit_acc(ACCESS, IMP_FIT -> ACCESS)

  'rule' Fit_acc(enumerated_access(P, AS), IF -> enumerated_access(P, AS2)):
	 Fit_accs(AS, IF -> AS2)

  'rule' Fit_acc(completed_access(P, nil), _ -> completed_access(P, nil)):
  
  'rule' Fit_acc(completed_access(P, qualification(Obj)), IF -> completed_access(P, qualification(Obj2))):
	 Fit_object(Obj, IF -> Obj2)

  'rule' Fit_acc(comprehended_access(P, A, set_limit(P1, TPS, R)), IF -> comprehended_access(P, A2, set_limit(P1, TPS2, R2))):
	 Fit_acc(A, IF -> A2)
	 Fit_typings(TPS, IF -> TPS2)
	 Fit_restriction(R, IF -> R2)

  'rule' Fit_acc(variable(P, I, Q), IF -> variable(P, I2, Q2)):
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_variable_id(I, VARF -> I2)
	 Fit_opt_qualification(Q, IF -> Q2)

  'rule' Fit_acc(channel(P, I, Q), IF -> channel(P, I2, Q2)):
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_channel_id(I, CHF -> I2)
	 Fit_opt_qualification(Q, IF -> Q2)

'condition' Same_parms(FORMAL_FUNCTION_PARAMETERS, FORMAL_FUNCTION_PARAMETERS)

  'rule' Same_parms(list(form_parm(_,P), PS), list(form_parm(_,P1), PS1)):
	 Same_bindings(P, P1)
	 Same_parms(PS, PS1)

  'rule' Same_parms(nil, nil):

'condition' Same_type(TYPE_EXPR, TYPE_EXPR, IMP_FIT)

  'rule' Same_type(unit, unit, _):
	 
  'rule' Same_type(bool, bool, _):
	 
  'rule' Same_type(int, int, _):
	 
  'rule' Same_type(nat, nat, _):
	 
  'rule' Same_type(real, real, _):
	 
  'rule' Same_type(text, text, _):
	 
  'rule' Same_type(char, char, _):
	 
  'rule' Same_type(time, time, _):

  'rule' Same_type(defined(I, _), defined(I1, _), _):
	 eq(I, I1)
	 
  'rule' Same_type(T, defined(I1, _), IF):
	 I1'Def -> abbreviation(T1)
	 Same_type(T, T1, IF)

  'rule' Same_type(defined(I, _), T1, IF):
	 I'Def -> abbreviation(T)
	 Same_type(T, T1, IF)

  'rule' Same_type(product(TS), product(TS1), IF):
	 Same_product_type(TS, TS1, IF)

  'rule' Same_type(fin_set(T), fin_set(T1), IF):
	 Same_type(T, T1, IF)
	 
  'rule' Same_type(infin_set(T), infin_set(T1), IF):
	 Same_type(T, T1, IF)
	 
  'rule' Same_type(fin_list(T), fin_list(T1), IF):
	 Same_type(T, T1, IF)
	 
  'rule' Same_type(infin_list(T), infin_list(T1), IF):
	 Same_type(T, T1, IF)
	 
  'rule' Same_type(fin_map(D, R), fin_map(D1, R1), IF):
	 Same_type(D, D1, IF)
	 Same_type(R, R1, IF)
	 
  'rule' Same_type(infin_map(D, R), infin_map(D1, R1), IF):
	 Same_type(D, D1, IF)
	 Same_type(R, R1, IF)

  'rule' Same_type(fun(D, A, R), fun(D1, A1, R1), IF):
	 eq(A, A1)
	 Same_type(D, D1, IF)
	 Same_result(R, R1, IF)

  'rule' Same_type(bracket(T), T1, IF):
	 Same_type(T, T1, IF)

  'rule' Same_type(T, bracket(T1), IF):
	 Same_type(T, T1, IF)

  'rule' Same_type(subtype(TP, R), subtype(TP1, R1), IF):
	 Same_typing(TP, TP1, IF)
	 Same_restriction(R, R1, IF)
 

'condition' Same_product_type(PRODUCT_TYPE, PRODUCT_TYPE, IMP_FIT)

  'rule' Same_product_type(list(T, TS), list(T1, TS1), IF):
	 Same_type(T, T1, IF)
	 Same_product_type(TS, TS1, IF)

  'rule' Same_product_type(nil, nil, _):

'condition' Same_result(RESULT, RESULT, IMP_FIT)

  'rule' Same_result(result(T, RD, WR, IN, OUT), result(T1, RD1, WR1, IN1, OUT1), IF):
	 Same_type(T, T1, IF)
	 Same_accs(RD, RD1)
	 Same_accs(WR, WR1)
	 Same_accs(IN, IN1)
	 Same_accs(OUT, OUT1)

'condition' Same_accs(ACCESSES, ACCESSES)

  'rule' Same_accs(list(A, AS), list(A1, AS1)):
	 Same_acc(A, A1)
	 Same_accs(AS, AS1)

  'rule' Same_accs(nil, nil):

'condition' Same_acc(ACCESS, ACCESS)

  'rule' Same_acc(enumerated_access(_, AS), enumerated_access(_, AS1)):
	 Same_accs(AS, AS1)

  'rule' Same_acc(completed_access(_, nil), completed_access(_, nil)):
  
  'rule' Same_acc(completed_access(_, qualification(Obj)), completed_access(_, qualification(Obj1))):
	 Id_of_object(Obj -> I)
	 Id_of_object(Obj1 -> I1)
	 eq(I, I1)

  'rule' Same_acc(variable(_, I,_), variable(_, I1,_)):
	 eq(I, I1)

  'rule' Same_acc(channel(_, I,_), channel(_, I1,_)):
	 eq(I, I1)

'condition' Same_expr(VALUE_EXPR, VALUE_EXPR, IMP_FIT)

  'rule' Same_expr(literal_expr(_, L), literal_expr(_, L1), _):
	 Same_literal(L, L1)

  'rule' Same_expr(chaos(_), chaos(_), _):

  'rule' Same_expr(skip(_), skip(_), _):

  'rule' Same_expr(stop(_), stop(_), _):

  'rule' Same_expr(swap(_), swap(_), _):

  'rule' Same_expr(product(_, VS), product(_, VS1), IF):
	 Same_exprs(VS, VS1, IF)

  'rule' Same_expr(ranged_set(_, L, R), ranged_set(_, L1, R1), IF):
	 Same_expr(L, L1, IF)
	 Same_expr(R, R1, IF)

  'rule' Same_expr(enum_set(_, VS), enum_set(_, VS1), IF):
	 Same_exprs(VS, VS1, IF)

  'rule' Same_expr(comp_set(_, E, set_limit(_, TPS, R)), comp_set(_, E1, set_limit(_, TPS1, R1)), IF):
	 Same_expr(E, E1, IF)
	 Same_typings(TPS, TPS1, IF)
	 Same_restriction(R, R1, IF)
	 
  'rule' Same_expr(ranged_list(_, L, R), ranged_list(_, L1, R1), IF):
	 Same_expr(L, L1, IF)
	 Same_expr(R, R1, IF)

  'rule' Same_expr(enum_list(_, VS), enum_list(_, VS1), IF):
	 Same_exprs(VS, VS1, IF)

  'rule' Same_expr(comp_list(_, E, list_limit(_, B, V, R)), comp_list(_, E1, list_limit(_, B1, V1, R1)), IF):
	 Same_expr(E, E1, IF)
	 Same_binding(B, B1)
	 Same_expr(V, V1, IF)
	 Same_restriction(R, R1, IF)

  'rule' Same_expr(enum_map(_, PRS), enum_map(_, PRS1), IF):
	 Same_pairs(PRS, PRS1, IF)

  'rule' Same_expr(comp_map(_, pair(L,R), set_limit(_, TPS, REST)), comp_map(_, pair(L1,R1), set_limit(_, TPS1, REST1)), IF):
	 Same_expr(L, L1, IF)
	 Same_expr(R, R1, IF)
	 Same_typings(TPS, TPS1, IF)
	 Same_restriction(REST, REST1, IF)

  'rule' Same_expr(function(_, P, E), function(_, P1, E1), IF):
	 Same_lambda_parameter(P, P1, IF)
	 Same_expr(E, E1, IF)

  'rule' Same_expr(application(_, E, AS), application(_, E1, AS1), IF):
	 Same_expr(E, E1, IF)
	 Same_args(AS, AS1, IF)

  'rule' Same_expr(quantified(_, Q, TPS, R), quantified(_, Q1, TPS1, R1), IF):
	 eq(Q, Q1)
	 Same_typings(TPS, TPS1, IF)
	 Same_restriction(R, R1, IF)  

  'rule' Same_expr(equivalence(_, L, R, nil), equivalence(_, L1, R1, nil), IF):
	 Same_expr(L, L1, IF)
	 Same_expr(R, R1, IF)

  'rule' Same_expr(equivalence(_, L, R, pre_cond(_, PRE)), equivalence(_, L1, R1, pre_cond(_, PRE1)), IF):
	 Same_expr(L, L1, IF)
	 Same_expr(R, R1, IF)
	 Same_expr(PRE, PRE1, IF)

  'rule' Same_expr(post(_, E, C, P), post(_, E1, C1, P1), IF):
	 Same_expr(E, E1, IF)
	 Same_postcond(C, C1, IF)
	 Same_precond(P, P1, IF)

  'rule' Same_expr(disamb(_, E, _), E1, IF):
	 Same_expr(E, E1, IF)

  'rule' Same_expr(E, disamb(_, E1, _), IF):
	 Same_expr(E, E1, IF)

  'rule' Same_expr(bracket(_, E), E1, IF):
	 Same_expr(E, E1, IF)

  'rule' Same_expr(E, bracket(_, E1), IF):
	 Same_expr(E, E1, IF)

  'rule' Same_expr(ax_infix(_, L, C, R, _), ax_infix(_, L1, C1, R1, _), IF):
	 eq(C, C1)
	 Same_expr(L, L1, IF)
	 Same_expr(R, R1, IF)

  'rule' Same_expr(stmt_infix(_, L, C, R), stmt_infix(_, L1, C1, R1), IF):
	 eq(C, C1)
	 Same_expr(L, L1, IF)
	 Same_expr(R, R1, IF)

  'rule' Same_expr(always(_, E), always(_, E1), IF):
	 Same_expr(E, E1, IF)

  'rule' Same_expr(ax_prefix(_, C, E), ax_prefix(_, C1, E1), IF):
	 eq(C, C1)
	 Same_expr(E, E1, IF)

  'rule' Same_expr(comprehended(_, C, E, set_limit(_, TPS, R)), comprehended(_, C1, E1, set_limit(_, TPS1, R1)), IF):
	 eq(C, C1)
	 Same_expr(E, E1, IF)
	 Same_typings(TPS, TPS1, IF)
	 Same_restriction(R, R1, IF)

  'rule' Same_expr(initialise(_, nil), initialise(_, nil), _):

  'rule' Same_expr(initialise(_, qualification(Obj)), initialise(_, qualification(Obj1)), IF):
	 Same_object(Obj, Obj1, IF)

-- TODO local properly

  'rule' Same_expr(let_expr(_, DS, E), let_expr(_, DS1, E1), IF):
	 Same_let_defs(DS, DS1, IF)
	 Same_expr(E, E1, IF)

  'rule' Same_expr(if_expr(_, E, TH, _, ELSIF, EL), if_expr(_, E1, TH1, _, ELSIF1, EL1), IF):
	 Same_expr(E, E1, IF)
	 Same_expr(TH, TH1, IF)
	 Same_elsifs(ELSIF, ELSIF1, IF)
	 Same_else(EL, EL1, IF)

  'rule' Same_expr(case_expr(_, E, _, CS), case_expr(_, E1, _, CS1), IF):
	 Same_expr(E, E1, IF)
	 Same_cases(CS, CS1, IF)

  'rule' Same_expr(while_expr(_, G, E), while_expr(_, G1, E1), IF):
	 Same_expr(G, G1, IF)
	 Same_expr(E, E1, IF)
	 
  'rule' Same_expr(until_expr(_, E, G), until_expr(_, E1, G1), IF):
	 Same_expr(E, E1, IF)
	 Same_expr(G, G1, IF)

  'rule' Same_expr(for_expr(_, list_limit(_, B, V, R), E), for_expr(_, list_limit(_, B1, V1, R1), E1), IF):
	 Same_binding(B, B1)
	 Same_expr(V, V1, IF)
	 Same_restriction(R, R1, IF)
	 Same_expr(E, E1, IF)

  'rule' Same_expr(val_occ(_, I, Q),  val_occ(_, I1, Q1), IF):
	 (|
	   eq(I, I1)
	 ||
	   -- also accept same idents if types same and no qualifier
	   -- to allow for let, quantifers, etc.
	   I'Ident -> Id
	   I1'Ident -> Id1
	   Same_id_or_op(Id, Id1)
	   eq(Q, nil)
	   eq(Q1, nil)
	   I'Type -> T
	   I1'Type -> T1
	   Fit_type(T, IF -> T2)
	   Same_type(T2, T1, IF)
	 |)
	 
  'rule' Same_expr(var_occ(_, I, _),  var_occ(_, I1, _), _):
 print("Same_expr")
	 eq(I, I1)
	 
  'rule' Same_expr(pre_occ(_, I, _),  pre_occ(_, I1, _), _):
	 eq(I, I1)
	 
  'rule' Same_expr(infix_occ(_, L, I, _, R),  infix_occ(_, L1, I1, _, R1), IF):
	 eq(I, I1)
	 Same_expr(L, L1, IF)
	 Same_expr(R, R1, IF)
	 
  'rule' Same_expr(prefix_occ(_, I, _, R),  prefix_occ(_, I1, _, R1), IF):
	 eq(I, I1)
	 Same_expr(R, R1, IF)
	 
  'rule' Same_expr(ass_occ(_, I, _, E),	 ass_occ(_, I1, _, E1), IF):
	 eq(I, I1)
	 Same_expr(E, E1, IF)
	 
  'rule' Same_expr(input_occ(_, I, _),	input_occ(_, I1, _), _):
	 eq(I, I1)
	 
  'rule' Same_expr(output_occ(_, I, _, E),  output_occ(_, I1, _, E1), IF):
	 eq(I, I1)
	 Same_expr(E, E1, IF)

  'rule' Same_expr(no_val, no_val, _):

	 
'condition' Same_restriction(RESTRICTION, RESTRICTION, IMP_FIT)

  'rule' Same_restriction(restriction(_, E), restriction(_, E1), IF):
	 Same_expr(E, E1, IF)

  'rule' Same_restriction(nil, nil, _):

'condition' Same_exprs(VALUE_EXPRS, VALUE_EXPRS, IMP_FIT)

  'rule' Same_exprs(list(V, VS), list(V1, VS1), IF):
	 Same_expr(V, V1, IF)
	 Same_exprs(VS, VS1, IF)

  'rule' Same_exprs(nil, nil, _):


'condition' Same_pairs(VALUE_EXPR_PAIRS, VALUE_EXPR_PAIRS, IMP_FIT)

  'rule' Same_pairs(list(pair(L,R), PRS), list(pair(L1,R1), PRS1), IF):
	 Same_expr(L, L1, IF)
	 Same_expr(R, R1, IF)
	 Same_pairs(PRS, PRS1, IF)

  'rule' Same_pairs(nil, nil, _):

'condition' Same_lambda_parameter(LAMBDA_PARAMETER, LAMBDA_PARAMETER, IMP_FIT)

  'rule' Same_lambda_parameter(l_typing(_, TPS), l_typing(_, TPS1), IF):
	 Same_typings(TPS, TPS1, IF)

  'rule' Same_lambda_parameter(s_typing(_, TP), s_typing(_, TP1), IF):
	 Same_typing(TP, TP1, IF)

'condition' Same_args(ACTUAL_FUNCTION_PARAMETERS, ACTUAL_FUNCTION_PARAMETERS, IMP_FIT)

  'rule' Same_args(list(fun_arg(_, VS), AS), list(fun_arg(_, VS1), AS1), IF):
	 Same_exprs(VS, VS1, IF)
	 Same_args(AS, AS1, IF)

  'rule' Same_args(nil, nil, _):

'condition' Same_precond(PRE_CONDITION, PRE_CONDITION, IMP_FIT)

  'rule' Same_precond(pre_cond(_, E), pre_cond(_, E1), IF):
	 Same_expr(E, E1, IF)

  'rule' Same_precond(nil, nil, _):

'condition' Nil_or_same_postcond(OPT_POST_CONDITION, OPT_POST_CONDITION, IMP_FIT)

  'rule' Nil_or_same_postcond(nil, _, _):

  'rule' Nil_or_same_postcond(post(PC), post(PC1), IF):
	 Same_postcond(PC, PC1, IF)

'condition' Same_postcond(POST_CONDITION, POST_CONDITION, IMP_FIT)

  'rule' Same_postcond(post_cond(_, RN, E), post_cond(_, RN1, E1), IF):
	 Same_result_naming(RN, RN1)
	 Same_expr(E, E1, IF)

'condition' Same_result_naming(RESULT_NAMING, RESULT_NAMING)

  'rule' Same_result_naming(result(_, B), result(_, B1)):
	 Same_binding(B, B1)

  'rule' Same_result_naming(nil, nil):

'condition' Same_let_defs(LET_DEFS, LET_DEFS, IMP_FIT)

  'rule' Same_let_defs(list(D, DS), list(D1, DS1), IF):
	 Same_let_def(D, D1, IF)
	 Same_let_defs(DS, DS1, IF)

  'rule' Same_let_defs(nil, nil, _):

'condition' Same_let_def(LET_DEF, LET_DEF, IMP_FIT)

  'rule' Same_let_def(explicit(_, B, E), explicit(_, B1, E1), IF):
	 Same_let_binding(B, B1)
	 Same_expr(E, E1, IF)

  'rule' Same_let_def(implicit(_, TP, R), implicit(_, TP1, R1), IF):
	 Same_typing(TP, TP1, IF)
	 Same_restriction(R, R1, IF)

'condition' Same_let_binding(LET_BINDING, LET_BINDING)

  'rule' Same_let_binding(binding(_, B), binding(_, B1)):
	 Same_binding(B, B1)

  'rule' Same_let_binding(pattern(_, P), pattern(_, P1)):
	 Same_pattern(P, P1)

'condition' Same_elsifs(ELSIF_BRANCHES, ELSIF_BRANCHES, IMP_FIT)

  'rule' Same_elsifs(list(elsif(_, E, TH, _), ELS), list(elsif(_, E1, TH1, _), ELS1), IF):
	 Same_expr(E, E1, IF)
	 Same_expr(TH, TH1, IF)
	 Same_elsifs(ELS, ELS1, IF)

  'rule' Same_elsifs(nil, nil, _):

'condition' Same_else(ELSE_BRANCH, ELSE_BRANCH, IMP_FIT)

  'rule' Same_else(else(_, E), else(_, E1), IF):
	 Same_expr(E, E1, IF)

  'rule' Same_else(nil, nil, _)

'condition' Same_cases(CASE_BRANCHES, CASE_BRANCHES, IMP_FIT)

  'rule' Same_cases(list(C, CS), list(C1, CS1), IF):
	 Same_case(C, C1, IF)
	 Same_cases(CS, CS1, IF)

  'rule' Same_cases(nil, nil, _):

'condition' Same_case(CASE_BRANCH, CASE_BRANCH, IMP_FIT)

  'rule' Same_case(case(_, P, E, _), case(_, P1, E1, _), IF):
	 Same_pattern(P, P1)
	 Same_expr(E, E1, IF)

'condition' Same_bindings(BINDINGS, BINDINGS)

  'rule' Same_bindings(list(B, BS), list(B1, BS1)):
	 Same_binding(B, B1)	  
	 Same_bindings(BS, BS1)

  'rule' Same_bindings(nil, nil):

'condition' Same_binding(BINDING, BINDING)

  'rule' Same_binding(single(_, Id), single(_, Id1)):
	 Same_id_or_op(Id, Id1)

  'rule' Same_binding(product(_, BS), product(_, BS1)):
	 Same_bindings(BS, BS1)

'condition' Same_typings(TYPINGS, TYPINGS, IMP_FIT)

  'rule' Same_typings(list(TP, TPS), list(TP1, TPS1), IF):
	 Same_typing(TP, TP1, IF)	  
	 Same_typings(TPS, TPS1, IF)

  'rule' Same_typings(nil, nil, _):

'condition' Same_typing(TYPING, TYPING, IMP_FIT)

  'rule' Same_typing(single(_, B, T), single(_, B1, T1), IF):
	 Same_binding(B, B1)
	 Same_type(T, T1, IF)

  'rule' Same_typing(multiple(_, BS, T), multiple(_, BS1, T1), IF):
	 Same_bindings(BS, BS1)
	 Same_type(T, T1, IF)

'condition' Same_pattern(PATTERN, PATTERN)

  'rule' Same_pattern(literal_pattern(_, L), literal_pattern(_, L1)):
	 Same_literal(L, L1)

  'rule' Same_pattern(id_pattern(_, Id), id_pattern(_, Id1)):
	 Same_id_or_op(Id, Id1)

  'rule' Same_pattern(wildcard_pattern(), wildcard_pattern()):

  'rule' Same_pattern(product_pattern(_, PS), product_pattern(_, PS1)):
	 Same_patterns(PS, PS1)

  'rule' Same_pattern(enum_list(_, PS), enum_list(_, PS1)):
	 Same_patterns(PS, PS1)

  'rule' Same_pattern(conc_list(_, L, R), conc_list(_, L1, R1)):
	 Same_patterns(L, L1)
	 Same_pattern(R, R1)

  'rule' Same_pattern(name_occ_pattern(_, I, _), name_occ_pattern(_, I1, _)):
	 eq(I, I1)

  'rule' Same_pattern(record_occ_pattern(_, I, _, PS), record_occ_pattern(_, I1, _, PS1)):
	 eq(I, I1)
	 Same_patterns(PS, PS1)

'condition' Same_patterns(PATTERNS, PATTERNS)

  'rule' Same_patterns(list(P, PS), list(P1, PS1)):
	 Same_pattern(P, P1)
	 Same_patterns(PS, PS1)

  'rule' Same_patterns(nil, nil):

'condition' Same_id_or_op(ID_OR_OP, ID_OR_OP)

  'rule' Same_id_or_op(id_op(Id), id_op(Id1)):
	 eq(Id, Id1)

  'rule' Same_id_or_op(op_op(Op), op_op(Op1)):
	 eq(Op, Op1)

'condition' Same_literal(VALUE_LITERAL, VALUE_LITERAL)

  'rule' Same_literal(unit, unit):

  'rule' Same_literal(bool_true, bool_true):

  'rule' Same_literal(bool_false, bool_false):

  'rule' Same_literal(int(I), int(I1)):
	 eq(I, I1)
  
  'rule' Same_literal(real(I), real(I1)):
	 eq(I, I1)
  
  'rule' Same_literal(text(I), text(I1)):
	 eq(I, I1)
  
  'rule' Same_literal(char(I), char(I1)):
	 eq(I, I1)

'condition' Same_object(OBJECT_EXPR, OBJECT_EXPR, IMP_FIT)

  'rule' Same_object(obj_appl(Obj, Parms), obj_appl(Obj1, Parms1), IF):
	 Same_exprs(Parms, Parms1, IF)
	 Same_object(Obj, Obj1, IF)

  'rule' Same_object(obj_array(TPS, Obj), obj_array(TPS1, Obj1), IF):
	 Same_typings(TPS, TPS1, IF)
	 Same_object(Obj, Obj1, IF)

  'rule' Same_object(obj_fit(Obj, RNS), obj_fit(Obj1, RNS1), IF):
	 Same_renames(RNS, RNS1, IF)
	 Same_object(Obj, Obj1, IF)

  'rule' Same_object(obj_occ(_, I), obj_occ(_, I1), _):
	 eq(I, I1)

  'rule' Same_object(qual_occ(_, _, I), qual_occ(_, _, I1), _):
	 eq(I, I1)


'condition' Same_renames(RENAMES, RENAMES, IMP_FIT)

  'rule' Same_renames(list(H, T), list(H1, T1), IF):
	 Same_rename(H, H1, IF)
	 Same_renames(T, T1, IF)

  'rule' Same_renames(nil, nil, _):

'condition' Same_rename(RENAME, RENAME, IMP_FIT)

  'rule' Same_rename(rename(New, Old), rename(New1, Old1), IF):
	 Same_defined(New, New1, IF)
	 Same_defined(Old, Old1, IF)

'condition' Same_defined(DEFINED, DEFINED, IMP_FIT)

  'rule' Same_defined(def_name(_, Id), def_name(_, Id1), _):
	 Same_id_or_op(Id, Id1)

  'rule' Same_defined(disamb(_, Id, T), disamb(_, Id1, T1), IF):
	 Same_id_or_op(Id, Id1)
	 Same_type(T, T1, IF)  



'action' Fit_expr(VALUE_EXPR, IMP_FIT -> VALUE_EXPR)

  'rule' Fit_expr(literal_expr(P, L), _ -> literal_expr(P, L)):

  'rule' Fit_expr(named_val(P, N), _ -> named_val(P, N)):

  'rule' Fit_expr(chaos(P), _ -> chaos(P)):

  'rule' Fit_expr(skip(P), _ -> skip(P)):

  'rule' Fit_expr(stop(P), _ -> stop(P)):

  'rule' Fit_expr(swap(P), _ -> swap(P)):

  'rule' Fit_expr(product(P, VS), IF -> product(P, VS2)):
	 Fit_exprs(VS, IF -> VS2)

  'rule' Fit_expr(ranged_set(P, L, R), IF -> ranged_set(P, L2, R2)):
	 Fit_expr(L, IF -> L2)
	 Fit_expr(R, IF -> R2)

  'rule' Fit_expr(enum_set(P, VS), IF -> enum_set(P, VS2)):
	 Fit_exprs(VS, IF -> VS2)

  'rule' Fit_expr(comp_set(P, E, set_limit(P1, TPS, R)), IF -> comp_set(P, E2, set_limit(P1, TPS2, R2))):
	 Fit_expr(E, IF -> E2)
	 Fit_typings(TPS, IF -> TPS2)
	 Fit_restriction(R, IF -> R2)
	 
  'rule' Fit_expr(ranged_list(P, L, R), IF -> ranged_list(P, L2, R2)):
	 Fit_expr(L, IF -> L2)
	 Fit_expr(R, IF -> R2)

  'rule' Fit_expr(enum_list(P, VS), IF -> enum_list(P, VS2)):
	 Fit_exprs(VS, IF -> VS2)

  'rule' Fit_expr(comp_list(P, E, list_limit(P1, B, V, R)), IF ->
				  comp_list(P, E2, list_limit(P1, B, V2, R2))):
	 Fit_expr(E, IF -> E2)
	 Fit_expr(V, IF -> V2)
	 Fit_restriction(R, IF -> R2)	 

  'rule' Fit_expr(enum_map(P, PRS), IF -> enum_map(P, PRS2)):
	 Fit_pairs(PRS, IF -> PRS2)

  'rule' Fit_expr(comp_map(P, pair(L,R), set_limit(P1, TPS, REST)), IF -> comp_map(P, pair(L2,R2), set_limit(P1, TPS2, REST2))):
	 Fit_expr(L, IF -> L2)
	 Fit_expr(R, IF -> R2)
	 Fit_typings(TPS, IF -> TPS2)
	 Fit_restriction(REST, IF -> REST2)

  'rule' Fit_expr(function(P, PARM, E), IF -> function(P, PARM2, E2)):
	 Fit_lambda_parameter(PARM, IF -> PARM2)
	 Fit_expr(E, IF -> E2)

  'rule' Fit_expr(application(P, E, AS), IF -> application(P, E2, AS2)):
	 Fit_expr(E, IF -> E2)
	 Fit_args(AS, IF -> AS2)

  'rule' Fit_expr(quantified(P, Q, TPS, R), IF -> quantified(P, Q, TPS2, R2)):
	 Fit_typings(TPS, IF -> TPS2)
	 Fit_restriction(R, IF -> R2)

  'rule' Fit_expr(equivalence(P, L, R, nil), IF -> equivalence(P, L2, R2, nil)):
	 Fit_expr(L, IF -> L2)
	 Fit_expr(R, IF -> R2)

  'rule' Fit_expr(equivalence(P, L, R, pre_cond(P1, PRE)), IF ->
	 equivalence(P, L2, R2, pre_cond(P1, PRE2))):
	 Fit_expr(L, IF -> L2)
	 Fit_expr(R, IF -> R2)
	 Fit_expr(PRE, IF -> PRE2)

  'rule' Fit_expr(post(P, E, C, nil), IF -> post(P, E2, C2, nil)):
	 Fit_expr(E, IF -> E2)
	 Fit_post_cond(C, IF -> C2)	 

  'rule' Fit_expr(post(P, E, C, pre_cond(P1, PRE)), IF -> post(P, E2, C2, pre_cond(P1, PRE2))):
	 Fit_expr(E, IF -> E2)
	 Fit_post_cond(C, IF -> C2)	 
	 Fit_expr(PRE, IF -> PRE2)

  'rule' Fit_expr(disamb(P, E, T), IF -> disamb(P, E2, T2)):
	 Fit_expr(E, IF -> E2)
	 Fit_type(T, IF -> T2)

  'rule' Fit_expr(bracket(P, E), IF -> bracket(P, E2)):
	 Fit_expr(E, IF -> E2)

  'rule' Fit_expr(ax_infix(P, L, C, R, PE), IF -> ax_infix(P, L2, C, R2, PE)):
	 Fit_expr(L, IF -> L2)
	 Fit_expr(R, IF -> R2)

  'rule' Fit_expr(val_infix(P, L, O, R), IF -> val_infix(P, L2, O, R2)):
	 Fit_expr(L, IF -> L2)
	 Fit_expr(R, IF -> R2)

  'rule' Fit_expr(stmt_infix(P, L, C, R), IF -> stmt_infix(P, L2, C, R2)):
	 Fit_expr(L, IF -> L2)
	 Fit_expr(R, IF -> R2)

  'rule' Fit_expr(always(P, E), IF -> always(P, E2)):
	 Fit_expr(E, IF -> E2)

  'rule' Fit_expr(ax_prefix(P, C, E), IF -> ax_prefix(P, C, E2)):
	 Fit_expr(E, IF -> E2)

  'rule' Fit_expr(comprehended(P, C, E, set_limit(P1, TPS, R)), IF -> comprehended(P, C, E2, set_limit(P1, TPS2, R2))):
	 Fit_expr(E, IF -> E2)
	 Fit_typings(TPS, IF -> TPS2)
	 Fit_restriction(R, IF -> R2)	 

  'rule' Fit_expr(initialise(P, nil), _ -> initialise(P, nil)):

  'rule' Fit_expr(initialise(P, qualification(Obj)), IF -> initialise(P, qualification(Obj1))):
	 Fit_object(Obj, IF -> Obj1)

-- TODO local properly - declarations should be fitted
  'rule' Fit_expr(env_local(P, DECLS, ENV, E), IF -> env_local(P, DECLS, ENV, E2)): 
	 Fit_expr(E, IF -> E2)

  'rule' Fit_expr(let_expr(P, DS, E), IF -> let_expr(P, DS2, E2)):
	 Fit_let_defs(DS, IF -> DS2)
	 Fit_expr(E, IF -> E2)

  'rule' Fit_expr(if_expr(P, E, TH, RT, ELSIF, EL), IF -> if_expr(P, E2, TH2, RT, ELSIF2, EL2)):
	 Fit_expr(E, IF -> E2)
	 Fit_expr(TH, IF -> TH2)
	 Fit_elsifs(ELSIF, IF -> ELSIF2)
	 Fit_else(EL, IF -> EL2)

  'rule' Fit_expr(case_expr(P, E, PE, CS), IF -> case_expr(P, E2, PE, CS2)):
	 Fit_expr(E, IF -> E2)
	 Fit_cases(CS, IF -> CS2)

  'rule' Fit_expr(while_expr(P, G, E), IF -> while_expr(P, G2, E2)):
	 Fit_expr(G, IF -> G2)
	 Fit_expr(E, IF -> E2)
	 
  'rule' Fit_expr(until_expr(P, E, G), IF -> until_expr(P, E2, G2)):
	 Fit_expr(E, IF -> E2)
	 Fit_expr(G, IF -> G2)
	
  'rule' Fit_expr(for_expr(P, list_limit(P1, B, E, R), V), IF ->
			      for_expr(P, list_limit(P1, B, E2, R2), V2)):
	 Fit_expr(E, IF -> E2)
	 Fit_restriction(R, IF -> R2)	 
	 Fit_expr(V, IF -> V2)

  'rule' Fit_expr(val_occ(P, I, Q), IF -> val_occ(P, I2, Q2)):
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_value_id(I, VALF -> I2)
	 [|
	   eq(I, I2)
	   -- not changed, so local and type may need fitting
	   -- OK to just overwrite type?  Probably.
	   -- Could generate a new value_id, but then every instance of a
	   -- local binding would end up with a different value_id
	   I'Type -> T
	   Fit_type(T, IF -> T2)
	   I'Type <- T2
	 |]
	 Fit_opt_qualification(Q, IF -> Q2)
	 
  'rule' Fit_expr(var_occ(P, I, Q), IF -> var_occ(P, I2, Q2)):
print("fit_expr")
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_variable_id(I, VARF -> I2)
	 Fit_opt_qualification(Q, IF -> Q2)
	 
  'rule' Fit_expr(pre_occ(P, I, Q), IF -> pre_occ(P, I2, Q2)):
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_variable_id(I, VARF -> I2)
	 Fit_opt_qualification(Q, IF -> Q2)
	 
  'rule' Fit_expr(infix_occ(P, L, I, Q, R), IF -> infix_occ(P, L2, I2, Q2, R2)):
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_value_id(I, VALF -> I2)
	 Fit_expr(L, IF -> L2)
	 Fit_expr(R, IF -> R2)
	 Fit_opt_qualification(Q, IF -> Q2)
	 
  'rule' Fit_expr(prefix_occ(P, I, Q, R), IF -> prefix_occ(P, I2, Q2, R2)):
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_value_id(I, VALF -> I2)
	 Fit_expr(R, IF -> R2)
	 Fit_opt_qualification(Q, IF -> Q2)
	 
  'rule' Fit_expr(ass_occ(P, I, Q, E), IF -> ass_occ(P, I2, Q2, E2)):
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_variable_id(I, VARF -> I2)
	 Fit_expr(E, IF -> E2)
	 Fit_opt_qualification(Q, IF -> Q2)
	 
  'rule' Fit_expr(input_occ(P, I, Q), IF -> input_occ(P, I2, Q2)):
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_channel_id(I, CHF -> I2)
	 Fit_opt_qualification(Q, IF -> Q2)

  'rule' Fit_expr(output_occ(P, I, Q, E), IF -> output_occ(P, I2, Q2, E2)):
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_channel_id(I, CHF -> I2)
	 Fit_expr(E, IF -> E2)
	 Fit_opt_qualification(Q, IF -> Q2)

  'rule' Fit_expr(no_val, _ -> no_val):
	 
-- debug
--   'rule' Fit_expr(E, _ -> E)
-- Putmsg("Cannot fit ")
-- Print_expr(E)
-- Putnl()
-- print(E)

'action' Fit_exprs(VALUE_EXPRS, IMP_FIT -> VALUE_EXPRS)

  'rule' Fit_exprs(list(V, VS), IF -> list(V2, VS2)):
	 Fit_expr(V, IF -> V2)
	 Fit_exprs(VS, IF -> VS2)

  'rule' Fit_exprs(nil, _ -> nil):

'action' Fit_restriction(RESTRICTION, IMP_FIT -> RESTRICTION)

  'rule' Fit_restriction(restriction(P, E), IF -> restriction(P, E2)):
	 Fit_expr(E, IF -> E2)

  'rule' Fit_restriction(nil, _ -> nil):


'action' Fit_pairs(VALUE_EXPR_PAIRS, IMP_FIT -> VALUE_EXPR_PAIRS)

  'rule' Fit_pairs(list(pair(L,R), PRS), IF -> list(pair(L2,R2), PRS2)):
	 Fit_expr(L, IF -> L2)
	 Fit_expr(R, IF -> R2)
	 Fit_pairs(PRS, IF -> PRS2)

  'rule' Fit_pairs(nil, _ -> nil):

'action' Fit_lambda_parameter(LAMBDA_PARAMETER, IMP_FIT -> LAMBDA_PARAMETER)

  'rule' Fit_lambda_parameter(l_typing(P, TPS), IF -> l_typing(P, TPS2)):
	 Fit_typings(TPS, IF -> TPS2)

  'rule' Fit_lambda_parameter(s_typing(P, TP), IF -> s_typing(P, TP2)):
	 Fit_typing(TP, IF -> TP2)

'action' Fit_args(ACTUAL_FUNCTION_PARAMETERS, IMP_FIT -> ACTUAL_FUNCTION_PARAMETERS)

  'rule' Fit_args(list(fun_arg(P, VS), AS), IF -> list(fun_arg(P, VS2), AS2)):
	 Fit_exprs(VS, IF -> VS2)
	 Fit_args(AS, IF -> AS2)

  'rule' Fit_args(nil, _ -> nil):

'action' Fit_post_cond(POST_CONDITION, IMP_FIT -> POST_CONDITION)

  'rule' Fit_post_cond(post_cond(P, RN, E), IF -> post_cond(P, RN, E2)):
	 Fit_expr(E, IF -> E2)

'action' Fit_let_defs(LET_DEFS, IMP_FIT -> LET_DEFS)

  'rule' Fit_let_defs(list(D, DS), IF -> list(D2, DS2)):
	 Fit_let_def(D, IF -> D2)
	 Fit_let_defs(DS, IF -> DS2)

  'rule' Fit_let_defs(nil, _ -> nil):

'action' Fit_let_def(LET_DEF, IMP_FIT -> LET_DEF)

  'rule' Fit_let_def(explicit(P, LB, E), IF -> explicit(P, LB2, E2)):
	 Fit_expr(E, IF -> E2)
	 Fit_let_binding(LB, IF -> LB2)

  'rule' Fit_let_def(implicit(P, B, R), IF -> implicit(P, B, R2)):
	 Fit_restriction(R, IF -> R2)

'action' Fit_let_binding(LET_BINDING, IMP_FIT -> LET_BINDING)

  'rule' Fit_let_binding(binding(P, B), _ -> binding(P, B)):

  'rule' Fit_let_binding(pattern(P, PATT), IF -> pattern(P, PATT2)):
	 Fit_pattern(PATT, IF -> PATT2)

'action' Fit_elsifs(ELSIF_BRANCHES, IMP_FIT -> ELSIF_BRANCHES)

  'rule' Fit_elsifs(list(elsif(P, E, TH, PE), ELS), IF -> list(elsif(P, E2, TH2, PE), ELS2)):
	 Fit_expr(E, IF -> E2)
	 Fit_expr(TH, IF -> TH2)
	 Fit_elsifs(ELS, IF -> ELS2)

  'rule' Fit_elsifs(nil, _ -> nil):

'action' Fit_else(ELSE_BRANCH, IMP_FIT -> ELSE_BRANCH)

  'rule' Fit_else(else(P, E), IF -> else(P, E2)):
	 Fit_expr(E, IF -> E2)

  'rule' Fit_else(nil, _ -> nil)

'action' Fit_cases(CASE_BRANCHES, IMP_FIT -> CASE_BRANCHES)

  'rule' Fit_cases(list(C, CS), IF -> list(C2, CS2)):
	 Fit_case(C, IF -> C2)
	 Fit_cases(CS, IF -> CS2)

  'rule' Fit_cases(nil, _ -> nil):

'action' Fit_case(CASE_BRANCH, IMP_FIT -> CASE_BRANCH)

  'rule' Fit_case(case(P, PATT, E, PE), IF -> case(P, PATT2, E2, PE)):
	 Fit_pattern(PATT, IF -> PATT2)
	 Fit_expr(E, IF -> E2)

'action' Fit_typings(TYPINGS, IMP_FIT -> TYPINGS)

  'rule' Fit_typings(list(TP, TPS), IF -> list(TP2, TPS2)): 
	 Fit_typing(TP, IF -> TP2)
	 Fit_typings(TPS, IF -> TPS2)

  'rule' Fit_typings(nil, _ -> nil):

'action' Fit_typing(TYPING, IMP_FIT -> TYPING)

  'rule' Fit_typing(single(P, B, T), IF -> single(P, B, T2)):
	 Fit_type(T, IF -> T2)

  'rule' Fit_typing(multiple(P, BS, T), IF -> multiple(P, BS, T2)):
	 Fit_type(T, IF -> T2)

'action' Fit_pattern(PATTERN, IMP_FIT -> PATTERN)

  'rule' Fit_pattern(product_pattern(P, PATTS), IF -> product_pattern(P, PATTS2)):
	 Fit_patterns(PATTS, IF -> PATTS2)

  'rule' Fit_pattern(enum_list(P, PATTS), IF -> enum_list(P, PATTS2)):
	 Fit_patterns(PATTS, IF -> PATTS2)

  'rule' Fit_pattern(conc_list(P, PATTS, R), IF -> conc_list(P, PATTS2, R2)):
	 Fit_patterns(PATTS, IF -> PATTS2)
	 Fit_pattern(R, IF -> R2)

  'rule' Fit_pattern(name_occ_pattern(P, I, Q), IF -> name_occ_pattern(P, I2, Q2)):
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_value_id(I, VALF -> I2)
	 Fit_opt_qualification(Q, IF -> Q2)

  'rule' Fit_pattern(record_occ_pattern(P, I, Q, PATTS), IF -> record_occ_pattern(P, I2, Q2, PATTS2)):
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_value_id(I, VALF -> I2)
	 Fit_patterns(PATTS, IF -> PATTS2)
	 Fit_opt_qualification(Q, IF -> Q2)

-- others
  'rule' Fit_pattern(PATT, _ -> PATT):

'action' Fit_patterns(PATTERNS, IMP_FIT -> PATTERNS)

  'rule' Fit_patterns(list(PATT, PATTS), IF -> list(PATT2, PATTS2)): 
	 Fit_pattern(PATT, IF -> PATT2)
	 Fit_patterns(PATTS, IF -> PATTS2)

  'rule' Fit_patterns(nil, _ -> nil):

'action' Fit_opt_qualification(OPT_QUALIFICATION, IMP_FIT -> OPT_QUALIFICATION)

  'rule' Fit_opt_qualification(nil, _ -> nil):

  'rule' Fit_opt_qualification(qualification(Q), IF -> qualification(Q1)):
	 Fit_object(Q, IF -> Q1)

'action' Fit_object(OBJECT_EXPR, IMP_FIT -> OBJECT_EXPR)

  'rule' Fit_object(obj_name(N), IF -> obj_name(N)):

  'rule' Fit_object(obj_appl(Obj, Parms), IF -> obj_appl(Obj1, Parms1)):
	 Fit_exprs(Parms, IF -> Parms1)
	 Fit_object(Obj, IF -> Obj1)

  'rule' Fit_object(obj_array(TPS, Obj), IF -> obj_array(TPS1, Obj1)):
	 Fit_typings(TPS, IF -> TPS1)
	 Fit_object(Obj, IF -> Obj1)

  'rule' Fit_object(obj_fit(Obj, RNS), IF -> obj_fit(Obj1, RNS)):
	 Fit_object(Obj, IF -> Obj1)

  'rule' Fit_object(obj_occ(P, I), IF -> obj_occ(P, I1)):
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_object_id(I, OBJF -> I1)

  'rule' Fit_object(qual_occ(P, Obj, I), IF -> qual_occ(P, Obj1, I1)):
	 where(IF -> imp_fit(TYPF, VALF, VARF, CHF, OBJF))
	 Fit_object_id(I, OBJF -> I1)
	 Fit_object(Obj, IF -> Obj1)




'action' Fit_type_id(Type_id, TYPE_FITS -> Type_id)

  'rule' Fit_type_id(I, type_fit(I1, I2, TF) -> I3):
	 (|
	   eq(I, I1)
	   (|
	     where(I2 -> type_id(I3))
	   ||
	     where(I -> I3)
	   |)
	 ||
	   Fit_type_id(I, TF -> I3)
	 |)

  'rule' Fit_type_id(I, nil -> I):

'action' Fit_value_id(Value_id, VALUE_FITS -> Value_id)

  'rule' Fit_value_id(I, value_fit(I1, I2, TF) -> I3):
	 (|
	   eq(I, I1)
	   (|
	     where(I2 -> value_id(I3))
	   ||
	     where(I -> I3)
	   |)
	 ||
	   Fit_value_id(I, TF -> I3)
	 |)

  'rule' Fit_value_id(I, nil -> I):

'action' Fit_variable_id(Variable_id, VARIABLE_FITS -> Variable_id)

  'rule' Fit_variable_id(I, variable_fit(I1, I2, TF) -> I3):
	 (|
	   eq(I, I1)
	   (|
	     where(I2 -> variable_id(I3))
	   ||
	     where(I -> I3)
	   |)
	 ||
	   Fit_variable_id(I, TF -> I3)
	 |)

  'rule' Fit_variable_id(I, nil -> I):

'action' Fit_channel_id(Channel_id, CHANNEL_FITS -> Channel_id)

  'rule' Fit_channel_id(I, channel_fit(I1, I2, TF) -> I3):
	 (|
	   eq(I, I1)
	   (|
	     where(I2 -> channel_id(I3))
	   ||
	     where(I -> I3)
	   |)
	 ||
	   Fit_channel_id(I, TF -> I3)
	 |)

  'rule' Fit_channel_id(I, nil -> I):

'action' Fit_object_id(Object_id, OBJECT_FITS -> Object_id)

  'rule' Fit_object_id(I, object_fit(I1, I2, _, TF) -> I3):
	 (|
	   eq(I, I1)
	   (|
	     where(I2 -> object_id(I3))
	   ||
	     where(I -> I3)
	   |)
	 ||
	   Fit_object_id(I, TF -> I3)
	 |)

  'rule' Fit_object_id(I, nil -> I):




---------------------------------------------------------------
-- Utilities
---------------------------------------------------------------


-- checks for first type being known to be a subtype of the second
-- assumes the types can unify
-- assumes all types are resolved and not polymorphic
'condition' Static_subtype(TYPE_EXPR, TYPE_EXPR)

  'rule' Static_subtype(T, T1):
	 eq(T, T1)

  'rule' Static_subtype(T, T1):
	 Maximal(T1)

  'rule' Static_subtype(bracket(T), T1):
	 Static_subtype(T, T1)

  'rule' Static_subtype(T, bracket(T1)):
	 Static_subtype(T, T1)

  'rule' Static_subtype(subtype(single(_,_,T),_), T1):
	 Static_subtype(T, T1)

  'rule' Static_subtype(nat, int):

  'rule' Static_subtype(time, real):
	 IsTimed()

  'rule' Static_subtype(text, fin_list(char)):

  'rule' Static_subtype(fin_list(T), text):
	 Static_subtype(T, char)

  'rule' Static_subtype(fin_set(T), fin_set(T1)):
	 Static_subtype(T, T1)

  'rule' Static_subtype(infin_set(T), infin_set(T1)):
	 Static_subtype(T, T1)

  'rule' Static_subtype(fin_set(T), infin_set(T1)):
	 Static_subtype(T, T1)

  'rule' Static_subtype(fin_list(T), fin_list(T1)):
	 Static_subtype(T, T1)

  'rule' Static_subtype(infin_list(T), infin_list(T1)):
	 Static_subtype(T, T1)

  'rule' Static_subtype(fin_list(T), infin_list(T1)):
	 Static_subtype(T, T1)

  'rule' Static_subtype(fin_map(D, R), fin_map(D1, R1)):
	 Static_subtype(D, D1)
	 Static_subtype(R, R1)

  'rule' Static_subtype(infin_map(D, R), infin_map(D1, R1)):
	 Static_subtype(D, D1)
	 Static_subtype(R, R1)

  'rule' Static_subtype(fin_map(D, R), infin_map(D1, R1)):
	 Static_subtype(D, D1)
	 Static_subtype(R, R1)

  'rule' Static_subtype(product(PR), product(PR1)):
	 Static_subtype_prod(PR, PR1)

  'rule' Static_subtype(fun(T, total, result(R, _, _, _, _)),
			fun(T1, total, result(R1,_, _, _, _))):
	 Static_subtype(T1, T)
	 Static_subtype(R, R1)

  'rule' Static_subtype(fun(T, total, result(R, _, _, _, _)),
			fun(T1, partial, result(R1,_, _, _, _))):
	 Static_subtype(T1, T)
	 Static_subtype(R, R1)

  'rule' Static_subtype(fun(T, partial, result(R, _, _, _, _)),
			fun(T1, partial, result(R1,_, _, _, _))):
	 Static_subtype(T1, T)
	 Static_subtype(R, R1)

  'rule' Static_subtype(defined(I, _), defined(I1, _)):
	 eq(I, I1)

  'rule' Static_subtype(defined(I, _), T1):
	 I'Def -> abbreviation(T)
	 Static_subtype(T, T1)

  'rule' Static_subtype(T, defined(I1, _)):
	 I1'Def -> abbreviation(T1)
	 Static_subtype(T, T1)

'condition' Static_subtype_prod(PRODUCT_TYPE, PRODUCT_TYPE)

  'rule' Static_subtype_prod(list(T, TS), list(T1, TS1)):
	 Static_subtype(T, T1)
	 Static_subtype_prod(TS, TS1)

  'rule' Static_subtype_prod(nil, nil):

-- returns type of value_expr, with second parameter as default
-- if no better type can be found
-- There are probably a very large number of ways of improving on this
-- Assumes value_expr is resolved

'action' Type_of_val(VALUE_EXPR, TYPE_EXPR -> TYPE_EXPR)

  'rule' Type_of_val(literal_expr(_, int(_)), T -> nat):

  'rule' Type_of_val(literal_expr(_, real(_)), T -> time):
	 IsTimed()

  'rule' Type_of_val(literal_expr(_, text(_)), T -> text):

  'rule' Type_of_val(V, bracket(T) -> T1):
	 Type_of_val(V, T -> T1)

  'rule' Type_of_val(product(_, VS), T -> product(TS1)):
	 (|
	   where(T -> product(TS))
	 ||
	   Length_vs(VS -> N)
	   Make_product_type(T, N -> product(TS))
	 |)
	 Type_of_val_product(VS, TS -> TS1)

  'rule' Type_of_val(ranged_set(_, L, _), _ -> fin_set(nat)):
	 Type_of_val(L, int -> T)
	 Static_subtype(T, nat)

  'rule' Type_of_val(ranged_set(_, _, _), _ -> fin_set(int)):

  'rule' Type_of_val(enum_set(_, VS), ST -> fin_set(T1)):
	 Make_set_type(ST -> ST1)
	 (| where(ST1 -> infin_set(T)) || where(ST1 -> fin_set(T)) |)
	 Type_of_vals(VS, T -> T1)

  'rule' Type_of_val(comp_set(_, V, _), ST -> fin_set(T1)):
	 Make_set_type(ST -> fin_set(T))
	 Type_of_val(V, T -> T1)

  'rule' Type_of_val(comp_set(_, V, set_limit(_, TGL, R)), ST -> fin_set(T2)):
         where(TGL -> list(TG, nil))
         Split_typing(TG -> B, TT)
         Split_restriction(exists, R, B, TT -> SLM, T1, _)
	 (|
	   Type_is_set(T1 -> TE)
	   Type_of_val(SLM, infin_set(TE) -> ST1)
	   Match_up(ST1, fin_set(any) -> fin_set(_))
	 ||
	   Type_is_list(T1 -> TE)
	   Type_of_val(SLM, infin_list(TE) -> LT)
	   Match_up(LT, fin_list(any) -> fin_list(_))
	 ||
	   Type_is_map(T1 -> TD, TR)
	   Type_of_val(SLM, infin_map(TD, TR) -> MT)
	   Match_up(MT, fin_map(any, any) -> fin_map(_,_))
	 |) 
	 Make_set_type(ST -> infin_set(T))
	 Type_of_val(V, T -> T2)

  'rule' Type_of_val(comp_set(_, V, _), ST -> infin_set(T1)):
	 Make_set_type(ST -> infin_set(T))
	 Type_of_val(V, T -> T1)

  'rule' Type_of_val(ranged_list(_, L, _), _ -> fin_list(nat)):
	 Type_of_val(L, int -> T)
	 Static_subtype(T, nat)

  'rule' Type_of_val(ranged_list(_, _, _), _ -> fin_list(int)):

  'rule' Type_of_val(enum_list(_, VS), LT -> T2):
	 (| Make_list_type(LT -> infin_list(T)) || Make_list_type(LT -> fin_list(T)) |)
	 Type_of_vals(VS, T -> T1)
	 (|
	   eq(T1, char)
	   where(TYPE_EXPR'text -> T2)
	 ||
	   where(fin_list(T1) -> T2)
	 |)

  'rule' Type_of_val(comp_list(_, V, list_limit(_, _, L, _)), LT -> T2):
	 Type_of_val(L, infin_list(any) -> LT1)
	 Match_up(LT1, fin_list(any) -> fin_list(_))
	 Type_is_list(LT -> T)
	 Type_of_val(V, T -> T1)
	 (|
	   eq(T1, char)
	   where(TYPE_EXPR'text -> T2)
	 ||
	   where(fin_list(T1) -> T2)
	 |)

  'rule' Type_of_val(comp_list(_, V, _), LT -> infin_list(T1)):
	 Make_list_type(LT -> infin_list(T))
	 Type_of_val(V, T -> T1)

  'rule' Type_of_val(comp_list(_, V, _), LT -> T2):
	 Make_list_type(LT -> fin_list(T))
	 Type_of_val(V, T -> T1)
	 (|
	   eq(T1, char)
	   where(TYPE_EXPR'text -> T2)
	 ||
	   where(fin_list(T1) -> T2)
	 |)

-- next rule OK since we generate disjointness confidence
-- conditions for enumerations of two or more pairs
  'rule' Type_of_val(enum_map(_, Pairs), MT -> fin_map(D1, R1)):
	 (| Make_map_type(MT -> infin_map(D, R)) || Make_map_type(MT -> fin_map(D, R)) |)
	 Type_of_pairs(Pairs, D, R -> D1, R1)

  'rule' Type_of_val(comp_map(_, pair(DV, RV), _), MT -> fin_map(D1, R1)):
	 Make_map_type(MT -> fin_map(D, R))
	 Type_of_val(DV, D -> D1)
	 Type_of_val(RV, R -> R1)

  'rule' Type_of_val(comp_map(_, pair(DV, RV), set_limit(_, TGL, R)), MT -> fin_map(D2, R2)):
         where(TGL -> list(TG, nil))
         Split_typing(TG -> B, TT)
         Split_restriction(exists, R, B, TT -> SLM, T1, _)
	 (|
	   Type_is_set(T1 -> TE)
	   Type_of_val(SLM, infin_set(TE) -> ST)
	   Match_up(ST, fin_set(any) -> fin_set(_))
	 ||
	   Type_is_list(T1 -> TE)
	   Type_of_val(SLM, infin_list(TE) -> LT)
	   Match_up(LT, fin_list(any) -> fin_list(_))
	 ||
	   Type_is_map(T1 -> TD, TR)
	   Type_of_val(SLM, infin_map(TD, TR) -> MT1)
	   Match_up(MT1, fin_map(any, any) -> fin_map(_, _))
	 |)
	 -- weak but common and sufficient for determinism
         Matches_binding(DV, B)
	 Make_map_type(MT -> infin_map(D1, R1))
	 Type_of_val(DV, D1 -> D2)
	 Type_of_val(RV, R1 -> R2)

  'rule' Type_of_val(comp_map(_, pair(DV, RV), _), MT -> infin_map(D1, R1)):
	 Make_map_type(MT -> infin_map(D, R))
	 Type_of_val(DV, D -> D1)
	 Type_of_val(RV, R -> R1)

  'rule' Type_of_val(application(_,FUN, ARGS), T -> T1):
	 (|
	   (|
	     where(FUN -> val_occ(_, I, _))
	     I'Type -> FT
	   ||
	     where(FUN -> var_occ(_, I1, _))
             I1'Type -> FT
	   ||
	     where(FUN -> pre_occ(_, I2, _))
	     I2'Type -> FT
	   ||
	     where(FUN -> input_occ(_, I3, _))
	     I3'Type -> FT
	   |)
	   Type_of_application(ARGS, FT -> T1)
	 ||
	   where(T -> T1)
	 |)

-- since a disambiguation generates a confidence condition we can
-- safely use the disambiguation type
  'rule' Type_of_val(disamb(_,V,T), _ -> T):

  'rule' Type_of_val(bracket(_, V), T -> T1):
	 Type_of_val(V, T -> T1)

  'rule' Type_of_val(stmt_infix(_, _, sequence, V), T -> T1):
	 Type_of_val(V, T -> T1)

  'rule' Type_of_val(let_expr(_, _, V), T -> T1):
	 Type_of_val(V, T -> T1)

  'rule' Type_of_val(if_expr(_,_,THEN,_,ELSIF,ELS), T -> T1):
	 (|
	   where(ELS -> else(_, ELSE))
	   Type_of_val(THEN, T -> TT)
	   Type_of_val(ELSE, T -> TEL)
	   (|
	     ne(ELSIF, nil)
	     Type_of_elsif(ELSIF, T -> TEF)
	     Match_up(TEF, TEL -> T2)
	   ||
	     where(TEL -> T2)
	   |)
	   Match_up(TT, T2 -> T1)
	 ||
	   where(TYPE_EXPR'unit -> T1)
	 |)

  'rule' Type_of_val(case_expr(_,_,_,CS), T -> T1):
	 Type_of_cases(CS, T -> T1)
	 
  'rule' Type_of_val(val_occ(_, I, _), _ -> T):
	 I'Type -> T

  'rule' Type_of_val(var_occ(_, I, _), _ -> T):
         I'Type -> T

  'rule' Type_of_val(pre_occ(_, I, _), _ -> T):
	 I'Type -> T

  'rule' Type_of_val(input_occ(_, I, _), _ -> T):
	 I'Type -> T

  'rule' Type_of_val(infix_occ(P, L, I, _, R), T -> T1):
	 -- make default first in case nothing better
	 I'Type -> FT
	 Type_of_application(list(fun_arg(P, list(L, list(R, nil))), nil), FT -> TD0)
	 -- but this default can be polymorphic
	 Contains_any_or_poly(TD0, nil -> Found)
	 (|
	   eq(Found, found)
	   where(T -> TD)
	 ||
	   where(TD0 -> TD)
	 |)
	 (|
	   -- check we have a built-in operator
	   I'Ident -> op_op(Op)
	   Built_in(Op, I)
	   (|
	     eq(Op, rem)
	     (| -- rem : Nat >< Nat -> Nat
	       I'Type -> fun(product(list(int,list(int,nil))),_,_)
	       Type_of_val(L, int -> TL)
	       Static_subtype(TL, nat)
	       Type_of_val(R, int -> TR)
	       Static_subtype(TR, nat)
	       where(nat -> T1)
	     || -- rem : T-set >< T-infset -> T-set
	       I'Type -> fun(product(list(infin_set(_),_)),_,_)
	       Make_set_type(T -> infin_set(T2))
	       Type_of_val(L, infin_set(T2) -> TL)
	       Make_set_type(TL -> fin_set(T3))
	       where(fin_set(T3) -> T1)
	     || -- rem : (T -m-> R) >< T-infset -> (T -m-> R)
	       I'Type -> fun(product(list(infin_map(_,_),_)),_,_)
	       Make_map_type(T -> infin_map(T2, T3)) 
	       Type_of_val(L, infin_map(T2, T3) -> TL)
	       Make_map_type(TL -> fin_map(T4, T5))
	       where(fin_map(T4, T5) -> T1)
	     ||
	       where(TD -> T1)
	     |)
	   || -- caret : T-list >< T-list -> T-list
	     eq(Op, caret)
	     (|
	       Make_list_type(T -> infin_list(T2))
	       Type_of_val(L, infin_list(T2) -> TL)
	       Make_list_type(TL -> fin_list(T3))
	       Type_of_val(R, infin_list(T2) -> TR)
	       Make_list_type(TR -> fin_list(T4))
	       Match_up(T3, T4 -> T5)
	       (|
		 eq(T5, char)
		 where(TYPE_EXPR'text -> T1)
	       ||
		 where(fin_list(T5) -> T1)
	       |)
	     ||
	       where(TD -> T1)
	     |)
	   ||
	     eq(Op, union)
	     (| -- union : T-set >< T-set -> T-set
	       -- check we have set union
	       I'Type -> fun(product(list(infin_set(_),_)),_,_)
	       Make_set_type(T -> infin_set(T2))
	       Type_of_val(L, infin_set(T2) -> TL)
	       Make_set_type(TL -> fin_set(T3))
	       Type_of_val(R, infin_set(T2) -> TR)
	       Make_set_type(TR -> fin_set(T4))
	       Match_up(T3, T4 -> T5)
	       where(fin_set(T5) -> T1)
	     ||
	       -- we have map union
	       -- union : (T -m-> R) >< (T -m-> R) -~-> (T -m-> R)
	       -- when its precondition is true (generated separately)
	       Make_map_type(T -> infin_map(T2, T3))
	       Type_of_val(L, infin_map(T2, T3) -> TL)
	       Make_map_type(TL -> fin_map(DL,RL))
	       Type_of_val(R, infin_map(T2, T3) -> TR)
	       Make_map_type(TR -> fin_map(DR,RR))
	       Match_up(DL, DR -> DT)
	       Match_up(RL, RR -> RT)
	       where(fin_map(DT, RT) -> T1)
	     ||
	       where(TD -> T1)
	     |)
	   ||
	     eq(Op, inter)
	     Make_set_type(T -> infin_set(T2))
	     Type_of_val(L, infin_set(T2) -> TL)
	     Type_of_val(R, infin_set(T2) -> TR)
	     (| -- T-set >< T-infset -> T-set
	       Make_set_type(TL -> fin_set(T3))
	       (| Make_set_type(TR -> fin_set(T4))
	       || Make_set_type(TR -> infin_set(T4)) |)
	       Match_up(T3, T4 -> T5)
	       where(fin_set(T5) -> T1)
	     || -- T-inset >< T-set -> T-set
	       (| Make_set_type(TL -> fin_set(T3))
	       || Make_set_type(TL -> infin_set(T3)) |)
	       Make_set_type(TR -> fin_set(T4))
	       Match_up(T3, T4 -> T5)
	       where(fin_set(T5) -> T1)
	     ||
	       where(TD -> T1)
	     |)
	   || -- override : (T -m-> R) >< (T -m-> R) -> (T -m-> R)
	     eq(Op, override)
	     (|
	       Make_map_type(T -> infin_map(T2, T3))
	       Type_of_val(L, infin_map(T2, T3) -> TL)
	       Make_map_type(TL -> fin_map(DL,RL))
	       Type_of_val(R, infin_map(T2, T3) -> TR)
	       Make_map_type(TR -> fin_map(DR,RR))
	       Match_up(DL, DR -> DT)
	       Match_up(RL, RR -> RT)
	       where(fin_map(DT, RT) -> T1)
	     ||
	       where(TD -> T1)
	     |)
	   ||
	     (| eq(Op, plus)
	     || eq(Op, mult)
	     || eq(Op, div) |)
	     (| -- plus, mult, div : Nat >< Nat -~-> Nat
	       -- check we have the integer version
	       I'Type -> fun(product(list(int,_)),_,_)
	       Type_of_val(L, int -> TL)
	       Static_subtype(TL, nat)
	       Type_of_val(R, int -> TR)
	       Static_subtype(TR, nat)
	       where(nat -> T1)
	     || -- div : (T -m-> R) >< T-infset -> (T -m-> R)
	       eq(Op, div)
	       -- check we have the map version
	       I'Type -> fun(product(list(infin_map(_,_),_)),_,_)
	       Make_map_type(T -> infin_map(T2, T3)) 
	       Type_of_val(L, infin_map(T2, T3) -> TL)
	       Make_map_type(TL -> fin_map(T4, T5))
	       where(fin_map(T4, T5) -> T1)
	     ||
	       where(TD -> T1)
	     |)
	   || -- exp : Nat >< Int -~-> Nat
	     eq(Op, exp)
	     (|
	       -- check we have the integer version
	       I'Type -> fun(product(list(int,_)),_,_)	     
	       Type_of_val(L, int -> TL)
	       Static_subtype(TL, nat)
	       where(nat -> T1)
	     ||
	       where(TD -> T1)
	     |)
	   ||
	     -- other operators
	     where(TD -> T1)
	   |)
	 ||
	   where(TD -> T1)
	 |)

  'rule' Type_of_val(prefix_occ(P, I, _, V), T -> T1):
	 -- make default first in case nothing better
	 I'Type -> FT
	 Type_of_application(list(fun_arg(P, list(V, nil)), nil), FT -> TD0)
	 -- but this default can be polymorphic
	 Contains_any_or_poly(TD0, nil -> Found)
	 (|
	   eq(Found, found)
	   where(T -> TD)
	 ||
	   where(TD0 -> TD)
	 |)
	 (|
	   -- check we have a built-in operator
	   I'Ident -> op_op(Op)
	   Built_in(Op, I)
	   (| -- abs : Int -> Nat
	     eq(Op, abs)
	     (| -- integer version
	       I'Type -> fun(int,_,_)
	       where(nat -> T1)
	     || -- real version
	       IsTimed()
	       where(time -> T1)
	     ||
	       where(TYPE_EXPR'real -> T1)
	     |)
	   ||
	     (| eq(Op, card) || eq(Op, len) |)
	     where(nat -> T1)
	   || -- inds : T-list -> Nat-set
	     eq(Op, inds)
	     (|
	       Type_of_val(V, infin_list(any) -> TV)
	       (|
		 Make_list_type(TV -> fin_list(_))
		 where(fin_set(nat) -> T1)
	       ||
		 Make_list_type(TV -> infin_list(_))
		 where(infin_set(nat) -> T1)
	       |)
	     ||
	       where(TD -> T1)
	     |)
	   || -- elems : T-list -> T-set
	     eq(Op, elems)
	     (|
	       Make_set_type(T -> infin_set(T2))
	       Type_of_val(V, infin_list(T2) -> TV)
	       (|
		 Make_list_type(TV -> fin_list(T3))
		 where(fin_set(T3) -> T1)
	       ||
		 Make_list_type(TV -> infin_list(T3))
		 where(infin_set(T3) -> T1)
	       |)
	     ||
	       where(TD -> T1)
	     |)
	   || -- tl : T-list -~-> T-list
	     eq(Op, tl)
	     (|
	       Make_list_type(T -> infin_list(T2))
	       Type_of_val(V, infin_list(T2) -> TV)
	       (|
		 Make_list_type(TV -> fin_list(T3))
		 (|
		   eq(T3, char)
		   where(TYPE_EXPR'text -> T1)
		 ||
		   where(fin_list(T3) -> T1)
		 |)
	       ||
	         Make_list_type(TV -> infin_list(T3))
		 where(infin_list(T3) -> T1)
	       |)
	     ||
	       where(TD -> T1)
	     |)
	   || -- dom : (T -m-> R) -> T-set
	     eq(Op, dom)
	     (|
	       Make_set_type(T -> infin_set(T2))
	       Type_of_val(V, infin_map(T2, any) -> TV)
	       (|
	         Make_map_type(TV -> fin_map(T3, _))
	         where(fin_set(T3) -> T1)
	       ||
	         Make_map_type(TV -> infin_map(T3, _))
		 where(infin_set(T3) -> T1)
	       |)
	     ||
	       where(TD -> T1)
	     |)
	   || -- rng : (T -m-> R) -> R-set
	     eq(Op, rng)
	     (|
	       Make_set_type(T -> infin_set(T2))
	       Type_of_val(V, infin_map(any, T2) -> TV)
	       (|
	         Make_map_type(TV -> fin_map(_, T3))
	         where(fin_set(T3) -> T1)
	       ||
	         Make_map_type(TV -> infin_map(_, T3))
	         where(infin_set(T3) -> T1)
	       |)
	     ||
	       where(TD -> T1)
	     |)
	   || -- plus : Nat -> Nat
	     eq(Op, plus)
	     (|
	       -- check we have the integer version
	       I'Type -> fun(int,_,_)
	       Type_of_val(V, int -> TV)
	       Static_subtype(TV, nat)
	       where(TV -> T1)
	     ||
	       where(TD -> T1)
	     |)
	   || -- int : Time -> Nat
	     IsTimed()
	     eq(Op, int)
	     Type_of_val(V, real -> TV)
	     Static_subtype(TV, time)
	     where(nat -> T1)
	   || -- real : Nat -> Time
	     IsTimed()
	     eq(Op, real)
	     Type_of_val(V, int -> TV)
	     Static_subtype(TV, nat)
	     where(time -> T1)	   
	   ||
	     -- other operators
	     where(TD -> T1)
	   |)
	 ||
	   where(TD -> T1)
	 |)

-- final default
  'rule' Type_of_val(_, T -> T):

'action' Type_of_val_product(VALUE_EXPRS, PRODUCT_TYPE -> PRODUCT_TYPE)

  'rule' Type_of_val_product(list(V, VS), list(T, TS) -> list(T1, TS1)):
	 Type_of_val(V, T -> T1)
	 Type_of_val_product(VS, TS -> TS1)

  'rule' Type_of_val_product(nil, nil -> nil):

'action' Type_of_vals(VALUE_EXPRS, TYPE_EXPR -> TYPE_EXPR)

  'rule' Type_of_vals(nil, T -> T):

  'rule' Type_of_vals(list(V, nil), T -> T1):
	 Type_of_val(V, T -> T1)

  'rule' Type_of_vals(list(V, VS), T -> T1):
	 Type_of_val(V, T -> T2)
	 Type_of_vals(VS, T -> T3)
	 Match_up(T2, T3 -> T1)

'action' Type_of_pairs(VALUE_EXPR_PAIRS, TYPE_EXPR, TYPE_EXPR -> TYPE_EXPR, TYPE_EXPR)

  'rule' Type_of_pairs(nil, D, R -> D, R):

  'rule' Type_of_pairs(list(pair(LV,RV), nil), D, R -> D1, R1):
	 Type_of_val(LV, D -> D1)
	 Type_of_val(RV, R -> R1)

  'rule' Type_of_pairs(list(pair(LV,RV), PRS), D, R -> D1, R1):
	 Type_of_val(LV, D -> D2)
	 Type_of_val(RV, R -> R2)
	 Type_of_pairs(PRS, D, R -> D3, R3)
	 Match_up(D2, D3 -> D1)
	 Match_up(R2, R3 -> R1)

'action' Type_of_application(ACTUAL_FUNCTION_PARAMETERS, TYPE_EXPR -> TYPE_EXPR)

  'rule' Type_of_application(list(ARG, ARGS), T -> T1):
	 Split_fun_type(T -> _, T3)
	 Type_of_application(ARGS, T3 -> T1)

  'rule' Type_of_application(nil, T -> T):

'action' Type_of_elsif(ELSIF_BRANCHES, TYPE_EXPR -> TYPE_EXPR)

  'rule' Type_of_elsif(list(elsif(_,_,V,_), nil), T -> T1):
	 Type_of_val(V, T -> T1)

  'rule' Type_of_elsif(list(elsif(_,_,V,_), E), T -> T1):
	 Type_of_val(V, T -> T2)
	 Type_of_elsif(E, T -> T3)
	 Match_up(T2, T3 -> T1)

'action' Type_of_cases(CASE_BRANCHES, TYPE_EXPR -> TYPE_EXPR)

  'rule' Type_of_cases(list(case(_,_,V,_), nil), T -> T1):
	 Type_of_val(V, T -> T1)

  'rule' Type_of_cases(list(case(_,_,V,_), CS), T -> T1):
	 Type_of_val(V, T -> T2)
	 Type_of_cases(CS, T -> T3)
	 Match_up(T2, T3 -> T1)

'condition' Built_in(OP, Value_id)

  'rule' Built_in(Op, I):
	 Lookup_op_types(Op -> Is)
	 Isin_value_ids(I, Is)

'condition' Isin_value_ids(Value_id, Value_ids)

  'rule' Isin_value_ids(I, list(Id, Ids))
	 (| eq(I, Id) || Isin_value_ids(I, Ids) |)

--------------------------------------------------------------------
-- Pattern matching

'action' Pattern_match(VALUE_EXPR, PATTERN -> VALUE_EXPR, LET_DEFS)

  'rule' Pattern_match(V, literal_pattern(P, L) ->
			infix_occ(P, V, Ieq, nil, literal_expr(P, L)), nil):
	 Id_of_eq -> Ieq

  'rule' Pattern_match(V, id_pattern(P, Id) -> no_val, list(D, nil)):
	 where(explicit(P, binding(P, single(P, Id)), V) -> D)

  'rule' Pattern_match(V, wildcard_pattern -> no_val, nil):

  'rule' Pattern_match(product(_, VL), product_pattern(P, Patts) -> V1, D):
	 Prod_pattern_match(P, VL, Patts -> V1, D)

  'rule' Pattern_match(V, product_pattern(P, list(Patt, nil)) -> V1, D):
	 Pattern_match(V, Patt -> V1, D)

  'rule' Pattern_match(V, product_pattern(P, Patts) -> QV, list(D, DS)):
	 Length_ps(Patts -> N)
	 Make_results(V -> list(result(T,_,_,_,_),_))
	 Make_product_type(T, N -> XT)
	 Make_pattern_typings(P, XT, 1 -> TL)
	 Pattern_typings_to_exprs(TL -> VL)
	 Pattern_typings_to_bindings(TL -> BL)
	 Pattern_match(product(P, VL), product_pattern(P, Patts) -> VR, DS)
	 where(explicit(P, binding(P, product(P, BL)), V) -> D)
	 (|
	   (| SMLWanted() || FDRWanted() |)
	   where(let_expr(P, list(D, nil), VR) -> QV)
	 ||
	   where(quantified(P, exists, TL, restriction(P, VR)) -> QV)
	 |)

  'rule' Pattern_match(V, enum_list(P, Patts) -> V01, D):
	 Length_ps(Patts -> N)
	 Int_to_string(N -> NS)
	 string_to_id(NS -> Nid)
	 Id_of_len -> Ilen
	 Id_of_eq -> Ieq
	 where(VALUE_EXPR'infix_occ(P, prefix_occ(P, Ilen, nil, V), Ieq, nil,
					  literal_expr(P, int(Nid))) -> V0)
	 List_pattern_match(P, V, Patts -> V1, D)
	 where(ax_infix(P, V0, and, V1, P) -> V01)

  'rule' Pattern_match(V,  conc_list(P, Patts, Patt) -> V012, D012):
	 Length_ps(Patts -> N)
	 Int_to_string(N -> NS)
	 string_to_id(NS -> Nid)
	 Id_of_len -> Ilen
	 Id_of_ge_int -> Ige
	 where(VALUE_EXPR'infix_occ(P, prefix_occ(P, Ilen, nil, V), Ige, nil,
					  literal_expr(P, int(Nid))) -> V0)
	 List_pattern_match(P, V, Patts -> V1, D1)
	 Tl_n(P, V, N -> Tlnv)
	 Pattern_match(Tlnv, Patt -> V2, D2)
	 where(ax_infix(P, V1, and, V2, P) -> V12)
	 where(ax_infix(P, V0, and, V12, P) -> V012)
	 Append_defs(D1, D2 -> D012)

  'rule' Pattern_match(V, name_occ_pattern(P, Id, Q) -> V1, nil):
	 Id_of_eq -> Ieq
	 where(VALUE_EXPR'infix_occ(P, V, Ieq, nil, val_occ(P, Id, Q)) -> V1)
  
  'rule' Pattern_match(V, record_occ_pattern(P, Id, Q, Patts) ->
						    QV, DS):
	 (| PVSWanted() || SALWanted() |)
	 Id'Type -> T
	 Id'Pos -> Pos
	 Make_function_type(T -> fun(DT, _, result(RT,_,_,_,_)))
	 where(RT -> defined(I, _))
	 where(ACTUAL_FUNCTION_PARAMETERS'list(fun_arg(P,list(V,nil)),nil) -> Args)

	 where(T ->fun(DT1, _, result(RT1,_,_,_,_)))
	 (|
	   I'Type -> sort(record(Comps))
	   where(no_val -> QV1)
	 ||
	   I'Type -> sort(variant(Variants))
	   Get_variant_components(Id, Variants -> Comps)
	   Id'Ident -> id_op(Ident)
	   id_to_string(Ident -> S)
	   Concatenate(S, "?" -> S1)
	   string_to_id(S1 -> Ident1)
	   New_value_id(Pos, id_op(Ident1) -> Id1)
	   Id1'Type <- fun(RT, total, result(bool,nil,nil,nil,nil))
	   where(VALUE_EXPR'application(P, val_occ(P, Id1, Q), Args) -> QV1)
	 ||
	   Puterror(P)
	   Putmsg("Pattern not constructor of record or variant")
	   Putnl()
	   where(COMPONENTS'nil -> Comps)
	   where(no_val -> QV1)
	 |)
	 Make_destructor_apps(P, Args, Q, Comps -> Apps)
	 Prod_pattern_match(P, Apps, Patts -> QV2, DS)
	 where(ax_infix(P, QV1, and, QV2, P) -> QV)


  'rule' Pattern_match(V, record_occ_pattern(P, Id, Q, Patts) ->
						    QV, list(D,DS)):
	 Id'Type -> T
	 Make_function_type(T -> fun(DT, _, result(RT,_,_,_,_)))
	 Make_pattern_typings(P, DT, 1 -> TL)
	 Pattern_typings_to_exprs(TL -> VL)
	 Pattern_typings_to_patts(TL -> PL)
	 (| -- check for record type constructor (not variant)
	   where(RT -> defined(I, _))
	   I'Type -> sort(record(_))
	   Id'Ident -> id_op(Cid)
	   I'Ident -> Tid
	   id_to_string(Tid -> TS)
	   Make_mk_name(TS -> CTS)
	   string_to_id(CTS -> CTid)
	   eq(Cid, CTid)
	   where(no_val -> V1)
	 ||
	   where(VALUE_EXPR'application(P, val_occ(P, Id, Q),
				list(fun_arg(P, VL), nil)) -> App)
	   Id_of_eq -> Ieq
	   where(VALUE_EXPR'infix_occ(P, V, Ieq, nil, App) -> V1)
	 |)
	 where(explicit(P,
	            pattern(P, record_occ_pattern(P, Id, Q, PL)), V)
		    -> D)
	 Pattern_match(product(P, VL), product_pattern(P, Patts) -> V2, DS)
	 where(ax_infix(P, V1, and, V2, P) -> VR)
	 where(quantified(P, exists, TL, restriction(P, VR)) -> QV)

-- debug
--   'rule' Pattern_match(V, Patt -> no_val, nil)
-- Print_expr(V)
-- Putnl()
-- Print_pattern(Patt)
-- Putnl()
-- print(Patt)

'action' Prod_pattern_match(POS, VALUE_EXPRS, PATTERNS -> VALUE_EXPR, LET_DEFS)

  'rule' Prod_pattern_match(P, list(V, nil), list(Patt, nil) -> V1, DS):
	 Pattern_match(V, Patt -> V1, DS)

  'rule' Prod_pattern_match(P, list(V, VL), list(Patt, Patts) -> V3, DS):
	 Pattern_match(V, Patt -> V1, DS1)
	 Prod_pattern_match(P, VL, Patts -> V2, DS2)
	 where(ax_infix(P, V1, and, V2, P) -> V3)
	 Append_defs(DS1, DS2 -> DS)

-- debug
--   'rule' Prod_pattern_match(P, VL, Patts -> no_val, nil):
-- Print_expr(product(P, VL))
-- Putnl()
-- Print_pattern(product_pattern(P, Patts))
-- Putnl()

'action' List_pattern_match(POS, VALUE_EXPR, PATTERNS -> VALUE_EXPR, LET_DEFS)

  'rule' List_pattern_match(P, V, list(Patt, Patts) -> V3, DS)
	 Id_of_hd_list -> Ihd
	 Pattern_match(prefix_occ(P, Ihd, nil, V), Patt -> V1, DS1)
	 Id_of_tl -> Itl
	 List_pattern_match(P, prefix_occ(P, Itl, nil, V), Patts -> V2, DS2)
	 where(ax_infix(P, V1, and, V2, P) -> V3)
	 Append_defs(DS1, DS2 -> DS)

  'rule' List_pattern_match(_, _, nil -> no_val, nil):

'condition' Get_variant_components(Value_id, VARIANTS -> COMPONENTS)

  'rule' Get_variant_components(I, list(V, VS) -> Comps):
	 (|
	   where(V -> record(_, con_ref(CI), Comps))
	   eq(I, CI)
	 ||
	   Get_variant_components(I, VS -> Comps)
	 |)


'action' Make_destructor_apps(POS, ACTUAL_FUNCTION_PARAMETERS,
				   OPT_QUALIFICATION, COMPONENTS -> VALUE_EXPRS)

  'rule' Make_destructor_apps(P, As, Q, list(C, CS) -> list(V, VS)):
	 where(C -> component(PC, D, _, _))
	 (|
	   where(D -> dest_ref(I))
	   where(VALUE_EXPR'application(P, val_occ(P, I, Q), As) -> V)
	 ||
	   Puterror(PC)
	   Putmsg("Missing destructor")
	   Putnl()
	   where(no_val -> V)
	 |)
	 Make_destructor_apps(P, As, Q, CS -> VS)

  'rule' Make_destructor_apps(_, _, _, nil -> nil):
  
'action' Tl_n(POS, VALUE_EXPR, INT -> VALUE_EXPR)

  'rule' Tl_n(_, V, N -> V):
	 eq(N, 0)

  'rule' Tl_n(P, V, N -> prefix_occ(P, Itl, nil, V1)):
	 Id_of_tl -> Itl
	 Tl_n(P, V, N-1 -> V1)

'action' Append_defs(LET_DEFS, LET_DEFS -> LET_DEFS)

  'rule' Append_defs(nil, D -> D):

  'rule' Append_defs(list(D, DS0), DS1 -> list(D, DS)):
	 Append_defs(DS0, DS1 -> DS)

'action' Make_pattern_typings(POS, TYPE_EXPR, INT -> TYPINGS)

  'rule' Make_pattern_typings(P, product(list(T, nil)), N -> list(TY, nil)):
	 Make_typing(P, T, N -> TY)

  'rule' Make_pattern_typings(P, product(list(T, TP)), N -> list(TY, TL)):
	 Make_typing(P, T, N -> TY)
	 Make_pattern_typings(P, product(TP), N+1 -> TL)

  'rule' Make_pattern_typings(P, T, N -> list(TY, nil)):
	 Make_typing(P, T, N -> TY)

'action' Make_typing(POS, TYPE_EXPR, INT -> TYPING)

  'rule' Make_typing(P, T, N -> single(P, B, T)):
	 Make_binding(P, N -> B)

'action' Make_binding(POS, INT -> BINDING)

  'rule' Make_binding(P, N -> single(P, id_op(Id))):
	 Int_to_string(N -> NS)
	 Concatenate3("x", NS, "_" -> Nid)
	 string_to_id(Nid -> Id)

'action' Pattern_typings_to_exprs(TYPINGS -> VALUE_EXPRS)

  'rule' Pattern_typings_to_exprs(list(TY, TL) -> list(V, VL)):
	 Pattern_typing_to_expr(TY -> V)
	 Pattern_typings_to_exprs(TL -> VL)

  'rule' Pattern_typings_to_exprs(nil -> nil)

'action' Pattern_typing_to_expr(TYPING -> VALUE_EXPR)

  'rule' Pattern_typing_to_expr(single(_, single(P, Id), T) ->
						 val_occ(P, I, nil)):
	 New_value_id(P, Id -> I)
	 I'Type <- T

'action' Pattern_typings_to_bindings(TYPINGS -> BINDINGS)

  'rule' Pattern_typings_to_bindings(list(TY, TL) -> list(B, BL)):
	 Pattern_typing_to_binding(TY -> B)
	 Pattern_typings_to_bindings(TL -> BL)

  'rule' Pattern_typings_to_bindings(nil -> nil):

'action' Pattern_typing_to_binding(TYPING -> BINDING)

  'rule' Pattern_typing_to_binding(single(_, B, _) -> B):

'action' Pattern_typings_to_patts(TYPINGS -> PATTERNS)

  'rule' Pattern_typings_to_patts(list(TY, TL) -> list(P, PL)):
	 Pattern_typing_to_patt(TY -> P)
	 Pattern_typings_to_patts(TL -> PL)

  'rule' Pattern_typings_to_patts(nil -> nil):

'action' Pattern_typing_to_patt(TYPING -> PATTERN)

  'rule' Pattern_typing_to_patt(single(_, single(P, Id), T) -> 
				       id_pattern(P, Id)):



