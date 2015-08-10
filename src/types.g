-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the functions for looking up type names
-- plus the second pass of the type checker: Complete_type_env
-- plus Unify (which finds the least upper bound of two types)
-- plus Subtype (to check one type is a subtype of another)

'module' types

'use' ast print ext env values

'export' 
-- Make type definitions
   Make_type_env_defs Complete_type_env Check_duplicate_types

-- Check types
   Lookup_type_id Lookup_type_name Lookup_current_type_name
   Lookup_env_type_name Lookup_env
   TYPE_EXPRS Match Match_up Unify_by_result Unify_to_resolve
   Poly_disambiguate_type No_unification
   Make_result_types Length_bs Length_pr Length_ps Length_vs
   Check_type_defined Check_access_defined
   Check_object_defined Env_of_defined_object
   Make_function_type Make_map_type Make_array_type
   Make_product_type Make_any_product
   Make_list_type Make_set_type Supertype_of_vals
   Qualify_class_env
   Unfold_type_id Unfold_type_id_check Notin
   Qualify_by_with
   Remove_Brackets


------------------------------------------------------------------------
-- Type lookup
------------------------------------------------------------------------

'action' Lookup_type_id(POS, IDENT -> OPT_TYPE_ID)
	 
  'rule' Lookup_type_id(P, Id -> I):
	 Lookup_type_name(name(P, id_op(Id)) -> I)

'action' Lookup_type_name(NAME -> OPT_TYPE_ID)

  'rule' Lookup_type_name(N -> I):
	 Current -> C
	 Extend_paths -> Paths
	 Lookup_current_type_name(N, C, Paths, ownenv, ownclass -> I)

'action' Lookup_current_type_name(NAME, CURRENT_ENV, PATHS, OWNENV, OWNCLASS -> OPT_TYPE_ID)

  'rule' Lookup_current_type_name(N, C, Paths, Ownenv, Ownclass -> I):
	 where(C -> current_env(CE, C1))
-- debug
-- print(C)
	 where(Paths -> list(Path, Paths1))
	 Get_current_path_env(CE, Path -> CE1)
-- print(CE1)
	 (|
	   where(CE1 -> instantiation_env(PF, CE2))
	 ||
	   where(PARAM_FIT'nil -> PF)
	   where(CE1 -> CE2)
	 |)
	 Lookup_env_type_name(N, CE2, Ownenv, Ownclass -> Oid)
-- debug
-- Putmsg("Looking for ")
-- Print_name(N)
-- (| eq(Ownclass, ownclass) Putmsg(" in ownclass\n") || Putmsg(" in\n") |)
-- print(CE1)
	 (|
	   ne(Oid,nil)
	   where(Oid -> I)
	 ||
	   (|
	     -- do not look outside own scheme instantiation
	     eq(Ownclass, ownclass)
	     ne(PF, nil)
	     where(OPT_TYPE_ID'nil -> I)
	   ||
	     Lookup_current_type_name1(N, C, Paths, Ownenv, Ownclass -> I)
	   |)
	 |)

  'rule' Lookup_current_type_name(N, nil, Paths, Ownenv, Ownclass -> nil)

'action' Lookup_current_type_name1(NAME, CURRENT_ENV, PATHS, OWNENV, OWNCLASS -> OPT_TYPE_ID)

  'rule' Lookup_current_type_name1(N, C, Paths, Ownenv, Ownclass -> I):
	 where(C -> current_env(CE, C1))
	 where(Paths -> list(Path, Paths1))
	 (|
	   eq(Path, nil)
	   Lookup_current_type_name(N, C1, Paths1, Ownenv, Ownclass -> I)
	 ||
	   Up1(Path -> Up_path, Up_step)
	   -- check left branch if any before moving up
	   (|
	     where(Up_step -> right(nil))
	     Out_scope(Path -> Path1)
	     Get_current_path_env(CE, Path1 -> CE3)
	     DefaultPos(-> P)
	     Lookup_env_type_name(N, CE3, nil, Ownclass -> Oid3)
	   ||
	     where(OPT_TYPE_ID'nil -> Oid3)
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
	       where(OPT_TYPE_ID'nil -> I)
	     ||
	       Lookup_current_type_name1(N, C, list(Up_path, Paths1), Ownenv, Ownclass -> I)
	     |)
	   |)
	 |)

'action' Lookup_env_type_name(NAME, CLASS_ENV, OWNENV, OWNCLASS  -> OPT_TYPE_ID)

  'rule' Lookup_env_type_name(N, nil, Ownenv, Ownclass -> nil):

  'rule' Lookup_env_type_name(N, instantiation_env(PF, CE), Ownenv, Ownclass -> I):
	 Lookup_env_type_name(N, CE, OWNENV'nil, OWNCLASS'nil -> I)

  'rule' Lookup_env_type_name(N, CE, Ownenv, Ownclass -> I):
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
	     where(CE -> basic_env(TE,_,_,_,_,_,_,_,_,Objs,_))
	     -- only use withs if own environment
	     (|
	       eq(Ownenv,ownenv)
	       Lookup_type_name1(N1, N1, TE, Objs, ownenv, Ownclass -> I)
	     ||
	       Lookup_type_name1(N1, N1, TE, nil, nil, Ownclass -> I)
	     |)
	   ||
	     where(CE -> extend_env(CE1, CE2, _, _))
	     Lookup_env_type_name(N1, CE2, Ownenv, Ownclass -> I2)
	     (|
	       ne(I2,nil)
	       where(I2 -> I)
	     ||
	       Lookup_env_type_name(N1, CE1, Ownenv, Ownclass -> I)
	     |)
	   |)
	 ||
	   where(OPT_TYPE_ID'nil -> I)
	 |)


'action' Lookup_type_name1(NAME, NAME, TYPE_ENV, OBJECT_EXPRS, OWNENV, OWNCLASS -> OPT_TYPE_ID)

  'rule' Lookup_type_name1(Base, N, TE, Objs, Ownenv, Ownclass -> I):
-- use Objs list in order since 
-- "with A in with B in ... T" means T may be found as T, B.T, A.T or A.B.T
-- and the list will be internally B, A, A.B
-- We look in this order
-- debug
-- Putmsg("Looking for type ")
-- Print_name(N)
-- Putmsg(" with ")
-- Print_objects(Objs)
-- Putnl()
	 Lookup_type_name2(N, TE, Ownenv, Ownclass -> I1)
	 (|
	   eq(I1, nil)
	   (|
	     where(Objs -> list(Obj, Objs1))
	     Qualify_name(Obj, Base -> N1)
-- debug
-- Putmsg("Looking for type ")
-- Print_name(N1)
-- Putnl()
-- print(N1)
-- Putnl()
	     Lookup_type_name1(Base, N1, TE, Objs1, Ownenv, Ownclass -> I)
	   ||
	     where(OPT_TYPE_ID'nil -> I)
	   |)
	 ||
	   where(I1 -> I)
	 |)

'action' Lookup_type_name2(NAME, TYPE_ENV, OWNENV, OWNCLASS -> OPT_TYPE_ID)

  'rule' Lookup_type_name2(name(P, id_op(Id)), TE, Ownenv, Ownclass -> I):
	 Lookup_env(Id, TE -> I)

  'rule' Lookup_type_name2(qual_name(P, Obj, id_op(Id)), TE, Ownenv, Ownclass -> I):
-- debug
-- Putmsg("Looking for type ")
-- Print_id(Id)
-- Putmsg(" in object ")
-- Print_object(Obj)
-- (|
-- eq(Ownenv, ownenv)
-- Putmsg(" in ownenv")
-- ||
-- Putmsg(" not in ownenv")
-- |)
-- (|
-- eq(Ownclass, ownclass)
-- Putmsg(" in ownclass")
-- ||
-- Putmsg(" not in ownclass")
-- |)
-- Putnl()
	 Get_object_id1(Obj, Ownenv, Ownclass -> Oid, PF)
	 (|
	   where(Oid -> object_id(OI))
	   OI'Env -> CE
	   (|
	     ne(PF, nil)
	     Fit_name(name(P, id_op(Id)), OI, PF -> N1)
	   ||
	     where(name(P, id_op(Id)) -> N1)
	   |)
-- debug
-- Putmsg("Found object ")
-- Print_object(Obj)
-- Putnl()
-- print(Obj)
-- Putnl()
-- Putmsg("with env")
-- Putnl()
-- print(CE)
-- Putmsg("and looking for name ")
-- Print_name(N1)
-- Putnl()
	   Lookup_env_type_name(N1, CE, nil, nil -> I)
-- Putmsg("found ")
-- print(I)
	 ||
	   where(OPT_TYPE_ID'nil -> I)
	 |)

-- Like Lookup_env_type_name but does not expand withs again
-- Also know not in own environment, so need to adapt
'action' Lookup_env_type_name2(IDENT, CLASS_ENV  -> OPT_TYPE_ID)

  'rule' Lookup_env_type_name2(Id, nil -> nil):

  'rule' Lookup_env_type_name2(Id, instantiation_env(PF, CE) -> I):
	 Lookup_env_type_name2(Id, CE -> I)

  'rule' Lookup_env_type_name2(Id, CE -> I):
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
	     where(CE -> basic_env(TE,_,_,_,_,_,_,_,_,_,_))
	     Lookup_env(Id1, TE -> I)
	   ||
	     where(CE -> extend_env(CE1, CE2, _, _))
	     Lookup_env_type_name2(Id1, CE2 -> I2)
	     (|
	       ne(I2,nil)
	       where(I2 -> I)
	     ||
	       Lookup_env_type_name2(Id1, CE1 -> I)
	     |)
	   |)
	 ||
	   where(OPT_TYPE_ID'nil -> I)
	 |)


-- lookup only in current environment
'action' Lookup_env(IDENT, TYPE_ENV -> OPT_TYPE_ID)

  'rule' Lookup_env(Id, type_env(I2, E) -> I):
	 I2'Ident -> Id2
	 (|
	   ne(Id,Id2)
	   Lookup_env(Id, E -> I)
	 ||
	   where(type_id(I2) -> I)
	 |)

  'rule' Lookup_env(Id, nil -> nil):

'action' Get_type_id(POS, IDENT -> Type_id)

  'rule' Get_type_id(P, Id -> I):
	 Lookup_type_id(P, Id -> Oid)
	 (|
	   where(Oid -> type_id(I))
	 ||
	   New_type_id(P, Id -> I)
	   I'Type <- undef_type
	   Puterror(P)
	   Putmsg("Type identifier ")
	   Print_id(Id)
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   Get_current_types(-> TE)
	   Set_current_types(type_env(I,TE))
	 |)

'action' Get_new_type_id(POS, IDENT -> Type_id)

  'rule' Get_new_type_id(P, Id -> I):
	 Get_current_types(-> TE)
	 (|
	   Lookup_env(Id, TE -> type_id(I))
	   I'Pos -> P1
	   Puterror(P)
	   Putmsg("Type identifier ")
	   Print_id(Id)
	   Putmsg(" already defined at ")
	   PrintPos(P1)
	   Putnl()
	 ||
	   New_type_id(P, Id -> I)
	   Set_current_types(type_env(I,TE))
	 |)

'action' Check_duplicate_types(CLASS_ENV)

  'rule' Check_duplicate_types(instantiation_env(_,CE)):
	 Check_duplicate_types(CE)

  'rule' Check_duplicate_types(extend_env(CE1, CE2, _, _)):
	 Get_env_types(CE2 -> TE)
	 Check_duplicate_types1(TE, CE2, CE1)

'action' Check_duplicate_types1(TYPE_ENV, CLASS_ENV, CLASS_ENV)

  'rule' Check_duplicate_types1(type_env(I, TE), CE1, CE2):
	 I'Ident -> Id
	 I'Pos -> P
	 [|
	   Unadapt_env_name(name(P, id_op(Id)), CE1 -> act_name(N))
	   Lookup_env_type_name(N, CE2, nil, nil -> type_id(I1))
	   Puterror(P)
	   Putmsg("Type ")
	   Print_name(N)
	   Putmsg(" also defined at ")
	   I1'Pos -> P1
	   PrintPos(P1)
	   Putnl()
	 |]
	 Check_duplicate_types1(TE, CE1, CE2)

  'rule' Check_duplicate_types1(nil, CE1, CE2):



------------------------------------------------------------------
-- Make_type_env - part of first pass
------------------------------------------------------------------
'action' Make_type_env(CLASS)

  'rule' Make_type_env(basic(DS)):
	 Make_type_env_decls(DS)

  'rule' Make_type_env(instantiation(name(P,id_op(Id)), Objs)):
	 [| -- allow for failure to find scheme (already reported)
	   Get_id_of_scheme(Id -> scheme_id(I))
	   I'With -> W	 
	   Set_current_with(W)
	   I'Params -> PARMS
	   I'Class -> CL
	   Make_type_env(CL)
	 |]

  'rule' Make_type_env(extend(CL1, CL2)):
	 In_left 
	 Make_type_env(CL1)
	 Left_right
	 Make_type_env(CL2)
	 Out_right
	 Get_current_env(-> CE)
	 Check_duplicate_types(CE)
	 
  'rule' Make_type_env(hide(H, C)):
	 Make_type_env(C)

  'rule' Make_type_env(rename(R, C)):
	 Make_type_env(C)

  'rule' Make_type_env(with(P,Obj, C))
	 Make_type_env(C)
	 -- with put in environment by Make_basic_env

-- debug
--   'rule' Make_type_env(CL)
-- print(CL)
-- Current -> C
-- print(C)

'action' Make_type_env_decls(DECLS)

  'rule' Make_type_env_decls(list(D,DS)):
	 Make_type_env_decl(D)
	 Make_type_env_decls(DS)

  'rule' Make_type_env_decls(nil):

'action' Make_type_env_decl(DECL)

  'rule' Make_type_env_decl(object_decl(P,Defs)):
	 Make_object_type_env_defs(Defs)

  'rule' Make_type_env_decl(type_decl(P,Defs)):
	 Make_type_env_defs(Defs)

  'rule' Make_type_env_decl(D):

'action' Make_object_type_env_defs(OBJECT_DEFS)

  'rule' Make_object_type_env_defs(list(D,DS)):
	 Make_object_type_env_def(D)
	 Make_object_type_env_defs(DS)

  'rule' Make_object_type_env_defs(nil):

'action' Make_object_type_env_def(OBJECT_DEF)

  'rule' Make_object_type_env_def(odef(P, Id, TS, CL)):
	 Get_current_modules(-> ME)
	 Lookup_object_in_module(Id, ME -> Oid)
	 (|
	   where(Oid -> object_id(I))
	   Current -> C
	   I'Env -> CE
	   Current <- current_env(CE,C)
	   Extend_paths -> Paths
	   Extend_paths <- list(nil,Paths)
	   Make_type_env(CL)
	   Extend_paths <- Paths
	   Current -> current_env(CE1,C1)
	   I'Env <- CE1
	   Current <- C1
	 ||
	   Puterror(P)
	   Putmsg("Object ")
	   Print_id(Id)
	   Putmsg(" is hidden, renamed, or or not defined")
	   Putnl()
	 |)


'action' Make_type_env_defs(TYPE_DEFS)

  'rule' Make_type_env_defs(list(H,T)):
	 Make_type_env_def(H)
	 Make_type_env_defs(T)

  'rule' Make_type_env_defs(nil):

'action' Make_type_env_def(TYPE_DEF)

  'rule' Make_type_env_def(sort(P,Id)):
	 Define_sort(P,Id,abstract)

  'rule' Make_type_env_def(variant(P, Id, VARS)):
	 Define_sort(P,Id,variant(VARS))

  'rule' Make_type_env_def(record(P, Id, COMPS)):
	 Define_sort(P,Id,record(COMPS))

  'rule' Make_type_env_def(union(P, Id, CHS)):
	 Define_sort(P,Id,union(CHS))

  'rule' Make_type_env_def(abbrev(P,Id,Type))
	 Define_abbrev(P,Id,Type)

'action' Define_sort(POS,IDENT,SORT_KIND)

  'rule' Define_sort(P,Id,K)
	 Get_new_type_id(P, Id -> I)
	 I'Type <- sort(K)
	 
'action' Define_abbrev(POS, IDENT, TYPE_EXPR)

  'rule' Define_abbrev(P, Id, Type):
	 Get_new_type_id(P, Id -> I)
	 I'Type <- undef_type


-----------------------------------------------------------------------
-- Complete abbreviations: second pass
-----------------------------------------------------------------------

'action' Complete_type_env(CLASS)

  'rule' Complete_type_env(basic(DS)):
	 Complete_type_env_decls(DS)
-- debug
-- Get_current_env(-> class_env(TYP,VAL,_,_,_,_,_,_))
-- Print_type_env(TYP)
-- print(TYP)

  'rule' Complete_type_env(instantiation(N, Objs)):
	 (|
	   where(N -> name(P,id_op(Id)))
	 || -- error of using qualified scheme name already reporte
	    -- in Make_basic_env
	   where(N -> qual_name(P, _, id_op(Id)))
	 |)
-- debug
-- Putmsg("Instantiating ")
-- Print_id(Id)
-- Putnl()
	 [| -- allow for failure to find scheme
	    ---(already reported in Make_basic_env)
	   Get_id_of_scheme(Id -> scheme_id(I))	 
	   I'With -> W	 
	   Set_current_with(W)
	   I'Params -> PARMS
-- Putmsg("Formals ")
-- print(PARMS)
	   I'Class -> CL
	   -- cannot make params in first pass
	   -- as objects created during first pass
	   Make_actual_params(P, PARMS, Objs)
-- Putmsg("Made params\n")
	   Complete_type_env(CL)
-- Putmsg("Completed type env\n")
-- Putmsg("Current environment: ")
-- Get_current_env(-> CE)
-- print(CE)
-- Putmsg("Complete environment: ")
-- Current -> C
-- print(C)
	 |]

  'rule' Complete_type_env(extend(CL1, CL2)):
	 In_left 
	 Complete_type_env(CL1)
	 Left_right
	 Complete_type_env(CL2)
	 Out_right
	 
  'rule' Complete_type_env(hide(H, C)):
	 Complete_type_env(C)

  'rule' Complete_type_env(rename(R, C)):
	 Complete_type_env(C)

  'rule' Complete_type_env(with(P,Obj, C))
	 Complete_type_env(C)

'action' Complete_type_env_decls(DECLS)

  'rule' Complete_type_env_decls(list(D,DS)):
	 Complete_type_env_decl(D)
	 Complete_type_env_decls(DS)

  'rule' Complete_type_env_decls(nil):

'action' Complete_type_env_decl(DECL)

  'rule' Complete_type_env_decl(object_decl(P,Defs)):
	 Complete_object_type_env_defs(Defs)

  'rule' Complete_type_env_decl(type_decl(P,Defs)):
	 Complete_type_env_defs(Defs)

  'rule' Complete_type_env_decl(D):

'action' Complete_object_type_env_defs(OBJECT_DEFS)

  'rule' Complete_object_type_env_defs(list(D,DS)):
	 Complete_object_type_env_def(D)
	 Complete_object_type_env_defs(DS)

  'rule' Complete_object_type_env_defs(nil):

'action' Complete_object_type_env_def(OBJECT_DEF)

  'rule' Complete_object_type_env_def(odef(P, Id, TS, CL)):
	 [| -- hidden or missing object reported earlier
	    -- in Make_object_type_env_def
	   Get_current_modules(-> ME)
	   Lookup_object_in_module(Id, ME -> object_id(I))
	   Current -> C
	   I'Env -> CE
	   [|
	     ne(TS, nil)
	     Make_single_typing(TS -> TP)
	     where(TP -> single(_,_,T))
	     Check_type_defined(T -> T1)
	     I'Params <- param_type(T1)
	   |]
	   Current <- current_env(CE,C)
	   Extend_paths -> Paths
	   Extend_paths <- list(nil,Paths)
	   Complete_type_env(CL)
	   Extend_paths <- Paths
	   Current -> current_env(CE1,C1)
	   I'Env <- CE1
	   Current <- C1
	 |]  

'action' Complete_type_env_defs(TYPE_DEFS)

  'rule' Complete_type_env_defs(list(H,T)):
	 Complete_type_env_def(H)
	 Complete_type_env_defs(T)

  'rule' Complete_type_env_defs(nil):

'action' Complete_type_env_def(TYPE_DEF)

  'rule' Complete_type_env_def(sort(P,Id)):

  'rule' Complete_type_env_def(variant(P, Id, VARS)):
	 Complete_type_env_variants(VARS)

  'rule' Complete_type_env_def(record(P, Id, COMPS)):
	 Complete_type_env_components(COMPS)

  'rule' Complete_type_env_def(union(P, Id, CHS)):
	 Get_current_types(-> TE)
	 Lookup_env(Id, TE -> type_id(I))
	 Add_coercions(I, CHS, nil)

  'rule' Complete_type_env_def(abbrev(P,Id,Type))
	 Get_current_types(-> TE)
	 Lookup_env(Id, TE -> type_id(I))
-- Print_type(Type)
-- Putnl()
	 Define_type(Type -> Type1)
-- Print_type(Type1)
-- Putmsg(" stored in ")
-- print(I)
	 I'Type <- abbrev(Type1)
	 -- check for circularities
	 Unfold_type_id(I -> T1)
-- debug
-- Print_id(Id)
-- Putmsg(" unfolds to ")
-- Print_type(T1)
-- Putnl()

'action' Complete_type_env_variants(VARIANTS)

  'rule' Complete_type_env_variants(list(record(_,_,COMPS), VS)):
	 Complete_type_env_components(COMPS)
	 Complete_type_env_variants(VS)

  'rule' Complete_type_env_variants(nil):

'action' Complete_type_env_components(COMPONENTS)

  'rule' Complete_type_env_components(list(component(_,_,T,_), CS)):
	 Define_type(T -> T1)
	 Complete_type_env_components(CS)

  'rule' Complete_type_env_components(nil):

-- debug
--   'rule' Complete_type_env_def(T)
-- print(T)
-- Current -> C
-- print(C)

-- replace occurrences of type names with Type_ids
'action' Define_type(TYPE_EXPR -> TYPE_EXPR)

  'rule' Define_type(product(Pr) -> product(Pr1)):
	 Define_type_prod(Pr -> Pr1)

  'rule' Define_type(fin_set(T) -> fin_set(T1)):
	 Define_type(T -> T1)

  'rule' Define_type(infin_set(T) -> infin_set(T1)):
	 Define_type(T -> T1)

  'rule' Define_type(fin_list(T) -> fin_list(T1)):
	 Define_type(T -> T1)

  'rule' Define_type(infin_list(T) -> infin_list(T1)):
	 Define_type(T -> T1)

  'rule' Define_type(fin_map(D,R) -> fin_map(D1,R1)):
	 Define_type(D -> D1)
	 Define_type(R -> R1)

  'rule' Define_type(function(D,ARR,result(ACC,R)) -> fun(D1,ARR,result(R1,RD,WR,IN,OUT))):
	 Check_access_defined(ACC, nil, nil, nil, nil -> RD,WR,IN,OUT)
	 Define_type(D -> D1)
	 Define_type(R -> R1)

  'rule' Define_type(subtype(single(P,B,T),R) -> subtype(single(P,B,T1),R)):
	 Define_type(T -> T1)

  'rule' Define_type(bracket(T) -> bracket(T1)):
	 Define_type(T -> T1)

  'rule' Define_type(named_type(name(P,id_op(Id))) -> T):
	 Get_type_id(P, Id -> I)
	 where(defined(I, nil) -> T)

  'rule' Define_type(named_type(qual_name(P, Obj, id_op(Id))) -> T):
	 Lookup_type_name(qual_name(P, Obj, id_op(Id)) -> Oid)
	 (|
	   where(Oid -> type_id(I))
-- Print_type(defined(I,nil))
-- Putnl()
	   Check_object_defined(Obj -> Obj1, _)
-- Putmsg("Object ")
-- Print_object(Obj)
-- Putmsg(" checked\n")
	   where(defined(I, qualification(Obj1)) -> T)
	 ||
	   Get_object_id(Obj -> Oid1, _)
	   (|
	     where(Oid1 -> object_id(I1))
	     Puterror(P)
	     Putmsg("Type name ")
	     Print_name(qual_name(P, Obj, id_op(Id)))
	     Putmsg(" is hidden, renamed, or not defined")
	     Putnl()
	     where(TYPE_EXPR'any -> T)
	   ||
	     Puterror(P)
	     Putmsg("Object name ")
	     Print_object(Obj)
	     Putmsg(" is hidden, renamed, or not defined")
	     Putnl()
	     where(TYPE_EXPR'any -> T)
	   |)
	 |)

  'rule' Define_type(T -> T):

'action' Define_type_prod(PRODUCT_TYPE -> PRODUCT_TYPE)

  'rule' Define_type_prod(list(T,PR) -> list(T1,PR1)):
	 Define_type(T -> T1)
	 Define_type_prod(PR -> PR1)

  'rule' Define_type_prod(nil -> nil):

-- check for circularites in type abbreviations
'action' Unfold_type_id(Type_id -> TYPE_EXPR)

  'rule' Unfold_type_id(I -> T)
	 I'Type -> T1
	 (|
	   where(T1 -> abbrev(T2))
	   I'Ident -> Id
	   Unfold_type_id_check(list(I,nil), T2 -> T)
	 ||
	   where(T1 -> sort(_))
	   where(defined(I, nil) -> T)
	 ||
	   where(TYPE_EXPR'any -> T)  -- or none?
	 |)

'action' Unfold_type_id_check(Type_ids, TYPE_EXPR -> TYPE_EXPR)

  'rule' Unfold_type_id_check(Is, product(Pr) -> product(Pr1)):
	 Unfold_type_id_check_prod(Is, Pr -> Pr1)

  'rule' Unfold_type_id_check(Is, fin_set(T) -> fin_set(T1)):
	 Unfold_type_id_check(Is, T -> T1)

  'rule' Unfold_type_id_check(Is, infin_set(T) -> infin_set(T1)):
	 Unfold_type_id_check(Is, T -> T1)

  'rule' Unfold_type_id_check(Is, fin_list(T) -> fin_list(T1)):
	 Unfold_type_id_check(Is, T -> T1)

  'rule' Unfold_type_id_check(Is, infin_list(T) -> infin_list(T1)):
	 Unfold_type_id_check(Is, T -> T1)

  'rule' Unfold_type_id_check(Is, fin_map(D,R) -> fin_map(D1,R1)):
	 Unfold_type_id_check(Is, D -> D1)
	 Unfold_type_id_check(Is, R -> R1)

  'rule' Unfold_type_id_check(Is, function(D,ARR,result(ACC,R)) -> function(D1,ARR,result(ACC,R1))):
	 Unfold_type_id_check(Is, D -> D1)
	 Unfold_type_id_check(Is, R -> R1)

  'rule' Unfold_type_id_check(Is, subtype(single(P,B,T),R) -> subtype(single(P,B,T1),R)):
	 Unfold_type_id_check(Is, T -> T1)

  'rule' Unfold_type_id_check(Is, bracket(T) -> bracket(T1)):
	 Unfold_type_id_check(Is, T -> T1)

  'rule' Unfold_type_id_check(Is, defined(I, Q) -> T):
	 I'Ident -> Id
	 (|
	   Notin(I, Is)
	   I'Type -> T1
	   (|
	     where(T1 -> abbrev(T2))
	     Unfold_type_id_check(list(I, Is), T2 -> T)
	   ||
	     where(defined(I, Q) -> T)
	   |)
	 ||
	   I'Pos -> P
	   Puterror(P)
	   Putmsg("Definition of type ")
	   Print_id(Id)
	   Putmsg(" is circular")
	   Putnl()
	   -- change type to none to avoid circularities in unification
	   I'Type <- abbrev(none)
	   where(defined(I, Q) -> T)
	 |)

  'rule' Unfold_type_id_check(Is, named_type(qual_name(P, O, Id)) -> T):
	 (|
	   Lookup_type_name(qual_name(P, O, Id) -> type_id(I))
	   Check_object_defined(O -> O1, _)
	   where(defined(I, qualification(O1)) -> T)
	 ||
	   Puterror(P)
	   Putmsg("Type name ")
	   Print_name(qual_name(P, O, Id))
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   where(TYPE_EXPR'any -> T)
	 |)

  'rule' Unfold_type_id_check(Is, T -> T):

'action' Unfold_type_id_check_prod(Type_ids, PRODUCT_TYPE -> PRODUCT_TYPE)

  'rule' Unfold_type_id_check_prod(Is, list(T,PR) -> list(T1,PR1)):
	 Unfold_type_id_check(Is, T -> T1)
	 Unfold_type_id_check_prod(Is, PR -> PR1)

  'rule' Unfold_type_id_check_prod(Is, nil -> nil):

'condition' Notin(Type_id, Type_ids)

  'rule' Notin(I, list(I2, Is)):
	 ne(I,I2)
	 Notin(I, Is)

  'rule' Notin(I, nil):

'action' Add_coercions(Type_id, todo:CHOICES, done:Type_ids)

  'rule' Add_coercions(I, list(CH, CHS), Is):
	 (|
	   where(CH -> choice(P,N))
	   (|
	     Lookup_type_name(N -> type_id(I1))
	     (|
	       Notin(I1, Is)
	       I1'Coercions_up -> C
	       I1'Coercions_up <- coercions(coercion(I,nil),C)
	       I'Coercions_down -> C1
	       I'Coercions_down <- coercions(coercion(I1,nil),C1)
	       Add_coercions(I, CHS, list(I1,Is))
	     ||
	       Puterror(P)
	       Putmsg("Type name ")
	       Print_name(N)
	       Putmsg(" appears twice in union")
	       Putnl()
	       Add_coercions(I, CHS, Is)
	     |)
	   ||
	     Puterror(P)
	     Putmsg("Type name ")
	     Print_name(N)
	     Putmsg(" is hidden, renamed, or not defined")
	     Putnl()
	     Add_coercions(I, CHS, Is)
	   |)
	 ||
	   -- wildcard
	   Add_coercions(I, CHS, Is)
	 |)

  'rule' Add_coercions(I, nil, Is):

----------------------------------------------------------------
-- Add qualifiers
----------------------------------------------------------------

-- When an object is defined (including formal scheme parameters)
-- all the entities defined in it are qualified (in the Entity_id
-- table)
-- This improves error messages and is also used in checking
-- implementation
-- "any" accesses in function types are also qualified

'action' Qualify_class_env(Object_id, CLASS_ENV -> CLASS_ENV)

  'rule' Qualify_class_env(I, basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD) ->
				basic_env(TYP1, VAL1, VAR1, CH1, MOD1, AX, TC, TS, Prop, WITH, AD)):  
	 Qualify_type_env(I, TYP -> TYP1)
	 Qualify_value_envs(I, VAL -> VAL1)
	 Qualify_variable_env(I, VAR -> VAR1)
	 Qualify_channel_env(I, CH -> CH1)
	 Qualify_module_env(I, MOD -> MOD1)
 
  'rule' Qualify_class_env(I, extend_env(CE1, CE2, WITH, AD) -> extend_env(CE11, CE21, WITH, AD)):
	 Qualify_class_env(I, CE1 -> CE11)
	 Qualify_class_env(I, CE2 -> CE21)

  'rule' Qualify_class_env(I, instantiation_env(PF, CE) -> instantiation_env(PF, CE1)):
	 Qualify_class_env(I, CE -> CE1)  

'action' Qualify_type_env(Object_id, TYPE_ENV -> TYPE_ENV)

  'rule' Qualify_type_env(Id, type_env(I, TE) -> type_env(I, TE1)):
	 I'Qualifier -> Q
	 I'Qualifier <- list(Id,Q)
-- I'Ident -> Tid
-- Putmsg("Type ")
-- Print_id(Tid)
-- Putmsg(" has qualifier ")
-- Print_qualifier(list(Id, Q))
-- Putnl
-- print(I)
	 Qualify_type_env(Id, TE -> TE1)

  'rule' Qualify_type_env(Id, nil -> nil):

'action' Qualify_value_envs(Object_id, VALUE_ENVS -> VALUE_ENVS)

  'rule' Qualify_value_envs(Id, list(VE, VES) -> list(VE1, VES1)):
	 Qualify_value_env(Id, VE -> VE1)
	 Qualify_value_envs(Id, VES -> VES1)

  'rule' Qualify_value_envs(Id, nil -> nil):

'action' Qualify_value_env(Object_id, Value_ids -> Value_ids)

  'rule' Qualify_value_env(Id, list(I, TE) -> list(I, TE1)):
	 I'Qualifier -> Q
	 I'Qualifier <- list(Id,Q)
	 I'Type -> T
	 Qualify_any(Id, T -> T1)
	 I'Type <- T1
	 Qualify_value_env(Id, TE -> TE1)

  'rule' Qualify_value_env(Id, nil -> nil):

'action' Qualify_variable_env(Object_id, VARIABLE_ENV -> VARIABLE_ENV)

  'rule' Qualify_variable_env(Id, variable_env(I, TE) -> variable_env(I, TE1)):
	 I'Qualifier -> Q
	 I'Qualifier <- list(Id,Q)
	 I'Type -> T
	 Qualify_any(Id, T -> T1)
	 I'Type <- T1
	 Qualify_variable_env(Id, TE -> TE1)

  'rule' Qualify_variable_env(Id, nil -> nil):

'action' Qualify_channel_env(Object_id, CHANNEL_ENV -> CHANNEL_ENV)

  'rule' Qualify_channel_env(Id, channel_env(I, TE) -> channel_env(I, TE1)):
	 I'Qualifier -> Q
	 I'Qualifier <- list(Id,Q)
	 I'Type -> T
	 Qualify_any(Id, T -> T1)
	 I'Type <- T1
	 Qualify_channel_env(Id, TE -> TE1)

  'rule' Qualify_channel_env(Id, nil -> nil):

'action' Qualify_module_env(Object_id, MODULE_ENV -> MODULE_ENV)

  'rule' Qualify_module_env(Id, object_env(I, ME) -> object_env(I, ME1)):
	 I'Qualifier -> Q
	 I'Qualifier <- list(Id,Q)
	 I'Env -> CE
	 Qualify_class_env(Id, CE -> CE1)
	 I'Env <- CE1
	 Qualify_module_env(Id, ME -> ME1)

  'rule' Qualify_module_env(Id, nil -> nil):

'action' Qualify_any(Object_id, TYPE_EXPR -> TYPE_EXPR)

  'rule' Qualify_any(I, product(PR) -> product(PR1)):
	 Qualify_any_prod(I, PR -> PR1)

  'rule' Qualify_any(I, fin_set(T) -> fin_set(T1)):
	 Qualify_any(I, T -> T1)

  'rule' Qualify_any(I, infin_set(T) -> infin_set(T1)):
	 Qualify_any(I, T -> T1)

  'rule' Qualify_any(I, fin_list(T) -> fin_list(T1)):
	 Qualify_any(I, T -> T1)

  'rule' Qualify_any(I, infin_list(T) -> infin_list(T1)):
	 Qualify_any(I, T -> T1)

  'rule' Qualify_any(I, fin_map(D, R) -> fin_map(D1, R1)):
	 Qualify_any(I, D -> D1)
	 Qualify_any(I, R -> R1)

  'rule' Qualify_any(I, fun(T, Arr, result(R, RD, WR, IN, OUT)) -> fun(T1, Arr, result(R1, RD1, WR1, IN1, OUT1))):
	 Qualify_any(I, T -> T1)
	 Qualify_any(I, R -> R1)
	 Qualify_accesses(I, RD -> RD1)
	 Qualify_accesses(I, WR -> WR1)
	 Qualify_accesses(I, IN -> IN1)
	 Qualify_accesses(I, OUT -> OUT1)
	 
  'rule' Qualify_any(I, subtype(single(P,B,T),R) -> subtype(single(P,B,T1),R)):
	 Qualify_any(I, T -> T1)

  'rule' Qualify_any(I, bracket(T) -> bracket(T1)):
	 Qualify_any(I, T -> T1)

  'rule' Qualify_any(I, T -> T)

'action' Qualify_any_prod(Object_id, PRODUCT_TYPE -> PRODUCT_TYPE)

  'rule' Qualify_any_prod(I, list(T, TS) -> list(T1, TS1)):
	 Qualify_any(I, T -> T1)
	 Qualify_any_prod(I, TS -> TS1)

  'rule' Qualify_any_prod(I, nil -> nil):
  

'action' Qualify_accesses(Object_id, ACCESSES -> ACCESSES)

  'rule' Qualify_accesses(I, list(A,AS) -> list(A1,AS1)):
	 Qualify_access(I, A -> A1)
	 Qualify_accesses(I, AS -> AS1)

  'rule' Qualify_accesses(I, nil -> nil):

'action' Qualify_access(Object_id, ACCESS -> ACCESS)

  'rule' Qualify_access(I, enumerated_access(P, AS) -> enumerated_access(P, AS1)):
	 Qualify_accesses(I, AS -> AS1)

  'rule' Qualify_access(I, completed_access(P, nil) ->
			   completed_access(P, qualification(obj_occ(P, I)))):

  'rule' Qualify_access(I, comprehended_access(P, A, L) -> comprehended_access(P, A1, L)):
	 Qualify_access(I, A -> A1)

  'rule' Qualify_access(I, A -> A):

-------------------------------------------------------------------
-- Checking - everything defined; no circularities
-- also replace named_type(N) with defined(I)
-- and function(...) with fun(...)
-------------------------------------------------------------------

'action' Check_type_defined(TYPE_EXPR -> TYPE_EXPR)

  'rule' Check_type_defined(defined(I, nil) -> defined(I, Q)):
	 (| -- may be affected by WITH
	   I'Qualifier -> list(Id, _)
	   I'Pos -> P
	   Qualify_by_with(P, Id -> Q)
	 ||
	   where(OPT_QUALIFICATION'nil -> Q)
	 |)
	 
 
  'rule' Check_type_defined(defined(I, qualification(Obj)) -> defined(I, qualification(Obj1))):
	 Check_object_defined(Obj -> Obj1, _)

  'rule' Check_type_defined(named_type(N) -> defined(I, Q)):
-- debug
-- Print_name(N)
-- Putnl()
-- Current -> C
-- print(C)
-- Putnl()
-- Extend_paths -> P
-- print(P)
-- Putnl()
	 Lookup_type_name(N -> type_id(I))
	 (|
	   where(N -> qual_name(_, Obj, _))
	   Check_object_defined(Obj -> Obj1, _)
	   where(qualification(Obj1) -> Q)
	 ||
	   (| -- may be affected by WITH
	     I'Qualifier -> list(Id, _)
	     I'Pos -> P
	     Qualify_by_with(P, Id -> Q)
	   ||
	     where(OPT_QUALIFICATION'nil -> Q)
	   |)
	 |)

  'rule' Check_type_defined(named_type(N) -> any):
	 (|
	   where(N -> name(P,_))
	 ||
	   where(N -> qual_name(P,_,_))
	 |)
	 Puterror(P)
	 Putmsg("Type name ")
	 Print_name(N)
	 Putmsg(" is hidden, renamed, or not defined")
	 Putnl()
-- debug
-- [|
-- Current -> current_env(instantiation_env(param_fit(F,A,_,ADS,_), _), nil)
-- F'Ident -> Fid
-- A'Ident -> Aid
-- Putmsg("Formal: ")
-- Print_id(Fid)
-- Putmsg(" with env ")
-- Putnl()
-- F'Env -> Fenv
-- print(Fenv)
-- Putmsg("Actual: ")
-- Print_id(Aid)
-- Putmsg(" with env ")
-- Putnl()
-- A'Env -> Aenv
-- print(Aenv)
-- Putmsg("Adapts: ")
-- Print_adapts(ADS)
-- Putnl()
-- |]


  'rule' Check_type_defined(product(PR) -> product(PR1)):
	 Check_product_defined(PR -> PR1)

  'rule' Check_type_defined(fin_set(T) -> fin_set(T1)):
	 Check_type_defined(T -> T1)

  'rule' Check_type_defined(infin_set(T) -> infin_set(T1)):
	 Check_type_defined(T -> T1)

  'rule' Check_type_defined(fin_list(T) -> fin_list(T1)):
	 Check_type_defined(T -> T1)

  'rule' Check_type_defined(infin_list(T) -> infin_list(T1)):
	 Check_type_defined(T -> T1)

  'rule' Check_type_defined(fin_map(D,R) -> fin_map(D1,R1)):
	 Check_type_defined(D -> D1)
	 Check_type_defined(R -> R1)

  'rule' Check_type_defined(infin_map(D,R) -> infin_map(D1,R1)):
	 Check_type_defined(D -> D1)
	 Check_type_defined(R -> R1)

  'rule' Check_type_defined(function(D,ARR,result(ACC,R)) -> fun(D1,ARR,result(R1,READ,WRITE,IN,OUT))):
	 Check_type_defined(D -> D1)
	 Check_access_defined(ACC, nil, nil, nil, nil -> READ, WRITE, IN, OUT)
	 Check_type_defined(R -> R1)

  'rule' Check_type_defined(subtype(single(P,B,T),R) -> subtype(single(P,B,T1),R)):
	 Check_type_defined(T -> T1)

  'rule' Check_type_defined(bracket(T) -> bracket(T1)):
	 Check_type_defined(T -> T1)

  'rule' Check_type_defined(array(T1,T2) -> array(T1Res, T2Res))
         Check_type_defined(T1 -> T1Res)
         Check_type_defined(T2 -> T2Res)

  'rule' Check_type_defined(T -> T):

'action' Check_product_defined(PRODUCT_TYPE -> PRODUCT_TYPE)

  'rule' Check_product_defined(list(T,PR) -> list(T1,PR1)):
	 Check_type_defined(T -> T1)
	 Check_product_defined(PR -> PR1)

  'rule' Check_product_defined(nil -> nil):

'action' Check_access_defined(ACCESS_DESCS, ACCESSES, ACCESSES, ACCESSES, ACCESSES -> ACCESSES, ACCESSES, ACCESSES, ACCESSES)

  'rule' Check_access_defined(list(D, DS), READ, WRITE, IN, OUT ->
					   READ2, WRITE2, IN2, OUT2):
	 Check_access_defined1(D, READ, WRITE, IN, OUT ->
					   READ1, WRITE1, IN1, OUT1)
         Check_access_defined(DS, READ1, WRITE1, IN1, OUT1 ->
					   READ2, WRITE2, IN2, OUT2)

  'rule' Check_access_defined(nil, READ, WRITE, IN, OUT ->
					   READ, WRITE, IN, OUT):

'action' Check_access_defined1(ACCESS_DESC, ACCESSES, ACCESSES, ACCESSES, ACCESSES -> ACCESSES, ACCESSES, ACCESSES, ACCESSES)

  'rule' Check_access_defined1(access(read, AS), READ, WRITE, IN, OUT ->
					   READ1, WRITE, IN, OUT)
	 Check_read_accesses(AS, READ -> READ1)

  'rule' Check_access_defined1(access(write, AS), READ, WRITE, IN, OUT ->
					   READ, WRITE1, IN, OUT)
	 Check_write_accesses(AS, WRITE -> WRITE1)

  'rule' Check_access_defined1(access(in, AS), READ, WRITE, IN, OUT ->
					   READ, WRITE, IN1, OUT)
	 Check_in_accesses(AS, IN -> IN1)

  'rule' Check_access_defined1(access(out, AS), READ, WRITE, IN, OUT ->
					   READ, WRITE, IN, OUT1)
	 Check_out_accesses(AS, OUT -> OUT1)

'action' Check_read_accesses(ACCESSES, ACCESSES -> ACCESSES)

  'rule' Check_read_accesses(list(A, AS), READ -> READ2):
	 Check_read_accesses(AS, READ -> READ1)
	 Check_read_access(A, READ1 -> READ2)

  'rule' Check_read_accesses(nil, READ -> READ):

'action' Check_read_access(ACCESS, ACCESSES -> ACCESSES)

  'rule' Check_read_access(named_access(P, N), READ -> READ1):
	 (|
	   Lookup_variable_name(N -> variable_id(I))
	   (|
	     where(N -> qual_name(_, Obj, _))
	     Check_object_defined(Obj -> Obj1, _)
	     where(qualification(Obj1) -> Q)
	   ||
	     where(OPT_QUALIFICATION'nil -> Q)
	   |)
	   where(ACCESSES'list(variable(P, I, Q), READ) -> READ1)
	 ||
	   Puterror(P)
	   Putmsg("Variable name ")
	   Print_name(N)
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   where(READ -> READ1)
	 |)

  'rule' Check_read_access(enumerated_access(P, AS), READ -> READ1):
	 (|
	   Check_read_accesses(AS, nil -> list(A1, AS1))
	   where(ACCESSES'list(enumerated_access(P, list(A1, AS1)), READ) -> READ1)
	 ||
	   where(READ -> READ1)
	 |)

  'rule' Check_read_access(completed_access(P, nil), READ -> list(completed_access(P, nil),READ)):

  'rule' Check_read_access(completed_access(P, qualification(Obj)), READ -> READ1):	 
	 (|
	   Get_object_id(Obj -> object_id(I), PF)
	   [| -- if object found in fitting don't try to check
	     eq(PF, nil)
	     Object_type_check(Obj, I)
	   |]
	   Check_object_defined(Obj -> Obj1, _)
	   where(ACCESSES'list(completed_access(P, qualification(Obj1)), READ) -> READ1)
	 ||
	   Puterror(P)
	   Putmsg("Object ")
	   Print_object(Obj)
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   where(READ -> READ1)
	 |)

  'rule' Check_read_access(comprehended_access(P, A, set_limit(P1,TS,R)), READ -> READ1):
	 Openenv()
	 Define_value_typings(TS)
	 [|
	   where(R -> restriction(P2, V))
	   Make_results(V -> RS)
	   Type_check(P2, result(bool,nil,nil,nil,nil), RS -> RS1) |]
	 (|
	   Check_read_access(A, nil -> list(A1, nil))
	   where(ACCESSES'list(comprehended_access(P, A1, set_limit(P1,TS,R)), READ) -> READ1)
	 ||
	   where(READ -> READ1)
	 |)
	 Closeenv()

'action' Check_write_accesses(ACCESSES, ACCESSES -> ACCESSES)

  'rule' Check_write_accesses(list(A, AS), WRITE -> WRITE2):
	 Check_write_accesses(AS, WRITE -> WRITE1)
	 Check_write_access(A, WRITE1 -> WRITE2)

  'rule' Check_write_accesses(nil, WRITE -> WRITE):

'action' Check_write_access(ACCESS, ACCESSES -> ACCESSES)

  'rule' Check_write_access(named_access(P, N), WRITE -> WRITE1):
	 (|
	   Lookup_variable_name(N -> variable_id(I))
	   (|
	     where(N -> qual_name(_, Obj, _))
	     Check_object_defined(Obj -> Obj1, _)
	     where(qualification(Obj1) -> Q)
	   ||
	     where(OPT_QUALIFICATION'nil -> Q)
	   |)
	   where(ACCESSES'list(variable(P, I, Q), WRITE) -> WRITE1)
	 ||
	   Puterror(P)
	   Putmsg("Variable name ")
	   Print_name(N)
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   where(WRITE -> WRITE1)
	 |)

  'rule' Check_write_access(enumerated_access(P, AS), WRITE -> WRITE1):
	 (|
	   Check_write_accesses(AS, nil -> list(A1, AS1))
	   where(ACCESSES'list(enumerated_access(P, list(A1, AS1)), WRITE) -> WRITE1)
	 ||
	   where(WRITE -> WRITE1)
	 |)

  'rule' Check_write_access(completed_access(P, nil), WRITE -> list(completed_access(P, nil),WRITE)):

  'rule' Check_write_access(completed_access(P, qualification(Obj)), WRITE -> WRITE1):	 
	 (|
	   Get_object_id(Obj -> object_id(I), PF)
	   [| -- if object found in fitting don't try to check
	     eq(PF, nil)
	     Object_type_check(Obj, I)
	   |]
	   Check_object_defined(Obj -> Obj1, _)
	   where(ACCESSES'list(completed_access(P, qualification(Obj1)), WRITE) -> WRITE1)
	 ||
	   Puterror(P)
	   Putmsg("Object ")
	   Print_object(Obj)
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   where(WRITE -> WRITE1)
	 |)

  'rule' Check_write_access(comprehended_access(P, A, set_limit(P1,TS,R)), WRITE -> WRITE1):
	 Openenv()
	 Define_value_typings(TS)
	 [|
	   where(R -> restriction(P2, V))
	   Make_results(V -> RS)
	   Type_check(P2, result(bool,nil,nil,nil,nil), RS -> RS1) |]
	 (|
	   Check_write_access(A, nil -> list(A1, nil))
	   where(ACCESSES'list(comprehended_access(P, A1, set_limit(P1,TS,R)), WRITE) -> WRITE1)
	 ||
	   where(WRITE -> WRITE1)
	 |)
	 Closeenv()

'action' Check_in_accesses(ACCESSES, ACCESSES -> ACCESSES)

  'rule' Check_in_accesses(list(A, AS), IN -> IN2):
	 Check_in_accesses(AS, IN -> IN1)
	 Check_in_access(A, IN1 -> IN2)

  'rule' Check_in_accesses(nil, IN -> IN):

'action' Check_in_access(ACCESS, ACCESSES -> ACCESSES)

  'rule' Check_in_access(named_access(P, N), IN -> IN1):
	 (|
	   Lookup_channel_name(N -> channel_id(I))
	   (|
	     where(N -> qual_name(_, Obj, _))
	     Check_object_defined(Obj -> Obj1, _)
	     where(qualification(Obj1) -> Q)
	   ||
	     where(OPT_QUALIFICATION'nil -> Q)
	   |)
	   where(ACCESSES'list(channel(P, I, Q), IN) -> IN1)
	 ||
	   Puterror(P)
	   Putmsg("Channel name ")
	   Print_name(N)
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   where(IN -> IN1)
	 |)

  'rule' Check_in_access(enumerated_access(P, AS), IN -> IN1):
	 (|
	   Check_in_accesses(AS, nil -> list(A1, AS1))
	   where(ACCESSES'list(enumerated_access(P, list(A1, AS1)), IN) -> IN1)
	 ||
	   where(IN -> IN1)
	 |)

  'rule' Check_in_access(completed_access(P, nil), IN -> list(completed_access(P, nil),IN)):

  'rule' Check_in_access(completed_access(P, qualification(Obj)), IN -> IN1):	 
	 (|
	   Get_object_id(Obj -> object_id(I), PF)
	   [| -- if object found in fitting don't try to check
	     eq(PF, nil)
	     Object_type_check(Obj, I)
	   |]
	   Check_object_defined(Obj -> Obj1, _)
	   where(ACCESSES'list(completed_access(P, qualification(Obj1)), IN) -> IN1)
	 ||
	   Puterror(P)
	   Putmsg("Object ")
	   Print_object(Obj)
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   where(IN -> IN1)
	 |)

  'rule' Check_in_access(comprehended_access(P, A, set_limit(P1,TS,R)), IN -> IN1):
	 Openenv()
	 Define_value_typings(TS)
	 [|
	   where(R -> restriction(P2, V))
	   Make_results(V -> RS)
	   Type_check(P2, result(bool,nil,nil,nil,nil), RS -> RS1) |]
	 (|
	   Check_in_access(A, nil -> list(A1, nil))
	   where(ACCESSES'list(comprehended_access(P, A1, set_limit(P1,TS,R)), IN) -> IN1)
	 ||
	   where(IN -> IN1)
	 |)
	 Closeenv()

'action' Check_out_accesses(ACCESSES, ACCESSES -> ACCESSES)

  'rule' Check_out_accesses(list(A, AS), OUT -> OUT2):
	 Check_out_accesses(AS, OUT -> OUT1)
	 Check_out_access(A, OUT1 -> OUT2)

  'rule' Check_out_accesses(nil, OUT -> OUT):

'action' Check_out_access(ACCESS, ACCESSES -> ACCESSES)

  'rule' Check_out_access(named_access(P, N), OUT -> OUT1):
	 (|
	   Lookup_channel_name(N -> channel_id(I))
	   (|
	     where(N -> qual_name(_, Obj, _))
	     Check_object_defined(Obj -> Obj1, _)
	     where(qualification(Obj1) -> Q)
	   ||
	     where(OPT_QUALIFICATION'nil -> Q)
	   |)
	   where(ACCESSES'list(channel(P, I, Q), OUT) -> OUT1)
	 ||
	   Puterror(P)
	   Putmsg("Channel name ")
	   Print_name(N)
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   where(OUT -> OUT1)
	 |)

  'rule' Check_out_access(enumerated_access(P, AS), OUT -> OUT1):
	 (|
	   Check_out_accesses(AS, nil -> list(A1, AS1))
	   where(ACCESSES'list(enumerated_access(P, list(A1, AS1)), OUT) -> OUT1)
	 ||
	   where(OUT -> OUT1)
	 |)

  'rule' Check_out_access(completed_access(P, nil), OUT -> list(completed_access(P, nil),OUT)):

  'rule' Check_out_access(completed_access(P, qualification(Obj)), OUT -> OUT1):	 
	 (|
	   Get_object_id(Obj -> object_id(I), PF)
	   [| -- if object found in fitting don't try to check
	     eq(PF, nil)
	     Object_type_check(Obj, I)
	   |]
	   Check_object_defined(Obj -> Obj1, _)
	   where(ACCESSES'list(completed_access(P, qualification(Obj1)), OUT) -> OUT1)
	 ||
	   Puterror(P)
	   Putmsg("Object ")
	   Print_object(Obj)
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   where(OUT -> OUT1)
	 |)

  'rule' Check_out_access(comprehended_access(P, A, set_limit(P1,TS,R)), OUT -> OUT1):
	 Openenv()
	 Define_value_typings(TS)
	 [|
	   where(R -> restriction(P2, V))
	   Make_results(V -> RS)
	   Type_check(P2, result(bool,nil,nil,nil,nil), RS -> RS1) |]
	 (|
	   Check_out_access(A, nil -> list(A1, nil))
	   where(ACCESSES'list(comprehended_access(P, A1, set_limit(P1,TS,R)), OUT) -> OUT1)
	 ||
	   where(OUT -> OUT1)
	 |)
	 Closeenv()


'action' Check_object_defined(OBJECT_EXPR -> OBJECT_EXPR, PARAM_FIT)

  'rule' Check_object_defined(obj_name(name(P, id_op(Id))) -> Obj, PF):
         (|
	   Get_object_id(obj_name(name(P, id_op(Id))) -> object_id(I), PF)
	   where(obj_occ(P, I) -> Obj)
	 ||
	   Get_current_with(-> WITH)
	   Check_object_defined_with(name(P, id_op(Id)), WITH -> object_id(I), PF)
	   where(obj_occ(P, I) -> Obj)
	 ||
	   Puterror(P)
	   Putmsg("Object ")
	   Print_object(obj_name(name(P, id_op(Id))))
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   where(obj_name(name(P, id_op(Id))) -> Obj)
	   where(PARAM_FIT'nil -> PF)
	 |)

  'rule' Check_object_defined(obj_name(qual_name(P, Obj, id_op(Id))) -> Obj2, nil):
	 Check_object_defined(Obj -> Obj1, PF)
-- Putmsg("Object ")
-- Print_object(Obj)
-- Putmsg(" checked as ")
-- Print_object(Obj1)
-- Putnl()
	 Env_of_defined_object(Obj1 -> CE)
-- print(CE)
	 (|
	   ne(PF, nil)
	   where(Obj1 -> obj_occ(_, I1))
	   Fit_name(name(P, id_op(Id)), I1, PF -> N1)
	 ||
	   where(name(P, id_op(Id)) -> N1)
	 |)
	 (|
	   Lookup_object_in_env(obj_name(N1), CE, nil -> object_id(I))
	   where(qual_occ(P, Obj1, I) -> Obj2)
	 ||
	   Puterror(P)
	   Putmsg("Object ")
	   Print_object(obj_name(name(P, id_op(Id))))
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   where(obj_name(name(P, id_op(Id))) -> Obj2)
	 |)

  'rule' Check_object_defined(obj_appl(Obj, Parms) -> obj_appl(Obj1, Parms), PF):
	 Check_object_defined(Obj -> Obj1, PF)

  'rule' Check_object_defined(obj_array(TPS, Obj) -> obj_array(TPS, Obj1), PF):
	 Check_object_defined(Obj -> Obj1, PF)

  'rule' Check_object_defined(obj_fit(Obj, RNS) -> obj_fit(Obj1, RNS), PF):
	 Check_object_defined(Obj -> Obj1, PF)

  'rule' Check_object_defined(obj_occ(P, I) -> obj_occ(P, I), nil):

  'rule' Check_object_defined(qual_occ(P, Obj, I) -> qual_occ(P, Obj1, I), nil):
	 I'Env -> CE
	 Check_object_defined_in_env(Obj, CE -> Obj1)

'action' Check_object_defined_with(NAME, OBJECT_EXPRS -> OPT_OBJECT_ID, PARAM_FIT)

  'rule' Check_object_defined_with(N, list(Obj, Objs) -> Oid, PF):
	 Qualify_name(Obj, N -> N1)
	 (|
	   Get_object_id(obj_name(N1) -> object_id(I), PF)
	   where(object_id(I) -> Oid)
	 ||
	   Check_object_defined_with(N, Objs -> Oid, PF)
	 |)
	 
  'rule' Check_object_defined_with(N, nil -> nil, nil):

'action' Check_object_defined_in_env(OBJECT_EXPR, CLASS_ENV -> OBJECT_EXPR)

  'rule' Check_object_defined_in_env(obj_name(name(P, id_op(Id))), CE -> Obj):
	 (|
	   Lookup_object_in_env(obj_name(name(P, id_op(Id))), CE, nil -> object_id(I))
	   where(obj_occ(P, I) -> Obj)
	 ||
	   Puterror(P)
	   Putmsg("Object ")
	   Print_object(obj_name(name(P, id_op(Id))))
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   where(obj_name(name(P, id_op(Id))) -> Obj)
	 |)

  'rule' Check_object_defined_in_env(obj_name(qual_name(P, Obj, id_op(Id))), CE -> Obj2):
	 Check_object_defined_in_env(Obj, CE -> Obj1)
	 Env_of_defined_object(Obj1 -> CE1)
	 (|
	   Lookup_object_in_env(obj_name(name(P, id_op(Id))), CE1, nil -> object_id(I))
	   where(qual_occ(P, Obj1, I) -> Obj2)
	 ||
	   Puterror(P)
	   Putmsg("Object ")
	   Print_object(obj_name(name(P, id_op(Id))))
	   Putmsg(" is hidden, renamed, or not defined")
	   Putnl()
	   where(obj_name(name(P, id_op(Id))) -> Obj2)
	 |)
	 
  'rule' Check_object_defined_in_env(obj_appl(Obj, Parms), CE -> obj_appl(Obj1, Parms)):
	 Check_object_defined_in_env(Obj, CE -> Obj1)

  'rule' Check_object_defined_in_env(obj_array(TPS, Obj), CE -> obj_array(TPS, Obj1)):
	 Check_object_defined_in_env(Obj, CE -> Obj1)

  'rule' Check_object_defined_in_env(obj_fit(Obj, RNS), CE -> obj_fit(Obj1, RNS)):
	 Check_object_defined_in_env(Obj, CE -> Obj1)

  'rule' Check_object_defined_in_env(obj_occ(P, I), _ -> obj_occ(P, I)):

  'rule' Check_object_defined_in_env(qual_occ(P, Obj, I), _ -> qual_occ(P, Obj1, I)):
	 I'Env -> CE
	 Check_object_defined_in_env(Obj, CE -> Obj1)

'action' Env_of_defined_object(OBJECT_EXPR -> CLASS_ENV)

  'rule' Env_of_defined_object(obj_appl(Obj, _) -> CE):
	 Env_of_defined_object(Obj -> CE)

  'rule' Env_of_defined_object(obj_array(_, Obj) -> CE):
	 Env_of_defined_object(Obj -> CE) 

  'rule' Env_of_defined_object(obj_fit(Obj, _) -> CE):
	 Env_of_defined_object(Obj -> CE)

  'rule' Env_of_defined_object(obj_occ(_, I) -> CE):
	 I'Env -> CE

  'rule' Env_of_defined_object(qual_occ(_, _, I) -> CE):
	 I'Env -> CE

  'rule' Env_of_defined_object(_ -> nil):


---------------------------------------------------------------------------
-- Unification
---------------------------------------------------------------------------
'type' TYPE_EXPRS
        list		(TYPE_EXPR,
			 TYPE_EXPRS)
	nil

'type' SUBSTITUTION
        sub		(num	:	INT,
			 type	:	TYPE_EXPR,
			 dir	:	DIRECTION,
			 tail	:	SUBSTITUTION)
	nil

'action' Lookup_sub(INT, SUBSTITUTION -> TYPE_EXPR, DIRECTION)

  'rule' Lookup_sub(N, sub(N1,T,Dir,S) -> T1, Dir1):
	 (|
	   eq(N,N1)
	   where(T -> T1)
	   where(Dir -> Dir1)
	 ||
	   Lookup_sub(N, S -> T1, Dir1)
	 |)

  'rule' Lookup_sub(N, nil -> any, nil):

'action' Override_sub(INT, TYPE_EXPR, DIRECTION, SUBSTITUTION -> SUBSTITUTION)

  'rule' Override_sub(N, T, Dir, sub(N1,T1,Dir1,S) -> S1):
	 (|
	   eq(N, N1)
	   where(sub(N, T, Dir, S) -> S1)
	 ||
	   Override_sub(N, T, Dir, S -> S2)
	   where(sub(N1,T1,Dir1,S2) -> S1)
	 |)

'action' Print_substitution(SUBSTITUTION)

  'rule' Print_substitution(sub(N, T, Dir, S)):
	 Putint(N)
	 Putmsg(" +> ")
	 Print_type(T)
	 (|
	   ne(S, nil)
	   Putmsg(",")
	   Print_substitution(S)
	 ||
	   Putnl()
	 |)

  'rule' Print_substitution(nil):

'action' Poly_disambiguate_type(TYPE_EXPR, TYPE_EXPR -> TYPE_EXPR)
-- Increment polynums in first until no overlap with second

  'rule' Poly_disambiguate_type(T1, T2 -> T3)
	 Collect_polynums(T1, nil -> NS1)
	 (|
	   ne(NS1, nil)
	   Collect_polynums(T2, nil -> NS2)
	   ne(NS2, nil)
	   Intersect_polynums(NS1, NS2)
	   Increment_polynums(T1 -> T11)
	   Poly_disambiguate_type(T11, T2 -> T3)
	 ||
	   where(T1 -> T3)
	 |)

'condition' No_unification(TYPE_EXPR, TYPE_EXPR)

  'rule' No_unification(T1, T2):
	 Poly_disambiguate_type(T1, T2 -> T11)
	 Unify(T11, nil, T2, nil, nil -> T3, S)
	 Unify(any, nil, T3, nil, S -> none, _)

'condition' Match(TYPE_EXPR, DIRECTION, TYPE_EXPR)

  'rule' Match(T1, Dir, T2):
	 Poly_disambiguate_type(T1, T2 -> T11)
	 Unify(T11, Dir, T2, nil, nil -> T3, S)
-- Now check for none.
-- If none has appeared in the first unification the next one
-- will generate none for the whole type; otherwise it will 
-- leave it unchanged
	 Unify(any, nil, T3, nil, S -> T, S1)
	 ne(T, none)

'action' Match_up(TYPE_EXPR, TYPE_EXPR -> TYPE_EXPR)

  'rule' Match_up(T1, T2 -> T):
	 Poly_disambiguate_type(T1, T2 -> T11)
	 Unify(T11, up, T2, up, nil -> T3, S)
	 Unify(any, nil, T3, nil, S -> T, S1)

'action' Unify_by_result(TYPE_EXPR, TYPE_EXPR, TYPE_EXPR -> TYPE_EXPR)
-- Second parameter is result type of third, which is a function, map
-- or list type.
-- First parameter is an expected result, which can be used to remove
-- polymorphism from the function type, which is returned.

  'rule' Unify_by_result(T1, T2, FT -> FT1):
	 Poly_disambiguate_type(T1, FT -> T11)
	 Unify(T11, up, T2, nil, nil -> T3, S)
	 Unify(any, nil, T3, nil, S -> T4, S1)
	 (|
	   eq(T4, none)
	   where(none -> FT1)
	 ||
	   Unify(FT, nil, FT, nil, S1 -> FT1, _)
	 |)

'action' Unify_to_resolve(TYPE_EXPR, TYPE_EXPR -> TYPE_EXPR)

  'rule' Unify_to_resolve(T, T1 -> T2)
-- If T1 matches up to T, then return T with any polymorphism removed
-- if possible
-- debug
-- Putmsg("T is ")
-- Print_type(T)
-- Putnl
-- Print_type(T1)
-- Putnl
         Poly_disambiguate_type(T, T1 -> T0)
-- Print_type(T0)
-- Putnl
	 Unify(T1, up, T0, nil, nil -> T3, S)
-- Print_type(T3)
-- Putnl
-- Print_substitution(S)
	 Unify(any, nil, T3, nil, S -> T4, S1)
-- Print_type(T4)
-- Putnl
-- Print_substitution(S1)
	 (|
	   eq(T4, none)
	   where(none -> T2)
	 ||
	   Unify(T0, nil, T0, nil, S1 -> T2, _)
	 |)
-- Print_type(T2)	 
-- Putnl
-- Putnl

-- poly(0) should not be used in types; 0 in a substitution is used 
-- to indicate failure in unification.

'action' Unify(TYPE_EXPR, DIRECTION, TYPE_EXPR, DIRECTION, SUBSTITUTION -> TYPE_EXPR, SUBSTITUTION)

  'rule' Unify(T, Dir1, none, Dir2, S -> none, S)

  'rule' Unify(none, Dir1, T, Dir2, S -> none, S)

  'rule' Unify(bracket(T1), Dir1, T2, Dir2, S -> T, S1):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)

  'rule' Unify(T1, Dir1, bracket(T2), Dir2, S -> T, S1):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)

  'rule' Unify(subtype(single(P1,B,T1),R), Dir1, T2, Dir2, S -> T, S1):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)

  'rule' Unify(T1, Dir1, subtype(single(P1,B,T2),R), Dir2, S -> T, S1):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)
	 
  'rule' Unify(defined(I1, Q), Dir1, defined(I2, _), Dir2, S -> defined(I1, Q), S):
	 eq(I1,I2)

  'rule' Unify(defined(I1, _), up, defined(I2, Q), Dir2, S -> defined(I2, Q), S):
	 I1'Coercions_up -> C1
	 Is_in_coercions(I2, C1)
-- debug
-- I1'Ident -> Id1
-- I2'Ident -> Id2
-- Print_id(Id1)
-- Putmsg(" and ")
-- Print_id(Id2)
-- Putmsg(" unify up to ")
-- Print_id(Id2)
-- Putnl()

  'rule' Unify(defined(I1, Q), Dir1, defined(I2, _), up, S -> defined(I1, Q), S):
	 I2'Coercions_up -> C2
	 Is_in_coercions(I1, C2)
-- debug
-- I1'Ident -> Id1
-- I2'Ident -> Id2
-- Print_id(Id1)
-- Putmsg(" and ")
-- Print_id(Id2)
-- Putmsg(" unify up to ")
-- Print_id(Id1)
-- Putnl()
	 
  'rule' Unify(defined(I1, _), up, defined(I2, _), up, S -> defined(I, nil), S):
	 I1'Coercions_up -> C1
	 I2'Coercions_up -> C2
	 Lub_coercions(C1, C2 -> type_id(I))
-- debug
-- I1'Ident -> Id1
-- I2'Ident -> Id2
-- I'Ident -> Id
-- Print_id(Id1)
-- Putmsg(" and ")
-- Print_id(Id2)
-- Putmsg(" unify up to ")
-- Print_id(Id)
-- Putnl()
	 
  'rule' Unify(defined(I1, X), up, T2, Dir2, S -> T, S1):
	 Contains_any_or_poly(T2, nil -> nil)
	 I1'Coercions_up -> C1
	 Unify_with_coercions(C1, up, T2, Dir2, S -> T, S1)
-- Print_type(defined(I1, X))
-- Putmsg(" unifies up with ")
-- Print_type(T2)
-- Putmsg(" to give (1) ")
-- Print_type(T)
-- Putnl()

  'rule' Unify(T1, Dir1, defined(I2, X), up, S -> T, S1):
	 Contains_any_or_poly(T1, nil -> nil)
	 I2'Coercions_up -> C2
	 Unify_with_coercions(C2, up, T1, Dir1, S -> T, S1)
-- Print_type(defined(I2, X))
-- Putmsg(" unifies up with ")
-- Print_type(T1)
-- Putmsg(" to give (2) ")
-- Print_type(T)
-- Putnl()

  'rule' Unify(T1, up, T2:defined(I2, _), nil, S -> T2, S1):
	 Contains_any_or_poly(T1, nil -> nil)
	 I2'Coercions_down -> C2
	 Unify_with_coercions(C2, down, T1, nil, S -> T, S1)

  'rule' Unify(T1:defined(I1, _), up, T2, up, S -> T1, S1):
	 Contains_any_or_poly(T2, nil -> nil)
	 I1'Coercions_down -> C1
	 Unify_with_coercions(C1, down, T2, nil, S -> T, S1)

--  'rule' Unify(T1, up, T2:defined(I2, _), up, S -> T2, S1):
--	 I2'Coercions_down -> C2
--	 Unify_with_coercions(C2, down, T1, nil, S -> T, S1)

  'rule' Unify(defined(I1, _), down, defined(I2, Q), Dir2, S -> defined(I2, Q), S):
	 I1'Coercions_down -> C1
	 Is_in_coercions(I2, C1)
-- debug
-- I1'Ident -> Id1
-- I2'Ident -> Id2
-- Print_id(Id1)
-- Putmsg(" and ")
-- Print_id(Id2)
-- Putmsg(" unify down to ")
-- Print_id(Id2)
-- Putnl()

  'rule' Unify(defined(I1, Q), Dir1, defined(I2, _), down, S -> defined(I1, Q), S):
	 I2'Coercions_down -> C2
	 Is_in_coercions(I1, C2)
-- debug
-- I1'Ident -> Id1
-- I2'Ident -> Id2
-- Print_id(Id1)
-- Putmsg(" and ")
-- Print_id(Id2)
-- Putmsg(" unify down to ")
-- Print_id(Id1)
-- Putnl()

  'rule' Unify(defined(I1, _), down, defined(I2, _), down, S -> defined(I, nil), S):
	 I1'Coercions_down -> C1
	 I2'Coercions_down -> C2
	 Lub_coercions(C1, C2 -> type_id(I))
-- debug
-- I1'Ident -> Id1
-- I2'Ident -> Id2
-- I'Ident -> Id
-- Print_id(Id1)
-- Putmsg(" and ")
-- Print_id(Id2)
-- Putmsg(" unify down to ")
-- Print_id(Id)
-- Putnl()

  'rule' Unify(defined(I1, X), down, T2, Dir2, S -> T, S1):
	 Contains_any_or_poly(T2, nil -> nil)
	 I1'Coercions_down -> C1
	 Unify_with_coercions(C1, down, T2, Dir2, S -> T, S1)
-- Print_type(defined(I1, X))
-- Putmsg(" unifies down with ")
-- Print_type(T2)
-- Putmsg(" to give (3) ")
-- Print_type(T)
-- Putnl()

  'rule' Unify(T1, Dir1, defined(I2, X), down, S -> T, S1):
	 Contains_any_or_poly(T1, nil -> nil)
	 I2'Coercions_down -> C2
	 Unify_with_coercions(C2, down, T1, Dir1, S -> T, S1)
-- Print_type(defined(I2, X))
-- -- Putmsg(" unifies down with ")
-- Print_type(T1)
-- Putmsg(" to give (4) ")
-- Print_type(T)
-- Putnl()

  'rule' Unify(T1, down, T2:defined(I2, _), nil, S -> T2, S1):
	 Contains_any_or_poly(T1, nil -> nil)
	 I2'Coercions_up -> C2
	 Unify_with_coercions(C2, up, T1, nil, S -> T, S1)

  'rule' Unify(T1:defined(I1, _), down, T2, down, S -> T1, S1):
	 Contains_any_or_poly(T2, nil -> nil)
	 I1'Coercions_up -> C1
	 Unify_with_coercions(C1, up, T2, nil, S -> T, S1)

--  'rule' Unify(T1, down, T2:defined(I2, _), down, S -> T2, S1):
--	 I2'Coercions_up -> C2
--	 Unify_with_coercions(C2, up, T1, nil, S -> T, S1)



  'rule' Unify(text, Dir1, T, Dir2, S -> T1, S1):
	 Unify(fin_list(char), Dir1, T, Dir2, S -> T1, S1)

  'rule' Unify(T, Dir1, text, Dir2, S -> T1, S1):
	 Unify(T, Dir1, fin_list(char), Dir2, S -> T1, S1)

  'rule' Unify(unit, Dir1, unit, Dir2, S -> unit, S):

  'rule' Unify(bool, Dir1, bool, Dir2, S -> bool, S):

  'rule' Unify(int, Dir1, int, Dir2, S -> int, S):

  'rule' Unify(nat, Dir1, nat, Dir2, S -> nat, S):

  'rule' Unify(nat, Dir1, int, Dir2, S -> int, S):

  'rule' Unify(int, Dir1, nat, Dir2, S -> int, S):

  'rule' Unify(real, Dir1, real, Dir2, S -> real, S):

  'rule' Unify(char, Dir1, char, Dir2, S -> char, S):

  'rule' Unify(time, Dir1, time, Dir2, S -> time, S):
	 IsTimed()

  'rule' Unify(time, Dir1, real, Dir2, S -> real, S):
	 IsTimed()

  'rule' Unify(real, Dir1, time, Dir2, S -> real, S):
	 IsTimed()

  'rule' Unify(fin_set(T1), Dir1, fin_set(T2), Dir2, S -> fin_set(T), S1):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)

  'rule' Unify(infin_set(T1), Dir1, infin_set(T2), Dir2, S -> infin_set(T), S1):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)

  'rule' Unify(fin_set(T1), Dir1, infin_set(T2), Dir2, S ->  infin_set(T), S1):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)

  'rule' Unify(infin_set(T1), Dir1, fin_set(T2), Dir2, S ->  infin_set(T), S1):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)

  'rule' Unify(fin_list(T1), Dir1, fin_list(T2), Dir2, S ->  fin_list(T), S1):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)

  'rule' Unify(infin_list(T1), Dir1, infin_list(T2), Dir2, S -> infin_list(T), S1):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)

  'rule' Unify(fin_list(T1), Dir1, infin_list(T2), Dir2, S -> infin_list(T), S1):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)

  'rule' Unify(infin_list(T1), Dir1, fin_list(T2), Dir2, S -> infin_list(T), S1):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)

  'rule' Unify(fin_map(D1,R1), Dir1, fin_map(D2, R2), Dir2, S -> fin_map(D,R), S2):
	 Unify(D1, Dir1, D2, Dir2, S -> D, S1)
	 Unify(R1, Dir1, R2, Dir2, S1 -> R, S2)

  'rule' Unify(infin_map(D1,R1), Dir1, infin_map(D2, R2), Dir2, S -> infin_map(D,R), S2):
	 Unify(D1, Dir1, D2, Dir2, S -> D, S1)
	 Unify(R1, Dir1, R2, Dir2, S1 -> R, S2)

  'rule' Unify(fin_map(D1,R1), Dir1, infin_map(D2, R2), Dir2, S -> infin_map(D,R), S2):
	 Unify(D1, Dir1, D2, Dir2, S -> D, S1)
	 Unify(R1, Dir1, R2, Dir2, S1 -> R, S2)

  'rule' Unify(infin_map(D1,R1), Dir1, fin_map(D2, R2), Dir2, S -> infin_map(D,R), S2):
	 Unify(D1, Dir1, D2, Dir2, S -> D, S1)
	 Unify(R1, Dir1, R2, Dir2, S1 -> R, S2)

  'rule' Unify(fun(D1,A1,R1), Dir1, fun(D2,A2,R2), Dir2, S -> fun(D,A,R), S2):
	 Reverse(Dir1 -> OppDir1)  
	 Reverse(Dir2 -> OppDir2)  
	 Unify(D1, OppDir1, D2, OppDir2, S -> D, S1)
	 Unify_arrows(A1, A2 -> A)
	 Unify_result(R1, Dir1, R2, Dir2, S1 -> R, S2)

  'rule' Unify(product(PR1), Dir1, product(PR2), Dir2, S -> product(PR), S1):
	 Length_pr(PR1 -> N1)
	 Length_pr(PR2 -> N2)
	 eq(N1, N2)
	 Unify_prod(PR1, Dir1, PR2, Dir2, S -> PR, S1)

  'rule' Unify(any, Dir1, T, Dir2, S -> T2, S):
	 Lookup_sub(0, S -> T1, Dir)
	 (| eq(T1, none) where(TYPE_EXPR'none -> T2) || where(T -> T2) |)

  'rule' Unify(T, Dir1, any, Dir2, S -> T2, S):
	 Lookup_sub(0, S -> T1, Dir)
	 (| eq(T1, none) where(TYPE_EXPR'none -> T2) || where(T -> T2) |)

  'rule' Unify(poly(N), Dir1, T, Dir2, S -> T2, S2):
	 Lookup_sub(N, S -> T1, Dir)
	 (|
	   eq(T1, any)
	   (|
	     where(T -> poly(N1))
	     (|
	       eq(N, N1)
	       where(poly(N) -> T2)
	       where(S -> S2)
	     ||
	       -- if N1 has a substitution we can unify that with N
	       Lookup_sub(N1, S -> T11, Dir11)
	       (|
	         eq(T11, any)
		 -- N1 does not have a substitution
		 where(sub(N,poly(N1),Dir1,S) -> S2)
		 where(poly(N) -> T2)
-- debug
-- Print_substitution(S2)
	       ||
	         Unify(poly(N), Dir1, T11, Dir11, S -> T2, S2)
	       |)
	     |)
	   ||
	     Contains_poly(T, nil -> Found)
	     (|
	       eq(Found, found)
	       -- make sure T is as resolved as possible
	       -- to avoid circularities
	       Unify(T, nil, T, nil, S -> T21, _)
	       -- circularity iff T mentions poly(N)
	       (|
		 Contains_polynum(T21, N)
		 where(TYPE_EXPR'none -> T2)
		 where(sub(0,none,nil,S) -> S2)
-- debug
-- Putmsg("Circularity: ")
-- where(sub(N,T,Dir2,S) -> S3)
-- Print_substitution(S3)
	       ||
		 where(sub(N,T21,Dir2,S) -> S2)
	         where(T21 -> T2)
-- debug
-- Print_substitution(S2)
	       |)
	     ||
	       where(sub(N,T,Dir2,S) -> S2)
	       where(T -> T2)
-- debug
-- Print_substitution(S2)
	     |)
	   |)
	 ||
	   Unify(T1, Dir, T, Dir2, S -> T2, S1)
	   -- T2 may be a more defined type than T1,
	   -- and so should replace T1 as the substitution for N
	   Override_sub(N, T2, Dir, S1 -> S2)
-- debug
-- Putmsg("Replacing ")
-- Print_substitution(S1)
-- Putmsg(" with ")
-- Print_substitution(S2)
	 |)

  'rule' Unify(T, Dir1, poly(N), Dir2, S -> T2, S2):
	 Unify(poly(N), Dir2, T, Dir1, S -> T2, S2)

  'rule' Unify(named_type(N), Dir1, T2, Dir2, S -> T3, S3):
	 Lookup_type_name(N -> type_id(I))
	 Unify(defined(I, nil), Dir1, T2, Dir2, S -> T3, S3)

  'rule' Unify(T1, Dir1, named_type(N), Dir2, S -> T3, S3):
	 Lookup_type_name(N -> type_id(I))
	 Unify(T1, Dir1, defined(I, nil), Dir2, S -> T3, S3)

  'rule' Unify(defined(I, _), Dir1, T2, Dir2, S -> T3, S3):
	 I'Type -> T
	 (|
	   where(T -> abbrev(T1))
	   Unify(T1, Dir1, T2, Dir2, S -> T3, S3)
	 ||
	   eq(T,undef_type)
	   -- presume error reported earlier
	   where(S -> S3)
	   where(TYPE_EXPR'any -> T3)
	 |)

  'rule' Unify(T1, Dir1, defined(I, _), Dir2, S -> T3, S3):
	 I'Type -> T
	 (|
	   where(T -> abbrev(T2))
	   Unify(T1, Dir1, T2, Dir2, S -> T3, S3)
	 ||
	   eq(T,undef_type)
	   -- presume error reported earlier
	   where(S -> S3)
	   where(TYPE_EXPR'any -> T3)
	 ||
	   where(TYPE_EXPR'none -> T3)
	   where(sub(0,none,nil,S) -> S3)
	 |)

  'rule' Unify(array(TI1,TV1), Dir1, array(TI2,TV2), Dir2, S -> array(TR1,TR2), S)
         --Check_type(TI1,TI2)
         Unify(TI1, Dir1, TI2, Dir2, S -> TR1, nil)
         Unify(TV1, Dir1, TV2, Dir2, S -> TR2, nil)

  'rule' Unify(T1, Dir1, T2, Dir2, S -> none, sub(0,none,nil,S)):

'condition' Check_type(TYPE_EXPR, TYPE_EXPR)
  'rule' Check_type(T1, T2)
         eq(T1,T2)

  'rule' Check_type(named_type(name(_,I1)), named_type(name(_,I2)))
         eq(I1,I2)

'action' Unify_prod(PRODUCT_TYPE, DIRECTION, PRODUCT_TYPE, DIRECTION, SUBSTITUTION -> PRODUCT_TYPE, SUBSTITUTION)

  'rule' Unify_prod(list(T1,PR1), Dir1, list(T2, PR2), Dir2, S -> list(T, PR), S2):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)
	 Unify_prod(PR1, Dir1, PR2, Dir2, S1 -> PR, S2)

  'rule' Unify_prod(nil, Dir1, nil, Dir2, S -> nil, S)

'action' Unify_arrows(FUNCTION_ARROW, FUNCTION_ARROW -> FUNCTION_ARROW)

  'rule' Unify_arrows(total, total -> total):

  'rule' Unify_arrows(A1, A2 -> partial)

'action' Unify_result(RESULT, DIRECTION, RESULT, DIRECTION, SUBSTITUTION -> RESULT, SUBSTITUTION)

  'rule' Unify_result(result(T1,RD1,WR1,IN1,OUT1), Dir1, result(T2,RD2,WR2,IN2,OUT2), Dir2, S -> result(T,RD,WR,IN,OUT), S1):
	 Unify(T1, Dir1, T2, Dir2, S -> T, S1)
	 Concat_accs(RD1, RD2 -> RD)
	 Concat_accs(WR1, WR2 -> WR)
	 Concat_accs(IN1, IN2 -> IN)
	 Concat_accs(OUT1, OUT2 -> OUT)

'condition' Unify_with_coercions(COERCIONS, DIRECTION, TYPE_EXPR, DIRECTION, SUBSTITUTION -> TYPE_EXPR, SUBSTITUTION)

  'rule' Unify_with_coercions(coercions(C, Cs), Dir1, T2, Dir2, S -> T, S1):
	 (|
	   Unify_with_coercion(C, Dir1, T2, Dir2, S -> T, S1)
	   ne(T, none)
	 ||
	   Unify_with_coercions(Cs, Dir1, T2, Dir2, S -> T, S1)
	 |)
  
'condition' Unify_with_coercion(COERCION, DIRECTION, TYPE_EXPR, DIRECTION, SUBSTITUTION -> TYPE_EXPR, SUBSTITUTION)

  'rule' Unify_with_coercion(coercion(I1, C1), Dir1, T2, Dir2, S -> T, S1):
	 Unify(defined(I1, nil), Dir1, T2, Dir2, S -> T3, S3)
	 Unify(any, nil, T3, nil, S3 -> T4, S4)
	 (|
	   eq(T4, none)
	   Unify_with_coercion(C1, Dir1, T2, Dir2, S -> T, S1)
	 ||
	   where(T4 -> T)
	   where(S4 -> S1)
	 |)
	     

'action' Make_result_types(TYPE_EXPR, RESULTS, RESULT -> RESULTS)
-- First parameter is function, map or list domain type;
-- second argument are possible argument results
-- third argument is function, map or list result.
-- For each type in second argument,
-- if first argument unifies with it, 
-- apply substitution to type of third
-- to make result

  'rule' Make_result_types(D, list(result(T,RD1,WR1,IN1,OUT1),RS), result(R,RD2,WR2,IN2,OUT2) -> RS2):
	 Poly_disambiguate_type(T, fun(D,partial,result(R,nil,nil,nil,nil)) -> T11)
	 Make_result_types(D, RS, result(R,RD2,WR2,IN2,OUT2) -> RS1)
         (|
	   Subtype(T11, D, nil -> _)

	   Unify(T11, up, D, nil, nil -> T1, S)
-- debug
-- Putmsg("Unified type from ")
-- Print_type(T)
-- Putmsg(" and ")
-- Print_type(D)
-- Putmsg(" is ")
-- Print_type(T1)
-- Putnl()
-- Print_substitution(S)
	   Unify(any, nil, T1, nil, S -> T2, S1)
-- Putmsg("After checking for none, type is ")
-- Print_type(T2)
-- Putnl()
-- Print_substitution(S1)
	   (|
	     eq(T2, none)
	     where(RS1 -> RS2)
	   ||
	     -- unifying a type with itself with a substitution causes
	     -- the substitution to be applied
-- Putmsg("Unifying with itself: ")
-- Print_type(R)
	     Unify(R, nil, R, nil, S1 -> R1, S2)
-- Putmsg(" gives ")
-- Print_type(R1)
-- Putnl()
-- Print_substitution(S2)
	     Concat_accs(RD1, RD2 -> RD)
	     Concat_accs(WR1, WR2 -> WR)
	     Concat_accs(IN1, IN2 -> IN)
	     Concat_accs(OUT1, OUT2 -> OUT)
	     where(RESULT'result(R1,RD,WR,IN,OUT) -> Res)
	     -- check for unresolvable overloading

	     where(RESULTS'list(Res, RS1) -> RS2)
	   |)
	 ||

	   where(RS1 -> RS2)
	 |)

  'rule' Make_result_types(_, nil, _ -> nil)

'action' Reverse(DIRECTION -> DIRECTION)

  'rule' Reverse(up -> down):

  'rule' Reverse(down -> up):

  'rule' Reverse(nil -> nil):

'action' Make_function_type(TYPE_EXPR -> TYPE_EXPR)

  'rule' Make_function_type(fun(T, A, R) -> fun(T, A, R)):

-- Unify the type expression with a general function type
-- This will unfold as necessary until a function type is found
-- or return failure as the type "none"
  'rule' Make_function_type(T -> T1):
	 Unify(T, nil, fun(any, total, result(any,nil,nil,nil,nil)), nil, SUBSTITUTION'nil -> T1, S1)

'action' Make_map_type(TYPE_EXPR -> TYPE_EXPR)
-- Similar to Make_function_type

  'rule' Make_map_type(fin_map(D, R) -> fin_map(D, R)):

  'rule' Make_map_type(infin_map(D, R) -> infin_map(D, R)):

  'rule' Make_map_type(T -> T1):
	 Unify(T, nil, fin_map(any, any), nil, SUBSTITUTION'nil -> T1, S1)

'action' Make_array_type(TYPE_EXPR -> TYPE_EXPR)
-- Similar to Make_function_type

  'rule' Make_array_type(array(I, V) -> array(I, V)):

  'rule' Make_array_type(T -> T2):
Remove_Brackets(T -> T1)
	 Unify(T1, nil, array(any, any), nil, SUBSTITUTION'nil -> T2, S1)

'action' Make_product_type(TYPE_EXPR, INT -> TYPE_EXPR)
-- Similar to Make_function_type

  'rule' Make_product_type(T:product(TS), N -> T):
	 Length_pr(TS -> N1)
	 eq(N, N1) 

-- Tries to make product of length given by second parameter
  'rule' Make_product_type(T, N -> T1):
	 Make_any_product(N -> PR)
	 Unify(T, nil, product(PR), nil, SUBSTITUTION'nil -> T1, S1)

'action' Make_any_product(INT -> PRODUCT_TYPE)

  'rule' Make_any_product(N -> list(any, PR)):
	 gt(N,0)
	 Make_any_product(N-1 -> PR)

  'rule' Make_any_product(N -> nil):

'action' Make_list_type(TYPE_EXPR -> TYPE_EXPR)
-- Similar to Make_function_type

  'rule' Make_list_type(fin_list(T) -> fin_list(T)):

  'rule' Make_list_type(infin_list(T) -> infin_list(T)):

  'rule' Make_list_type(T -> T1):
	 Unify(T, nil, fin_list(any), nil, nil -> T1, S1)

'action' Make_set_type(TYPE_EXPR -> TYPE_EXPR)
-- Similar to Make_function_type

  'rule' Make_set_type(fin_set(T) -> fin_set(T)):

  'rule' Make_set_type(infin_set(T) -> infin_set(T)):

  'rule' Make_set_type(T -> T1):
	 Unify(T, nil, fin_set(any), nil, nil -> T1, S1)

'condition' Supertype_of_vals(TYPE_EXPR, Value_ids)
-- succeeeds if the type of one in the second parameter
-- is a subtype of the first 

  'rule' Supertype_of_vals(T, list(I, Ids)):
	 (|
	   I'Type -> T1
	   Subtype(T1, T, nil -> S)
         ||
	   Supertype_of_vals(T, Ids)
	 |)

'condition' Subtype(TYPE_EXPR, TYPE_EXPR, SUBSTITUTION -> SUBSTITUTION)

  'rule' Subtype(T, T1, S -> S):
	 eq(T,T1)

  'rule' Subtype(bracket(T), T1, S -> S1):
	 Subtype(T, T1, S -> S1)

  'rule' Subtype(T, bracket(T1), S -> S1):
	 Subtype(T, T1, S -> S1)

  'rule' Subtype(subtype(single(P,B,T),R), T1, S -> S1):
	 Subtype(T, T1, S -> S1)

  'rule' Subtype(T, subtype(single(P,B,T1),R), S -> S1):
	 Subtype(T, T1, S -> S1)

  'rule' Subtype(text, T, S -> S1):
	 Subtype(fin_list(char), T, S -> S1)

  'rule' Subtype(T, text, S -> S1):
	 Subtype(T, fin_list(char), S -> S1)

  'rule' Subtype(nat, int, S -> S):
   
  'rule' Subtype(int, nat, S -> S):

  'rule' Subtype(time, real, S -> S):
	 IsTimed()

  'rule' Subtype(real, time, S -> S):
	 IsTimed()

  'rule' Subtype(fin_set(T), fin_set(T1), S -> S1):
	 Subtype(T, T1, S -> S1)

  'rule' Subtype(infin_set(T), fin_set(T1), S -> S1):
	 Subtype(T, T1, S -> S1)

  'rule' Subtype(fin_set(T), infin_set(T1), S -> S1):
	 Subtype(T, T1, S -> S1)

  'rule' Subtype(infin_set(T), infin_set(T1), S -> S1):
	 Subtype(T, T1, S -> S1)

  'rule' Subtype(fin_list(T), fin_list(T1), S -> S1):
	 Subtype(T, T1, S -> S1)

  'rule' Subtype(infin_list(T), fin_list(T1), S -> S1):
	 Subtype(T, T1, S -> S1)

  'rule' Subtype(fin_list(T), infin_list(T1), S -> S1):
	 Subtype(T, T1, S -> S1)

  'rule' Subtype(infin_list(T), infin_list(T1), S -> S1):
	 Subtype(T, T1, S -> S1)

  'rule' Subtype(fin_map(D1,R1), fin_map(D2, R2), S -> S2):
	 Subtype(D1, D2, S -> S1)
	 Subtype(R1, R2, S1 -> S2)

  'rule' Subtype(infin_map(D1,R1), fin_map(D2, R2), S -> S2):
	 Subtype(D1, D2, S -> S1)
	 Subtype(R1, R2, S1 -> S2)

  'rule' Subtype(fin_map(D1,R1), infin_map(D2, R2), S -> S2):
	 Subtype(D1, D2, S -> S1)
	 Subtype(R1, R2, S1 -> S2)

  'rule' Subtype(infin_map(D1,R1), infin_map(D2, R2), S -> S2):
	 Subtype(D1, D2, S -> S1)
	 Subtype(R1, R2, S1 -> S2)

  'rule' Subtype(product(PR1), product(PR2), S -> S1):
	 Subtype_prod(PR1, PR2, S -> S1)

  'rule' Subtype(fun(T, Arr, result(R, RD, WR, IN, OUT)),
		  fun(T1, Arr1, result(R1, RD1, WR1, IN1, OUT1)), S -> S2):
	 No_more_accesses(list(result(R, RD, WR, IN, OUT), nil), RD1, WR1, IN1, OUT1)
	 Subtype(T1, T, S -> S1)
	 Subtype(R, R1, S1 -> S2)

  'rule' Subtype(any, T, S -> S):

  'rule' Subtype(T, any, S -> S):

  'rule' Subtype(defined(I, _), defined(I1, _), S -> S):
	 eq(I, I1)

  'rule' Subtype(defined(I, _), T1, S -> S1):
	 I'Type -> abbrev(T)
	 Subtype(T, T1, S -> S1)
	 
  'rule' Subtype(T, defined(I, _), S -> S1):
	 I'Type -> abbrev(T1)
	 Subtype(T, T1, S -> S1)

  'rule' Subtype(poly(N), T, S -> S1):
	 Lookup_sub(N, S -> T1, Dir)
	 (|
	   eq(T1, any)
	   (|
	     where(T -> poly(N1))
	     eq(N, N1)
	     where(S -> S1)
	   ||
	     where(sub(N,T,nil,S) -> S1)
	   |)
	 ||
	   Subtype(T1, T, S -> S1)
	 |)

  'rule' Subtype(T, poly(N), S -> S1):
	 Lookup_sub(N, S -> T1, Dir)
	 (|
	   eq(T1, any)
	   where(sub(N,T,nil,S) -> S1)
	 ||
	   Subtype(T, T1, S -> S1)
	 |)

  'rule' Subtype(named_type(name(_,I1)), named_type(name(_,I2)), S -> S)
         eq(I1,I2)

  'rule' Subtype(array(I1,V1), array(I2,V2), S -> S2)
         Subtype(I1, I2, S -> S1)
         Subtype(V1, V2, S1 -> S2)

'condition' Subtype_prod(PRODUCT_TYPE, PRODUCT_TYPE, SUBSTITUTION -> SUBSTITUTION)

  'rule' Subtype_prod(list(T, TS), list(T1, TS1), S -> S2):
	 Subtype(T, T1, S -> S1)
	 Subtype_prod(TS, TS1, S1 -> S2)

  'rule' Subtype_prod(nil, nil, S -> S):

------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------

'action' Length_bs(BINDINGS -> INT)

  'rule' Length_bs(list(_,T) -> N+1):
	 Length_bs(T -> N)

  'rule' Length_bs(nil -> 0):

'action' Length_pr(PRODUCT_TYPE -> INT)

  'rule' Length_pr(list(_,T) -> N+1):
	 Length_pr(T -> N)

  'rule' Length_pr(nil -> 0):

'action' Length_ps(PATTERNS -> INT)

  'rule' Length_ps(list(_,T) -> N+1):
	 Length_ps(T -> N)

  'rule' Length_ps(nil -> 0):

'action' Length_vs(VALUE_EXPRS -> INT)

  'rule' Length_vs(list(_,T) -> N+1):
	 Length_vs(T -> N)

  'rule' Length_vs(nil -> 0):

'action' Qualify_by_with(POS, Object_id -> OPT_QUALIFICATION)

  'rule' Qualify_by_with(P, I -> Q):
	 Get_current_with(-> WITH)
	 Qualify_by_with1(P, I, WITH -> Q) 

'action' Qualify_by_with1(POS, Object_id, OBJECT_EXPRS -> OPT_QUALIFICATION)

  'rule' Qualify_by_with1(_, _, nil -> nil):

  'rule' Qualify_by_with1(P, I, list(Obj, Objs) -> Q):
	 (|
	   Get_object_id(Obj -> object_id(I1), _)
	   eq(I, I1)
	   Check_object_defined(Obj -> Obj1, _)
	   where(qualification(Obj1) -> Q)
	 ||
	   Qualify_by_with1(P, I, Objs -> Q)
	 |)


'action' Remove_Brackets(TYPE_EXPR -> TYPE_EXPR)

  'rule' Remove_Brackets(bracket(T) -> Res)
         Remove_Brackets(T -> Res)

  'rule' Remove_Brackets(defined(Id,_) -> Res)
         Id'Type -> abbrev(Type)
         Remove_Brackets(Type -> Res)

  'rule' Remove_Brackets(T -> T)

