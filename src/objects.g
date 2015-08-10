-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the first pass of the type checker: Make_basic_env
-- This creates table entries for objects, types, variables and channels
-- and puts them in the environment
-- It also creates the adapts (renames and hides) and withs and puts
-- these in the environment

'module' objects

'use' ast print ext env types values

'export'

	 Make_basic_env Add_renames


---------------------------------------------------------------------
-- First pass
---------------------------------------------------------------------

'action' Make_basic_env(CLASS)

  'rule' Make_basic_env(basic(DS)):
	 Make_basic_env_decls(DS)

  'rule' Make_basic_env(instantiation(N, Objs)):
         (|
	   where(N -> name(P,id_op(Id)))
	 ||
	   where(N -> qual_name(P, _, id_op(Id)))
	   Putwarning(P)
	   Putmsg("Scheme names may not be qualified: qualification in ")
	   Print_name(N)
	   Putmsg(" ignored")
	   Putnl()
	 |)
	 Get_id_of_scheme(Id -> Oid)	 
	 (|
	   where(Oid -> scheme_id(I))
	   -- WITH is not imported
	   Set_current_with(nil)
	   I'Params -> PARMS
	   I'Class -> CL
	   -- cannot make params in first pass
	   -- as objects created during first pass
	   Make_basic_env(CL)
	   Get_current_with(-> W)
	   I'With <- W
	 ||
	   Puterror(P)
	   Putmsg("Scheme ")
	   Print_id(Id)
	   Putmsg(" is not defined")
	   Putnl()
	 |)

  'rule' Make_basic_env(extend(CL1, CL2)):
	 Get_current_with( -> W)
	 Start_extend(W)
	 Make_basic_env(CL1)
	 Left_right
	 Make_basic_env(CL2)
	 Out_right
	 Get_current_env(-> CE)
	 Check_duplicate_modules(CE)
	 Check_duplicate_types(CE)
	 
  'rule' Make_basic_env(hide(H, C)):
	 Make_basic_env(C)
	 Get_current_adapts(->ADS)
	 Add_hides(H, ADS -> ADS1)
	 Set_current_adapts(ADS1)

  'rule' Make_basic_env(rename(R, C)):
	 Make_basic_env(C)
	 Get_current_adapts(->ADS)
	 Add_renames(R, ADS -> ADS1)
	 Set_current_adapts(ADS1)

  'rule' Make_basic_env(with(P, Objs, C))
	 Check_duplicate_withs(P, Objs -> Objs1)
	 Get_current_adapts(-> Ads)
	 Adapt_withs(Objs1, Ads -> Objs2)
	 Get_current_with( -> Objs3)
	 (|
	   ne(Objs3, nil)
	   -- for "with A in with B in"
	   -- Objs3 will contain A, Objs2 will contain B
	   -- and we need to make the list B, A, A.B 
	   Prefix_withs(Objs3, Objs2 -> Objs4)
	   -- Objs4 is A.B
	   Concat_withs(Objs2, Objs3 -> Objs5)
	   -- Objs5 is B, A
	   Concat_withs(Objs5, Objs4 -> Objs6)
	   -- Objs6 is B, A, A.B
	   Set_current_with(Objs6)
-- debug
-- Putmsg("Withs set to ")
-- Print_objects(Objs6)
-- Putnl()
	 ||
	   Set_current_with(Objs2)
	 |)
	 Make_basic_env(C)

-- debug
--   'rule' Make_basic_env(CL)
-- print(CL)
-- Current -> C
-- print(C)

'action' Check_duplicate_withs(POS, OBJECT_EXPRS -> OBJECT_EXPRS)

  'rule' Check_duplicate_withs(P, list(Obj, nil) -> list(Obj, nil)):

  'rule' Check_duplicate_withs(P, list(Obj, Objs) -> Objs1):
	 (|
	   Obj_is_in_objs(Obj, Objs)
	   Puterror(P)
	   Putmsg("Duplicated with object ")
	   Print_object(Obj)
	   Putmsg(": ignored")
	   Putnl()
	   Check_duplicate_withs(P, Objs -> Objs1)
	 ||
	   Check_duplicate_withs(P, Objs -> Objs2)
	   where(OBJECT_EXPRS'list(Obj, Objs2) -> Objs1)
	 |)
	 

'action' Make_basic_env_decls(DECLS)

  'rule' Make_basic_env_decls(list(D,DS)):
	 Make_basic_env_decl(D)
	 Make_basic_env_decls(DS)

  'rule' Make_basic_env_decls(nil)

'action' Make_basic_env_decl(DECL)

  'rule' Make_basic_env_decl(object_decl(P, Defs)):
	 Make_basic_env_defs(Defs)

  'rule' Make_basic_env_decl(type_decl(P, Defs)):
	 Make_type_env_defs(Defs)

  'rule' Make_basic_env_decl(variable_decl(P, Defs)):
	 Make_variable_env_defs(Defs)

  'rule' Make_basic_env_decl(channel_decl(P, Defs)):
	 Make_channel_env_defs(Defs)

  'rule' Make_basic_env_decl(D):

'action' Make_basic_env_defs(OBJECT_DEFS)

  'rule' Make_basic_env_defs(list(D,DS)):
	 Make_basic_env_def(D)
	 Make_basic_env_defs(DS)

  'rule' Make_basic_env_defs(nil):

'action' Make_basic_env_def(OBJECT_DEF)

  'rule' Make_basic_env_def(odef(P, Id, TS, CL)):
	 Get_current_modules(-> ME)
	 (|
	   Lookup_object_in_module(Id, ME -> object_id(I1))
	   I1'Pos -> P1
	   Puterror(P)
	   Putmsg("Object identifier ")
	   Print_id(Id)
	   Putmsg(" already defined at ")
	   PrintPos(P1)
	   Putnl()
	 ||
	   New_object_id(P, Id -> I)
	   [|
	     ne(TS, nil)
	     -- make param type any for now to prevent "not an array" errors
	     I'Params <- param_type(any)
	   |]
	   Append_object(I, ME -> ME1)
	   Set_current_modules(ME1)
	   Extend_paths -> Paths
	   Extend_paths <- list(nil,Paths)
	   Get_current_with( -> W)
	   Current -> C
	   Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,W,nil),C)
	   Make_basic_env(CL)
	   Extend_paths <- Paths
	   Current -> current_env(CE, C1)
	   I'Env <- CE
	   Current <- C1
	 |)

'condition' Obj_is_in_objs(OBJECT_EXPR, OBJECT_EXPRS)

  'rule' Obj_is_in_objs(Obj, list(Obj1, Objs)):
	 Equal_object(Obj, Obj1)

  'rule' Obj_is_in_objs(Obj, list(Obj1, Objs)):
	 Obj_is_in_objs(Obj, Objs)

'condition' Equal_object(OBJECT_EXPR, OBJECT_EXPR)

  'rule' Equal_object(obj_name(N1), obj_name(N2)):
	 Equal_name(N1, N2)

'condition' Equal_name(NAME, NAME)

  'rule' Equal_name(name(P1,Id1), name(P2,Id2)):
	 Equal_id_or_op(Id1,Id2)

  'rule' Equal_name(qual_name(P1, Obj1, Id1), qual_name(P2, Obj2, Id2)):
	 Equal_id_or_op(Id1,Id2)
	 Equal_object(Obj1, Obj2)

'action' Append_object(Object_id, MODULE_ENV -> MODULE_ENV)

  'rule' Append_object(I, object_env(I1, ME) -> object_env(I1, ME1)):
	 Append_object(I, ME -> ME1)

  'rule' Append_object(I, scheme_env(I1, ME) -> scheme_env(I1, ME1)):
	 Append_object(I, ME -> ME1)

  'rule' Append_object(I, nil -> object_env(I, nil)):

-- checking for modules defined in second part of extend also being defined in first
'action' Check_duplicate_modules(CLASS_ENV)

-- debug
-- 'rule' Check_duplicate_modules(CE)
-- Putmsg("Checking duplicates in ")
-- print(CE)

  'rule' Check_duplicate_modules(instantiation_env(_,CE)):
	 Check_duplicate_modules(CE)

  'rule' Check_duplicate_modules(extend_env(CE1, CE2, W, AD)):
	 Get_env_modules(CE2 -> ME)
	 Check_duplicate_modules1(ME, CE2, CE1)

'action' Check_duplicate_modules1(MODULE_ENV, CLASS_ENV, CLASS_ENV)

  'rule' Check_duplicate_modules1(object_env(I, ME), CE1, CE2):
	 I'Ident -> Id
	 I'Pos -> P
	 [|
	   Unadapt_env_name(name(P, id_op(Id)), CE1 -> act_name(N))
-- debug
-- Putmsg("Checking for ")
-- Print_name(N)
-- Putnl()
-- print(I)
-- Putmsg(" from ")
-- print(CE1)
-- Putmsg(" in ")
-- print(CE2)
-- Putnl()
	   Lookup_object_in_env(obj_name(N), CE2, nil -> object_id(I1))
	   Puterror(P)
	   Putmsg("Object ")
	   Print_name(N)
	   Putmsg(" also defined at ")
	   I1'Pos -> P1
	   PrintPos(P1)
	   Putnl()
	 |]
	 Check_duplicate_modules1(ME, CE1, CE2)

  'rule' Check_duplicate_modules1(nil, CE1, CE2):


'action' Add_hides(DEFINEDS, ADAPTS -> ADAPTS)
  'rule' Add_hides(list(disamb(P,Id,T),DS), ADS -> hide(Id,ADS1)):
	 Puterror(P)
	 Putmsg("Disambiguation in hidden item: ignored")
	 Putnl()
	 Add_hides(DS, ADS -> ADS1)

  'rule' Add_hides(list(def_name(P,Id), DS), ADS -> hide(Id,ADS1)):
	 Add_hides(DS, ADS -> ADS1)

  'rule' Add_hides(nil, ADS -> ADS):
	 
'action' Add_renames(RENAMES, ADAPTS -> ADAPTS)
-- checking of duplicates etc done later
	 
  'rule' Add_renames(list(rename(disamb(P,Id,T),OD),DS), ADS -> ADS1):
	 Puterror(P)
	 Putmsg("Disambiguation in new item: ignored")
	 Putnl()
	 Add_renames(list(rename(def_name(P,Id),OD),DS), ADS -> ADS1)

  'rule' Add_renames(list(rename(ND,disamb(P,Id,T)),DS), ADS -> ADS1):
	 Puterror(P)
	 Putmsg("Disambiguation in old item: ignored")
	 Putnl()
	 Add_renames(list(rename(ND,def_name(P,Id)),DS), ADS -> ADS1)

  'rule' Add_renames(list(rename(def_name(P1,Nid),def_name(P2,Oid)), RS), ADS -> rename(Nid,Oid,ADS1)):
	 Add_renames(RS, ADS -> ADS1)

  'rule' Add_renames(nil, ADS -> ADS):

'action' Adapt_withs(OBJECT_EXPRS, ADAPTS -> OBJECT_EXPRS)

  'rule' Adapt_withs(list(Obj, Objs), Ads -> list(Obj1, Objs1)):
	 Adapt_with(Obj, Ads -> Obj1)
	 Adapt_withs(Objs, Ads -> Objs1)

  'rule' Adapt_withs(nil, Ads -> nil):

'action' Adapt_with(OBJECT_EXPR, ADAPTS -> OBJECT_EXPR)
-- "with X in use X for Y" = "use X for Y in with Y" 
-- "with X in hide X" = "hide X in with X"

  'rule' Adapt_with(obj_appl(Obj, A), ADS -> Obj):
	 Object_pos(Obj -> P)
	 Puterror(P)
	 Putmsg("Element objects not allowed in with clauses")
	 Putnl()
	 
  'rule' Adapt_with(obj_array(TS, Obj), ADS -> Obj):
	 Object_pos(Obj -> P)
	 Puterror(P)
	 Putmsg("Array objects not allowed in with clauses")
	 Putnl()
	 
  'rule' Adapt_with(obj_fit(Obj, F), ADS -> Obj):
	 Object_pos(Obj -> P)
	 Puterror(P)
	 Putmsg("Fitting objects not allowed in with clauses")
	 Putnl()
	 
  'rule' Adapt_with(obj_name(qual_name(P, Obj, Id)), ADS -> obj_name(qual_name(P, Obj1, Id))):
	 Adapt_with(Obj, ADS -> Obj1)
	 
  'rule' Adapt_with(obj_name(name(P, Id)), rename(Nid,Oid,ADS) -> Obj1):
	 (|
	   -- only def_names can be objects
	   eq(Id,Nid)
	   where(obj_name(name(P, Oid)) -> Obj1)
	 ||
	   Adapt_with(obj_name(name(P, Id)), ADS -> Obj1) 
	 |)

  'rule' Adapt_with(Obj, hide(Id,ADS) -> Obj1):
	 Adapt_with(Obj, ADS -> Obj1)

  'rule' Adapt_with(Obj, nil -> Obj):

'action' Concat_withs(OBJECT_EXPRS, OBJECT_EXPRS -> OBJECT_EXPRS)

  'rule' Concat_withs(list(Obj, Objs1), Objs2 -> list(Obj, Objs3)):
	 Concat_withs(Objs1, Objs2 -> Objs3)

  'rule' Concat_withs(nil, Objs -> Objs):

'action' Prefix_withs(OBJECT_EXPRS, OBJECT_EXPRS -> OBJECT_EXPRS)

  'rule' Prefix_withs(list(Obj, Objs), Objs1 -> Objs2):
	 Prefix_with(Obj, Objs1 -> Objs3)
	 Prefix_withs(Objs, Objs1 -> Objs4)
	 Concat_withs(Objs3, Objs4 -> Objs2)

  'rule' Prefix_withs(nil, Objs -> nil):

'action' Prefix_with(OBJECT_EXPR, OBJECT_EXPRS -> OBJECT_EXPRS)

  'rule' Prefix_with(Obj, list(Obj1, Objs1) -> list(Obj2, Objs2)):
	 Concat_objs(Obj, Obj1 -> Obj2)
	 Prefix_with(Obj, Objs1 -> Objs2)

  'rule' Prefix_with(Obj, nil -> nil):

------------------------------------------------------------------
-- Variables
------------------------------------------------------------------

'action' Make_variable_env_defs(VARIABLE_DEFS)

  'rule' Make_variable_env_defs(list(D, DS)):
	 Make_variable_env_def(D)
	 Make_variable_env_defs(DS)

  'rule' Make_variable_env_defs(nil):

'action' Make_variable_env_def(VARIABLE_DEF)

  'rule' Make_variable_env_def(single(P, Id, T, E)):
	 Make_variable_def(P, Id)

  'rule' Make_variable_env_def(multiple(P, Ids, T)):
	 Make_variable_defs(P, Ids)

'action' Make_variable_defs(POS, IDENTS)

  'rule' Make_variable_defs(P, list(Id, Ids)):
	 Make_variable_def(P, Id)
	 Make_variable_defs(P, Ids)

  'rule' Make_variable_defs(P, nil):

'action' Make_variable_def(POS, IDENT)

  'rule' Make_variable_def(P, Id)
	 Get_current_variables(-> VARS)
	 (|
	   Lookup_env_variable_id(Id, nil, VARS -> variable_id(I))
	   I'Pos -> P1
	   Puterror(P)
	   Putmsg("Variable identifier ")
	   Print_id(Id)
	   Putmsg(" already defined at ")
	   PrintPos(P1)
	   Putnl()
	 ||
	   New_variable_id(P, Id -> I)
	   Set_current_variables(variable_env(I, VARS))
	 |)
	 	 

------------------------------------------------------------------
-- Channels
------------------------------------------------------------------

'action' Make_channel_env_defs(CHANNEL_DEFS)

  'rule' Make_channel_env_defs(list(D, DS)):
	 Make_channel_env_def(D)
	 Make_channel_env_defs(DS)

  'rule' Make_channel_env_defs(nil):

'action' Make_channel_env_def(CHANNEL_DEF)

  'rule' Make_channel_env_def(single(P, Id, T)):
	 Make_channel_def(P, Id)

  'rule' Make_channel_env_def(multiple(P, Ids, T)):
	 Make_channel_defs(P, Ids)

'action' Make_channel_defs(POS, IDENTS)

  'rule' Make_channel_defs(P, list(Id, Ids)):
	 Make_channel_def(P, Id)
	 Make_channel_defs(P, Ids)

  'rule' Make_channel_defs(P, nil):

'action' Make_channel_def(POS, IDENT)

  'rule' Make_channel_def(P, Id)
	 Get_current_channels(-> CHS)
	 (|
	   Lookup_env_channel_id(Id, CHS -> channel_id(I))
	   I'Pos -> P1
	   Puterror(P)
	   Putmsg("Channel identifier ")
	   Print_id(Id)
	   Putmsg(" already defined at ")
	   PrintPos(P1)
	   Putnl()
	 ||
	   New_channel_id(P, Id -> I)
	   Set_current_channels(channel_env(I, CHS))
	 |)
	 	 


