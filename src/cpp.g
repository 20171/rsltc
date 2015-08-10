-- RSL Type Checker
-- Copyright (C) 2000 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the translator to C++

'module' cpp

'use' ast print ext env objects values types pp cc c_ast c_unparse
      c_decl sml

'export' Translate_to_CPP CPP_global_object CPP_init
	 Id_or_op_to_id Rearrange_application
	 Add_to_table_types Collect_type_ids
	 Is_in_ids

-----------------------------------------------------------------------
-- Translate to C++
-----------------------------------------------------------------------
'action' Max_prod_length(-> INT)

-- Microsoft Visual C++ compilers don't like the product templates!
  'rule' Max_prod_length(-> 0):
	 VisualCPP()

-- max size of product defined in RSL_prod.h
  'rule' Max_prod_length(-> 10)

'var' CCFilename : STRING

'var' HFilename : STRING

'var' Declared_types : Type_ids

'var' Current_funs : Value_ids -- stack of functions being defined

'var' Local_depth : INT -- > 0 means in env_local 

'var' Test_cases : TEST_CASE_DEFS

-- stacks of bindings and their types (for making variables for extra
-- namespaces for local expressions, quantified expressions, etc)

'type' BINDINGSS

       list (head : BINDINGS,
	     tail : BINDINGSS)
       nil

'type' PRODUCT_TYPES

       list (head : PRODUCT_TYPE,
	     tail : PRODUCT_TYPES)
       nil

'var' Current_parms : BINDINGSS

'var' Current_parm_types : PRODUCT_TYPES

'var' RSL_ts : C_NAME
'var' RSL_char_ts : C_NAME
'var' RSL_string_ts : C_NAME
'var' RSL_bool_ts : C_NAME
'var' RSL_int_ts : C_NAME
'var' RSL_double_ts : C_NAME
'var' RSL_identity : C_NAME
'var' RSL_true : C_NAME

--begin
-- Universal type ids of maps used as types of variables
'var' TableTypes : IDENTS 
--end

'action' CPP_init

  'rule' CPP_init:
	 Module_name -> S
	 string_to_id(S -> Id)
	 OpenHFile(Id -> Sh)
	 HFilename <- Sh
	 OpenCcFile(Id -> Scc)
	 CCFilename <- Scc
	 C_Init(S, Sh, Scc)
	 Declared_types <- nil
	 Current_funs <- nil
	 Local_depth <- 0
	 Current_parms <- nil
	 Current_parm_types <- nil
	 Test_cases <- nil
	 Namespace_init
	 string_to_id("RSL_to_string" -> Id1)
	 RSL_ts <- C_NAME'id(Id1)
	 string_to_id("RSL_char_to_string" -> Id2)
	 RSL_char_ts <- C_NAME'id(Id2)
	 string_to_id("RSL_string_to_string" -> Id3)
	 RSL_string_ts <- C_NAME'id(Id3)
	 string_to_id("RSL_bool_to_string" -> Id4)
	 RSL_bool_ts <- C_NAME'id(Id4)
	 string_to_id("RSL_int_to_string" -> Id5)
	 RSL_int_ts <- C_NAME'id(Id5)
	 string_to_id("RSL_double_to_string" -> Id6)
	 RSL_double_ts <- C_NAME'id(Id6)
	 string_to_id("RSL_identity" -> Id7)
	 RSL_identity <- C_NAME'id(Id7)
	 string_to_id("RSL_true" -> Id8)
	 RSL_true <- C_NAME'id(Id8)
	 --beg
		TableTypes <- nil
	 --end
	 
	 

'action' Translate_to_CPP (IDENT, CLASS, MODULE_KIND)

  'rule' Translate_to_CPP(Id, CL, K):
	 (|
	   HasErrors()
	   Putmsg("Errors found, so cannot translate")
	   Putnl()
	 ||
	   Get_current_with(->Objs)
	   Open_c_globals(Objs)
	   C_id_to_string(Id -> S)
	   [|
	     eq(K, object)
	     Concatenate3("namespace ", S, " {\n" -> S1)
	     WriteHCcString(S1) 
	     DefaultPos(-> P)
	     New_object_id(P, Id -> I)
	     Push_namespace(I)
	     Current -> current_env(CE, _)
	     Qualify_class_env(I, CE -> CE1)
	     I'Env <- CE1
	   |]
	   Resolve_class(CL)
	   Translate_class(CL, top)
	   Get_current_top_values(-> Is)
	   C_Check_ambiguity(Is)
	   [|
	     eq(K, object)
	     Pop_namespace()
	     Concatenate3("\n} // end of namespace ", S, "\n" -> S2)
	     WriteHCcString(S2)
	   |]
	   [|
	     Test_cases -> TCs
	     where(TCs -> list(_,_))
	     IfIoWanted()
	     Translate_test_case_defs(TCs)
	     Mk_main_function
	     EndIfIoWanted()
	   |]
	   Concatenate3("\n#endif //", S, "_RSL\n" -> S3)
	   WriteHString(S3)
	   CloseHFile()
	   CloseCcFile()
	   Putmsg("Translated as ")
	   HFilename -> Sh
	   Putmsg(Sh)
	   Putmsg(" and ")
	   CCFilename -> Scc
	   Putmsg(Scc)
	   Putnl()
	 |)

'action' CPP_global_object(IDENT, Object_id, CLASS)

  'rule' CPP_global_object(Id, I, CL):
	 (|
	   HasErrors()	-- no need for message: generated in Translate_to_CPP
	 ||
	   I'Params -> nil
	   C_id_to_string(Id -> S)
	   Concatenate3("namespace ", S, " {\n" -> S1)
	   WriteHCcString(S1) 
	   Push_namespace(I)
	   Resolve_class(CL)
	   Translate_class(CL, lower)
	   Get_current_top_values(-> Is)
	   C_Check_ambiguity(Is)
	   Pop_namespace()
	   Concatenate3("\n} // end of namespace ", S, "\n" -> S2)
	   WriteHCcString(S2)
	 ||
	   I'Pos -> P
	   Puterror(P)
	   Putmsg("Cannot translate object arrays")
	   Putnl()
	 |)
	 
'action' Open_c_globals(OBJECT_EXPRS)

  'rule' Open_c_globals(Objs)
	 Get_global_object_ids(-> Ids)
	 Open_c_globals1(Ids, Objs)

'action' Open_c_globals1(IDENTS, OBJECT_EXPRS)

  'rule' Open_c_globals1(list(Id, Ids), Objs):
	 C_id_to_string(Id -> S)
	 Open_c_withs(S, Id, Objs)
	 Open_c_globals1(Ids, Objs)

  'rule' Open_c_globals1(nil, _):

'action' Open_c_withs(STRING, IDENT, OBJECT_EXPRS)

  'rule' Open_c_withs(S, Id, list(Obj, Objs)):
	 (|
	   where(Obj -> obj_name(name(_, id_op(Id1))))
	   eq(Id, Id1)
	   Concatenate3("\nusing namespace ", S, ";\n" -> S1)
	   WriteHCcString(S1)
	 ||
	   where(Obj -> obj_name(qual_name(P, Obj1, Id1)))
	   Split_name(qual_name(P, Obj1, Id1) -> obj_name(name(_, id_op(Id2))), N2)
	   eq(Id, Id2)
	   Object_to_string(obj_name(N2) -> S2)
	   string_to_id(S2 -> Id22)
	   C_id_to_string(Id22 -> S22)
	   Concatenate3("\nusing namespace ", S, "::" -> S1)
	   Concatenate3(S1, S22, ";\n" -> S3)
	   WriteHCcString(S3)
	 ||
	   -- ignore
	 |)
	 Open_c_withs(S, Id, Objs)

  'rule' Open_c_withs(_, _, nil):

'action' Translate_class(CLASS, MODULE_CATEGORY)

  'rule' Translate_class(basic(DS), Cat):
	 Translate_decls(DS, Cat)

  'rule' Translate_class(instantiation(name(P,id_op(Id)), Objs), Cat):
	 Get_id_of_scheme(Id -> scheme_id(I))
	 I'With -> W   
	 Set_current_with(W)
	 I'Class -> CL1
	 Resolve_class(CL1)
	 Translate_class(CL1, lower) -- so test cases not included

  'rule' Translate_class(extend(CL1, CL2), Cat):
	 In_left
	 Translate_class(CL1, Cat)
	 Left_right
	 Translate_class(CL2, Cat)
	 Out_right

  'rule' Translate_class(hide(H, C), Cat):
	 [|
	   where(H -> list(D,_))
	   (| where(D -> def_name(P,_)) || where(D -> disamb(P,_,_)) |)
	   Putwarning(P)
	   Putmsg("hidings are ignored")
	   Putnl()
	 |]
	 Translate_class(C, Cat)

  'rule' Translate_class(rename(R, C), Cat)
	 [|
	   where(R -> list(rename(D, _),_))
	   (| where(D -> def_name(P,_)) || where(D -> disamb(P,_,_)) |)
	   Putwarning(P)
	   Putmsg("renamings are ignored")
	   Putnl()
	 |]
	 Translate_class(C, Cat)

  'rule' Translate_class(with(P,Obj, C), Cat):
	 Translate_class(C, Cat)

  'rule' Translate_class(nil, _):

-----------------------------------------------------------------------
-- Type declarations
-----------------------------------------------------------------------

'action' Translate_decls(DECLS, MODULE_CATEGORY)

  'rule' Translate_decls(DS, Cat):
	 Translate_type_decls(DS, nil -> Ids)
	 Declared_types -> Done
	 Subtract_types(Ids, Done -> Ids1)
	 Translate_type_ids(Ids1, nil, Done, nil)
	 Translate_variant_components(Ids1)
	 Translate_object_decls(DS)
	 Collect_value_decls(DS, nil -> Vids)
	 Translate_value_ids(Vids, nil, nil)
	 Translate_variable_decls(DS)
	 [|
	   eq(Cat, top)
	   test_case_ids <- nil
	   Collect_test_cases(DS)
	 |]

'action' Translate_object_decls(DECLS)

  'rule' Translate_object_decls(list(D, DS)):
	 Translate_object_decl(D)
	 Translate_object_decls(DS)

  'rule' Translate_object_decls(nil):

'action' Translate_object_decl(DECL)

  'rule' Translate_object_decl(object_decl(_, ODS)):
	 Translate_object_defs(ODS)

  'rule' Translate_object_decl(_):

'action' Translate_object_defs(OBJECT_DEFS)

  'rule' Translate_object_defs(list(D, DS)):
	 Translate_object_def(D)
	 Translate_object_defs(DS)

  'rule' Translate_object_defs(nil):

'action' Translate_object_def(OBJECT_DEF)

  'rule' Translate_object_def(odef(P, Id, PS, CL))
	 (|
	   eq(PS, nil)
	   Get_current_modules(-> ME)
	   (|
	     Lookup_object_in_module(Id, ME -> object_id(I))
	   || -- may be local: try with localised name
	     Localise_id(P, Id -> LId)
	     Lookup_object_in_module(LId, ME -> object_id(I))
	   |)
	   Current -> C
	   I'Param_env -> PCE
	   I'Env -> CE
	   I'Ident -> Id1
	   Current <- current_env(CE,current_env(PCE, C))
	   Extend_paths -> Paths
	   Extend_paths <- list(nil, list(nil, Paths))
	   C_id_to_string(Id1 -> S)
	   Concatenate3("\nnamespace ", S, " {\n" -> S1)
	   WriteHCcString(S1) 
	   Push_namespace(I)
	   Translate_class(CL, lower)
	   Get_current_top_values(-> Is)
	   C_Check_ambiguity(Is)
	   Pop_namespace()
	   Concatenate3("\n} // end of namespace ", S, "\n\n" -> S2)
	   WriteHCcString(S2)
	   Current -> current_env(CE1,current_env(PCE1,C1))
	   Current <- C1
	   Extend_paths <- Paths
	   Get_current_with(-> Objs)
	   Open_c_withs(S, Id, Objs)
	 ||
	   Puterror(P)
	   Putmsg("Cannot translate object arrays")
	   Putnl()
	 |)


'action' Translate_type_decls(DECLS, Type_ids -> Type_ids)

  'rule' Translate_type_decls(list(D, DS), Ids -> Ids2):
	 Translate_type_decl(D, Ids -> Ids1)
	 Translate_type_decls(DS, Ids1 -> Ids2)

  'rule' Translate_type_decls(nil, Ids -> Ids):

'action' Translate_type_decl(DECL, Type_ids -> Type_ids)

  'rule' Translate_type_decl(type_decl(_, Defs), Ids -> Ids1):
	 Translate_type_defs(Defs, Ids -> Ids1)

  'rule' Translate_type_decl(object_decl(_, Defs), Ids -> Ids1):
	 Translate_object_type_decls(Defs, Ids -> Ids1)

  'rule' Translate_type_decl(_, Ids -> Ids):

'action' Translate_object_type_decls(OBJECT_DEFS, Type_ids -> Type_ids)

  'rule' Translate_object_type_decls(list(D, Ds), Ids -> Ids1):
	 Translate_object_type_decl(D, Ids -> Ids2)
	 Translate_object_type_decls(Ds, Ids2 -> Ids1)

  'rule' Translate_object_type_decls(nil, Ids -> Ids):

'action' Translate_object_type_decl(OBJECT_DEF, Type_ids -> Type_ids)

  'rule' Translate_object_type_decl(odef(P, Id, _, CL), Ids -> Ids1)
	 Get_current_modules(-> ME)
	 (|
	   Lookup_object_in_module(Id, ME -> object_id(I))
	 || -- may be local: try with localised name
	   Localise_id(P, Id -> LId)
	   Lookup_object_in_module(LId, ME -> object_id(I))
	 |)
	 Current -> C
	 I'Param_env -> PCE
	 I'Env -> CE
	 Current <- current_env(CE,current_env(PCE, C))
	 Extend_paths -> Paths
	 Extend_paths <- list(nil, list(nil, Paths))
	 Translate_class_type_decls(CL, Ids -> Ids1)
	 Current -> current_env(CE1,current_env(PCE1,C1))
	 Current <- C1
	 Extend_paths <- Paths

'action' Translate_class_type_decls(CLASS, Type_ids -> Type_ids)

  'rule' Translate_class_type_decls(basic(DS), Ids -> Ids1):
	 Translate_type_decls(DS, Ids -> Ids1)

  'rule' Translate_class_type_decls(instantiation(name(P,id_op(Id)), Objs), Ids -> Ids1):
	 Get_id_of_scheme(Id -> scheme_id(I))
	 I'With -> W   
	 Set_current_with(W)
	 I'Class -> CL1
	 Resolve_class(CL1)
	 Translate_class_type_decls(CL1, Ids -> Ids1)

  'rule' Translate_class_type_decls(extend(CL1, CL2), Ids -> Ids1):
	 In_left
	 Translate_class_type_decls(CL1, Ids -> Ids2)
	 Left_right
	 Translate_class_type_decls(CL2, Ids2 -> Ids1)
	 Out_right

  'rule' Translate_class_type_decls(hide(H, C), Ids -> Ids1):
	 Translate_class_type_decls(C, Ids -> Ids1)

  'rule' Translate_class_type_decls(rename(R, C), Ids -> Ids1)
	 Translate_class_type_decls(C, Ids -> Ids1)

  'rule' Translate_class_type_decls(with(P,Obj, C), Ids -> Ids1):
	 Translate_class_type_decls(C, Ids -> Ids1)

  'rule' Translate_class_type_decls(nil, Ids -> Ids):





'action' Translate_type_defs(TYPE_DEFS, Type_ids -> Type_ids)

  'rule' Translate_type_defs(list(H,T), Ids -> Ids2):
	 (|
	   Translate_type_def(H -> type_id(I))
	   Insert(I, Ids -> Ids1)
	   Translate_type_defs(T, Ids1 -> Ids2)
	 ||
	   Translate_type_defs(T, Ids -> Ids2)
	 |)

  'rule' Translate_type_defs(nil, Ids -> Ids):

'action' Translate_type_def(TYPE_DEF -> OPT_TYPE_ID)

  'rule' Translate_type_def(abbrev(P, Id, _) -> type_id(I)):
	 Get_current_types(-> TE)
	 (|
	   Lookup_env(Id, TE -> type_id(I))
	 || -- may be local: try with localised name
	   Localise_id(P, Id -> LId)
	   Lookup_env(LId, TE -> type_id(I))
	 |)

  'rule' Translate_type_def(sort(P, Id) -> type_id(I)):
	 Get_current_types(-> TE)
	 (|
	   Lookup_env(Id, TE -> type_id(I))
	 || -- may be local: try with localised name
	   Localise_id(P, Id -> LId)
	   Lookup_env(LId, TE -> type_id(I))
	 |)

  'rule' Translate_type_def(variant(P, Id, CS) -> type_id(I)):
	 Get_current_types(-> TE)
	 (|
	   Lookup_env(Id, TE -> type_id(I))
	 || -- may be local: try with localised name
	   Localise_id(P, Id -> LId)
	   Lookup_env(LId, TE -> type_id(I))
	 |)

  'rule' Translate_type_def(record(P, Id, _) -> type_id(I)):
	 Get_current_types(-> TE)
	 (|
	   Lookup_env(Id, TE -> type_id(I))
	 || -- may be local: try with localised name
	   Localise_id(P, Id -> LId)
	   Lookup_env(LId, TE -> type_id(I))
	 |)

  'rule' Translate_type_def(union(P, Id, CS) -> nil):
	 Puterror(P)
	 Putmsg("Cannot translate union types: ignored")
	 Putnl()

'action' Translate_type_ids(todo:Type_ids, waiting:Type_ids, done:Type_ids, FOUND)

  'rule' Translate_type_ids(nil, nil, Done, _):
	 Declared_types <- Done

  'rule' Translate_type_ids(nil, Waiting, Done, Found):
	 (|
	   eq(Found, found)
	   Translate_type_ids(Waiting, nil, Done, nil)
	 ||
	   where(Waiting -> Type_ids'list(I, _))
	   I'Pos -> P
	   I'Ident -> Id
	   Puterror(P)
	   Putmsg("Type ")
	   Print_id(Id)
	   Putmsg(" seems to be involved in mutual recursion")
	   Putnl()
	 |)

  'rule' Translate_type_ids(list(I, IS), Waiting, Done, Found):
	 I'Ident -> Id
	 I'Type -> Type
	 Collect_type_ids(Type, nil -> Deps)
	 Subtract_types(Deps, Done -> Deps1)
	 (| -------------------------------
	   I'Def -> abbreviation(T)
	   (|
	     eq(Deps1, nil)
	     I'Qualifier -> Is
	     (|
	       I'Subtype -> nil
	       Open_qual_namespaces(Is, h_file -> Is1)
	     ||
	       Open_qual_namespaces(Is, h_and_cc_file -> Is1)
	     |)
	     Translate_type(T -> T1)
	     C_Begin_decl()
	       C_Add_decl_specifier(typedef)
	       C_Add_decl_specifier(type(T1))
	       C_Add_declarator(dname(id(Id)))
	     C_End_decl(-> D)
	     C_Decl_to_string(D -> Sh)
	     WriteHString(Sh)
	     (|
	       I'Subtype -> funct(I1)
	       -- would like to put this in #ifdef RSL_pre
	       -- but some namespaces get outside such ifdefs
	       -- WriteHCcString("\n#ifdef RSL_pre\n//subtype predicate\n")
	       WriteHCcString("\n//subtype predicate\n")
	       I1'Pos -> P
	       I1'Ident -> Fid
	       I1'Type -> FT
	       I1'Def -> Def
-- debug
-- where(Def -> expl_fun(_, E, _, _, _, _))
-- Print_expr(E)
-- Putnl()
-- print(Def)
	       Current_funs -> Ids
	       Current_funs <- list(I1, Ids)
	       Translate_expl_fun(P, Fid, FT, Def -> Decl)
	       Current_funs <- Ids
	       C_Decl_to_string(Decl -> Scc)
	       WriteCcString(Scc)
	       C_Decl_to_string_h(Decl -> Sh1)
	       WriteHString(Sh1)
	       -- WriteHCcString("#endif //RSL_pre\n")
	       Close_qual_namespaces(Is1, h_and_cc_file)
	     ||
	       Close_qual_namespaces(Is1, h_file)
	     |)
	     Insert(I, Done -> Done1)
	     Translate_type_ids(IS, Waiting, Done1, found)
	   ||
	     Insert(I, Waiting -> Waiting1)
	     Translate_type_ids(IS, Waiting1, Done, Found)
	   |)
	 || -------------------------------
	   I'Type -> sort(K)
	   (| -- allow for recursion (possibly mutual)
	      -- through variants
	     (| eq(Deps1, nil) || where(K -> variant(_)) |)
	     I'Qualifier -> Is
--	     (|
--	       where(K -> record(Cs))
--	       Length_cs(Cs -> N)
--	       Max_prod_length(-> Max)
--	       le(N, Max)
--	       where(h_file -> File)
--	     ||
--	       where(h_and_cc_file -> File)
--	     |)
	     -- above was wrong: reconstructors need .cc file
	     Open_qual_namespaces(Is, h_and_cc_file -> Is1)
	     Translate_sort(I, K)
	     Close_qual_namespaces(Is1, h_and_cc_file)
	     Insert(I, Done -> Done1)
	     Translate_type_ids(IS, Waiting, Done1, found)
	   ||
	     Insert(I, Waiting -> Waiting1)
	     Translate_type_ids(IS, Waiting1, Done, Found)
	   |)
	 |)


-----------------------------------------------------------------------
-- Type expressions
-----------------------------------------------------------------------

'action' Translate_type(TYPE_EXPR -> C_TYPE_SPECIFIER)

  'rule' Translate_type(unit -> void):

  'rule' Translate_type(bool -> bool):

  'rule' Translate_type(int -> int):

  'rule' Translate_type(nat -> int):

  'rule' Translate_type(real -> double):

  'rule' Translate_type(char -> rsl_char):

  'rule' Translate_type(text -> rsl_string):

  'rule' Translate_type(time -> double):
	 IsTimed()

  'rule' Translate_type(defined(I, Q) -> T):
	 I'Type -> Type
	 (|
	   where(Type -> abbrev(_))
	   I'Def -> abbreviation(TExpr)
	   Translate_type(TExpr -> T)
	 ||
	   I'Ident -> Id
	   where(Type -> sort(_))
	   I'Qualifier -> Is
	   Translate_type_id(Id, Q, Is -> T)
	 |)

  'rule' Translate_type(bracket(T) -> S):
	 Translate_type(T -> S)

  'rule' Translate_type(TExpr -> CT):
	 Universal_type_id(TExpr -> Id)
	 Lookup_declared_type(Id -> CT)

  'rule' Translate_type(TExpr -> CT):
	 where(TExpr -> product(Ts))
	 Universal_type_id(TExpr -> UId)
	 Translate_product(UId, Ts)
	 Define_universal_type(UId -> CT)

  'rule' Translate_type(TExpr -> CT):
	 where(TExpr -> fun(ParmType, Arrow, Result))
	 Universal_type_id(TExpr -> UId)
	 C_Begin_decl()
	   C_Add_decl_specifier(typedef)
	   where(Result -> result(T, _, _, _, _))
	   Translate_type(T -> T1)
	   C_Add_decl_specifier(type(T1))
--	   (|
--	     Type_is_product(ParmType -> Ts)
--	   ||
--	     where(PRODUCT_TYPE'list(ParmType, nil) -> Ts)
--	   |)
--	   Parm_to_args(Ts -> Args)
	   Parm_to_args(list(ParmType, nil) -> Args)
	   C_Add_declarator(with_args(with_bracket(ptr_to(ptr, dname(id(UId)))), Args, nil))
	 C_End_decl(-> Decl)
	 C_Decl_to_string(Decl -> Sh)
	 WriteHString(Sh)
	 Define_universal_type(UId -> CT)

  'rule' Translate_type(T -> CT):
	 where(T -> infin_set(T1))
	 Universal_type_id(T -> UId)
	 C_Begin_decl()
	   C_Add_decl_specifier(typedef)
	   Mk_Set_id(-> Id)
	   Translate_type(T1 -> T11)
	   C_Add_decl_specifier(type(template(Id, list(T11, nil))))
	   C_Add_declarator(dname(id(UId)))
	 C_End_decl(-> D)
	 C_Decl_to_string(D -> Sh)
	 WriteHString(Sh)
	 Define_universal_type(UId -> CT)
	 [|
	   VisualCPP() -- add an RSL_to_string def
		       -- as Visual C++ compilers cannot find
		       -- template one
	   RSL_ts -> FN
	   C_Begin_func_def(FN)
	     C_Add_decl_specifier(type(string))
	     C_Arg_decl_specifier(type(const))
	     C_Arg_decl_specifier(type(ref_to(CT)))
	     string_to_id("set" -> Set)
	     C_Arg_declarator(dname(id(Set)))
	     string_to_id("s" -> S)
	     C_Add_function_body(decl(decl(list(type(string), nil), list(with_init(dname(id(S)), assign(text_literal("{"))), nil))))
	     string_to_id("p" -> P)
	     C_Add_function_body(decl(decl(list(type(CT), nil), list(with_init(dname(id(P)), assign(name(id(Set)))), nil))))
	     string_to_id("RSL_set_empty" -> Empty)
	     string_to_id("hd" -> Hd)
	     where(unary(not,postfix(name(id(Empty)), bracket(list(name(id(P)), nil)))) -> Cond)
	     RSL_to_string_name(T11 -> NM)
	     where(expr(binary(name(id(S)), plus_assign, postfix(name(NM), bracket(list(postfix(name(id(Hd)), bracket(list(name(id(P)), nil))), nil))))) -> C1) 
	     where(expr(binary(name(id(P)), assign, binary(name(id(P)), modulo, postfix(name(template_member(Id, list(T11, nil), id(Id))), bracket(list(postfix(name(id(Hd)), bracket(list(name(id(P)), nil))), nil)))))) -> C2)
	     where(C_STATEMENT'if(Cond, expr(binary(name(id(S)), plus_assign, text_literal(","))), nil)	 -> C3)
	     C_Add_function_body(while(Cond, compound(list(C1, list(C2, list(C3, nil))))))
	     C_Add_function_body(expr(binary(name(id(S)), plus_assign, text_literal("}"))))
	     C_Add_function_body(return(name(id(S))))
	   C_End_func_def(-> D1)
	   C_Decl_to_string(D1 -> Sh1)
	   WriteHString(Sh1)
	   [|
	     -- Visual C++ compiler needs RSL_to_string
	     -- functions defined in namespaces to also
	     -- be defined at the top level, or it cannot
	     -- find occurrences in templates
             Namespaces_to_idents(-> Ids)
             ne(Ids, nil)
             Define_to_string_at_top(UId, Ids)
	   |]
	 |]

  'rule' Translate_type(T -> CT):
	 where(T -> infin_list(T1))
	 (|
	   Match(T1, nil, char)
	   where(C_TYPE_SPECIFIER'rsl_string -> CT)
	 ||
	   Universal_type_id(T -> UId)
	   C_Begin_decl()
	     C_Add_decl_specifier(typedef)
	     Mk_List_id(-> Id)
	     Translate_type(T1 -> T11)
	     C_Add_decl_specifier(type(template(Id, list(T11, nil))))
	     C_Add_declarator(dname(id(UId)))
	   C_End_decl(-> D)
	   C_Decl_to_string(D -> Sh)
	   WriteHString(Sh)
	   Define_universal_type(UId -> CT)
	   [|
	     VisualCPP() -- add an RSL_to_string def
			 -- as Visual C++ compilers cannot find
			 -- template one
	     RSL_ts -> FN
	     C_Begin_func_def(FN)
	       C_Add_decl_specifier(type(string))
	       C_Arg_decl_specifier(type(const))
	       C_Arg_decl_specifier(type(ref_to(CT)))
	       string_to_id("list" -> List)
	       C_Arg_declarator(dname(id(List)))
	       string_to_id("s" -> S)
	       C_Add_function_body(decl(decl(list(type(string), nil), list(with_init(dname(id(S)), assign(text_literal("<."))), nil))))
	       string_to_id("p" -> P)
	       C_Add_function_body(decl(decl(list(type(CT), nil), list(with_init(dname(id(P)), assign(name(id(List)))), nil))))
	       string_to_id("RSL_list_empty" -> Empty)
	       string_to_id("hd" -> Hd)
	       string_to_id("tl" -> Tl)
	       where(unary(not,postfix(name(id(Empty)), bracket(list(name(id(P)), nil)))) -> Cond)
	       RSL_to_string_name(T11 -> NM)
	       where(expr(binary(name(id(S)), plus_assign, postfix(name(NM), bracket(list(postfix(name(id(Hd)), bracket(list(name(id(P)), nil))), nil))))) -> C1) 
	       where(expr(binary(name(id(P)), assign, postfix(name(id(Tl)), bracket(list(name(id(P)), nil))))) -> C2)
	       where(C_STATEMENT'if(Cond, expr(binary(name(id(S)), plus_assign, text_literal(","))), nil)  -> C3)
	       C_Add_function_body(while(Cond, compound(list(C1, list(C2, list(C3, nil))))))
	       C_Add_function_body(expr(binary(name(id(S)), plus_assign, text_literal(".>"))))
	       C_Add_function_body(return(name(id(S))))
	     C_End_func_def(-> D1)
	     C_Decl_to_string(D1 -> Sh1)
	     WriteHString(Sh1)
	     [|
	       -- Visual C++ compiler needs RSL_to_string
	       -- functions defined in namespaces to also
	       -- be defined at the top level, or it cannot
	       -- find occurrences in templates
	       Namespaces_to_idents(-> Ids)
	       ne(Ids, nil)
	       Define_to_string_at_top(UId, Ids)
	     |]
	   |]
	 |)

  'rule' Translate_type(T -> CT):
	 where(T -> infin_map(D, R))
	 Universal_type_id(T -> UId)
	 C_Begin_decl()
	   C_Add_decl_specifier(typedef)
	   Mk_Map_id(-> Id)
	   Translate_type(D -> D1)
	   Translate_type(R -> R1)
	   C_Add_decl_specifier(type(template(Id, list(D1, list(R1, nil)))))
	   C_Add_declarator(dname(id(UId)))
	 C_End_decl(-> Decl)
	 C_Decl_to_string(Decl -> Sh)
--b	
-- need check SQLWanted() and Is_table_type(Uid) 
	 (|
	   SQLWanted()
	   Is_table_type(UId)
	   id_to_string(UId -> STb)
	   Concatenate(STb, "_tbl" -> STbl)
	   string_to_id(STbl -> IDtbl)
	   C_Type_to_string(D1 ->SIDd)
	   string_to_id(SIDd -> IDd)
	   Make_mode_name(D1 -> named_type(D1MId))
	   C_Type_to_string(R1 -> SR1)
	   string_to_id(SR1 -> IDr)
	   (|
	     where(R -> defined(I, _))
	     I'Type -> sort(record(CS))
	     Record_destructorsm(CS, 0 -> N, CTS)
	     where(IDr -> IDProd)
	   ||	
	     Type_is_product(R -> P)
	     Translate_product_type(P -> P1)
	     Product_types_field(P1, 0 -> N, CTS)
	     string_to_id("__" -> IDProd)
	   ||
	     where(1 -> N)
	     string_to_id("RSL_f1" -> IDF1)
	     Make_mode_name(R1 -> R1M)
	     where(C_TYPE_SPECIFIERS'list(R1, list(R1M, list(named_type(IDF1), nil))) -> CTS)
	     string_to_id("__" -> IDProd)
	   |)
	   Int_to_string(N -> NStr)
	   Concatenate("CRT_ST_PROD_", NStr -> SCrt)
	   string_to_id(SCrt -> IDCrt)
	   C_Begin_func_def(id(IDCrt))
	     C_Arg_declarator(dname(id(IDtbl)))
	     C_Arg_declarator(dname(id(IDProd)))
	     C_Arg_declarator(dname(id(IDd)))
	     C_Arg_declarator(dname(id(D1MId)))
	     string_to_id("RSL_key" -> IDkey)
	     C_Arg_declarator(dname(id(IDkey)))
	     C_Arg_declarator(dname(id(IDr))) 
	     Makeup_arglistm(CTS)
	   C_End_func_def(-> Macr)
	   C_Decl_to_string(Macr -> SMacr)
	   WriteHString(SMacr) 
	   C_Begin_decl()
	     C_Add_decl_specifier(typedef)
	     string_to_id("RSL_SQL"-> IDsql)
	     Ident_to_cts(IDtbl -> Tbcts)
	     C_Add_decl_specifier(type(template(IDsql, list(D1, list(R1, list(Tbcts, nil))))))
	     C_Add_declarator(dname(id(UId)))
	   C_End_decl(-> Dsql)
	   C_Decl_to_string(Dsql -> SDsql)
	   WriteHString(SDsql)
	 ||
	   WriteHString(Sh)  
	 |)
--end
	 
	 Define_universal_type(UId -> CT)
	 [|
	   VisualCPP() -- add an RSL_to_string def
		       -- as Visual C++ compilers cannot find
		       -- template one
	   RSL_ts -> FN
	   C_Begin_func_def(FN)
	     C_Add_decl_specifier(type(string))
	     C_Arg_decl_specifier(type(const))
	     C_Arg_decl_specifier(type(ref_to(CT)))
	     string_to_id("map" -> Map)
	     C_Arg_declarator(dname(id(Map)))
	     string_to_id("s" -> S)
	     C_Add_function_body(decl(decl(list(type(string), nil), list(with_init(dname(id(S)), assign(text_literal("["))), nil))))
	     string_to_id("p" -> P)
	     C_Add_function_body(decl(decl(list(type(CT), nil), list(with_init(dname(id(P)), assign(name(id(Map)))), nil))))
	     string_to_id("h" -> H)
	     C_Add_function_body(decl(decl(list(type(D1), nil), list(dname(id(H)), nil))))
	     string_to_id("RSL_map_empty" -> Empty)
	     string_to_id("hd" -> Hd)
	     Mk_Set_id( -> RSLSet)
	     where(unary(not,postfix(name(id(Empty)), bracket(list(name(id(P)), nil)))) -> Cond)
	     RSL_to_string_name(D1 -> NMD)
	     RSL_to_string_name(R1 -> NMR)
	     where(expr(binary(name(id(H)), assign, postfix(name(id(Hd)), bracket(list(name(id(P)), nil))))) -> C0)
	     where(expr(binary(name(id(S)), plus_assign, postfix(name(NMD), bracket(list(name(id(H)), nil))))) -> C1) 
	     where(expr(binary(name(id(S)), plus_assign, text_literal("+>"))) -> C2)
	     where(expr(binary(name(id(S)), plus_assign, postfix(name(NMR), bracket(list(postfix(name(id(P)), index(name(id(H)))), nil))))) -> C3) 
	     where(expr(binary(name(id(P)), assign, binary(name(id(P)), modulo, postfix(name(template_member(RSLSet, list(D1, nil), id(RSLSet))), bracket(list(postfix(name(id(Hd)), bracket(list(name(id(P)), nil))), nil)))))) -> C4)
	     where(C_STATEMENT'if(Cond, expr(binary(name(id(S)), plus_assign, text_literal(","))), nil)	 -> C5)
	     C_Add_function_body(while(Cond, compound(list(C0, list(C1, list(C2, list(C3, list(C4, list(C5, nil)))))))))
	     C_Add_function_body(expr(binary(name(id(S)), plus_assign, text_literal("]"))))
	     C_Add_function_body(return(name(id(S))))
	   C_End_func_def(-> D2)
	   C_Decl_to_string(D2 -> Sh1)
	   WriteHString(Sh1)
	   [|
	     -- Visual C++ compiler needs RSL_to_string
	     -- functions defined in namespaces to also
	     -- be defined at the top level, or it cannot
	     -- find occurrences in templates
             Namespaces_to_idents(-> Ids)
             ne(Ids, nil)
             Define_to_string_at_top(UId, Ids)
	   |]
	 |]

  'rule' Translate_type(TExpr -> T):
	 Maxtype(TExpr -> TExpr1)
	 ne(TExpr, TExpr1)
	 Translate_type(TExpr1 -> T)

  'rule' Translate_type(TExpr -> named_type(Dummy)):
	 string_to_id("/*Untranslatable type*/" -> Dummy)
	 Putmsg("Cannot translate type: ")
	 Print_type(TExpr)
	 Putnl()

'action' Translate_product_type(PRODUCT_TYPE -> C_TYPE_SPECIFIERS)

  'rule' Translate_product_type(list(T, Ts) -> list(T1, Ts1)):
	 Translate_type(T -> T1)
	 Translate_product_type(Ts -> Ts1)

  'rule' Translate_product_type(nil -> nil):

-- Auxiliary functions
'action' Define_to_string_at_top(IDENT, IDENTS)

  'rule' Define_to_string_at_top(Id, Ids):
	 RSL_ts -> NM
	 C_Begin_func_def(NM)
	   C_Add_decl_specifier(type(string))
	   C_Arg_decl_specifier(type(const))
	   C_Arg_decl_specifier(type(ref_to(qualified(named_type(Id), Ids))))
	   string_to_id("RSL_v" -> RSL_v)
	   C_Arg_declarator(dname(id(RSL_v)))
	   where(postfix(name(qualified(NM, Ids)),
			 bracket(list(name(id(RSL_v)), nil))) -> E)
	   C_Add_function_body(return(E))
	 C_End_func_def(-> D)
	 Close_namespaces_h()
	 C_Decl_to_string(D -> Sh)	WriteHString(Sh)
	 Open_namespaces_h()


'action' Record_to_string(IDENT, STRING, STRING, INT, C_TYPE_SPECIFIERS -> C_DECL)

  'rule' Record_to_string(Id, VS, CS, N, Ts -> D)
	 RSL_ts -> NM
	 C_Begin_func_def(NM)
	   C_Add_decl_specifier(type(string))
	   C_Arg_decl_specifier(type(const))
	   C_Arg_decl_specifier(type(ref_to(named_type(Id))))
	   string_to_id("RSL_v" -> RSL_v)
	   C_Arg_declarator(dname(id(RSL_v)))
	   (|
	     eq(VS,"")
	     where(RSL_v -> RSL_v1)
	   ||
	     Concatenate("RSL_v.", VS -> VS1)
	     string_to_id(VS1 -> RSL_v1)
	   |)
	   Product_to_string(RSL_v1, 1, N, Ts -> E)
	   where(binary(text_literal("("), plus, binary(E, plus, text_literal(")"))) -> E1)
	   (|
	     eq(CS, "")
	     C_Add_function_body(return(E1))
	   ||
	     string_to_id("s_" -> S_)
	     C_Add_function_body(decl(decl(list(type(string), nil), list(with_init(dname(id(S_)), assign(text_literal(CS))), nil))))
	     C_Add_function_body(return(binary(name(id(S_)), plus, E1)))
	   |)
	 C_End_func_def(-> D)

'action' Product_to_string(IDENT, INT, INT, C_TYPE_SPECIFIERS -> C_EXPR)

  'rule' Product_to_string(RSL_v, I, N, list(T, Ts) -> E)
	 Mk_nth_field_id(I -> Fid)
	 RSL_to_string_name(T -> NM)
	 where(postfix(name(NM),
	     bracket(list(postfix(name(id(RSL_v)), dot(id(Fid))), nil))) -> E1)
	 (|
	   lt(I, N)
	   Product_to_string(RSL_v, I+1, N, Ts -> E2)
	   where(binary(E1, plus, binary(text_literal(","), plus, E2)) -> E)
	 ||
	   where(E1 -> E)
	 |)

'action' String_to_RSL_name(C_TYPE_SPECIFIER -> C_NAME)

  'rule' String_to_RSL_name(CT -> NM):
	 C_Type_to_string(CT -> Str) string_to_id(Str -> Id)
	 where(C_NAME'id(Id) -> NM)

'action' RSL_to_string_name(C_TYPE_SPECIFIER -> C_NAME)

  'rule' RSL_to_string_name(T -> NM):
	 (|
	   eq(T, rsl_char)
	   RSL_char_ts -> NM
	 ||
	   eq(T, rsl_string)
	   RSL_string_ts -> NM
	 ||
	   eq(T, bool)
	   RSL_bool_ts -> NM
	 ||
	   eq(T, int)
	   RSL_int_ts -> NM
	 ||
	   eq(T, double)
	   RSL_double_ts -> NM
	 ||
	   where(T -> qualified(_, Ids))
	   VisualCPP() -- Visual C++ compilers seem to need this
	   RSL_ts -> NM1
	   where(C_NAME'qualified(NM1, Ids) -> NM)
	 ||
	   RSL_ts -> NM
	 |)

'sweep' Collect_type_ids(ANY, Type_ids -> Type_ids)

  'rule' Collect_type_ids(defined(I,_), IS -> IS1):
	 Insert(I, IS -> IS1)

'sweep' Collect_value_ids(ANY, Value_ids -> Value_ids)

  'rule' Collect_value_ids(val_occ(_,I,_), IS -> list(I, IS)):

'sweep' Collect_fun_ids(ANY, Value_ids -> Value_ids)

  'rule' Collect_fun_ids(val_occ(_,I,_), Is -> Is1):
	 (|
	   Isin_value_ids(I, Is)
	   where(Is -> Is1)
	 ||
	   I'Def -> expl_fun(_, V, _, _, _, _)
	   Collect_fun_ids(V, list(I, Is) -> Is1)
	 ||
	   where(Is -> Is1)
	 |)

'sweep' Collect_pre_occs(ANY, VALUE_EXPRS -> VALUE_EXPRS)

  'rule' Collect_pre_occs(PO:pre_occ(_,_,_), POs -> POs1):
	 Insert_pre_occ(PO, POs -> POs1)

-- Insert(ID, IDs -> IDs ^ <ID>)
'action' Insert(Type_id, Type_ids -> Type_ids)

  'rule' Insert(I, list(I1, IS) -> list(I1, IS1)):
	 (|
	   eq(I, I1)
	   where(IS -> IS1)
	 ||
	   Insert(I, IS -> IS1)
	 |) 

  'rule' Insert(I, nil -> list(I, nil)):

'action' Insert_pre_occ(VALUE_EXPR, VALUE_EXPRS -> VALUE_EXPRS)

  'rule' Insert_pre_occ(PO, list(PO1, POs) -> list(PO1, POs1)):
	 where(PO -> pre_occ(_, I, _))
	 where(PO1 -> pre_occ(_, I1, _))
	 (|
	   eq(I, I1)
	   where(POs -> POs1)
	 ||
	   Insert_pre_occ(PO, POs -> POs1)
	 |) 

  'rule' Insert_pre_occ(PO, nil -> list(PO, nil)):

-- Subtract(A, B -> A\B)
'action' Subtract_types(Type_ids, Type_ids -> Type_ids)

  'rule' Subtract_types(list(I, IS), B -> C):
	 Subtract_types(IS, B -> C1)
	 (|
	   Notin(I, B)
	   where(Type_ids'list(I, C1) -> C)
	 ||
	   where(C1 -> C)
	 |)

  'rule' Subtract_types(nil, _ -> nil):

'action' Intersect_values(Value_ids, Value_ids -> Value_ids)

  'rule' Intersect_values(list(I, IS), B -> C):
	 Intersect_values(IS, B -> C1)
	 (|
	   Isin_values(I, B)
	   where(Value_ids'list(I, C1) -> C)
	 ||
	   where(C1 -> C)
	 |)

  'rule' Intersect_values(nil, _ -> nil):

'condition' Isin_values(Value_id, Value_ids)

  'rule' Isin_values(I1, list(I, Is)):
	 (| eq(I1, I) || Isin_values(I1, Is) |)

'action' Parm_to_args(PRODUCT_TYPE -> C_ARG_DECLS)

  'rule' Parm_to_args(list(T, Ts) -> As):
	 (|
	   ne(T, unit)
	   Translate_arg(T -> T1)
	   where(arg(list(type(const), list(type(T1), nil)), nil, nil) -> A)
	   Parm_to_args(Ts -> As2)
	   where(C_ARG_DECLS'list(A, As2) -> As)
	 || -- skip 'void' type parameters
	   Parm_to_args(Ts -> As)
	 |)

  'rule' Parm_to_args(nil -> nil)

-----------------------------------------------------------------------
-- Sort, record and product type declaration support
-----------------------------------------------------------------------

'action' Translate_product(IDENT, PRODUCT_TYPE)

  'rule' Translate_product(Id, Ts):
	 DefaultPos(-> Pos)
	 Length_pr(Ts -> N)
	 Translate_product_type(Ts -> Ts1)
	 (|
	   Max_prod_length(-> Max)
	   le(N, Max)
	   string_to_id("RSL_constructor_fun" -> CCF)
	   Conc_c_types(Ts1, list(named_type(CCF), nil) -> Ts2)
	   C_Begin_decl()
	     C_Add_decl_specifier(typedef)
	     Mk_Product_id(N -> PId)
	     C_Add_decl_specifier(type(template(PId, Ts2)))
	     C_Add_declarator(dname(id(Id)))
	   C_End_decl(-> D)
	   C_Decl_to_string(D -> Sp)
	   WriteHString(Sp)
	 ||
	   C_Begin_decl()
	     C_Begin_class_def(struct, id(Id))
	       Add_fields(Ts)
	       Add_basic_member_functions(Pos, Id, Ts, true)
	     C_End_class_def(-> T)
	     C_Add_decl_specifier(type(T))
	   C_End_decl(-> Decl)
	   C_Decl_to_string(Decl -> S)
	   WriteHString(S)
	   -- RSL_to_string function
	   Record_to_string(Id, "", "", N, Ts1 -> D0)
	   C_Decl_to_string(D0 -> Sh0)	 WriteHString(Sh0)
	   [|
	     -- Visual C++ compiler needs RSL_to_string
	     -- functions defined in namespaces to also
	     -- be defined at the top level, or it cannot
	     -- find occurrences in templates
	     VisualCPP()
             Namespaces_to_idents(-> Ids)
             ne(Ids, nil)
             Define_to_string_at_top(Id, Ids)
	   |]
	   [|
	     IfIoWanted_h()
	     Record_io_routines(Pos, Id, Ts, 0 -> Dsh, Dscc)
	     C_Decls_to_string(Dsh -> Sh)	  WriteHString(Sh)
	     EndIfIoWanted_h()
	   |]
	 |)

'action' Translate_sort(Type_id, SORT_KIND)

  'rule' Translate_sort(Id, K):
	 (|
	   eq(K, abstract)
	   Translate_abstract(Id)
	 ||
	   where(K -> record(_))
	   Translate_record(Id)
	 ||
	   where(K -> union(_))
	   --Translate_union(Id)
	   Id'Pos -> P
	   Puterror(P)
	   Putmsg("Cannot translate union")
	   Putnl()
	 ||
	   where(K -> variant(_))
	   Translate_variant(Id)
	 |)

'action' Translate_abstract(Type_id)

  'rule' Translate_abstract(I):
	 I'Pos -> P
	 Putwarning(P)
	 I'Ident -> Ident
	 Print_id(Ident)
	 Putmsg(" is an abstract type, and so is undefined")
	 Putnl()
	 C_Begin_decl()
	   C_id_to_string(Ident -> S1)
	   Concatenate(S1, "/*INCOMPLETE: abstract type*/" -> S2)
	   string_to_id(S2 -> Ident1)
	   C_Begin_class_def(struct, id(Ident1))
	     -- operator==
	     C_Begin_func_def(op_fun(eq))
	       C_Add_decl_specifier(fct(inline))
	       C_Add_decl_specifier(type(bool))
	       C_Arg_decl_specifier(type(const))
	       C_Arg_decl_specifier(type(ref_to(named_type(Ident))))
	       string_to_id("RSL_v" -> RSL_v)
	       C_Arg_declarator(dname(id(RSL_v)))
	       C_Add_cv_qualifier(const)
	       C_Add_function_body(return(literal(bool_true)))
	     C_End_func_def(-> EqualityFunc)
	     C_Add_member(member(EqualityFunc))
	     -- operator!=
	     C_Begin_func_def(op_fun(neq))
	       C_Add_decl_specifier(fct(inline))
	       C_Add_decl_specifier(type(bool))
	       C_Arg_decl_specifier(type(const))
	       C_Arg_decl_specifier(type(ref_to(named_type(Ident))))
	       --string_to_id("RSL_v" -> RSL_v)
	       C_Arg_declarator(dname(id(RSL_v)))
	       C_Add_cv_qualifier(const)
	       C_Add_function_body(return(literal(bool_false)))
	     C_End_func_def(-> InequalityFunc)
	     C_Add_member(member(InequalityFunc))
	   C_End_class_def(-> C)
	   C_Add_decl_specifier(type(C))
	 C_End_decl(-> D)
	 C_Decl_to_string(D -> Sh)	WriteHString(Sh)
	 -- RSL_to_string function
	 RSL_ts -> NM
	 C_Begin_func_def(NM)
	   C_Add_decl_specifier(type(string))
	   C_Arg_decl_specifier(type(const))
	   C_Arg_decl_specifier(type(ref_to(named_type(Ident))))
	   C_Arg_declarator(dname(id(RSL_v)))
	   C_Add_function_body(return(text_literal("Unknown abstract value")))
	 C_End_func_def(-> D0)
	 C_Decl_to_string(D0 -> Sh0)	 WriteHString(Sh0)
	 [|
	   -- Visual C++ compiler needs RSL_to_string
	   -- functions defined in namespaces to also
	   -- be defined at the top level, or it cannot
	   -- find occurrences in templates
	   VisualCPP()
	   Namespaces_to_idents(-> Ids)
	   ne(Ids, nil)
	   Define_to_string_at_top(Ident, Ids)
	 |]
	 [|
	   IfIoWanted()
	   -- operator<<
	   C_Begin_func_def(op_fun(shl))
	     string_to_id("ostream" -> Os)
	     C_Add_decl_specifier(type(ref_to(named_type(Os))))
	     C_Arg_decl_specifier(type(ref_to(named_type(Os))))
	     string_to_id("RSL_os" -> RSL_os)
	     C_Arg_declarator(dname(id(RSL_os)))
	     C_Arg_decl_specifier(type(const))
	     C_Arg_decl_specifier(type(ref_to(named_type(Ident))))
	     --string_to_id("RSL_v" -> RSL_v)
	     C_Arg_declarator(dname(id(RSL_v)))
	     --
	     C_Add_function_body(return(name(id(RSL_os))))
	   C_End_func_def(-> OutputFunc)
	   C_Decl_to_string_h(OutputFunc -> Sh1)	WriteHString(Sh1)
	   C_Decl_to_string(OutputFunc -> Scc1)		WriteCcString(Scc1)
	   -- operator>>
	   C_Begin_func_def(op_fun(shr))
	     string_to_id("istream" -> Is)
	     C_Add_decl_specifier(type(ref_to(named_type(Is))))
	     C_Arg_decl_specifier(type(ref_to(named_type(Is))))
	     string_to_id("RSL_is" -> RSL_is)
	     C_Arg_declarator(dname(id(RSL_is)))
	     C_Arg_decl_specifier(type(ref_to(named_type(Ident))))
	     C_Arg_declarator(dname(id(RSL_v)))
	     --
	     C_Add_function_body(return(name(id(RSL_is))))
	   C_End_func_def(-> InputFunc)
	   C_Decl_to_string_h(InputFunc -> Sh2)		WriteHString(Sh2)
	   C_Decl_to_string(InputFunc -> Scc2)		WriteCcString(Scc2)
	   EndIfIoWanted()
	 |]

'action' Translate_arg(TYPE_EXPR -> C_TYPE_SPECIFIER)

  'rule' Translate_arg(T -> T11):
	 Translate_type(T -> T1)
	 Translated_size(T -> N)
	 (|
	   Threshold_size(-> NT)
	   gt(N, NT)
	   where(C_TYPE_SPECIFIER'ref_to(T1) -> T11)
	 ||
	   where(T1 -> T11)
	 |)

'action' Translate_variant(Type_id)

  'rule' Translate_variant(I):
	 I'Ident -> Ident
	 I'Type -> sort(variant(Vs))
	 --
	 Variant_tag_decls(Vs)
	 Variant_forward_decls(Vs)
	 --
	 C_Begin_decl()
	   C_Begin_class_def(struct, id(Ident))
	     -- tag field
	     C_Begin_decl()
	       C_Add_decl_specifier(type(int))
	       Mk_tag_id(nil -> TagId)
	       C_Add_declarator(dname(id(TagId)))
	     C_End_decl(-> TagField)
	     C_Add_member(member(TagField))
	     -- pointer field
	     C_Begin_decl()
	       string_to_id("RSL_class" -> BaseId)
	       C_Add_decl_specifier(type(ptr_to(named_type(BaseId))))
	       Mk_ptr_id( -> PtrId)
	       C_Add_declarator(dname(id(PtrId)))
	     C_End_decl(-> PtrField)
	     C_Add_member(member(PtrField))
	     -- default constructor
	     C_Begin_func_def(id(Ident))
	       C_Add_decl_specifier(fct(inline))
	       C_Arg_decl_specifier(type(const))
	       C_Arg_decl_specifier(type(int))
	       string_to_id("0" -> Zero)
	       C_Arg_def_val(literal(int(Zero)))
	       Mk_nth_parm_id(0 -> ParmId)
	       C_Arg_declarator(dname(id(ParmId)))
	       C_Add_function_body(expr(binary(name(id(TagId)), assign, name(id(ParmId)))))
	       C_Add_function_body(expr(binary(name(id(PtrId)), assign, literal(int(Zero)))))
	     C_End_func_def(-> DefaultConstructor)
	     C_Add_member(member(DefaultConstructor))
	     --
	     Variants_to_constructors(Vs)
	     -- destructor helper (RSL_destructor())
	     string_to_id("RSL_destructor" -> RSL_destr)
	     C_Begin_func_def(id(RSL_destr))
	       C_Add_decl_specifier(type(void))
	       Variants_to_destructor_cases(Vs -> DCs)
	       (|
		 ne(DCs, nil)
		 C_Add_function_body(switch(name(id(TagId)), compound(DCs)))
	       ||
		 -- constant records only
		 C_Add_function_body(nil)
	       |)
	     C_End_func_def(-> DestrHelper)
	     C_Add_member(member(DestrHelper))
	     -- destructor
	     C_Begin_func_def(destr_call(Ident))
	       C_Add_decl_specifier(fct(inline))
	       C_Add_function_body(expr(postfix(name(id(RSL_destr)), bracket(nil))))
	     C_End_func_def(-> Destr)
	     C_Add_member(member(Destr))
	     -- copy constructor
	     C_Begin_func_def(id(Ident))
	       C_Arg_decl_specifier(type(const))
	       C_Arg_decl_specifier(type(ref_to(named_type(Ident))))
	       string_to_id("RSL_v" -> RSL_v)
	       string_to_id("refcnt" -> Refcnt)
	       C_Arg_declarator(dname(id(RSL_v)))
	       Variants_to_cases(Vs -> Cases)
	       --
	       where(
		 expr(
		   postfix(
		     postfix(
		       postfix(name(id(RSL_v)), dot(id(PtrId))),
		       arrow(id(Refcnt))
		     ),
		     inc
		   )
		 ) -> IncRefcnt
	       )
	       Append_statement(Cases, IncRefcnt  -> Cases1)
	       --
	       [|
		 ne(Cases, nil)
		 C_Add_function_body(switch(postfix(name(id(RSL_v)), dot(id(TagId))), compound(Cases1)))
	       |]
	       C_Add_function_body(
		 expr(
		   binary(
		     name(id(TagId)),
		     assign,
		     postfix(name(id(RSL_v)), dot(id(TagId)))
		   )
		 )
	       )
	       C_Add_function_body(
		 expr(
		   binary(
		     name(id(PtrId)),
		     assign,
		     postfix(name(id(RSL_v)), dot(id(PtrId)))
		   )
		 )
	       )	 
	     C_End_func_def(-> CopyCons)
	     C_Add_member(member(CopyCons))
	     -- operator=
	     C_Begin_func_def(op_fun(assign))
	       C_Add_decl_specifier(type(const))
	       C_Add_decl_specifier(type(ref_to(named_type(Ident))))
	       C_Arg_decl_specifier(type(const))
	       C_Arg_decl_specifier(type(ref_to(named_type(Ident))))
	       --string_to_id("RSL_v" -> RSL_v)
	       C_Arg_declarator(dname(id(RSL_v)))
	       C_Add_function_body(
		 if(binary(this, eq, unary(address_of, name(id(RSL_v)))),
		   return(name(id(RSL_v))), nil
		 )
	       )
	       [|
		 ne(Cases, nil)
		 C_Add_function_body(switch(postfix(name(id(RSL_v)), dot(id(TagId))), compound(Cases1)))
	       |]
	       C_Add_function_body(expr(postfix(name(id(RSL_destr)), bracket(nil))))
	       C_Add_function_body(
		 expr(
		   binary(
		     name(id(TagId)),
		     assign,
		     postfix(name(id(RSL_v)), dot(id(TagId)))
		   )
		 )
	       )
	       C_Add_function_body(
		 expr(
		   binary(
		     name(id(PtrId)),
		     assign,
		     postfix(name(id(RSL_v)), dot(id(PtrId)))
		   )
		 )
	       )
	       C_Add_function_body(return(unary(deref, this)))
	     C_End_func_def(-> AssignOpFunc)
	     C_Add_member(member(AssignOpFunc))
	     -- operator==
	     C_Begin_func_def(op_fun(eq))
	       C_Add_decl_specifier(type(bool))
	       C_Add_cv_qualifier(const)
	       C_Arg_decl_specifier(type(const))
	       C_Arg_decl_specifier(type(ref_to(named_type(Ident))))
	       --string_to_id("RSL_v" -> RSL_v)
	       C_Arg_declarator(dname(id(RSL_v)))
	       C_Add_function_body(
		 if(binary(name(id(TagId)), neq, postfix(name(id(RSL_v)), dot(id(TagId)))),
		   return(literal(bool_false)), nil
		 )
	       )
	       Variants_to_compare_cases(Vs -> CCs)
	       (|
	         eq(CCs, nil)
		 C_Add_function_body(return(literal(bool_true)))
	       ||
		 Append_statement(CCs, default -> CCs1)
		 Append_statement(CCs1, return(literal(bool_true)) -> CCs2)
		 C_Add_function_body(switch(name(id(TagId)), compound(CCs2)))
	       |)
	     C_End_func_def(-> Equality)
	     C_Add_member(member(Equality))
	     -- operator!=
	     C_Begin_func_def(op_fun(neq))
	       C_Add_decl_specifier(fct(inline))
	       C_Add_cv_qualifier(const)
	       C_Add_decl_specifier(type(bool))
	       C_Arg_decl_specifier(type(const))
	       C_Arg_decl_specifier(type(ref_to(named_type(Ident))))
	       C_Arg_declarator(dname(id(RSL_v)))
	       C_Add_function_body(return(unary(not,
		    postfix(name(op_fun(eq)), bracket(list(name(id(RSL_v)), nil))))))
	     C_End_func_def(-> Unequality)
	     C_Add_member(member(Unequality))
	   C_End_class_def(-> C)
	   C_Add_decl_specifier(type(C))
	 C_End_decl(-> D)
	 C_Decl_to_string_h(D -> Sh)   WriteHString(Sh)
	 C_Decl_to_string_cc(D -> Scc) WriteCcString(Scc)
	 -- RSL_to_string function
	 Variant_to_string_routine(Ident, Vs -> D0)
	 C_Decl_to_string_h(D0 -> Sh0)	 WriteHString(Sh0)
	 C_Decl_to_string(D0 -> Scc0)	 WriteCcString(Scc0)
	 [|
	   -- Visual C++ compiler needs RSL_to_string
	   -- functions defined in namespaces to also
	   -- be defined at the top level, or it cannot
	   -- find occurrences in templates
	   VisualCPP()
	   Namespaces_to_idents(-> Ids)
	   ne(Ids, nil)
	   Define_to_string_at_top(Ident, Ids)
	 |]
	 [|
	   IfIoWanted()
	   Variant_io_routines(Ident, Vs -> Dsh, Dscc)
	   C_Decls_to_string_h(Dsh -> Sh1)	 WriteHString(Sh1)
	   C_Decls_to_string(Dscc -> Scc1)	 WriteCcString(Scc1)
	   EndIfIoWanted()
	 |]

'action' Translate_variant_components(Type_ids)

  'rule' Translate_variant_components(list(I, Is)):
	 [|
	   I'Type -> sort(variant(Vs))
	   I'Ident -> Ident
	   I'Qualifier -> QIs
	   Open_qual_namespaces(QIs, h_and_cc_file -> QIs1)
	   Translate_variant_records(Ident, Vs, QIs)
	   Close_qual_namespaces(QIs1, h_and_cc_file)
	 |]
	 Translate_variant_components(Is)

  'rule' Translate_variant_components(nil):
	 
'action' Variant_tag_decls(VARIANTS)

  'rule' Variant_tag_decls(Vs):
	 Variant_tag_decls1(1, Vs)

'action' Variant_tag_decls1(counter:INT, VARIANTS)

  'rule' Variant_tag_decls1(N, list(record(_, Cons, _), Rs)):
	 [|
	   where(Cons -> con_ref(I))
	   I'Ident -> Cons_id_or_op
	   C_Begin_decl()
	     C_Add_decl_specifier(storage(static))
	     C_Add_decl_specifier(type(const))
	     C_Add_decl_specifier(type(int))
	     (|
	       where(Cons_id_or_op -> id_op(Id))
	       Mk_tag_id(ident(Id) -> TagId)
	     ||
	       where(Cons_id_or_op -> op_op(Op))
	       Mk_op_tag_id(Op -> TagId)
	     |)
	     Int_to_string(N -> NS)
	     string_to_id(NS -> TagVal)
	     C_Add_declarator(with_init(dname(id(TagId)), assign(literal(int(TagVal)))))
	   C_End_decl(-> TagDecl)
	   C_Decl_to_string(TagDecl -> Sh)
	   WriteHString(Sh)
	 |]
	 Variant_tag_decls1(N + 1, Rs)

  'rule' Variant_tag_decls1(_, nil)

'action' Variant_forward_decls(VARIANTS)

  'rule' Variant_forward_decls(list(record(_, Cons, Comps), Rs)):
	 [|
	   ne(Comps, nil)
	   where(Cons -> con_ref(I))
	   I'Ident -> Cons_id_or_op
	   (|
	     where(Cons_id_or_op -> id_op(Id))
	     Mk_record_id(Id -> Id1)
	   ||
	     where(Cons_id_or_op -> op_op(Op))
	     Mk_op_record_id(Op -> Id1)
	   |)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(elaborated(struct, Id1)))
	   C_End_decl(-> D)
	   C_Decl_to_string(D -> S)
	   WriteHString(S)
	 |]
	 Variant_forward_decls(Rs)

  'rule' Variant_forward_decls(nil)

'action' Mk_tag_id(OPT_IDENT -> IDENT)

  'rule' Mk_tag_id(nil -> Id):
	 string_to_id("RSL_tag" -> Id)

  'rule' Mk_tag_id(ident(Id) -> Id1):
	 id_to_string(Id -> S)
	 Concatenate3("RSL_", S, "_tag" -> S1)
	 string_to_id(S1 -> Id1)

'action' Mk_op_tag_id(OP -> IDENT)

  'rule' Mk_op_tag_id(Op -> Id):
	 Op_name(Op -> Ops)
	 Concatenate3("RSL_", Ops, "_tag" -> S)
	 string_to_id(S -> Id)

'action' Op_to_cid(OP -> IDENT)

  'rule' Op_to_cid(Op -> Id):
	 Translate_op(Op -> Cop)
	 C_Op_to_string(Cop -> Cops)
	 string_to_id(Cops -> Id)

'action' Id_or_op_to_id(ID_OR_OP -> IDENT)

  'rule' Id_or_op_to_id(id_op(Id) -> Id):

  'rule' Id_or_op_to_id(op_op(Op) -> Id)
	 Op_name(Op -> S)
	 Concatenate3("RSL_", S , "_op" -> S1)
	 string_to_id(S1 -> Id)

'action' Op_name(OP -> STRING) -- simliar to sml.g::Op_to_alpha_string()

  'rule' Op_name(eq -> "EQ"):

  'rule' Op_name(neq -> "NOTEQ"):

  'rule' Op_name(eqeq -> "EQEQ"):

  'rule' Op_name(gt -> "GT"):

  'rule' Op_name(lt -> "LT"):

  'rule' Op_name(ge -> "GEQ"):

  'rule' Op_name(le -> "LEQ"):

  'rule' Op_name(supset -> "PSUP"):

  'rule' Op_name(subset -> "PSUB"):

  'rule' Op_name(supseteq -> "SUP"):

  'rule' Op_name(subseteq -> "SUB"):

  'rule' Op_name(isin -> "ISIN"):

  'rule' Op_name(notisin -> "NOTISIN"):

  'rule' Op_name(rem -> "MOD"):

  'rule' Op_name(caret -> "CONC"):

  'rule' Op_name(union -> "UNION"):

  'rule' Op_name(override -> "OVER"):

  'rule' Op_name(mult -> "AST"):

  'rule' Op_name(div -> "DIV"):

  'rule' Op_name(hash -> "HASH"):

  'rule' Op_name(inter -> "INTER"):

  'rule' Op_name(exp -> "EXP"):

  'rule' Op_name(abs -> "ABS"):

  'rule' Op_name(int -> "INT"):

  'rule' Op_name(real -> "REAL"):

  'rule' Op_name(card -> "CARD"):

  'rule' Op_name(len -> "LEN"):

  'rule' Op_name(inds -> "INDS"):

  'rule' Op_name(elems -> "ELEMS"):

  'rule' Op_name(hd -> "HD"):

  'rule' Op_name(tl -> "TL"):

  'rule' Op_name(dom -> "DOM"):

  'rule' Op_name(rng -> "RNG"):

  'rule' Op_name(wait -> "WAIT"):

  'rule' Op_name(plus -> "PLUS"):

  'rule' Op_name(minus -> "MINUS"):

'action' Mk_record_id(IDENT -> IDENT)

  'rule' Mk_record_id(Id1 -> Id2)
	 id_to_string(Id1 -> S1)
	 Concatenate3("RSL_", S1, "_type" -> S2)
	 string_to_id(S2 -> Id2)

'action' Mk_op_record_id(OP -> IDENT)

  'rule' Mk_op_record_id(Op -> Id):
	 Op_name(Op -> Ops)
	 Concatenate3("RSL_", Ops, "_type" -> S)
	 string_to_id(S -> Id)

'action' Mk_nth_field_id(INT -> IDENT)

  'rule' Mk_nth_field_id(N -> Id):
	 Int_to_string(N -> NS)
	 Concatenate("RSL_f", NS -> S)
	 string_to_id(S -> Id)

'action' Mk_nth_parm_id(INT -> IDENT)

  'rule' Mk_nth_parm_id(N -> Id):
	 Int_to_string(N -> NS)
	 Concatenate("RSL_p", NS -> S)
	 string_to_id(S -> Id)

'action' Mk_ptr_id(-> IDENT)

  'rule' Mk_ptr_id(-> Id):
	 string_to_id("RSL_ptr" -> Id)

'action' Variants_to_constructors(VARIANTS)

  'rule' Variants_to_constructors(list(record(Pos, Cons, Comps), Rs)):
	 [|
	   ne(Comps, nil)
	   (|
	     eq(Cons, wildcard)
	     Putwarning(Pos)
	     Putmsg("cannot translate wildcard constructor: ignored")
	     Putnl()
	   ||
	     where(Cons -> con_ref(I))
	     I'Ident -> Cons_id_or_op
	     (|
	       where(Cons_id_or_op -> id_op(Id))
	       Mk_record_id(Id -> Id1)
	       Mk_tag_id(ident(Id) -> TagValId)
	     ||
	       where(Cons_id_or_op -> op_op(Op))
	       Mk_op_record_id(Op -> Id1)
	       Mk_op_tag_id(Op -> TagValId)
	     |)
	     C_Class_id(-> id(Cid))
	     C_Begin_func_def(id(Cid))
	       C_Add_decl_specifier(fct(inline))
	       C_Arg_decl_specifier(type(const))
	       C_Arg_decl_specifier(type(ptr_to(named_type(Id1))))
	       string_to_id("RSL_v" -> RSL_v)
	       C_Arg_declarator(dname(id(RSL_v)))
	       string_to_id("RSL_class" -> BaseId)
	       Mk_tag_id(nil -> TagId)
	       C_Add_function_body(
		 expr(
		   binary(
		     name(id(TagId)),
		     assign,
		     name(id(TagValId))
		   )
		 )
	       )
	       Mk_ptr_id(-> PtrId)
	       C_Add_function_body(
		 expr(
		   binary(
		     name(id(PtrId)),
		     assign,
		     ptr_cast(BaseId, name(id(RSL_v)))
		   )
		 )
	       )
	     C_End_func_def(-> F)
	     C_Add_member(member(F))
	   |)
	 |]
	 Variants_to_constructors(Rs)

  'rule' Variants_to_constructors(nil)

'action' Variants_to_cases(VARIANTS -> C_STATEMENTS)

  'rule' Variants_to_cases(list(record(_, _, nil), Rs) -> Cs):
	 Variants_to_cases(Rs -> Cs)

  'rule' Variants_to_cases(list(record(_, con_ref(I), _), Rs) -> list(C, Cs)):
	 I'Ident -> Cons_id_or_op
	 (|
	   where(Cons_id_or_op -> id_op(Id))
	   Mk_tag_id(ident(Id) -> TagId)
	 ||
	   where(Cons_id_or_op -> op_op(Op))
	   Mk_op_tag_id(Op -> TagId)
	 |)
	 where(C_STATEMENT'case(name(id(TagId))) -> C)
	 Variants_to_cases(Rs -> Cs)

  'rule' Variants_to_cases(nil -> nil)

'action' Variants_to_compare_cases(VARIANTS -> C_STATEMENTS)

  'rule' Variants_to_compare_cases(list(record(_, _, nil), Rs) -> Cs):
	 Variants_to_compare_cases(Rs -> Cs)

  'rule' Variants_to_compare_cases(list(record(_, con_ref(I), _), Rs) -> Cs):
	 I'Ident -> Cons_id_or_op
	 (|
	   where(Cons_id_or_op -> id_op(Id))
	   Mk_tag_id(ident(Id) -> TagId)
	   Mk_record_id(Id -> TypeId)
	 ||
	   where(Cons_id_or_op -> op_op(Op))
	   Mk_op_tag_id(Op -> TagId)
	   Mk_op_record_id(Op -> TypeId)
	 |)
	 Mk_ptr_id(-> PtrId)
	 string_to_id("RSL_v" -> RSL_v)
	 where(
	   binary(
	     unary(deref, ptr_cast(TypeId, name(id(PtrId)))),
	     eq,
	     unary(deref, ptr_cast(TypeId, postfix(name(id(RSL_v)), dot(id(PtrId)))))
	   ) -> Eq
	 )
	 where(C_STATEMENT'case(name(id(TagId))) -> C1)
	 where(return(Eq) -> C2)
	 Append_statement(nil, C1 -> Cs1)
	 Append_statement(Cs1, C2 -> Cs2)
	 Variants_to_compare_cases(Rs -> Cs3)
	 Concatenate_statements(Cs2, Cs3 -> Cs)

  'rule' Variants_to_compare_cases(nil -> nil)

'action' Variants_to_destructor_cases(VARIANTS -> C_STATEMENTS)

  'rule' Variants_to_destructor_cases(list(record(_, _, nil), Rs) -> Cs):
	 Variants_to_destructor_cases(Rs -> Cs)

  'rule' Variants_to_destructor_cases(list(record(_, wildcard, _), Rs) -> Cs):
	 Variants_to_destructor_cases(Rs -> Cs)

  'rule' Variants_to_destructor_cases(list(record(_, con_ref(I), _), Rs) -> Cs):
	 I'Ident -> Cons_id_or_op
	 (|
	   where(Cons_id_or_op -> id_op(Id))
	   Mk_tag_id(ident(Id) -> TagId)
	   Mk_record_id(Id -> TypeId)
	 ||
	   where(Cons_id_or_op -> op_op(Op))
	   Mk_op_tag_id(Op -> TagId)
	   Mk_op_record_id(Op -> TypeId)
	 |)
	 Mk_ptr_id(-> PtrId)
	 string_to_id("RSL_v" -> RSL_v)
	 string_to_id("0" -> Zero)
	 string_to_id("refcnt" -> Refcnt)
	 where(
	   binary(
	     unary(dec, bracket(postfix(name(id(PtrId)), arrow(id(Refcnt))))),
	     eq,
	     literal(int(Zero))
	   ) -> Cond
	 )
	 where(
	   unary(
	     delete,
	     ptr_cast(TypeId, name(id(PtrId)))
	   ) -> Del
	 )
	 where(C_STATEMENTS'nil -> Cs0)
	 where(C_STATEMENT'case(name(id(TagId))) -> C)
	 where(C_STATEMENT'if(Cond, expr(Del), nil) -> St)
	 Append_statement(Cs0, C -> Cs1)
	 Append_statement(Cs1, St -> Cs2)
	 Append_statement(Cs2, break -> Cs3)
	 Variants_to_destructor_cases(Rs -> Cs4)
	 Concatenate_statements(Cs3, Cs4 -> Cs)

  'rule' Variants_to_destructor_cases(nil -> nil)

'action' Translate_variant_records(IDENT, VARIANTS, Object_ids)

  'rule' Translate_variant_records(VarId, list(record(Pos, Cons, Comps), Rs), QIs):
	 (|
	   eq(Cons, wildcard)
	   Putwarning(Pos)
	   Putmsg("cannot translate wildcard constructor: ignored")
	   Putnl()
	 ||
	   where(Cons -> con_ref(I))
	   I'Pos -> P1
	   I'Ident -> Cons_id_or_op
	   (|
	     eq(Comps, nil)
	     Record_id(Cons_id_or_op -> RecId)
	     C_Begin_decl()
	       C_Add_decl_specifier(storage(static))
	       C_Add_decl_specifier(type(const))
	       C_Add_decl_specifier(type(named_type(VarId)))
	       Mk_tag_id(ident(RecId) -> TagId)
	       C_Add_declarator(with_init(dname(id(RecId)), bracket(list(name(id(TagId)), nil))))
	     C_End_decl(-> D)
	     C_Decl_to_string(D -> Sh)
	     WriteHString(Sh)
	   ||
	     (|
	       where(QIs -> list(_, _)) -- variant defined in object
	       Last_object(QIs -> OI)
	       OI'Env -> CE
	       Get_env_top_values(CE -> VE1)
	     || 
	       Get_current_top_values(-> VE1)
	     |)
	     Select_id_by_pos(P1, VE1 -> value_id(I1))
	     I1'Type -> fun(T1, _, _)
	     (|
	       where(T1 -> product(Ts))
	     ||
	       where(PRODUCT_TYPE'list(T1, nil) -> Ts)
	     |)
	     C_record_id(Cons_id_or_op -> CrecId)
	     Length_pr(Ts -> N)
	     Translate_product_type(Ts -> Ts1)
	     (|
	       Type_is_product(T1 -> Ts3)
	       Length_pr(Ts3 -> N3)
	     ||
	       where(Ts -> Ts3)
	       where(N -> N3)
	     |)	       
	     (|
	       Max_prod_length(-> Max)
	       le(N, Max)
	       string_to_id("RSL_constructor_fun" -> CCF)
	       Conc_c_types(Ts1, list(named_type(CCF), nil) -> Ts2)
	       C_Begin_decl()
		 C_Begin_class_def(struct, id(CrecId))
		   string_to_id("RSL_class" -> BaseId)
		   C_Class_add_base(base(id(BaseId), nil))
		   Mk_Product_id(N -> PId)
		   C_Class_add_base(template_base(PId, Ts2, nil))
		   Add_prod_member_functions(Pos, CrecId, PId, Ts2, Ts, N)
		 C_End_class_def(-> C)
		 C_Add_decl_specifier(type(C))
	       C_End_decl(-> D)
	       C_Decl_to_string_h(D -> Sh)   WriteHString(Sh)
--	       Variant_record_prod_constructor(Pos, VarId, Cons_id_or_op, Ts, PId, Ts2)
	       Set_num_data_members(N3)
	       Variant_record_constructor(Pos, VarId, Cons_id_or_op, Ts3)
	       Variant_record_destructors(VarId, Cons_id_or_op, Comps)
	       -- not checked recons when single variant expands to product
	       -- known bug: see ~/tmp/temp.rsl
	       -- TODO
	       Variant_record_reconstructors(VarId, Cons_id_or_op, Comps)
	     ||
	       C_Begin_decl()
		 C_Begin_class_def(struct, id(CrecId))
		   string_to_id("RSL_class" -> BaseId)
		   C_Class_add_base(base(id(BaseId), nil))
		   Components_to_fields(Comps)
		   Add_basic_member_functions(Pos, CrecId, Ts, false)
		 C_End_class_def(-> C)
		 C_Add_decl_specifier(type(C))
	       C_End_decl(-> D)
	       C_Decl_to_string_h(D -> Sh)   WriteHString(Sh)
	       C_Decl_to_string_cc(D -> Scc) WriteCcString(Scc)
	       Set_num_data_members(N3)
	       Variant_record_constructor(Pos, VarId, Cons_id_or_op, Ts3)
	       Variant_record_destructors(VarId, Cons_id_or_op, Comps)
	       Variant_record_reconstructors(VarId, Cons_id_or_op, Comps)
	       -- RSL_to_string function
	       Translate_product_type(Ts3 -> CTs3)
	       (|
	         eq(N, N3)
		 where("" -> VS)
		 where(2 -> Kind)
	       ||
	         where("RSL_f1" -> VS)
		 where(3 -> Kind)
	       |)
	       Record_to_string(CrecId, VS, "", N3, CTs3 -> D0)
	       C_Decl_to_string(D0 -> Sh0)   WriteHString(Sh0)
	       [|
		 IfIoWanted()
		 Record_io_routines(Pos, CrecId, Ts3, Kind -> Dsh, Dscc)
		 C_Decls_to_string_h(Dsh -> Sh1)	WriteHString(Sh1)
		 C_Decls_to_string(Dscc -> Scc1)	WriteCcString(Scc1)
		 EndIfIoWanted()
	       |]
	     |)
	   |)
	 |)
	 Translate_variant_records(VarId, Rs, QIs)

  'rule' Translate_variant_records(_, nil, _):


'action' Variant_record_constructor(POS, var_id:IDENT, Cons_id_or_op:ID_OR_OP, PRODUCT_TYPE)

  'rule' Variant_record_constructor(Pos, VarId, Cons_id_or_op, Ts):
	 C_record_id(Cons_id_or_op -> CrecId)
	 C_cons_fname(Cons_id_or_op -> ConsFid)
	 C_Begin_func_def(ConsFid)
	   C_Add_decl_specifier(type(named_type(VarId)))
	   Makeup_arglist(Ts)
	   Makeup_parms(Pos, Ts -> Parms, Cond, Ss)
	   [|
             ne(Cond, nil)
	     (|
	       where(Ts -> list(T,nil))
	     ||
	       where(TYPE_EXPR'product(Ts) -> T)
	     |)
	     PosAsString(Pos -> PS)
	     C_Name_to_string(ConsFid -> IdS)
	     Parms_to_output_string(Parms, Ts -> SB)
	     GetF2String("%s Arguments of %s(", PS, IdS -> ST1)
	     Append_statement(Ss,
	       cond_warn(Cond,
	                 binary(text_literal(ST1),
			 plus,
			 binary(SB, plus, text_literal(") not in subtypes"))))
			 -> Ss1)
	     where(cpp(ifdef("RSL_pre")) -> S0)
	     where(cpp(endif("RSL_pre")) -> S1)
	     Append_statement(C_STATEMENTS'list(S0, Ss1), S1 -> Ss2)
	     C_Set_function_body(Ss2)
	   |]
	   C_Begin_decl()
	     C_Add_decl_specifier(type(ptr_to(named_type(CrecId))))
	     string_to_id("RSL_v" -> RSL_v)
	     C_Add_declarator(
	       with_init(
		 dname(id(RSL_v)),
		 assign(unary(new, postfix(name(id(CrecId)), bracket(Parms))))
	       )
	     )
	   C_End_decl(-> PtrDecl)
	   C_Add_function_body(decl(PtrDecl))
	   string_to_id("abort" -> Abort)
	   C_Add_function_body(
	     if(unary(not, name(id(RSL_v))),
	       expr(postfix(name(id(Abort)), bracket(nil))), 
	       nil
	     )
	   )
	   C_Add_function_body(
	     return(postfix(name(id(VarId)), bracket(list(name(id(RSL_v)), nil))))
	   )
	 C_End_func_def(-> Decl)
	 C_Decl_to_string_h(Decl -> Sh) WriteHString(Sh)
	 C_Decl_to_string(Decl -> Scc)	WriteCcString(Scc)


'action' Variant_record_prod_constructor(POS, var_id:IDENT, Cons_id_or_op:ID_OR_OP, PRODUCT_TYPE, prod_id:IDENT, prod_args:C_TYPE_SPECIFIERS)

  'rule' Variant_record_prod_constructor(Pos, VarId, Cons_id_or_op, Ts, PId, Ts2):
	 C_record_id(Cons_id_or_op -> CrecId)
	 C_cons_fname(Cons_id_or_op -> ConsFid)
	 C_Begin_func_def(ConsFid)
	   C_Add_decl_specifier(type(named_type(VarId)))
	   Makeup_arglist(Ts)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(ptr_to(named_type(CrecId))))
	     string_to_id("RSL_v" -> RSL_v)
	     Makeup_parms(Pos, Ts -> Parms, Cond, Ss)
	     -- function  not currently used so Cond ignored
	     where(C_EXPR'name(template_member(PId, Ts2, id(PId))) -> E)
	     C_Add_declarator(
	       with_init(
		 dname(id(RSL_v)),
		 assign(ptr_cast(CrecId, unary(new, postfix(E, bracket(Parms)))))
	       )
	     )
	   C_End_decl(-> PtrDecl)
	   C_Add_function_body(decl(PtrDecl))
	   string_to_id("abort" -> Abort)
	   C_Add_function_body(
	     if(unary(not, name(id(RSL_v))),
	       expr(postfix(name(id(Abort)), bracket(nil))), 
	       nil
	     )
	   )
	   C_Add_function_body(
	     return(postfix(name(id(VarId)), bracket(list(name(id(RSL_v)), nil))))
	   )
	 C_End_func_def(-> Decl)
	 C_Decl_to_string_h(Decl -> Sh) WriteHString(Sh)
	 C_Decl_to_string(Decl -> Scc)	WriteCcString(Scc)


'action' Record_id(cons:ID_OR_OP -> IDENT)

 'rule'	 Record_id(id_op(Id) -> Id)

 'rule'	 Record_id(op_op(Op) -> Id):
	 Op_name(Op -> Ops)
	 string_to_id(Ops -> Id)
	 
'action' C_record_id(cons:ID_OR_OP -> IDENT)

  'rule' C_record_id(id_op(Id) -> CrecId):
	 Mk_record_id(Id -> CrecId)

  'rule' C_record_id(op_op(Op) -> CrecId):
	 Mk_op_record_id(Op -> CrecId)

'condition' C_cons_fname(cons:ID_OR_OP -> C_NAME)

  'rule' C_cons_fname(id_op(Id) -> C_NAME'id(Id))

  'rule' C_cons_fname(op_op(Op) -> ConsFid):
	 Translate_op(Op -> Cop)
	 (|
	   where(Cop -> literal(S))
	   Op_to_cid(Op -> Fid)
	   where(C_NAME'id(Fid) -> ConsFid)
	 ||
	   where(C_NAME'op_fun(Cop) -> ConsFid)
	 |)


'action' Variant_record_destructors(var_id:IDENT, cons_id_or_op:ID_OR_OP, COMPONENTS)

  'rule' Variant_record_destructors(VarId, Cons_id_or_op, Cs):
	 Variant_record_destructors1(1, VarId, Cons_id_or_op, Cs)

'action' Variant_record_destructors1(counter:INT, var_id:IDENT, cons_id_or_op:ID_OR_OP, COMPONENTS)

  'rule' Variant_record_destructors1(N, VarId, Cons_id_or_op, list(component(_, Destr, T, _), Cs)):
	 [|
	   where(Destr -> dest_ref(VI))
	   VI'Ident -> Destr_id_or_op
	   VI'Pos -> P
	   (|
	     where(Destr_id_or_op -> id_op(I))
	   ||
	     where(Destr_id_or_op -> op_op(Op))
	     Op_to_cid(Op -> I)
	   |)
	   C_record_id(Cons_id_or_op -> CrecId)
	   Translate_type(T -> T1)
	   C_Begin_func_def(id(I))
	     C_Add_decl_specifier(fct(inline))
	     C_Add_decl_specifier(type(T1))
	     string_to_id("RSL_v" -> RSL_v)
	     C_Arg_decl_specifier(type(const))
	     C_Arg_decl_specifier(type(ref_to(named_type(VarId))))
	     C_Arg_declarator(dname(id(RSL_v)))
	     --
	     Mk_nth_field_id(N -> MemberId)
	     Mk_ptr_id(-> PtrId)
	     Mk_tag_id(nil -> TagId1)
	     (|
	       where(Cons_id_or_op -> id_op(Id2))
	       Mk_tag_id(ident(Id2) -> TagId2)
	     ||
	       where(Cons_id_or_op -> op_op(Op2))
	       Mk_op_tag_id(Op2 -> TagId2)
	     |)
	     C_Add_function_body(cpp(ifdef("RSL_pre")))
	     id_to_string(I -> SI)
	     Concatenate3("Destructor ", SI, " applied to wrong variant" -> ST)
	     Fail(P, ST -> FS)
	     C_Add_function_body(if(
	       binary(postfix(name(id(RSL_v)), dot(id(TagId1))),
		      neq, name(id(TagId2))),
	       FS, nil))
	     C_Add_function_body(cpp(endif("RSL_pre")))	 
	     C_Add_function_body(
	       return(
		 postfix(
		   bracket(ptr_cast(CrecId, postfix(name(id(RSL_v)), dot(id(PtrId))))),
		   arrow(id(MemberId))
		 )
	       )
	     )
	   C_End_func_def(-> Decl)
	   C_Decl_to_string(Decl -> S)
	   WriteHString(S)
	 |]
	 Variant_record_destructors1(N + 1, VarId, Cons_id_or_op, Cs)

  'rule' Variant_record_destructors1(_, _, _, nil)


'action' Variant_record_reconstructors(var_id:IDENT, cons_id_or_op:ID_OR_OP, COMPONENTS)

  'rule' Variant_record_reconstructors(VarId, Cons_id_or_op, Cs):
	 Variant_record_reconstructors1(1, VarId, Cons_id_or_op, Cs)

'action' Variant_record_reconstructors1(counter:INT, var_id:IDENT, cons_id_or_op:ID_OR_OP, COMPONENTS)

  'rule' Variant_record_reconstructors1(N, VarId, Cons_id_or_op, list(component(_, _, T, Recons), Cs)):
	 [|
	   where(Recons -> recon_ref(VI))
	   VI'Ident -> Recons_id_or_op
	   VI'Pos -> Pos
	   (|
	     C_cons_fname(Recons_id_or_op -> ReconsId)
	     C_Begin_func_def(ReconsId)
	       C_Add_decl_specifier(type(named_type(VarId)))
	       C_Arg_decl_specifier(type(const))
	       Mk_nth_parm_id(0 -> ParmId1)
	       Translate_arg(T -> T1)
	       C_Arg_decl_specifier(type(T1))
	       C_Arg_declarator(dname(id(ParmId1)))
	       --
	       C_Arg_decl_specifier(type(const))
	       C_Arg_decl_specifier(type(ref_to(named_type(VarId))))
	       string_to_id("RSL_v" -> RSL_v)
	       C_Arg_declarator(dname(id(RSL_v)))
	       C_record_id(Cons_id_or_op -> CrecId)
	       Variant_makeup_Nth_parms(VarId, CrecId, N -> Parms)
	       C_cons_fname(Cons_id_or_op -> ConsFid)
	       Mk_ptr_id(-> PtrId)
	       Mk_tag_id(nil -> TagId1)
	       (|
		 where(Cons_id_or_op -> id_op(Id2))
		 Mk_tag_id(ident(Id2) -> TagId2)
	       ||
		 where(Cons_id_or_op -> op_op(Op2))
		 Mk_op_tag_id(Op2 -> TagId2)
	       |)
	       C_Add_function_body(cpp(ifdef("RSL_pre")))
	       C_Name_to_string(ReconsId -> SI)
	       Concatenate3("Reconstructor ", SI, " applied to wrong variant" -> ST)
	       Fail(Pos, ST -> FS)
	       C_Add_function_body(if(
		 binary(postfix(name(id(RSL_v)), dot(id(TagId1))),
			neq, name(id(TagId2))),
		 FS, nil))
	       C_Add_function_body(cpp(endif("RSL_pre")))  
	       C_Add_function_body(return(postfix(name(ConsFid), bracket(Parms))))
	     C_End_func_def(-> Decl)
	     C_Decl_to_string_h(Decl -> Sh) WriteHString(Sh)
	     C_Decl_to_string(Decl -> Scc)  WriteCcString(Scc)
	   ||
	       Puterror(Pos)
	       Putmsg("Cannot translate this reconstructor: ignored")
	       Putnl()
	   |)
	 |]
	 Variant_record_reconstructors1(N + 1, VarId, Cons_id_or_op, Cs)

  'rule' Variant_record_reconstructors1(_, _, _, nil)

'action' Variant_makeup_Nth_parms(var_id:IDENT, crec_id:IDENT, INT -> C_EXPRS)

  'rule' Variant_makeup_Nth_parms(VarId, CrecId, N -> Ps):
	 Variant_makeup_Nth_parms1(VarId, CrecId, 1, N, nil -> Ps)

'action' Variant_makeup_Nth_parms1(var_id:IDENT, crec_id:IDENT, counter:INT, stopper:INT, C_EXPRS -> C_EXPRS)

  'rule' Variant_makeup_Nth_parms1(VarId, CrecId, N, Nth, Ps -> Ps1):
	 C_Class_num_data_members(-> N1)
	 (|
	   le(N, N1)
	   (|
	     eq(N, Nth)
	     Mk_nth_parm_id(0 -> ParmId)
	     where(C_EXPR'name(id(ParmId)) -> P)
	   ||
	     Mk_nth_field_id(N -> MemberId)
	     string_to_id("RSL_v" -> RSL_v)
	     Mk_ptr_id(-> PtrId)
	     where(
	       postfix(
		 bracket(ptr_cast(CrecId, postfix(name(id(RSL_v)), dot(id(PtrId))))),
		 arrow(id(MemberId))
	       ) -> P
	     )
	   |)
	   Append_expr(Ps, P -> Ps2)
	   Variant_makeup_Nth_parms1(VarId, CrecId, N + 1, Nth, Ps2 -> Ps1)
	 ||
	   where(Ps -> Ps1)
	 |)



-- I/O routines for variants

'action' Variant_input_token_decls(VARIANTS, C_DECLS -> C_DECLS)

  'rule' Variant_input_token_decls(Vs, Ds0 -> Ds):
	 Variant_input_token_decls1(1, Vs, Ds0 -> Ds)

'action' Variant_input_token_decls1(counter:INT, VARIANTS, C_DECLS -> C_DECLS)

  'rule' Variant_input_token_decls1(N, list(record(_, Cons, _), Rs), Ds0 -> Ds):
	 (|
	   where(Cons -> con_ref(I))
	   I'Ident -> Cons_id_or_op
	   C_Begin_decl()
	     C_Add_decl_specifier(type(const))
	     string_to_id("RSL_input_token_type" -> RSL_input_token_type)
	     C_Add_decl_specifier(type(named_type(RSL_input_token_type)))
	     (|
	       where(Cons_id_or_op -> id_op(Id))
	       Mk_token_id(Id -> TokId)
	     ||
	       where(Cons_id_or_op -> op_op(Op))
	       Mk_op_token_id(Op -> TokId)
	     |)
	     Int_to_string(N -> NS)
	     string_to_id(NS -> TokNum)
	     string_to_id("Token_StartIndex" -> TSI)
	     where(binary(name(id(TSI)), plus, literal(int(TokNum))) -> TokVal)
	     C_Add_declarator(with_init(dname(id(TokId)), assign(TokVal)))
	   C_End_decl(-> TokDecl)
	   Append_decl(Ds0, TokDecl -> Ds1)
	 ||
	   where(Ds0 -> Ds1)
	 |)
	 Variant_input_token_decls1(N + 1, Rs, Ds1 -> Ds)

  'rule' Variant_input_token_decls1(_, nil, Ds -> Ds)

'action' Mk_token_id(IDENT -> IDENT)

  'rule' Mk_token_id(Id -> Id1):
	 id_to_string(Id -> S)
	 Concatenate3("RSL_", S, "_token" -> S1)
	 string_to_id(S1 -> Id1)

'action' Mk_op_token_id(OP -> IDENT)

  'rule' Mk_op_token_id(Op -> Id):
	 Op_name(Op -> Ops)
	 Concatenate3("RSL_", Ops, "_token" -> Ops1)
	 string_to_id(Ops1 -> Id)

'action' Variant_to_string_routine(IDENT, VARIANTS -> C_DECL)

  'rule' Variant_to_string_routine(VarId, Vs -> D):
	 RSL_ts -> NM
	 C_Begin_func_def(NM)
	   C_Add_decl_specifier(type(string))
	   C_Arg_decl_specifier(type(const))
	   C_Arg_decl_specifier(type(ref_to(named_type(VarId))))
	   string_to_id("RSL_v" -> RSL_v)
	   C_Arg_declarator(dname(id(RSL_v)))
	   Mk_temp_id(nil -> TempId)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(string))
	     C_Add_declarator(dname(id(TempId)))
	   C_End_decl(-> TempVar)
	   C_Add_function_body(decl(TempVar))
	   Variant_memberwise_to_string(TempId, Vs -> S)
	   C_Add_function_body(S)
	   C_Add_function_body(return(name(id(TempId))))
	C_End_func_def(-> D) 
	   
	   
	 
'action' Variant_io_routines(IDENT, VARIANTS -> h:C_DECLS, cc:C_DECLS)

  'rule' Variant_io_routines(VarId, Cs -> Dsh, Dscc):
	 -- operator<<
	 C_Begin_func_def(op_fun(shl))
	   string_to_id("ostream" -> Os)
	   C_Add_decl_specifier(type(ref_to(named_type(Os))))
	   C_Arg_decl_specifier(type(ref_to(named_type(Os))))
	   string_to_id("RSL_os" -> RSL_os)
	   C_Arg_declarator(dname(id(RSL_os)))
	   C_Arg_decl_specifier(type(const))
	   C_Arg_decl_specifier(type(ref_to(named_type(VarId))))
	   string_to_id("RSL_v" -> RSL_v)
	   C_Arg_declarator(dname(id(RSL_v)))
	   --
	   Variant_memberwise_output(Cs -> Sw1)
	   C_Add_function_body(Sw1)
	   C_Add_function_body(return(name(id(RSL_os))))
	 C_End_func_def(-> OutputFunc)
	 Append_decl(nil, OutputFunc -> Dsh0)
	 Append_decl(nil, OutputFunc -> Dscc0)
	 -- RSL_input_token_<Id>
	 Variant_input_token_decls(Cs, Dscc0 -> Dscc1)
	 --
	 id_to_string(VarId -> SVarId)
	 Concatenate("RSL_input_token_", SVarId -> Sfid)
	 string_to_id(Sfid -> Fid)
	 C_Begin_func_def(id(Fid))
	   C_Add_decl_specifier(storage(static))
	   C_Add_decl_specifier(type(void))
	   string_to_id("istream" -> Is)
	   C_Arg_decl_specifier(type(ref_to(named_type(Is))))
	   string_to_id("RSL_is" -> RSL_is)
	   C_Arg_declarator(dname(id(RSL_is)))
	   string_to_id("RSL_input_token_type" -> RSL_input_token_type)
	   C_Arg_decl_specifier(type(ref_to(named_type(RSL_input_token_type))))
	   string_to_id("RSL_token" -> RSL_token)
	   C_Arg_declarator(dname(id(RSL_token)))
	   --
	   C_Begin_decl()
	     C_Add_decl_specifier(type(char))
	     string_to_id("RSL_buf" -> RSL_buf)
	     string_to_id("128" -> BufSize)
	     C_Add_declarator(with_index(dname(id(RSL_buf)), literal(int(BufSize))))
	   C_End_decl(-> BufDecl)
	   C_Add_function_body(decl(BufDecl))
	   string_to_id("RSL_fetch_token" -> RSL_fetch_token)
	   where(C_EXPRS'nil -> Ps0)
	   Append_expr(Ps0, name(id(RSL_is)) -> Ps1)
	   Append_expr(Ps1, name(id(RSL_token)) -> Ps2)
	   Append_expr(Ps2, name(id(RSL_buf)) -> Ps)
	   C_Add_function_body(
	     expr(
	       postfix(
		 name(id(RSL_fetch_token)),
		 bracket(Ps)
	       )
	     )
	   )
	   Variant_memberwise_tokchk(Cs -> Tokchks)
	   string_to_id("RSL_constructor_token" -> RSL_constructor_token)
	   C_Add_function_body(
	     if(
	       binary(
		 name(id(RSL_token)),
		 eq,
		 name(id(RSL_constructor_token))
	       ),
	       compound(Tokchks),
	       nil
	     )
	   )
	 C_End_func_def(-> OutputFunc2)
	 Append_decl(Dscc1, OutputFunc2 -> Dscc2)
	 -- operator>>
	 C_Begin_func_def(op_fun(shr))
	   C_Add_decl_specifier(type(ref_to(named_type(Is))))
	   C_Arg_decl_specifier(type(ref_to(named_type(Is))))
	   C_Arg_declarator(dname(id(RSL_is)))
	   C_Arg_decl_specifier(type(ref_to(named_type(VarId))))
	   C_Arg_declarator(dname(id(RSL_v)))
	   --
	   C_Begin_decl()
	     C_Add_decl_specifier(type(named_type(RSL_input_token_type)))
	     C_Add_declarator(dname(id(RSL_token)))
	   C_End_decl(-> RSL_token_decl)
	   C_Add_function_body(decl(RSL_token_decl))
	   C_Begin_decl()
	     C_Add_decl_specifier(type(named_type(VarId)))
	     string_to_id("RSL_temp" -> RSL_temp)
	     C_Add_declarator(dname(id(RSL_temp)))
	   C_End_decl(-> TempDecl)
	   C_Add_function_body(decl(TempDecl))
	   C_Begin_decl()
	     string_to_id("RSL_class" -> RSL_class)
	     C_Add_decl_specifier(type(ptr_to(named_type(RSL_class))))
	     --string_to_id("RSL_temp" -> RSL_temp)
	     Mk_ptr_id(-> RSL_ptr)
	     string_to_id("0" -> Zero)
	     C_Add_declarator(with_init(dname(id(RSL_ptr)), assign(literal(int(Zero)))))
	   C_End_decl(-> PtrDecl)
	   C_Add_function_body(decl(PtrDecl))
	   Concatenate("RSL_input_token_", SVarId -> TokInputFname)
	   string_to_id(TokInputFname -> TokInputFid)
	   C_Add_function_body(
	     expr(
	       postfix(
		 name(id(TokInputFid)),
		 bracket(list(name(id(RSL_is)), list(name(id(RSL_token)), nil)))
	       )
	     )
	   )
	   --
	   Variant_memberwise_input(VarId, Cs -> Sw2)
	   C_Add_function_body(Sw2)
	   string_to_id("RSL_is.clear" -> ClearFid)
	   string_to_id("ios::badbit" -> BadBit)
	   C_Add_function_body(
	     if(
	       name(id(RSL_is)),
	       expr(
		 binary(
		   name(id(RSL_v)),
		   assign,
		   name(id(RSL_temp))
		 )
	       ),
	       expr(postfix(name(id(ClearFid)), bracket(list(name(id(BadBit)), nil))))
	     )
	   )
	   C_Add_function_body(return(name(id(RSL_is))))
	 C_End_func_def(-> OutputFunc3)
	 Append_decl(Dsh0, OutputFunc3 -> Dsh)
	 Append_decl(Dscc2, OutputFunc3 -> Dscc)

'action' Variant_memberwise_to_string(IDENT, VARIANTS -> C_STATEMENT)

  'rule' Variant_memberwise_to_string(Tid, Vs -> switch(postfix(name(id(RSL_v)), dot(id(RSL_tag))), compound(Ss))):
	 Variant_memberwise_to_string1(Tid, Vs, nil -> Ss)
	 string_to_id("RSL_v" -> RSL_v)
	 Mk_tag_id(nil -> RSL_tag)

'action' Variant_memberwise_to_string1(IDENT, VARIANTS, C_STATEMENTS -> C_STATEMENTS)

  'rule' Variant_memberwise_to_string1(Tid, list(record(_, Cons, Comps), Rs), Ss0 -> Ss):
	 (|
	   where(Cons -> con_ref(I))
	   I'Ident -> Cons_id_or_op
	   (|
	     where(Cons_id_or_op -> id_op(Id))
	     Mk_tag_id(ident(Id) -> TagId)
	     C_id_to_string(Id -> Sid)
	   ||
	     where(Cons_id_or_op -> op_op(Op))
	     Mk_op_tag_id(Op -> TagId)
	     Translate_op(Op -> Cop)
	     C_Op_to_string(Cop -> Sid)
	   |)
	   where(C_EXPR'text_literal(Sid) -> Header)
	   (|
	     eq(Comps, nil)
	     where(Header -> E)
	   ||
	     C_record_id(Cons_id_or_op -> CrecId)
	     Mk_ptr_id(-> RSL_ptr)
	     string_to_id("RSL_v" -> RSL_v)
	     RSL_ts -> NM
	     where(unary(mult,
			 ptr_cast(CrecId,
				  postfix(name(id(RSL_v)),
					  dot(id(RSL_ptr))))) -> Arg)
	     where(binary(Header, plus,
			  postfix(name(NM),
				  bracket(list(Arg, nil)))) -> E)
	   |)
	   Append_statement(Ss0, case(name(id(TagId))) -> Ss1)
	   Append_statement(Ss1, expr(binary(name(id(Tid)), assign, E)) -> Ss2)
	   Append_statement(Ss2, break -> Ss3)
	 ||
	   -- simply ignore (the rest will be managed by 'default')
	   where(Ss0 -> Ss3)
	 |)
	 Variant_memberwise_to_string1(Tid, Rs, Ss3 -> Ss)

  'rule' Variant_memberwise_to_string1(Tid, nil, Ss0 -> Ss)
	 Append_statement(Ss0, default -> Ss1)
	 Append_statement(Ss1, expr(binary(name(id(Tid)), assign, text_literal("Unknown variant value"))) -> Ss2)
	 Append_statement(Ss2, break -> Ss)


'action' Variant_memberwise_output(VARIANTS -> C_STATEMENT)

  'rule' Variant_memberwise_output(Vs -> switch(postfix(name(id(RSL_v)), dot(id(RSL_tag))), compound(Ss))):
	 Variant_memberwise_output1(Vs, nil -> Ss)
	 string_to_id("RSL_v" -> RSL_v)
	 Mk_tag_id(nil -> RSL_tag)

'action' Variant_memberwise_output1(VARIANTS, C_STATEMENTS -> C_STATEMENTS)

  'rule' Variant_memberwise_output1(list(record(_, Cons, Comps), Rs), Ss0 -> Ss):
	 (|
	   where(Cons -> con_ref(I))
	   I'Ident -> Cons_id_or_op
	   (|
	     where(Cons_id_or_op -> id_op(Id))
	     Mk_tag_id(ident(Id) -> TagId)
	     C_id_to_string(Id -> Sid)
	   ||
	     where(Cons_id_or_op -> op_op(Op))
	     Mk_op_tag_id(Op -> TagId)
	     Translate_op(Op -> Cop)
	     C_Op_to_string(Cop -> Sid)
	   |)
	   where(C_EXPR'text_literal(Sid) -> Header)
	   (|
	     eq(Comps, nil)
	     where(Header -> E)
	   ||
	     C_record_id(Cons_id_or_op -> CrecId)
	     Mk_ptr_id(-> RSL_ptr)
	     string_to_id("RSL_v" -> RSL_v)
	     where(binary(Header, shl, unary(mult, ptr_cast(CrecId, postfix(name(id(RSL_v)), dot(id(RSL_ptr)))))) -> E)
	   |)
	   Append_statement(Ss0, case(name(id(TagId))) -> Ss1)
	   string_to_id("RSL_os" -> RSL_os)
	   Append_statement(Ss1, expr(binary(name(id(RSL_os)), shl, E)) -> Ss2)
	   Append_statement(Ss2, break -> Ss3)
	 ||
	   -- simply ignore (the rest will be managed by 'default')
	   where(Ss0 -> Ss3)
	 |)
	 Variant_memberwise_output1(Rs, Ss3 -> Ss)

  'rule' Variant_memberwise_output1(nil, Ss0 -> Ss)
	 Append_statement(Ss0, default -> Ss1)
	 string_to_id("RSL_os" -> RSL_os)
	 Append_statement(Ss1, expr(binary(name(id(RSL_os)), shl, text_literal("Unknown variant value"))) -> Ss2)
	 Append_statement(Ss2, break -> Ss)


'action' Variant_memberwise_tokchk(VARIANTS -> C_STATEMENTS)

  'rule' Variant_memberwise_tokchk(Vs -> Ss):
	 Variant_memberwise_tokchk1(Vs, nil -> Ss)

'action' Variant_memberwise_tokchk1(VARIANTS, C_STATEMENTS -> C_STATEMENTS)

  'rule' Variant_memberwise_tokchk1(list(record(_, Cons, Comps), Rs), Ss0 -> Ss):
	 (|
	   where(Cons -> con_ref(I))
	   I'Ident -> Cons_id_or_op
	   (|
	     where(Cons_id_or_op -> id_op(Id))
	     Mk_token_id(Id -> TokId)
	     C_id_to_string(Id -> Stokval)
	   ||
	     where(Cons_id_or_op -> op_op(Op))
	     Mk_op_token_id(Op -> TokId)
	     Translate_op(Op -> Cop)
	     C_Op_to_string(Cop -> Stokval)
	   |)
	   string_to_id("RSL_streq" -> RSL_streq)
	   string_to_id("RSL_token" -> RSL_token)
	   string_to_id("RSL_buf" -> RSL_buf)
	   where(
	     C_STATEMENT'if(
	       postfix(
		 name(id(RSL_streq)),
		 bracket(
		   list(
		     name(id(RSL_buf)),
		     list(text_literal(Stokval), nil)
		   )
		 )
	       ),
	       compound(
		 list(
		   expr(binary(name(id(RSL_token)), assign, name(id(TokId)))),
		   list(return(nil), nil)
		 )
	       ),
	       nil
	     ) -> S
	   )
	   Append_statement(Ss0, S -> Ss1)
	 ||
	   where(Ss0 -> Ss1)
	 |)
	 Variant_memberwise_tokchk1(Rs, Ss1 -> Ss)

  'rule' Variant_memberwise_tokchk1(nil, Ss0 -> Ss)
	 string_to_id("RSL_token" -> RSL_token)
	 string_to_id("RSL_error_token" -> RSL_eror_token)
	 Append_statement(Ss0, expr(binary(name(id(RSL_token)), assign, name(id(RSL_eror_token)))) -> Ss)


'action' Variant_memberwise_input(var_id:IDENT, VARIANTS -> C_STATEMENT)

  'rule' Variant_memberwise_input(VarId, Vs -> switch(name(id(RSL_token)), compound(Ss))):
	 Variant_memberwise_input1(VarId, Vs, nil -> Ss)
	 string_to_id("RSL_token" -> RSL_token)

'action' Variant_memberwise_input1(IDENT, VARIANTS, C_STATEMENTS -> C_STATEMENTS)

  'rule' Variant_memberwise_input1(VarId, list(record(_, Cons, Comps), Rs), Ss0 -> Ss):
	 (|
	   where(Cons -> con_ref(I))
	   I'Ident -> Cons_id_or_op
	   C_record_id(Cons_id_or_op -> CrecId)
	   (|
	     where(Cons_id_or_op -> id_op(Id))
	     Mk_token_id(Id -> TokId)
	     Mk_tag_id(ident(Id) -> TagId)
	   ||
	     where(Cons_id_or_op -> op_op(Op))
	     Mk_op_token_id(Op -> TokId)
	     Mk_op_tag_id(Op -> TagId)
	   |)
	   Append_statement(Ss0, case(name(id(TokId))) -> Ss1)
	   string_to_id("RSL_temp" -> RSL_temp)
	   (|
	     eq(Comps, nil)
	     Append_statement(Ss1,
	       expr(
		 binary(
		   name(id(RSL_temp)),
		   assign,
		   postfix(name(id(VarId)),
		   bracket(list(name(id(TagId)), nil)))
		 )
	       ) -> Ss4
	     )
	   ||
	     Mk_ptr_id(-> RSL_ptr)
	     string_to_id("RSL_v" -> RSL_v)
	     string_to_id("RSL_is" -> RSL_is)
	     Append_statement(Ss1,
	       expr(binary(name(id(RSL_ptr)), assign, unary(new, name(id(CrecId))))) -> Ss2)
	     Append_statement(Ss2,
	       expr(binary(name(id(RSL_is)), shr, unary(mult, ptr_cast(CrecId, name(id(RSL_ptr)))))) -> Ss3)
	     Append_statement(Ss3,
	       if(name(id(RSL_is)),
		 expr(
		   binary(
		     name(id(RSL_temp)),
		     assign,
		     postfix(name(id(VarId)), bracket(list(ptr_cast(CrecId, name(id(RSL_ptr))), nil)))
		   )
		 ),
		 nil
	       ) -> Ss4
	     )
	   |)
	   Append_statement(Ss4, break -> Ss5)
	 ||
	   -- simply ignore (the rest will be managed by 'default')
	   where(Ss0 -> Ss5)
	 |)
	 Variant_memberwise_input1(VarId, Rs, Ss5 -> Ss)

  'rule' Variant_memberwise_input1(_, nil, Ss0 -> Ss)
	 Append_statement(Ss0, default -> Ss1)
	 string_to_id("RSL_is" -> RSL_is)
	 string_to_id("RSL_is.clear" -> ClearFid)
	 string_to_id("ios::badbit" -> BadBit)
	 Append_statement(Ss1, expr(postfix(name(id(ClearFid)), bracket(list(name(id(BadBit)), nil)))) -> Ss2)
	 Append_statement(Ss2, break -> Ss)


-- record declarations

'action' Translate_record(Type_id)

  'rule' Translate_record(I):
	 I'Pos -> Pos
	 I'Qualifier -> Q
	 (|
	   where(Q -> list(_, _)) -- record defined in object
	   Last_object(Q -> OI)
	   OI'Env -> CE
	   Get_env_top_values(CE -> VE)
	 || 
	   Get_current_top_values(-> VE)
	 |)
	 Select_id_by_pos(Pos, VE -> value_id(I1)) -- look up Value_id for constructor (mk_...)
	 I1'Type -> fun(T1, _, _)
	 (|
	   Type_is_product(T1 -> Ts)
	 ||
	   where(PRODUCT_TYPE'list(T1, nil) -> Ts)
	 |)
	 I'Ident -> Ident
	 I'Type -> sort(record(Cs))
	 Length_pr(Ts -> N)
	 Translate_product_type(Ts -> Ts1)
	 (|
	   Max_prod_length(-> Max)
	   le(N, Max)
	   C_id_to_string(Ident -> Sid)
	   Concatenate3("RSL_mk_", Sid, "_fun" -> Sfun)
	   string_to_id(Sfun -> RSL_mk_X_fun)
	   C_Begin_func_def(id(RSL_mk_X_fun))
	     C_Add_decl_specifier(type(ptr_to(char)))
	     Make_mk_name(Sid -> Mk_X)
	     C_Add_function_body(return(text_literal(Mk_X)))
	   C_End_func_def(-> Mk_fun)
	   C_Decl_to_string(Mk_fun -> FunS)		WriteHString(FunS)
	   Conc_c_types(Ts1, list(named_type(RSL_mk_X_fun), nil) -> Ts2)
	   C_Begin_decl()
	     C_Add_decl_specifier(typedef)
	     Mk_Product_id(N -> PId)
	     C_Add_decl_specifier(type(template(PId, Ts2)))
	     C_Add_declarator(dname(id(Ident)))
	   C_End_decl(-> D)
	   C_Decl_to_string(D -> Sp)	 WriteHString(Sp)
	   Set_num_data_members(N)
	   Record_constructor(Pos, Ident, Ts)
	   Record_destructors(Ident, Cs)
	   Record_reconstructors(Ident, Cs)
	 ||
	   C_Begin_decl()
	     C_Begin_class_def(struct, id(Ident))
	       Components_to_fields(Cs)
	       Add_basic_member_functions(Pos, Ident, Ts, true)
	     C_End_class_def(-> C)
	     C_Add_decl_specifier(type(C))
	   C_End_decl(-> D)
	   C_Decl_to_string_h(D -> Sh)	 WriteHString(Sh)
	   C_Decl_to_string_cc(D -> Scc) WriteCcString(Scc)
	   Record_constructor(Pos, Ident, Ts)
	   Record_destructors(Ident, Cs)
	   Record_reconstructors(Ident, Cs)
	   -- RSL_to_string function
	   id_to_string(Ident -> ST)
	   Make_mk_name(ST -> Mkid)
	   Record_to_string(Ident, "", Mkid, N, Ts1 -> D0)
	   C_Decl_to_string(D0 -> Sh0)	 WriteHString(Sh0)
	   [|
	     -- Visual C++ compiler needs RSL_to_string
	     -- functions defined in namespaces to also
	     -- be defined at the top level, or it cannot
	     -- find occurrences in templates
	     VisualCPP()
             Namespaces_to_idents(-> Ids)
             ne(Ids, nil)
             Define_to_string_at_top(Ident, Ids)
	   |]
	   [|
	     IfIoWanted()
	     Record_io_routines(Pos, Ident, Ts, 1 -> Dsh, Dscc)
	     C_Decls_to_string_h(Dsh -> Sh1)	WriteHString(Sh1)
	     C_Decls_to_string(Dscc -> Scc1)	WriteCcString(Scc1)
	     EndIfIoWanted()
	   |]
	 |)

'action' Last_object(Object_ids -> Object_id)

  'rule' Last_object(list(I, nil) -> I):

  'rule' Last_object(list(_, Is) -> I):
	 Last_object(Is -> I)

-- NOTE: supposed to be called inside of C_Begin/End_class_def() pair

'action' Components_to_fields(COMPONENTS) -- very similar to 'Add_fields'

  'rule' Components_to_fields(Cs):
	 Components_to_fields1(1, Cs)

'action' Components_to_fields1(counter:INT, COMPONENTS)

  'rule' Components_to_fields1(N, list(C, Cs)):
	 where(C -> component(_, _, T, _))
	 C_Begin_decl()
	   Translate_type(T -> T1)
	   C_Add_decl_specifier(type(T1))
	     Mk_nth_field_id(N -> I)
	     C_Add_declarator(dname(id(I)))
	 C_End_decl(-> Decl)
	 C_Add_member(member(Decl))
	 Components_to_fields1(N + 1, Cs)

  'rule' Components_to_fields1(_, nil)

'action' Record_constructor(POS, IDENT, PRODUCT_TYPE)

  'rule' Record_constructor(P, Id, Ts):
	 id_to_string(Id -> S1)
	 Make_mk_name(S1 -> S2)
	 string_to_id(S2 -> I)
	 C_Begin_func_def(id(I))
	   C_Add_decl_specifier(type(named_type(Id)))
	   Makeup_arglist(Ts)
	   Makeup_parms(P, Ts -> Parms, Cond, Ss)
	   [|
             ne(Cond, nil)
	     (|
	       where(Ts -> list(T,nil))
	     ||
	       where(TYPE_EXPR'product(Ts) -> T)
	     |)
	     PosAsString(P -> PS)
	     Parms_to_output_string(Parms, Ts -> SB)
	     GetF2String("%s Arguments of %s(", PS, S2 -> ST1)
	     Append_statement(Ss,
	       cond_warn(Cond,
	                 binary(text_literal(ST1),
			 plus,
			 binary(SB, plus, text_literal(") not in subtypes"))))
			 -> Ss1)
	     where(cpp(ifdef("RSL_pre")) -> S0)
	     where(cpp(endif("RSL_pre")) -> S01)
	     Append_statement(C_STATEMENTS'list(S0, Ss1), S01 -> Ss2)
	     C_Set_function_body(Ss2)
	   |]
	   C_Add_function_body(return(postfix(name(id(Id)), bracket(Parms))))
	 C_End_func_def(-> Decl)
	 C_Decl_to_string_h(Decl -> Sh)    WriteHString(Sh)
	 C_Decl_to_string(Decl -> Scc)     WriteCcString(Scc)

'action' Makeup_parms(POS, PRODUCT_TYPE -> C_EXPRS, C_EXPR, C_STATEMENTS)	
-- make up actual parameter list
-- and conditions that parameters are in subtypes

  'rule' Makeup_parms(P, Prod -> Ts, Cond, Ss):
	 Makeup_parms1(P, 1, Prod -> Ts, Cond, Ss)

'action' Makeup_parms1(POS, counter:INT, PRODUCT_TYPE -> C_EXPRS, C_EXPR, C_STATEMENTS)

  'rule' Makeup_parms1(_, _, nil -> nil, nil, nil):

  'rule' Makeup_parms1(P, N, list(T, Ts) -> list(name(id(Id)), Ps), Cond, Ss):
	 Mk_nth_parm_id(N -> Id)
	 New_value_id(P, id_op(Id) -> I)
	 Maxtype(T -> Tm)
	 I'Type <- Tm
	 Isin_subtype(val_occ(P, I, nil), T -> Pred)
	 Simplify(Pred -> Pred1)
	 (|
           (| eq(Pred1, no_val) || 
	      where(Pred1 -> literal_expr(_,bool_true)) |)
	   where(C_EXPR'nil -> Cond1)
	   where(C_STATEMENTS'nil -> Ss1)
	 ||
	   Translate_value(bool, Pred1 -> Cond1, Ss1)
	 |)
	 Makeup_parms1(P, N + 1, Ts -> Ps, Cond2, Ss2)
	 Conjoin(Cond1, Cond2 -> Cond)
	 Concatenate_statements(Ss1, Ss2 -> Ss)


'action' Append_expr(C_EXPRS, C_EXPR -> C_EXPRS)

  'rule' Append_expr(list(E, Es), E1 -> list(E, Es1)):
	 (|
	   eq(E, E1)
	   where(Es -> Es1)
	 ||
	   Append_expr(Es, E1 -> Es1)
	 |)

  'rule' Append_expr(nil, E -> list(E, nil))

'action' Record_destructors(IDENT, COMPONENTS)

  'rule' Record_destructors(Id, Cs):
	 Record_destructors1(1, Id, Cs)

'action' Record_destructors1(counter:INT, IDENT, COMPONENTS)

  'rule' Record_destructors1(N, Id, list(component(_, Destr, T, _), Cs)):
	 [|
	   where(Destr -> dest_ref(VI))
	   VI'Ident -> Id_or_op
	   (|
	     where(Id_or_op -> id_op(I))
	     where(C_NAME'id(I) -> DN)
	   ||
	     where(Id_or_op -> op_op(Op))
	     Translate_op(Op -> Op1)
	     where(op_fun(Op1) -> DN)
	   |)
	   Translate_type(T -> T1)
	   C_Begin_func_def(DN)
	     C_Add_decl_specifier(fct(inline))
	     C_Add_decl_specifier(type(T1))
	     string_to_id("RSL_v" -> RSL_v)
	     C_Arg_decl_specifier(type(const))
	     C_Arg_decl_specifier(type(ref_to(named_type(Id))))
	     C_Arg_declarator(dname(id(RSL_v)))
	     --
	     Mk_nth_field_id(N -> MemberId)
	     C_Add_function_body(return(postfix(name(id(RSL_v)), dot(id(MemberId)))))
	   C_End_func_def(-> Decl)
	   C_Decl_to_string(Decl -> S)
	   WriteHString(S)
	 |]
	 Record_destructors1(N + 1, Id, Cs)

  'rule' Record_destructors1(_, _, nil)

'action' Record_reconstructors(IDENT, COMPONENTS)

  'rule' Record_reconstructors(Id, Cs):
	 Record_reconstructors1(1, Id, Cs)

'action' Record_reconstructors1(counter:INT, IDENT, COMPONENTS)

  'rule' Record_reconstructors1(N, Id, list(component(P, _, T, Recons), Cs)):
	 [|
	   where(Recons -> recon_ref(VI))
	   VI'Ident -> Id_or_op
	   (|
	     where(Id_or_op -> id_op(I))
	     where(C_NAME'id(I) -> RN)
	   ||
	     where(Id_or_op -> op_op(Op))
	     Translate_op(Op -> Op1)
	     where(op_fun(Op1) -> RN)
	   |)
	   C_Begin_func_def(RN)
	     C_Add_decl_specifier(type(named_type(Id)))
	     C_Arg_decl_specifier(type(const))
	     Mk_nth_parm_id(0 -> ParmId1)
	     New_value_id(P, id_op(ParmId1) -> I)
	     Maxtype(T -> Tm)
	     I'Type <- Tm
	     Isin_subtype(val_occ(P, I, nil), T -> Pred)
	     Simplify(Pred -> Pred1)
	     (|
	       (| eq(Pred1, no_val) || 
		  where(Pred1 -> literal_expr(_,bool_true)) |)
	       where(C_EXPR'nil -> Cond)
	       where(C_STATEMENTS'nil -> Ss)
	     ||
	       Translate_value(bool, Pred1 -> Cond, Ss)
	     |)
	     [|
	       ne(Cond, nil)
	       PosAsString(P -> PS)
	       Parm_to_output_string(name(id(ParmId1)), T -> SB)
	       GetFString("%s First parameter ", PS -> ST1)
	       Id_or_op_to_string(Id_or_op -> IdS)
	       GetFString(" of reconstructor %s not in subtype", IdS -> ST2)
	       Append_statement(Ss,
		 cond_warn(Cond,
			   binary(text_literal(ST1),
			   plus,
			   binary(SB, plus, text_literal(ST2))))
			     -> Ss1)
	       where(cpp(ifdef("RSL_pre")) -> S0)
	       where(cpp(endif("RSL_pre")) -> S01)
	       Append_statement(C_STATEMENTS'list(S0, Ss1), S01 -> Ss2)
	       C_Set_function_body(Ss2)
	     |]
	     Translate_arg(T -> T1)
	     C_Arg_decl_specifier(type(T1))
	     C_Arg_declarator(dname(id(ParmId1)))
	     --
	     C_Arg_decl_specifier(type(const))
	     C_Arg_decl_specifier(type(ref_to(named_type(Id))))
	     string_to_id("RSL_v" -> RSL_v)
	     C_Arg_declarator(dname(id(RSL_v)))
	     Makeup_Nth_parms(N -> Parms)
	     C_Add_function_body(return(postfix(name(id(Id)), bracket(Parms))))
	   C_End_func_def(-> Decl)
	   C_Decl_to_string_h(Decl -> Sh) WriteHString(Sh)
	   C_Decl_to_string(Decl -> Scc)  WriteCcString(Scc)
	 |]
	 Record_reconstructors1(N + 1, Id, Cs)

  'rule' Record_reconstructors1(_, _, nil)

'action' Makeup_Nth_parms(INT -> C_EXPRS)

  'rule' Makeup_Nth_parms(N -> Ps):
	 Makeup_Nth_parms1(1, N, nil -> Ps)

'action' Makeup_Nth_parms1(counter:INT, stopper:INT, C_EXPRS -> C_EXPRS)

  'rule' Makeup_Nth_parms1(N, Nth, Ps -> Ps1):
	 C_Class_num_data_members(-> N1)
	 (|
	   le(N, N1)
	   (|
	     eq(N, Nth)
	     Mk_nth_parm_id(0 -> ParmId)
	     where(C_EXPR'name(id(ParmId)) -> P)
	   ||
	     Mk_nth_field_id(N -> MemberId)
	     string_to_id("RSL_v" -> RSL_v)
	     where(postfix(name(id(RSL_v)), dot(id(MemberId))) -> P)
	   |)
	   Append_expr(Ps, P -> Ps2)
	   Makeup_Nth_parms1(N + 1, Nth, Ps2 -> Ps1)
	 ||
	   where(Ps -> Ps1)
	 |)

'action' Add_fields(PRODUCT_TYPE)

  'rule' Add_fields(Ts):
	 Add_fields1(1, Ts)

'action' Add_fields1(counter:INT, PRODUCT_TYPE)

  'rule' Add_fields1(N, list(T, Ts)):
	 C_Begin_decl()
	   Translate_type(T -> T1)
	   C_Add_decl_specifier(type(T1))
	     Mk_nth_field_id(N -> I)
	     C_Add_declarator(dname(id(I)))
	 C_End_decl(-> Decl)
	 C_Add_member(member(Decl))
	 Add_fields1(N + 1, Ts)

  'rule' Add_fields1(_, nil)

-- NOTE: supposed to be called inside of C_Begin/End_class_def() pair

'action' Add_basic_member_functions(POS, IDENT, PRODUCT_TYPE, copy_constructor:BOOL)

  'rule' Add_basic_member_functions(Pos, Id, Ts, Copy):
	 -- default constructor
	 C_Begin_func_def(id(Id))
	   C_Add_decl_specifier(fct(inline))
	   C_Add_function_body(nil)
	 C_End_func_def(-> DefaultConstructor)
	 C_Add_member(member(DefaultConstructor))
	 -- copy constructor
	 string_to_id("RSL_v" -> RSL_v)
	 [|
	   eq(Copy, true)
	   C_Begin_func_def(id(Id))
	     C_Arg_decl_specifier(type(const))
	     C_Arg_decl_specifier(type(ref_to(named_type(Id))))
	     --string_to_id("RSL_v" -> RSL_v)
	     C_Arg_declarator(dname(id(RSL_v)))
	     Bitwise_assignment()
	   C_End_func_def(-> CopyConstructor)
	   C_Add_member(member(CopyConstructor))
	 |]
	 -- component constructor
	 C_Begin_func_def(id(Id))
	   (|
	     eq(Copy, false)
	     where(Ts -> list(T, nil))
	     Type_is_product(T -> Ts1)
	     -- have variant V with component single T
	     -- where T expands to product Ts1
	     Makeup_arglist(Ts1)
	     Length_pr(Ts1 -> N1)
	     Set_num_data_members(N1)
	     Makeup_parms(Pos, Ts1 -> Parms, Cond, Ss)
	     -- deal with Cond TODO
	     Mk_nth_field_id(1 -> MemberId)
	     Universal_type_id(T -> Uid)
	     where(postfix(name(id(Uid)), bracket(Parms)) -> E)
	     C_Add_member_initializer(init(id(MemberId), list(E, nil)))
	   ||
	     Makeup_arglist(Ts)
	     Makeup_member_initializers()
	   |)
	   C_Add_function_body(nil)
	 C_End_func_def(-> ComponentConstructor)
	 C_Add_member(member(ComponentConstructor))
	 -- operator=
	 [|
	   eq(Copy, true)
	   C_Begin_func_def(op_fun(assign))
	     C_Add_decl_specifier(type(named_type(Id)))
	     C_Arg_decl_specifier(type(const))
	     C_Arg_decl_specifier(type(ref_to(named_type(Id))))
	     --string_to_id("RSL_v" -> RSL_v)
	     C_Arg_declarator(dname(id(RSL_v)))
	     Bitwise_assignment()
	     C_Add_function_body(return(unary(mult, this)))
	   C_End_func_def(-> AssignOpFunc)
	   C_Add_member(member(AssignOpFunc))
	 |]
	 -- operator==
	 C_Begin_func_def(op_fun(eq))
	   C_Add_cv_qualifier(const)
	   C_Add_decl_specifier(type(bool))
	   C_Arg_decl_specifier(type(const))
	   C_Arg_decl_specifier(type(ref_to(named_type(Id))))
	   --string_to_id("RSL_v" -> RSL_v)
	   C_Arg_declarator(dname(id(RSL_v)))
	   Bitwise_compare()
	 C_End_func_def(-> Equality)
	 C_Add_member(member(Equality))
	 -- operator!=
	 C_Begin_func_def(op_fun(neq))
	   C_Add_decl_specifier(fct(inline))
	   C_Add_cv_qualifier(const)
	   C_Add_decl_specifier(type(bool))
	   C_Arg_decl_specifier(type(const))
	   C_Arg_decl_specifier(type(ref_to(named_type(Id))))
	   --string_to_id("RSL_v" -> RSL_v)
	   C_Arg_declarator(dname(id(RSL_v)))
	   C_Add_function_body(return(unary(not,
		postfix(name(op_fun(eq)), bracket(list(name(id(RSL_v)), nil))))))
	 C_End_func_def(-> Unequality)
	 C_Add_member(member(Unequality))

'action' Add_prod_member_functions(POS, IDENT, IDENT, C_TYPE_SPECIFIERS, PRODUCT_TYPE, INT)

  'rule' Add_prod_member_functions(Pos, Id, PId, CTs, Ts, N):
	 -- default constructor
	 C_Begin_func_def(id(Id))
	   C_Add_decl_specifier(fct(inline))
	   C_Add_function_body(nil)
	 C_End_func_def(-> DefaultConstructor)
	 C_Add_member(member(DefaultConstructor))
	 -- component constructor
	 -- if the variant V has component type T,
	 -- and T is defined as a product T1 >< T2
	 -- then the constructor must be of type T1 >< T2 -> V
	 C_Begin_func_def(id(Id))
	   C_Add_decl_specifier(fct(inline))
	   (|
	     where(Ts -> list(T, nil))
	     Type_is_product(T -> Ts2)
	   ||
	     where(Ts -> Ts2)
	     where(1 -> N2)
	   |)
	   Length_pr(Ts2 -> N2)
	   Makeup_arglist(Ts2)
	   string_to_id("RSL_class" -> CId)
	   C_Add_member_initializer(init(id(CId),nil))
	   Set_num_data_members(N2)
	   Makeup_parms(Pos, Ts2 -> Parms, Cond, Ss)
	   -- deal with Cond TODO
	   (|
	     eq(N2,N)
	     C_Add_member_initializer(init(template_member(PId, CTs, id(PId)), Parms))
	   ||
	     Translate_product_type(Ts2 -> CTs2)
	     string_to_id("RSL_constructor_fun" -> CCF)
	     Conc_c_types(CTs2, list(named_type(CCF), nil) -> CTs3)
	     Mk_Product_id(N2 -> PId2)
	     where(postfix(name(template_member(PId2, CTs3, id(PId2))), bracket(Parms)) -> Parm2)
	     C_Add_member_initializer(init(template_member(PId, CTs, id(PId)), list(Parm2,nil)))
	   |)
	   C_Add_function_body(nil)
	 C_End_func_def(-> ComponentConstructor)
	 C_Add_member(member(ComponentConstructor))
	 

'action' Makeup_arglist(PRODUCT_TYPE)

  'rule' Makeup_arglist(Ts):
	 Makeup_arglist1(1, Ts)

'action' Makeup_arglist1(counter:INT, PRODUCT_TYPE)

  'rule' Makeup_arglist1(N, list(T, Ts)):
	 C_Arg_decl_specifier(type(const))
	 Mk_nth_parm_id(N -> I)
	 Translate_arg(T -> T1)
	 C_Arg_decl_specifier(type(T1))
	 C_Arg_declarator(dname(id(I)))
	 Makeup_arglist1(N + 1, Ts)

  'rule' Makeup_arglist1(_, nil)

'action' Makeup_member_initializers()

  'rule' Makeup_member_initializers():
	 Makeup_member_initializers1(1)

'action' Makeup_member_initializers1(counter:INT)

  'rule' Makeup_member_initializers1(N):
	 C_Class_num_data_members(-> N1)
	 [|
	   le(N, N1)
	   Mk_nth_field_id(N -> MemberId)
	   Mk_nth_parm_id(N -> ParmId)
	   C_Add_member_initializer(init(id(MemberId), list(name(id(ParmId)), nil)))
	   Makeup_member_initializers1(N + 1)
	 |]

'action' Bitwise_assignment()

  'rule' Bitwise_assignment():
	 Bitwise_assignment1(1)

'action' Bitwise_assignment1(counter:INT)

  'rule' Bitwise_assignment1(N):
	 C_Class_num_data_members(-> N1)
	 [|
	   le(N, N1)
	   Mk_nth_field_id(N -> MemberId)
	   string_to_id("RSL_v" -> RSL_v)
	   C_Add_function_body(
	     expr(
	       binary(
		 name(id(MemberId)),
		 assign,
		 pm(name(id(RSL_v)), member, name(id(MemberId)))
	       )
	     )
	   )
	   Bitwise_assignment1(N + 1)
	 |]
	   
'action' Bitwise_compare()

  'rule' Bitwise_compare():
	 Bitwise_compare1(1 -> Expr)
	 C_Add_function_body(return(Expr))

'action' Bitwise_compare1(counter:INT -> C_EXPR)

  'rule' Bitwise_compare1(N -> Expr):
	 C_Class_num_data_members(-> N1)
	 (|
	   le(N, N1)
	   Mk_nth_field_id(N -> MemberId)
	   string_to_id("RSL_v" -> RSL_v)
	   where(binary(name(id(MemberId)), eq, pm(name(id(RSL_v)),
		member, name(id(MemberId)))) -> Expr1)
	   Bitwise_compare1(N + 1 -> Expr2)
	   Conjoin(Expr1, Expr2 -> Expr)
	 ||
	   where(C_EXPR'nil -> Expr)
	 |)

'action' Record_io_routines(POS, struct_id:IDENT, member_types:PRODUCT_TYPE, kind:INT -> h:C_DECLS, cc:C_DECLS)
-- Kind = 0 : product
--	  1 : simple record
--	  2 : variant record
--	  3 : variant record with single type that is a product

  'rule' Record_io_routines(Pos, Id, Ts, Kind -> Dsh, Dscc):
	 -- operator<<
	 C_Begin_func_def(op_fun(shl))
	   [|
	     eq(Kind, 0)
	     C_Add_decl_specifier(fct(inline))
	   |]
	   string_to_id("ostream" -> Os)
	   C_Add_decl_specifier(type(ref_to(named_type(Os))))
	   C_Arg_decl_specifier(type(ref_to(named_type(Os))))
	   string_to_id("RSL_os" -> RSL_os)
	   C_Arg_declarator(dname(id(RSL_os)))
	   C_Arg_decl_specifier(type(const))
	   C_Arg_decl_specifier(type(ref_to(named_type(Id))))
	   string_to_id("RSL_v" -> RSL_v)
	   C_Arg_declarator(dname(id(RSL_v)))
	   --
	   Memberwise_output(Id, Kind)
	   C_Add_function_body(return(name(id(RSL_os))))
	 C_End_func_def(-> OutputFunc)
	 Append_decl(nil, OutputFunc -> Dsh0)
	 Append_decl(nil, OutputFunc -> Dscc0)
	 -- RSL_input_token_<Id>
	 string_to_id("RSL_input_token_type" -> RSL_input_token_type)
	 (|
	   eq(Kind, 1)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(const))
	     C_Add_decl_specifier(type(named_type(RSL_input_token_type)))
	     id_to_string(Id -> Sid)
	     Concatenate3("RSL_mk_", Sid, "_token" -> Stok)
	     string_to_id(Stok -> RSL_mk_X_token)
	     string_to_id("Token_StartIndex" -> Tsi)
	     string_to_id("1" -> One)
	     C_Add_declarator(
	       with_init(
		 dname(id(RSL_mk_X_token)),
		 assign(binary(name(id(Tsi)), plus, literal(int(One))))
	       )
	     )
	   C_End_decl(-> TokenConst)
	   Append_decl(Dscc0, TokenConst  -> Dscc1)
	 ||
	   -- non-record (probably product)
	   where(Dscc0 -> Dscc1)
	 |)
	 id_to_string(Id -> Sid)
	 Concatenate("RSL_input_token_", Sid -> Sfid)
	 string_to_id(Sfid -> Fid)
	 C_Begin_func_def(id(Fid))
	   (|
	     eq(Kind, 0)
	     C_Add_decl_specifier(fct(inline))
	   ||
	     C_Add_decl_specifier(storage(static))
	   |)
	   C_Add_decl_specifier(type(void))
	   string_to_id("istream" -> Is)
	   C_Arg_decl_specifier(type(ref_to(named_type(Is))))
	   string_to_id("RSL_is" -> RSL_is)
	   C_Arg_declarator(dname(id(RSL_is)))
	   C_Arg_decl_specifier(type(ref_to(named_type(RSL_input_token_type))))
	   string_to_id("RSL_token" -> RSL_token)
	   C_Arg_declarator(dname(id(RSL_token)))
	   --
	   C_Begin_decl()
	     C_Add_decl_specifier(type(char))
	     string_to_id("RSL_buf" -> RSL_buf)
	     string_to_id("128" -> BufSize)
	     C_Add_declarator(with_index(dname(id(RSL_buf)), literal(int(BufSize))))
	   C_End_decl(-> BufDecl)
	   C_Add_function_body(decl(BufDecl))
	   string_to_id("RSL_fetch_token" -> RSL_fetch_token)
	   where(C_EXPRS'nil -> Ps0)
	   Append_expr(Ps0, name(id(RSL_is)) -> Ps1)
	   Append_expr(Ps1, name(id(RSL_token)) -> Ps2)
	   Append_expr(Ps2, name(id(RSL_buf)) -> Ps)
	   C_Add_function_body(
	     expr(
	       postfix(
		 name(id(RSL_fetch_token)),
		 bracket(Ps)
	       )
	     )
	   )
	   string_to_id("RSL_constructor_token" -> RSL_constructor_token)
	   string_to_id("RSL_error_token" -> RSL_error_token)
	   where(C_STATEMENTS'nil -> Ss0)
	   (|
	     eq(Kind, 1)
	     where(C_STATEMENTS'nil -> Ss00)
	     C_id_to_string(Id -> Sid1)
	     Concatenate3("RSL_mk_", Sid1, "_token" -> Stok)
	     string_to_id(Stok -> RSL_mk_X_token)
	     Append_statement(Ss00, expr(binary(name(id(RSL_token)), assign, name(id(RSL_mk_X_token)))) -> Ss01)
	     Append_statement(Ss01, return(nil) -> Ss02)
	     string_to_id("RSL_streq" -> RSL_streq)
	     where(C_EXPRS'nil -> Es0)
	     Append_expr(Es0, name(id(RSL_buf)) -> Es1)
	     Concatenate("mk_", Sid1 -> Smk_X)
	     Append_expr(Es1, text_literal(Smk_X) -> Es)
	     where(C_STATEMENT'if(postfix(name(id(RSL_streq)), bracket(Es)), compound(Ss02), nil) -> S1)
	     Append_statement(Ss0, S1 -> Ss1)
	   ||
	     where(Ss0 -> Ss1)
	   |)
	   Append_statement(Ss1, expr(binary(name(id(RSL_token)), assign, name(id(RSL_error_token)))) -> Ss)
	   C_Add_function_body(
	     if(
	       binary(
		 name(id(RSL_token)),
		 eq,
		 name(id(RSL_constructor_token))
	       ),
	       compound(Ss),
	       nil
	     )
	   )
	 C_End_func_def(-> OutputFunc2)
	 Append_decl(Dsh0, OutputFunc2 -> Dsh2)
	 Append_decl(Dscc1, OutputFunc2 -> Dscc2)
	 -- operator>>
	 C_Begin_func_def(op_fun(shr))
	   [|
	     eq(Kind, 0)
	     C_Add_decl_specifier(fct(inline))
	   |]
	   C_Add_decl_specifier(type(ref_to(named_type(Is))))
	   C_Arg_decl_specifier(type(ref_to(named_type(Is))))
	   C_Arg_declarator(dname(id(RSL_is)))
	   C_Arg_decl_specifier(type(ref_to(named_type(Id))))
	   C_Arg_declarator(dname(id(RSL_v)))
	   --
	   C_Begin_decl()
	     C_Add_decl_specifier(type(named_type(RSL_input_token_type)))
	     C_Add_declarator(dname(id(RSL_token)))
	   C_End_decl(-> RSL_token_decl)
	   C_Add_function_body(decl(RSL_token_decl))
	   Memberwise_input(Id, Ts, Fid, Kind)
	   Makeup_parms(Pos, Ts -> Parms, Cond, _)
	   -- deal with Cond TODO
	   C_Add_function_body(
	     expr(
	       binary(
		 name(id(RSL_v)),
		 assign,
		 postfix(
		   name(id(Id)),
		   bracket(Parms)
		 )
	       )
	     )
	   )
	   C_Add_function_body(return(name(id(RSL_is))))
	 C_End_func_def(-> OutputFunc3)
	 Append_decl(Dsh2, OutputFunc3 -> Dsh)
	 Append_decl(Dscc2, OutputFunc3 -> Dscc)

'action' Memberwise_output(IDENT, kind:INT)

  'rule' Memberwise_output(Id, Kind):
	 Memberwise_output1(Id, Kind, 1)

'action' Memberwise_output1(struct_id:IDENT, kind:INT, counter:INT)

  'rule' Memberwise_output1(Id, Kind, N):
	 C_Class_num_data_members(-> N1)
	 [|
	   le(N, N1)
	   string_to_id("RSL_os" -> RSL_os)
	   [| -- opening bracket
	     eq(N, 1)
	     (|
	       eq(Kind, 1)
	       C_id_to_string(Id -> Sid)
	       Concatenate3("mk_", Sid, "(" -> S)
	     ||
	       where("(" -> S)
	     |)
	     C_Add_function_body(
	       expr(
		 binary(
		   name(id(RSL_os)),
		   shl,
		   text_literal(S)
		 )
	       )
	     )
	   |]
	   Mk_nth_field_id(N -> MemberId)
	   (|
	     eq(Kind, 3)
	     string_to_id("RSL_v.RSL_f1" -> RSL_v)
	   ||
	     string_to_id("RSL_v" -> RSL_v)
	   |)
	   where(pm(name(id(RSL_v)), member, name(id(MemberId))) -> Field)
	   (|
	     gt(N, 1) -- intervening comma
	     where(binary(text_literal(","), shl, Field) -> Data)
	   ||
	     where(Field -> Data)
	   |)
	   C_Add_function_body(
	     expr(
	       binary(
		 name(id(RSL_os)),
		 shl,
		 Data
	       )
	     )
	   )
	   Memberwise_output1(Id, Kind, N + 1)
	   [| -- closing bracket
	     eq(N, N1)
	     C_Add_function_body(
	       expr(
		 binary(
		   name(id(RSL_os)),
		   shl,
		   text_literal(")")
		 )
	       )
	     )
	   |]
	 |]
	   
'action' Memberwise_input(struct_id:IDENT, PRODUCT_TYPE, input_proc:IDENT, kind:INT)

  'rule' Memberwise_input(Id, Ts, Fid, Prod):
	 Memberwise_input1(Id, Ts, Fid, Prod, 1)

'action' Memberwise_input1(struct_id:IDENT, PRODUCT_TYPE, input_proc:IDENT, kind:INT, counter:INT)

  'rule' Memberwise_input1(Id, list(T, Ts), Fid, Kind, N):
	 C_Class_num_data_members(-> N1)
	 [|
	   le(N, N1)
	   [| -- opening bracket
	     eq(N, 1)
	     [|
	       eq(Kind, 1)
	       C_id_to_string(Id -> Sid)
	       Concatenate3("RSL_mk_", Sid, "_token" -> Stok)
	       Memberwise_input_helper(Sid, T, Fid, Stok, N)
	     |]
	     Memberwise_input_helper("", T, Fid, "RSL_lpar_token", N)
	   |]
	   [| -- intervening comma
	     gt(N, 1)
	     Memberwise_input_helper("", T, Fid, "RSL_comma_token", N)
	   |]
	   Memberwise_input_helper("", T, Fid, "", N) -- member input
	   Memberwise_input1(Id, Ts, Fid, Kind, N + 1)
	   [| -- closing bracket
	     eq(N, N1)
	     Memberwise_input_helper("", T, Fid, "RSL_rpar_token", N)
	   |]
	 |]

  'rule' Memberwise_input1(_, nil, _, _, _):

'action' Memberwise_input_helper(struct_id:STRING, input_type:TYPE_EXPR, input_proc:IDENT, token_name:STRING, INT)

  'rule' Memberwise_input_helper(Sid, T, Fid, Stok, N):
	 string_to_id("RSL_is" -> RSL_is)
	 string_to_id("RSL_token" -> RSL_token)
	 where(C_EXPRS'nil -> Ps0)
	 Append_expr(Ps0, name(id(RSL_is)) -> Ps1)
	 Append_expr(Ps1, name(id(RSL_token)) -> Parms)
	 (|
	   eq(Stok, "")
	   Mk_nth_parm_id(N -> Temp)
	   Translate_type(T -> T1)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(T1))
	     C_Add_declarator(dname(id(Temp)))
	   C_End_decl(-> TempDecl)
	   C_Add_function_body(decl(TempDecl))
	   C_Add_function_body(expr(binary(name(id(RSL_is)), shr, name(id(Temp)))))
	 ||
	   C_Add_function_body(expr(postfix(name(id(Fid)), bracket(Parms))))
	 |)
	 string_to_id("RSL_is.clear" -> ClearFid)
	 string_to_id("ios::badbit" -> BadBit)
	 where(C_STATEMENTS'nil -> Ss0)
	 Append_statement(Ss0, expr(postfix(name(id(ClearFid)), bracket(list(name(id(BadBit)), nil)))) -> Ss1)
	 Append_statement(Ss1, return(name(id(RSL_is))) -> ClearAndReturn)
	 (|
	   eq(Stok, "")
	   where(C_EXPR'name(id(RSL_is)) -> E)
	 ||
	   string_to_id(Stok -> Tokid)
	   where(
	     C_EXPR'bracket(
	       binary(
		 binary(
		   name(id(RSL_is)),
		   logical_and,
		   name(id(RSL_token))
		 ),
		 eq,
		 name(id(Tokid))
	       )
	     ) -> E
	   )
	 |)
	 C_Add_function_body(if(unary(not, E), compound(ClearAndReturn), nil))


-----------------------------------------------------------------------
-- variable declarations
-----------------------------------------------------------------------

'action' Translate_variable_decls(DECLS)

  'rule' Translate_variable_decls(list(D, DS)):
	 Translate_variable_decl(D)
	 Translate_variable_decls(DS)

  'rule' Translate_variable_decls(nil):

'action' Translate_variable_decl(DECL)

  'rule' Translate_variable_decl(variable_decl(_, Defs)):
	 Translate_variable_defs(Defs)

  'rule' Translate_variable_decl(_):

'action' Translate_variable_defs(VARIABLE_DEFS)

  'rule' Translate_variable_defs(list(D, DS)):
	 Translate_variable_def(D)
	 Translate_variable_defs(DS)

  'rule' Translate_variable_defs(nil):

'action' Translate_variable_def(VARIABLE_DEF)

  'rule' Translate_variable_def(single(P, Id, _, _)):
	 Get_current_variables(-> VARS)
	 Lookup_env_variable_id(Id, nil, VARS -> OI)
	 (|
	   where(OI -> variable_id(I))
	 || -- may be local: try with localised name
	   Localise_id(P, Id -> LId)
	   Lookup_env_variable_id(LId, nil, VARS -> variable_id(I))
	 |)
	 I'Ident -> Id1
	 I'Type -> T
	 Translate_type(T -> T1)
	 I'Init -> Init
	 (|
--b	 
	   SQLWanted()
	   Universal_type_id(T -> Uid)
	   Is_table_type(Uid)
	   -- check for map
	   Type_matches_map(T) 
	   (|
	     eq(Init, nil)
	     C_Type_to_string(T1 -> Tp)
	     Concatenate(Tp, "_tbl" -> Stb)
	     string_to_c_expr(Stb -> InitExpr)
	     string_to_id("SQL_TABLE_NOT_INITIALISED"-> InitId)
	   ||
	     where(Init -> initial(VExpr))
	     Translate_value(T, VExpr -> CExpr, Ss)
	     Debracket_maxtype(T -> T2)
	     (|
	       Type_is_product(T2 -> _)
	       Universal_type_id(T -> Pid)
	       Lookup_declared_type(Pid -> CT)
	       Type_name_to_c_name(CT -> N)
	       where(CExpr -> multiple(Exprs))
	       where(postfix(name(N), bracket(Exprs)) -> InitExpr)
	     ||
	       where(CExpr -> InitExpr)
	     |)
	     string_to_id("SQL_TABLE_INITIALISED"-> InitId)
	   |)
	   C_Begin_decl()
	     C_Add_decl_specifier(storage(extern))
	     C_Add_decl_specifier(type(T1))
	     C_Add_declarator(dname(id(Id1))) 
	   C_End_decl( -> Dh) C_Decl_to_string(Dh -> SDh)
	   WriteHString(SDh)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(T1))
	     string_to_id("RSL_DEF_HOST" -> Rdh)
	     string_to_id("RSL_DEF_USER" -> Rdu)
	     string_to_id("RSL_DEF_DB" -> Rdd)
	     string_to_id("RSL_DEF_PSW" -> Rdp)
	     id_to_string(Id1 -> S) 
	     C_Add_declarator(with_init(dname(id(Id1)),
	       bracket(list(name(id(Rdh)),
	       list(name(id(Rdu)),
	       list(name(id(Rdd)),
	       list(name(id(Rdp)),
	       list(text_literal(S),
	       list(InitExpr,
	       list(name(id(InitId)), nil))))))))))
	   C_End_decl( -> Dcc) C_Decl_to_string(Dcc -> SDcc)
	   WriteCcString(SDcc)
--e
	 ||  
	   eq(Init, nil)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(T1))
	     C_Add_declarator(dname(id(Id1)))
	   C_End_decl(-> D)
	   C_Decl_to_string_h(D -> Sh)	WriteHString(Sh)
	   C_Decl_to_string(D -> Scc)	WriteCcString(Scc)
	 ||
	   where(Init -> initial(VExpr))
	   Current_parms -> CPS
	   Current_parms <- list(nil, CPS)
	   Current_parm_types -> CPTS
	   Current_parm_types <- list(nil, CPTS)
	   Translate_value(T, VExpr -> CExpr, Ss)
	   Current_parms <- CPS
	   Current_parm_types <- CPTS
	   Debracket_maxtype(T -> T2)
	   (|
	     Type_is_product(T2 -> _)
	     Universal_type_id(T -> Pid)
	     Lookup_declared_type(Pid -> CT)
	     Type_name_to_c_name(CT -> N)
	     where(CExpr -> multiple(Exprs))
	     where(postfix(name(N), bracket(Exprs)) -> InitExpr)
	   ||
	     where(CExpr -> InitExpr)
	   |)
	   (|
	     where(Ss -> nil)
	     where(InitExpr -> InitExpr1)
	   ||
	     Mk_temp_id(nil -> Fid)
	     C_Begin_func_def(id(Fid))
	       C_Add_decl_specifier(type(T1))
	       Append_statement(Ss, return(InitExpr) -> Ss1)
	       C_Set_function_body(Ss1)
	     C_End_func_def(-> DF)
	     C_Decl_to_string_h(DF -> ShF)	WriteHString(ShF)
	     C_Decl_to_string(DF -> SccF)	WriteCcString(SccF)
	     where(postfix(name(id(Fid)), bracket(nil)) -> InitExpr1)
	   |)
	   -- get best type
	   Type_of_val(VExpr, T2 -> T3)
	   New_value_id(P, id_op(Id1) -> I1)
	   I1'Type <- T3
	   Isin_subtype(val_occ(P, I1, nil), T -> Pred)	   
	   Simplify(Pred -> Pred1)
	   Make_var_def(1, T1, Id1, InitExpr1 -> D)
	   C_Decl_to_string_h(D -> Sh)	WriteHString(Sh)
	   (|
	     eq(Pred1, no_val)
	     C_Decl_to_string(D -> Scc)		WriteCcString(Scc)
	   ||
	     WriteHCcString("\n#ifdef RSL_pre\n")
	     (|
	       -- if Pred1 is a function application with one argument
	       -- matching Id1 no need to generate subtype predicate
	       where(Pred1 -> application(_, FP:val_occ(_, IP, _), list(fun_arg(_, list(VP, nil)), nil)))
	       Matches_binding(VP, single(P, id_op(Id1)))
	       IP'Type -> PT
	       Translate_value(PT, FP -> PF, nil)
	     ||
	       WriteHCcString("//subtype predicate\n")
	       Mk_temp_id(nil -> TempId)
	       Make_predicate_def(P, T1, TempId, Id1, Pred1 -> Pdef)
	       C_Decl_to_string_h(Pdef -> PSh)	WriteHString(PSh)
	       C_Decl_to_string(Pdef -> PScc)	WriteCcString(PScc)
	       where(C_EXPR'name(id(TempId)) -> PF)
	     |)
	     string_to_id("RSL_check" -> Cid)
	     PosAsString(P -> PS)
	     id_to_string(Id1 -> IdS)
	     Concatenate(PS, " Initial value " -> S1)
	     RSL_to_string_name(T1 -> Rtsn)
	     where(postfix(name(Rtsn), bracket(list(InitExpr1, nil))) -> RTSApp)
	     where(binary(text_literal(S1), plus, RTSApp) -> SE1)
	     Concatenate3(" of variable ", IdS, " not in subtype" -> S2)
	     where(binary(SE1, plus, text_literal(S2)) -> SE2)    
	     where(postfix(name(template(Cid, list(T1, nil))),
			   bracket(
			     list(PF,
			     list(InitExpr1,
			     list(SE2, nil))))) -> CheckExpr)
	     Make_var_def(1, T1, Id1, CheckExpr -> D0)
	     C_Decl_to_string(D0 -> Scc)	WriteCcString(Scc)
	     
	     WriteCcString("#else //not RSL_pre\n")
	     C_Decl_to_string(D -> Scc1)	WriteCcString(Scc1)
	     WriteHCcString("#endif //RSL_pre\n\n")
	   |)
	 |)
	
  'rule' Translate_variable_def(multiple(P, list(Id, Ids), T0)):
	 Translate_variable_def(single(P, Id, T0, nil))
	 Translate_variable_def(multiple(P, Ids, T0))

  'rule' Translate_variable_def(multiple(_, nil, _)):



-----------------------------------------------------------------------
-- value declarations
-----------------------------------------------------------------------

'action' Rev_value_ids(Value_ids, Value_ids -> Value_ids)

  'rule' Rev_value_ids(list(I, Is), Is1 -> Is2):
	 Rev_value_ids(Is, list(I, Is1) -> Is2)

  'rule' Rev_value_ids(nil, Is -> Is):

'action' Collect_value_decls(DECLS, Value_ids -> Value_ids)

  'rule' Collect_value_decls(list(D, DS), Ids -> Ids2):
	 Collect_value_decl(D, Ids -> Ids1)
	 Collect_value_decls(DS, Ids1 -> Ids2)

  'rule' Collect_value_decls(nil, Ids -> Ids1):
	 Rev_value_ids(Ids, nil -> Ids1)
	 

'action' Collect_value_decl(DECL, Value_ids -> Value_ids)

  'rule' Collect_value_decl(value_decl(_, Defs), Ids -> Ids1):
	 Get_current_top_values(-> VE)
	 Collect_value_defs(VE, Defs, Ids -> Ids1)

  'rule' Collect_value_decl(_, Ids -> Ids):

'action' Collect_value_defs(Value_ids, VALUE_DEFS, Value_ids -> Value_ids)

  'rule' Collect_value_defs(VE, list(H,T), Ids -> Ids3):
	 Collect_value_def(VE, H -> Ids1)
	 Conc_values(Ids1, Ids -> Ids2)
	 Collect_value_defs(VE, T, Ids2 -> Ids3)

  'rule' Collect_value_defs(_, nil, Ids -> Ids):

'action' Conc_values(Value_ids, Value_ids -> Value_ids)

  'rule' Conc_values(list(I, Ids), Ids1 -> list(I, Ids2)):
	 Conc_values(Ids, Ids1 -> Ids2)

  'rule' Conc_values(nil, Ids -> Ids):

'action' Collect_value_def(Value_ids, VALUE_DEF -> Value_ids)

  'rule' Collect_value_def(VE, typing(_, single(_, B, _)) -> Is):
	 Collect_value_binding(VE, B -> Is)

  'rule' Collect_value_def(VE, typing(_, multiple(_, Bs, _)) -> Is):
	 Collect_value_bindings(VE, Bs -> Is)
	 
  'rule' Collect_value_def(VE, exp_val(_, single(_, B, _), _) -> Is):
	 Collect_value_binding(VE, B -> Is)

  'rule' Collect_value_def(VE, exp_fun(_, single(_, B, _), _, _, _, _, _) -> Is):
	 Collect_value_binding(VE, B -> Is)

  'rule' Collect_value_def(VE, imp_val(_, single(_, B, _), _) -> Is):
	 Collect_value_binding(VE, B -> Is)

  'rule' Collect_value_def(VE, imp_fun(_, single(_, B,_), _, _, _) -> Is):
	 Collect_value_binding(VE, B -> Is)

'action' Collect_value_binding(Value_ids, BINDING -> Value_ids)

  'rule' Collect_value_binding(VE, single(P, _) -> list(I, nil)):
	 Select_id_by_pos(P, VE -> value_id(I))

  'rule' Collect_value_binding(VE, product(_, Bs) -> Is):
	 Collect_value_bindings(VE, Bs -> Is)

  'rule' Collect_value_binding(VE, single(P, _) -> nil):

'action' Collect_value_bindings(Value_ids, BINDINGS -> Value_ids)

  'rule' Collect_value_bindings(VE, list(B, Bs) -> Is):
	 Collect_value_bindings(VE, Bs -> Is1)
	 (|
	   where(B -> single(P, _))
	   Select_id_by_pos(P, VE -> value_id(I))
	   where(Value_ids'list(I, Is1) -> Is)
	 ||
	   where(B -> product(P, Bs1))
	   Collect_value_bindings(VE, Bs1 -> Is2)
	   Conc_values(Is2, Is1 -> Is)
	 |)

  'rule' Collect_value_bindings(_, nil -> nil):

'action' Translate_value_ids(Value_ids, Value_ids, FOUND)

  'rule' Translate_value_ids(list(I, Is), Wait, Found):
	 I'Def -> Def
	 Translate_value_id(I, Def, Is, Wait, Found -> Wait1, Found1)
	 Translate_value_ids(Is, Wait1, Found1)

  'rule' Translate_value_ids(nil, nil, _):

  'rule' Translate_value_ids(nil, Wait:list(I, _), Found):
	 (|
	   eq(Found, found)
	   Translate_value_ids(Wait, nil, nil)
	 ||
	   I'Pos -> P
	   I'Ident -> Id
	   Puterror(P)
	   Print_id_or_op(Id)
	   Putmsg(" seems to be involved in a mutual recursion: cannot translate")
	   Putnl()
	 |)
	   

'action' Translate_value_id(Value_id, VALUE_DEFINITION, Value_ids, Value_ids, FOUND -> Value_ids, FOUND)

  'rule' Translate_value_id(I, no_def, _, Wait, Found -> Wait, found):
	 I'Pos -> P
	 I'Ident -> Id_or_op
	 I'Type -> T
	 Id_or_op_to_id(Id_or_op -> Id)
	 Translate_type(T -> T1)
	 C_Begin_decl()
	   C_Add_decl_specifier(type(T1))
	   C_Add_declarator(dname(id(Id)))
	 C_End_decl(-> D)
	 C_Decl_to_string(D -> Scc)
	 WriteCcString(Scc)
	 Putwarning(P)
	 Print_id(Id)
	 Putmsg(" has no definition")
	 Putnl()
	 WriteCcString("/*INCOMPLETE: undefined value*/\n")
	   
  'rule' Translate_value_id(I, expl_val(V, _), Todo, Wait, Found -> Wait1, Found1):
	 Collect_value_ids(V, nil -> Deps)
	 Intersect_values(Deps, Wait -> Wait_deps)
	 Intersect_values(Deps, Todo -> Todo_deps)
	 (|
	   eq(Wait_deps, nil)
	   eq(Todo_deps, nil)
	   where(Wait -> Wait1)
	   where(found -> Found1)
	   I'Ident -> Id_or_op
	   I'Type -> T
	   I'Pos -> P
	   Id_or_op_to_id(Id_or_op -> Id)
	   Translate_value(T, V -> CExpr, Ss)
	   Debracket_maxtype(T -> T1)
	   (|
	     Type_is_product(T1 -> _)
	     Universal_type_id(T -> Pid)
	     Lookup_declared_type(Pid -> CT)
	     Type_name_to_c_name(CT -> N)
	     where(CExpr -> multiple(Exprs))
	     where(postfix(name(N), bracket(Exprs)) -> InitExpr)
	   ||
	     where(CExpr -> InitExpr)
	   |)
	   Translate_type(T -> CT)
	   (|
	     where(Ss -> nil)
	     where(InitExpr -> InitExpr1)
	   ||
	     Mk_temp_id(nil -> Fid)
	     C_Begin_func_def(id(Fid))
	       C_Add_decl_specifier(type(CT))
	       Append_statement(Ss, return(InitExpr) -> Ss1)
	       C_Set_function_body(Ss1)
	     C_End_func_def(-> DF)
	     C_Decl_to_string_h(DF -> ShF)	WriteHString(ShF)
	     C_Decl_to_string(DF -> SccF)	WriteCcString(SccF)
	     where(postfix(name(id(Fid)), bracket(nil)) -> InitExpr1)
	   |)
	   (| -- explicit values stored as disambiguations
	     where(V -> disamb(_, V1, _))
	   ||
	     where(V -> V1)
	   |)
	   -- get best type
	   Type_of_val(V1, T1 -> T2)
	   New_value_id(P, Id_or_op -> I1)
	   I1'Type <- T2
	   Isin_subtype(val_occ(P, I1, nil), T -> Pred)
	   Simplify(Pred -> Pred1)
	   Local_depth -> N
	   Make_var_def(N, CT, Id, InitExpr1 -> D)
	   (|
	     eq(Pred1, no_val)
	     C_Decl_to_string_h(D -> Sh)	WriteHString(Sh)
	     C_Decl_to_string(D -> Scc)		WriteCcString(Scc)
	   ||
	     WriteHCcString("\n#ifdef RSL_pre\n")
	     (|
	       -- if Pred1 is a function application with one argument
	       -- matching Id_or_op no need to generate subtype predicate
	       where(Pred1 -> application(_, FP:val_occ(_, IP, _), list(fun_arg(_, list(VP, nil)), nil)))
	       Matches_binding(VP, single(P, Id_or_op))
	       IP'Type -> PT
	       Translate_value(PT, FP -> PF, nil)
	     ||
	       WriteHCcString("//subtype predicate\n")
	       Mk_temp_id(nil -> TempId)
	       Make_predicate_def(P, CT, TempId, Id, Pred1 -> Pdef)
	       C_Decl_to_string_h(Pdef -> PSh)	WriteHString(PSh)
	       C_Decl_to_string(Pdef -> PScc)	WriteCcString(PScc)
	       where(C_EXPR'name(id(TempId)) -> PF)
	     |)
	     string_to_id("RSL_check" -> Cid)
	     PosAsString(P -> PS)
	     id_to_string(Id -> IdS)
	     Concatenate(PS, " Value " -> S1)
	     RSL_to_string_name(CT -> Rtsn)
	     where(postfix(name(Rtsn), bracket(list(InitExpr1, nil))) -> RTSApp)
	     where(binary(text_literal(S1), plus, RTSApp) -> SE1)
	     Concatenate3(" of constant ", IdS, " not in subtype" -> S2)
	     where(binary(SE1, plus, text_literal(S2)) -> SE2)    
	     where(postfix(name(template(Cid, list(CT, nil))),
			   bracket(
			     list(PF,
			     list(InitExpr1,
			     list(SE2, nil))))) -> CheckExpr)
	     Make_var_def(N, CT, Id, CheckExpr -> D0)
	     C_Decl_to_string_h(D0 -> Sh)	WriteHString(Sh)
	     C_Decl_to_string(D0 -> Scc)	WriteCcString(Scc)
	     
	     WriteHCcString("#else //not RSL_pre\n")
	     C_Decl_to_string_h(D -> Sh1)	WriteHString(Sh1)
	     C_Decl_to_string(D -> Scc1)	WriteCcString(Scc1)
	     WriteHCcString("#endif //RSL_pre\n\n")
	   |)
	 ||
	   where(Value_ids'list(I, Wait) -> Wait1)
	   where(Found -> Found1)
	 |)

  'rule' Translate_value_id(I, F:expl_fun(Parms, VExpr, Post, Pre, Cond, Pcond), Todo, Wait, Found -> Wait, found):
	 I'Ident -> Id_or_op
	 I'Type -> T
	 I'Pos -> P
	 Make_function_type(T -> fun(T1, _, _))
	 Current_funs -> Is
	 Current_funs <- list(I, Is)
	 Translate_expl_fun(P, Id_or_op, T, F -> Decl)
	 Current_funs <- Is
	 C_Decl_to_string(Decl -> Scc)
	 WriteCcString(Scc)
	 C_Decl_to_string_h(Decl -> Sh)
	 WriteHString(Sh)

  'rule' Translate_value_id(I, impl_val(V), Todo, Wait, Found -> Wait, found):
	 I'Ident -> Id_or_op
	 I'Type -> T
	 I'Pos -> P
	 Id_or_op_to_id(Id_or_op -> Id)
	 Putwarning(P)
	 Print_id(Id)
	 Putmsg("has an implicit definition: no initial value")
	 Putnl()
	 C_Begin_decl()
	   [|
	     Local_depth -> N
	     eq(N, 0) -- not in local expression
	     C_Add_decl_specifier(type(const))
	   |]
	   Translate_type(T -> T1)
	   C_Add_decl_specifier(type(T1))
	   C_Add_declarator(dname(id(Id)))
	 C_End_decl(-> D)
	 C_Decl_to_string_h(D -> Sh)	WriteHString(Sh)
	 C_Decl_to_string(D -> Scc)	WriteCcString(Scc)
	 WriteCcString("/*INCOMPLETE: implicit value definition*/\n")

  'rule' Translate_value_id(I, impl_fun(Parms, _, _, _), Todo, Wait, Found -> Wait, found):
	 I'Pos -> P
	 Putwarning(P)
	 Putmsg("implicit function definition: no definition generated")
	 Putnl()
	 I'Ident -> Id_or_op
	 I'Type -> T
	 Translate_impl_fun(Id_or_op, T, Parms -> Decl)
	 C_Decl_to_string(Decl -> Scc)
--	 WriteCcString("/*INCOMPLETE: implicit function definition*/\n")
	 WriteCcString(Scc)
	 C_Decl_to_string_h(Decl -> Sh)
	 WriteHString(Sh)

'action' Make_var_def(INT, C_TYPE_SPECIFIER, IDENT, C_EXPR -> C_DECL)

  'rule' Make_var_def(N, CT, Id, Expr -> D):
	 C_Begin_decl()
	   [|
	     eq(N, 0) -- not in local expression
	     C_Add_decl_specifier(type(const))
	   |]
	   C_Add_decl_specifier(type(CT))
	   C_Add_declarator(with_init(dname(id(Id)), assign(Expr)))
	 C_End_decl(-> D)

'action' Make_predicate_def(POS, C_TYPE_SPECIFIER, IDENT, IDENT, VALUE_EXPR -> C_DECL)

  'rule' Make_predicate_def(P, CT, Fid, Id, Pred -> D):
	 C_Begin_func_def(id(Fid))
	   C_Add_decl_specifier(type(bool))
	   C_Arg_decl_specifier(type(const))
	   C_Arg_decl_specifier(type(CT))
	   C_Arg_declarator(dname(id(Id)))
	   Translate_function_body(P, id_op(Fid), nil, unit, bool, Pred, nil, nil, nil, nil)
	 C_End_func_def(-> D)

---------------------------------------
-- explicit function definition support
---------------------------------------

'action' Translate_expl_fun(POS, ID_OR_OP, TYPE_EXPR, VALUE_DEFINITION -> C_DECL)

  'rule' Translate_expl_fun(P, Id_or_op, fun(T1, Arrow, result(T2, _, _, _, _)), F:expl_fun(Parms, VExpr, Post, Pre, Cond, Pcond) -> Decl):
	 where(Parms -> list(FP, _))
	 where(FP -> form_parm(_, Bs))
	 [|
	   -- if single argument has product type, make sure type defined
	   Type_is_product(T1 -> XT)
	   where(Bs -> list(_, nil))
	   Translate_type(product(XT) -> _)
	 |]
	 Current_funs -> list(I, _)
	 [|
	   Collect_fun_ids(Cond, nil -> Is)
	   Isin_value_ids(I, Is)
	   Putwarning(P)
	   Print_id_or_op(Id_or_op)
	   Putmsg(" is circular in its subtype condition\n")
	 |]
	 [|
	   Collect_fun_ids(Pre, nil -> Is1)
	   Isin_value_ids(I, Is1)
	   Putwarning(P)
	   Print_id_or_op(Id_or_op)
	   Putmsg(" is circular in its precondition\n")
	 |]
	 Translate_type(T2 -> T)
	 Id_or_op_to_id(Id_or_op -> Id)
	 C_Begin_func_def(id(Id))
	   C_Add_decl_specifier(type(T))
	   Translate_parms_to_args(T1, Parms -> Ss)
	   Translate_function_body(P, Id_or_op, Bs, T1, T2, VExpr, Post, Pre, Cond, Pcond)
	   Current_parms -> list(_, CPS)
	   Current_parms <- CPS
	   Current_parm_types -> list(_, CPTS)
	   Current_parm_types <- CPTS
	   C_Prefix_function_body(Ss)
	 C_End_func_def(-> Decl)

'action' Translate_impl_fun(ID_OR_OP, TYPE_EXPR, FORMAL_FUNCTION_PARAMETERS -> C_DECL)

  'rule' Translate_impl_fun(Id_or_op, fun(T1, _, result(T2,_,_,_,_)), Parms -> Decl):
	 [|
	   -- if single argument has product type, make sure type defined
	   Type_is_product(T1 -> XT)
	   where(Parms -> list(FP, _))
	   where(FP -> form_parm(_, list(_, nil)))
	   Translate_type(product(XT) -> _)
	 |]
	 Translate_type(T2 -> T)
	 Id_or_op_to_id(Id_or_op -> Id)
	 C_Begin_func_def(id(Id))
	   C_Add_decl_specifier(type(T))
	   Translate_parms_to_args(T1, Parms -> Ss)
	   string_to_id("/*INCOMPLETE: implicit function definition*/" -> Cmnt)
	   C_Add_function_body(expr(name(id(Cmnt))))
	   C_Prefix_function_body(Ss)
	   Current_parms -> list(_, CPS)
	   Current_parms <- CPS
	   Current_parm_types -> list(_, CPTS)
	   Current_parm_types <- CPTS
	 C_End_func_def(-> Decl)

'action' Translate_parms_to_args(TYPE_EXPR, FORMAL_FUNCTION_PARAMETERS -> C_STATEMENTS)

  'rule' Translate_parms_to_args(T, list(form_parm(_, Bs), nil) -> Ss):
	 Translate_bindings_to_args(T, Bs -> Ss)

  'rule' Translate_parms_to_args(_, list(form_parm(P, _), _) -> nil):
	 Puterror(P)
	 Putmsg("INCOMPLETE: Cannot translate functions with more than one formal parameter")
	 Putnl()

'action' Translate_bindings_to_args(TYPE_EXPR, BINDINGS -> C_STATEMENTS)

  'rule' Translate_bindings_to_args(T, Bs -> Ss):
	 Current_parms -> CPS
	 Current_parm_types -> CPTS
	 (|
	   eq(Bs, nil) -- ignore unit type
	   where(C_STATEMENTS'nil -> Ss)
	   Current_parms <- list(nil, CPS)
	   Current_parm_types <- list(nil, CPTS)
	 ||
	   Type_is_product(T -> XT)
	   (|
	     where(Bs -> list(B, nil))
	     Resolve_parm_types(list(T, nil), Bs -> Ss)
	     Current_parms <- list(Bs, CPS)
	     Current_parm_types <- list(list(T, nil), CPTS)
	   ||
	     Resolve_parm_types(XT, Bs -> Ss)
	     Current_parms <- list(Bs, CPS)
	     Current_parm_types <- list(XT, CPTS)
	   |)
	 ||
	   where(Bs -> list(B, nil))
	   Resolve_parm_types(list(T, nil), Bs -> Ss)
	   Current_parms <- list(Bs, CPS)
	   Current_parm_types <- list(list(T, nil), CPTS)
	 ||
	   Length_bs(Bs -> N)
	   Make_product_type(T, N -> product(XT))
	   Resolve_parm_types(XT, Bs -> Ss)
	   Current_parms <- list(Bs, CPS)
	   Current_parm_types <- list(XT, CPTS)
	 |)
	 

'action' Resolve_parm_types(PRODUCT_TYPE, BINDINGS -> C_STATEMENTS)

  'rule' Resolve_parm_types(list(T, Ts), list(B, Bs) -> Ss):
	 (|
	   eq(T, unit) -- simply ignore unit type
	   where(C_STATEMENTS'nil -> Ss1)
	 ||
	   (|
	     -- single binding
	     where(B -> single(P, Id_or_op))
	     Id_or_op_to_id(Id_or_op -> Id)
	     C_Arg_decl_specifier(type(const))
	     Translate_arg(T -> T1)
	     C_Arg_decl_specifier(type(T1))
	     C_Arg_declarator(dname(local_id(P,Id)))
	     where(C_STATEMENTS'nil -> Ss1)
	   ||
	     -- product binding
	     where(B -> product(_, Bs1))
	     Mk_temp_id(nil -> TempId)
	     C_Arg_decl_specifier(type(const))
	     Translate_arg(T -> T1)
	     C_Arg_decl_specifier(type(T1))
	     C_Arg_declarator(dname(id(TempId)))
	     Debracket_maxtype(T -> Tm)
	     Type_is_product(Tm -> Ts1)
	     Product_binding_to_decls(name(id(TempId)), Ts1, Bs1 -> Ss1)
	   |)
	 |)
	 Resolve_parm_types(Ts, Bs -> Ss2)
	 Concatenate_statements(Ss1, Ss2 -> Ss)

  'rule' Resolve_parm_types(nil, nil -> nil):

-- debug
--  'rule' Resolve_parm_types(TS, Bs):
--Print_type(product(TS))
--Print_bindings(Bs)

'action' Pre_name_defs(VALUE_EXPR -> C_STATEMENTS)

  'rule' Pre_name_defs(V -> Ss):
	 Collect_pre_occs(V, nil -> POs)
	 Pre_occ_defs(POs -> Ss)

'action' Pre_occ_defs(VALUE_EXPRS -> C_STATEMENTS)

  'rule' Pre_occ_defs(list(PO, POs) -> list(S, Ss)):
	 Pre_occ_def(PO -> S)
	 Pre_occ_defs(POs -> Ss)

  'rule' Pre_occ_defs(nil -> nil):

'action' Pre_occ_def(VALUE_EXPR -> C_STATEMENT)

  'rule' Pre_occ_def(pre_occ(_, I, OptQ) -> decl(D)):
	 I'Ident -> Id
	 I'Qualifier -> Is
	 I'Type -> T
	 Translate_type(T -> CT)
	 id_to_string(Id -> Str)
	 Concatenate(Str, "_rsL" -> Str1)
	 string_to_id(Str1 -> PreId)
	 Translate_id(id_op(Id), OptQ, Is -> N)
	 C_Begin_decl()
	   C_Add_decl_specifier(type(CT))
	   C_Add_declarator(
	       with_init(
		 dname(id(PreId)),
		 assign(name(N))
	       )
	     )
	 C_End_decl(-> D)

'action' Translate_function_body(POS, ID_OR_OP, BINDINGS, TYPE_EXPR, TYPE_EXPR, VALUE_EXPR, OPT_POST_CONDITION, PRE_CONDITION, OPT_CONDITION, OPT_CONDITION)

  'rule' Translate_function_body(P, Id, Bs, PT, T, V, Post, Pre, Cond, PCond):
	 PosAsString(P -> PS)
	 (|
	   where(Id -> op_op(rem))
	   where("\\\\" -> IdS)
	 ||
	   Id_or_op_to_string(Id -> IdS)
	 |)
	 Bindings_to_output_string(Bs, PT -> SB)
	 (|
	   eq(Pre, nil)
	   eq(Cond, nil)
	   eq(Post, nil)
	   where(C_STATEMENTS'nil -> Ss0)
	 ||
	   (|
	     where(Cond -> condition(C0))
	     Translate_value(bool, C0 -> E0, Ss000)
	     (|
	       eq(Bs, nil)
	       GetF2String("%s Arguments of %s() not in subtypes",
			       PS, IdS -> ST1)
	       Append_statement(Ss000, cond_warn(E0, text_literal(ST1)) -> Ss00)
	     ||
	       GetF2String("%s Arguments of %s(", PS, IdS -> ST1)
	       Append_statement(Ss000,
		cond_warn(E0,
			  binary(text_literal(ST1),
			  plus,
			  binary(SB, plus, text_literal(") not in subtypes"))))
			  -> Ss00)
	     |)
	   ||
	     where(C_STATEMENTS'nil -> Ss00)
	   |)
	   (|
	     where(Pre -> pre_cond(_, C1))
	     Translate_value(bool, C1 -> E1, Ss010)
	     (|
	       eq(Bs, nil)
	       GetF2String("%s Precondition of %s() not satisfied",
			       PS, IdS -> ST2)
	       Append_statement(Ss010, cond_warn(E1, text_literal(ST2)) -> Ss01)
	     ||
	       GetF2String("%s Precondition of %s(", PS, IdS -> ST2)
	       Append_statement(Ss010,
	        cond_warn(E1,
			  binary(text_literal(ST2),
			  plus,
			  binary(SB, plus, text_literal(") not satisfied"))))
			  -> Ss01)
	     |)
	   ||
	     where(C_STATEMENTS'nil -> Ss01)
	   |)
	   (|
	     where(Post -> post(post_cond(_, _, C2)))
	     Pre_name_defs(C2 -> Ss02)
	   ||
	     where(C_STATEMENTS'nil -> Ss02)
	   |)
	   Concatenate_statements(Ss00, Ss01 -> Ss0001)
	   Concatenate_statements(Ss0001, Ss02 -> Ss03)
	   (|
	     eq(Ss03, nil)
	     where(C_STATEMENTS'nil -> Ss0)
	   ||
	     where(cpp(ifdef("RSL_pre")) -> S0)
	     where(cpp(endif("RSL_pre")) -> S1)
	     Append_statement(C_STATEMENTS'list(S0, Ss03), S1 -> Ss0)
	   |)
	 |)
	 Translate_value(T, V -> E, Ss)
	 (|
	   ne(T, unit)
	   (|
	     Debracket_maxtype(T -> T1)
	     Type_is_product(T1 -> _)
	     Universal_type_id(T -> Pid)
	     Lookup_declared_type(Pid -> CT)
	     Type_name_to_c_name(CT -> N)
	     where(E -> multiple(Exprs))
	     where(postfix(name(N), bracket(Exprs)) -> E1)
	   ||
	     where(E -> E1)
	   |)
	   (|
	     (| where(PCond -> condition(_)) ||
	        where(Post -> post(_)) |)
	     (|
	        where(Post -> post(post_cond(_, result(_, single(_, id_op(RId))), _)))
	     ||
	       string_to_id("RSL_res_" -> RId)
	     |)
	     Translate_type(T -> RT)
	     C_Begin_decl()
	       C_Add_decl_specifier(type(RT))
	       C_Add_declarator(with_init(dname(id(RId)), assign(E1)))
	     C_End_decl(-> D)
	     Concatenate_statements(Ss, 
				    list(cpp(ifdef("RSL_pre")),
				    list(decl(D), nil)) -> Ss10)
	     GetFString("%s Result ", PS -> ST31)
	     RSL_to_string_name(RT -> Rtsn)
	     where(postfix(name(Rtsn), bracket(list(name(id(RId)), nil))) -> RTSApp)
	     where(binary(text_literal(ST31), plus, RTSApp) -> STE1)
	     GetFString(" of %s(", IdS -> ST32)
	     where(binary(STE1, plus, text_literal(ST32)) -> STE2)
	     where(binary(STE2, plus, SB) -> STE3)
	     where(binary(STE3, plus, text_literal(")")) -> STE4)
	     (|
	       where(PCond -> condition(PC))
	       where(binary(STE4, plus, text_literal(" not in subtype")) -> STE5)
	       Translate_value(bool, PC -> EPC, Ss11)
	       Concatenate_statements(Ss10, Ss11 -> Ss12)
	       Append_statement(Ss12, cond_warn(EPC, STE5) -> Ss13)
	     ||
	       where(Ss10 -> Ss13)
	     |)
	     (|
	       where(Post -> post(post_cond(PP, RN, PostCond)))
	       (|
	         (| eq(RN, nil) ||
		    where(RN -> result(_, single(_, id_op(_)))) |)
		 Translate_value(bool, PostCond -> EPostCond, Ss14)
	       ||
	         where(RN -> result(PRN, Bind))
		 New_value_id(PRN, id_op(RId) -> RI)
		 where(explicit(PP, binding(PP, Bind), val_occ(PP, RI, nil)) -> LD)
		 Translate_value(bool, let_expr(PP, list(LD, nil), PostCond) -> EPostCond, Ss14)
	       |)
	       Concatenate_statements(Ss13, Ss14 -> Ss15)
	       where(binary(STE4, plus, text_literal(" does not satisfy postcondition")) -> STE6)
	       Append_statement(Ss15, cond_warn(EPostCond, STE6) -> Ss16)
	     ||
	       where(Ss13 -> Ss16)
	     |)
	     Concatenate_statements(Ss16,
				    list(return(name(id(RId))),
				    list(cpp(else("RSL_pre")),
				    list(return(E1),
				    list(cpp(endif("RSL_pre")), nil)))) -> Ss1)
	   ||
	     Append_statement(Ss, return(E1) -> Ss1)
	   |)
	 ||
	   Append_statement(Ss, expr(E) -> Ss17)
	   (|
	     where(Post -> post(post_cond(_, RN, PostCond)))
	     [|
	       where(RN -> result(PRN, _))
	       Putwarning(PRN)
	       Putmsg("Result naming for Unit-type function ")
	       Print_id_or_op(Id)
	       Putmsg(": ignored")
	       Putnl()
	     |]
	     (|
	       eq(Bs, nil)
	       GetF2String("%s Function call %s() does not satisfy postcondition", PS, IdS -> ST31)
	       where(text_literal(ST31) -> STE3)
	     ||
	       GetF2String("%s Function call %s(", PS, IdS -> ST1)
	       where(binary(text_literal(ST1), plus, SB) -> STE2)
	       where(binary(STE2, plus, text_literal(") does not satisfy postcondition")) -> STE3)
	     |)
	     Append_statement(Ss17, cpp(ifdef("RSL_pre")) -> Ss18)
	     Translate_value(bool, PostCond -> EPostCond, Ss19)
	     Concatenate_statements(Ss18, Ss19 -> Ss20)
	     Concatenate_statements(Ss20,
				    list(cond_warn(EPostCond, STE3),
				    list(cpp(endif("RSL_pre")), nil)) -> Ss1)
	   ||
	     where(Ss17 -> Ss1)
	   |)
	 |)
	 Concatenate_statements(Ss0, Ss1 -> Ss2)
	 C_Set_function_body(Ss2)

'action' Parms_to_output_string(C_EXPRS, PRODUCT_TYPE -> C_EXPR)

  'rule' Parms_to_output_string(list(E, nil), list(T, _) -> S):
	 Parm_to_output_string(E, T -> S)

  'rule' Parms_to_output_string(list(E, Es), list(T, Ts) ->
	      binary(S1, plus, binary(text_literal(", "), plus, S2))): 
	 Parm_to_output_string(E, T -> S1)
	 Parms_to_output_string(Es, Ts -> S2)

'action' Parm_to_output_string(C_EXPR, TYPE_EXPR -> C_EXPR)

  'rule' Parm_to_output_string(E, T ->
              postfix(name(N), bracket(list(E, nil)))):
	 Translate_type(T -> CT)
	 RSL_to_string_name(CT -> N)

'action' Bindings_to_output_string(BINDINGS, TYPE_EXPR -> C_EXPR)

  'rule' Bindings_to_output_string(list(B, nil), T -> S):
	 Binding_to_output_string(B, T -> S)

  'rule' Bindings_to_output_string(Bs:list(_,_), T -> S):
	 (|
	   where(T -> product(XT))
	 ||
	   Length_bs(Bs -> N)
	   Make_product_type(T, N -> product(XT))
	 |)
	 Bindings_to_output_string1(Bs, XT -> S)

  'rule' Bindings_to_output_string(nil, _ -> text_literal("")):

'action' Bindings_to_output_string1(BINDINGS, PRODUCT_TYPE -> C_EXPR)

  'rule' Bindings_to_output_string1(list(B, nil), list(T, nil) -> S):
	 Binding_to_output_string(B, T -> S)

  'rule' Bindings_to_output_string1(list(B, Bs), list(T, Ts) ->
		binary(S1, plus, binary(text_literal(", "), plus, S2))):
	 Binding_to_output_string(B, T -> S1)
	 Bindings_to_output_string1(Bs, Ts -> S2)

'action' Binding_to_output_string(BINDING, TYPE_EXPR -> C_EXPR)

  'rule' Binding_to_output_string(single(P, Id_op), T ->
		postfix(name(N), bracket(list(name(local_id(P, Id)), nil)))):
	 Id_or_op_to_id(Id_op -> Id)
	 Translate_type(T -> CT)
	 RSL_to_string_name(CT -> N) 

  'rule' Binding_to_output_string(product(_, Bs), T ->
	   binary(text_literal("("), plus, binary(S, plus, text_literal(")")))):
	 Bindings_to_output_string(Bs, T -> S)

-----------------------------------------------------------------------
-- Value expressions
-----------------------------------------------------------------------

'action' Translate_value(TYPE_EXPR, VALUE_EXPR -> C_EXPR, C_STATEMENTS)

  'rule' Translate_value(bracket(T), V -> E, Ss):
	 Translate_value(T, V -> E, Ss)

  'rule' Translate_value(_, literal_expr(_, VL) -> literal(VL), nil):

  'rule' Translate_value(T, product(P, Vs) -> E, Ss):
	 -- make sure type defined
	 Translate_type(T -> _)
	 Translate_values(T, Vs -> Es, Ss)
	 Debracket_maxtype(T -> T1)
	 Universal_type_id(T -> Pid)
	 Lookup_declared_type(Pid -> CT)
	 Type_name_to_c_name(CT -> N)
	 where(postfix(name(N), bracket(Es)) -> E)

  'rule' Translate_value(_, val_occ(_, I, Q) -> E, nil):
	 I'Ident -> Id_or_op
	 I'Qualifier -> Is
	 (|
	   where(Id_or_op -> id_op(_))
	   Translate_id(Id_or_op, Q, Is -> N)
	 ||
	   where(Id_or_op -> op_op(Op))
	   (|
	     Built_in(Op, I)
	     Translate_built_in_op(Op, I -> Op1)
	     where(op_fun(Op1) -> N)
	   ||
	     Translate_id(Id_or_op, Q, Is -> N)
	   |)
	 |)
	 where(C_EXPR'name(N) -> E)


  'rule' Translate_value(_, disamb(_, VExpr, TExpr) -> CExpr, Ss):
	 Translate_value(TExpr, VExpr  -> CExpr, Ss)

  'rule' Translate_value(T, bracket(P, VExpr) -> bracket(CExpr), Ss):
	 Translate_value(T, VExpr -> CExpr, Ss)

  'rule' Translate_value(T, ax_infix(P, LExpr, C, RExpr, PE) -> E, Ss):
	 (|
	   eq(C, and)
	   Translate_value(T, if_expr(P, LExpr, RExpr, region(P,PE), nil, else(P,literal_expr(P,bool_false))) -> E, Ss)
	 ||
	   eq(C, or)
	   Translate_value(T, if_expr(P, LExpr, literal_expr(P,bool_true), region(P,P), nil, else(P,RExpr)) -> E, Ss)
	 || -- implies
	   Translate_value(T, if_expr(P, LExpr, RExpr, region(P,PE), nil, else(P,literal_expr(P,bool_true))) -> E, Ss)
	 |)

  'rule' Translate_value(T, infix_occ(P, LExpr, Op, Qual, RExpr) -> E, Ss):
	 Make_results(LExpr -> list(result(LT,_,_,_,_),_))
	 Make_results(RExpr -> list(result(RT,_,_,_,_),_))
	 Op'Ident -> op_op(O)
	 (|
	   Built_in(O, Op)
	   (|
	     (| eq(O, isin) || eq(O, notisin) |)
	     De_bracket_arg(LExpr -> LExpr1)
	     De_bracket_arg(RExpr -> RExpr01)
	     -- check for isin dom, isin elems
	     (|
	       Dom_or_elems(RExpr01 -> RExpr02)
	       De_bracket_arg(RExpr02 -> RExpr1)
	     ||
	       where(RExpr01 -> RExpr1)
	     |)
	     
	   ||
	     where(LExpr -> LExpr1)
	     where(RExpr -> RExpr1)
	   |)
	 ||
	   De_bracket_arg(LExpr -> LExpr1)
	   De_bracket_arg(RExpr -> RExpr1)
	 |)
	 Translate_values(product(list(LT, list(RT, nil))),
			  list(LExpr1, list(RExpr1, nil)) -> Es:list(E1, list(E2, nil)), Ss)
	 (|
	   Built_in(O, Op)
	   (|
	     eq(O, isin)
	     string_to_id("isin" -> Fid)
	     where(postfix(name(id(Fid)), bracket(Es)) -> E)
	   ||
	     eq(O, notisin)
	     string_to_id("isin" -> Fid)
	     where(unary(not, bracket(postfix(name(id(Fid)), bracket(Es)))) -> E)
	   ||
	     Translate_built_in_op(O, Op -> C_Op)
	     where(binary(E1, C_Op, E2) -> E)
	   |)
	 ||
	   Op'Qualifier -> Is
	   Translate_id(op_op(O), Qual, Is -> N)
	   where(postfix(name(N), bracket(Es)) -> E)
	 |)

  'rule' Translate_value(T, ax_prefix(_, C, VExpr) -> E, Ss):
	 Translate_connective(C -> C_Op)
	 Translate_value(T, VExpr -> CExpr, Ss)
	 where(unary(C_Op, CExpr) -> E)

  'rule' Translate_value(_, prefix_occ(P, Op, Qual, VExpr) -> E, Ss):
	 Op'Ident -> op_op(O)
	 Make_results(VExpr -> list(result(T,_,_,_,_),_))
	 De_bracket_arg(VExpr -> VExpr1)
	 Translate_value(T, VExpr1 -> CExpr, Ss)
	 Translate_prefix(O, Op, Qual, CExpr -> E)

  'rule' Translate_value(T, ranged_set(P, L, R) -> E, Ss):
	 -- translate type to check defined
	 Translate_type(T -> _)
	 string_to_id("init_ranged_set" -> Fid)
	 [|
	   Not_yet_declared_id(Fid)
	   C_Begin_func_def(id(Fid))
	     Mk_Set_id(-> SetId)
	     Universal_type_id(fin_set(int) -> Tid)
	     Lookup_declared_type(Tid -> CT)
	     Type_name_to_c_name(CT -> N)
	     C_Add_decl_specifier(storage(static))
	     C_Add_decl_specifier(type(CT))
	     -- args
	     C_Arg_decl_specifier(type(const))
	     C_Arg_decl_specifier(type(int))
	     string_to_id("l" -> L_)
	     Mk_temp_id(ident(L_) -> L1_)
	     C_Arg_declarator(dname(id(L1_)))
	     C_Arg_decl_specifier(type(const))
	     C_Arg_decl_specifier(type(int))
	     string_to_id("r" -> R_)
	     Mk_temp_id(ident(R_) -> R1_)
	     C_Arg_declarator(dname(id(R1_)))
	     -- body
	     C_Begin_decl()
	       C_Add_decl_specifier(type(CT))
	       string_to_id("s" -> S_)
	       Mk_temp_id(ident(S_) -> S1_)
	       C_Add_declarator(dname(id(S1_)))
	     C_End_decl(-> D)
	     C_Add_function_body(decl(D))
	     C_Add_function_body(expr(binary(name(id(S1_)), assign, postfix(name(N), bracket(nil)))))
	     string_to_id("i" -> I_)
	     Mk_temp_id(ident(I_) -> I1_)
	     where(
	       expr(
		 binary(
		   name(id(S1_)),
		   assign,
		   postfix(name(N), bracket(list(name(id(I1_)), list(name(id(S1_)), nil))))
		 )
	       ) -> Body
	     )
	     C_Add_function_body(
	       for(
		 decl(
		   decl(
		     list(type(int), nil), list(with_init(dname(id(I1_)), assign(name(id(R1_)))), nil)
		   )
		 ),
		 binary(name(id(I1_)), ge, name(id(L1_))),
		 postfix(name(id(I1_)), dec),
		 compound(list(Body, nil))
	       )
	     )
	     C_Add_function_body(return(name(id(S1_))))
	   C_End_func_def(-> Fdef)
	   C_Decl_to_string(Fdef -> Scc)
	   WriteCcString(Scc)
	   Register_declared_id(Fid)
	 |]
	 Translate_value(T, L -> LE, LSs)
	 Translate_value(T, R -> RE, RSs)
	 where(postfix(name(id(Fid)), bracket(list(LE, list(RE, nil)))) -> E)
	 Concatenate_statements(LSs, RSs -> Ss)

  'rule' Translate_value(T, enum_set(_, Vs) -> E, Ss):
	 -- translate type to check defined
	 Translate_type(T -> _)
	 Length_vs(Vs -> K)
	 Debracket_maxtype(T -> infin_set(ET))
	 (|
	   ge(K, 2)
	   Replicate_type(ET, K -> XT)
	   where(TYPE_EXPR'product(XT) -> ET1)
	 ||
	   where(ET -> ET1)
	 |)
	 Translate_values(ET1, Vs -> Es, Ss)
	 Universal_type_id(T -> Tid)
	 Lookup_declared_type(Tid -> CT)
	 Type_name_to_c_name(CT -> N)
	 Mk_enum_call(N, Es -> E)

  'rule' Translate_value(T, comp_set(P, V, set_limit(_, TPs, R)) -> E, Ss):
	 -- translate type to check defined
	 Translate_type(T -> _)
	 Translate_comp_set(P, T, V, TPs, R -> E, Ss)

  'rule' Translate_value(T, ranged_list(P, L, R) -> E, Ss):
	 -- translate type to check defined
	 Translate_type(T -> _)
	 string_to_id("init_ranged_list" -> Fid)
	 [|
	   Not_yet_declared_id(Fid)
	   C_Begin_func_def(id(Fid))
	     Mk_List_id(-> ListId)
	     Universal_type_id(infin_list(int) -> Tid)
	     Lookup_declared_type(Tid -> CT)
	     Type_name_to_c_name(CT -> N)
	     C_Add_decl_specifier(storage(static))
	     C_Add_decl_specifier(type(CT))
	     -- args
	     C_Arg_decl_specifier(type(const))
	     C_Arg_decl_specifier(type(int))
	     string_to_id("l" -> L_)
	     Mk_temp_id(ident(L_) -> L1_)
	     C_Arg_declarator(dname(id(L1_)))
	     C_Arg_decl_specifier(type(const))
	     C_Arg_decl_specifier(type(int))
	     string_to_id("r" -> R_)
	     Mk_temp_id(ident(R_) -> R1_)
	     C_Arg_declarator(dname(id(R1_)))
	     -- body
	     C_Begin_decl()
	       C_Add_decl_specifier(type(CT))
	       string_to_id("lst" -> LST_)
	       Mk_temp_id(ident(LST_) -> LST1_)
	       C_Add_declarator(dname(id(LST1_)))
	     C_End_decl(-> D)
	     C_Add_function_body(decl(D))
	     C_Add_function_body(expr(binary(name(id(LST1_)), assign, postfix(name(N), bracket(nil)))))
	     string_to_id("i" -> I_)
	     Mk_temp_id(ident(I_) -> I1_)
	     where(
	       expr(
		 binary(
		   name(id(LST1_)),
		   assign,
		   postfix(name(N), bracket(list(name(id(I1_)), list(name(id(LST1_)), nil))))
		 )
	       ) -> Body
	     )
	     C_Add_function_body(
	       for(
		 decl(
		   decl(
		     list(type(int), nil), list(with_init(dname(id(I1_)), assign(name(id(R1_)))), nil)
		   )
		 ),
		 binary(name(id(I1_)), ge, name(id(L1_))),
		 postfix(name(id(I1_)), dec),
		 compound(list(Body, nil))
	       )
	     )
	     C_Add_function_body(return(name(id(LST1_))))
	   C_End_func_def(-> Fdef)
	   C_Decl_to_string(Fdef -> Scc)
	   WriteCcString(Scc)
	   Register_declared_id(Fid)
	 |]
	 Translate_value(int, L -> L1, LSs)
	 Translate_value(int, R -> R1, RSs)
	 where(postfix(name(id(Fid)), bracket(list(L1, list(R1, nil)))) -> E)
	 Concatenate_statements(LSs, RSs -> Ss)

  'rule' Translate_value(T, enum_list(_, Vs) -> E, Ss):
	 Type_matches_text(T)
	 Append_chars(Vs, literal(text("")) -> E, Ss)

  'rule' Translate_value(T, enum_list(_, Vs) -> E, Ss):
	 -- translate type to check defined
	 Translate_type(T -> _)
	 Length_vs(Vs -> K)
	 Debracket_maxtype(T -> infin_list(ET))
	 (|
	   ge(K, 2)
	   Replicate_type(ET, K -> XT)
	   where(TYPE_EXPR'product(XT) -> ET1)
	 ||
	   where(ET -> ET1)
	 |)
	 Translate_values(ET1, Vs -> Es, Ss)
	 Universal_type_id(T -> Tid)
	 Lookup_declared_type(Tid -> CT)
	 Type_name_to_c_name(CT -> N)
	 Mk_enum_call(N, Es -> E)

  'rule' Translate_value(T, comp_list(P, V, list_limit(_, B, VL, R)) -> E, Ss):
	 -- translate type to check defined
	 Translate_type(T -> _)
	 Translate_comp_list(P, T, V, B, VL, R -> E, Ss)

  'rule' Translate_value(T, enum_map(_, VPs) -> E, Ss):
	 -- translate type to check defined
	 Translate_type(T -> _)
	 Debracket_maxtype(T -> infin_map(DT, RT))
	 Translate_pairs(DT, RT, VPs -> Es, Ss)
	 Universal_type_id(T -> Tid)
--b
	(|	  
	  SQLWanted()
	  Is_table_type(Tid)
	  id_to_string(Tid -> S)	
	  Concatenate(S, "_tbl" -> Tb)
	  string_to_id(Tb -> Iq)
	  Ident_to_cts(Iq -> CT)
	  Type_name_to_c_name(CT -> N)
	  Mk_enum_map_call(N, Es -> E)
	||
	  Lookup_declared_type(Tid -> CT)
	  Type_name_to_c_name(CT -> N)
	  Mk_enum_map_call(N, Es -> E)
	|)	 
	
--e

  'rule' Translate_value(T, comp_map(P, VP, set_limit(_, TGL, R)) -> E, Ss):
	 -- translate type to check defined
	 Translate_type(T -> _)
	 Translate_comp_map(P, T, VP, TGL, R -> E, Ss)

  'rule' Translate_value(T, application(P, F, As:list(_, list(_, _))) -> E, Ss):
	 Rearrange_application(P, F, As -> V)
	 Translate_value(T, V -> E, Ss)

  'rule' Translate_value(T, application(P, F, list(A, nil)) -> E, Ss):
	 (|
	   where(F -> val_occ(_, I, _))
	   I'Def -> Def
	   I'Type -> FT
	 || -- allow other expressions if uniquely typed
	   Make_results(F -> list(result(FT,_,_,_,_),nil))
	   where(VALUE_DEFINITION'no_def -> Def)
	 |)
	 Translate_value(FT, F -> FE, FSs)
	 Debracket_maxtype(FT -> MFT)
	 (|
	   where(MFT -> fun(PT, _, result(RT,_,_,_,_)))
	 ||
	   where(MFT -> infin_map(PT, RT))
	 ||
	   where(MFT -> infin_list(RT))
	   where(TYPE_EXPR'int -> PT)
	 |)
	 Actual_parm_to_exprs(PT, A -> Ps, PSs)
	 (|
	   where(MFT -> fun(_,_,_))
	   (|
	     (|
	       where(Def -> expl_fun(list(form_parm(_, Bs),_),_,_,_,_,_))
	     ||
	       where(Def -> impl_fun(list(form_parm(_, Bs),_),_,_,_))
	     |)
	     Length_bs(Bs -> ParmCount)
	   ||
	     Type_is_product(PT -> XT)
	     Length_pr(XT -> ParmCount)
	   ||
	     where(1 -> ParmCount)
	   |)
	   where(A -> fun_arg(_, Vs))
	   Length_vs(Vs -> ActCount)
	   (|
	     (|
	       eq(ActCount, ParmCount)
	     ||
	       (| eq(ActCount, 0) || eq(ParmCount, 0) |)
	       -- allows for Unit type with no actuals
	       -- or with actuals but no formals
	     |)
	     where(C_POSTFIX'bracket(Ps) -> Args)
	     Concatenate_statements(FSs, PSs -> Ss)
	   || -- ParmCount > ActCount(=1)
	     where(Ps -> list(P1, nil))
	     -- need to decompose actual
	     Mk_temp_id(nil -> TempId)
	     Translate_type(PT -> PT1)
	     C_Begin_decl()
	       C_Add_decl_specifier(type(PT1))
	       C_Add_declarator(with_init(dname(id(TempId)), assign(P1)))
	     C_End_decl(-> D)
	     Decompose_actual(C_EXPR'name(id(TempId)), 1, ParmCount -> Ps1)
	     where(C_POSTFIX'bracket(Ps1) -> Args)
	     Concatenate_statements(FSs, PSs -> Ss1)
	     Append_statement(Ss1, decl(D) -> Ss)
	   ||
	     -- need to compose actuals
	     Universal_type_id(PT -> PTid)
	     Lookup_declared_type(PTid -> CT)
	     Type_name_to_c_name(CT -> N)
	     where(C_POSTFIX'bracket(list(postfix(name(N), bracket(Ps)),nil)) -> Args)
	     Concatenate_statements(FSs, PSs -> Ss)
	   |)
	 ||
	   -- map or list
	   (|
	     where(Ps -> list(P1, nil))
-- -1 now included in RSL_text.h
--	     (|
--	       where(MFT -> infin_list(char))
	       -- C++ strings indexed from zero
--	       string_to_id("1" -> One)
--	       where(index(binary(P1, minus, literal(int(One)))) -> Args)
--	     ||
	       where(index(P1)-> Args)
--	     |)
	   || -- domain type is a product
	     Universal_type_id(PT -> PTid)
	     Lookup_declared_type(PTid -> CT)
	     Type_name_to_c_name(CT -> N)
	     where(index(postfix(name(N), bracket(Ps))) -> Args)
	   |)
	   Concatenate_statements(FSs, PSs -> Ss)
	 |)
	 
	 (| -- change for map as database
	   SQLWanted()
	   where(MFT -> infin_map(_, RT1))
-- debug
-- Putmsg("Found a map application with result type ")
-- Print_type(RT1)
-- Putnl()
	   where(postfix(FE, Args) -> E1)
	   Translate_type(RT1 -> CRT)
	   String_to_RSL_name(CRT -> Nstr)
	   where(postfix(name(Nstr), bracket(list(E1, nil))) -> E)
	 ||
	   where(postfix(FE, Args) -> E)
	 |)

  'rule' Translate_value(T, quantified(P, Q, TPs, R) -> E, Ss):
	 Translate_quantified(P, Q, TPs, R -> E, Ss)

  'rule' Translate_value(T, if_expr(P, Cond, Then, _, nil, else(_,Else)) -> E, Ss):
	 Translate_value(bool, Cond -> Cond1, Ss1)
	 Translate_value(T, Then -> Th, ThSs)
	 Translate_value(T, Else -> El, ElSs)
	 (|
	   ne(T, unit)
	   eq(ThSs, nil)
	   eq(ElSs, nil)
	   where(C_EXPR'bracket(conditional(Cond1, Th, El)) -> E)
	   where(Ss1 -> Ss)
	 ||
	   (|
	     ne(T, unit)
	     C_Begin_decl()
	       Translate_type(T -> T1)
	       C_Add_decl_specifier(type(T1))
	       Mk_temp_id(nil -> TempId)
	       C_Add_declarator(dname(id(TempId)))
	     C_End_decl(-> TempDecl)
	     Append_statement(Ss1, decl(TempDecl) -> Ss11)
	     where(ident(TempId) -> OptId)
	     where(C_EXPR'name(id(TempId)) -> E)
	   ||
	     where(Ss1 -> Ss11)
	     where(OPT_IDENT'nil -> OptId)
	     where(C_EXPR'nil -> E)
	   |)
	   Terminate_expr(OptId, Th, ThSs -> SsThen)
	   Terminate_expr(OptId, El, ElSs -> SsElse)
	   where(C_STATEMENT'if(Cond1, compound(SsThen), compound(SsElse)) -> S)
	   Append_statement(Ss11, S -> Ss)
	 |)

  'rule' Translate_value(T, X:if_expr(P, Cond, Then, RT, Elsif, Else) -> E, Ss):
	 (| eq(T, unit) ||
	    Make_results(X -> list(result(_,nil,nil,nil,nil),_)) |)
	 -- either unit type or pure,
	 -- so worth trying to deal with elsifs as nested ifs.
	 -- Nesting is less efficient in general, since each if will use a
	 -- new local variable, but better if we don't need local variables
	 where(Elsif -> list(elsif(P1, Cond1, Then1, _), Elsifs))
	 Translate_value(T, if_expr(P, Cond, Then, RT, nil, else(P1, if_expr(P1, Cond1, Then1, RT, Elsifs, Else))) -> E, Ss)

  'rule' Translate_value(T, if_expr(P, Cond, Then, _, Elsif, Else) -> E, Ss):
	 Translate_value(bool, Cond -> Cond1, Ss1)
	 Translate_value(T, Then -> Th, ThSs)
	 (|
	   ne(T, unit)
	   C_Begin_decl()
	     Translate_type(T -> T1)
	     C_Add_decl_specifier(type(T1))
	     Mk_temp_id(nil -> TempId)
	     C_Add_declarator(dname(id(TempId)))
	   C_End_decl(-> TempDecl)
	   Append_statement(Ss1, decl(TempDecl) -> Ss11)
	   where(ident(TempId) -> OptId)
	   where(C_EXPR'name(id(TempId)) -> E)
	 ||
	   where(Ss1 -> Ss11)
	   where(OPT_IDENT'nil -> OptId)
	   where(C_EXPR'nil -> E)
	 |)
	 Terminate_expr(OptId, Th, ThSs -> SsThen)
	 Translate_elsif_branches(T, OptId, Elsif, Else -> SsElse)
	 where(C_STATEMENT'if(Cond1, compound(SsThen), compound(SsElse)) -> S)
	 Append_statement(Ss11, S -> Ss)

  'rule' Translate_value(_, ass_occ(P, VarId, OptQ, V) -> E, Ss):
	 VarId'Ident -> Id
	 VarId'Type -> T
	 VarId'Qualifier -> Is
	 Translate_value(T, V -> E1, Ss1)
	 Debracket_maxtype(T -> T1)
	 -- get best type
	 Type_of_val(V, T1 -> T2)
	 New_value_id(P, id_op(Id) -> I1)
	 I1'Type <- T2
-- debug
-- Print_id(Id)
-- Putmsg(" of type ")
-- Print_type(T)
	 Isin_subtype(val_occ(P, I1, nil), T -> Pred)
-- Putmsg(" gives predicate ")
-- Print_expr(Pred)
-- Putmsg(" for value ")
-- Print_expr(V)
-- Putmsg(" of best type ")
-- Print_type(T2)
-- Putnl()
	 Simplify(Pred -> Pred1)
	 Translate_id(id_op(Id), OptQ, Is -> N)
	 (|
	   eq(Pred1, no_val)
	   where(binary(name(N), assign, E1) -> E)
	   where(Ss1 -> Ss)
	 ||
	   Translate_type(T -> CT)
	   (|
	     -- if Pred1 is a function application with one argument
	     -- matching Id_or_op no need to generate subtype predicate
	     where(Pred1 -> application(_, FP:val_occ(_, IP, _), list(fun_arg(_, list(VP, nil)), nil)))
	     Matches_binding(VP, single(P, id_op(Id)))
	     IP'Type -> PT
	     Translate_value(PT, FP -> PF, nil)
	     where(C_STATEMENTS'nil -> Ssp)
	   ||
	     WriteHCcString("\n#ifdef RSL_pre\n")
	     Mk_temp_id(nil -> TempId)
	     Mk_temp_id(nil -> NSId)
	     C_id_to_string(NSId -> NS)
	     Concatenate3("\nnamespace ", NS, " {\n// namespace for subtype predicate\n" -> Sp1)
	     WriteHCcString(Sp1)
	     Current_parms -> CPS
	     Current_parm_types -> CPTS
	     Define_current_parms(CPS, CPTS, NSId -> Ssp)
	     Make_predicate_def(P, CT, TempId, Id, Pred1 -> Pdef)
	     C_Decl_to_string_h(Pdef -> PSh)	WriteHString(PSh)
	     C_Decl_to_string(Pdef -> PScc)	WriteCcString(PScc)
	     Concatenate3("\n} // end of namespace ", NS, "\n\n" -> Sp2)
	     WriteHCcString(Sp2)
	     WriteHCcString("#endif //RSL_pre\n\n")
	     where(C_EXPR'name(qualified(id(TempId), list(NSId, nil))) -> PF)
	   |)
	   string_to_id("RSL_check" -> Cid)
	   PosAsString(P -> PS)
	   id_to_string(Id -> IdS)
	   Concatenate(PS, " Assigned value " -> ST1)
	   RSL_to_string_name(CT -> Rtsn)
	   where(postfix(name(Rtsn), bracket(list(E1, nil))) -> RTSApp)
	   where(binary(text_literal(ST1), plus, RTSApp) -> SE1)
	   Concatenate3(" of variable ", IdS, " not in subtype" -> ST2)
	   where(binary(SE1, plus, text_literal(ST2)) -> SE2)    
	   where(cpp(ifdef("RSL_pre")) -> S0)
	   where(expr(binary(name(N), assign,
			postfix(name(template(Cid, list(CT, nil))),
			 bracket(
			   list(PF,
			   list(E1,
			   list(SE2, nil))))))) -> S1)
	   where(cpp(else("RSL_pre")) -> S2)
	   where(expr(binary(name(N), assign, E1)) -> S3)
	   where(cpp(endif("RSL_pre")) -> S4)
	   where(C_STATEMENTS'list(S1, list(S2, list(S3, list(S4, nil)))) -> Ss2)
	   Concatenate_statements(Ss1, list(S0, Ssp) -> Ss11)
	   Concatenate_statements(Ss11, Ss2 -> Ss)
	   where(C_EXPR'nil -> E)
	 |)

  'rule' Translate_value(_, var_occ(_, VarId, OptQ) -> E, nil):
	 VarId'Ident -> Id
	 VarId'Type -> T
	 VarId'Qualifier -> Is
	 Translate_id(id_op(Id), OptQ, Is -> N)
	 where(C_EXPR'name(N) -> E)

  'rule' Translate_value(_, pre_occ(_, VarId, _) -> name(id(PreId)), nil):
	 VarId'Ident -> Id
	 id_to_string(Id -> Str)
	 Concatenate(Str, "_rsL" -> Str1)
	 string_to_id(Str1 -> PreId)

  'rule' Translate_value(T, V -> E, Ss):
	 where(V -> case_expr(P, V1, _, CS))
	 Make_results(V1 -> list(result(T1,_,_,_,_),_))
	 Translate_value(T1, V1 -> VE, Ss0)
	 Translate_type(T1 -> T11)
	 Mk_temp_id(nil -> VId)
	 C_Begin_decl()
	   C_Add_decl_specifier(type(T11))
	   C_Add_declarator(with_init(dname(id(VId)), assign(VE)))
	 C_End_decl(-> D)
	 Append_statement(Ss0, decl(D) -> Ss1)
	 (|
	   ne(T, unit)
	   Translate_type(T -> CT)
	   Mk_temp_id(nil -> TempId)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(CT))
	     C_Add_declarator(dname(id(TempId)))
	   C_End_decl(-> TempDecl)
	   Append_statement(Ss1, decl(TempDecl) -> Ss2)
	   Translate_case_branches(P, ident(TempId), name(id(VId)), T1, T, CS -> S)
	   Append_statement(Ss2, S -> Ss)
	   where(C_EXPR'name(id(TempId)) -> E)
	 ||
	   Translate_case_branches(P, nil, name(id(VId)), T1, T, CS -> S)
	   where(C_EXPR'nil -> E)
	   Append_statement(Ss1, S -> Ss)
	 |)

  'rule' Translate_value(_, while_expr(_, V1, V2) -> nil, Ss):
	 Translate_value(bool, V1 -> Cond, Ss1)
	 Translate_value(unit, V2 -> Body, Ss2)
	 Append_statement(Ss1, if(unary(not, bracket(Cond)), break, nil) -> Ss11)
	 (|
	   eq(Body, nil)
	   where(Ss2 -> Ss21)
	 ||
	   Append_statement(Ss2, expr(Body) -> Ss21)
	 |)
	 Concatenate_statements(Ss11, Ss21 -> Ss3)
	 where(C_STATEMENTS'list(for(nil, nil, nil, compound(Ss3)), nil) -> Ss)

  'rule' Translate_value(_, until_expr(_, V1, V2) -> nil, Ss):
	 Translate_value(unit, V1 -> Body, Ss1)
	 Translate_value(bool, V2 -> Cond, Ss2)
	 (|
	   eq(Body, nil)
	   where(Ss1 -> Ss11)
	 ||
	   Append_statement(Ss1, expr(Body) -> Ss11)
	 |)
	 Concatenate_statements(Ss11, Ss2 -> Ss3)
	 where(C_STATEMENTS'list(do_while(compound(Ss3), unary(not, bracket(Cond))), nil) -> Ss)

  'rule' Translate_value(_, for_expr(_, LL, V) -> nil, list(compound(Ss), nil)):
	 Translate_for_expr(LL, V -> Ss)

  'rule' Translate_value(T, V -> E, Ss):
	 where(V -> stmt_infix(P, _, Comb, _))
	 (|
	   eq(Comb, sequence)
	   Translate_expr_sequence(T, V, nil -> Ss, E)
	 ||
	   Puterror(P)
	   Putmsg("Cannot translate the combinator ")
	   Print_combinator(Comb)
	   Putnl()
	   where(C_EXPR'nil -> E)
	   where(C_STATEMENTS'nil -> Ss)
	 |)

  'rule' Translate_value(T, let_expr(P, list(Def, nil), V) -> E, Ss):
	 Let_def_to_decls(Def -> Ss1)
	 Translate_value(T, V -> E1, Ss2)
	 Current_parms -> list(_, Bss)
	 Current_parms <- Bss
	 Current_parm_types -> list(_, Tss)
	 Current_parm_types <- Tss
	 Concatenate_statements(Ss1, Ss2 -> Ss3)
	 (|
	   ne(T, unit)
	   where(E1 -> E)
	   where(Ss3 -> Ss)
	 ||
	   Append_statement(Ss3, expr(E1) -> Ss)
	   where(C_EXPR'nil -> E)
	 |)

  'rule' Translate_value(T, let_expr(P, list(Def, Defs), V) -> E, Ss):
	 Translate_value(T, let_expr(P, list(Def, nil),
					let_expr(P, Defs, V)) -> E, Ss)
	 

  'rule' Translate_value(_, pre_name(P, N) -> name(id(Msg)), nil):
	 Puterror(P)
	 Putmsg("Cannot translate prename: ")
	 Print_name(N)
	 Putnl()
	 string_to_id("/*Cannot translate prename*/" -> Msg)

  'rule' Translate_value(T, V -> E, Ss):
	 where(V -> env_local(P, DS, CE, V1))
	 Only_vars_and_constants(DS -> Bs, Ts)
	 Current -> C
	 Current <- current_env(CE, C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 Local_depth -> N
	 Local_depth <- N+1
--	 Define_local_constant_decls(DS, nil -> Ss0)
--	 Define_local_variable_decls(DS, Ss0 -> Ss1)
	 Current_parms -> CPS
	 Current_parms <- list(Bs, CPS)
	 Current_parm_types -> CPTS
	 Current_parm_types <- list(Ts, CPTS)
	 Collect_value_decls(DS, nil -> Vids)
	 Define_constants(Vids, nil, nil -> nil, Decls1, Vs1)
	 -- returns functions to do, declarations, and assignments to constants
	 Define_vars(DS -> Decls2, Vs2)
	 Concatenate_decls(Decls1, Decls2 -> Decls)
	 Decls_to_statements(Decls -> Ss1)
	 Concatenate_values(Vs1, Vs2 -> Vs)
	 Translate_assignments(Vs -> Ss2)
	 Concatenate_statements(Ss1, Ss2 -> Ss12)
	 Translate_value(T, V1 -> E, Ss3)
	 Concatenate_statements(Ss12, Ss3 -> Ss)
	 Current_parms <- CPS
	 Current_parm_types <- CPTS
	 Current <- C
	 Extend_paths <- Paths
	 Local_depth <- N
	 
  'rule' Translate_value(T, V -> E, Ss):
	 where(V -> env_local(P, DS, CE, V1))
	 [|
	   Current_funs -> list(I, _)
	   Collect_fun_ids(V, nil -> Is)
	   Isin_value_ids(I, Is)
	   Puterror(P)
	   Putmsg("Recursive function containing local expression\n")
	 |]
	 Current -> C
	 Current <- current_env(CE, C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil,Paths)
	 Local_depth -> N
	 Local_depth <- N+1
	 Mk_temp_id(nil -> TempId)
	 C_id_to_string(TempId -> S)
	 Concatenate3("\nnamespace ", S, " {\n// namespace for local expression\n" -> S1)
	 WriteHCcString(S1)
	 Define_local_parms(TempId -> Ss00)
	 Translate_type_decls(DS, nil -> Ids)
	 Declared_types -> Done
	 Subtract_types(Ids, Done -> Ids1)
	 Translate_type_ids(Ids1, nil, Done, nil)
	 Translate_variant_components(Ids1)
	 Translate_object_decls(DS)
	 Collect_value_decls(DS, nil -> Vids)
	 Define_constants(Vids, nil, nil -> Fids, Decls1, Vs1)
	 -- returns functions to do, declarations, and assignments to constants
	 Define_vars(DS -> Decls2, Vs2)
	 C_Decls_to_string_h(Decls1 -> Sh1)	WriteHString(Sh1)
	 C_Decls_to_string(Decls1 -> Scc1)	WriteCcString(Scc1)
	 C_Decls_to_string_h(Decls2 -> Sh2)	WriteHString(Sh2)
	 C_Decls_to_string(Decls2 -> Scc2)	WriteCcString(Scc2)
	 Concatenate_values(Vs1, Vs2 -> Vs)
	 Translate_assignments(Vs -> Ss01)
	 Concatenate_statements(Ss00, Ss01 -> Ss0)
	 Translate_value_ids(Fids, nil, nil)
	 Concatenate("\n} // end of namespace ", S -> S2)
	 WriteHCcString(S2)
	 Concatenate3("\nusing namespace ", S, ";\n" -> S3)
	 WriteHCcString(S3)
	 Translate_value(T, V1 -> E, Ss1)
	 Concatenate_statements(Ss0, Ss1 -> Ss)
	 Current <- C
	 Extend_paths <- Paths
	 Local_depth <- N

  'rule' Translate_value(_, skip -> literal(unit), nil):
  
  'rule' Translate_value(T, V -> E, Ss):
	 Maxtype(T -> T1)
	 ne(T, T1)
	 Translate_value(T1, V -> E, Ss)

  'rule' Translate_value(T, V -> name(id(Msg)), nil):
	 Putmsg("Cannot translate this value expression:\n")
	 Print_expr(V)
	 Putmsg(" of type ")
	 Print_type(T)
	 Putnl()
	 string_to_id("/*Cannot translate this value expression*/" -> Msg)

'action' Translate_values(TYPE_EXPR, VALUE_EXPRS -> C_EXPRS, C_STATEMENTS)

  'rule' Translate_values(T, Vs -> Es, Ss):
	 (|
	   Readonly_exprs(Vs)
	   where(readonly -> RO)
	 ||
	   where(READONLY'nil -> RO)
	 |)
	 Translate_values1(T, Vs, RO -> Es, Ss)

'action' Translate_values1(TYPE_EXPR, VALUE_EXPRS, READONLY -> C_EXPRS, C_STATEMENTS)

  'rule' Translate_values1(product(list(T, nil)), list(V, nil), RO -> Es, Ss):
	 Translate_values1(T, list(V, nil), RO -> Es, Ss)

  'rule' Translate_values1(T, list(V, nil), RO -> list(E, nil), Ss):
	 Translate_value(T, V -> E, Ss)

  'rule' Translate_values1(PT, list(V, Vs), RO -> list(E, Es), Ss):
	 Type_is_product(PT -> list(T, Ts))
	 Translate_value(T, V -> E1, Ss1)
	 (|
	   (| eq(RO, readonly) || Pure_expr(V) |)
	   where(E1 -> E)
	   where(Ss1 -> Ss11)
	 ||
	   Translate_type(T -> T1)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(T1))
	     Mk_temp_id(nil -> TempId)
	     C_Add_declarator(with_init(dname(id(TempId)), assign(E1)))
	   C_End_decl(-> D)
	   Append_statement(Ss1, decl(D) -> Ss11)
	   where(C_EXPR'name(id(TempId)) -> E)
	 |)
	 Translate_values1(TYPE_EXPR'product(Ts), Vs, RO -> Es, Ss2)
	 Concatenate_statements(Ss11, Ss2 -> Ss)

  'rule' Translate_values1(_, nil, _ -> nil, nil):

  'rule' Translate_values1(T, Vs, RO -> Es, Ss):
	 Length_vs(Vs -> N)
	 Make_product_type(T, N -> T1)
	 Translate_values1(T1, Vs, RO -> Es, Ss) 

'action' Translate_pairs(TYPE_EXPR, TYPE_EXPR, VALUE_EXPR_PAIRS -> C_EXPRS, C_STATEMENTS)

  'rule' Translate_pairs(DT, RT, VPs -> Es, Ss):
	 (|
	   Readonly_pairs(VPs)
	   where(readonly -> RO)
	 ||
	   where(READONLY'nil -> RO)
	 |)
	 Translate_pairs1(DT, RT, VPs, RO -> Es, Ss)

'action' Translate_pairs1(TYPE_EXPR, TYPE_EXPR, VALUE_EXPR_PAIRS, READONLY -> C_EXPRS, C_STATEMENTS)
  
  'rule' Translate_pairs1(DT, RT, list(pair(L,R), nil), RO -> list(LE, list(RE, nil)), Ss):
	 Translate_value(DT, L -> LE, Ss1)
	 Translate_value(RT, R -> RE, Ss2)
	 Concatenate_statements(Ss1, Ss2 -> Ss)

  'rule' Translate_pairs1(DT, RT, list(pair(L,R), VPs), RO -> list(LE, list(RE, Es)), Ss):
	 Translate_value(DT, L -> LE1, Ss1)
	 (|
	   (| eq(RO, readonly) || Pure_expr(L) |)
	   where(LE1 -> LE)
	   where(Ss1 -> Ss11)
	 ||
	   Translate_type(DT -> DT1)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(DT1))
	     Mk_temp_id(nil -> LTempId)
	     C_Add_declarator(with_init(dname(id(LTempId)), assign(LE1)))
	   C_End_decl(-> D)
	   Append_statement(Ss1, decl(D) -> Ss11)
	   where(C_EXPR'name(id(LTempId)) -> LE)
	 |)
	 Translate_value(RT, R -> RE1, Ss2)
	 (|
	   (| eq(RO, readonly) || Pure_expr(R) |)
	   where(RE1 -> RE)
	   where(Ss2 -> Ss21)
	 ||
	   Translate_type(RT -> RT1)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(RT1))
	     Mk_temp_id(nil -> RTempId)
	     C_Add_declarator(with_init(dname(id(RTempId)), assign(RE1)))
	   C_End_decl(-> D)
	   Append_statement(Ss2, decl(D) -> Ss21)
	   where(C_EXPR'name(id(RTempId)) -> RE)
	 |)
	 Translate_pairs1(DT, RT, VPs, RO -> Es, Ss3)
	 Concatenate_statements(Ss11, Ss21 -> Ss12)
	 Concatenate_statements(Ss12, Ss3 -> Ss)

  'rule' Translate_pairs1(_, _, nil, _ -> nil, nil):

'action' Replicate_type(TYPE_EXPR, INT -> PRODUCT_TYPE)

  'rule' Replicate_type(_, N -> nil):
	 eq(N, 0)

  'rule' Replicate_type(T, N -> list(T, Ts)):
	 Replicate_type(T, N-1 -> Ts)

'condition' Readonly_pairs(VALUE_EXPR_PAIRS)

  'rule' Readonly_pairs(list(pair(L,R), VPs)):
	 Readonly_expr(L)
	 Readonly_expr(R)
	 Readonly_pairs(VPs)

  'rule' Readonly_pairs(nil):

'condition' Readonly_exprs(VALUE_EXPRS)

  'rule' Readonly_exprs(list(V, Vs)):
	 Readonly_expr(V)
	 Readonly_exprs(Vs)

  'rule' Readonly_exprs(nil):

'condition' Readonly_expr(VALUE_EXPR)

  'rule' Readonly_expr(V):
	 Make_results(V -> Rs)
	 Readonly_results(Rs)

'condition' Readonly_results(RESULTS)

  'rule' Readonly_results(list(result(_,_,nil,nil,nil), Rs)):
	 Readonly_results(Rs)

  'rule' Readonly_results(nil):
	 
'condition' Pure_expr(VALUE_EXPR)

  'rule' Pure_expr(V):
	 Make_results(V -> Rs)
	 Pure_results(Rs)

'condition' Pure_results(RESULTS)

  'rule' Pure_results(list(result(_,nil,nil,nil,nil), Rs)):
	 Pure_results(Rs)

  'rule' Pure_results(nil):
	 

'condition' Simple_type(TYPE_EXPR)

  'rule' Simple_type(bool):
  'rule' Simple_type(char):
  'rule' Simple_type(nat):
  'rule' Simple_type(int):
  'rule' Simple_type(bool):
  'rule' Simple_type(real):

'action' Define_temp_fun(POS, BINDING, TYPE_EXPR, VALUE_EXPR, TYPE_EXPR,
			 C_NAME, C_STATEMENTS, OPT_IDENT
			 -> C_EXPR, C_DECL, OPT_IDENT)

-- defines a function -\ Bid : TT :- V if necessary, and returns its
-- name as GF and definition as Gdef
-- Oid is a namespace name if needed, ditto Oid1
-- BId is an identifier for B, a temporary if B is a product, when 
-- Ss are the statements to define the identifiers in B
  'rule' Define_temp_fun(P, B, TT, V, T, BId, Ss, Oid -> GF, Gdef, Oid1):
	 (|
	   -- if V is a function application with one argument
	   -- matching B no need to generate temporary function
	   where(V -> application(_, F:val_occ(_, IF, _), list(fun_arg(_, list(VP, nil)), nil)))
	   Matches_binding(VP, B)
	   IF'Type -> FT
	   where(FT -> fun(_,_,_)) -- not list or map application
	   Translate_value(FT, F -> GF, nil)
	   where(Oid -> Oid1)
	   where(C_DECL'nil -> Gdef)
	 ||
	   -- if V instantiates B, use identity function
	   Matches_binding(V, B)
	   RSL_identity -> GN
	   where(fun(TT,total,result(TT,nil,nil,nil,nil)) -> ITT)
	   Universal_type_id(ITT -> UITT)
	   (|
	     Lookup_declared_type(UITT -> CITT)
	   ||
	     -- declare at top level
	     -- for reuse in different namespaces
	     Close_namespaces_h()
	     Translate_type(ITT -> CITT)
	     Open_namespaces_h()
	   |)
	   where(cast(UITT, name(GN)) -> GF)
	   where(Oid -> Oid1)
	   where(C_DECL'nil -> Gdef)
	 ||
	   -- if V is just "true", use RSL_true
	   where(V -> literal_expr(_, bool_true))
	   RSL_true -> PN
	   where(fun(TT,total,result(bool,nil,nil,nil,nil)) -> ITT)
	   Universal_type_id(ITT -> UITT)
	   (|
	     Lookup_declared_type(UITT -> CITT)
	   ||
	     -- declare at top level
	     -- for reuse in different namespaces
	     Close_namespaces_h()
	     Translate_type(ITT -> CITT)
	     Open_namespaces_h()
	   |)
	   where(cast(UITT, name(PN)) -> GF)
	   where(Oid -> Oid1)
	   where(C_DECL'nil -> Gdef)
	 ||
	   (|
	     where(Oid -> ident(NSId))
	     where(Oid -> Oid1)
	   ||
	     Mk_temp_id(nil -> NSId)
	     where(ident(NSId) -> Oid1)
	   |)
	   Translate_arg(TT -> TT1)
	   Mk_temp_id(nil -> Gid)
	   C_Begin_func_def(id(Gid))
	     Translate_type(T -> T1)
	     C_Add_decl_specifier(type(T1))
	     C_Arg_decl_specifier(type(const))
	     C_Arg_decl_specifier(type(TT1))
	     C_Arg_declarator(dname(BId))
	     Translate_function_body(P, id_op(Gid), nil, unit, T, V, nil, nil, nil, nil)
	     C_Prefix_function_body(Ss)
	   C_End_func_def(-> Gdef)
	   where(C_EXPR'name(qualified(id(Gid),list(NSId,nil))) -> GF)
	 |)

'condition' Translate_comp_set(POS, TYPE_EXPR, VALUE_EXPR, TYPINGS, RESTRICTION -> C_EXPR, C_STATEMENTS)

-- Comprehensions involve defining extra functions.
-- To avoid a recursive call between the extra functions
-- being initialised and the evaluation of the set,
-- the set is assigned to an extra variable.
  'rule' Translate_comp_set(P0, TS, V, TGL, R -> E, Ss):
	 (|
	   Type_is_set(TS -> TSE)
	   where(TGL -> list(TG, nil))
	   Split_typing(TG -> B, TT)
	   Split_restriction(exists, R, B, TT -> SLM, T, Pred)
	   [|
	     Current_funs -> list(I, _)
	     Collect_fun_ids(V, nil -> Is0)
	     Collect_fun_ids(Pred, Is0 -> Is1)
	     Isin_value_ids(I, Is1)
	     Puterror(P0)
	     Putmsg("Recursion through comprehended set\n")
	   |]
	   Translate_value(T, SLM -> E1, Ss1)
	   (|
	     where(B -> single(P, id_op(Id)))
	     where(BINDINGS'list(B, nil) -> Bs)
	     where(local_id(P,Id) -> BId)
	     where(C_STATEMENTS'nil -> Ss2)
	     where(PRODUCT_TYPE'list(TT, nil) -> Ts)
	   ||
	     where(B -> product(_, Bs))
	     Mk_temp_id(nil -> TempId)
	     where(C_NAME'id(TempId) -> BId)
	     Debracket_maxtype(TT -> TTm)
	     Type_is_product(TTm -> Ts)
	     Product_binding_to_decls(name(id(TempId)), Ts, Bs -> Ss2)
	   |)
	   Translate_type(TSE -> CT1)
	   (|
	     Type_is_set(T -> TE)
	     string_to_id("RSL_compss" -> Fid)
	     Translate_type(TE -> CT)
	     where(C_NAME'template(Fid, list(CT, list(CT1, nil))) -> FN)
	   ||
	     Type_matches_text(T)
	     string_to_id("RSL_compts" -> Fid)
	     where(C_NAME'template(Fid, list(CT1, nil)) -> FN)
	   ||
	     Type_is_list(T -> TE)
	     string_to_id("RSL_compls" -> Fid)
	     Translate_type(TE -> CT)
	     where(C_NAME'template(Fid, list(CT, list(CT1, nil))) -> FN)
	   ||
	     Type_is_map(T -> TD, TR)
	     Translate_type(TD -> CD)
	     Translate_type(TR -> CR)
--b    
	     (|
	        SQLWanted()
	        Universal_type_id(T -> Uid)
	        Is_table_type(Uid)
		string_to_id("RSL_compds" -> Fid)
		id_to_string(Uid -> S)
		Concatenate(S, "_tbl" -> Tb) string_to_id(Tb -> Iq)
		Ident_to_cts(Iq -> Tq)
		where(C_NAME'template(Fid, list(CD, list(CT1, list(CR,
		list(Tq, nil))))) -> FN)
	     ||
		string_to_id("RSL_compms" -> Fid)
		where(C_NAME'template(Fid, list(CD, list(CT1, list(CR,  nil)))) -> FN)
	     |)
--e
	   |)
	   Current_parms -> CPS
	   Current_parms <- list(Bs, CPS)
	   Current_parm_types -> CPTS
	   Current_parm_types <- list(Ts, CPTS)
	   Define_temp_fun(P0, B, TT, V, TSE, BId, Ss2, nil -> GF, Gdef, Oid1)
	   Define_temp_fun(P0, B, TT, Pred, bool, BId, Ss2, Oid1 -> PF, Pdef, Oid2)
	   Current_parms <- CPS
	   Current_parm_types <- CPTS
	   where(postfix(name(FN),
			 bracket(list(GF,
				 list(PF,
				 list(E1,nil))))) -> E2)
	   (|
	     eq(Gdef, nil)
	     eq(Pdef, nil)
	     where(Ss1 -> Ss)
	     where(E2 -> E)
	   ||
	     where(Oid2 -> ident(NSId))
	     C_id_to_string(NSId -> NS)
	     Concatenate3("\nnamespace ", NS, " {\n// namespace for comprehended set\n" -> S1)
	     WriteHCcString(S1)
	     Define_temp_vars(NSId -> Ss0)
	     [|
	       ne(Gdef, nil)
	       C_Decl_to_string_h(Gdef -> Sh)	WriteHString(Sh)
	       C_Decl_to_string(Gdef -> Scc)	WriteCcString(Scc)
	     |]
	     [|
	       ne(Pdef, nil)
	       C_Decl_to_string_h(Pdef -> Sh1)	WriteHString(Sh1)
	       C_Decl_to_string(Pdef -> Scc1)	WriteCcString(Scc1)
	     |]
	     Concatenate3("\n} // end of namespace ", NS, "\n\n" -> S2)
	     WriteHCcString(S2)
	     Concatenate_statements(Ss0, Ss1 -> Ss01)
	     Mk_temp_id(nil -> TempId)
	     where(C_NAME'id(TempId) -> EId)
	     where(C_EXPR'name(EId) -> E)
	     Translate_type(TS -> CTS)
	     C_Begin_decl()
	       C_Add_decl_specifier(type(CTS))
	       C_Add_declarator(with_init(dname(EId), assign(E2)))
	     C_End_decl(-> ED)
	     Append_statement(Ss01, decl(ED) -> Ss)
	   |)
	 ||
	   Puterror(P0)
	   Putmsg("Cannot translate comprehended sets in general: ignored")
	   Putnl()
	   where(C_EXPR'nil -> E)
	   where(C_STATEMENTS'nil -> Ss)
	 |)

'condition' Translate_comp_list(POS, TYPE_EXPR, VALUE_EXPR, BINDING, VALUE_EXPR, RESTRICTION -> C_EXPR, C_STATEMENTS)

  'rule' Translate_comp_list(P0, TL, V, B, VL, R -> E, Ss):
	 Type_is_list(TL -> TLE)
	 ne(TLE, unit) -- lists of unit involve reference to void that
		      -- g++ does not like
	 (|
	   where(R -> nil)
	   where(literal_expr(P0, bool_true) -> Pred)
	 ||
	   where(R -> restriction(_, Pred))
	 |)
	 [|
	   Current_funs -> list(I, _)
	   Collect_fun_ids(V, nil -> Is0)
	   Collect_fun_ids(Pred, Is0 -> Is1)
	   Isin_value_ids(I, Is1)
	   Puterror(P0)
	   Putmsg("Recursion through comprehended list\n")
	 |]
	 Make_results(VL -> list(result(TL1,_,_,_,_),_))
	 Type_is_list(TL1 -> TT)
	 Translate_value(TL1, VL -> E1, Ss1)
	 (|
	   where(B -> single(P, id_op(Id)))
	   where(BINDINGS'list(B, nil) -> Bs)
	   where(local_id(P,Id) -> BId)
	   where(C_STATEMENTS'nil -> Ss2)
	   where(PRODUCT_TYPE'list(TT, nil) -> Ts)
	 ||
	   where(B -> product(_, Bs))
	   Mk_temp_id(nil -> TempId)
	   where(C_NAME'id(TempId) -> BId)
	   Debracket_maxtype(TT -> TTm)
	   Type_is_product(TTm -> Ts)
	   Product_binding_to_decls(name(id(TempId)), Ts, Bs -> Ss2)
	 |)
	 Translate_type(TLE -> CT1)
	 (|
	   Type_matches_text(TL1)
	   (|
	     Type_matches_text(TL)
	     string_to_id("RSL_comptt" -> Fid)
	     where(C_NAME'id(Fid) -> FN)
	   ||
	     string_to_id("RSL_comptl" -> Fid)
	     where(C_NAME'template(Fid, list(CT1, nil)) -> FN)
	   |)
	 ||
	   (|
	     Type_matches_text(TL)
	     string_to_id("RSL_complt" -> Fid)
	     Translate_type(TT -> CT)
	     where(C_NAME'template(Fid, list(CT, nil)) -> FN)
	   ||
	     string_to_id("RSL_compll" -> Fid)
	     Translate_type(TT -> CT)
	     where(C_NAME'template(Fid, list(CT, list(CT1, nil))) -> FN)
	   |)
	 |)
	 Current_parms -> CPS
	 Current_parms <- list(Bs, CPS)
	 Current_parm_types -> CPTS
	 Current_parm_types <- list(Ts, CPTS)
	 Define_temp_fun(P0, B, TT, V, TLE, BId, Ss2, nil -> GF, Gdef, Oid1)
	 Define_temp_fun(P0, B, TT, Pred, bool, BId, Ss2, Oid1 -> PF, Pdef, Oid2)
	 Current_parms <- CPS
	 Current_parm_types <- CPTS
	 where(postfix(name(FN),
		       bracket(list(GF,
			       list(PF,
			       list(E1,nil))))) -> E2)
	 (|
	   eq(Gdef, nil)
	   eq(Pdef, nil)
	   where(Ss1 -> Ss)
	   where(E2 -> E)
	 ||
	   where(Oid2 -> ident(NSId))
	   C_id_to_string(NSId -> NS)
	   Concatenate3("\nnamespace ", NS, " {\n// namespace for comprehended list\n" -> S1)
	   WriteHCcString(S1)
	   Define_temp_vars(NSId -> Ss0)
	   [|
	     ne(Gdef, nil)
	     C_Decl_to_string_h(Gdef -> Sh)	WriteHString(Sh)
	     C_Decl_to_string(Gdef -> Scc)	WriteCcString(Scc)
	   |]
	   [|
	     ne(Pdef, nil)
	     C_Decl_to_string_h(Pdef -> Sh1)	WriteHString(Sh1)
	     C_Decl_to_string(Pdef -> Scc1)	WriteCcString(Scc1)
	   |]
	   Concatenate3("\n} // end of namespace ", NS, "\n\n" -> S2)
	   WriteHCcString(S2)
	   Concatenate_statements(Ss0, Ss1 -> Ss01)
	   Mk_temp_id(nil -> TempId)
	   where(C_NAME'id(TempId) -> EId)
	   where(C_EXPR'name(EId) -> E)
	   Translate_type(TL -> CTL)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(CTL))
	     C_Add_declarator(with_init(dname(EId), assign(E2)))
	   C_End_decl(-> ED)
	   Append_statement(Ss01, decl(ED) -> Ss)
	 |)

'condition' Translate_comp_map(POS, TYPE_EXPR, VALUE_EXPR_PAIR, TYPINGS, RESTRICTION -> C_EXPR, C_STATEMENTS)

  'rule' Translate_comp_map(P0, TS, pair(LV, RV), TGL, R -> E, Ss):
	 (|
	   Type_is_map(TS -> TD, TR)
	   where(TGL -> list(TG, nil))
	   Split_typing(TG -> B, TT)
	   Split_restriction(exists, R, B, TT -> SLM, T, Pred)
	   [|
	     Current_funs -> list(I, _)
	     Collect_fun_ids(LV, nil -> Is0)
	     Collect_fun_ids(RV, Is0 -> Is1)
	     Collect_fun_ids(Pred, Is1 -> Is2)
	     Isin_value_ids(I, Is2)
	     Puterror(P0)
	     Putmsg("Recursion through comprehended map\n")
	   |]
	   Translate_value(T, SLM -> E1, Ss1)
	   (|
	     where(B -> single(P, id_op(Id)))
	     where(BINDINGS'list(B, nil) -> Bs)
	     where(local_id(P,Id) -> BId)
	     where(C_STATEMENTS'nil -> Ss2)
	     where(PRODUCT_TYPE'list(TT, nil) -> Ts)
	   ||
	     where(B -> product(_, Bs))
	     Mk_temp_id(nil -> TempId)
	     where(C_NAME'id(TempId) -> BId)
	     Debracket_maxtype(TT -> TTm)
	     Type_is_product(TTm -> Ts)
	     Product_binding_to_decls(name(id(TempId)), Ts, Bs -> Ss2)
	   |)
	   Translate_type(TD -> CD1)
	   Translate_type(TR -> CR1)
	   (|
	     Type_is_set(T -> TE)
	     Translate_type(TE -> CT)
	     (|
	       SQLWanted()
	       Universal_type_id(TS -> Uid)
	       Is_table_type(Uid)
	       string_to_id("RSL_compsd" -> Fid)
	       id_to_string(Uid -> S)
	       Concatenate(S, "_tbl" -> Tb) string_to_id(Tb -> Iq)
	       Ident_to_cts(Iq -> Tq)
	       where(C_NAME'template(Fid, list(CT, list(CD1, list(CR1, list(Tq, nil))))) -> FN)
	     ||
	       string_to_id("RSL_compsm" -> Fid)
	       where(C_NAME'template(Fid, list(CT, list(CD1, list(CR1, nil)))) -> FN)
	     |)
	   ||
	     Type_matches_text(T)
	     (|
	       SQLWanted()
	       Universal_type_id(TS -> Uid)
	       Is_table_type(Uid)
	       string_to_id("RSL_comptd" -> Fid)
	       id_to_string(Uid -> S)
	       Concatenate(S, "_tbl" -> Tb) string_to_id(Tb -> Iq)
	       Ident_to_cts(Iq -> Tq)
	       where(C_NAME'template(Fid, list(CD1, list(CR1, list(Tq, nil)))) -> FN)
	     ||
	       string_to_id("RSL_comptm" -> Fid)
	       where(C_NAME'template(Fid, list(CD1, list(CR1, nil))) -> FN)
	     |)
	   ||
	     Type_is_list(T -> TE)
	     Translate_type(TE -> CT)
	     (|
	       SQLWanted()
	       Universal_type_id(TS -> Uid)
	       Is_table_type(Uid)
	       string_to_id("RSL_compld" -> Fid)
	       id_to_string(Uid -> S)
	       Concatenate(S, "_tbl" -> Tb) string_to_id(Tb -> Iq)
	       Ident_to_cts(Iq -> Tq)
	       where(C_NAME'template(Fid, list(CT, list(CD1, list(CR1, list(Tq, nil))))) -> FN)
	     ||
	       string_to_id("RSL_complm" -> Fid)
	       where(C_NAME'template(Fid, list(CT, list(CD1, list(CR1, nil)))) -> FN)
	     |)
	   ||
	     Type_is_map(T -> TD0, TR0)
	     Translate_type(TD0 -> CD0)
	     Translate_type(TR0 -> CR0)
	     (|
	       SQLWanted()
	       Universal_type_id(TS -> Uid)
	       Is_table_type(Uid)
	       (|
	         Universal_type_id(T -> Uid0)
		 Is_table_type(Uid0)
	         string_to_id("RSL_compdd" -> Fid)
	       ||
	         string_to_id("RSL_compmd" -> Fid)
	       |)
	       id_to_string(Uid -> S)
	       Concatenate(S, "_tbl" -> Tb) string_to_id(Tb -> Iq)
	       Ident_to_cts(Iq -> Tq)
	       where(C_NAME'template(Fid, list(CD0, list(CD1, list(CR0, list(CR1, list(Tq, nil)))))) -> FN)
	     ||
	       (|
	         SQLWanted()
	         Universal_type_id(T -> Uid0)
		 Is_table_type(Uid0)
	         id_to_string(Uid0 -> S)
	         Concatenate(S, "_tbl" -> Tb) string_to_id(Tb -> Iq)
	         Ident_to_cts(Iq -> Tq)
		 string_to_id("RSL_compdm" -> Fid)
	         where(C_NAME'template(Fid, list(CD0, list(CD1, list(CR0, list(CR1, list(Tq, nil)))))) -> FN)
	       ||
	         string_to_id("RSL_compmm" -> Fid)
	         where(C_NAME'template(Fid, list(CD0, list(CD1, list(CR0, list(CR1, nil))))) -> FN)
	       |)
	     |)
	   |)
	   Current_parms -> CPS
	   Current_parms <- list(Bs, CPS)
	   Current_parm_types -> CPTS
	   Current_parm_types <- list(Ts, CPTS)
	   Define_temp_fun(P0, B, TT, LV, TD, BId, Ss2, nil -> LGF, LGdef, Oid1)
	   Define_temp_fun(P0, B, TT, RV, TR, BId, Ss2, Oid1 -> RGF, RGdef, Oid2)
	   Define_temp_fun(P0, B, TT, Pred, bool, BId, Ss2, Oid2 -> PF, Pdef, Oid3)
	   Current_parms <- CPS
	   Current_parm_types <- CPTS
	   where(postfix(name(FN),
			 bracket(list(LGF,
				 list(RGF,
				 list(PF,
				 list(E1,nil)))))) -> E2)
	   (|
	     eq(LGdef, nil)
	     eq(RGdef, nil)
	     eq(Pdef, nil)
	     where(Ss1 -> Ss)
	     where(E2 -> E)
	   ||
	     where(Oid3 -> ident(NSId))
	     C_id_to_string(NSId -> NS)
	     Concatenate3("\nnamespace ", NS, " {\n// namespace for comprehended map\n" -> S1)
	     WriteHCcString(S1)
	     Define_temp_vars(NSId -> Ss0)
	     [|
	       ne(LGdef, nil)
	       C_Decl_to_string_h(LGdef -> Sh)	WriteHString(Sh)
	       C_Decl_to_string(LGdef -> Scc)	WriteCcString(Scc)
	     |]
	     [|
	       ne(RGdef, nil)
	       C_Decl_to_string_h(RGdef -> Sh0)	WriteHString(Sh0)
	       C_Decl_to_string(RGdef -> Scc0)	WriteCcString(Scc0)
	     |]
	     [|
	       ne(Pdef, nil)
	       C_Decl_to_string_h(Pdef -> Sh1)	WriteHString(Sh1)
	       C_Decl_to_string(Pdef -> Scc1)	WriteCcString(Scc1)
	     |]
	     Concatenate3("\n} // end of namespace ", NS, "\n\n" -> S2)
	     WriteHCcString(S2)
	     Concatenate_statements(Ss0, Ss1 -> Ss01)
	     Mk_temp_id(nil -> TempId)
	     where(C_NAME'id(TempId) -> EId)
	     where(C_EXPR'name(EId) -> E)
	     Translate_type(TS -> CTS)
	     C_Begin_decl()
	       C_Add_decl_specifier(type(CTS))
	       C_Add_declarator(with_init(dname(EId), assign(E2)))
	     C_End_decl(-> ED)
	     Append_statement(Ss01, decl(ED) -> Ss)
	   |)
	 ||
	   Puterror(P0)
	   Putmsg("Cannot translate comprehended maps in general: ignored")
	   Putnl()
	   where(C_EXPR'nil -> E)
	   where(C_STATEMENTS'nil -> Ss)
	 |)


'condition' Translate_quantified(POS, QUANTIFIER, TYPINGS, RESTRICTION -> C_EXPR, C_STATEMENTS)

  'rule' Translate_quantified(P0, Q, TGL, R -> E, Ss):
	 (|
	   where(TGL -> list(TG, nil))
	   Split_typing(TG -> B, TT)
	   Split_restriction(Q, R, B, TT -> SLM, T, Pred)
	   [|
	     Current_funs -> list(I, _)
	     Collect_fun_ids(Pred, nil -> Is)
	     Isin_value_ids(I, Is)
	     Puterror(P0)
	     Putmsg("Recursion through quantified expression\n")
	   |]
	   Translate_value(T, SLM -> E1, Ss1)
	   (|
	     where(B -> single(P, id_op(Id)))
	     where(BINDINGS'list(B, nil) -> Bs)
	     where(local_id(P,Id) -> BId)
	     where(C_STATEMENTS'nil -> Ss2)
	     where(PRODUCT_TYPE'list(TT, nil) -> Ts)
	   ||
	     where(B -> product(_, Bs))
	     Mk_temp_id(nil -> TempId)
	     where(C_NAME'id(TempId) -> BId)
	     Debracket_maxtype(TT -> TTm)
	     Type_is_product(TTm -> Ts)
	     Product_binding_to_decls(name(id(TempId)), Ts, Bs -> Ss2)
	   |)
	   -- different names alls, allt etc really just for
	   -- Visual C++ compiler, and so is use of templates
	   (|
	     where(Q -> all)
	     (|
	       Type_is_set(T -> TE)
	       string_to_id("alls" -> Qid)
	       Translate_type(TE -> CT)
	       where(C_NAME'template(Qid, list(CT, nil)) -> QN)
	     ||
	       Type_matches_text(T)
	       string_to_id("allt" -> Qid)
	       where(C_NAME'id(Qid) -> QN)
	     ||
	       Type_is_list(T -> TE)
	       string_to_id("alll" -> Qid)
	       Translate_type(TE -> CT)
	       where(C_NAME'template(Qid, list(CT, nil)) -> QN)
	     ||
	       Type_is_map(T -> TD, TR)
	       string_to_id("allm" -> Qid)
	       Translate_type(TD -> CD)
	       Translate_type(TR -> CR)
	       where(C_NAME'template(Qid, list(CD, list(CR, nil))) -> QN)
	     |)
	   ||
	     where(Q -> exists)
	     (|
	       Type_is_set(T -> TE)
	       string_to_id("existss" -> Qid)
	       Translate_type(TE -> CT)
	       where(C_NAME'template(Qid, list(CT, nil)) -> QN)
	     ||
	       Type_matches_text(T)
	       string_to_id("existst" -> Qid)
	       where(C_NAME'id(Qid) -> QN)
	     ||
	       Type_is_list(T -> TE)
	       string_to_id("existsl" -> Qid)
	       Translate_type(TE -> CT)
	       where(C_NAME'template(Qid, list(CT, nil)) -> QN)
	     ||
	       Type_is_map(T -> TD, TR)
	       string_to_id("existsm" -> Qid)
	       Translate_type(TD -> CD)
	       Translate_type(TR -> CR)
	       where(C_NAME'template(Qid, list(CD, list(CR, nil))) -> QN)
	     |)
	   ||
	     where(Q -> exists1)
	     (|
	       Type_is_set(T -> TE)
	       string_to_id("exists1s" -> Qid)
	       Translate_type(TE -> CT)
	       where(C_NAME'template(Qid, list(CT, nil)) -> QN)
	     ||
	       Type_matches_text(T)
	       string_to_id("exists1t" -> Qid)
	       where(C_NAME'id(Qid) -> QN)
	     ||
	       Type_is_list(T -> TE)
	       string_to_id("exists1l" -> Qid)
	       Translate_type(TE -> CT)
	       where(C_NAME'template(Qid, list(CT, nil)) -> QN)
	     ||
	       Type_is_map(T -> TD, TR)
	       string_to_id("exists1m" -> Qid)
	       Translate_type(TD -> CD)
	       Translate_type(TR -> CR)
	       where(C_NAME'template(Qid, list(CD, list(CR, nil))) -> QN)
	     |)
	   |)
	   Current_parms -> CPS
	   Current_parms <- list(Bs, CPS)
	   Current_parm_types -> CPTS
	   Current_parm_types <- list(Ts, CPTS)
	   Define_temp_fun(P0, B, TT, Pred, bool, BId, Ss2, nil -> PF, Pdef, Oid)
	   Current_parms <- CPS
	   Current_parm_types <- CPTS
	   where(postfix(name(QN),
			 bracket(list(PF,
				 list(E1,nil)))) -> E)
	   (|
	     eq(Pdef, nil)
	     where(Ss1 -> Ss)
	   ||
	     where(Oid -> ident(NSId))
	     C_id_to_string(NSId -> NS)
	     Concatenate3("\nnamespace ", NS, " {\n// namespace for quantified expression\n" -> S1)
	     WriteHCcString(S1)
	     Define_temp_vars(NSId -> Ss0)
	     [|
	       ne(Pdef, nil)
	       C_Decl_to_string_h(Pdef -> Sh1)	WriteHString(Sh1)
	       C_Decl_to_string(Pdef -> Scc1)	WriteCcString(Scc1)
	     |]
	     Concatenate3("\n} // end of namespace ", NS, "\n\n" -> S2)
	     WriteHCcString(S2)
	     Concatenate_statements(Ss0, Ss1 -> Ss)
	   |)
	 ||
	   Puterror(P0)
	   Putmsg("Cannot translate quantified expressions in general: ignored")
	   Putnl()
	   where(C_EXPR'nil -> E)
	   where(C_STATEMENTS'nil -> Ss)
	 |)


	 
'action' Rearrange_application(POS, VALUE_EXPR, ACTUAL_FUNCTION_PARAMETERS -> VALUE_EXPR)

  'rule' Rearrange_application(P, F, list(A, nil) -> application(P, F, list(A, nil))):

  'rule' Rearrange_application(P, F, list(A, As) ->
	      application(P, application(P, F, list(A, nil)), As)) 

'action' Translate_elsif_branches(TYPE_EXPR, OPT_IDENT, ELSIF_BRANCHES, ELSE_BRANCH -> C_STATEMENTS)

  'rule' Translate_elsif_branches(T, OptId, list(elsif(P, Cond, Then,_), Elsifs), Else -> Ss):
	 Translate_value(bool, Cond -> Cond1, Ss1)
	 Translate_value(T, Then -> Th, ThSs)
	 Terminate_expr(OptId, Th, ThSs -> SsThen)
	 Translate_elsif_branches(T, OptId, Elsifs, Else -> SsElse)
	 where(C_STATEMENT'if(Cond1, compound(SsThen), compound(SsElse)) -> S)
	 Append_statement(Ss1, S -> Ss) 
 
  'rule' Translate_elsif_branches(T, OptId, nil, else(_, V) -> Ss):
	 Translate_value(T, V -> E, Ss1)
	 Terminate_expr(OptId, E, Ss1 -> Ss)

  'rule' Translate_elsif_branches(_, _, nil, nil -> nil)


'action' Terminate_expr(OPT_IDENT, C_EXPR, C_STATEMENTS -> C_STATEMENTS)

  'rule' Terminate_expr(ident(TempId), E, Ss1 -> Ss):
	 Append_statement(Ss1, expr(binary(name(id(TempId)), assign, E)) -> Ss)

  'rule' Terminate_expr(nil, E, Ss1 -> Ss):
	 Append_statement(Ss1, expr(E) -> Ss)


'action' Translate_expr_sequence(TYPE_EXPR, VALUE_EXPR, C_STATEMENTS -> C_STATEMENTS, C_EXPR)

  'rule' Translate_expr_sequence(T, stmt_infix(P, V1, Comb, V2), Ss0 -> Ss, E):
	 (|
	   eq(Comb, sequence)
	   Translate_value(unit, V1 -> E1, Ss1)
	   Concatenate_statements(Ss0, Ss1 -> Ss01)
	   Append_statement(Ss01, expr(E1) -> Ss2)
	   Translate_expr_sequence(T, V2, Ss2 -> Ss, E)
	 ||
	   Puterror(P)
	   Putmsg("Cannot yet translate this combinator, later expression ignored ")
	   Print_combinator(Comb)
	   Putnl()
	   where(Ss0 -> Ss)
	   where(C_EXPR'nil -> E)
	 |)
	 
  'rule' Translate_expr_sequence(T, V, Ss0 -> Ss, E):
	 Translate_value(T, V -> E, Ss1)
	 Concatenate_statements(Ss0, Ss1 -> Ss)

'action' Translate_built_in_op(OP, Value_id -> C_OP)

  'rule' Translate_built_in_op(div, I -> COp):
	 (|
	   Id_of_div_int -> I1
	   eq(I, I1)
	   where(C_OP'literal("RSL_DIV_INT") -> COp)
	 ||
	   Id_of_div_real -> I2
	   eq(I, I2)
	   where(C_OP'literal("RSL_DIV_REAL") -> COp)
	 ||
	   where(C_OP'div -> COp)
	 |)

  'rule' Translate_built_in_op(rem, I -> COp):
	 (|
	   Id_of_rem_int -> I1
	   eq(I, I1)
	   where(C_OP'literal("RSL_REM_INT") -> COp)
	 ||
	   where(C_OP'modulo -> COp)
	 |)

  'rule' Translate_built_in_op(exp, I -> COp):
	 (|
	   Id_of_exp_int -> I1
	   eq(I, I1)
	   where(C_OP'literal("RSL_EXP_INT") -> COp)
	 ||
	   Id_of_exp_real -> I2
	   eq(I, I2)
	   where(C_OP'literal("RSL_EXP_REAL") -> COp)
	 ||
	   where(C_OP'literal("EXP") -> COp)
	 |)

  'rule' Translate_built_in_op(Op, _ -> COp):
	 Translate_op(Op -> COp)

'action' Translate_op(OP -> C_OP)

  'rule' Translate_op(eq -> eq):
  'rule' Translate_op(neq -> neq):
  'rule' Translate_op(gt -> gt):
  'rule' Translate_op(lt -> lt):
  'rule' Translate_op(ge -> ge):
  'rule' Translate_op(le -> le):
  'rule' Translate_op(supset -> gt):
  'rule' Translate_op(subset -> lt):
  'rule' Translate_op(supseteq -> ge):
  'rule' Translate_op(subseteq -> le):
  'rule' Translate_op(plus -> plus):
  'rule' Translate_op(minus -> minus):
  'rule' Translate_op(mult -> mult):
  'rule' Translate_op(div -> div):
  'rule' Translate_op(inter -> mult):
  'rule' Translate_op(caret -> plus):
  'rule' Translate_op(union -> plus):
  'rule' Translate_op(override -> plus):
  'rule' Translate_op(rem -> modulo):
  'rule' Translate_op(Op -> literal(S)):
	 Op_name(Op -> S)

'action' Translate_prefix(OP, Value_id, OPT_QUALIFICATION, C_EXPR -> C_EXPR)

  'rule' Translate_prefix(Op, I, _, E -> unary(Cop, E)):
	 Built_in(Op, I)
	 Translate_prefix_op(Op -> Cop)

  'rule' Translate_prefix(Op, I, Q, E -> postfix(name(N), bracket(list(E, nil)))):
	 (|
	   Built_in(Op, I)
	   Prefix_to_fname(Op -> S)
	   string_to_id(S -> Fid)
	   where(C_NAME'id(Fid) -> N)
	 ||
	   I'Qualifier -> Is
	   Translate_id(op_op(Op), Q, Is -> N)
	 |)

'condition' Translate_prefix_op(OP -> C_OP)

  'rule' Translate_prefix_op(plus -> plus)
  'rule' Translate_prefix_op(minus -> minus)
  
'condition' Prefix_to_fname(OP -> STRING)

  'rule' Prefix_to_fname(abs -> "RSL_abs")
  'rule' Prefix_to_fname(int -> "RSL_int")
  'rule' Prefix_to_fname(real -> "real")
  'rule' Prefix_to_fname(card -> "card")
  'rule' Prefix_to_fname(len -> "len")
  'rule' Prefix_to_fname(inds -> "inds")
  'rule' Prefix_to_fname(elems -> "elems")
  'rule' Prefix_to_fname(hd -> "hd")
  'rule' Prefix_to_fname(tl -> "tl")
  'rule' Prefix_to_fname(dom -> "dom")
  'rule' Prefix_to_fname(rng -> "rng")

'condition' Translate_connective(CONNECTIVE -> C_OP)

  'rule' Translate_connective(or -> logical_or)
  'rule' Translate_connective(and -> logical_and)
  'rule' Translate_connective(not -> not)


'action' Translate_id(ID_OR_OP, OPT_QUALIFICATION, Object_ids -> C_NAME)

  'rule' Translate_id(Id_or_op, Q, Is -> N):
	 Id_or_op_to_id(Id_or_op -> Id)
	 (|
	   where(Is -> list(_,_))
	   Object_ids_to_idents(Is -> Ids)
	   where(C_NAME'qualified(id(Id), Ids) -> N)
	 ||
	   where(Q -> qualification(Obj))
	   Object_to_idents(Obj -> Ids)
	   where(C_NAME'qualified(id(Id), Ids) -> N)
	 ||
	   where(C_NAME'id(Id) -> N)
	 |)
	   
'action' Translate_type_id(IDENT, OPT_QUALIFICATION, Object_ids -> C_TYPE_SPECIFIER)

  'rule' Translate_type_id(Id, nil, nil -> named_type(Id)):

  'rule' Translate_type_id(Id, _, Is:list(_,_) -> qualified(named_type(Id), Ids)):
	 Object_ids_to_idents(Is -> Ids)

  'rule' Translate_type_id(Id, qualification(Obj), _ -> qualified(named_type(Id), Ids)):
	 Object_to_idents(Obj -> Ids)

'action' Append_chars(VALUE_EXPRS, C_EXPR -> C_EXPR, C_STATEMENTS)

  'rule' Append_chars(list(V, Vs), E0 -> E2, Ss):
	 Translate_value(char, V -> E1, Ss1)
	 Append_chars(Vs, binary(E0, plus, E1) -> E2, Ss2)
	 Concatenate_statements(Ss1, Ss2 -> Ss)

  'rule' Append_chars(nil, E -> E, nil):

'action' Mk_enum_call(C_NAME, C_EXPRS -> C_EXPR)

  'rule' Mk_enum_call(N, list(E, Es) -> postfix(name(N), bracket(list(E, list(E1, nil))))):
	 Mk_enum_call(N, Es -> E1)

  'rule' Mk_enum_call(N, nil -> postfix(name(N), bracket(nil))):

'action' Mk_enum_map_call(C_NAME, C_EXPRS -> C_EXPR)

  'rule' Mk_enum_map_call(N, list(L, list(R, Es)) -> postfix(name(N), bracket(list(L, list(R, list(E1, nil)))))):
	 Mk_enum_map_call(N, Es -> E1)

  'rule' Mk_enum_map_call(N, nil -> postfix(name(N), bracket(nil))):

'action' Mk_Product_id(INT -> IDENT)

  'rule' Mk_Product_id(N -> Id):
	 Int_to_string(N -> SN)
	 Concatenate("RSLProduct", SN -> S)
	 string_to_id(S -> Id)

'action' Mk_Set_id(-> IDENT)

  'rule' Mk_Set_id(-> Id):
	 string_to_id("RSLSet" -> Id)

'action' Mk_Map_id(-> IDENT)

  'rule' Mk_Map_id(-> Id):
	 string_to_id("RSLMap" -> Id)

'action' Mk_List_id(-> IDENT)

  'rule' Mk_List_id(-> Id):
	 string_to_id("RSLList" -> Id)

'action' Actual_parm_to_exprs(TYPE_EXPR, ACTUAL_FUNCTION_PARAMETER -> C_EXPRS, C_STATEMENTS)

  'rule' Actual_parm_to_exprs(T, fun_arg(_, Vs) -> Es, Ss):
	 -- C++ doesn't like bracketed arguments
	 De_bracket_args(Vs -> Vs1)
	 Translate_values(T, Vs1 -> Es, Ss)

'action' De_bracket_args(VALUE_EXPRS -> VALUE_EXPRS)

  'rule' De_bracket_args(list(V, Vs) -> list(V1, Vs1)):
	 De_bracket_arg(V -> V1)
	 De_bracket_args(Vs -> Vs1)

  'rule' De_bracket_args(nil -> nil):

'action' De_bracket_arg(VALUE_EXPR -> VALUE_EXPR)

  'rule' De_bracket_arg(bracket(_, V) -> V1):
	 De_bracket_arg(V -> V1)

  'rule' De_bracket_arg(V -> V):

'action' Translate_pattern(C_EXPR, TYPE_EXPR, PATTERN -> C_EXPR, C_STATEMENTS)

  'rule' Translate_pattern(E, _, literal_pattern(_, L) -> Cond, nil):
	 where(binary(E, eq, literal(L)) -> Cond)

  'rule' Translate_pattern(E, T, id_pattern(P, Id_or_op) -> nil, Ss):
	 (|
	   where(Id_or_op -> id_op(Id))
	   Translate_type(T -> CT)
	   where(local_id(P,Id) -> Id1)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(CT))
	     C_Add_declarator(with_init(dname(Id1), assign(E))) 
	   C_End_decl(-> D)
	   where(C_STATEMENTS'list(decl(D), nil) -> Ss)
	   Current_parms -> list(Bs, Bss)
	   Current_parms <- list(list(single(P, Id_or_op), Bs), Bss)
	   Current_parm_types -> list(Ts, Tss)
	   Current_parm_types <- list(list(T, Ts), Tss)
	 ||
	   Puterror(P)
	   Putmsg("INCOMPLETE: cannot translate this pattern: ")
	   Print_pattern(id_pattern(P, Id_or_op))
	   Putnl()
	   where(C_STATEMENTS'nil -> Ss)
	 |)
	 
  'rule' Translate_pattern(_, _, wildcard_pattern(_) -> nil, nil):

  'rule' Translate_pattern(E, T, product_pattern(_, Patts) -> Cond, Ss):
	 Debracket_maxtype(T -> Tm)
	 Type_is_product(Tm -> Ts)
	 Translate_product_patterns(E, Ts, Patts, 1 -> Cond, Ss)
	 
  'rule' Translate_pattern(E, T, enum_list(P1, Patts) -> Cond, Ss):
	 string_to_id("len" -> Fid)
	 where(postfix(name(id(Fid)), bracket(list(E, nil))) -> E1)
	 Length_ps(Patts -> N)
	 Int_to_string(N -> NS)
	 string_to_id(NS -> Nid)
	 where(binary(E1, eq, literal(int(Nid))) -> Cond1)
	 Type_is_list(T -> TE)
	 Translate_list_patterns(E, TE, Patts, 1 -> Cond2, Ss)
	 Conjoin(Cond1, Cond2 -> Cond)
	 
  'rule' Translate_pattern(E, T, conc_list(P1, Patts, Patt) -> Cond, Ss):
	 string_to_id("len" -> Fid)
	 where(postfix(name(id(Fid)), bracket(list(E, nil))) -> E1)
	 Length_ps(Patts -> N)
	 Int_to_string(N -> NS)
	 string_to_id(NS -> Nid)
	 where(binary(E1, ge, literal(int(Nid))) -> Cond1)
	 Type_is_list(T -> TE)
	 Translate_list_patterns(E, TE, Patts, 1 -> Cond2, Ss1)
	 string_to_id("tl_n" -> Fid1)
	 where(postfix(name(id(Fid1)), bracket(list(E, list(literal(int(Nid)),nil)))) -> E2)
	 Translate_pattern(E2, T, Patt -> Cond3, Ss2)
	 Conjoin(Cond2, Cond3 -> Cond23)
	 Conjoin(Cond1, Cond23 -> Cond)
	 Concatenate_statements(Ss1, Ss2 -> Ss)

  'rule' Translate_pattern(E, T, name_occ_pattern(P, I, Q) -> Cond, Ss):
	 Translate_value(T, val_occ(P, I, Q) -> E1, nil)
	 where(binary(E, eq, E1) -> Cond)
	 where(C_STATEMENTS'nil -> Ss)
	 
  'rule' Translate_pattern(E, T, record_occ_pattern(P, I, Q, Patts) -> Cond, Ss):
	 (|
	   Debracket_maxtype(T -> T1)
	   where(T1 -> defined(Tid, _))
	   (|
	     Tid'Type -> sort(variant(Rs))
	     Mk_tag_id(nil -> TagId1)
	     I'Ident -> id_op(Id)
	     I'Qualifier -> Is
	     Mk_tag_id(ident(Id) -> TagId2)
	     Translate_id(id_op(TagId2), Q, Is -> TN)
	     where(binary(postfix(E, dot(id(TagId1))), eq, name(TN)) -> Cond1)
	     Get_pattern_record(Rs, I -> R)
	     Translate_pattern_variant(E, R, I, Q, Patts -> Cond2, Ss)
	     Conjoin(Cond1, Cond2 -> Cond)
	   ||
	     Tid'Type -> sort(record(Cs))
	     Translate_pattern_record_components(E, Cs, Patts, 1 -> Cond, Ss)
	   |)
	 ||
	   Puterror(P)
	   Putmsg("INCOMPLETE: cannot translate this pattern: ")
	   Print_pattern(record_occ_pattern(P, I, Q, Patts))
	   Putnl()
	   where(C_STATEMENTS'nil -> Ss)
	   where(C_EXPR'nil -> Cond)
	 |)

'action' Translate_product_patterns(C_EXPR, PRODUCT_TYPE, PATTERNS, INT -> C_EXPR, C_STATEMENTS)

  'rule' Translate_product_patterns(E, list(T, Ts), list(P, Ps), N -> Cond, Ss):
	 Mk_nth_field_id(N -> MemberId)
	 Translate_pattern(postfix(E, dot(id(MemberId))), T, P -> Cond1, Ss1)
	 Translate_product_patterns(E, Ts, Ps, N+1 -> Cond2, Ss2)
	 Concatenate_statements(Ss1, Ss2 -> Ss)
	 Conjoin(Cond1, Cond2 -> Cond)

  'rule' Translate_product_patterns(_, _, nil, _ -> nil, nil):

'action' Translate_list_patterns(C_EXPR, TYPE_EXPR, PATTERNS, INT -> C_EXPR, C_STATEMENTS)

  'rule' Translate_list_patterns(E, T, list(P, Ps), N -> Cond, Ss):
	 Int_to_string(N -> S)
	 string_to_id(S -> Nid)
	 Translate_pattern(postfix(E, index(literal(int(Nid)))), T, P -> Cond1, Ss1)
	 Translate_list_patterns(E, T, Ps, N+1 -> Cond2, Ss2)
	 Concatenate_statements(Ss1, Ss2 -> Ss)
	 Conjoin(Cond1, Cond2 -> Cond)

  'rule' Translate_list_patterns(_, _, nil, _ -> nil, nil):

'condition' Translate_pattern_variant(C_EXPR, VARIANT, Value_id, OPT_QUALIFICATION, PATTERNS -> C_EXPR, C_STATEMENTS)

  'rule' Translate_pattern_variant(E, R, I, Q, Patts -> Cond, Ss):
	 I'Ident -> id_op(Id)
	 I'Qualifier -> Is
	 Mk_record_id(Id -> Id1)
	 (|
	   where(Is -> list(_,_))
	   Object_ids_to_idents(Is -> Ids)
	 ||
	   where(Q -> qualification(Obj))
	   Object_to_idents(Obj -> Ids)
	 ||
	   where(IDENTS'nil -> Ids)
	 |)
	 (|
	   where(Ids -> list(_,_))
	   Qualifier_to_string(Ids -> QS)
	   id_to_string(Id1 -> S1)
	   Concatenate3(QS, "::", S1 -> QS1)
	   string_to_id(QS1 -> Id2)
	 ||
	   where(Id1 -> Id2)
	 |)
	 where(R -> record(_, _, Comps))
	 Mk_ptr_id(-> PtrId)
	 where(C_EXPR'bracket(ptr_cast(Id2, postfix(E, dot(id(PtrId))))) -> E1)
	 Translate_pattern_variant_components(E1, Comps, Patts, 1 -> Cond, Ss)

'condition' Translate_pattern_variant_components(C_EXPR, COMPONENTS, PATTERNS, counter:INT -> C_EXPR, C_STATEMENTS)

  'rule' Translate_pattern_variant_components(E, list(C, CS), list(P, Ps), N -> Cond, Ss):
	 where(C -> component(_, _, T, _))
	 Mk_nth_field_id(N -> MemberId)
	 Translate_pattern(bracket(postfix(E, arrow(id(MemberId)))), T, P -> Cond1, Ss1)
	 Translate_pattern_variant_components(E, CS, Ps, N+1 -> Cond2, Ss2)
	 Conjoin(Cond1, Cond2 -> Cond)
	 Concatenate_statements(Ss1, Ss2 -> Ss)

  'rule' Translate_pattern_variant_components(_, _, nil, _ -> nil, nil):

'condition' Translate_pattern_record_components(C_EXPR, COMPONENTS, PATTERNS, counter:INT -> C_EXPR, C_STATEMENTS)

  'rule' Translate_pattern_record_components(E, list(C, CS), list(P, Ps), N -> Cond, Ss):
	 where(C -> component(_, _, T, _))
	 Mk_nth_field_id(N -> MemberId)
	 Translate_pattern(postfix(E, dot(id(MemberId))), T, P -> Cond1, Ss1)
	 Translate_pattern_record_components(E, CS, Ps, N+1 -> Cond2, Ss2)
	 Conjoin(Cond1, Cond2 -> Cond)
	 Concatenate_statements(Ss1, Ss2 -> Ss)

  'rule' Translate_pattern_record_components(_, _, nil, _ -> nil, nil):





'action' Translate_case_branches(POS, OPT_IDENT, C_EXPR, TYPE_EXPR, TYPE_EXPR, CASE_BRANCHES -> C_STATEMENT)

  'rule' Translate_case_branches(P0, Opt_id, E, T, TR, list(case(P, Patt, V, _), Cs) -> S):
	 Current_parms -> Bss
	 Current_parms <- list(nil, Bss)
	 Current_parm_types -> Tss
	 Current_parm_types <- list(nil, Tss)
	 Translate_pattern(E, T, Patt -> Cond, Ss0)
	 Translate_value(TR, V -> E1, Ss1)
	 Current_parms <- Bss
	 Current_parm_types <- Tss
	 Concatenate_statements(Ss0, Ss1 -> Ss01)
	 Terminate_expr(Opt_id, E1, Ss01 -> Ss11)
	 (|
	   eq(Cond, nil)
	   where(compound(Ss11) -> S)
	 ||
	   Translate_case_branches(P0, Opt_id, E, T, TR, Cs -> S2)
	   where(C_STATEMENT'if(Cond, compound(Ss11), S2) -> S)
	 |)

  'rule' Translate_case_branches(P, _, _, _, _, nil -> S):
	 Fail(P, "Case exhausted" -> S)

'action' Fail(POS, STRING -> C_STATEMENT)

  'rule' Fail(P, ST -> S):
	 PosAsString(P -> PS)
	 Concatenate3(PS, " ", ST -> ST1)
	 string_to_id("RSL_fail" -> Fid)
	 where(expr(postfix(name(id(Fid)),
			    bracket(list(text_literal(ST1), nil)))) -> S)
	 

'action' Conjoin(C_EXPR, C_EXPR -> C_EXPR)

  'rule' Conjoin(E, nil -> E):

  'rule' Conjoin(nil, E -> E):

  'rule' Conjoin(E, E1 -> binary(E, logical_and, E1)):

'condition' Get_pattern_record(VARIANTS, Value_id -> VARIANT)

  'rule' Get_pattern_record(Vs, Vid -> V):
	 Vid'Ident -> Id_or_op
	 Lookup_record(Vs, Id_or_op -> V)

'condition' Lookup_record(VARIANTS, ID_OR_OP -> VARIANT)

  'rule' Lookup_record(list(V, Vs), Id_or_op -> V1):
	 (|
	   where(V -> record(_, con_ref(I), Comps))
	   I'Ident -> Id_or_op1
	   eq(Id_or_op, Id_or_op1)
	   where(V -> V1)
	 ||
	   Lookup_record(Vs, Id_or_op -> V1)
	 |)


'action' Translate_for_expr(LIST_LIMITATION, VALUE_EXPR -> C_STATEMENTS)

  'rule' Translate_for_expr(list_limit(_, B, LV, R), FV -> Ss):
	 where(B -> single(PB, id_op(Id)))
	 where(local_id(PB,Id) -> Varid)
	 where(LV -> disamb(P, LV1, LT))
	 Make_list_element_type(P, LT -> T1)
	 Translate_type(T1 -> T11)
	 Translate_value(unit, FV -> E, SsE)
	 Append_statement(SsE, expr(E) -> Body)
	 (|
	   eq(R, nil)
	   where(Body -> Body1)
	 ||
	   where(R -> restriction(_, RV))
	   Translate_value(bool, RV -> R1, SsRV)
	   where(C_STATEMENT'if(R1, compound(Body), nil) -> S)
	   Append_statement(SsRV, S -> Body1)
	 |)
	 (| -- ranged_list
	   where(LV1 -> ranged_list(_, Left, Right))
	   Translate_value(T1, Left -> Left1, SsL)
	   Translate_value(T1, Right -> Right1, SsR)
	   (|
	     Pure_expr(Right)
	     where(SsR -> SsR1)
	     where(Right1 -> Right2)
	   ||
	     Mk_temp_id(nil -> TempId)
	     where(C_NAME'id(TempId) -> RId)
	     C_Begin_decl()
	       C_Add_decl_specifier(type(int))
	       C_Add_declarator(with_init(dname(RId), assign(Right1)))
	     C_End_decl(-> RD)
	     Append_statement(SsR, decl(RD) -> SsR1)
	     where(C_EXPR'name(RId) -> Right2)
	   |)
	   Concatenate_statements(SsL, SsR1 -> SsLR)
	   where(
	     C_STATEMENT'
	     for(
	       decl(
		 decl(
		   list(type(T11), nil),
		   list(with_init(dname(Varid), assign(Left1)), nil)
		 )
	       ),
	       binary(name(Varid), le, Right2),
	       postfix(name(Varid), inc),
	       compound(Body1)
	     ) -> S
	   )
	   Append_statement(SsLR, S -> Ss)
	 ||
	   C_Begin_decl()
	     C_Add_decl_specifier(type(T11))
	     C_Add_declarator(dname(Varid))
	   C_End_decl(-> D)
	   Append_statement(nil, decl(D) -> Ss0)
	   string_to_id("x" -> X)
	   Mk_temp_id(ident(X) -> X_)
	   (|
	     -- enum_list
	     where(LV1 -> enum_list(_, Vs))
	     Mk_temp_id(nil -> A_)
	     C_Begin_decl()
	       C_Add_decl_specifier(type(T11))
	       Length_vs(Vs -> Length)
	       Int_to_string(Length -> SLength)
	       string_to_id(SLength -> Length1)
	       C_Add_declarator(with_index(dname(id(A_)), literal(int(Length1))))
	     C_End_decl(-> D1)
	     Append_statement(Ss0, decl(D1) -> Ss1)
	     Init_array(A_, T1, Vs -> Ssa)
	     Concatenate_statements(Ss1, Ssa -> Ss2)
	     string_to_id("0" -> Zero)
	     --
	     Append_statement(nil, expr(binary(name(Varid), assign, postfix(name(id(A_)), index(name(id(X_)))))) -> Body0)
	     Concatenate_statements(Body0, Body1 -> Body2)
	     --
	     where(
	       C_STATEMENT'
	       for(
		 decl(
		   decl(
		     list(type(int), nil),
		     list(with_init(dname(id(X_)), assign(literal(int(Zero)))), nil)
		   )
		 ),
		 binary(name(id(X_)), lt, literal(int(Length1))),
		 postfix(name(id(X_)), inc),
		 compound(Body2)
	       ) -> S
	     )
	     Append_statement(Ss2, S -> Ss)
	   ||
	     -- else
	     Translate_value(LT, LV1 -> LV11, LVSs)
	     C_Begin_decl()
	       Translate_type(LT -> LT1)
	       C_Add_decl_specifier(type(LT1))
	       string_to_id("list" -> List)
	       Mk_temp_id(ident(List) -> List_)
	       C_Add_declarator(with_init(dname(id(List_)), assign(LV11)))
	     C_End_decl(-> D1)
	     string_to_id("len" -> Len)
	     Mk_temp_id(ident(Len) -> Len_)
	     where(postfix(name(id(Len)), bracket(list(name(id(List_)), nil))) -> LenE)
	     C_Begin_decl()
	       C_Add_decl_specifier(type(int))
	       C_Add_declarator(with_init(dname(id(Len_)), assign(LenE)))
	     C_End_decl(-> D2)
	     Concatenate_statements(Ss0, LVSs -> Ss01)
	     Append_statement(Ss01, decl(D1) -> Ss1)
	     Append_statement(Ss1, decl(D2) -> Ss2)
	     Append_statement(nil, expr(binary(name(Varid), assign, postfix(name(id(List_)), index(name(id(X_)))))) -> Body0)
	     Concatenate_statements(Body0, Body1 -> Body2)
	     string_to_id("1" -> One)
	     where(
	       C_STATEMENT'
	       for(
		 decl(
		   decl(
		     list(type(int), nil),
		     list(with_init(dname(id(X_)), assign(literal(int(One)))), nil)
		   )
		 ),
		 binary(name(id(X_)), le, name(id(Len_))),
		 postfix(name(id(X_)), inc),
		 compound(Body2)
	       ) -> S
	     )
	     Append_statement(Ss2, S -> Ss)
	   |)
	 |)

'action' Init_array(IDENT, TYPE_EXPR, VALUE_EXPRS -> C_STATEMENTS)

  'rule' Init_array(Id, T, Vs -> Ss):
	 Init_array1(Id, T, Vs, 0 -> Ss)

'action' Init_array1(IDENT, TYPE_EXPR, VALUE_EXPRS, INT -> C_STATEMENTS)

  'rule' Init_array1(Id, T, list(V, Vs), N -> Ss):
	 Translate_value(T, V -> E, Ss0)
	 Int_to_string(N -> SN)
	 string_to_id(SN -> Nid)
	 where(
	   expr(
	     binary(
	       postfix(name(id(Id)), index(literal(int(Nid)))),
	       assign,
	       E
	     )
	   ) -> S
	 )
	 Append_statement(Ss0, S -> Ss1)
	 Init_array1(Id, T, Vs, N + 1 -> Ss2)
	 Concatenate_statements(Ss1, Ss2 -> Ss)

  'rule' Init_array1(_, _, nil, _ -> nil):


--'action' Let_defs_to_decls(LET_DEFS -> C_STATEMENTS)

--  'rule' Let_defs_to_decls(list(D, Ds) -> Ss):
--	 Let_def_to_decls(D -> Ss1)
--	 Let_defs_to_decls(Ds -> Ss2)
--	 Concatenate_statements(Ss1, Ss2 -> Ss)

--  'rule' Let_defs_to_decls(nil -> nil):

'action' Let_def_to_decls(LET_DEF -> C_STATEMENTS)

  'rule' Let_def_to_decls(explicit(P0, B, V) -> Ss):
	 (|
	   where(V -> disamb(_, V1, T1))
	 ||
	   Make_results(V -> list(result(T1,_,_,_,_),_))
	   where(V -> V1)
	 |)
	 Translate_type(T1 -> T11)
	 Translate_value(T1, V1 -> E, Ss1)
	 (|
	   where(B -> binding(_, Binding))
	   (|
	     where(Binding -> single(P, id_op(I)))
	     where(local_id(P,I) -> BId)
	     where(C_STATEMENTS'nil -> Ss2)
	     C_Begin_decl()
	       C_Add_decl_specifier(type(T11))
	       C_Add_declarator(with_init(dname(BId), assign(E)))
	     C_End_decl(-> D)
	     Append_statement(Ss1, decl(D) -> Ss0)
	     where(BINDINGS'list(Binding, nil) -> Bs)
	     where(PRODUCT_TYPE'list(T1, nil) -> Ts)
	   ||
	     where(Binding -> product(_, Bs))
	     Debracket_maxtype(T1 -> T2)
	     Type_is_product(T2 -> Ts)
	     (|
	       where(E -> name(_))
	       -- no need for extra variable
	       Product_binding_to_decls(E, Ts, Bs -> Ss2)
	       where(Ss1 -> Ss0)
	     ||
	       Mk_temp_id(nil -> TempId)
	       where(C_NAME'id(TempId) -> BId)
	       C_Begin_decl()
		 C_Add_decl_specifier(type(T11))
		 C_Add_declarator(with_init(dname(BId), assign(E)))
	       C_End_decl(-> D)
	       Append_statement(Ss1, decl(D) -> Ss0)
	       Product_binding_to_decls(name(BId), Ts, Bs -> Ss2)
	     |)
	   |)
	   Concatenate_statements(Ss0, Ss2 -> Ss)
	   Current_parms -> Bss
	   Current_parms <- list(Bs, Bss)
	   Current_parm_types -> Tss
	   Current_parm_types <- list(Ts, Tss)
	 ||
	   where(B -> pattern(PP, Pat))
	   Current_parms -> Bss
	   Current_parms <- list(nil, Bss)
	   Current_parm_types -> Tss
	   Current_parm_types <- list(nil, Tss)
	   (|
	     where(E -> name(_))
	     -- no need for extra variable
	     Translate_pattern(E, T1, Pat -> Cond, Ss2)
	     where(Ss1 -> Ss0)
	   ||
	     Mk_temp_id(nil -> TempId)
	     where(C_NAME'id(TempId) -> BId)
	     C_Begin_decl()
	       C_Add_decl_specifier(type(T11))
	       C_Add_declarator(with_init(dname(BId), assign(E)))
	     C_End_decl(-> D)
	     Append_statement(Ss1, decl(D) -> Ss0)
	     Translate_pattern(name(BId), T1, Pat -> Cond, Ss2)
	   |)
	   (|
	     eq(Cond, nil)
	     Concatenate_statements(Ss0, Ss2 -> Ss)
	   ||
	     Fail(PP, "Let pattern does not match" -> S)
	     where(C_STATEMENT'if(unary(not,bracket(Cond)), S, nil) -> S1)
	     Append_statement(Ss0, S1 -> Ss11)
	     Concatenate_statements(Ss11, Ss2 -> Ss)
	   |)
	 |)

  'rule' Let_def_to_decls(implicit(P0, TG, R) -> Ss):
	 (|
	   Split_typing(TG -> B, TT)
	   Split_restriction(exists, R, B, TT -> SLM, T, Pred)
	   [|
	     Current_funs -> list(I, _)
	     Collect_fun_ids(Pred, nil -> Is)
	     Isin_value_ids(I, Is)
	     Puterror(P0)
	     Putmsg("Recursion through implicit let\n")
	   |]
	   Translate_value(T, SLM -> E1, Ss1)
	   (|
	     where(B -> single(P, id_op(Id)))
	     where(BINDINGS'list(B, nil) -> Bs)
	     where(local_id(P,Id) -> BId)
	     where(C_STATEMENTS'nil -> Ss2)
	     where(PRODUCT_TYPE'list(TT, nil) -> Ts)
	   ||
	     where(B -> product(_, Bs))
	     Mk_temp_id(nil -> TempId)
	     where(C_NAME'id(TempId) -> BId)
	     Debracket_maxtype(TT -> TTm)
	     Type_is_product(TTm -> Ts)
	     Product_binding_to_decls(name(id(TempId)), Ts, Bs -> Ss2)
	   |)
	   -- different names chooses, chooset etc really just for
	   -- Visual C++ compiler, and so is use of templates
	   (| 
	     Type_is_set(T -> TE)
	     string_to_id("RSL_chooses" -> Fid)
	     Translate_type(TE -> CT)
	     where(C_NAME'template(Fid, list(CT, nil)) -> FN)
	   ||
	     Type_matches_text(T)
	     string_to_id("RSL_chooset" -> Fid)
	     where(C_NAME'id(Fid) -> FN)
	   ||
	     Type_is_list(T -> TE)
	     string_to_id("RSL_choosel" -> Fid)
	     Translate_type(TE -> CT)
	     where(C_NAME'template(Fid, list(CT, nil)) -> FN)
	   ||
	     Type_is_map(T -> DT, RT)
	     string_to_id("RSL_choosem" -> Fid)
	     Translate_type(DT -> CD)
	     Translate_type(RT -> CR)
	     where(C_NAME'template(Fid, list(CD, list(CR, nil))) -> FN)
	   |)
	   Current_parms -> CPS
	   Current_parms <- list(Bs, CPS)
	   Current_parm_types -> CPTS
	   Current_parm_types <- list(Ts, CPTS)
	   Define_temp_fun(P0, B, TT, Pred, bool, BId, Ss2, nil -> PF, Pdef, Oid)
	   where(postfix(name(FN),
			 bracket(list(PF,
				 list(E1,nil)))) -> E2)
	   Translate_type(TT -> TT2)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(TT2))
	     C_Add_declarator(with_init(dname(BId), assign(E2)))
	   C_End_decl(-> D)
	   (|
	     where(Oid -> ident(NSId))
	     C_id_to_string(NSId -> NS)
	     Concatenate3("\nnamespace ", NS, " {\n// namespace for implicit let\n" -> S1)
	     WriteHCcString(S1)
	     Define_current_parms(CPS, CPTS, NSId -> Ss0)
	     [|
	       ne(Pdef, nil)
	       C_Decl_to_string_h(Pdef -> Sh1)	WriteHString(Sh1)
	       C_Decl_to_string(Pdef -> Scc1)	WriteCcString(Scc1)
	     |]
	     Concatenate3("\n} // end of namespace ", NS, "\n\n" -> S2)
	     WriteHCcString(S2)
	   ||
	     where(C_STATEMENTS'nil -> Ss0)
	   |)
	   Concatenate_statements(Ss0, Ss1 -> Ss01)
	   Append_statement(Ss01, decl(D) -> Ss11)
	   Concatenate_statements(Ss11, Ss2 -> Ss)
	 ||
	   Puterror(P0)
	   Putmsg("Cannot translate implicit let definitions in general: ignored")
	   Putnl()
	   where(C_STATEMENTS'nil -> Ss)
	   Current_parms -> CPS
	   Current_parms <- list(nil, CPS)
	   Current_parm_types -> CPTS
	   Current_parm_types <- list(nil, CPTS)
	 |)


'action' Product_binding_to_decls(C_EXPR, PRODUCT_TYPE, BINDINGS -> C_STATEMENTS)

  'rule' Product_binding_to_decls(E, Ts, Bs -> Ss):
	 Product_binding_to_decls1(E, 1, Ts, Bs -> Ss)

'action' Product_binding_to_decls1(C_EXPR, INT, PRODUCT_TYPE, BINDINGS -> C_STATEMENTS)

  'rule' Product_binding_to_decls1(E, N, list(T, Ts), list(single(P, Id_or_op), Bs) -> list(S, Ss)):
	 where(Id_or_op -> id_op(Id))
	 where(local_id(P,Id) -> Id1)
	 C_Begin_decl()
	   Translate_type(T -> T1)
	   C_Add_decl_specifier(type(T1))
	   Mk_nth_field_id(N -> FieldId)
	   C_Add_declarator(
	       with_init(
		 dname(Id1),
		 assign(postfix(E, dot(id(FieldId))))
	       )
	     )
	 C_End_decl(-> D)
	 where(C_STATEMENT'decl(D) -> S)
	 Product_binding_to_decls1(E, N + 1, Ts, Bs -> Ss)

  'rule' Product_binding_to_decls1(_, _, _, nil -> nil):

  'rule' Product_binding_to_decls1(E, N, list(T, Ts), list(product(_, Bs1), Bs) -> Ss):
	 Mk_temp_id(nil -> TempId1)
	 C_Begin_decl()
	   Translate_type(T -> T1)
	   C_Add_decl_specifier(type(T1))
	   Mk_nth_field_id(N -> FieldId)
	   C_Add_declarator(
	       with_init(
		 dname(id(TempId1)),
		 assign(postfix(E, dot(id(FieldId))))
	       )
	     )
	 C_End_decl(-> D)
	 where(C_STATEMENT'decl(D) -> S)
	 Debracket_maxtype(T -> Tm)
	 Type_is_product(Tm -> Ts1)
	 Product_binding_to_decls(name(id(TempId1)), Ts1, Bs1 -> Ss1)
	 Product_binding_to_decls1(E, N + 1, Ts, Bs -> Ss2)
	 Concatenate_statements(list(S,Ss1), Ss2 -> Ss)



'action' Decompose_actual(C_EXPR, INT, INT -> C_EXPRS)

  'rule' Decompose_actual(E, Next, Last -> list(EN, Es)):
	 Mk_nth_field_id(Next -> FieldId)
	 where(postfix(E, dot(id(FieldId))) -> EN)
	 (|
	   eq(Next, Last)
	   where(C_EXPRS'nil -> Es)
	 ||
	   Decompose_actual(E, Next+1, Last -> Es)
	 |)
	 
'condition' Only_vars_and_constants(DECLS -> BINDINGS, PRODUCT_TYPE)

  'rule' Only_vars_and_constants(list(D, DS) -> Bs, Ts):
	 Only_vars_and_constants1(D -> Bs1, Ts1)
	 Only_vars_and_constants(DS -> Bs2, Ts2)
	 Concatenate_bindings(Bs1, Bs2 -> Bs)
	 Concatenate_product_types(Ts1, Ts2 -> Ts)

  'rule' Only_vars_and_constants(nil -> nil, nil):

'condition' Only_vars_and_constants1(DECL -> BINDINGS, PRODUCT_TYPE)

  'rule' Only_vars_and_constants1(variable_decl(_, Defs) -> Bs, Ts):
	 Variables_bindings_and_types(Defs -> Bs, Ts)
	 
  'rule' Only_vars_and_constants1(value_decl(_, DS) -> Bs, Ts):
	 Only_constants(DS -> Bs, Ts)

'action' Variables_bindings_and_types(VARIABLE_DEFS -> BINDINGS, PRODUCT_TYPE)

  'rule' Variables_bindings_and_types(list(D, DS) -> Bs, Ts):
	 Variable_bindings_and_types(D -> Bs1, Ts1)
	 Variables_bindings_and_types(DS -> Bs2, Ts2)
	 Concatenate_bindings(Bs1, Bs2 -> Bs)
	 Concatenate_product_types(Ts1, Ts2 -> Ts)

  'rule' Variables_bindings_and_types(nil -> nil, nil):	 

'action' Variable_bindings_and_types(VARIABLE_DEF -> BINDINGS, PRODUCT_TYPE)

  'rule' Variable_bindings_and_types(single(P, Id, T, _) -> list(B, nil), list(T1, nil)):
	 where(BINDING'single(P, id_op(Id)) -> B)
	 Resolve_type(T -> T1)

  'rule' Variable_bindings_and_types(multiple(P, list(Id, Ids), T) -> list(B, Bs), list(T1, Ts)): 
	 Variable_bindings_and_types(single(P, Id, T, nil) -> list(B, nil), list(T1, nil))
	 Variable_bindings_and_types(multiple(P, Ids, T) -> Bs, Ts)

  'rule' Variable_bindings_and_types(multiple(_, nil, _) -> nil, nil):






'condition' Only_constants(VALUE_DEFS -> BINDINGS, PRODUCT_TYPE)

  'rule' Only_constants(list(D, DS) -> Bs, Ts):
	 Is_constant(D -> Bs1, Ts1)
	 Only_constants(DS -> Bs2, Ts2)
	 Concatenate_bindings(Bs1, Bs2 -> Bs)
	 Concatenate_product_types(Ts1, Ts2 -> Ts)

  'rule' Only_constants(nil -> nil, nil):

'condition' Is_constant(VALUE_DEF -> BINDINGS, PRODUCT_TYPE)

  'rule' Is_constant(exp_val(_,single(_, B, T),_) -> Bs, Ts):
	 Resolve_type(T -> T1)
	 (|
	   where(B -> single(_,_))
	   where(BINDINGS'list(B, nil) -> Bs)
	   where(PRODUCT_TYPE'list(T1, nil) -> Ts)
	 ||
	   where(B -> product(_, Bs))
	   (|
	     Type_is_product(T1 -> Ts)
	   ||
	     Length_bs(Bs -> N)
	     Make_product_type(T1, N -> product(Ts))
	   |)
	 |)

'action' Concatenate_bindings(BINDINGS, BINDINGS -> BINDINGS)

  'rule' Concatenate_bindings(list(B, Bs), Bs1 -> list(B, Bs2)):
	 Concatenate_bindings(Bs, Bs1 -> Bs2)

  'rule' Concatenate_bindings(nil, Bs -> Bs):

'action' Concatenate_product_types(PRODUCT_TYPE, PRODUCT_TYPE -> PRODUCT_TYPE)

  'rule' Concatenate_product_types(list(T, Ts), Ts1 -> list(T, Ts2)):
	 Concatenate_product_types(Ts, Ts1 -> Ts2)

  'rule' Concatenate_product_types(nil, Ts -> Ts):


'action' Define_temp_vars(IDENT -> C_STATEMENTS)

  'rule' Define_temp_vars(Id -> Ss)
	 Current_parms -> Bss
	 Current_parm_types -> XTs
	 Define_current_parms(Bss, XTs, Id -> Ss)

'action' Define_current_parms(BINDINGSS, PRODUCT_TYPES, IDENT -> C_STATEMENTS)

  'rule' Define_current_parms(list(Bs, Bss), list(XT, XTs), Id -> Ss):
	 Define_current_parms(Bss, XTs, Id -> Ss1)
	 Define_parameter_vars(Bs, XT, Id, nil -> Ss2)
	 Concatenate_statements(Ss1, Ss2 -> Ss)

  'rule' Define_current_parms(nil, _, _ -> nil):	 

'action' Define_local_parms(IDENT -> C_STATEMENTS)

  'rule' Define_local_parms(Id -> Ss):
	 Current_parms -> list(Bs, _)
	 Current_parm_types -> list(Ts, _)
	 -- top level parms only as local namespaces are nested
	 Define_parameter_vars(Bs, Ts, Id, nil -> Ss)

'action' Define_parameter_vars(BINDINGS, PRODUCT_TYPE, IDENT, C_STATEMENTS -> C_STATEMENTS)

  'rule' Define_parameter_vars(list(B, Bs), list(T, Ts), Q, Ss -> Ss1):
	 (|
	   where(B -> single(P, Id_or_op))
	   Id_or_op_to_id(Id_or_op -> Id)
	   Translate_type(T -> T1)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(T1))
	     C_Add_declarator(dname(local_id(P,Id)))
	   C_End_decl(-> D)
	   C_Decl_to_string_h(D -> Sh)	 WriteHString(Sh)
	   C_Decl_to_string(D -> Scc)	 WriteCcString(Scc)
	   Append_statement(Ss,
		expr(binary(name(qualified(local_id(P,Id),list(Q,nil))),
			    assign,
			    name(local_id(P,Id))))
		 -> Ss2)
	 ||
	   where(B -> product(_, Bs1))
	   (|
	     Type_is_product(T -> XT)
	   ||
	     Length_bs(Bs1 -> N)
	     Make_product_type(T, N -> product(XT))
	   |)
	   Define_parameter_vars(Bs1, XT, Q, Ss -> Ss2)
	 |)
	 Define_parameter_vars(Bs, Ts, Q, Ss2 -> Ss1)

  'rule' Define_parameter_vars(nil, _, _, Ss -> Ss):

-- debug
--  'rule' Define_parameter_vars(Bs, Ts, _, Ss -> Ss):
--print(Bs)
--print(Ts)

'action' Collect_constant_ids

'action' Define_constants(Value_ids, Value_ids, FOUND -> Value_ids, C_DECLS, VALUE_EXPRS)

  'rule' Define_constants(list(I, Is), Wait, Found -> Fids, Ds, Vs):
	 I'Def -> Def
	 (|
	   (| where(Def -> expl_fun(_,_,_,_,_,_))
	   || where(Def -> impl_fun(_,_,_,_)) |)
	   Define_constants(Is, Wait, Found -> Fids1, Ds, Vs)
	   where(Value_ids'list(I, Fids1) -> Fids)
	 || 
	   Define_constant(I, Def, Is, Wait, Found -> Wait1, Found1, D, V)
	   Define_constants(Is, Wait1, Found1 -> Fids, Ds1, Vs1)
	   where(VALUE_EXPRS'list(V, Vs1) -> Vs)
	   where(C_DECLS'list(D, Ds1) -> Ds)
	 |)

  'rule' Define_constants(nil, nil, _ -> nil, nil, nil):

  'rule' Define_constants(nil, Wait:list(I, _), Found -> Fids, Ds, Vs):
	 (|
	   eq(Found, found)
	   Define_constants(Wait, nil, nil -> Fids, Ds, Vs)
	 ||
	   I'Pos -> P
	   I'Ident -> Id
	   Puterror(P)
	   Print_id_or_op(Id)
	   Putmsg(" seems to be involved in a mutual recursion: cannot translate")
	   Putnl()
	   where(Value_ids'nil -> Fids)
	   where(VALUE_EXPRS'nil -> Vs)
	   where(C_DECLS'nil -> Ds)
	 |)

'action' Define_constant(Value_id, VALUE_DEFINITION, Value_ids, Value_ids, FOUND -> Value_ids, FOUND, C_DECL, VALUE_EXPR)

  'rule' Define_constant(I, no_def, _, Wait, Found -> Wait, found, D, A)
	 Define_constant_id(I -> D)
	 I'Pos -> P
	 I'Ident -> Id
	 Putwarning(P)
	 Print_id_or_op(Id)
	 Putmsg(" has no definition")
	 Putnl()
	 WriteCcString("/*INCOMPLETE: undefined value*/\n")
	 where(literal_expr(P, unit) -> A)

  'rule' Define_constant(I, expl_val(V, _), Todo, Wait, Found -> Wait1, Found1, D, A):
	 Collect_value_ids(V, nil -> Deps)
	 Intersect_values(Deps, Wait -> Wait_deps)
	 Intersect_values(Deps, Todo -> Todo_deps)
	 I'Pos -> P
	 (|
	   eq(Wait_deps, nil)
	   eq(Todo_deps, nil)
	   where(Wait -> Wait1)
	   where(found -> Found1)
	   Define_constant_id(I -> D)
	   (| -- explicit values have disambiguations
	     where(V -> disamb(_, V1, _))
	   ||
	     where(V -> V1)
	   |)
	   (|
	     I'Ident -> id_op(Id)
	     New_variable_id(P, Id -> VI)
	     I'Type -> T
	     VI'Type <- T
	     where(ass_occ(P, VI, nil, V1) -> A)
	   ||
	     Puterror(P)
	     Putmsg("Cannot translate constant definition of ")
	     I'Ident -> Id1
	     Print_id_or_op(Id1)
	     Putnl()
	     where(literal_expr(P, unit) -> A)
	   |)
	 ||
	   where(Value_ids'list(I, Wait) -> Wait1)
	   where(Found -> Found1)
	   where(literal_expr(P, unit) -> A)
	   where(C_DECL'nil -> D)
	 |)
	 
  'rule' Define_constant(I, impl_val(V), Todo, Wait, Found -> Wait, found, D, A):
	 Define_constant_id(I -> D)
	 I'Pos -> P
	 I'Ident -> Id
	 Putwarning(P)
	 Print_id_or_op(Id)
	 Putmsg(" has an implicit definition: no initial value")
	 Putnl()
	 WriteCcString("/*INCOMPLETE: implicit value definition*/\n")
	 where(literal_expr(P, unit) -> A)

'action' Define_constant_id(Value_id -> C_DECL)

  'rule' Define_constant_id(I -> D):
	 I'Ident -> Id_or_op
	 I'Type -> T
	 Id_or_op_to_id(Id_or_op -> Id)
	 Translate_type(T -> T1)
	 C_Begin_decl()
	   C_Add_decl_specifier(type(T1))
	   C_Add_declarator(dname(id(Id)))
	 C_End_decl(-> D)



'action' Define_vars(DECLS -> C_DECLS, VALUE_EXPRS)

  'rule' Define_vars(list(D, Ds) -> CDs, Vs):
	 Define_vars1(D -> CDs1, Vs1)
	 Define_vars(Ds -> CDs2, Vs2)
	 Concatenate_values(Vs1, Vs2 -> Vs)
	 Concatenate_decls(CDs1, CDs2 -> CDs)

  'rule' Define_vars(nil -> nil, nil)

'action' Define_vars1(DECL -> C_DECLS, VALUE_EXPRS)

  'rule' Define_vars1(variable_decl(_, Defs) -> Ds, Vs):
	 Get_current_variables(-> Vars)
	 Define_var_defs(Vars, Defs -> Ds, Vs)

  'rule' Define_vars1(_ -> nil, nil):


'action' Define_var_defs(VARIABLE_ENV, VARIABLE_DEFS -> C_DECLS, VALUE_EXPRS)

  'rule' Define_var_defs(VE, list(D, DS) -> CDs, Vs):
	 Define_var_def(VE, D -> CDs1, Vs1)
	 Define_var_defs(VE, DS -> CDs2, Vs2)
	 Concatenate_values(Vs1, Vs2 -> Vs)
	 Concatenate_decls(CDs1, CDs2 -> CDs)

  'rule' Define_var_defs(_, nil -> nil, nil):

'action' Define_var_def(VARIABLE_ENV, VARIABLE_DEF -> C_DECLS, VALUE_EXPRS)

  'rule' Define_var_def(VE, single(P, Id, _, _) -> list(D, nil), list(A, nil)):
	 Lookup_env_variable_id(Id, nil, VE -> OI)
	 (|
	   where(OI -> variable_id(I))
	 || -- may be local: try with localised name
	   Localise_id(P, Id -> LId)
	   Lookup_env_variable_id(LId, nil, VE -> variable_id(I))
	 |)
	 I'Ident -> Id1
	 I'Type -> T
	 Translate_type(T -> CT)
	 C_Begin_decl()
	   C_Add_decl_specifier(type(CT))
	   C_Add_declarator(dname(id(Id1)))
	 C_End_decl(-> D)
	 (|
	   I'Init -> initial(V)
	   where(ass_occ(P, I, nil, V) -> A)
	 ||
	   where(literal_expr(P, unit) -> A)
	 |)

  'rule' Define_var_def(VE, multiple(P, list(Id, Ids), T) -> list(D, Ds), list(V, Vs)):
	 Define_var_def(VE, single(P, Id, T, nil) -> list(D, nil), list(V, nil))
	 Define_var_def(VE, multiple(P, Ids, T) -> Ds, Vs)

  'rule' Define_var_def(_, multiple(_, nil, _) -> nil, nil):

'action' Concatenate_values(VALUE_EXPRS, VALUE_EXPRS -> VALUE_EXPRS)

  'rule' Concatenate_values(list(V, Vs), Vs1 -> list(V, Vs2)):
	 Concatenate_values(Vs, Vs1 -> Vs2)

  'rule' Concatenate_values(nil, Vs -> Vs):

'action' Translate_assignments(VALUE_EXPRS -> C_STATEMENTS)

  'rule' Translate_assignments(list(A:ass_occ(_, _, _, _), Vs) -> Ss):
	 Translate_value(unit, A -> E, Ss0)
	 Append_statement(Ss0, expr(E) -> Ss01)
	 Translate_assignments(Vs -> Ss1)
	 Concatenate_statements(Ss01, Ss1 -> Ss)

  'rule' Translate_assignments(list(literal_expr(_, unit), Vs) -> Ss):
	 Translate_assignments(Vs -> Ss)

  'rule' Translate_assignments(nil -> nil):

'action' Decls_to_statements(C_DECLS -> C_STATEMENTS)

  'rule' Decls_to_statements(list(D, Ds) -> list(decl(D), Ss)):
	 Decls_to_statements(Ds -> Ss)

  'rule' Decls_to_statements(nil -> nil):


'action' Define_local_constant_decls(DECLS, C_STATEMENTS -> C_STATEMENTS)

  'rule' Define_local_constant_decls(list(D, Ds), Ss0 -> Ss1):
	 Define_local_constant_decl(D, Ss0 -> Ss2)
	 Define_local_constant_decls(Ds, Ss2 -> Ss1)
	   
  'rule' Define_local_constant_decls(nil, Ss -> Ss)

'action' Define_local_constant_decl(DECL, C_STATEMENTS -> C_STATEMENTS)

  'rule' Define_local_constant_decl(value_decl(_, Defs), Ss -> Ss1):
	 Define_local_constant_defs(Defs, Ss -> Ss1)

  'rule' Define_local_constant_decl(_, Ss -> Ss):

'action' Define_local_constant_defs(VALUE_DEFS, C_STATEMENTS -> C_STATEMENTS)

  'rule' Define_local_constant_defs(list(D, DS), Ss -> Ss1):
	 Define_local_constant_def(D, Ss -> Ss2)
	 Define_local_constant_defs(DS, Ss2 -> Ss1)

  'rule' Define_local_constant_defs(nil, Ss -> Ss):

'action' Define_local_constant_def(VALUE_DEF, C_STATEMENTS -> C_STATEMENTS)

  'rule' Define_local_constant_def(D, Ss -> Ss1)
	 (|
	   where(D -> exp_val(_, single(_, B, _), _))
	   Get_current_top_values(-> VE)
	   Collect_value_binding(VE, B -> Is)
	   Define_local_constants(Is, Ss -> Ss1)
	 ||
	   where(Ss -> Ss1)
	 |)

'action' Define_local_constants(Value_ids, C_STATEMENTS -> C_STATEMENTS)

  'rule' Define_local_constants(list(I, Is), Ss -> Ss1):
	 Define_local_constant(I, Ss -> Ss2)
	 Define_local_constants(Is, Ss2 -> Ss1)

  'rule' Define_local_constants(nil, Ss -> Ss):

'action' Define_local_constant(Value_id, C_STATEMENTS -> C_STATEMENTS)

  'rule' Define_local_constant(I, Ss -> Ss1)
	 (|
	   I'Ident -> id_op(Id)
	   I'Type -> T
	   I'Def -> Def
	   where(Def -> expl_val(V, _))
	   Translate_value(T, V -> E, Ss0)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(const))
	     Translate_type(T -> T1)
	     C_Add_decl_specifier(type(T1))
	     C_Add_declarator(with_init(dname(id(Id)), assign(E)))
	   C_End_decl(-> D)
	   Append_statement(Ss0, decl(D) -> Ss01)
	   Concatenate_statements(Ss, Ss01 -> Ss1)
	 ||
	   I'Pos -> P
	   Puterror(P)
	   Putmsg("Unable to translate constant definition ")
	   I'Ident -> Id1
	   Print_id_or_op(Id1)
	   Putnl()
	   where(Ss -> Ss1)
	 |)
	   
'action' Define_local_variable_decls(DECLS, C_STATEMENTS -> C_STATEMENTS)

  'rule' Define_local_variable_decls(list(D, Ds), Ss0 -> Ss1):
	 Define_local_variable_decl(D, Ss0 -> Ss2)
	 Define_local_variable_decls(Ds, Ss2 -> Ss1)
	   
  'rule' Define_local_variable_decls(nil, Ss -> Ss)

'action' Define_local_variable_decl(DECL, C_STATEMENTS -> C_STATEMENTS)

  'rule' Define_local_variable_decl(variable_decl(_, Defs), Ss -> Ss1):
	 Define_local_variable_defs(Defs, Ss -> Ss1)

  'rule' Define_local_variable_decl(_, Ss -> Ss):

'action' Define_local_variable_defs(VARIABLE_DEFS, C_STATEMENTS -> C_STATEMENTS)

  'rule' Define_local_variable_defs(list(D, DS), Ss -> Ss1):
	 Define_local_variable_def(D, Ss -> Ss2)
	 Define_local_variable_defs(DS, Ss2 -> Ss1)

  'rule' Define_local_variable_defs(nil, Ss -> Ss):

'action' Define_local_variable_def(VARIABLE_DEF, C_STATEMENTS -> C_STATEMENTS)

  'rule' Define_local_variable_def(single(P, Id, _, _), Ss -> Ss1):
	 Get_current_variables(-> VARS)
	 Lookup_env_variable_id(Id, nil, VARS -> OI)
	 (|
	   where(OI -> variable_id(I))
	 || -- may be local: try with localised name
	   Localise_id(P, Id -> LId)
	   Lookup_env_variable_id(LId, nil, VARS -> variable_id(I))
	 |)
	 I'Ident -> Id1
	 I'Type -> T
	 Translate_type(T -> T1)
	 I'Init -> Init
	 (|
	   eq(Init, nil)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(T1))
	     C_Add_declarator(dname(id(Id1)))
	   C_End_decl(-> D)
	 ||
	   where(Init -> initial(VExpr))
	   Translate_value(T, VExpr -> CExpr, Ss0)
	   [|
	     ne(Ss0, nil)
	     Puterror(P)
	     Putmsg("Cannot translate initial expression ")
	     Print_expr(VExpr)
	     Putnl()
	   |]
	   (|
	     Debracket_maxtype(T -> T2)
	     Type_is_product(T2 -> _)
	     Universal_type_id(T -> Pid)
	     Lookup_declared_type(Pid -> CT)
	     Type_name_to_c_name(CT -> N)
	     where(CExpr -> multiple(Exprs))
	     where(postfix(name(N), bracket(Exprs)) -> InitExpr)
	   ||
	     where(CExpr -> InitExpr)
	   |)
	   C_Begin_decl()
	     C_Add_decl_specifier(type(T1))
	     C_Add_declarator(with_init(dname(id(Id1)), assign(InitExpr)))
	   C_End_decl(-> D)
	 |)
	 Append_statement(Ss, decl(D) -> Ss1)

  'rule' Define_local_variable_def(multiple(P, list(Id, Ids), T0), Ss -> Ss0):
	 Define_local_variable_def(single(P, Id, T0, nil), Ss -> Ss1)
	 Define_local_variable_def(multiple(P, Ids, T0), Ss1 -> Ss0)

  'rule' Define_local_variable_def(multiple(_, nil, _), Ss -> Ss):


-----------------------------------------------------------------------
-- Universal type names (See section 14 of translator manual)
-----------------------------------------------------------------------

'action' Define_universal_type(IDENT -> C_TYPE_SPECIFIER)

  'rule' Define_universal_type(UId -> CT):
-- defines universal type UId
-- as UId qualified by Ids
	 Namespaces_to_idents(-> Ids) 
	 (|
	   eq(Ids, nil)
	   where(C_TYPE_SPECIFIER'named_type(UId) -> CT)
	 ||
	   where(C_TYPE_SPECIFIER'qualified(named_type(UId), Ids) -> CT)
	 |)
	 Register_declared_type(CT)

'action' Universal_type_id(TYPE_EXPR -> IDENT)

  'rule' Universal_type_id(T -> I):
	 Debracket_maxtype(T -> T1)
	 Compose_type_name(T1 -> S1)
	 Concatenate("RSL_", S1 -> S2)
	 string_to_id(S2 -> I)

'action' Compose_type_name(TYPE_EXPR -> STRING)

  'rule' Compose_type_name(unit -> "U")

  'rule' Compose_type_name(int -> "I")

  'rule' Compose_type_name(bool -> "B")

  'rule' Compose_type_name(real -> "R")

  'rule' Compose_type_name(char -> "C")

  'rule' Compose_type_name(text -> "lC")

  'rule' Compose_type_name(product(list(bracket(T), P)) -> S):
	 Compose_type_name(product(list(T, P)) -> S)

  'rule' Compose_type_name(product(list(T, P)) -> S):
	 (|
	   Lower_type_precedence(T, 2)
	   where(T -> T1)
	 ||
	   where(TYPE_EXPR'bracket(T) -> T1)
	 |)
	 Compose_type_name(T1 -> S1)
	 (|
	   eq(P, nil)
	   where(S1 -> S)
	 ||
	   Compose_type_name(product(P) -> S2)
	   Concatenate3(S1, "x", S2 -> S)
	 |)

  'rule' Compose_type_name(fun(bracket(T), A, R) -> S):
	 Compose_type_name(fun(T, A, R) -> S)

  'rule' Compose_type_name(fun(T1, A, result(bracket(T2),RD,WR,IN,OUT))  -> S):
	 Compose_type_name(fun(T1, A, result(T2,RD,WR,IN,OUT))  -> S)

  'rule' Compose_type_name(fun(T1, partial, result(T2, _, _, _, _)) -> S):
	 (|
	   Lower_type_precedence(T1, 3)
	   where(T1 -> T11)
	 ||
	   where(TYPE_EXPR'bracket(T1) -> T11)
	 |)
	 Compose_type_name(T11 -> S1)
	 Compose_type_name(T2 -> S2)
	 Concatenate3(S1, "f", S2 -> S)

  'rule' Compose_type_name(infin_map(bracket(TD), TR) -> S):
	 Compose_type_name(infin_map(TD, TR) -> S)

  'rule' Compose_type_name(infin_map(TD, bracket(TR)) -> S):
	 Compose_type_name(infin_map(TD, TR) -> S)

  'rule' Compose_type_name(infin_map(TD, TR) -> S):
	 (|
	   Lower_type_precedence(TD, 3)
	   where(TD -> TD1)
	 ||
	   where(TYPE_EXPR'bracket(TD) -> TD1)
	 |)
	 Compose_type_name(TD1 -> S1)
	 Compose_type_name(TR -> S2)
	 Concatenate3(S1, "m", S2 -> S)

  'rule' Compose_type_name(infin_set(bracket(T)) -> S):
	 Compose_type_name(infin_set(T) -> S)

  'rule' Compose_type_name(infin_set(T) -> S):
	 (|
	   Lower_type_precedence(T, 1)
	   where(T -> T1)
	 ||
	   where(TYPE_EXPR'bracket(T) -> T1)
	 |)
	 Compose_type_name(T1 -> S1)
	 Concatenate("s", S1 -> S)

  'rule' Compose_type_name(infin_list(bracket(T)) -> S):
	 Compose_type_name(infin_list(T) -> S)

  'rule' Compose_type_name(infin_list(T) -> S):
	 (|
	   Lower_type_precedence(T, 1)
	   where(T -> T1)
	 ||
	   where(TYPE_EXPR'bracket(T) -> T1)
	 |)
	 Compose_type_name(T1 -> S1)
	 Concatenate("l", S1 -> S)

  'rule' Compose_type_name(bracket(T) -> S):
	 Compose_type_name(T -> S1)
	 Concatenate3("6", S1, "9" -> S)

  'rule' Compose_type_name(defined(Id, _) -> S):
	 Id'Ident -> Ident
	 Id'Type -> Type
	 (|
	   where(Type -> sort(_))
	   Id'Pos -> P
	   C_id_to_string(Ident -> S1)
	   Pos_to_string(P -> S2)
	   Concatenate3(S1, "_", S2 -> S)
	 ||
	   where(Type -> abbrev(_))
	   Id'Def -> abbreviation(TExpr)
	   Compose_type_name(TExpr -> S)
	 |)

  'rule' Compose_type_name(TExpr -> S):
	 Maxtype(TExpr -> TExpr1)
	 ne(TExpr, TExpr1)
	 Compose_type_name(TExpr1 -> S)

  'rule' Compose_type_name(TExpr -> "/*INCOMPLETE:unspecified type component name*/"):
	 Putmsg("Internal error: cannot translate type ")
	 Print_type(TExpr)
	 Putnl()	 

'action' Debracket_maxtype(TYPE_EXPR -> TYPE_EXPR)

  'rule' Debracket_maxtype(bracket(T) -> T1):
	 Debracket_maxtype(T -> T1)

  'rule' Debracket_maxtype(subtype(single(_, _, T), _) -> T1):
	 Debracket_maxtype(T -> T1)

  'rule' Debracket_maxtype(T -> T1):
	 Maxtype(T -> T1)

-----------------------------------------------------------------------
-- Get the size of translated C++ type
-----------------------------------------------------------------------

'action' Translated_size(TYPE_EXPR -> INT)

  'rule' Translated_size(unit -> N):
	 Int_size(-> N)

  'rule' Translated_size(int -> N):
	 Int_size(-> N)

  'rule' Translated_size(bool -> N):
	 Int_size(-> N)

  'rule' Translated_size(real -> 8)

  'rule' Translated_size(char -> N):
	 Threshold_size(-> M)
	 where(M + 1 -> N)
	 
  'rule' Translated_size(text -> N):
	 Threshold_size(-> M)
	 where(M + 1 -> N)

  'rule' Translated_size(product(list(T, P)) -> N):
	 Translated_size(T -> N1)
	 (|
	   eq(P, nil)
	   where(N1 -> N)
	 ||
	   Translated_size(product(P) -> N2)
	   where(N1 + N2 -> N)
	 |)
/*******
  'rule' Translated_size(fun(T1, partial, result(T2, _, _, _, _)) -> S):
	 Translated_size(T1 -> S1)
	 Translated_size(T2 -> S2)
	 Concatenate3(S1, "f", S2 -> S)
*******/

  'rule' Translated_size(infin_map(_, _) -> N):
	 Threshold_size(-> M)
	 where(M + 1 -> N)

  'rule' Translated_size(infin_set(_) -> N):
	 Threshold_size(-> M)
	 where(M + 1 -> N)

  'rule' Translated_size(infin_list(_) -> N):
	 Threshold_size(-> M)
	 where(M + 1 -> N)

  'rule' Translated_size(bracket(T) -> N):
	 Translated_size(T -> N)

  'rule' Translated_size(defined(Id, _) -> N):
	 Id'Ident -> Ident
	 Id'Type -> Type
	 (|
	   eq(Type, undef_type)
	   where(0 -> N)
	 ||
	   where(Type -> sort(K))
	   Threshold_size(-> M)
	   where(M + 1 -> N)
--	   (|
--	     where(K -> abstract)
--	     Threshold_size(-> M)
--	     where(M + 1 -> N)
--	   ||
--	     where(K -> record(Comps))
--	     Component_size(Comps -> N)
--	   ||
--	     where(K -> variant(Vs))
--	     Threshold_size(-> M)
--	     where(M + 1 -> N)
--	   /*
--	   ||
--	     where(K -> union(Choices))
--	   */
--	   |)
	 ||
	   where(Type -> abbrev(_))
	   Id'Def -> abbreviation(TExpr)
	   Translated_size(TExpr -> N)
	 |)

  'rule' Translated_size(TExpr -> N):
	 Maxtype(TExpr -> TExpr1)
	 ne(TExpr, TExpr1)
	 Translated_size(TExpr1 -> N)

  'rule' Translated_size(_ -> 0)


'action' Component_size(COMPONENTS -> INT)

  'rule' Component_size(list(component(_, _, T, _), Cs) -> N):
	 Translated_size(T -> N1)
	 Component_size(Cs -> N2)
	 where(N1 + N2 -> N)

  'rule' Component_size(nil -> 0):


'action' Int_size(-> INT)

  'rule' Int_size(-> 4)

'action' Ptr_size(-> INT)

  'rule' Ptr_size(-> N):
	 Int_size(-> N)

'action' Threshold_size(-> INT) -- converted to reference type if greater than this size

  'rule' Threshold_size(-> 8)

'action' C_Check_ambiguity(Value_ids)

  'rule' C_Check_ambiguity(nil):

  'rule' C_Check_ambiguity(list(I, Is)):
	 I'Ident -> Id
	 Split_by_id_or_op(Id, Is -> Is1, Is2)
	 -- do rest first so earlier ones reported earlier
	 -- (environment is reversed)
	 C_Check_ambiguity(Is2)
	 (|
	   CPP_different_funs(list(I, Is1))
	 ||
	   I'Pos -> P	
	   Putwarning(P)
	   Print_id_or_op(Id)
	   Putmsg(" is ambiguous in C++")
	   Putnl()
	 |)

-- splits second param into those with same id_or_op as first
-- and the rest
'action' Split_by_id_or_op(ID_OR_OP, Value_ids -> Value_ids, Value_ids)

  'rule' Split_by_id_or_op(_, nil -> nil, nil):

  'rule' Split_by_id_or_op(Id, list(I, Is) -> Is1, Is2)
	 Split_by_id_or_op(Id, Is -> Is11, Is21)
	 I'Ident -> Id1
	 (|
	   eq(Id, Id1)
	   where(Value_ids'list(I, Is11) -> Is1)
	   where(Is21 -> Is2)
	 ||
	   where(Is11 -> Is1)
	   where(Value_ids'list(I, Is21) -> Is2)
	 |)

-- true if all ids are of functions, maps or lists with different
-- argument types
'condition' CPP_different_funs(Value_ids)

  'rule' CPP_different_funs(list(_, nil)):

  'rule' CPP_different_funs(list(I, Is)):
	 I'Type -> T
	 Split_fun_type(T -> T1, _)
	 ne(T1, none)
	 CPP_different_arg_types(T1, Is)
	 CPP_different_funs(Is)

'condition' CPP_different_arg_types(TYPE_EXPR, Value_ids)

  'rule' CPP_different_arg_types(DT, list(I, Is)):
	 I'Type -> T
	 Split_fun_type(T -> DT1, _)
	 ne(DT1, none)
	 No_unification(DT, DT1)
	 CPP_different_arg_types(DT, Is)

  'rule' CPP_different_arg_types(_, nil):




-----------------------------------------------------------------------
-- test_case declarations
-----------------------------------------------------------------------

'type' TC_STRINGS

       list	(name	:	STRING,
		 type	:	C_TYPE_SPECIFIER,
		 tail	:	TC_STRINGS)
       nil

-- strings identifying test cases (in reverse order)
'var' test_case_ids : TC_STRINGS

'action' Collect_test_cases(DECLS)

  'rule' Collect_test_cases(list(D, DS)):
	 Collect_test_cases1(D)
	 Collect_test_cases(DS)

  'rule' Collect_test_cases(nil)


'action' Collect_test_cases1(DECL)

  'rule' Collect_test_cases1(test_case_decl(_, Defs)):
	 Collect_test_cases2(Defs)

  'rule' Collect_test_cases1(_):

'action' Collect_test_cases2(TEST_CASE_DEFS)

  'rule' Collect_test_cases2(list(D, DS)):
	 Test_cases -> TCs
	 Test_cases <- list(D, TCs)
	 Collect_test_cases2(DS)

  'rule' Collect_test_cases2(nil):


'action' Translate_test_case_defs(TEST_CASE_DEFS)
-- collection reverses the order, so reverse again
  'rule' Translate_test_case_defs(list(D, DS)):
	 Translate_test_case_defs(DS)
	 Translate_test_case_def(D)

  'rule' Translate_test_case_defs(nil):

'action' Translate_test_case_def(TEST_CASE_DEF)

  'rule' Translate_test_case_def(test_case_def(P, _, _)):
	 Get_current_test_cases(top -> TCS)
	 [|
	   Lookup_test_case(P, TCS -> I)
	   I'Ident -> Opt_id
	   I'Test_case -> V
	   I'Type -> T
	   I'Paths -> Paths
	   Extend_paths -> Save_paths
	   Extend_paths <- Paths
	   Translate_type(T -> T1)
	   Mk_test_case_id(Opt_id, T1 -> Id)
	   C_Begin_func_def(id(Id))
	     C_Add_decl_specifier(type(T1))
	     Translate_function_body(P, id_op(Id), nil, unit, T, V, nil, nil, nil, nil)
	   C_End_func_def(-> Fdef)
	   C_Decl_to_string_h(Fdef -> Sh) WriteHString(Sh)
	   C_Decl_to_string(Fdef -> Scc)	WriteCcString(Scc)
	   Extend_paths <- Save_paths
	 |]

'action' Mk_test_case_id(OPT_IDENT, C_TYPE_SPECIFIER -> IDENT)
	 
  'rule' Mk_test_case_id(ident(Id), T -> Fid):
	 id_to_string(Id -> S0)
	 test_case_ids -> STS
	 test_case_ids <- list(S0, T, STS)
	 Concatenate("RSL_test_case_", S0 -> S)
	 string_to_id(S -> Fid)

  'rule' Mk_test_case_id(nil, T -> Fid):
	 Mk_temp_id(nil -> TempId)
	 id_to_string(TempId -> S0)
	 test_case_ids -> STS
	 test_case_ids <- list(S0, T, STS)
	 Concatenate("RSL_test_case_", S0 -> S)
	 string_to_id(S -> Fid)

'action' Mk_main_function

  'rule' Mk_main_function:
	 string_to_id("main" -> Mid)
	 C_Begin_func_def(id(Mid))
	   test_case_ids -> STS
	   Add_test_case_invocations(STS)
	   (|
	     VisualCPP()  -- complains about int
	     C_Add_decl_specifier(type(void))
	   ||
	     C_Add_decl_specifier(type(int))
	   |)
	 C_End_func_def(-> Fdef)
	 C_Decl_to_string(Fdef -> Scc)	WriteCcString(Scc)

'action' Add_test_case_invocations(TC_STRINGS)

-- STS is in reverse order, so add last first
  'rule' Add_test_case_invocations(list(S, T, STS)):
	 Add_test_case_invocations(STS)
	 string_to_id("cout" -> Cout)
-- use endl rather than \n to ensure test cases are flushed 
         string_to_id("endl" -> Endl)
	 Concatenate3("[", S, "] " -> Stc)
	 Concatenate("RSL_test_case_", S -> S1)
	 string_to_id(S1 -> Fid)
	 where(postfix(name(id(Fid)), bracket(nil)) -> Arg)
	 (|
	   eq(T, void)
	   C_Add_function_body(
	     compound(
	       list(expr(Arg),
	       list(expr(
		    binary(name(id(Cout)),
			   shl,
			   binary(text_literal(Stc),
				  shl,
				  name(id(Endl))))),
	       nil))))
	     
	 ||
	   RSL_to_string_name(T -> NM)
	   where(postfix(name(NM), bracket(list(Arg, nil))) -> F)
	   C_Add_function_body(
	     expr(
	       binary(name(id(Cout)),
		      shl,
		      binary(text_literal(Stc),
			     shl,
			     binary(F, shl, name(id(Endl)))))))
	 |)		    
	 

  'rule' Add_test_case_invocations(nil):
	 C_Add_function_body(cpp(ifdef("RSL_boolalpha")))
	 string_to_id("cout" -> Cout)
	 string_to_id("boolalpha" -> BA)
	 C_Add_function_body(expr(binary(name(id(Cout)),
					 shl,
					 name(id(BA)))))
	 C_Add_function_body(cpp(endif("RSL_boolalpha")))

/*----
	   [|
	     ne(T1, void)
	     C_Begin_decl()
	       Mk_temp_id(nil -> TempId)
	       C_Add_decl_specifier(type(T1))
	       C_Add_declarator(dname(id(TempId)))
	     C_End_decl(-> TempVar)
	     C_Add_function_body(decl(TempVar))
	     C_Add_function_body(return(name(id(TempId))))
	   |]
----*/

-- currently always succeeds

'condition' IfIoWanted_cc

  'rule' IfIoWanted_cc:
	 WriteCcString("#ifdef RSL_io\n")

'action' EndIfIoWanted_cc

  'rule' EndIfIoWanted_cc:
	 WriteCcString("#endif //RSL_io\n")

'condition' IfIoWanted_h

  'rule' IfIoWanted_h:
	 WriteHString("#ifdef RSL_io\n")

'action' EndIfIoWanted_h

  'rule' EndIfIoWanted_h:
	 WriteHString("#endif //RSL_io\n")

'condition' IfIoWanted

  'rule' IfIoWanted:
	 IfIoWanted_h()
	 IfIoWanted_cc()

'action' EndIfIoWanted

  'rule' EndIfIoWanted:
	 EndIfIoWanted_h()
	 EndIfIoWanted_cc()

'action' Length_cs(COMPONENTS -> INT)

  'rule' Length_cs(list(_, Cs) -> N+1):
	 Length_cs(Cs -> N)

  'rule' Length_cs(nil -> 0):

--begin
'action' Add_to_table_types(TYPE_EXPR)

  'rule' Add_to_table_types(T):
	 [|
	   Type_matches_map(T)
	   Universal_type_id(T -> Id)
	   TableTypes -> Ids 
	   Add_uid(Id, Ids -> Ids1)
	   TableTypes <- Ids1
	 |]

-- id added only if not already present
'action' Add_uid(IDENT, IDENTS -> IDENTS)

  'rule' Add_uid(Id, list(Id1, Ids) -> list(Id1, Ids1)):
	 (|
	   eq(Id, Id1)
	   where(Ids -> Ids1)
	 ||
	   Add_uid(Id, Ids -> Ids1)
	 |)

  'rule' Add_uid(Id, nil -> list(Id, nil)):

'condition' Is_table_type(IDENT)

  'rule' Is_table_type(Id):
	 TableTypes -> Ids
	 Is_in_ids(Id, Ids)

'condition' Is_in_ids(IDENT, IDENTS)

  'rule' Is_in_ids(Id, list(Id1, Ids)):
	 (| eq(Id, Id1) || Is_in_ids(Id, Ids) |)


'action' Ident_to_cts(IDENT -> C_TYPE_SPECIFIER)
   'rule' Ident_to_cts(Id -> named_type(Id))

'action' String_to_cts(STRING -> C_TYPE_SPECIFIER)

  'rule' String_to_cts(S -> CT):
	 string_to_id(S -> Id)
	 Ident_to_cts(Id -> CT)



'action' Record_destructorsm(COMPONENTS, INT -> INT, C_TYPE_SPECIFIERS)

  'rule' Record_destructorsm(list(component(_, Destr, T, _), Cs), N ->
					       M, list(T1, list(T1M, list(CT, CTS)))):
	 (|
	   where(Destr -> dest_ref(VI))
	   VI'Ident -> Id_or_op
	   (|
	     where(Id_or_op -> id_op(I))
	     where(C_NAME'id(I) -> DN)
	   ||
	     where(Id_or_op -> op_op(Op))
	     Translate_op(Op -> Op1)
	     where(op_fun(Op1) -> DN)
	   |)
	   C_Name_to_string(DN -> DNStr) 
	   string_to_id(DNStr -> DNid)
	 ||
	   Mk_nth_field_id(N+1 -> DNid)
	 |)
	 Translate_type(T -> T1)
	 Make_mode_name(T1 -> T1M)
	 Ident_to_cts(DNid -> CT)
	 Record_destructorsm(Cs, N+1 -> M, CTS)

  'rule' Record_destructorsm(nil, N -> N, nil):


'action' Makeup_arglistm(C_TYPE_SPECIFIERS)

  'rule' Makeup_arglistm(list(T, Ts)):
	 (|
	   where(T -> named_type(Id))
	   C_Arg_declarator(dname(id(Id)))
	 ||
	   C_Type_to_string(T -> S)
	   string_to_id(S -> Id)
	   C_Arg_declarator(dname(id(Id)))
	 |)
	 Makeup_arglistm(Ts)

  'rule' Makeup_arglistm(nil):

'action' Product_types_field(C_TYPE_SPECIFIERS, INT -> INT, C_TYPE_SPECIFIERS)

  'rule' Product_types_field(list(CT, CTs), N -> 
				      M, list(CT, list(CT0, list(CT1, CTS1)))):
	 Make_mode_name(CT -> CT0)
	 Mk_nth_field_id(N+1 -> Id)
	 Ident_to_cts(Id -> CT1)
	 Product_types_field(CTs, N+1 -> M, CTS1) 
	
  'rule' Product_types_field(nil, N -> N, nil):

'action' Make_mode_name(C_TYPE_SPECIFIER -> C_TYPE_SPECIFIER)

  'rule' Make_mode_name(bool -> CT):
	 String_to_cts("BOOL" -> CT)

  'rule' Make_mode_name(int -> CT):
	 String_to_cts("INT" -> CT)

  'rule' Make_mode_name(double -> CT):
	 String_to_cts("REAL" -> CT)

  'rule' Make_mode_name(rsl_char -> CT):
	 String_to_cts("CHAR" -> CT)

  'rule' Make_mode_name(rsl_string -> CT):
	 String_to_cts("TEXT" -> CT)

  'rule' Make_mode_name(_ -> CT):
	 String_to_cts("OTHER" -> CT)

	  
'action' string_to_c_expr(STRING -> C_EXPR)

  'rule' string_to_c_expr(S -> C)
	 string_to_id(S -> I)
	 where(C_EXPR'postfix(name(id(I)), bracket(nil)) -> C)

--end



