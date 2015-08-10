-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the rsl->sml translator

'module' sml

'use' ast print ext env objects values types pp print cc cpp

'export' Init_SML_vars Init_SML_file Close_SML_file SML_global_object
	 Translate_to_SML
	 Extract_objects_in_declares Collect_object_idents  Uses_defs
	 Get_global_object_ids Type_is_product
	 Split_typing Split_restriction Dom_or_elems Matches_binding
	 Type_matches_set Type_matches_list Type_matches_map
	 Type_matches_text
	 Type_is_set Type_is_list Type_is_map Type_is_array Type_is_fun
	 Prune_object_ids1 Object_ids_to_object
	 Op_to_alpha_string
	 Matches_product_binding
--------------------------------------------------
-- types
--------------------------------------------------

'type' TYPE_ALIAS
       alias            (name   :       STRING,
                         expr   :       TYPE_EXPR)

'type' DATA_CONS
       cons             (name   :       STRING,
                         id	:       Value_id)

'type' DATA_CONS_LIST
       list             (head   :       DATA_CONS,
                         tail   :       DATA_CONS_LIST)
       nil

'type' TYPE_ALIASES     
       list             (head   :       TYPE_ALIAS,
                         tail   :       TYPE_ALIASES)
       nil

--'type' USER_TYPE_DEF    
--       type_def         (tid    :       Type_id,
--                         tdef   :       TYPE_DEF)

--'type' USER_TYPE_DEFS
--       list             (head   :       USER_TYPE_DEF,
--                         tail   :       USER_TYPE_DEFS)
--       nil

'type' TYPE_OPTION
       none
       some             (expr   :       TYPE_EXPR)

'type' OPT_VDEF
       value            (def    :       VALUE_DEF)
       variable         (def    :       VARIABLE_DEF)
       subtype_fun	(id	:	Value_id)

'type' OPT_VDEFS
       list             (head   :       OPT_VDEF,
                         tail   :       OPT_VDEFS)
       nil

'type' OPT_VDEFS_LIST
       list             (head   :       OPT_VDEFS,
                         tail   :       OPT_VDEFS_LIST)
       nil

'type' VARIANT_OR_RECORD
       variant
       record

--------------------------------------------------
-- variables
--------------------------------------------------

-- type exprs already defined in some SML text
-- these exprs are stored in the ENV and identified by Type_id
----------------------------------------------------
'var' Var_aliased_types         : TYPE_ALIASES

'var' Var_defined_aliases       : TYPE_ALIASES

'var' Var_extracted_value_ids   : Value_ids

'var' Var_extracted_variable_ids: Variable_ids

'var' Var_data_cons_list        : DATA_CONS_LIST

-- stack of objects currently being defined
-- latest at front
'var' Var_objects		: Object_ids

-- Coverage regions

'var' Var_regions		: REGIONS

--------------------------------------------------

'condition' False_cond

  'rule' False_cond:
         eq(0, 1)

'action' Internal_error(OPT_POS, STRING)
         
  'rule' Internal_error(PosO, S):
         [|
           where(PosO -> pos(Pos))
           Puterror(Pos)
         |]
         Putmsg("Internal error: ")
         ErrorUsage(S)

'action' Not_support(OPT_POS, STRING)

  'rule' Not_support(PosO, S):
         [|
           where(PosO -> pos(Pos))
           Puterror(Pos)
         |]
         Putmsg("Feature not supported: ")
         Putmsg(S)
         Putnl
         -- False_cond

'action' Err_default_value
         
  'rule' Err_default_value:
         Putmsg("Error in generating default value")
         Putnl       
         -- False_cond

'action' Not_resolved(POS, STRING)

  'rule' Not_resolved(Pos, S):
         Puterror(Pos)
         Putmsg("Not resolved: ")
         Putmsg(S)
         Putnl

--'action' Rev_type_aliases(TYPE_ALIASES, TYPE_ALIASES -> TYPE_ALIASES)

--  'rule' Rev_type_aliases(TaLin, TaLacc -> TaLout):
--         (|
--           where(TaLin -> list(T, Tail))
--           Rev_type_aliases(Tail, list(T, TaLacc) -> TaLout)
--         ||
--           where(TaLin -> nil)
--           where(TaLacc -> TaLout)
--         |)

'action' LParen

  'rule' LParen:
         WriteFile("(")

'action' RParen

  'rule' RParen:
         WriteFile(")")

'action' Id_or_op_to_SML_id(ID_OR_OP, OPT_QUALIFICATION -> STRING)

  'rule' Id_or_op_to_SML_id(Id, QO -> S):
         Id_or_op_to_alpha_string(Id -> S1)
         (|
           where(QO -> qualification(Obj))
           Object_to_string(Obj -> S0)
           GetF2String("%s.%s_", S0, S1 -> S)
         ||
           where(QO -> nil)
           GetFString("%s_", S1 -> S)
         |)
         

'action' Id_to_SML_id(IDENT, OPT_QUALIFICATION -> STRING)

  'rule' Id_to_SML_id(Id, QO -> S):
         Id_or_op_to_SML_id(id_op(Id), QO -> S)

--------------------------------------------------

'condition' Type_is_set(TYPE_EXPR -> TYPE_EXPR)

  'rule' Type_is_set(T -> ET):
	 Get_abbrev_type(T -> T1)
         (|
           where(T1 -> fin_set(ET))
         ||
           where(T1 -> infin_set(ET))
	 |)

'condition' Type_is_list(TYPE_EXPR -> TYPE_EXPR)
   
  'rule' Type_is_list(T -> ET):
	 Get_abbrev_type(T -> T1)
         (|
           where(T1 -> fin_list(ET))
         ||
           where(T1 -> infin_list(ET))
	 ||
	   where(T1 -> text)
	   where(TYPE_EXPR'char -> ET)
	 |)
         
'condition' Type_is_map(TYPE_EXPR -> TYPE_EXPR, TYPE_EXPR)

  'rule' Type_is_map(T -> DT, RT):
	 Get_abbrev_type(T -> T1)
         (|
           where(T1 -> fin_map(DT, RT))
         ||
           where(T1 -> infin_map(DT, RT))
	 |)

'condition' Type_is_array(TYPE_EXPR -> TYPE_EXPR, TYPE_EXPR)

  'rule' Type_is_array(T -> DT, RT):
	 Get_abbrev_type(T -> T1)
           where(T1 -> array(DT, RT))

'condition' Type_is_fun(TYPE_EXPR -> TYPE_EXPR, FUNCTION_ARROW, TYPE_EXPR)

  'rule' Type_is_fun(T -> PT, Arrow, RT):
	 Get_abbrev_type(T -> T1)
         (|
           where(T1 -> fun(PT, Arrow, result(RT, _, _, _, _)))
         ||
           where(T1 -> function(PT, Arrow, result(_, RT)))
	 |)

'condition' Type_is_product(TYPE_EXPR -> PRODUCT_TYPE)

  'rule' Type_is_product(T -> XT):
	 Get_abbrev_type(T -> T1)
	 where(T1 -> product(XT))
	 
         
--------------------------------------------------


'condition' Search_value_id_in_list(Value_id, Value_ids)

  'rule' Search_value_id_in_list(VI, VIL):
         where(VIL -> list(VI1, Tail))
         (|
           eq(VI, VI1)
         ||
           Search_value_id_in_list(VI, Tail)
         |)

'condition' Value_id_type_extracted(Value_id)

  'rule' Value_id_type_extracted(VI):
         Var_extracted_value_ids -> VIL
         (|
           Search_value_id_in_list(VI, VIL)
         ||
           Var_extracted_value_ids <- list(VI, VIL)
           False_cond
         |)

'condition' Search_variable_id_in_list(Variable_id, Variable_ids)

  'rule' Search_variable_id_in_list(VarI, VarIL):
         where(VarIL -> list(VarI1, Tail))
         (|
           eq(VarI, VarI1)
         ||
           Search_variable_id_in_list(VarI, Tail)
         |)

'condition' Variable_id_type_extracted(Variable_id)

  'rule' Variable_id_type_extracted(VarI):
         Var_extracted_variable_ids -> VarIL
         (|
           Search_variable_id_in_list(VarI, VarIL)
         ||
           Var_extracted_variable_ids <- list(VarI, VarIL)
           False_cond
         |)

-------------------------------------------------- 

'condition' Match_type(TYPE_EXPR, TYPE_EXPR)

  'rule' Match_type(T, T1):
         Match(T, nil, T1)

'condition' Match_type_in_aliases(TYPE_EXPR, TYPE_ALIASES -> STRING)

  'rule' Match_type_in_aliases(T, TAL -> S):
         where(TAL -> list(TA, Tail))
         (|
           where(TA -> alias(S, T1))
           Match_type(T, T1)
         ||
           Match_type_in_aliases(T, Tail -> S)
         |)

'condition' Lookup_aliased_type(TYPE_EXPR -> STRING)

  'rule' Lookup_aliased_type(T -> S):
         Var_aliased_types -> TaL
         Match_type_in_aliases(T, TaL -> S)

'action' Get_aliased_type(TYPE_EXPR -> STRING)

  'rule' Get_aliased_type(T -> S):
         Up_type(T -> T1)
         Lookup_aliased_type(T1 -> S)

'condition' Lookup_defined_alias(TYPE_EXPR -> STRING)

  'rule' Lookup_defined_alias(T -> S):
         Var_defined_aliases -> TaL
         Match_type_in_aliases(T, TaL -> S)

'action' Get_defined_alias(TYPE_EXPR -> STRING)

  'rule' Get_defined_alias(T -> S):
         Up_type(T -> T1)
         (|
           Lookup_defined_alias(T1 -> S)
         ||
--           [|
--             where(T1 -> defined(I,_))
--             I'Ident -> Id
--             Id_to_SML_id(Id, nil -> S1)
--             print(S1)
--             I'Type -> TY
--             where(TY -> abbrev(T2))
--             print(T2)
--           |]
           where("" -> S)
	   DefaultPos( -> P)
	   Puterror(P)
	   Putmsg("Internal error: no type alias for type ")
	   Print_type(T1)
	   Putnl()
--           False_cond
         |)

'action' Add_defined_alias(TYPE_ALIAS)

  'rule' Add_defined_alias(Ta):
         Var_defined_aliases -> TaL
         Var_defined_aliases <- list(Ta, TaL)
-- debug
-- Done_count -> N
-- Done_count <- N+1

'action' Remove_last_defined_alias

  'rule' Remove_last_defined_alias:
	 Var_defined_aliases -> list(_, TaL)
	 Var_defined_aliases <- TaL
-- debug
-- Done_count -> N
-- Done_count <- N-1

--------------------------------------------------

'condition' Named_type_expr(TYPE_EXPR -> TYPE_EXPR)
  
  'rule' Named_type_expr(T -> defined(I, Q)):
         (|
           where(T -> defined(I, Q))
         ||
           where(T -> named_type(_))
           Resolve_type(T -> defined(I, Q))
         |)

'condition' Named_type_is_abbrev(Type_id -> TYPE_EXPR)
 
  'rule' Named_type_is_abbrev(I -> T):
         I'Def -> TY
	 (|
	   where(TY -> abbreviation(T))
	 ||
	   I'Type -> TY1
	   where(TY1 -> abbrev(T1))
	   Resolve_type(T1 -> T)
	 |)

'condition' Ident_to_type_expr(POS, IDENT -> TYPE_EXPR)
         
  'rule' Ident_to_type_expr(Pos, Id -> T):
         Named_type_expr(named_type(name(Pos, id_op(Id))) -> T)

--------------------------------------------------

'action' Add_data_constructor(STRING, Value_id)

  'rule' Add_data_constructor(S, I):
         Var_data_cons_list -> L
         Var_data_cons_list <- list(cons(S, I), L)

'condition' Lookup_data_constructor_in_list(DATA_CONS_LIST, Value_id -> STRING)

  'rule' Lookup_data_constructor_in_list(L, I -> S):
         where(L -> list(DC, Tail))
         (|
           where(DC -> cons(S, I1))
           eq(I, I1)
         ||
           Lookup_data_constructor_in_list(Tail, I -> S)
         |)

'condition' Lookup_data_constructor(Value_id -> STRING)

  'rule' Lookup_data_constructor(I -> S):
         Var_data_cons_list -> L
         Lookup_data_constructor_in_list(L, I -> S)

--------------------------------------------------

'action' New_SML_struct_name(STRING -> STRING)

  'rule' New_SML_struct_name(Prefix -> S):
         NewSeqNum(->N)
         Int_to_string(N -> S1)
         GetF2String("RT_%s%s", Prefix, S1 -> S)

'action' New_temp_name(STRING -> STRING)

  'rule' New_temp_name(Prefix -> S):
         NewSeqNum(->N)
         Int_to_string(N -> S1)
         GetF2String("%s%s", Prefix, S1 -> S)

'action' Add_type_alias(STRING, TYPE_EXPR)
  
  'rule' Add_type_alias(S, T):
         Var_aliased_types -> TaL
         Var_aliased_types <- list(alias(S, T), TaL)
-- debug
-- Putmsg(S)
-- Putmsg(" aliased to ")
-- Print_type(T)
-- Putnl

'action' Up_type(TYPE_EXPR -> TYPE_EXPR)

  'rule' Up_type(T -> T1):
         (|
           where(T -> fin_set(TE))
           where(infin_set(TE) -> T1)
         ||
           where(T -> fin_list(TE))
           where(infin_list(TE) -> T1)
         ||
           where(T -> fin_map(TD, TR))
           where(infin_map(TD, TR) -> T1)
         ||
           where(T -> T1)
         |)   

'action' Alias_types_in_product(PRODUCT_TYPE)

  'rule' Alias_types_in_product(XT):
         (|
           where(XT -> list(T1, Tail))
           Alias_type_0(T1)
           Alias_types_in_product(Tail)
         ||
           where(XT -> nil)
         |)
           
'action' Alias_type_0(TYPE_EXPR)

  'rule' Alias_type_0(T):
         (| -- do subtypes first to ensure restriction dealt with
           where(T -> subtype(single(_,_,T1), R))
           Alias_type_0(T1)
	   Extract_types_in_restr(R)
         ||
           Lookup_defined_alias(T -> _)
         ||
           Lookup_aliased_type(T -> _)
         ||
           where(T -> unit)
           Add_type_alias("RT_Unit", T)
         ||
           where(T -> bool)
           Add_type_alias("RT_Bool", T)
         ||
           where(T -> int)
           Add_type_alias("RT_Int", T)
         ||
           where(T -> nat)
           Add_type_alias("RT_Nat", T)
         ||
           where(T -> real)
           Add_type_alias("RT_Real", T)
         ||
           where(T -> text)
           Add_type_alias("RT_Text", T)
         ||
           where(T -> char)
           Add_type_alias("RT_Char", T)
         ||
           where(T -> defined(I, Q))
           (|
             Named_type_is_abbrev(I -> T1)
             Alias_type_0(T1)
           ||
             I'Ident -> Id
             Id_to_SML_id(Id, nil -> S1)
             GetFString("u_%s_", S1 -> S2)
             New_SML_struct_name(S2 -> US)
             Add_type_alias(US, T)
           |)
         ||
           where(T -> product(XT))
           Alias_types_in_product(XT)
           New_SML_struct_name("x_" -> PS)
           Add_type_alias(PS, T)
         ||
           Type_is_set(T -> TE)
           Alias_type_0(TE)
           New_SML_struct_name("s_" -> SS)
           Add_type_alias(SS, T)
         ||
           Type_is_list(T -> TE)
           (|
             Get_abbrev_type(TE -> T1)
             where(T1 -> char)
             Add_type_alias("RT_Text", T)
           ||
             Alias_type_0(TE)
             New_SML_struct_name("l_" -> LS)
             Add_type_alias(LS, T)
           |)
         ||
           Type_is_map(T -> TD, TR)
           Alias_type_0(TD)
           Alias_type_0(TR)
           New_SML_struct_name("m_" -> MS)
           Add_type_alias(MS, T)
         ||
           Type_is_fun(T -> TP, _, TR)
           Alias_type_0(TP)
           Alias_type_0(TR)
           New_SML_struct_name("f_" -> FS)
           Add_type_alias(FS, T)
         ||
           where(T -> bracket(T1))
           Alias_type_0(T1)
         ||
           print(T)
           Internal_error(no_pos, "Alias_type_0")
         |)

'action' Alias_type(TYPE_EXPR)

  'rule' Alias_type(T):
         Resolve_type(T -> T1)
         Alias_type_0(T1)

--------------------------------------------------

'action' Init_SML_vars

  'rule' Init_SML_vars:
         Var_aliased_types <- nil
         Var_defined_aliases <- nil
         Var_extracted_value_ids <- nil
         Var_extracted_variable_ids <- nil
         Var_data_cons_list <- nil
	 Var_objects <- nil
	 Var_regions <- nil

'action' Init_SML_file

  'rule' Init_SML_file:
         Module_name -> S
         string_to_id(S -> Id)
         OpenSMLFile(Id -> _)
         SetFileIndentSpace(4)
	 -- keep the compilation manager relatively quiet
	 WriteFile("#set CM.Control.verbose false;")
         WritelnFile(1)
	 -- load the compiler
	 WriteFile("CM.autoload \"$smlnj/compiler/compiler.cm\";")
	 WritelnFile(1)
	 -- reduce the amount of output
         WriteFile("Compiler.Control.Print.signatures := 0;")
         WritelnFile(1)
         WriteFile("Compiler.Control.Print.printOpens := false;")
         WritelnFile(1)
	 -- prevent garbage collection messages
	 WriteFile("SMLofNJ.Internals.GC.messages false;")
	 WritelnFile(1)
         Get_env_string("RSLML_PATH", "/usr/share/rsltc/sml" -> SPath)
	 Dos_to_Unix(SPath -> SPath1)
-- debug
-- Putmsg(SPath)
-- Putmsg(" changed to ")
-- Putmsg(SPath1)
-- Putnl
         WriteFFile("CM.autoload \"%s/rslml.cm\";", SPath1)
         WritelnFile(1)
	 WriteFFile("use \"%s_.sml\" handle RSL.RSL_exception s => TextIO.print (s ^ \"\\n\") | RSL.swap s => TextIO.print (s ^ \"\\n\");", S)
         WritelnFile(2)
	 CloseOutputFile()
	 Concatenate(S, "_" -> S2)
	 string_to_id(S2 -> Id2)
         OpenSMLFile(Id2 -> _)

'action' Close_SML_file

  'rule' Close_SML_file:
         CloseOutputFile()
         Module_name -> S
         Putmsg("SML output is in files ")
         Putmsg(S)
	 Putmsg(".sml and ")
	 Putmsg(S)
	 Putmsg("_.sml")
         Putnl()

--------------------------------------------------

'action' Translate_to_SML(IDENT, CLASS)
-- SML_main_module

  'rule' Translate_to_SML(Id, CL):
         (|
           HasErrors()
           Putmsg("Errors found, so SML translation cannot be generated")
           Putnl()
         ||
           Get_current_with(-> Objs)
           Open_globals(Objs)
           SML_translate_class(Id, CL)
           id_to_string(Id -> S)
           Open_withs(S, Id, Objs)
           Emit_test_cases(S)
           Close_SML_file
         |)

'action' SML_translate_class(IDENT, CLASS)

  'rule' SML_translate_class(Id, CL):
         Resolve_class(CL)
         Var_aliased_types <- nil
         Extract_types_in_class(CL)
         Define_types
         id_to_string(Id -> S)
         Define_class(S, Id, CL)

'action' SML_global_object(IDENT, Object_id, CLASS)

  'rule' SML_global_object(Id, I, CL):
         (|
           HasErrors()  -- no need for message: generated in Translate_to_SML
         ||
           I'Params -> nil
	   Push_object(I)
           SML_translate_class(Id, CL)
	   Pop_object()
         ||
           I'Pos -> Pos
           Not_support(pos(Pos), "object array")
         |)

---------------------------------------------------

'action' Extract_types_in_class(CLASS)

  'rule' Extract_types_in_class(CL):
         (|
           where(CL -> basic(DL))
           Extract_types_in_decls(DL)
         ||
           where(CL -> extend(CL1, CL2))
           In_left
           Extract_types_in_class(CL1)
           Left_right
           Extract_types_in_class(CL2)
           Out_right
         ||
           where(CL -> hide(_, CL1))
           Extract_types_in_class(CL1)
         ||
           where(CL -> rename(_, CL1))
           Extract_types_in_class(CL1)
         ||
           where(CL -> with(_, _, CL1))
           Extract_types_in_class(CL1)
         ||
           where(CL -> instantiation(name(Pos, id_op(Id)), Objs))
           Get_id_of_scheme(Id -> scheme_id(I))
           I'Class -> CL1
           Extract_types_in_class(CL1)
         |)

---------------------------------------------------

'action' Extract_types_in_decls(DECLS)

  'rule' Extract_types_in_decls(DL):
         (|
           where(DL -> list(D, Tail))
           (|
             where(D -> type_decl(_, TDL))
             Extract_types_in_type_defs(TDL)
           ||
             where(D -> value_decl(_, VDL))
             Extract_types_in_value_defs(VDL)
           ||
             where(D -> variable_decl(_, VarDL))
             Extract_types_in_variable_defs(VarDL)
           ||
             where(D -> channel_decl(Pos, ChDL))
             Extract_types_in_channel_defs(Pos, ChDL)
           ||
             where(D -> object_decl(_, ODL))
             Extract_types_in_object_defs(ODL)
           ||
             where(D -> axiom_decl(Pos, ADL))
             Extract_types_in_axiom_defs(Pos, ADL)
           ||
             where(D -> test_case_decl(_, ADL))
             Extract_types_in_test_case_defs(ADL)
	   ||
	     where(D -> trans_system_decl(_,_))
	   ||
	     where(D -> property_decl(_,_))
           |)
           Extract_types_in_decls(Tail)
         ||
           where(DL -> nil)
         |)

---------------------------------------------------

'action' Extract_types_in_typing(TYPING)

  'rule' Extract_types_in_typing(TG):
         (| 
           where(TG -> single(_, _, T))
         || 
           where(TG -> multiple(_, _, T))
         |)
         Alias_type(T)

'action' Extract_types_in_typing_list(TYPINGS)
  
  'rule' Extract_types_in_typing_list(TGL):
         (|
           where(TGL -> list(TG, Tail))
           Extract_types_in_typing(TG)
           Extract_types_in_typing_list(Tail)
         ||
           where(TGL -> nil)
         |)

'action' Extract_types_in_value_list(VALUE_EXPRS)

  'rule' Extract_types_in_value_list(VL):
         (| 
           where(VL -> list(V, Tail))
           Extract_types_in_value_expr(V)
           Extract_types_in_value_list(Tail)
         ||
           where(VL -> nil)
         |)

'action' Extract_types_in_value_pair(VALUE_EXPR_PAIR)

  'rule' Extract_types_in_value_pair(VP)
         where(VP -> pair(V1, V2))
         Extract_types_in_value_expr(V1)
         Extract_types_in_value_expr(V2)

'action' Extract_types_in_value_pair_list(VALUE_EXPR_PAIRS)

  'rule' Extract_types_in_value_pair_list(VPL):
         (| 
           where(VPL -> list(VP, Tail))
           Extract_types_in_value_pair(VP)
           Extract_types_in_value_pair_list(Tail)
         ||
           where(VPL -> nil)
         |)

'action' Extract_types_in_restr(RESTRICTION)

  'rule' Extract_types_in_restr(R):
         [|
           where(R -> restriction(_, V))
           Extract_types_in_value_expr(V)
         |]

'action' Extract_types_in_set_limit(SET_LIMITATION)

  'rule' Extract_types_in_set_limit(Limit):
         where(Limit -> set_limit(_, TGL, R))
         Extract_types_in_typing_list(TGL)
         Extract_types_in_restr(R)

'action' Extract_types_in_list_limit(LIST_LIMITATION)

  'rule' Extract_types_in_list_limit(Limit):
         where(Limit -> list_limit(_, _, V, R))
         Extract_types_in_value_expr(V)
         Extract_types_in_restr(R)

'action' Extract_types_in_lambda_param(LAMBDA_PARAMETER)

  'rule' Extract_types_in_lambda_param(P):
         (|
           where(P -> l_typing(_, TGL))
           Extract_types_in_typing_list(TGL)
         ||
           where(P -> s_typing(_, TG))
           Extract_types_in_typing(TG)
         |)

'action' Extract_types_in_actual_param(ACTUAL_FUNCTION_PARAMETER)

  'rule' Extract_types_in_actual_param(A):
         where(A -> fun_arg(_, VL))
         Extract_types_in_value_list(VL)

'action' Extract_types_in_actual_param_list(ACTUAL_FUNCTION_PARAMETERS)

  'rule' Extract_types_in_actual_param_list(AL):
         (|
           where(AL -> list(A, Tail))
           Extract_types_in_actual_param(A)
           Extract_types_in_actual_param_list(Tail)
         ||
           where(AL -> nil)
         |)

'action' Extract_types_in_opt_post(OPT_POST_CONDITION)

  'rule' Extract_types_in_opt_post(post(Post)):
	 Extract_types_in_post_cond(Post)

  'rule' Extract_types_in_opt_post(nil):

'action' Extract_types_in_pre_cond(PRE_CONDITION)

  'rule' Extract_types_in_pre_cond(Pre):
         (|
           where(Pre -> pre_cond(_, V))
           Extract_types_in_value_expr(V)
         ||
           where(Pre -> nil)
         |)

'action' Extract_types_in_opt_cond(OPT_CONDITION)

  'rule' Extract_types_in_opt_cond(Opt):
         (|
           where(Opt -> condition(V))
           Extract_types_in_value_expr(V)
         ||
           where(Opt -> nil)
         |)

'action' Extract_types_in_post_cond(POST_CONDITION)

  'rule' Extract_types_in_post_cond(Post):
         where(Post -> post_cond(_, _, V))
         Extract_types_in_value_expr(V)  

'action' Extract_types_in_literal(VALUE_LITERAL)

  'rule' Extract_types_in_literal(Lit):
         (|
           where(Lit -> unit)
           Alias_type_0(unit)
         ||
           (| where(Lit -> bool_true) || where(Lit -> bool_false) |)
           Alias_type_0(bool)
         ||
           where(Lit -> int(_))
           Alias_type_0(int)
         ||
           where(Lit -> real(_))
           Alias_type_0(real)
         ||
           where(Lit -> text(_))
           Alias_type_0(text)
         ||
           where(Lit -> char(_))
           Alias_type_0(char)
         |)

'action' Extract_types_in_pattern(PATTERN)

  'rule' Extract_types_in_pattern(P):
         (|
           where(P -> literal_pattern(_, Lit))
           Extract_types_in_literal(Lit)
         ||
           where(P -> name_pattern(_, _))
         ||
           where(P -> record_pattern(_, _, PL))
           Extract_types_in_pattern_list(PL)
         ||
           where(P -> id_pattern(_, _))
         ||
           where(P -> wildcard_pattern(_))
         ||
           where(P -> product_pattern(_, PL))
           Extract_types_in_pattern_list(PL)
         ||
           where(P -> enum_list(_, PL))
           Extract_types_in_pattern_list(PL)
         ||
           where(P -> conc_list(_, PL, P1))
           Extract_types_in_pattern_list(PL)
           Extract_types_in_pattern(P1)
         ||
           where(P -> name_occ_pattern(_, VI, _))
           Extract_types_in_value_id(VI)
         ||
           where(P -> record_occ_pattern(_, VI, _, PL))
	   -- Do we need types of applied functions?
           -- Extract_types_in_value_id(VI)
           Extract_types_in_pattern_list(PL)
         |)

'action' Extract_types_in_pattern_list(PATTERNS)
      
  'rule' Extract_types_in_pattern_list(PL):
         (|
           where(PL -> list(P, Tail))
           Extract_types_in_pattern(P)
           Extract_types_in_pattern_list(Tail)
         ||
           where(PL -> nil)
         |)

'action' Extract_types_in_let_defs(LET_DEFS)

  'rule' Extract_types_in_let_defs(LDL):
         (|
           where(LDL -> list(LD, Tail))
           (|
             where(LD -> explicit(_, LB, V))
             (|
               where(LB -> binding(_, _))
             ||
               where(LB -> pattern(_, P))
               Extract_types_in_pattern(P)
             |)
             Extract_types_in_value_expr(V)
           ||
             where(LD -> implicit(_, TG, R))
             Extract_types_in_typing(TG)
             Extract_types_in_restr(R)
--           Not_support(pos(Pos), "implicit let def")
           |)
           Extract_types_in_let_defs(Tail)
         ||
           where(LDL -> nil)
         |)

'action' Open_local_decls(DECLS -> PATHS)

  'rule' Open_local_decls(DL -> Paths)
         Get_current_with(-> WITH)
         Current -> C
         Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,WITH,nil), C)
         Extend_paths -> Paths
         Extend_paths <- list(nil,Paths)
         Make_basic_env(basic(DL))
         Complete_type_env(basic(DL))
         Make_value_env(basic(DL))
         Check_value_env(basic(DL))

'action' Close_local_decls(PATHS)

  'rule' Close_local_decls(Paths)
         Current -> current_env(CE, C1)
         Current <- C1
         Extend_paths <- Paths

'action' Extract_types_in_local_expr(DECLS, VALUE_EXPR)

  'rule' Extract_types_in_local_expr(DL, V):
         Open_local_decls(DL -> Paths)
         Extract_types_in_decls(DL)
         Extract_types_in_value_expr(V)
         Close_local_decls(Paths)

'action' Open_local_env(CLASS_ENV -> PATHS)

  'rule' Open_local_env(CE -> Paths):
         Current -> C
         Current <- current_env(CE, C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil, Paths)
         
'action' Close_local_env(PATHS)

  'rule' Close_local_env(Paths):
         Current -> current_env(_, C)
         Current <- C
	 Extend_paths <- Paths

'action' Extract_types_in_env_local(DECLS, CLASS_ENV, VALUE_EXPR)

  'rule' Extract_types_in_env_local(DL, CE, V):
         Open_local_env(CE -> Paths)
         Extract_types_in_decls(DL)
         Extract_types_in_value_expr(V)
         Close_local_env(Paths)

'action' Extract_types_in_elif_branches(ELSIF_BRANCHES)

  'rule' Extract_types_in_elif_branches(ELIFL):
         (|
           where(ELIFL -> list(ELIF, Tail))
           where(ELIF -> elsif(_, V1, V2, _))
           Extract_types_in_value_expr(V1)
           Extract_types_in_value_expr(V2)
           Extract_types_in_elif_branches(Tail)
         ||
           where(ELIFL -> nil)
         |)

'action' Extract_types_in_else_branch(ELSE_BRANCH)
       
  'rule' Extract_types_in_else_branch(EL):
         (|
           where(EL -> else(_, V))
           Extract_types_in_value_expr(V)
         ||
           where(EL -> nil)
         |)

'action' Extract_types_in_case_branches(CASE_BRANCHES)

  'rule' Extract_types_in_case_branches(CBL):
         (|
           where(CBL -> list(CB, Tail))
           where(CB -> case(_, P, V, _))
           Extract_types_in_pattern(P)
           Extract_types_in_value_expr(V)
           Extract_types_in_case_branches(Tail)
         ||
           where(CBL -> nil)
         |)

'action' Extract_types_in_value_definition(VALUE_DEFINITION)

  'rule' Extract_types_in_value_definition(VDF):
         (|
           where(VDF -> no_def)
         ||
           where(VDF -> expl_val(V, Cond))
           Extract_types_in_value_expr(V)
	   Extract_types_in_opt_cond(Cond)
         ||
           where(VDF -> expl_fun(FFP, V, Post, Pre, Cond, PCond))
           Extract_types_in_value_expr(V)
	   Extract_types_in_opt_post(Post)
           Extract_types_in_pre_cond(Pre)
	   Extract_types_in_opt_cond(Cond)
	   Extract_types_in_opt_cond(PCond)
         |)

'action' Extract_types_in_value_id(Value_id)

  'rule' Extract_types_in_value_id(VI):
         (|
           Value_id_type_extracted(VI)
         ||
           VI'Type -> T
           Alias_type_0(T)
           VI'Ident -> Id_or_op
           (|
             where(Id_or_op -> op_op(_))
           ||
             VI'Def -> VDF
             Extract_types_in_value_definition(VDF)
           |)
         |)

'action' Extract_types_in_variable_id(Variable_id)

  'rule' Extract_types_in_variable_id(VarI):
         (|
           Variable_id_type_extracted(VarI)
         ||
           VarI'Type -> T
           Alias_type_0(T)
           VarI'Init -> Init1
           (|
             where(Init1 -> initial(V))
             Extract_types_in_value_expr(V)
	     VarI'Subtype -> Cond
	     Extract_types_in_opt_cond(Cond)
           ||
             where(Init1 -> nil)
           |)
         |)

'action' Value_to_type(VALUE_EXPR -> TYPE_EXPR)

  'rule' Value_to_type(V -> T):
         Make_results(V -> list(result(T, _, _, _, _), _))

-- debug
--  'rule' Value_to_type(V -> any):
--       Make_results(V -> R)
-- Print_expr(V)
-- Putnl
-- print(V)
-- print(R)


'action' Alias_type_of_value_expr(VALUE_EXPR)

  'rule' Alias_type_of_value_expr(V):
         Value_to_type(V -> T)
         Alias_type(T)

'action' Extract_types_in_value_expr(VALUE_EXPR)

  'rule' Extract_types_in_value_expr(V):
         (|
           where(V -> literal_expr(_, Lit))
           Extract_types_in_literal(Lit)
           Alias_type_of_value_expr(V)
         ||
           where(V -> named_val(Pos, _))
           Not_resolved(Pos, "named_val")
         ||
           where(V -> pre_name(Pos, _))
           Not_resolved(Pos, "pre_name")
         ||
           where(V -> chaos(_))
           Alias_type_of_value_expr(V)
         ||
           where(V -> skip(_))
           Alias_type_of_value_expr(V)
         ||
           where(V -> stop(_))
           Alias_type_of_value_expr(V)
         ||
           where(V -> swap(_))
           Alias_type_of_value_expr(V)
         ||
           where(V -> product(_, VL))
           Extract_types_in_value_list(VL)
           Alias_type_of_value_expr(V)
         ||
           where(V -> ranged_set(_, V1, V2))
           Extract_types_in_value_expr(V1)
           Extract_types_in_value_expr(V2)
           Alias_type_of_value_expr(V)
         ||
           where(V -> enum_set(_, VL))
           Extract_types_in_value_list(VL)
           Alias_type_of_value_expr(V)
         ||
           where(V -> comp_set(_, V1, set_limit(_, TGL, R)))
           Extract_types_in_value_expr(V1)
           Extract_types_in_typing_list(TGL)
           Extract_types_in_restr(R)
           Alias_type_of_value_expr(V)
         ||
           where(V -> ranged_list(_, V1, V2))
           Extract_types_in_value_expr(V1)
           Extract_types_in_value_expr(V2)
           Alias_type_of_value_expr(V)
         ||
           where(V -> enum_list(_, VL))
           Extract_types_in_value_list(VL)
           Alias_type_of_value_expr(V)
         ||
           where(V -> comp_list(_, V1, list_limit(_, B, VL, R)))
           Extract_types_in_value_expr(V1)
           Extract_types_in_value_expr(VL)
           Extract_types_in_restr(R)
           Alias_type_of_value_expr(V)
         ||
           where(V -> enum_map(_, VPL))
           Extract_types_in_value_pair_list(VPL)
           Alias_type_of_value_expr(V)
         ||
           where(V -> comp_map(_, VP, set_limit(_, TGL, R)))
           Extract_types_in_value_pair(VP)
           Extract_types_in_typing_list(TGL)
           Extract_types_in_restr(R)
           Alias_type_of_value_expr(V)
         ||
           where(V -> function(_, P, V1))
           Extract_types_in_lambda_param(P)
           Extract_types_in_value_expr(V1)
           Alias_type_of_value_expr(V)
         ||
           where(V -> application(_, F, AL))
	   -- Do we need types of function names that are just applied? TODO
	   (|
	     where(F -> val_occ(_,_,_))
	   ||
	     Extract_types_in_value_expr(F)
	   |)
           Extract_types_in_actual_param_list(AL)
           Alias_type_of_value_expr(V)
         ||
           where(V -> quantified(Pos, _, TGL, R))
           Extract_types_in_typing_list(TGL)
           Extract_types_in_restr(R)       
         ||
           where(V -> equivalence(Pos, V1, V2, Pre))
           Not_support(pos(Pos), "equivalence")
         ||
           where(V -> post(Pos, V1, Post, Pre))
           Not_support(pos(Pos), "post condition")         
         ||
           where(V -> disamb(_, V1, T))
           Alias_type(T)
           Extract_types_in_value_expr(V1)
         ||
           where(V -> bracket(_, V1))
           Extract_types_in_value_expr(V1)
         ||
           where(V -> ax_infix(_, V1, _, V2, _))
           Extract_types_in_value_expr(V1)
           Extract_types_in_value_expr(V2)
           Alias_type_of_value_expr(V)
         ||
           where(V -> val_infix(Pos, V1, _, V2))
           Not_resolved(Pos, "val_infix")
         ||
           where(V -> stmt_infix(Pos, V1, Comb, V2))
           (|
             where(Comb -> ext_choice)
             Not_support(pos(Pos), "external choice")
           ||
             where(Comb -> int_choice)
             Extract_types_in_value_expr(V1)
             Extract_types_in_value_expr(V2)
--             Not_support(pos(Pos), "internal choice")
           ||
             where(Comb -> parallel)
             Not_support(pos(Pos), "parallel")
           ||
             where(Comb -> interlock)
             Not_support(pos(Pos), "interlock")
           ||
             where(Comb -> sequence)
             Extract_types_in_value_expr(V1)
             Extract_types_in_value_expr(V2)
           |)
         ||
           where(V -> always(_, V1))
         ||
           where(V -> ax_prefix(_, _, V1))
           Extract_types_in_value_expr(V1)
           Alias_type_of_value_expr(V)
         ||
           where(V -> val_prefix(Pos, _, V1))
           Not_resolved(Pos, "val_prefix")
         ||
           where(V -> comprehended(Pos, _, _, _))
           Not_support(pos(Pos), "comprehended expression")
         ||
           where(V -> initialise(Pos, _))
           Not_support(pos(Pos), "initialise")
         ||
           where(V -> assignment(Pos, _, V1))
           Not_resolved(Pos, "assignment")
         ||
           where(V -> input(Pos, _))
           Not_support(pos(Pos), "input")
         ||
           where(V -> output(Pos, _, _))
           Not_support(pos(Pos), "output")
         ||
           where(V -> local_expr(Pos, DL, V1))
           Not_resolved(Pos, "local expression")
         ||
           where(V -> let_expr(_, LDL, V1))
           Extract_types_in_let_defs(LDL)
           Extract_types_in_value_expr(V1)
         ||
           where(V -> if_expr(_, V1, V2, _, ELIFL, EL))
           Extract_types_in_value_expr(V1)
           Extract_types_in_value_expr(V2)
           Extract_types_in_elif_branches(ELIFL)
           Extract_types_in_else_branch(EL)
         ||
           where(V -> case_expr(_, V1, _, CBL))
           Extract_types_in_value_expr(V1)
           Extract_types_in_case_branches(CBL)
         ||
           where(V -> while_expr(_, V1, V2))
           Extract_types_in_value_expr(V1)
           Extract_types_in_value_expr(V2)
         ||
           where(V -> until_expr(_, V1, V2))
           Extract_types_in_value_expr(V1)
           Extract_types_in_value_expr(V2)
         ||
           where(V -> for_expr(_, LLim, V1))
           Extract_types_in_list_limit(LLim)
           Extract_types_in_value_expr(V1)
         ||
           where(V -> class_scope_expr(Pos, _, _))
           Not_support(pos(Pos), "class scope")
         ||
           where(V -> env_class_scope(Pos, _, _, _))
           Not_support(pos(Pos), "class scope")
         ||
           where(V -> implementation_relation(Pos, _, _))
           Not_support(pos(Pos), "implementation relation")
         ||
           where(V -> implementation_expr(Pos, _, _))
           Not_support(pos(Pos), "implementation expression")
         ||
           where(V -> val_occ(_, VI, _))
           Extract_types_in_value_id(VI)
         ||
           where(V -> var_occ(_, VarI, _))
           Extract_types_in_variable_id(VarI)
         ||
           where(V -> pre_occ(_, VarI, _))
         ||
           where(V -> infix_occ(_, V1, VI, _, V2))
           Alias_type_of_value_expr(V)
           Extract_types_in_value_expr(V1)
           Extract_types_in_value_expr(V2)
         ||
           where(V -> prefix_occ(_, VI, _, V1))
           Alias_type_of_value_expr(V)
           Extract_types_in_value_expr(V1)
         ||
           where(V -> ass_occ(_, VarI, _, V1))
           Alias_type_of_value_expr(V)
           Extract_types_in_variable_id(VarI)
           Extract_types_in_value_expr(V1)
         ||
           where(V -> input_occ(Pos, _, _))
           Not_support(pos(Pos), "input_occ")
         ||
           where(V -> output_occ(Pos, _, _, _))
           Not_support(pos(Pos), "output_occ")     
         ||
           where(V -> env_local(_, DL, CE, V1))
           Extract_types_in_env_local(DL, CE, V1)
         ||
           where(V -> no_val)
         ||
           where(V -> cc_expr(PosO, _, _, _))
         |) 
                   
---------------------------------------------------

'action' Openenv_and_define_formal_function_application(POS, TYPING, FORMAL_FUNCTION_APPLICATION)

  'rule' Openenv_and_define_formal_function_application(Pos, TG, FFA):
         Defined_type_of_typing(TG -> T)
         Openenv
         where(FFA -> form_appl(_, Id_or_op, ParamL))
         Result_type(Pos, T, ParamL -> _)

'condition' Get_first_single_from_binding(BINDING -> BINDING)

  'rule' Get_first_single_from_binding(B0 -> B):
         (|
           where(B0 -> single(_, _))
           where(B0 -> B)
         ||
           where(B0 -> product(P, list(B1, BL)))  
           (|
             Get_first_single_from_binding(B1 -> B)
           ||
             Get_first_single_from_binding(product(P, BL) -> B)
           |)
         |)

'action' Get_resolved_exp_val_def(TYPING -> TYPE_EXPR, VALUE_EXPR, OPT_CONDITION)

  'rule' Get_resolved_exp_val_def(TG -> T, V, Cond):
         Get_current_top_values(-> VE)
         where(TG -> single(_, B, T0))
         Get_first_single_from_binding(B -> single(Pos, _))
         Select_id_by_pos(Pos, VE -> value_id(I))
         I'Def -> DF
         where(DF -> expl_val(V1, Cond))
         (|
           where(B -> product(_, _))
           where(V1 -> let_expr(_, list(explicit(_, _, V2), nil), _))
	   Resolve_type(T0 -> T)
         ||
	   I'Type -> T
           where(V1 -> V2)
         |)
	 -- can ignore any disambiguation
	 (|
	   where(V2 -> disamb(_, V, _))
	 ||
	   where(V2 -> V)
	 |)

'action' Extract_types_in_resolved_exp_val_def(TYPING)

  'rule' Extract_types_in_resolved_exp_val_def(TG):
         Get_resolved_exp_val_def(TG -> T, V, Cond)
         Alias_type_0(T)
         Extract_types_in_value_expr(V)
	 Extract_types_in_opt_cond(Cond)

'action' Get_resolved_exp_fun_def(TYPING -> TYPE_EXPR, VALUE_DEFINITION)

  'rule' Get_resolved_exp_fun_def(TG -> T, DF):
         Get_current_top_values(-> VE)
         where(TG -> single(_, B, _))
         Get_first_single_from_binding(B -> single(Pos, _))
         Select_id_by_pos(Pos, VE -> value_id(I))
         I'Type -> T
         I'Def -> DF

'action' Extract_types_in_resolved_exp_fun_def(TYPING)

  'rule' Extract_types_in_resolved_exp_fun_def(TG):
         Get_resolved_exp_fun_def(TG -> T, expl_fun(ParamL, V, Post, Pre, Cond, PCond))
	 -- Do we need types of defined functions?
         -- Alias_type(T)
	 Alias_fun_type(T)
         Extract_types_in_value_expr(V)
	 Extract_types_in_opt_post(Post)
         Extract_types_in_pre_cond(Pre)
         Extract_types_in_opt_cond(Cond)
         Extract_types_in_opt_cond(PCond)

'action' Alias_fun_type(TYPE_EXPR)

  'rule' Alias_fun_type(T):
	 (|
	   Type_is_fun(T -> PT, _, RT)
	   Alias_type_0(PT)
	   Alias_fun_type(RT) -- may be curried
	 ||
	   Alias_type_0(T)
	 |)

'action' Extract_types_in_value_defs(VALUE_DEFS)

  'rule' Extract_types_in_value_defs(VDL):
         (|
           where(VDL -> list(VD, Tail))
           (|
             where(VD -> typing(_, _))
           ||
             where(VD -> exp_val(_, TG, _))
             Extract_types_in_resolved_exp_val_def(TG)
           ||
             where(VD -> imp_val(_, TG, R))
           ||
             where(VD -> exp_fun(_, TG, _, _, _, _, _))
             Extract_types_in_resolved_exp_fun_def(TG)
           ||
             where(VD -> imp_fun(_, _, _, _, _))
           |)
           Extract_types_in_value_defs(Tail)
         ||
           where(VDL -> nil)
         |)

---------------------------------------------------

'action' Extract_types_in_initialisation(INITIALISATION, OPT_CONDITION)

  'rule' Extract_types_in_initialisation(Ini, Cond):
         (|
           where(Ini -> initial(V))
           Extract_types_in_value_expr(V)
	   Extract_types_in_opt_cond(Cond)
         ||
           where(Ini -> nil)
         |)

'action' Extract_types_in_variable_def_ids(IDENTS)

  'rule' Extract_types_in_variable_def_ids(Ids):
         (|
           where(Ids -> list(Id, Tail))
           Get_current_variables(-> VARS)
           Lookup_env_variable_id(Id, nil, VARS -> variable_id(VarI))
           VarI'Type -> T
           Alias_type(T)
           VarI'Init -> Ini
	   VarI'Subtype -> Cond
           Extract_types_in_initialisation(Ini, Cond)
           Extract_types_in_variable_def_ids(Tail)
         ||
           where(Ids -> nil)
         |)

'action' Extract_types_in_variable_defs(VARIABLE_DEFS)

  'rule' Extract_types_in_variable_defs(VarDL):
         (|
           where(VarDL -> list(VarD, Tail))
           (|
             where(VarD -> single(_, Id, _, _))
             Extract_types_in_variable_def_ids(list(Id, nil))
           ||
             where(VarD -> multiple(_, Ids, _))
             Extract_types_in_variable_def_ids(Ids)
           |)
           Extract_types_in_variable_defs(Tail)
         ||
           where(VarDL -> nil)
         |)

---------------------------------------------------

'action' Extract_types_in_channel_defs(POS, CHANNEL_DEFS)

  'rule' Extract_types_in_channel_defs(Pos, ChDL):
         Not_support(pos(Pos), "channel defs")

---------------------------------------------------

'action' Extract_types_in_object_defs(OBJECT_DEFS)

  'rule' Extract_types_in_object_defs(ODL):
         (|
           where(ODL -> list(odef(Pos, Id, PS, CL), Tail))
           (|
             where(PS -> nil)
             Get_current_modules(-> ME)
             Lookup_object_in_module(Id, ME -> object_id(I))
             Current -> C
             I'Param_env -> PCE
             I'Env -> CE
             Current <- current_env(CE, current_env(PCE, C))
             Extend_paths -> Paths
             Extend_paths <- list(nil, list(nil, Paths))
             Extract_types_in_class(CL)
             Current -> current_env(CE1, current_env(PCE1, C1))
             Current <- C1
             Extend_paths <- Paths
           ||
             Not_support(pos(Pos), "object array")
           |)
           Extract_types_in_object_defs(Tail)
         ||
           where(ODL -> nil)
         |)

---------------------------------------------------

'action' Extract_types_in_axiom_defs(POS, AXIOM_DEFS)

  'rule' Extract_types_in_axiom_defs(Pos, ADL):
         Not_support(pos(Pos), "axiom defs")

---------------------------------------------------

'action' Extract_types_in_test_case_defs(TEST_CASE_DEFS)

  'rule' Extract_types_in_test_case_defs(TCL):
         (|
           where(TCL -> list(test_case_def(P, N, E), Tail))
           Get_current_test_cases(all -> TCS)
           Lookup_test_case(P, TCS -> I)
           I'Test_case -> V
           Extract_types_in_value_expr(V)
           Extract_types_in_test_case_defs(Tail)
         ||
           where(TCL -> nil)
         |)
         

---------------------------------------------------

--'action' Extract_user_type_defs_from_decls(DECLS, Type_ids -> Type_ids)

--  'rule' Extract_user_type_defs_from_decls(DL, UTDL0 -> UTDL):
--         (|
--           where(DL -> list(type_decl(Pos, TDL), Tail))
--           Extract_user_type_defs_from_type_defs(TDL, UTDL0 -> UTDL1)
--           Extract_user_type_defs_from_decls(Tail, UTDL1 -> UTDL)
--         ||
--          where(UTDL0 -> UTDL)
--         |)

--  'rule' Extract_user_type_defs_from_decls(DL, UTDL0 -> UTDL):
--         (|
--           where(DL -> list(D, Tail))
--	   (|
--	     where(D -> type_decl(Pos, TDL))
--	     Extract_user_type_defs_from_type_defs(TDL, UTDL0 -> UTDL1)
--	   ||
--	     where(UTDL0 -> UTDL1)
--	   |)
--           Extract_user_type_defs_from_decls(Tail, UTDL1 -> UTDL)
--         ||
--           where(UTDL0 -> UTDL)
--         |)
--
--'action' Extract_user_type_defs_from_type_defs(TYPE_DEFS, Type_ids -> Type_ids)
--
--  'rule' Extract_user_type_defs_from_type_defs(TDL, UTDL0 -> UTDL):
--         (|
--           where(TDL -> list(TD, Tail))
--           (|
--             (|
--               where(TD -> sort(Pos, Id))
--               Not_support(pos(Pos), "abstract type")
--             ||
--               where(TD -> variant(Pos, Id, _))
--             ||
--               where(TD -> record(Pos, Id, _))
--             ||
--               where(TD -> union(Pos, Id, _))
--               Not_support(pos(Pos), "union type")
--             |)
--             Lookup_type_id(Pos, Id -> type_id(I))
--             Extract_user_type_defs_from_type_defs(Tail, list(I, UTDL0) -> UTDL)
--           ||
--             Extract_user_type_defs_from_type_defs(Tail, UTDL0 -> UTDL)
--           |)        
--         ||
--           where(TDL -> nil)
--           where(UTDL0 -> UTDL)
--         |)
--
--'action' Merge_user_type_defs(Type_ids, Type_ids -> Type_ids)
--
--  'rule' Merge_user_type_defs(UTDL1, UTDL2 -> UTDL):
--         (|
--           where(UTDL1 -> list(UTD, Tail))
--           Merge_user_type_defs(Tail, list(UTD, UTDL2) -> UTDL)
--         ||
--           where(UTDL1 -> nil)
--           where(UTDL2 -> UTDL)
--         |)
--
--'condition' Take_user_type_def_from_list(Type_id, Type_ids, Type_ids -> Type_id, Type_ids)
--
--  'rule' Take_user_type_def_from_list(I, UTDL, UTDL0 -> UTD1, UTDL1):
--         where(UTDL -> list(I1, Tail))
--         (|
--           eq(I, I1)
--           where(I -> UTD1)
--           Merge_user_type_defs(Tail, UTDL0 -> UTDL1)
--         ||
--           Take_user_type_def_from_list(I, Tail, list(I1, UTDL0) -> UTD1, UTDL1)
--         |)
--
--'action' Extract_types_in_user_type_def(Type_id, Type_ids -> Type_ids)
--
--  'rule' Extract_types_in_user_type_def(I, UTDL -> UTDL1):
--	 I'Type -> TY
--         (|
--           where(TY -> sort(abstract)) || 
--           where(UTDL -> UTDL1)
--         ||
--           where(TY -> sort(variant(VL)))
--           Extract_types_in_variants(I, VL, UTDL -> UTDL1)
--         ||
--           where(TY -> sort(record(CoL)))
--           Extract_types_in_components(I, CoL, UTDL -> UTDL1)
--         |)
--         Alias_type_0(defined(I, nil))

'action' Extract_types_in_variants(VARIANTS)

  'rule' Extract_types_in_variants(VL):
         (|
           where(VL -> list(V, Tail))
           where(V -> record(_, _, CoL))
           Extract_types_in_components(CoL)
           Extract_types_in_variants(Tail)
         ||
           where(VL -> nil)
         |)

'action' Extract_types_in_components(COMPONENTS)
  
  'rule' Extract_types_in_components(CoL):
         Components_to_type_option(CoL -> TO)
         (|
           where(TO -> some(T))
           Alias_type_0(T)
         ||
           where(TO -> none)
         |)

--'action' Alias_type_in_named(Type_id, TYPE_EXPR, Type_ids -> Type_ids, INT)
--
--  'rule' Alias_type_in_named(I, T, UTDL -> UTDL1, N):
--         (|
--           where(T -> defined(I1, Q))
--           (|
--             eq(I, I1)
--             where(UTDL -> UTDL1)
--             where(0 -> N)
--           ||
--             I1'Type -> abbrev(T1)
--             Alias_type_in_named(I, T1, UTDL -> UTDL1, N)
--           ||
--             Take_user_type_def_from_list(I1, UTDL, nil -> UTD, UTDL2)
--             Extract_types_in_user_type_def(UTD, UTDL2 -> UTDL1)
--             Alias_type_0(T)
--             where(1 -> N)
--           |)
--         ||
--           where(T -> product(XT))
--           Alias_product_in_named(I, XT, UTDL -> UTDL1, N)
--           [|
--             eq(N, 1)
--             Alias_type_0(T)
--           |]
--         ||
--           (| Type_is_set(T -> ET) || Type_is_list(T -> ET) |)
--           Alias_type_in_named(I, ET, UTDL -> UTDL1, N)
--           [|
--             eq(N, 1)
--             Alias_type_0(T)
--           |]
--         ||
--           Type_is_map(T -> DT, RT)
--           Alias_type_in_named(I, DT, UTDL -> UTDL2, N1)
--           Alias_type_in_named(I, RT, UTDL2-> UTDL1, N2)
--           (| 
--             eq(N1, 1)
--             eq(N2, 1)
--             Alias_type_0(T)
--             where(1 -> N)
--           ||
--             where(0 -> N)
--           |)
--         ||
--           Type_is_fun(T -> PT, _, RT)
--           Alias_type_in_named(I, PT, UTDL -> UTDL2, N1)
--           Alias_type_in_named(I, RT, UTDL2-> UTDL1, N2)
--           (| 
--             eq(N1, 0)
--             eq(N2, 0)
--             Alias_type_0(T)
--             where(1 -> N)
--           ||
--             where(0 -> N)
--           |)
--         ||
--           Alias_type_0(T)
--           where(UTDL -> UTDL1)
--           where(1 -> N)
--         |)
-- 
--'action' Alias_product_in_named(Type_id, PRODUCT_TYPE, Type_ids -> Type_ids, INT)
--
--  'rule' Alias_product_in_named(I, XT, UTDL -> UTDL1, N):
--         (|
--           where(XT -> list(T, Tail))
--           Alias_type_in_named(I, T, UTDL -> UTDL2, N1)
--           Alias_product_in_named(I, Tail, UTDL2 -> UTDL1, N2)
--           (|
--             eq(N1, 1)
--             eq(N2, 1)
--             where(1 -> N)
--           ||
--             where(0 -> N)
--           |)
--         ||
--           where(XT -> nil)
--           where(UTDL -> UTDL1)
--           where(1 -> N)
--         |)
--
--'action' Extract_types_in_user_type_defs(Type_ids)
--
--  'rule' Extract_types_in_user_type_defs(UTDL):
--         (|
--           where(UTDL -> list(UTD, Tail))
--           Extract_types_in_user_type_def(UTD, Tail -> UTDL1)
--           Extract_types_in_user_type_defs(UTDL1)
--         ||
--           where(UTDL -> nil)
--         |)

'action' Extract_types_in_type_defs(TYPE_DEFS)

  'rule' Extract_types_in_type_defs(TDL):
         (|
           where(TDL -> list(TD, Tail))
           (|
             where(TD -> sort(Pos, Id))
             Not_support(pos(Pos), "abstract type")
           ||
             where(TD -> abbrev(Pos, Id, _))
	     Lookup_type_id(Pos, Id -> type_id(I))
	     I'Def -> abbreviation(T)
             Alias_type_0(T)
	     [|
	       I'Subtype -> funct(I1)
	       I1'Def -> expl_fun(_, V, nil, nil, Cond, PCond)
	       Extract_types_in_value_expr(V)
	       Extract_types_in_opt_cond(Cond)
	       Extract_types_in_opt_cond(PCond)
	     |]
           ||
             where(TD -> variant(Pos, Id, _))
	     Lookup_type_id(Pos, Id -> type_id(I))
	     I'Type -> sort(variant(VL))
	     Extract_types_in_variants(VL)
	     Alias_type_0(defined(I, nil))
           ||
             where(TD -> record(Pos, Id, _))
	     Lookup_type_id(Pos, Id -> type_id(I))
	     I'Type -> sort(record(CoL))
	     Extract_types_in_components(CoL)
	     Alias_type_0(defined(I, nil))
           ||
             where(TD -> union(Pos, Id, _))
             Not_support(pos(Pos), "union type")
           |)
           Extract_types_in_type_defs(Tail)
         ||
           where(TDL -> nil)
         |)

---------------------------------------------------

'action' Components_to_product_type(COMPONENTS -> PRODUCT_TYPE)

  'rule' Components_to_product_type(CoL -> XT):
         (|
           where(CoL -> list(Co, Tail))
           where(Co -> component(_, _, T, _))
           Components_to_product_type(Tail -> XT1)
           where(PRODUCT_TYPE'list(T, XT1) -> XT)
         ||
           where(CoL -> nil)
           where(PRODUCT_TYPE'nil -> XT)
         |)

'action' Components_to_type_option(COMPONENTS -> TYPE_OPTION)

  'rule' Components_to_type_option(CoL -> TO):
         Components_to_product_type(CoL -> XT)
         (|
           where(XT -> nil)
           where(TYPE_OPTION'none -> TO)
         ||
           where(XT -> list(T, nil))
           where(some(T) -> TO)
         ||
           where(some(product(XT)) -> TO)
         |)

---------------------------------------------------

'action' Define_types_in_aliases(todo:TYPE_ALIASES, waiting:TYPE_ALIASES, FOUND)

  'rule' Define_types_in_aliases(TaL, WL, F):
         (|
           where(TaL -> list(Ta, Tail))
           where(Ta -> alias(S, T))
           (|
             where(T -> unit)
             Assign_struct(S, "RT_Unit")
             Add_defined_alias(Ta)
             Define_types_in_aliases(Tail, WL, found)
           ||
             where(T -> bool)
             Assign_struct(S, "RT_Bool")
             Add_defined_alias(Ta)
             Define_types_in_aliases(Tail, WL, found)
           ||
             where(T -> int)
             Assign_struct(S, "RT_Int")
             Add_defined_alias(Ta)
             Define_types_in_aliases(Tail, WL, found)
           ||
             where(T -> nat)
             Assign_struct(S, "RT_Nat")
             Add_defined_alias(Ta)
             Define_types_in_aliases(Tail, WL, found)
           ||
             where(T -> real)
             Assign_struct(S, "RT_Real")
             Add_defined_alias(Ta)
             Define_types_in_aliases(Tail, WL, found)
           ||
             Type_matches_text(T)
             Assign_struct(S, "RT_Text")
             Add_defined_alias(Ta)
             Define_types_in_aliases(Tail, WL, found)
           ||
             where(T -> char)
             Assign_struct(S, "RT_Char")
             Add_defined_alias(Ta)
             Define_types_in_aliases(Tail, WL, found)
           ||
             where(T -> defined(I, Q))
	     (|
	       I'Type -> TY
               Add_defined_alias(Ta) -- do first to allow for
				     -- recursion in variants
	       All_user_type_defined(TY)
               Define_user_type(S, I)
               Define_types_in_aliases(Tail, WL, found)
	     ||
	       Remove_last_defined_alias -- undo premature addition
-- debug
-- Postponed_count -> N
-- Postponed_count <- N+1
	       Define_types_in_aliases(Tail, list(Ta, WL), F)
	     |)
           ||   
             where(T -> product(XT))
	     (|
	       All_product_defined(XT)
               Emit_product_type_structdef(S, XT)
               Add_defined_alias(Ta)
               Define_types_in_aliases(Tail, WL, found)
	     ||
-- debug
-- Postponed_count -> N
-- Postponed_count <- N+1
	       Define_types_in_aliases(Tail, list(Ta, WL), F)
	     |)
           ||
             Type_is_set(T -> ET)
	     (|
	       Lookup_defined_alias(ET -> _)
               Emit_set_structdef(S, ET)
               Add_defined_alias(Ta)
               Define_types_in_aliases(Tail, WL, found)
	     ||
-- debug
-- Postponed_count -> N
-- Postponed_count <- N+1
	       Define_types_in_aliases(Tail, list(Ta, WL), F)
	     |)
           ||
             Type_is_list(T -> ET)
	     (|
	       Lookup_defined_alias(ET -> _)
               Emit_list_structdef(S, ET)
               Add_defined_alias(Ta)
               Define_types_in_aliases(Tail, WL, found)
	     ||
-- debug
-- Postponed_count -> N
-- Postponed_count <- N+1
	       Define_types_in_aliases(Tail, list(Ta, WL), F)
	     |)
           ||
             Type_is_map(T -> DT, RT)
	     (|
	       Lookup_defined_alias(DT -> _)
	       Lookup_defined_alias(RT -> _)
               Emit_map_structdef(S, DT, RT)
               Add_defined_alias(Ta)
               Define_types_in_aliases(Tail, WL, found)
	     ||
-- debug
-- Postponed_count -> N
-- Postponed_count <- N+1
	       Define_types_in_aliases(Tail, list(Ta, WL), F)
	     |)
           ||
             Type_is_fun(T -> PT, A, RT)
	     (|
	       Lookup_defined_alias(PT -> _)
	       Lookup_defined_alias(RT -> _)
               Emit_fun_structdef(S, PT, A, RT)
               Add_defined_alias(Ta)
               Define_types_in_aliases(Tail, WL, found)
	     ||
-- debug
-- Postponed_count -> N
-- Postponed_count <- N+1
	       Define_types_in_aliases(Tail, list(Ta, WL), F)
	     |)
           ||
             print(Ta)
             Internal_error(no_pos, "Define_types_in_aliases")
           |)
         ||
           where(TaL -> nil)
-- debug
-- Putmsg("Defined: ")
-- Done_count -> Done
-- print(Done)
-- Putmsg("Postponed: ")
-- Postponed_count -> Postponed
-- print(Postponed)
-- Done_count <- 0
-- Postponed_count <- 0
	   (|
	     where(WL -> nil)
	   ||
	     where(F -> found)
	     -- better to reverse waiting list to get original order
	     Rev_type_aliases(WL, nil -> WL1)
	     Define_types_in_aliases(WL1, nil, nil)
	   ||
	     where(WL -> list(alias(_,WT),_))
	     [| -- try for a position
	       Named_type_expr(WT -> defined(I1, _))
	       I1'Pos -> Pos
	       Puterror(Pos)
	     |]
	     Putmsg("Type ")
	     Print_type(WT)
	     Putmsg(" seems to be involved in mutual recursion with another record or variant.\n")
	     Not_support(no_pos, "Mutual recursion between records or variants")     
	   |)
         |)

'condition' All_product_defined(PRODUCT_TYPE)

  'rule' All_product_defined(nil):

  'rule' All_product_defined(list(T, Tail)):
	 Type_defined(T)
	 All_product_defined(Tail)

'condition' All_user_type_defined(TYPE)

  'rule' All_user_type_defined(sort(record(CoL))):
	 All_components_defined(CoL)

  'rule' All_user_type_defined(sort(variant(VL))):
	 All_variants_defined(VL)

'condition' All_variants_defined(VARIANTS)

  'rule' All_variants_defined(nil):

  'rule' All_variants_defined(list(record(_,_,CoL), VL)):
	 All_components_defined(CoL)
	 All_variants_defined(VL)

'condition' All_components_defined(COMPONENTS)

  'rule' All_components_defined(nil):

  'rule' All_components_defined(list(component(_,_,T,_), CoL)):
	 Type_defined(T)
	 All_components_defined(CoL)

'condition' Type_defined(TYPE_EXPR)

  'rule' Type_defined(T):
         (|
           Lookup_defined_alias(T -> _)
         ||
           where(T -> defined(I, Q))
           Named_type_is_abbrev(I -> T1)
           Type_defined(T1)
         ||
           where(T -> bracket(T1))
           Type_defined(T1)
         ||
           where(T -> subtype(single(_,_,T1), _))
           Type_defined(T1)
	 ||
	   Type_is_product(T -> XT)
	   All_product_defined(XT)
	 ||
	   Type_is_set(T -> ET)
	   Type_defined(ET)
	 ||
	   Type_is_list(T -> ET)
	   Type_defined(ET)
	 ||
	   Type_is_map(T -> DT, RT)
	   Type_defined(DT)
	   Type_defined(RT)
	 ||
	   Type_is_fun(T -> PT, _, RT)
	   Type_defined(PT)
	   Type_defined(RT)
         |)

-- debug 	 
-- 'var' Done_count : INT

-- 'var' Postponed_count : INT

'action' Define_types

  'rule' Define_types:
         Var_aliased_types -> TaL
-- debug
-- Print_type_aliases
-- Putmsg("Defining aliases\n")
-- Done_count <- 0
-- Postponed_count <- 0
	 -- more hits on first pass of Define_types_in_aliases
	 -- if list is first reversed
	 Rev_type_aliases(TaL, nil -> TaL1)
         Define_types_in_aliases(TaL1, nil, nil)

'action' Rev_type_aliases(TYPE_ALIASES, TYPE_ALIASES -> TYPE_ALIASES)

  'rule' Rev_type_aliases(TaLin, TaLacc -> TaLout):
         (|
           where(TaLin -> list(T, Tail))
           Rev_type_aliases(Tail, list(T, TaLacc) -> TaLout)
         ||
           where(TaLin -> nil)
           where(TaLacc -> TaLout)
         |)



---------------------------------------------------

'action' Emit_set_structdef(STRING, TYPE_EXPR)

  'rule' Emit_set_structdef(S, ET):
         Get_defined_alias(ET -> ES)
         WriteF2File("structure %s = RT_Set(structure Elem = %s);\n\n", S, ES)               

---------------------------------------------------

'action' Emit_list_structdef(STRING, TYPE_EXPR)

  'rule' Emit_list_structdef(S, ET):
         Get_defined_alias(ET -> ES)
         WriteF2File("structure %s = RT_List(structure Elem = %s);\n\n", S, ES)              

---------------------------------------------------

'action' Emit_map_structdef(STRING, TYPE_EXPR, TYPE_EXPR)

  'rule' Emit_map_structdef(S, DT, RT):
         Get_defined_alias(DT -> DS)
         Get_defined_alias(RT -> RS)
         WriteF3File("structure %s = RT_Map(structure DomainElem = %s structure RangeElem = %s);\n\n", S, DS, RS)  

---------------------------------------------------

'action' Emit_fun_structdef(STRING, TYPE_EXPR, FUNCTION_ARROW, TYPE_EXPR)

  'rule' Emit_fun_structdef(S, PT, A, RT):
         Get_defined_alias(PT -> PS)
         Get_defined_alias(RT -> RS)
         (|
           where(A -> partial)
           where("\"-~->\"" -> AS)
         ||
           where(A -> total)
           where("\"->\"" -> AS)
         |)
         WriteF4File("structure %s = RT_Fun(structure Param = %s val arrow = %s structure Result = %s);\n\n", S, PS, AS, RS)

---------------------------------------------------

'action' Emit_toStringSafe_def

  'rule' Emit_toStringSafe_def:
         WriteFile("fun toStringSafe x = toString(x())")
         WritelnFile(1)
         WriteFile("  handle RSL.RSL_exception s => (RSL.inc_exception_count(); s);")
         WritelnFile(2)
         
---------------------------------------------------

'action' Emit_defined_type_alias(TYPE_EXPR)
  
  'rule' Emit_defined_type_alias(T):
         Get_defined_alias(T -> S)
         WriteFFile("%s.t", S)

'action' Emit_product_type_expr(PRODUCT_TYPE)

  'rule' Emit_product_type_expr(XT):
         (|
           where(XT -> list(T, Tail))
           Emit_defined_type_alias(T)
           [|
             where(Tail -> list(_, _))
             WriteFile(" * ")
           |]
           Emit_product_type_expr(Tail)
         ||
           where(XT -> nil)
         |)

'action' Emit_product_default_value(INT, PRODUCT_TYPE)

  'rule' Emit_product_default_value(N, XT):
         [|
           eq(N, 0)
           LParen
         |]
         (|
           where(XT -> list(T, Tail))
           Get_defined_alias(T -> S)
           WriteFFile("%s.defval", S)
           [|
             where(Tail -> list(_, _))
             WriteFile(", ")
           |]
           Emit_product_default_value(1, Tail)
         ||
           where(XT -> nil)
           RParen
         |)

'action' Emit_product_equexpr(PRODUCT_TYPE, STRING, STRING, INT)

  'rule' Emit_product_equexpr(XT, Sx, Sy, N)
         (|
           where(XT -> list(T, Tail))
           Get_defined_alias(T -> S)
           WriteFFile("%s.equ(", S)
           WriteFFileInt("#%d", N)
           WriteFFile(" %s, ", Sx)
           WriteFFileInt("#%d", N)
           WriteFFile(" %s)", Sy)
           [|
             where(Tail -> list(_, _))
             WriteFile(" andalso ")
             WritelnFile(1)
           |]
           Emit_product_equexpr(Tail, Sx, Sy, N+1)
         ||
           where(XT -> nil)
         |)

'action' Emit_product_value_to_string(PRODUCT_TYPE, STRING, INT)

  'rule' Emit_product_value_to_string(XT, VS, N):
         (|
           where(XT -> list(T, Tail))
           LParen
           Get_defined_alias(T -> S)
           WriteFFile("%s.toString", S)
           WriteFFileInt("(#%d", N)
           WriteFFile(" %s ", VS)
           WriteFile("))")
           [|
             where(Tail -> list(_, _))
             WriteFile(" ^ \",\"")
           |]
           WriteFile(" ^")
           WritelnFile(1)
           Emit_product_value_to_string(Tail, VS, N+1)
         ||
           where(XT -> nil)
         |)

'action' Emit_product_type_to_string(PRODUCT_TYPE)

  'rule' Emit_product_type_to_string(XT):
         (|
           where(XT -> list(T, Tail))
           LParen
           Get_defined_alias(T -> S)
           WriteFFile("%s.typeToString ())", S)
           [|
             where(Tail -> list(_, _))
             WriteFile(" ^ \" >< \"")
           |]
           WriteFile(" ^")
           WritelnFile(1)
           Emit_product_type_to_string(Tail)
         ||
           where(XT -> nil)
         |)

'action' Emit_product_type_structdef(STRING, PRODUCT_TYPE)
  
  'rule' Emit_product_type_structdef(S, XT):
         Open_structdef(S)
         ---- type t
         WriteFile("type t = ")
         Emit_product_type_expr(XT)
         WriteFile(";")
         WritelnFile(2)
         ---- defval
--       WriteFile("val defval = ")
--       Emit_product_default_value(0, XT)
--       WriteFile(";")
--       WritelnFile(2)
         ---- equ
         WriteFile("fun equ (x:t, y:t) = ")
         PushSetIndentHere(0)
         Emit_product_equexpr(XT, "x", "y", 1)
         WriteFile(";")
         PopIndent
         WritelnFile(2)
         ---- toString
         WriteFile("fun toString (x:t) = ")
         PushSetIndentHere(0)
         WriteFile("\"(\" ^")
         WritelnFile(1)
         Emit_product_value_to_string(XT, "x", 1)
         WriteFile("\")\";")
         PopIndent
         WritelnFile(2)
         Emit_toStringSafe_def
         ---- typeToString
         WriteFile("fun typeToString () = ")
         PushSetIndentHere(0)
         WriteFile("\"(\" ^")
         WritelnFile(1)
         Emit_product_type_to_string(XT)
         WriteFile("\")\";")
         PopIndent
         WritelnFile(1)
         -- close strcut
         Close_structdef

---------------------------------------------------

'action' Assign_struct(STRING, STRING)

  'rule' Assign_struct(S1, S2):
         WriteF2File("structure %s = %s", S1, S2)
         WriteFile(";")
         WritelnFile(2)

'action' Open_structdef(STRING)

  'rule' Open_structdef(SS):
         WriteFFile("structure %s =", SS)
         WritelnFile(1)
         IndentFile
         WriteFile("struct")
         WritelnFile(1)
         IndentFile

'action' Close_structdef

  'rule' Close_structdef
         UnindentFile
         WriteFile("end;")
         WritelnFile(2)
         UnindentFile

'action' Close_user_structdef(STRING, IDENT)

  'rule' Close_user_structdef(S, Id)
         UnindentFile
         WriteFile("end;")
         WritelnFile(2)
         UnindentFile

'action' Open_withs(STRING, IDENT, OBJECT_EXPRS)

  'rule' Open_withs(S, Id, list(Obj, Objs)):
         (|
           where(Obj -> obj_name(name(_, id_op(Id1))))
           eq(Id, Id1)
           WriteFFile("open %s;", S)
           WritelnFile(1)
         ||
           where(Obj -> obj_name(qual_name(P, Obj1, Id1)))
           Split_name(qual_name(P, Obj1, Id1) -> obj_name(name(_, id_op(Id2))), N2)
           eq(Id, Id2)
           Object_to_string(obj_name(N2) -> S2)
           WriteF2File("open %s.%s;", S, S2)
           WritelnFile(1)
         ||
           -- ignore
         |)
         Open_withs(S, Id, Objs)

  'rule' Open_withs(_, _, nil):

---------------------------------------------------

'action' Open_globals(OBJECT_EXPRS)

  'rule' Open_globals(Objs)
         Get_global_object_ids(-> Ids)
         Open_globals1(Ids, Objs)

'action' Open_globals1(IDENTS, OBJECT_EXPRS)

  'rule' Open_globals1(list(Id, Ids), Objs):
         id_to_string(Id -> S)
         Open_withs(S, Id, Objs)
         Open_globals1(Ids, Objs)

  'rule' Open_globals1(nil, _):

'action' Get_global_object_ids(-> IDENTS)

  'rule' Get_global_object_ids(-> Ids):
         Globals -> G
         Get_global_object_ids1(G, nil -> Ids)

'action' Get_global_object_ids1(MODULE_ENV, IDENTS -> IDENTS)

  'rule' Get_global_object_ids1(object_env(I, ME), Ids -> list(Id, Ids1)):
         I'Ident -> Id
         Get_global_object_ids1(ME, Ids -> Ids1)

  'rule' Get_global_object_ids1(scheme_env(_, ME), Ids -> Ids1):
         Get_global_object_ids1(ME, Ids -> Ids1)

  'rule' Get_global_object_ids1(theory_env(_, ME), Ids-> Ids1):
         Get_global_object_ids1(ME, Ids -> Ids1)

  'rule' Get_global_object_ids1(nil, Ids -> Ids): 
         
---------------------------------------------------

--'action' Emit_sort_structdef(STRING, IDENT)

--  'rule' Emit_sort_structdef(S, Id):
--         Open_structdef(S)
--         Id_to_SML_id(Id, nil -> TS)
--         WriteFFile("datatype t = %s;", TS)
--         WritelnFile(2)
----       WriteFFile("val defval = %s;", TS)
----       WritelnFile(2)
--         WriteFile("fun equ (_: t, _: t) = true;")
--         WritelnFile(2)
--         WriteFFile("fun toString (_: t) = \"-:%s\";", TS)
--         WritelnFile(2)
--         Emit_toStringSafe_def
--         id_to_string(Id -> TS1)
--         Emit_sort_typestrfundef(TS1)
--         Close_structdef

'action' Emit_sort_typestrfundef(STRING)

  'rule' Emit_sort_typestrfundef(TS):
         WriteFFile("fun typeToString () = \"%s\";", TS)
         WritelnFile(1)
           
---------------------------------------------------

'action' Emit_defined_type_alias_with_selfref(STRING, TYPE_EXPR)
  
  'rule' Emit_defined_type_alias_with_selfref(S, T):
         (|
           Lookup_aliased_type(T -> S1)
           eq(S, S1)
           WriteFile("t")
         ||
           Lookup_defined_alias(T -> S1)
           WriteFFile("%s.t", S1)
         ||
           Named_type_expr(T -> defined(I, Q))
           Named_type_is_abbrev(I -> T1)
           Emit_defined_type_alias_with_selfref(S, T1)
         ||
           where(T -> bracket(T1))
           Emit_defined_type_alias_with_selfref(S, T1)
         ||
           where(T -> product(XT))
           LParen
           Emit_product_type_expr_with_selfref(S, XT)
           RParen          
         ||
           Type_is_set(T -> ET)
           LParen
           Emit_defined_type_alias_with_selfref(S, ET)
           WriteFile(" R'a_Set.mt)")
         ||
           Type_is_list(T -> ET)
           LParen
           Emit_defined_type_alias_with_selfref(S, ET)
           WriteFile(" R'a_List.mt)")
         ||
           Type_is_map(T -> DT, RT)
           WriteFile("((")
           Emit_defined_type_alias_with_selfref(S, DT)
           WriteFile(", ")
           Emit_defined_type_alias_with_selfref(S, RT)
           WriteFile(") R'a_Map.mt)")
         ||
           Type_is_fun(T -> PT, _, RT)
           WriteFile("((")
           Emit_defined_type_alias_with_selfref(S, PT)
           WriteFile(", ")
           Emit_defined_type_alias_with_selfref(S, RT)
           WriteFile(") R'a_Fun.mt)")
         ||
	   [| -- try for a position
	     Named_type_expr(T -> defined(I1, _))
	     I1'Pos -> Pos
	     Puterror(Pos)
	   |]
	   Putmsg("Type ")
	   Print_type(T)
	   Putmsg(" seems to be involved in mutually dependent record or variant definitions.\n")
	   Not_support(no_pos, "Mutually dependent record or variant definitions")
         |)

'action' Emit_product_type_expr_with_selfref(STRING, PRODUCT_TYPE)

  'rule' Emit_product_type_expr_with_selfref(S, XT):
         (|
           where(XT -> list(T, Tail))
           Emit_defined_type_alias_with_selfref(S, T)
           [|
             where(Tail -> list(_, _))
             WriteFile(" * ")
           |]
           Emit_product_type_expr_with_selfref(S, Tail)
         ||
           where(XT -> nil)
         |)

'action' Emit_variant_datatypedef(POS, STRING, VARIANTS)

  'rule' Emit_variant_datatypedef(Pos, S, VL)
         where(VL -> list(V, Tail))
         where(V -> record(_, Cons, CoL))
         (|
           (|
	     where(Cons -> constructor(CPos, Id))
	   ||
	     where(Cons -> con_ref(I1))
	     I1'Ident -> Id
	     I1'Pos -> CPos
             Add_data_constructor(S, I1)
	   |)
           Id_or_op_to_SML_id(Id, nil -> S1)
           WriteFile(S1)
           Components_to_type_option(CoL -> TO)
           [|
             where(TO -> some(T))
             WriteFile(" of ")
             Emit_defined_type_alias_with_selfref(S, T)
           |]
         ||
	   where(Cons -> wildcard)
	   Not_support(pos(Pos), "wildcard constructor")
	 |)
         [|
           where(Tail -> list(_, _))
           WritelnFile(1)
           WriteFile("| ")
           Emit_variant_datatypedef(Pos, S, Tail)     
         |]

'action' Emit_variant_destfundef(STRING, VARIANTS, VARIANT_OR_RECORD)
  
  'rule' Emit_variant_destfundef(SS, VL, VorR):
         (|
           where(VL -> list(V, Tail))
           [|
             where(V -> record(_, Cons, CoL))
	     (|
	       where(Cons -> constructor(_, Id))
	     ||
	       where(Cons -> con_ref(I1))
	       I1'Ident -> Id
	     |)
             Id_or_op_to_SML_id(Id, nil -> CS)
             Emit_components_destfundef(SS, CS, nil, CoL, VorR)
           |]
           Emit_variant_destfundef(SS, Tail, VorR)
         ||
           where(VL -> nil)
         |)

'action' Emit_components_destfundef(STRING, STRING, COMPONENTS, COMPONENTS, VARIANT_OR_RECORD)

  'rule' Emit_components_destfundef(SS, CS, Pre, CoL, VorR):
         (|
           where(CoL -> list(Co, Tail))
           where(Co -> component(_, Dest, _, Recon))
           [|
             (|
	       where(Dest -> destructor(Pos, DId))
	     ||
	       where(Dest -> dest_ref(I1))
	       I1'Ident -> DId
	       I1'Pos -> Pos
               Add_data_constructor(SS, I1)
	     |)
             Id_or_op_to_SML_id(DId, nil -> DS)
             WriteF2File("fun %s (%s x) = let val (", DS, CS)
             Emit_components_wildcards(0, 0, Pre -> _)
             WriteFile("i")
             Emit_components_wildcards(1, 0, Tail -> _)
             WriteFile(") = x in i end")
             (|
               where(VorR -> variant)
               WritelnFile(1)
               Id_or_op_to_alpha_string(DId -> DS1)
               PosAsString(Pos -> PS)
               WriteF3File("  | %s (_) = raise RSL.RSL_exception \"%s Destructor %s applied to wrong variant\";", DS, PS, DS1)
             ||
               WriteFile(";")
             |)
             WritelnFile(1)
           |]
           [|
             (|
	       where(Recon -> reconstructor(Pos, RId))
	     ||
	       where(Recon -> recon_ref(I2))
	       I2'Ident -> RId
	       I2'Pos -> Pos
               Add_data_constructor(SS, I2)
	     |)
             Id_or_op_to_SML_id(RId, nil -> RS)
             WriteF2File("fun %s (j, %s x) = let val (", RS, CS)
             Emit_components_wildcards(0, 1, Pre -> N)
             WriteFile("_")
             Emit_components_wildcards(1, N+1, Tail -> _)
             WriteFFile(") = x in %s(", CS)
             Emit_components_wildcards(0, 1, Pre -> N1)
             WriteFile("j")
             Emit_components_wildcards(1, N1+1, Tail -> _)
             WriteFile(") end")
             (|
               where(VorR -> variant)
               WritelnFile(1)
               Id_or_op_to_alpha_string(RId -> RS1)
               PosAsString(Pos -> PS)
               WriteF3File("  | %s (_) = raise RSL.RSL_exception \"%s Reconstructor %s applied to wrong variant\";", RS, PS, RS1)
             ||
               WriteFile(";")
             |)
             WritelnFile(1)
           |]
           Emit_components_destfundef(SS, CS, list(Co, Pre), Tail, VorR)
         ||
           where(CoL -> nil)
         |)

'action' Emit_components_wildcards(INT, INT, COMPONENTS -> INT)

  'rule' Emit_components_wildcards(L, N, CoL -> NN):
         (|
           where(CoL -> list(_, Tail))
           [|
             -- trailing list, begins with comma
             eq(L, 1) 
             WriteFile(",")
           |]
           (|
             -- wildcard
             eq(N, 0)
             WriteFile("_")
           ||
             -- identified
             Int_to_string(N -> S)
             WriteFFile("i%s", S)
           |)
           [|
             -- leading list, ends with comma
             eq(L, 0) 
             WriteFile(",")
           |]
	   (| -- if N is zero keep it zero
	     eq(N, 0)
	     where(N -> N1)
	   ||
	     where(N+1 -> N1)
	   |)
           Emit_components_wildcards(L, N1, Tail -> NN1)
           where(NN1+1 -> NN)
         ||
           where(CoL -> nil)
           where(0 -> NN)
         |)

'action' Emit_product_equexpr_with_selfref(STRING, STRING, STRING, INT, PRODUCT_TYPE)

  'rule' Emit_product_equexpr_with_selfref(S, Sx, Sy, N, XT):
         (|
           where(XT -> list(T, Tail))
           Int_to_string(N -> NS)
           GetF2String("#%s(%s)", NS, Sx -> Sx1)
           GetF2String("#%s(%s)", NS, Sy -> Sy1)
           Emit_equexpr_with_selfref(S, Sx1, Sy1, T)
           [|
             where(Tail -> list(_, _))
             WriteFile(" andalso ")
             WritelnFile(1)
           |]
           Emit_product_equexpr_with_selfref(S, Sx, Sy, N+1, Tail)
         ||
           where(XT -> nil)
         |)

'action' Emit_equexpr_with_selfref(STRING, STRING, STRING, TYPE_EXPR)

  'rule' Emit_equexpr_with_selfref(S, Sx, Sy, T):
         (|
           Lookup_aliased_type(T -> S1)
           eq(S, S1)
           WriteF2File("equ (%s, %s)", Sx, Sy)
         ||
           Lookup_defined_alias(T -> S1)
           WriteF3File("%s.equ (%s, %s)", S1, Sx, Sy)
         ||
           Named_type_expr(T -> defined(I, Q))
           Named_type_is_abbrev(I -> T1)
           Emit_equexpr_with_selfref(S, Sx, Sy, T1)
         ||
           where(T -> bracket(T1))
           Emit_equexpr_with_selfref(S, Sx, Sy, T1)
         ||
           where(T -> product(XT))
           PushSetIndentHere(1)
           LParen
           Emit_product_equexpr_with_selfref(S, Sx, Sy, 1, XT)
           RParen
           PopIndent
         ||
           Type_is_set(T -> ET)
           New_temp_name("ex" -> ESx)
           New_temp_name("ey" -> ESy)
           WriteF2File("R'a_Set.equ (fn (%s, %s) => ", ESx, ESy)
           Emit_equexpr_with_selfref(S, ESx, ESy, ET)
           WriteF2File(") (%s, %s)", Sx, Sy)
         ||
           Type_is_list(T -> ET)
           New_temp_name("ex" -> ESx)
           New_temp_name("ey" -> ESy)
           WriteF2File("R'a_List.equ (fn (%s, %s) => ", ESx, ESy)
           Emit_equexpr_with_selfref(S, ESx, ESy, ET)
           WriteF2File(") (%s, %s)", Sx, Sy)
         ||
           Type_is_map(T -> DT, RT)
           New_temp_name("dx" -> DSx)
           New_temp_name("dy" -> DSy)
           WriteF2File("R'a_Map.equ ((fn (%s, %s) => ", DSx, DSy)
           Emit_equexpr_with_selfref(S, DSx, DSy, DT)
           WriteFile("), ")
           New_temp_name("rx" -> RSx)
           New_temp_name("ry" -> RSy)
           WriteF2File("(fn (%s, %s) => ", RSx, RSy)
           Emit_equexpr_with_selfref(S, RSx, RSy, RT)
           WriteF2File(")) (%s, %s)", Sx, Sy)
         ||
           where(T -> fun(PT, _, result(RT, _, _, _, _)))
           New_temp_name("px" -> PSx)
           New_temp_name("py" -> PSy)
           WriteF2File("R'a_Fun.equ ((fn (%s, %s) => ", PSx, PSy)
           Emit_equexpr_with_selfref(S, PSx, PSy, PT)
           WriteFile("), ")
           New_temp_name("rx" -> RSx)
           New_temp_name("ry" -> RSy)
           WriteF2File("(fn (%s, %s) => ", RSx, RSy)
           Emit_equexpr_with_selfref(S, RSx, RSy, RT)
           WriteF2File(")) (%s, %s)", Sx, Sy)
	 ||
	   -- error reported elsewhere?
         |)

'action' Emit_product_strexpr_with_selfref(STRING, STRING, INT, PRODUCT_TYPE)

  'rule' Emit_product_strexpr_with_selfref(S, Sx, N, XT):
         (|
           where(XT -> list(T, Tail))
           Int_to_string(N -> NS)
           GetF2String("#%s(%s)", NS, Sx -> Sx1)
           LParen
           Emit_strexpr_with_selfref(S, Sx1, T)
           RParen
           [|
             where(Tail -> list(_, _))
             WriteFile(" ^ \",\" ^ ")
             WritelnFile(1)
           |]
           Emit_product_strexpr_with_selfref(S, Sx, N+1, Tail)
         ||
           where(XT -> nil)
         |)

'action' Emit_strexpr_with_selfref(STRING, STRING, TYPE_EXPR)

  'rule' Emit_strexpr_with_selfref(S, Sx, T):
         (|
           Lookup_aliased_type(T -> S1)
           eq(S, S1)
           WriteFFile("toString (%s)", Sx)
         ||
           Lookup_defined_alias(T -> S1)
           WriteF2File("%s.toString (%s)", S1, Sx)
         ||
           Named_type_expr(T -> defined(I, Q))
           Named_type_is_abbrev(I -> T1)
           Emit_strexpr_with_selfref(S, Sx, T1)
         ||
           where(T -> bracket(T1))
           Emit_strexpr_with_selfref(S, Sx, T1)
         ||
           where(T -> product(XT))
           WriteFile("\"(\" ^ (")
           PushSetIndentHere(0)
           Emit_product_strexpr_with_selfref(S, Sx, 1, XT)
           WriteFile(") ^ \")\"")
           PopIndent
         ||
           Type_is_set(T -> ET)
           New_temp_name("e" -> ESx)
           WriteFile("R'a_Set.toString ")
           PushSetIndentHere(0)
           WriteFFile("(fn %s => ", ESx)
           Emit_strexpr_with_selfref(S, ESx, ET)
           RParen
           WritelnFile(1)
           WriteFFile("(%s)", Sx)
           PopIndent
         ||
           Type_is_list(T -> ET)
           New_temp_name("e" -> ESx)
           WriteFile("R'a_List.toString ")
           PushSetIndentHere(0)
           WriteFFile("(fn %s => ", ESx)
           Emit_strexpr_with_selfref(S, ESx, ET)
           RParen
           WritelnFile(1)
           WriteFFile("(%s)", Sx)
           PopIndent
         ||
           Type_is_map(T -> DT, RT)
           New_temp_name("d" -> DSx)
           New_temp_name("r" -> RSx)
           WriteFile("R'a_Map.toString ")
           PushSetIndentHere(0)
           LParen
           PushSetIndentHere(0)
           WriteFFile("(fn %s => ", DSx)
           Emit_strexpr_with_selfref(S, DSx, DT)
           WriteFile("),")
           WritelnFile(1)
           WriteFFile("(fn %s => ", RSx)
           Emit_strexpr_with_selfref(S, RSx, RT)
           WriteFile("))")
           PopIndent
           WritelnFile(1)
           WriteFFile("(%s)", Sx)
           PopIndent
         ||
           Type_is_fun(T -> _, _, _)
           WriteFile("\"fn: \" ^ (")
           Emit_typestrexpr_with_selfref(S, "", T)
           RParen
	 ||
	   -- error reported elsewhere?
         |)

'action' Emit_product_typestrexpr_with_selfref(STRING, STRING, PRODUCT_TYPE)

  'rule' Emit_product_typestrexpr_with_selfref(S, TS, XT):
         (|
           where(XT -> list(T, Tail))
           LParen
           Emit_typestrexpr_with_selfref(S, TS, T)
           RParen
           [|
             where(Tail -> list(_, _))
             WriteFile(" ^ \" >< \" ^ ")
           |]
           Emit_product_typestrexpr_with_selfref(S, TS, Tail)
         ||
           where(XT -> nil)
         |)

'action' Get_fun_arrow_string(FUNCTION_ARROW -> STRING)

  'rule' Get_fun_arrow_string(Arrow -> AS):
         (|
           where(Arrow -> partial)
           where("-~->" -> AS)
         ||
           where(Arrow -> total)
           where("->" -> AS)
         |)

'action' Emit_typestrexpr_with_selfref(STRING, STRING, TYPE_EXPR)
    
  'rule' Emit_typestrexpr_with_selfref(S, TS, T):
         (|
           Lookup_aliased_type(T -> S1)
           eq(S, S1)
           (|
             eq(TS, "")
             WriteFile("typeToString ()")
           ||
             WriteFFile("\"%s\"", TS)
           |)
         ||
           Lookup_defined_alias(T -> S1)
           WriteFFile("%s.typeToString ()", S1) 
         ||
           Named_type_expr(T -> defined(I, Q))
           Named_type_is_abbrev(I -> T1)
           Emit_typestrexpr_with_selfref(S, TS, T1)
         ||
           where(T -> bracket(T1))
           Emit_typestrexpr_with_selfref(S, TS, T1)
         ||
           where(T -> product(XT))
           WriteFile("\"(\" ^ (")
           Emit_product_typestrexpr_with_selfref(S, TS, XT)
           WriteFile(") ^ \")\"")
         ||
           Type_is_set(T -> ET)
           WriteFile("R'a_Set.typeToString (fn () => ")
           Emit_typestrexpr_with_selfref(S, TS, ET)
           RParen
         ||
           Type_is_list(T -> ET)
           WriteFile("R'a_List.typeToString (fn () => ")
           Emit_typestrexpr_with_selfref(S, TS, ET)
           RParen
         ||
           Type_is_map(T -> DT, RT)
           WriteFile("R'a_Map.typeToString (fn () => ")
           Emit_typestrexpr_with_selfref(S, TS, DT)
           WriteFile(", fn () => ")
           Emit_typestrexpr_with_selfref(S, TS, RT)
           RParen
         ||
           Type_is_fun(T -> PT, Arrow, RT)
           WriteFile("R'a_Fun.typeToString (fn () => ")
           Emit_typestrexpr_with_selfref(S, TS, PT)
           Get_fun_arrow_string(Arrow -> AS)
           WriteFFile(", \"%s\", fn () => ", AS)
           Emit_typestrexpr_with_selfref(S, TS, RT)
           RParen
         |)

'condition' Try_emit_components_default_value(STRING, COMPONENTS)

  'rule' Try_emit_components_default_value(CS, CoL):
         Components_to_type_option(CoL -> TO)
         (|
           where(TO -> none)
           WriteFile(CS)
         ||
           where(TO -> some(T))
           Lookup_defined_alias(T -> S)
           WriteF2File("%s(%s.defval)", CS, S)
         |)

'action' Emit_variant_equfundef(STRING, INT, VARIANTS)

  'rule' Emit_variant_equfundef(S, N, VL):
         (|
           where(VL -> list(V, Tail))
           where(V -> record(_, Cons, CoL))
	   [| -- allow for wildcard constructor (reported earlier)
	     (|
	       where(Cons -> constructor(_, id_op(Id)))
	     ||
	       where(Cons -> con_ref(I))
	       I'Ident -> id_op(Id)
	     |)
	     (|
	       eq(N, 0)
	       WriteFile("fun ")
	     ||
	       WritelnFile(1)
	       WriteFile("  | ")
	     |)
	     WriteFile("equ ")
	     Id_to_SML_id(Id, nil -> CS)
	     Components_to_type_option(CoL -> TO)
	     (|
	       where(TO -> none)
	       WriteF2File("(%s, %s) = true", CS, CS)
	     ||
	       where(TO -> some(T))
	       WriteF2File("(%s x, %s y) = ", CS, CS)
	       Emit_equexpr_with_selfref(S, "x", "y", T)
	     |)
	   |]
           Emit_variant_equfundef(S, N+1, Tail)
         ||
           where(VL -> nil)
           (|
             eq(N, 1)  -- only 1 variant
           ||
             WritelnFile(1)
             WriteFile("  | equ (_, _) = false")
           |)
         |)

'action' Emit_variant_strfundef(STRING, INT, VARIANTS)

  'rule' Emit_variant_strfundef(S, N, VL):
         (|
           where(VL -> list(V, Tail))
           where(V -> record(_, Cons, CoL))
	   [| -- allow for wildcard constructor (reported earlier)
	     (|
	       where(Cons -> constructor(_, id_op(Id)))
	     ||
	       where(Cons -> con_ref(I))
	       I'Ident -> id_op(Id)
	     |)
	     (|
	       eq(N, 0)
	       WriteFile("fun ")
	     ||
	       WritelnFile(1)
	       WriteFile("  | ")
	     |)
	     WriteFile("toString ")
	     Id_to_SML_id(Id, nil -> CS)
	     SML_id_to_string(Id -> CS1)
	     Components_to_type_option(CoL -> TO)
	     (|
	       where(TO -> none)
	       WriteF2File(" (%s) = \"%s\"", CS, CS1)
	     ||
	       where(TO -> some(T))
	       (|
		 where(CoL -> list(_, nil)) -- brackets needed round single component
		 WriteF2File(" (%s x) = \"%s(\" ^ (", CS, CS1)
		 Emit_strexpr_with_selfref(S, "x", T)
		 WriteFile(" ^ \")\"")
	       ||
		 WriteF2File(" (%s x) = \"%s\" ^ (", CS, CS1)
		 Emit_strexpr_with_selfref(S, "x", T)
	       |)
	       RParen
	     |)
	   |]
           Emit_variant_strfundef(S, 1, Tail)
         ||
           where(VL -> nil)
         |)

-- dead
'action' Emit_variant_typestrfundef(STRING, STRING, INT, VARIANTS)

  'rule' Emit_variant_typestrfundef(S, TS, N, VL):
         (|
           where(VL -> list(V, Tail))
           where(V -> record(_, Cons, CoL))
	   (|
	     where(Cons -> constructor(_, id_op(Id)))
	   ||
	     where(Cons -> con_ref(I))
	     I'Ident -> id_op(Id)
	   |)
           (|
             eq(N, 0)
             WriteFile("fun typeToString () ")
             PushSetIndentHere(0)
             WriteFFile("= \"%s(\" ^ ", TS)
           ||
             WritelnFile(1)
             WriteFile("^ \"|\" ^ ")
           |)
           Id_to_SML_id(Id, nil -> CS)
           Components_to_type_option(CoL -> TO)
           (|
             where(TO -> none)
             WriteFFile("\"%s\"", CS)
           ||
             where(TO -> some(T))
             LParen
             Emit_typestrexpr_with_selfref(S, TS, T)
             RParen
           |)
           Emit_variant_typestrfundef(S, TS, 1, Tail)
         ||
           where(VL -> nil)
           [|
             ne(N, 0)
             WriteFile("^ \")\"")
             PopIndent
           |]
         |)

'action' Emit_variant_structdef(POS, STRING, IDENT, VARIANTS)
  
  'rule' Emit_variant_structdef(Pos, S, Id, VL):
         where(VL -> list(_, _))
         Open_structdef(S)
         ---- type
         WriteFile("datatype t = ")
         PushSetIndentHere(-2)
         Emit_variant_datatypedef(Pos, S, VL)
         WriteFile(";")
         WritelnFile(2)
         PopIndent
         ---- destructors and reconstructors
         (|
           where(VL -> list(_, nil)) -- effectively a record
           Emit_variant_destfundef(S, VL, record)
         ||
           Emit_variant_destfundef(S, VL, variant)
         |)
         WritelnFile(1)
         ---- default value
--       WriteFile("val defval = ")
--       Emit_variant_default_value(VL)
--       WriteFile(";")
--       WritelnFile(2)
         ---- equ
         Emit_variant_equfundef(S, 0, VL)
         WriteFile(";")
         WritelnFile(2)
         ---- toString
         Emit_variant_strfundef(S, 0, VL)
         WriteFile(";")
         WritelnFile(2)
         Emit_toStringSafe_def
         ---- typeToString
         SML_id_to_string(Id -> TS)
         Emit_sort_typestrfundef(TS)
--       Id_to_SML_id(Id, nil -> TS)
--       Emit_variant_typestrfundef(S, TS, 0, VL)
--       WriteFile(";")
--       WritelnFile(1)
         Close_structdef

---------------------------------------------------

-- dead
'action' Emit_record_default_value(STRING, COMPONENTS)

  'rule' Emit_record_default_value(S, CoL):
         (|
           Try_emit_components_default_value(S, CoL)
         ||
           Err_default_value
         |)

'action' Emit_record_structdef(POS, STRING, IDENT, Object_ids, COMPONENTS)
  
  'rule' Emit_record_structdef(Pos, S, Id, OIs, CoL):
         where(CoL -> list(_, _))
         Open_structdef(S)
         SML_id_to_string(Id -> CS)
         Make_mk_name(CS -> MKCS)
         string_to_id(MKCS -> Mkid)
	 Lookup_constructor(Pos, Mkid, OIs -> I)
	 Add_data_constructor(S, I)
         Id_to_SML_id(Mkid, nil -> MKS)
         ---- type
         WriteFFile("datatype t = %s of ", MKS)
         Components_to_type_option(CoL -> TO)
         where(TO -> some(T))
         Emit_defined_type_alias_with_selfref(S, T)
         WriteFile(";")
         WritelnFile(2)
         ---- destructors and reconstructors
         Emit_components_destfundef(S, MKS, nil, CoL, record)
         WritelnFile(1)
         ---- default value
--       WriteFile("val defval = ")
--       Emit_record_default_value(MKS, CoL)
--       WriteFile(";")
--       WritelnFile(2)
         ---- equ
         WriteF2File("fun equ (%s x, %s y) = ", MKS, MKS)
         Emit_equexpr_with_selfref(S, "x", "y", T)
         WriteFile(";")
         WritelnFile(2)
         ---- toString
         Id_to_SML_id(Id, nil -> TS)
         (|
           where(CoL -> list(_, nil)) -- brackets needed round single component
           WriteF2File("fun toString (%s x) = \"%s(\" ^ (", MKS, MKCS)
           Emit_strexpr_with_selfref(S, "x", T)
           WriteFile(" ^ \")\"")
         ||
           WriteF2File("fun toString (%s x) = \"%s\" ^ (", MKS, MKCS)
           Emit_strexpr_with_selfref(S, "x", T)
         |)
         RParen
         WriteFile(";")
         WritelnFile(2)
         Emit_toStringSafe_def
         ---- typeToString
--       WriteFFile("fun typeToString () = \"%s (\" ^ ", TS)
--       LParen
--       Emit_typestrexpr_with_selfref(S, TS, T)
--       RParen
--       WriteFile(" ^ \")\"")
--       WriteFile(";")
--       WritelnFile(1)
         Emit_sort_typestrfundef(CS)
         Close_structdef

'action' Lookup_constructor(POS, IDENT, Object_ids -> Value_id)

  'rule' Lookup_constructor(Pos, Id, OIs -> I):
	 (|
	   eq(OIs, nil)
	   Get_current_top_values(-> VE)
	   Lookup_id_or_op1(id_op(Id), VE -> list(I, nil))
-- debug
-- Print_id(Id)
-- Putmsg(" found at top\n")
	 ||
	   Get_last_object(OIs -> OI)
	   OI'Env -> CE
	   Lookup_env_value_name(name(Pos, id_op(Id)), CE, nil, ownclass -> list(I, nil))
-- Print_id(Id)
-- Putmsg(" found in object ")
-- OI'Ident -> Oid
-- Print_id(Oid)
-- Putnl
	 |)

'action' Get_last_object(Object_ids -> Object_id)

  'rule' Get_last_object(list(I, nil) -> I):

  'rule' Get_last_object(list(_, Is) -> I):
	 Get_last_object(Is -> I)
---------------------------------------------------

'action' Define_user_type(STRING, Type_id)

  'rule' Define_user_type(S, I)
	 I'Pos -> Pos
	 I'Ident -> Id
         I'Type -> TD
         (|
           where(TD -> sort(abstract))
--           Emit_sort_structdef(S, Id)
         ||
           where(TD -> sort(variant(VL)))
           Emit_variant_structdef(Pos, S, Id, VL)
         ||
           where(TD -> sort(record(CoL)))
	   I'Qualifier -> OIs
           Emit_record_structdef(Pos, S, Id, OIs, CoL)
         ||
           where(TD -> sort(union(_)))
         |)

---------------------------------------------------

'action' Define_class(STRING, IDENT, CLASS)

  'rule' Define_class(S, Id, CL):
         Open_structdef(S)
         Define_class_expr(CL)
         Close_user_structdef(S, Id)

'action' Define_class_expr(CLASS)

  'rule' Define_class_expr(CL):
         (|
           where(CL -> basic(DL))
           Emit_declares(DL)
         ||
           where(CL -> extend(CL1, CL2))
           In_left
           Define_class_expr(CL1)
           Left_right
           Define_class_expr(CL2)
           Out_right
         ||
           where(CL -> hide(_, CL1))
           Define_class_expr(CL1)
         ||
           where(CL -> rename(_, CL1))
           Define_class_expr(CL1)
         ||
           where(CL -> with(_, _, CL1))
           Define_class_expr(CL1)
         ||
           where(CL -> instantiation(name(Pos, id_op(Id)), Objs))
           Get_id_of_scheme(Id -> scheme_id(I))
           I'Class -> CL1
           Define_class_expr(CL1)
         |)

'action' Emit_declares(DECLS)

  'rule' Emit_declares(DL):
         Extract_objects_in_declares(DL -> ODL)
	 Process_object_defs(ODL, nil, nil)
         Process_type_decl_in_declares(DL)
         Extract_vdefs_from_declares(DL, nil -> OVDL)
         Process_vdefs(OVDL, nil)

'action' Extract_objects_in_declares(DECLS -> OBJECT_DEFS)

  'rule' Extract_objects_in_declares(DL -> ODL):
         (|
           where(DL -> list(D, Tail))
	   Extract_objects_in_declares(Tail -> ODL2)
           (|
             where(D -> object_decl(_, ODL1))
             Concatenate_object_defs(ODL1, ODL2 -> ODL)
           ||
	     where(ODL2 -> ODL)
	   |)
         ||
	   where(OBJECT_DEFS'nil -> ODL)
         |)

'action' Concatenate_object_defs(OBJECT_DEFS, OBJECT_DEFS -> OBJECT_DEFS)

  'rule' Concatenate_object_defs(list(D, DL), DL1 -> list(D, DL2)):
	 Concatenate_object_defs(DL, DL1 -> DL2)

  'rule' Concatenate_object_defs(nil, DL -> DL):

'action' Process_object_defs(OBJECT_DEFS, OBJECT_DEFS, FOUND)

  'rule' Process_object_defs(list(OD, Tail), Waiting, Found):
	 where(OD -> odef(_, Id, PS, CL))
	 (|
	   where(PS -> nil)
	   (|
	     Collect_object_idents(CL, nil -> Ids)
	     (| Uses_defs(Ids, Tail) || Uses_defs(Ids, Waiting) |)
	     Process_object_defs(Tail, list(OD, Waiting), Found)
	   ||
	     Get_current_modules(-> ME)
	     Lookup_object_in_module(Id, ME -> object_id(I))
	     Current -> C
	     I'Param_env -> PCE
	     I'Env -> CE
	     Current <- current_env(CE,current_env(PCE, C))
	     Extend_paths -> Paths
	     Extend_paths <- list(nil, list(nil, Paths))
	     id_to_string(Id -> S)
	     Push_object(I)
	     Define_class(S, Id, CL)
	     Pop_object()
	     Current -> current_env(CE1,current_env(PCE1,C1))
	     Current <- C1
	     Extend_paths <- Paths
	     Get_current_with(-> Objs)
	     Open_withs(S, Id, Objs)
	     Process_object_defs(Tail, Waiting, found)
	   |)
	 ||
	   Process_object_defs(Tail, Waiting, found)
	 |)

  'rule' Process_object_defs(nil, nil, _):
	   
  'rule' Process_object_defs(nil, Waiting, Found):
	 where(Waiting -> list(odef(P, Wid, _, _), _))
	 (|
	   eq(Found, nil)
	   Puterror(P)
	   Putmsg("Object ")
	   Print_id(Wid)
	   Putmsg(" seems to be involved in mutual recursion.")
	   Putnl()
	 ||
	   Process_object_defs(Waiting, nil, nil)
	 |)

'condition' Uses_defs(IDENTS, OBJECT_DEFS)

  'rule' Uses_defs(Ids, list(odef(_, Id, _, _), ODL)):
	 (|
	   Occurs_in_idents(Id, Ids)
	 ||
	   Uses_defs(Ids, ODL)
	 |)

'sweep' Collect_object_idents(ANY, IDENTS -> IDENTS)

  'rule' Collect_object_idents(instantiation(_, Objs), Ids2 -> Ids):
	 Idents_of_objects(Objs -> Ids1)
	 Concatenate_idents(Ids1, Ids2 -> Ids)

  'rule' Collect_object_idents(qual_name(_, Obj, _), Ids -> list(Id, Ids)):
	 Ident_of_object(Obj -> Id)

'action' Idents_of_objects(OBJECT_EXPRS -> IDENTS)

  'rule' Idents_of_objects(list(Obj, Objs) -> list(Id, Ids)):
	 Idents_of_objects(Objs -> Ids)
	 Ident_of_object(Obj -> Id)

  'rule' Idents_of_objects(nil -> nil):

'action' Ident_of_object(OBJECT_EXPR -> IDENT)

  'rule' Ident_of_object(obj_name(N) -> Id):
	 Ident_of_name(N -> Id)

  'rule' Ident_of_object(obj_appl(Obj, _) -> Id):
	 Ident_of_object(Obj -> Id)

  'rule' Ident_of_object(obj_array(_, Obj) -> Id):
	 Ident_of_object(Obj -> Id)

  'rule' Ident_of_object(obj_fit(Obj, _) -> Id):
	 Ident_of_object(Obj -> Id)

  'rule' Ident_of_object(obj_occ(_, I) -> Id):
	 I'Ident -> Id

  'rule' Ident_of_object(qual_occ(_, Obj, _) -> Id):
	 Ident_of_object(Obj -> Id)

'action' Ident_of_name(NAME -> IDENT)

  'rule' Ident_of_name(name(_, id_op(Id)) -> Id):

  'rule' Ident_of_name(qual_name(_, Obj, _) -> Id):
	 Ident_of_object(Obj -> Id)

'action' Concatenate_idents(IDENTS, IDENTS -> IDENTS)

  'rule' Concatenate_idents(list(Id, Ids1), Ids2 -> list(Id, Ids)):
	 Concatenate_idents(Ids1, Ids2 -> Ids)

  'rule' Concatenate_idents(nil, Ids -> Ids):

'condition' Occurs_in_idents(IDENT, IDENTS)

  'rule' Occurs_in_idents(Id, list(Id1, Ids)):
	 (| eq(Id, Id1) || Occurs_in_idents(Id, Ids) |)


'action' Push_object(Object_id)

  'rule' Push_object(I):
	 Var_objects -> Is
	 Var_objects <- list(I, Is)

'action' Pop_object

  'rule' Pop_object:
	 Var_objects -> list(I, Is)
	 Var_objects <- Is

'action' Prune_object_ids(Object_ids -> Object_ids)

  'rule' Prune_object_ids(Is -> Is1):
	 Var_objects -> Stack
	 Prune_object_ids1(Is, Stack -> Is1)

'action' Prune_object_ids1(Object_ids, Object_ids -> Object_ids)

  'rule' Prune_object_ids1(nil, _ -> nil):

  'rule' Prune_object_ids1(list(I, Is), Stack -> Is1):
	 Prune_object_ids1(Is, Stack -> Is2)
         (|
	   Isin_object_ids(I, Stack)
	   where(Is2 -> Is1)
	 ||
	   where(Object_ids'list(I, Is2) -> Is1)
	 |)

'condition' Isin_object_ids(Object_id, Object_ids)

  'rule' Isin_object_ids(I, list(I1, Is)):
	 (| eq(I, I1) || Isin_object_ids(I, Is) |)

'action' Append_value_defs(OPT_VDEFS, VALUE_DEFS -> OPT_VDEFS)

  'rule' Append_value_defs(OVDL0, VDL -> OVDL):
         (|
           where(VDL -> list(VD, Tail))
           Append_value_defs(list(value(VD), OVDL0), Tail -> OVDL)
         ||
           where(VDL -> nil)
           where(OVDL0 -> OVDL)
         |)

'action' Append_variable_defs(OPT_VDEFS, VARIABLE_DEFS -> OPT_VDEFS)

  'rule' Append_variable_defs(OVDL0, VarDL -> OVDL):
         (|
           where(VarDL -> list(VarD, Tail))
           Append_variable_defs(list(variable(VarD), OVDL0), Tail -> OVDL)
         ||
           where(VarDL -> nil)
           where(OVDL0 -> OVDL)
         |)

'action' Append_subtype_defs(OPT_VDEFS, TYPE_DEFS -> OPT_VDEFS)

  'rule' Append_subtype_defs(OVDL0, TDL -> OVDL):
         (|
           where(TDL -> list(TD, Tail))
	   (|
	     where(TD -> abbrev(P,Id,subtype(_,_)))
	     Lookup_type_id(P, Id -> type_id(I))
	     I'Subtype -> funct(I1)
	     Append_subtype_defs(list(subtype_fun(I1), OVDL0), Tail -> OVDL)
           ||
	     Append_subtype_defs(OVDL0, Tail -> OVDL)
	   |)
         ||
           where(OVDL0 -> OVDL)
         |)

'action' Extract_vdefs_from_declares(DECLS, OPT_VDEFS -> OPT_VDEFS)

  'rule' Extract_vdefs_from_declares(DL, OVDL0 -> OVDL):
         (|
           where(DL -> list(D, Tail))
           (|
             where(D -> value_decl(_, VDL))
             Append_value_defs(OVDL0, VDL -> OVDL1)
             Extract_vdefs_from_declares(Tail, OVDL1 -> OVDL)
           ||
             where(D -> variable_decl(_, VarDL))
             Append_variable_defs(OVDL0, VarDL -> OVDL1)
             Extract_vdefs_from_declares(Tail, OVDL1 -> OVDL)
	   ||
	     where(D -> type_decl(_, TDL))
	     Append_subtype_defs(OVDL0, TDL -> OVDL1)
             Extract_vdefs_from_declares(Tail, OVDL1 -> OVDL)
           ||
             Extract_vdefs_from_declares(Tail, OVDL0 -> OVDL)
           |)
         ||
           where(DL -> nil)
           where(OVDL0 -> OVDL)
         |)

'action' Process_type_decl_in_declares(DECLS)

  'rule' Process_type_decl_in_declares(DL):
         (|
           where(DL -> list(D, Tail))
           (|
             where(D -> type_decl(_, TDL))
             Emit_type_decl(TDL)
             Process_type_decl_in_declares(Tail)
           ||
             Process_type_decl_in_declares(Tail)
           |)
         ||
           where(DL -> nil)
         |)

'action' Emit_type_decl(TYPE_DEFS)

  'rule' Emit_type_decl(TDL):
         (|
           where(TDL -> list(TD, Tail))
           (|
             where(TD -> sort(Pos, Id))
           ||
             where(TD -> abbrev(Pos, Id, _))
           ||
             where(TD -> variant(Pos, Id, _))
           ||
             where(TD -> record(Pos, Id, _))
           |)
           Ident_to_type_expr(Pos, Id -> T)
           Get_defined_alias(T -> S)
           Id_to_SML_id(Id, nil -> TS)
           WriteF2File("type %s = %s.t;", TS, S)
           WritelnFile(2)
           Emit_type_decl(Tail)
         ||
           where(TDL -> nil)
         |)

'action' Process_vdefs(OPT_VDEFS, OPT_VDEFS_LIST)

  'rule' Process_vdefs(L, LL):
         (|
           where(L -> nil)
           where(LL -> nil)
         ||
           Try_define_vdefs(L, nil, LL -> L1, LL1)
           Process_vdefs(L1, LL1)
         |)

'action' Try_define_vdefs(OPT_VDEFS, OPT_VDEFS, OPT_VDEFS_LIST -> OPT_VDEFS, OPT_VDEFS_LIST)

  'rule' Try_define_vdefs(L0, Lskip, LL0 -> L, LL):
         (|
           where(L0 -> nil)
           where(Lskip -> L)
           Define_first_vdefs(LL0 -> LL)
         ||
           where(L0 -> list(OVD, Tail))
           (|
             Merge_vdefs_ring(OVD, LL0 -> LL1)
             Concat_vdefs(Lskip, Tail -> L1)
             Try_define_vdefs(L1, nil, LL1 -> L, LL)
           ||
             Try_define_vdefs(Tail, OPT_VDEFS'list(OVD, Lskip), LL0 -> L, LL)
           |)
         |)

'action' Define_first_vdefs(OPT_VDEFS_LIST -> OPT_VDEFS_LIST)

  'rule' Define_first_vdefs(LL0 -> LL):
         (|
           where(LL0 -> list(L, Tail))
           Emit_vdefs(0, L)
           where(Tail -> LL)
         ||
           where(LL0 -> LL)
         |)

'action' Concat_vdefs(OPT_VDEFS, OPT_VDEFS -> OPT_VDEFS)

  'rule' Concat_vdefs(L1, L2 -> L):
         (|
           where(L1 -> nil)
           where(L2 -> L)
         ||
           where(L1 -> list(D, Tail))
           Concat_vdefs(Tail, L2 -> L3)
           where(OPT_VDEFS'list(D, L3) -> L)
         |)

'condition' Merge_vdefs_ring(OPT_VDEF, OPT_VDEFS_LIST -> OPT_VDEFS_LIST)

  'rule' Merge_vdefs_ring(D, LL0 -> LL):
         (|
           where(LL0 -> nil)
           Insert_def_into_ring(D, LL0 -> LL, _)
         ||
           where(LL0 -> list(L, Tail))
           (|
             Def_is_in_vdefs_body(D, L)
             Insert_def_into_ring(D, LL0 -> LL, _)
           ||
             where(LL0 -> LL)
             False_cond
           |)
         |)

'action' Insert_def_into_ring(OPT_VDEF, OPT_VDEFS_LIST -> OPT_VDEFS_LIST, INT)

  'rule' Insert_def_into_ring(D, LL0 -> LL, N):
         (|
           where(LL0 -> nil)
           where(OPT_VDEFS_LIST'list(OPT_VDEFS'list(D, nil), nil) -> LL)
           where(0 -> N)
         ||
           where(LL0 -> list(L, Tail))
           Insert_def_into_ring(D, Tail -> LL1, N1)
           where(LL1 -> list(L1, Tail1))
           (|
             eq(N1, 1)
             Concat_vdefs(L, L1 -> L2)
             where(OPT_VDEFS_LIST'list(L2, Tail1) -> LL)
             where(1 -> N)
           ||
             eq(N1, 0)
             (|
               Defs_are_in_vdef_body(L, D)
               where(OPT_VDEFS_LIST'list(OPT_VDEFS'list(D, L), Tail1) -> LL)
               where(1 -> N)
             ||
               where(OPT_VDEFS_LIST'list(L1, LL0) -> LL)
               where(0 -> N)
             |)
           |)
         |)

'condition' Pos_is_in_value_expr_list(POS, VALUE_EXPRS)

  'rule' Pos_is_in_value_expr_list(Pos, VL):
         where(VL -> list(V, Tail))
         (|
           Pos_is_in_value_expr(Pos, V)
         ||
           Pos_is_in_value_expr_list(Pos, Tail)
         |)

'condition' Pos_is_in_value_pair_list(POS, VALUE_EXPR_PAIRS)

  'rule' Pos_is_in_value_pair_list(Pos, VPL):
         where(VPL -> list(VP, Tail))
         where(VP -> pair(V1, V2))
         (|
           Pos_is_in_value_expr(Pos, V1)
         ||
           Pos_is_in_value_expr(Pos, V2)
         ||
           Pos_is_in_value_pair_list(Pos, Tail)
         |)

'condition' Pos_is_in_opt_post(POS, OPT_POST_CONDITION)

  'rule' Pos_is_in_opt_post(Pos, post(Post)):
	 Pos_is_in_post_cond(Pos, Post)

'condition' Pos_is_in_pre_cond(POS, PRE_CONDITION)
  
  'rule' Pos_is_in_pre_cond(Pos, Pre):
         where(Pre -> pre_cond(_, V))
         Pos_is_in_value_expr(Pos, V)

'condition' Pos_is_in_opt_cond(POS, OPT_CONDITION)
  
  'rule' Pos_is_in_opt_cond(Pos, Opt):
         where(Opt -> condition(V))
         Pos_is_in_value_expr(Pos, V)

'condition' Pos_is_in_post_cond(POS, POST_CONDITION)

  'rule' Pos_is_in_post_cond(Pos, Post):
         where(Post -> post_cond(_, RN, V))
         Pos_is_in_value_expr(Pos, V)

'condition' Pos_is_in_initialisation(POS, INITIALISATION, OPT_CONDITION)

  'rule' Pos_is_in_initialisation(Pos, Ini, Cond):
         (|
           where(Ini -> initial(V))
	   (|
             Pos_is_in_value_expr(Pos, V)
	   ||
	     Pos_is_in_opt_cond(Pos, Cond)
	   |)
         ||
           where(Ini -> nil)
         |)

'condition' Pos_is_in_variable_def_ids(POS, IDENTS)

  'rule' Pos_is_in_variable_def_ids(Pos, Ids):
         where(Ids -> list(Id, Tail))
         Get_current_variables(-> VARS)
         Lookup_env_variable_id(Id, nil, VARS -> variable_id(VarI))
         VarI'Init -> Ini
	 VarI'Subtype -> Cond
         (|
           Pos_is_in_initialisation(Pos, Ini, Cond)
         ||
           Pos_is_in_variable_def_ids(Pos, Tail)
         |)

'condition' Pos_is_in_variable_def(POS, VARIABLE_DEF)

  'rule' Pos_is_in_variable_def(Pos, VarD):
         (|
           where(VarD -> single(_, Id, _, _))
           Pos_is_in_variable_def_ids(Pos, list(Id, nil))
         ||
           where(VarD -> multiple(_, Ids, _))
           Pos_is_in_variable_def_ids(Pos, Ids)
         |)

'condition' Pos_is_in_vdef_body(POS, OPT_VDEF)

  'rule' Pos_is_in_vdef_body(Pos, OVD):
         (|
           where(OVD -> value(VD))
           (|
             where(VD -> exp_val(_, TG, _))
             Get_resolved_exp_val_def(TG -> T, V, Cond)
	     (|
               Pos_is_in_value_expr(Pos, V)
	     ||
	       Pos_is_in_opt_cond(Pos, Cond)
	     |)
           ||
             where(VD -> exp_fun(_, TG, _, _, _, _, _))
             Get_resolved_exp_fun_def(TG -> _, expl_fun(_, V, Post, Pre, Cond, PCond))
             (|
               Pos_is_in_value_expr(Pos, V)
             ||
               Pos_is_in_opt_post(Pos, Post)
             ||
               Pos_is_in_pre_cond(Pos, Pre)
             ||
               Pos_is_in_opt_cond(Pos, Cond)
             ||
               Pos_is_in_opt_cond(Pos, PCond)
             |)
           |)
         ||
           where(OVD -> variable(VarD))
           Pos_is_in_variable_def(Pos, VarD)
	 ||
	   where(OVD -> subtype_fun(I))
	   I'Def -> expl_fun(_, V, nil, nil, Cond, PCond)
	   (|
	     Pos_is_in_value_expr(Pos, V)
	   ||
	     Pos_is_in_opt_cond(Pos, Cond)
	   ||
	     Pos_is_in_opt_cond(Pos, PCond)
	   |)
	 |)

'condition' Pos_is_in_vdefs_body(POS, OPT_VDEFS)

  'rule' Pos_is_in_vdefs_body(Pos, OVDL):
         where(OVDL -> list(OVD, Tail))
         (|
           Pos_is_in_vdef_body(Pos, OVD)
         ||
           Pos_is_in_vdefs_body(Pos, Tail)
         |)

'condition' Varids_are_in_vdefs_body(IDENTS, OPT_VDEFS)

  'rule' Varids_are_in_vdefs_body(Ids, OVDL):
         where(Ids -> list(Id, Tail))
         Get_current_variables(-> VARS)
         Lookup_env_variable_id(Id, nil, VARS -> variable_id(VarI))
         VarI'Pos -> Pos
         (|
           Pos_is_in_vdefs_body(Pos, OVDL)
         ||
           Varids_are_in_vdefs_body(Tail, OVDL)
         |)

'condition' Binding_is_in_vdefs_body(BINDING, OPT_VDEFS)

  'rule' Binding_is_in_vdefs_body(B, L):
         (|
           where(B -> single(Pos, _))
           Pos_is_in_vdefs_body(Pos, L)
         ||
           where(B -> product(_, BL))
           Bindings_are_in_vdefs_body(BL, L)
         |)

'condition' Bindings_are_in_vdefs_body(BINDINGS, OPT_VDEFS)

  'rule' Bindings_are_in_vdefs_body(BL, L):
         where(BL -> list(B, Tail))
         (|
           Binding_is_in_vdefs_body(B, L)
         ||
           Bindings_are_in_vdefs_body(Tail, L)
         |)

'condition' Typing_is_in_vdefs_body(TYPING, OPT_VDEFS)

  'rule' Typing_is_in_vdefs_body(TG, L):
         (|
           where(TG -> single(_, B, _))
           Binding_is_in_vdefs_body(B, L)
         ||
           where(TG -> multiple(_, BL, _))
           Bindings_are_in_vdefs_body(BL, L)
         |)

'condition' Def_is_in_vdefs_body(OPT_VDEF, OPT_VDEFS)

  'rule' Def_is_in_vdefs_body(D, L):
         (|
           where(D -> value(VD))
           (|
             where(VD -> exp_val(_, TG, _))
           ||
             where(VD -> exp_fun(_, TG, _, _, _, _, _))
           |)
           Typing_is_in_vdefs_body(TG, L)
         ||
           where(D -> variable(VarD))
           (|
             where(VarD -> single(_, Id, _, _))
             Varids_are_in_vdefs_body(IDENTS'list(Id, nil), L)
           ||
             where(VarD -> multiple(_, Ids, _))
             Varids_are_in_vdefs_body(Ids, L)
           |)
	 ||
	   where(D -> subtype_fun(I))
	   I'Pos -> P
	   Pos_is_in_vdefs_body(P, L)
         |)

'condition' Defs_are_in_vdef_body(OPT_VDEFS, OPT_VDEF)

  'rule' Defs_are_in_vdef_body(L, D):
         where(L -> list(D1, Tail))
         (|
           Def_is_in_vdefs_body(D1, OPT_VDEFS'list(D, nil))
         ||
           Defs_are_in_vdef_body(Tail, D)
         |)
           
'condition' Pos_is_in_args(POS, ACTUAL_FUNCTION_PARAMETERS)

  'rule' Pos_is_in_args(Pos, ArgL):
         where(ArgL -> list(Arg, Tail))
         where(Arg -> fun_arg(_, VL))
         (|
           Pos_is_in_value_expr_list(Pos, VL)
         ||
           Pos_is_in_args(Pos, Tail)
         |)  

'condition' Pos_is_in_env_local(POS, DECLS, CLASS_ENV, VALUE_EXPR)

  'rule' Pos_is_in_env_local(Pos, DL, CE, V):
         Open_local_env(CE -> Paths)
         (|
           Pos_is_in_value_expr(Pos, V)
           where(1 -> N)
         ||
           Extract_vdefs_from_declares(DL, nil -> OVDL)
           Pos_is_in_vdefs_body(Pos, OVDL)
           where(1 -> N)
         ||
           where(0 -> N)
         |) 
         Close_local_env(Paths)
         eq(N, 1)

'condition' Pos_is_in_let_def_list(POS, LET_DEFS)

  'rule' Pos_is_in_let_def_list(Pos, L):
         where(L -> list(D, Tail))
         (|
           where(D -> explicit(_, _, V))
           Pos_is_in_value_expr(Pos, V)
         ||
           Pos_is_in_let_def_list(Pos, Tail)
         |)

'condition' Pos_is_in_let_expr(POS, LET_DEFS, VALUE_EXPR)

  'rule' Pos_is_in_let_expr(Pos, LDL, V):
         (|
           Pos_is_in_value_expr(Pos, V)
         ||
           Pos_is_in_let_def_list(Pos, LDL)
         |)        

'condition' Pos_is_in_elif_branch_list(POS, ELSIF_BRANCHES)

  'rule' Pos_is_in_elif_branch_list(Pos, ELIL):
         where(ELIL -> list(ELI, Tail))
         where(ELI -> elsif(_, V1, V2, _))
         (|
           Pos_is_in_value_expr(Pos, V1)
         ||
           Pos_is_in_value_expr(Pos, V2)
         ||
           Pos_is_in_elif_branch_list(Pos, Tail)
         |)

'condition' Pos_is_in_else_branch(POS, ELSE_BRANCH)

  'rule' Pos_is_in_else_branch(Pos, EL):
         where(EL -> else(_, V))
         Pos_is_in_value_expr(Pos, V)

'condition' Pos_is_in_case_branch_list(POS, CASE_BRANCHES)

  'rule' Pos_is_in_case_branch_list(Pos, CBL):
         where(CBL -> list(CB, Tail))
         where(CB -> case(_, _, V, _))
         (|
           Pos_is_in_value_expr(Pos, V)
         ||
           Pos_is_in_case_branch_list(Pos, Tail)
         |)

'condition' Pos_is_in_list_limit(POS, LIST_LIMITATION)

  'rule' Pos_is_in_list_limit(Pos, Limit):
         where(Limit -> list_limit(_, B, V1, R))
         (|
           Pos_is_in_value_expr(Pos, V1)
         ||
           where(R -> restriction(_, V2))
           Pos_is_in_value_expr(Pos, V2)
         |)

'condition' Pos_is_in_value_id(POS, Value_id)

  'rule' Pos_is_in_value_id(Pos, VI):
         VI'Pos -> Pos1
         eq(Pos, Pos1)

'condition' Pos_is_in_variable_id(POS, Variable_id)
   
  'rule' Pos_is_in_variable_id(Pos, VarI):
         VarI'Pos -> Pos1
         eq(Pos, Pos1)

'condition' Pos_is_in_value_expr(POS, VALUE_EXPR)

  'rule' Pos_is_in_value_expr(Pos, V):
         (|
           where(V -> product(_, VL))
           Pos_is_in_value_expr_list(Pos, VL)
         ||
           where(V -> ranged_set(_, V1, V2))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_value_expr(Pos, V2)
           |)
         ||
           where(V -> enum_set(_, VL))
           Pos_is_in_value_expr_list(Pos, VL)
          ||
           where(V -> comp_set(_, V1, set_limit(_, TGL, R)))
	   (|
             Pos_is_in_value_expr(Pos, V1)
	   ||
	     where(R -> restriction(_, VR))
             Pos_is_in_value_expr(Pos, VR)
	   |)
        ||
           where(V -> ranged_list(_, V1, V2))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_value_expr(Pos, V2)
           |)
         ||
           where(V -> enum_list(_, VL))
           Pos_is_in_value_expr_list(Pos, VL)
          ||
           where(V -> comp_list(_, V1, list_limit(_, B, VL, R)))
	   (|
             Pos_is_in_value_expr(Pos, V1)
	   ||
             Pos_is_in_value_expr(Pos, VL)
	   ||
	     where(R -> restriction(_, VR))
             Pos_is_in_value_expr(Pos, VR)
	   |)
         ||
           where(V -> enum_map(_, VPL))
           Pos_is_in_value_pair_list(Pos, VPL)
          ||
           where(V -> comp_map(_, pair(V1, V2), set_limit(_, TGL, R)))
	   (|
             Pos_is_in_value_expr(Pos, V1)
	   ||
             Pos_is_in_value_expr(Pos, V2)
	   ||
	     where(R -> restriction(_, VR))
             Pos_is_in_value_expr(Pos, VR)
	   |)
         ||
           where(V -> function(_, _, V1))
           Pos_is_in_value_expr(Pos, V1)
         ||
           where(V -> application(_, V1, ArgL))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_args(Pos, ArgL)
           |)
         ||
            where(V -> quantified(_, _, TGL, R))
	    where(R -> restriction(_, V1))
            Pos_is_in_value_expr(Pos, V1)
         ||
           where(V -> equivalence(_, V1, V2, Pre))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_value_expr(Pos, V2)
           ||
             Pos_is_in_pre_cond(Pos, Pre)
           |)
         ||
           where(V -> post(_, V1, Post, Pre))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_post_cond(Pos, Post)
           ||
             Pos_is_in_pre_cond(Pos, Pre)
           |)
         ||
           where(V -> disamb(_, V1, _))
           Pos_is_in_value_expr(Pos, V1)
         ||
           where(V -> bracket(_, V1))
           Pos_is_in_value_expr(Pos, V1)
         ||
           where(V -> ax_infix(_, V1, _, V2, _))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_value_expr(Pos, V2)
           |)
         ||
           where(V -> val_infix(_, V1, _, V2))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_value_expr(Pos, V2)
           |)
         ||
           where(V -> stmt_infix(_, V1, _, V2))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_value_expr(Pos, V2)
           |)
         ||
           where(V -> always(_, V1))
           Pos_is_in_value_expr(Pos, V1)
         ||
           where(V ->ax_prefix(_, _, V1))
           Pos_is_in_value_expr(Pos, V1)
         ||
           where(V -> val_prefix(_, _, V1))
           Pos_is_in_value_expr(Pos, V1)
         ||
           where(V -> let_expr(_, LDL, V1))
           Pos_is_in_let_expr(Pos, LDL, V1)
         ||
           where(V -> if_expr(_, V1, V2, _, ELIL, EL))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_value_expr(Pos, V2)
           ||
             Pos_is_in_elif_branch_list(Pos, ELIL)
           ||
             Pos_is_in_else_branch(Pos, EL)
           |)
         ||
           where(V -> case_expr(_, V1, _, CBL))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_case_branch_list(Pos, CBL)
           |)           
         ||
           where(V -> while_expr(_, V1, V2))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_value_expr(Pos, V2)
           |)
         ||
           where(V -> until_expr(_, V1, V2))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_value_expr(Pos, V2)
           |)
         ||
           where(V -> for_expr(_, Limit, V1))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_list_limit(Pos, Limit)
           |)
         ||
           where(V -> val_occ(_, VI, Q))
           Pos_is_in_value_id(Pos, VI)
         ||
           where(V -> var_occ(_, VarI, Q))
           Pos_is_in_variable_id(Pos, VarI)
         ||
           where(V -> pre_occ(_, VarI, Q))
           Pos_is_in_variable_id(Pos, VarI)
         ||
           where(V -> infix_occ(_, V1, VI, Q, V2))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_value_expr(Pos, V2)
           ||
             Pos_is_in_value_id(Pos, VI)
           |)
         ||
           where(V -> prefix_occ(_, VI, Q, V1))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_value_id(Pos, VI)
           |)
         ||
           where(V -> ass_occ(_, VarI, Q, V1))
           (|
             Pos_is_in_value_expr(Pos, V1)
           ||
             Pos_is_in_variable_id(Pos, VarI)
           |)
         ||
           where(V -> env_local(_, DL, CE, V1))
           Pos_is_in_env_local(Pos, DL, CE, V1)
         |)

'action' Emit_parameters_as_string(FORMAL_FUNCTION_PARAMETERS, TYPE_EXPR)

  'rule' Emit_parameters_as_string(FFPL, T)
	 (|
	   where(FFPL -> list(FFP, Tail))
	   where(FFP -> form_parm(Pos, BL))
	   (|
	     where(BL -> list(B, nil))
	     WriteFile("\"(\" ^ ")
	   ||
	     where(BINDING'product(Pos, BL) -> B)
	   |)
	   Overload_binding(B -> B1)
	   where(T -> fun(PT, _, result(RT,_,_,_,_)))
	   Get_defined_alias(PT -> SPT)
	   WriteFFile("%s.toString ", SPT)
	   Emit_binding(B1)
	   [|
	     where(BL -> list(_, nil))
	     WriteFile(" ^ \")\"")
	   |]
	   [|
	     ne(Tail, nil)
	     WriteFile(" ^ ")
	     Emit_parameters_as_string(Tail, RT)
	   |]
	 ||
	   where(FFPL -> nil)
           WriteFile("()")
	 |)

'action' Emit_curried_parameter_list(INT, FORMAL_FUNCTION_PARAMETERS)

  'rule' Emit_curried_parameter_list(N, FFPL):
         (|
           where(FFPL -> list(FFP, Tail))
           where(FFP -> form_parm(Pos, BL))
           (|
             where(BL -> list(B, nil))
           ||
             where(BINDING'product(Pos, BL) -> B)
           |)
           Overload_binding(B -> B1)
           Emit_binding(B1)
           WriteFile(" ")
           Emit_curried_parameter_list(1, Tail)
         ||
           where(FFPL -> nil)
           [|
             eq(N, 0)
             WriteFile("() ")
           |]
         |)

'action' Emit_vdefs(INT, OPT_VDEFS)

  'rule' Emit_vdefs(N, L):
         (|
           where(L -> list(D, Tail))
           (|
             where(D -> value(VD))
             Emit_value_def(N, VD)
             (|
               where(Tail -> list(_, _))
               WritelnFile(1)
               Emit_vdefs(N+1, Tail)
             ||
               WriteFile(";")
               WritelnFile(2)
             |)
           ||
             where(D -> variable(VarD))
             Emit_variable_def(VarD)
             Emit_vdefs(N+1, Tail)
	   ||
	     where(D -> subtype_fun(I))
	     Emit_subtype_fun(N, I)
             (|
               where(Tail -> list(_, _))
               WritelnFile(1)
               Emit_vdefs(N+1, Tail)
             ||
               WriteFile(";")
               WritelnFile(2)
             |)
           |)
         ||
           where(L -> nil)
         |)

'action' Overload_pos_id_or_op(POS, ID_OR_OP -> IDENT)

  'rule' Overload_pos_id_or_op(Pos, Id -> Id1)
         Id_or_op_to_alpha_string(Id -> S1)
         Pos_to_string(Pos -> S2)
         GetF2String("%s'%s", S1, S2 -> S)
         string_to_id(S -> Id1)

'action' Op_to_alpha_string(OP -> STRING)

  'rule' Op_to_alpha_string(eq -> "eq"):

  'rule' Op_to_alpha_string(neq -> "noteq"):

  'rule' Op_to_alpha_string(eqeq -> "eqeq"):

  'rule' Op_to_alpha_string(gt -> "gt"):

  'rule' Op_to_alpha_string(lt -> "lt"):

  'rule' Op_to_alpha_string(ge -> "geq"):

  'rule' Op_to_alpha_string(le -> "leq"):

  'rule' Op_to_alpha_string(supset -> "psup"):

  'rule' Op_to_alpha_string(subset -> "psub"):

  'rule' Op_to_alpha_string(supseteq -> "sup"):

  'rule' Op_to_alpha_string(subseteq -> "sub"):

  'rule' Op_to_alpha_string(isin -> "isin"):

  'rule' Op_to_alpha_string(notisin -> "notisin"):

  'rule' Op_to_alpha_string(rem -> "mod"):

  'rule' Op_to_alpha_string(caret -> "conc"):

  'rule' Op_to_alpha_string(union -> "union"):

  'rule' Op_to_alpha_string(override -> "over"):

  'rule' Op_to_alpha_string(mult -> "mult"):

  'rule' Op_to_alpha_string(div -> "div"):

  'rule' Op_to_alpha_string(hash -> "hash"):

  'rule' Op_to_alpha_string(inter -> "inter"):

  'rule' Op_to_alpha_string(exp -> "exp"):

  'rule' Op_to_alpha_string(abs -> "abs"):

  'rule' Op_to_alpha_string(int -> "int"):

  'rule' Op_to_alpha_string(real -> "real"):

  'rule' Op_to_alpha_string(card -> "card"):

  'rule' Op_to_alpha_string(len -> "len"):

  'rule' Op_to_alpha_string(inds -> "inds"):

  'rule' Op_to_alpha_string(elems -> "elems"):

  'rule' Op_to_alpha_string(hd -> "hd"):

  'rule' Op_to_alpha_string(tl -> "tl"):

  'rule' Op_to_alpha_string(dom -> "dom"):

  'rule' Op_to_alpha_string(rng -> "rng"):

  'rule' Op_to_alpha_string(wait -> "wait"):

  'rule' Op_to_alpha_string(plus -> "plus"):

  'rule' Op_to_alpha_string(minus -> "minus"):

  'rule' Op_to_alpha_string(N -> "N"):

  'rule' Op_to_alpha_string(X -> "X"):

  'rule' Op_to_alpha_string(F -> "F"):

'action' Id_or_op_to_alpha_string(ID_OR_OP -> STRING)

  'rule' Id_or_op_to_alpha_string(Id -> S):
         (|
           where(Id -> id_op(Id1))
           SML_id_to_string(Id1 -> S)
         ||
           where(Id -> op_op(Op))
           Op_to_alpha_string(Op -> S)
         |)

'action' Binding_to_string(BINDING -> STRING)

  'rule' Binding_to_string(single(_, Id) -> S):
	 Id_or_op_to_alpha_string(Id -> S)

  'rule' Binding_to_string(product(_, BL) -> S):
	 Bindings_to_string(BL -> S1)
	 Concatenate3("(", S1, ")" -> S)

'action' Bindings_to_string(BINDINGS -> STRING)

  'rule' Bindings_to_string(list(B, nil) -> S):
	 Binding_to_string(B -> S)

  'rule' Bindings_to_string(list(B, BL) -> S):
	 Binding_to_string(B -> S1)
	 Bindings_to_string(BL -> S2)
	 Concatenate3(S1, ",", S2 -> S)

'action' Overload_binding(BINDING -> BINDING)

  'rule' Overload_binding(B -> B1):
         (|
           where(B -> single(Pos, Id))
           Overload_pos_id_or_op(Pos, Id -> Id1)
           where(BINDING'single(Pos, id_op(Id1)) -> B1)
         ||
           where(B -> product(Pos, BL))
           Overload_binding_list(BL -> BL1)
           where(BINDING'product(Pos, BL1) -> B1)
         ||
           where(B -> B1)
         |)

'action' Overload_binding_list(BINDINGS -> BINDINGS)

  'rule' Overload_binding_list(BL -> BL1):
         (|
           where(BL -> list(B, Tail))
           Overload_binding(B -> B1)
           Overload_binding_list(Tail -> Tail1)
           where(BINDINGS'list(B1, Tail1) -> BL1)
         ||
           where(BL -> nil)
           where(BL -> BL1)
         |)

'action' Emit_value_def(INT, VALUE_DEF)

  'rule' Emit_value_def(N, VD):
         (|
           where(VD -> typing(Pos, _))
           Not_support(pos(Pos), "underspecified value")
         ||
           where(VD -> exp_val(Pos, TG, _))
           (|
             where(TG -> single(_, B, _))
             Get_resolved_exp_val_def(TG -> T, V, Cond)
             (|
               eq(N, 0)
               WriteFile("val ")
             ||
               WriteFile("and ")
             |)
             Overload_binding(B -> B1)
             Emit_binding(B1)
             WriteFile(" = ")
	     (| -- explicit values stored as disambiguations
	       where(V -> disamb(_, V1, _))
	     ||
	       where(V -> V1)
	     |)
	     -- not easy to use stored subtype condition
	     -- as applies if values defined separately
	     Maxtype(T -> Tm)
	     -- get best type
	     Type_of_val(V1, Tm -> T1)
	     string_to_id("z__" -> Z)
	     New_value_id(Pos, id_op(Z) -> I)
	     I'Type <- T1
	     Isin_subtype(val_occ(Pos,I,nil), T -> Pred)
-- debug
-- Print_binding(B)
-- Putmsg(" value ")
-- Print_expr(V)
-- Putmsg(" type ")
-- Print_type(T)
-- Putmsg(" condition ")
-- Print_expr(Pred)
-- Putnl()
	     Simplify(Pred -> Pred1)
	     (|
	       ne(Pred1, no_val)
               Get_defined_alias(T -> TS)
	       Overload_pos_id_or_op(Pos, id_op(Z) -> Z1)
	       Id_to_SML_id(Z1, nil -> ZS)
	       WriteFFile("let val %s = ", ZS)
	       Emit_value_expr(V)
	       WriteFile(" in if not(")
	       Emit_value_expr(Pred1)
	       PosAsString(Pos -> PS)
	       WriteF3File(") then (RSL.add_load_err(\"%s Value \" ^ %s.toString(%s) ^ ", PS, TS, ZS)
	       Binding_to_string(B -> BS)
	       WriteF3File("\" of %s not in subtype\"); %s) else %s end", BS, ZS, ZS)
	     ||
	       Emit_value_expr(V)
	     |)	   
           ||
             Not_support(pos(Pos), "multiple typing")
           |)
         ||
           where(VD -> imp_val(Pos, _, _))
           Not_support(pos(Pos), "underspecified value")
         ||
           where(VD -> exp_fun(_, TG, _, _, _, _, Reg))
           where(TG -> single(_, B, _))
           Get_resolved_exp_fun_def(TG -> T, Def)
           where(B -> single(Pos, Id))
	   Emit_expl_fun_def(Pos, N, T, Id, Def, Reg)
         ||
           where(VD -> imp_fun(Pos, _, _, _, _))
           Not_support(pos(Pos), "implicit function")
         |)

'action' Emit_subtype_fun(INT, Value_id)

  'rule' Emit_subtype_fun(N, I):
	 I'Pos -> P
	 I'Type -> T
	 I'Ident -> Id
	 I'Def -> Def
	 Emit_expl_fun_def(P, N, T, Id, Def, region(P,P))

'action' Emit_expl_fun_def(POS, INT, TYPE_EXPR, ID_OR_OP, VALUE_DEFINITION, REGION)

  'rule' Emit_expl_fun_def(P, N, T, Id, expl_fun(ParamL, V, Post, Pre, Cond, PCond), Reg:region(PB, PE)):
	 [|
	   ne(PB, PE) -- exclude subtype functions
	   Add_region(Reg)
	 |]
	 (|
	   eq(N, 0)
	   WriteFile("fun ")
	 ||
	   WriteFile("and ")
	 |)
	 Id_or_op_to_alpha_string(Id -> FS)
	 Overload_pos_id_or_op(P, Id -> Id1)
	 Id_to_SML_id(Id1, nil -> FS1)
	 WriteFFile("%s ", FS1)
	 Emit_curried_parameter_list(0, ParamL)
	 WriteFile("= (")
	 [|
	   ne(PB, PE) -- exclude subtype functions
	   Emit_cancel(PB)
	   WriteFile("; ")
	 |]
	 PosAsString(P -> PS)
	 [|
	   where(Cond -> condition(CV))
	   WriteFile("if not(")
	   Emit_value_expr(CV)
	   WriteF2File(") then raise RSL.RSL_exception (\"%s Argument of %s\" ^ ", PS, FS)
	   Emit_parameters_as_string(ParamL, T)
	   WriteFile(" ^ \" not in subtype\") else ")
	 |]
	 [|
	   where(Pre -> pre_cond(PPos, V1))
	   WriteFile("if not(")
	   Emit_value_expr(V1)
	   PosAsString(PPos -> PPS)
	   WriteF2File(") then raise RSL.RSL_exception (\"%s Precondition of %s\" ^ ", PPS, FS)
	   Emit_parameters_as_string(ParamL, T)
	   WriteFile(" ^ \" not satisfied\") else ")
	 |]
	 (|
	   (| where(PCond -> condition(_)) ||
	      where(Post -> post(_)) |)
	   Pos_to_string(P -> PST)
	   WriteFFile("let val RSL_res_'%s_ = ", PST)
	   Emit_value_expr(V)
	   WriteFile(" in ")
	   where(T -> fun(_, _, result(RT,_,_,_,_)))
	   Get_defined_alias(RT -> SRT)
	   [|
	     where(PCond -> condition(PCV))
	     WriteFile("if not(")
	     Emit_value_expr(PCV)
	     WriteFFile(") then raise RSL.RSL_exception (\"%s Result \" ^ ", PS)
	     WriteF2File("%s.toString RSL_res_'%s_", SRT, PST)
	     WriteFFile(" ^ \" of %s\" ^ ", FS)
	     Emit_parameters_as_string(ParamL, T)
	     WriteFile(" ^ \" not in subtype\") else ")
	   |]
	   [|
	     where(Post -> post(post_cond(_, RB, PC)))
	     WriteFile("if not(")
	     (|
	       where(RB -> result(_, Bind))
	       WriteFile("let val ")
               Overload_binding(Bind -> Bind1)
	       Emit_binding(Bind1)
               WriteFFile(" = RSL_res_'%s_ in ", PST)
	       Emit_value_expr(PC)
	       WriteFile(" end")
	     ||
	       Emit_value_expr(PC)
	     |)
	     WriteFFile(") then raise RSL.RSL_exception (\"%s Result \" ^ ", PS)  
	     WriteF2File("%s.toString RSL_res_'%s_", SRT, PST)
	     WriteFFile(" ^ \" of %s\" ^ ", FS)
	     Emit_parameters_as_string(ParamL, T)
	     WriteFile(" ^ \" does not satisfy postcondition\") else ")
	   |]
	   WriteFFile("RSL_res_'%s_ end", PST)
	 ||
	   Emit_value_expr(V)
	 |)
	 WriteFile(")")

'action' Emit_variable_def(VARIABLE_DEF)

  'rule' Emit_variable_def(VarD):
         (|
           where(VarD -> single(_, Id, _, _))
           Get_current_variables(-> VARS)
           Lookup_env_variable_id(Id, nil, VARS -> variable_id(VarI))
           VarI'Type -> T
           VarI'Init -> Ini
           VarI'Pos -> P
           Id_to_SML_id(Id, nil -> S)
           Get_defined_alias(T -> TS)
           (|
             where(Ini -> nil)
             Not_support(pos(P), "uninitialised variable")
--           WriteF3File("val %s: %s.t ref = ref %s.defval;", S, TS, TS)
--           WritelnFile(1)
           ||
             where(Ini -> initial(V))
             WriteF2File("val %s: %s.t ref = ref (", S, TS)
	     (|
	       VarI'Subtype -> condition(Fn)
	       string_to_id("z__" -> Z)
	       New_value_id(P, id_op(Z) -> I)
	       I'Type <- T
	       Overload_pos_id_or_op(P, id_op(Z) -> Z1)
	       Id_to_SML_id(Z1, nil -> ZS)
	       WriteFFile("let val %s = ", ZS)
	       Emit_value_expr(V)
	       WriteFile(" in if not(")
	       where(fun_arg(P,list(val_occ(P,I,nil),nil)) -> Arg)
	       Emit_value_expr(application(P, Fn, list(Arg,nil)))
	       PosAsString(P -> PS)
	       SML_id_to_string(Id -> VS)
	       WriteF3File(") then (RSL.add_load_err(\"%s Initial value \" ^ %s.toString(%s) ^ ", PS, TS, ZS)
	       WriteF3File("\" of %s not in subtype\"); %s) else %s end", VS, ZS, ZS)
	     ||
	       Emit_value_expr(V)
	     |)	   
             WriteFile(");")
           |)
           WritelnFile(1)
         ||
           where(VarD -> multiple(P, Ids, T))
           -- multiple variables are not initialised
           Not_support(pos(P), "multiple variables")
--         (|
--           where(Ids -> list(Id1, Tail))
--           Emit_variable_def(single(P, Id1, T, nil))
--           Emit_variable_def(multiple(P, Tail, T))
--         ||
--           where(Ids -> nil)
--         |)
         |)

'action' Emit_test_cases(STRING)

  'rule' Emit_test_cases(S):
         -- open top level structure
         -- as test cases will refer to entities within it
         WriteFFile("open %s;", S)
         WritelnFile(2)
         Get_current_test_cases(top -> VE)
         Emit_test_cases_env(S, VE)
	 WriteFile("RSL.print_error_count();\n")
	 WriteFile("R_coverage.save_marked();\n")

'action' Emit_test_cases_env(STRING, TEST_CASE_ENV)

  'rule' Emit_test_cases_env(S, TCE):
         (|
           where(TCE -> test_case_env(I, Tail))
           Emit_test_cases_env(S, Tail)
           I'Test_case -> V
           I'Type -> T
	   I'Paths -> Paths
	   Extend_paths -> Save_paths
	   Extend_paths <- Paths
           Get_defined_alias(T -> ST)
           LParen
           (|
             I'Ident -> ident(Id)
             SML_id_to_string(Id -> S1)
             WriteF2File("RSL.C_output \"[%s] \" %s.toStringSafe ", S1, ST)
           ||
             WriteFFile("RSL.C_output \"\" %s.toStringSafe ", ST)
           |)  
           LParen
           WriteFile("fn _ => ")
           Emit_value_expr(V)
           RParen
           RParen
           WriteFile(";")
           WritelnFile(2)
	   Extend_paths <- Save_paths
         ||
           where(TCE -> nil)
	   WriteFile("RSL.print_load_errs();\n")
	   WriteFile("RSL.set_time();\n")
	   WriteFile("R_coverage.init();\n")
	   Mark_regions()
	 |)

---------------------------------------------------

'action' Emit_value_literal_expr(VALUE_LITERAL)

  'rule' Emit_value_literal_expr(L):
         (|
           where(L -> unit)
           WriteFile("()")
         ||
           where(L -> bool_true)
           WriteFile("true")
         ||
           where(L -> bool_false)
           WriteFile("false")
         ||
           where(L -> int(Id))
           id_to_string(Id -> S)
           WriteFFile("RT_Int.fromLit \"%s\"", S)
         ||
           where(L -> real(Id))
           id_to_string(Id -> S)
           WriteFFile("RT_Real.fromLit \"%s\"", S)
         ||
           where(L -> text(S1))
           String_to_SML_string(S1 -> S) 
           WriteFFile("RT_Text.fromLit \"%s\"", S)
         ||
           where(L -> char(C))
           Char_to_SML_char(C -> S)
           WriteFFile("#\"%s\"", S)
         |)

'action' Emit_value_comma_delimited_list(VALUE_EXPRS)

  'rule' Emit_value_comma_delimited_list(VL):
         (|
           where(VL -> list(V, Tail))
           Emit_value_expr(V)
           [|
             where(Tail -> list(_, _))
             WriteFile(", ")
           |]
           Emit_value_comma_delimited_list(Tail)
         ||
           where(VL -> nil)
         |)

'action' Emit_value_product(VALUE_EXPRS)

  'rule' Emit_value_product(VL):
         LParen
         Emit_value_comma_delimited_list(VL)
         RParen

'action' Emit_value_ranged_set(VALUE_EXPR, VALUE_EXPR)

  'rule' Emit_value_ranged_set(V1, V2):
--       Value_to_type(V1 -> T1)
--       (|
--         (| where(T1 -> int) || where(T1 -> nat) |)
--         WriteFile("R'a_Set.uptoInt (")
--       ||
--         where(T1 -> char)
--         WriteFile("R'a_Set.uptoChar (")
--       |)
         WriteFile("R'a_Set.uptoInt (")
         Emit_value_comma_delimited_list(list(V1, list(V2, nil)))
         RParen

'action' Emit_value_enum_set(VALUE_EXPR)

  'rule' Emit_value_enum_set(V):
         Value_to_type(V -> T)
         Get_defined_alias(T -> S)
         where(V -> enum_set(_, VL))
         WriteFFile("%s.R_fromList (", S)
         Emit_value_enum_list(VL)
         RParen 

'action' Emit_value_empty_set(TYPE_EXPR)

  'rule' Emit_value_empty_set(T)
         Get_defined_alias(T -> S)
         WriteFFile("%s.R_fromList []", S)

'action' Emit_value_enum_list(VALUE_EXPRS)
   
  'rule' Emit_value_enum_list(VL):
         WriteFile("[")
         Emit_value_comma_delimited_list(VL)
         WriteFile("]")

'action' Emit_value_empty_list(TYPE_EXPR)

  'rule' Emit_value_empty_list(T):
         Get_defined_alias(T -> S)
         WriteFFile("([]:%s.t)", S)

'action' Emit_value_ranged_list(VALUE_EXPR, VALUE_EXPR)

  'rule' Emit_value_ranged_list(V1, V2):
--       Value_to_type(V1 -> T1)
--       (|
--         (| where(T1 -> int) || where(T1 -> nat) |)
--         WriteFile("R'a_List.uptoInt(")
--       ||
--         where(T1 -> char)
--         WriteFile("R'a_List.uptoChar(")
--       |)
         WriteFile("R'a_List.uptoInt(")
         Emit_value_comma_delimited_list(list(V1, list(V2, nil)))
         RParen

'action' Emit_value_comma_delimited_pair_list(VALUE_EXPR_PAIRS)

  'rule' Emit_value_comma_delimited_pair_list(VPL):
         (|
           where(VPL -> list(VP, Tail))
           where(VP -> pair(V1, V2))
           LParen
           Emit_value_comma_delimited_list(list(V1, list(V2, nil)))
           RParen
           [|
             where(Tail -> list(_, _))
             WriteFile(", ")
           |]
           Emit_value_comma_delimited_pair_list(Tail)
         ||
           where(VPL -> nil)
         |)

'action' Emit_value_enum_map(VALUE_EXPR)

  'rule' Emit_value_enum_map(V):
         Value_to_type(V -> T)
         Get_defined_alias(T -> S)
         where(V -> enum_map(_, VPL))
         WriteFFile("%s.R_fromList ([", S)
         Emit_value_comma_delimited_pair_list(VPL)
         WriteFile("])") 

'action' Emit_value_empty_map(TYPE_EXPR)

  'rule' Emit_value_empty_map(T)
         Get_defined_alias(T -> S)
         WriteFFile("%s.R_fromList []", S)

'action' Emit_binding(BINDING)

  'rule' Emit_binding(B):
         (|
           where(B -> single(_, Id))
           Id_or_op_to_SML_id(Id, nil -> S)
           WriteFile(S)
         ||
           where(B -> product(_, BL))
           LParen
           Emit_binding_list(BL)
           RParen
         |)

'action' Emit_binding_list(BINDINGS)

  'rule' Emit_binding_list(BL):
         (|
           where(BL -> list(B, Tail))
           Emit_binding(B)
           [|
             where(Tail -> list(_, _))
             WriteFile(", ")
           |]
           Emit_binding_list(Tail)
         ||
           where(BL -> nil)
         |)

'action' Emit_comma_delimited_typing(TYPING)

  'rule' Emit_comma_delimited_typing(TG):
         (|
           where(TG -> single(_, B, T))
           Overload_binding(B -> B1)
           Emit_binding(B1)
           WriteFile(":")
           Get_defined_alias(T -> S)
           WriteFFile("%s.t", S)
         ||
           where(TG -> multiple(Pos, BL, T))
           (|
             where(BL -> list(B, Tail))
             Emit_comma_delimited_typing(single(Pos, B, T))
             [|
               where(Tail -> list(_, _))
               WriteFile(", ")
             |]
             Emit_comma_delimited_typing(multiple(Pos, Tail, T))
           ||
             where(BL -> nil)
           |)
         |)

'action' Emit_comma_delimited_typing_list(TYPINGS)

  'rule' Emit_comma_delimited_typing_list(TGL):
         (|
           where(TGL -> list(TG, Tail))
           Emit_comma_delimited_typing(TG)
           [|
             where(Tail -> list(_, _))
             WriteFile(", ")
           |]
           Emit_comma_delimited_typing_list(Tail)
         ||
           where(TGL -> nil)
         |)

'action' Emit_lambda_parameter(LAMBDA_PARAMETER)

  'rule' Emit_lambda_parameter(LE):
         WriteFile("fn (")
         (|
           where(LE -> l_typing(_, TGL))
           Emit_comma_delimited_typing_list(TGL)
         ||
           where(LE -> s_typing(_, TG))
           Emit_comma_delimited_typing(TG)
         |)
         RParen

'action' Emit_application_function(VALUE_EXPR, ACTUAL_FUNCTION_PARAMETERS)

  'rule' Emit_application_function(V, ArgL):
         LParen
         (|
           where(ArgL -> list(Arg, Tail))
           Emit_application_function(V, Tail)
         ||
           where(ArgL -> nil)
           Value_to_type(V -> T)
           (|
             (| Type_matches_map(T) || Type_matches_list(T) || Type_matches_text(T) |)
             Lookup_defined_alias(T -> S)
             WriteFFile("%s.R_app", S)
             LParen
             Emit_value_expr(V)
             RParen
           ||
             Emit_value_expr(V)
           |)
           RParen
         |)

'action' Emit_application_arg_list(ACTUAL_FUNCTION_PARAMETERS)

  'rule' Emit_application_arg_list(ArgL):
         (|
           where(ArgL -> list(Arg, Tail))
           where(Arg -> fun_arg(_, VL))
           WriteFile(" (")
           Emit_value_comma_delimited_list(VL)
           WriteFile("))")
           Emit_application_arg_list(Tail)
         ||
           where(ArgL -> nil)
         |)

'condition' Emit_implicit_let_def(TYPING, RESTRICTION)

  'rule' Emit_implicit_let_def(TG, R):
         Split_typing(TG -> B, TT)
         Split_restriction(exists, R, B, TT -> SLM, T, Pred)
         Get_defined_alias(T -> TS)
         Overload_binding(B -> B1)
         Emit_binding(B1)
         WriteFFile(" = (%s.R_choose (fn ", TS)
         Emit_binding(B1)
         WriteFile(" => ")
         Emit_value_expr(Pred)
         WriteFile(") (")
         Emit_value_expr(SLM)
         WriteFile("))")

'condition' Emit_value_comp_set(VALUE_EXPR, TYPINGS, RESTRICTION)

  'rule' Emit_value_comp_set(V, TGL, R):
         where(TGL -> list(TG, nil))
         Split_typing(TG -> B, TT)
         Split_restriction(exists, R, B, TT -> SLM, T, Pred)
         (|
           Type_matches_set(T)
           where("R_compss" -> FS)
         ||
           (| Type_matches_list(T) || Type_matches_text(T) |)
           where("R_compls" -> FS)
         ||
           Type_matches_map(T)
           where("R_compms" -> FS)
         |)
         Value_to_type(V -> T1)
         Get_defined_alias(fin_set(T1) -> TS1)
         Overload_binding(B -> B1)
         WriteF2File("(%s.%s (fn (", TS1, FS)
         Emit_binding(B1)
	 Get_defined_alias(TT -> TTS)
	 WriteFFile(":%s.t) => ", TTS)
         Emit_value_expr(V)
         WriteFile(") (fn (")
         Emit_binding(B1)
	 WriteFFile(":%s.t) => ", TTS)
         Emit_value_expr(Pred)
         WriteFile(") (")
         Emit_value_expr(SLM)
         WriteFile("))")
         
'condition' Emit_value_comp_list(VALUE_EXPR, BINDING, VALUE_EXPR, RESTRICTION)

  'rule' Emit_value_comp_list(V, B, VL, R):
         (|
           where(R -> nil)
           DefaultPos(-> Pos)
           where(literal_expr(Pos, bool_true) -> Pred)
         ||
           where(R -> restriction(_, Pred))
         |)
         Value_to_type(V -> T1)
         Get_defined_alias(fin_list(T1) -> TS1)
         Overload_binding(B -> B1)
         WriteFFile("(%s.R_compll (fn (", TS1)
         Emit_binding(B1)
	 Value_to_type(VL -> TL)
	 Type_is_list(TL -> TT)
	 Get_defined_alias(TT -> TTS)
	 WriteFFile(":%s.t) => ", TTS)
         Emit_value_expr(V)
         WriteFile(") (fn (")
         Emit_binding(B1)
	 WriteFFile(":%s.t) => ", TTS)
         Emit_value_expr(Pred)
         WriteFile(") (")
         Emit_value_expr(VL)
         WriteFile("))")

'condition' Emit_value_comp_map(VALUE_EXPR_PAIR, TYPINGS, RESTRICTION)

  'rule' Emit_value_comp_map(pair(LV, RV), TGL, R):
         where(TGL -> list(TG, nil))
         Split_typing(TG -> B, TT)
         Split_restriction(exists, R, B, TT -> SLM, T, Pred)
         (|
           Type_matches_set(T)
           where("R_compsm" -> FS)
         ||
           (| Type_matches_list(T) || Type_matches_text(T) |)
           where("R_complm" -> FS)
         ||
           Type_matches_map(T)
           where("R_compmm" -> FS)
         |)
         Value_to_type(LV -> LT)
         Value_to_type(RV -> RT)
         Get_defined_alias(fin_map(LT, RT) -> TS1)
         Overload_binding(B -> B1)
         WriteF2File("(%s.%s (fn (", TS1, FS)
         Emit_binding(B1)
	 Get_defined_alias(TT -> TTS)
	 WriteFFile(":%s.t) => (", TTS)
         Emit_value_expr(LV)
         WriteFile(", ")
         Emit_value_expr(RV)
         WriteFile(")) (fn (")
         Emit_binding(B1)
	 WriteFFile(":%s.t) => ", TTS)
         Emit_value_expr(Pred)
         WriteFile(") (")
         Emit_value_expr(SLM)
         WriteFile("))")

'condition' Emit_value_quantified(QUANTIFIER, TYPINGS, RESTRICTION)

  'rule' Emit_value_quantified(Q, TGL, R):
         where(TGL -> list(TG, nil))
         Split_typing(TG -> B, TT)
         Split_restriction(Q, R, B, TT -> SLM, T, Pred)
         Get_defined_alias(T -> TS)
         (|
           where(Q -> all)
           where("R_all" -> QS)
         ||
           where(Q -> exists)
           where("R_exists" -> QS)
         ||
           where(Q -> exists1)
           where("R_exists1" -> QS)
         |)
         WriteF2File("(%s.%s (fn (", TS,  QS)
         Overload_binding(B -> B1)
         Emit_binding(B1)
	 Get_defined_alias(TT -> TTS)
	 WriteFFile(":%s.t) => ", TTS)
         Emit_value_expr(Pred)
         WriteFile(") (")
         Emit_value_expr(SLM)
         WriteFile("))")

'action' Split_typing(TYPING -> BINDING, TYPE_EXPR)

  'rule' Split_typing(TG -> B, T)
         (|
           where(TG -> single(_, B, T))
         ||
           where(TG -> multiple(Pos, BL, T))
           where(BINDING'product(Pos, BL) -> B)
         |)

'condition' Split_restriction(QUANTIFIER, RESTRICTION, BINDING, TYPE_EXPR -> VALUE_EXPR, TYPE_EXPR, VALUE_EXPR)

  'rule' Split_restriction(Q, restriction(Pos,V), B, TT -> SLM, T, Pred):
         (|
           where(Q -> all)
           (|
             where(V -> ax_infix(_, L0, implies, Pred0, _))
	     (|
	       -- change A /\ B => C to A => B => C
	       Split_conjunct(L0 -> L, L01)
	       where(ax_infix(Pos, L01, implies, Pred0, Pos) -> Pred1)
	     ||
	       where(L0 -> L)
	       where(Pred0 -> Pred1)
	     |)
           ||
             where(V -> L)
             where(literal_expr(Pos, bool_true) -> Pred1)
           |) 
         ||  -- exists or exists1
           (|
             where(V -> ax_infix(_, L, and, Pred1, _))
           ||
             where(V -> L)
             where(literal_expr(Pos, bool_true) -> Pred1)
           |)
         |)
         where(L -> infix_occ(_, L1, I, nil, SLM0))
         Matches_binding(L1, B)
         I'Ident -> Id
         where(Id -> op_op(isin))
         Built_in(isin, I)
	 (| -- check for isin dom, isin elems
	   Dom_or_elems(SLM0 -> SLM)
	 ||
	   where(SLM0 -> SLM)
	 |)
         Value_to_type(SLM -> T)
	 -- general subtype checking now included
--	 Check_subtypes(TT, nil -> nil)
         Maxtype(TT -> TTm)
         Express_binding(B, TTm -> L11)
         Isin_subtype(L11, TT -> Pred2)
	 Simplify(Pred2 -> Pred2s)
         (|
           where(Pred2s -> no_val)
           where(Pred1 -> Pred)
         ||
           (|
             where(Q -> all)
             where(ax_infix(Pos, Pred2s, implies, Pred1, Pos) -> Pred3)
	   ||
             where(ax_infix(Pos, Pred2s, and, Pred1, Pos) -> Pred3) 
           |)
           Simplify(Pred3 -> Pred)
         |)

'condition' Dom_or_elems(VALUE_EXPR -> VALUE_EXPR)

  'rule' Dom_or_elems(prefix_occ(_, I, nil, V) -> V):
	 I'Ident -> op_op(Op)
	 Built_in(Op, I)
	 (| eq(Op, dom) || eq(Op, elems) |)

  'rule' Dom_or_elems(bracket(_, V) -> V1):
	 Dom_or_elems(V -> V1)

  'rule' Dom_or_elems(disamb(P, V, T) -> disamb(P, V1, T)):
	 Dom_or_elems(V -> V1) 

'condition' Split_conjunct(VALUE_EXPR -> VALUE_EXPR, VALUE_EXPR)

  'rule' Split_conjunct(V -> V1, V2):
	 (|
	   where(V -> ax_infix(_, V1, and, V2, _))
	 ||
	   where(V -> bracket(_, V0))
	   Split_conjunct(V0 -> V1, V2)
	 |) 

'sweep' Check_subtypes(ANY, FOUND -> FOUND)

  'rule' Check_subtypes(subtype(_,_), _ -> found):

  'rule' Check_subtypes(defined(I, _), _ -> found):
	 I'Def -> abbreviation(T)
	 Check_subtypes(T, nil -> found)

'condition' Matches_binding(VALUE_EXPR, BINDING)

  'rule' Matches_binding(disamb(_, V, _), B):
	 Matches_binding(V, B)

  'rule' Matches_binding(bracket(_, V), B):
	 Matches_binding(V, B)

  'rule' Matches_binding(V, B):
         (|
           where(B -> single(P, Id))
           where(V -> val_occ(_, I, _))
           I'Pos -> P0
	   eq(P, P0)
         ||
           where(B -> product(_, BL))
           where(V -> product(_, VS))
           Matches_product_binding(VS, BL)
         |)

'condition' Matches_product_binding(VALUE_EXPRS, BINDINGS)

  'rule' Matches_product_binding(list(V, VL), list(B, BL)):
         Matches_binding(V, B)
         Matches_product_binding(VL, BL)

  'rule' Matches_product_binding(nil, nil):

'condition' Express_binding(BINDING, TYPE_EXPR -> VALUE_EXPR)

  'rule' Express_binding(B, T -> V):
         (|
           where(B -> single(Pos, Id))
           New_value_id(Pos, Id -> I)
           I'Type <- T
	   [|
	     CPPWanted()
	     where(Id -> id_op(Id1))
	     Localise_id(Pos, Id1 -> Id2)
	     I'Ident <- id_op(Id2)
	   |]
           where(val_occ(Pos, I, nil) -> V)
         ||
           where(B -> product(Pos, BL))
	   Type_is_product(T -> TL)
           Express_product_binding(BL, TL -> VL)
           where(VALUE_EXPR'product(Pos, VL) -> V)
         |)

'condition' Express_product_binding(BINDINGS, PRODUCT_TYPE -> VALUE_EXPRS)

  'rule' Express_product_binding(list(B, BL), list(T, TL) -> list(V, VL)):
         Express_binding(B, T -> V)
         Express_product_binding(BL, TL -> VL)

  'rule' Express_product_binding(nil, nil -> nil):

'action' Emit_value_post(VALUE_EXPR, POST_CONDITION, PRE_CONDITION)

  'rule' Emit_value_post(V, Post, Pre):
         where(Pre -> pre_cond(_, V1))
         WriteFile("if ")
         Emit_value_expr(V1)
         WriteFile(" then ")
         where(Post -> post_cond(_, result(_, B), V2))
         WriteFile("let val ")
         Overload_binding(B -> B1)
         Emit_binding(B1)
         WriteFile(" = ")
         Emit_value_expr(V)
         WriteFile(" in if ")
         Emit_value_expr(V2)
         WriteFile(" then ")
         Emit_binding(B1)
         WriteFile(" else raise RSL.RSL_exception \"Postcondition not satisfied\" end")
         WriteFile(" else raise RSL.RSL_exception(\"Precondition not satisfied\"")

'action' Emit_value_ax_infix(POS, VALUE_EXPR, CONNECTIVE, VALUE_EXPR, POS)

  'rule' Emit_value_ax_infix(PB, V1, Conn, V2, PE):
         (|
           where(Conn -> implies)
           WriteFile("not (")
           Emit_value_expr(V1)
           WriteFile(") orelse (")
         ||
           where(Conn -> or)
           LParen
           Emit_value_expr(V1)
           WriteFile(") orelse (")
         ||
           where(Conn -> and)
           LParen
           Emit_value_expr(V1)
           WriteFile(") andalso (")
         |)
	 [|  -- generated axiom infixes
	     -- (preconditions of built in functions,
	     --  confidence conditions, etc)
	     -- set the two positions the same
	   ne(PB, PE)
	   Emit_cancel(PB)
	   WriteFile("; ")
	 |]
	 Emit_value_expr(V2)
	 RParen

'action' Get_abbrev_type(TYPE_EXPR -> TYPE_EXPR)

  'rule' Get_abbrev_type(T -> T1):
         (|
           where(T -> defined(I, Q))
           I'Def -> abbreviation(T2)
           Get_abbrev_type(T2 -> T1)
         ||
           where(T -> subtype(single(_,_,T2),_))
           Get_abbrev_type(T2 -> T1)
         ||
           where(T -> bracket(T2))
           Get_abbrev_type(T2 -> T1)
         ||
           where(T -> T1)
         |)

'condition' Type_matches_map(TYPE_EXPR)

  'rule' Type_matches_map(T):
         Type_is_map(T -> _, _)

'condition' Type_matches_set(TYPE_EXPR)

  'rule' Type_matches_set(T):
         Type_is_set(T -> _)

'condition' Type_matches_list(TYPE_EXPR)

  'rule' Type_matches_list(T):
         Type_is_list(T -> _)

'condition' Type_matches_text(TYPE_EXPR)

  'rule' Type_matches_text(T):
         Get_abbrev_type(T -> T1)
         (|
           where(T1 -> text)
         ||
           where(T1 -> fin_list(T2))
	   Get_abbrev_type(T2 -> char)
         ||
           where(T1 -> infin_list(T2))
	   Get_abbrev_type(T2 -> char)
         |)

'condition' Type_matches_int_or_nat(TYPE_EXPR)

  'rule' Type_matches_int_or_nat(T):
         Get_abbrev_type(T -> T1)
         (| 
           where(T1 -> int) 
         || 
           where(T1 -> nat)
         |)

'condition' Type_matches_real(TYPE_EXPR)

  'rule' Type_matches_real(T):
         Get_abbrev_type(T -> T1)
         where(T1 -> real) 

'action' Emit_value_op(OP, TYPE_EXPR, TYPE_OPTION)

  'rule' Emit_value_op(Op, T1, TO):
         Get_defined_alias(T1 -> S1)
         (|
           where(TO -> some(T2))
           Get_defined_alias(T2 -> S2)
         ||
           where(TO -> none)
           where("" -> S2)
         |)
         ---- infix
         (|
           where(Op -> eq)
           WriteFFile("%s.equ", S1)
         ||
           where(Op -> neq)
           WriteFFile("(RSL.C_not %s.equ)", S1)
         ||
           where(Op -> gt)
           WriteFFile("%s.R_gt", S1)
         ||
           where(Op -> lt)
           WriteFFile("%s.R_lt", S1)
         ||
           where(Op -> ge)
           WriteFFile("%s.R_ge", S1)
         ||
           where(Op -> le)
           WriteFFile("%s.R_le", S1)
         ||
           where(Op -> supset)
           WriteFFile("%s.R_supspro", S1)
         ||
           where(Op -> subset)
           WriteFFile("%s.R_subspro", S1)
         ||
           where(Op -> supseteq)
           WriteFFile("%s.R_sups", S1)
         ||
           where(Op -> subseteq)
           WriteFFile("%s.R_subs", S1)
         ||
           where(Op -> isin)
           WriteFFile("%s.R_mem", S2)
         ||
           where(Op -> notisin)
           WriteFFile("(RSL.C_not %s.R_mem)", S2)
         ||
           where(Op -> rem)
           (|
             Type_matches_map(T1)
             WriteFFile("%s.R_restrBySet", S1)
           ||
             Type_matches_set(T1)
             WriteFFile("%s.R_diff", S1)
           ||
             WriteFFile("%s.R_mod", S1)
           |)
         ||
           where(Op -> union)
           WriteFFile("%s.R_union", S1)
         ||
           where(Op -> override)
           WriteFFile("%s.R_override", S1)
         ||
           where(Op -> mult)
           WriteFFile("%s.R_mul", S1)
         ||
           where(Op -> div)
           (|
             Type_matches_map(T1)
             WriteFFile("%s.R_restrToSet", S1)
           ||
             WriteFFile("%s.R_div", S1)
           |)
         ||
           where(Op -> hash)
           (|
             Type_matches_map(T1)
             WriteFFile("%s.R_compose", S1)
           ||
             WriteFile("(op o)")
           |)
         ||
           where(Op -> inter)
           WriteFFile("%s.R_inter", S1)
         ||
           where(Op -> exp)
           WriteFFile("%s.R_exp", S1)
         ||
           where(Op -> plus)
           (|
             where(TO -> none)
             -- ignore
             -- WriteFFile("(RSL.C_output %s.toString)", S1)
           ||
             WriteFFile("%s.R_add", S1)
           |)
         ||
           where(Op -> minus)
           (|
             where(TO -> some(_))
             WriteFFile("%s.R_sub", S1)
           ||
             WriteFFile("%s.R_neg", S1)
           |)
         ||
         ---- prefix
           where(Op -> abs)
           WriteFFile("%s.R_abs", S1)
         ||
           where(Op -> int)
           WriteFFile("%s.R_int", S1)
         ||
           where(Op -> real)
           WriteFFile("%s.R_real", S1)
         ||
           where(Op -> card)
           WriteFFile("%s.R_card", S1)
         ||
           where(Op -> len)
           WriteFFile("%s.R_length", S1)
         ||
           where(Op -> inds)
           WriteFFile("%s.R_inds", S1)
         ||
           where(Op -> elems)
           WriteFFile("%s.R_elems", S1)
         ||
           where(Op -> hd)
           WriteFFile("%s.R_hd", S1)
         ||
           where(Op -> tl)
           WriteFFile("%s.R_tl", S1)
         ||
           where(Op -> caret)
           WriteFFile("%s.R_concat", S1)
         ||
           where(Op -> dom)
           WriteFFile("%s.R_dom", S1)
         ||
           where(Op -> rng)
           WriteFFile("%s.R_ran", S1)
         ||
           print(Op)
           False_cond
         |)

'action' Emit_value_op_as_fun(OP, TYPE_EXPR)

  'rule' Emit_value_op_as_fun(Op, FT):
         where(FT -> fun(T, _, _))
         (|
           where(T -> product(list(T1, list(T2, nil))))
           Emit_value_op(Op, T1, some(T2))
         ||
           Emit_value_op(Op, T, none)
         |)        

'action' Emit_value_val_infix(VALUE_EXPR, OP, Value_id, VALUE_EXPR)

-- translate <.e.>^l as (e)::(l)
  'rule' Emit_value_val_infix(enum_list(_, list(V1, nil)), InOp, I, V2):
	 eq(InOp, caret)
	 Built_in(InOp, I)
	 LParen
	 Emit_value_expr(V1)
	 WriteFile(")::(")
         Emit_value_expr(V2)
	 RParen

  'rule' Emit_value_val_infix(V1, InOp, _, V2):
         Value_to_type(V1 -> T1)
         Value_to_type(V2 -> T2)
         Emit_value_op(InOp, T1, some(T2))
         WriteFile(" (")
         Emit_value_expr(V1)
         WriteFile(", ")
         Emit_value_expr(V2)
         RParen

'action' Emit_value_ax_prefix(CONNECTIVE, VALUE_EXPR)

  'rule' Emit_value_ax_prefix(Conn, V):
         where(Conn -> not)
         WriteFile("not (")
         Emit_value_expr(V)
         RParen
         
'action' Emit_value_val_prefix(OP, VALUE_EXPR)

  'rule' Emit_value_val_prefix(PreOp, V):
         Value_to_type(V -> T)
         Emit_value_op(PreOp, T, none)
         LParen
         Emit_value_expr(V)
         RParen

'action' Emit_value_assignment(NAME, VALUE_EXPR)

  'rule' Emit_value_assignment(Na, V):
         where(Na -> name(_, id_op(Id)))
         Id_to_SML_id(Id, nil -> S)
         WriteFFile("%s := ", S)
         Emit_value_expr(V)

'action' Emit_value_local_expr(DECLS, VALUE_EXPR)

  'rule' Emit_value_local_expr(DL, V):
         Open_local_decls(DL -> Paths)
         WriteFile("let")
         WritelnFile(1)
         IndentFile
         Emit_declares(DL)
         UnindentFile
         WriteFile("in")
         WritelnFile(1)
         IndentFile
         Emit_value_expr(V)
         WritelnFile(1)
         UnindentFile
         WriteFile("end")
         Close_local_decls(Paths)

'action' Emit_value_env_local(DECLS, CLASS_ENV, VALUE_EXPR)

  'rule' Emit_value_env_local(DL, CE, V):
         Open_local_env(CE -> Paths)
         WriteFile("let")
         WritelnFile(1)
         IndentFile
         Emit_declares(DL)
         UnindentFile
         WriteFile("in")
         WritelnFile(1)
         IndentFile
         Emit_value_expr(V)
         WritelnFile(1)
         UnindentFile
         WriteFile("end")
         Close_local_env(Paths)

'action' Emit_value_let_expr(LET_DEFS, VALUE_EXPR)

  'rule' Emit_value_let_expr(LDL, V):
         WriteFile("let")
         WritelnFile(1)
         IndentFile
         Emit_let_def_list(LDL)
         WritelnFile(1)
         UnindentFile
         WriteFile("in")
         WritelnFile(1)
         IndentFile
         Emit_value_expr(V)
         WritelnFile(1)
         UnindentFile
         WriteFile("end")        
         
'action' Emit_elseif_branches(ELSIF_BRANCHES)

  'rule' Emit_elseif_branches(ELIF):
         (|
           where(ELIF -> list(elsif(PB, V1, V2, _), Tail))
           WriteFile(" else if ")
           Emit_value_expr(V1)
           WriteFile(" then (")
	   Emit_cancel(PB)
	   WriteFile("; ")
           Emit_value_expr(V2)
	   WriteFile(")")
           Emit_elseif_branches(Tail)
         ||
           where(ELIF -> nil)
         |)

'action' Emit_value_if_expr(POS, VALUE_EXPR, VALUE_EXPR, REGION, ELSIF_BRANCHES, ELSE_BRANCH)

  'rule' Emit_value_if_expr(P, V1, V2, RT, ELIF, EL):
	 Add_region(RT)
	 Add_elsif_regions(ELIF)
	 Add_else_region(P, EL)
         WriteFile("if ")
         Emit_value_expr(V1)
         WriteFile(" then (")
	 where(RT -> region(PTB, _))
	 Emit_cancel(PTB)
	 WriteFile("; ")
         Emit_value_expr(V2)
	 WriteFile(")")
         Emit_elseif_branches(ELIF)
         WriteFile(" else ")
         (|
           where(EL -> else(PEB, V3))
	   WriteFile("(")
	   Emit_cancel(PEB)
	   WriteFile("; ")
           Emit_value_expr(V3)
	   WriteFile(")")
         ||
           where(EL -> nil)
           DefaultPos(->Pos)
           Emit_value_expr(skip(Pos))
         |)

'action' Add_region(REGION)

  'rule' Add_region(R)
	 Var_regions -> RS
	 Var_regions <- list(R, RS)

'action' Mark_regions

  'rule' Mark_regions:
	 Var_regions -> RS
	 WriteFile("(")
	 Mark_regions1(RS)
	 WriteFile(");\n")


'action' Mark_regions1(REGIONS)

  'rule' Mark_regions1(list(R, RS)):
	 where(R -> region(PB, PE))
	 PosDecrypt(PB -> F, LB, CB)
	 PosDecrypt(PE -> _, LE, CE)
	 WriteF5File("R_coverage.mark(RT_Text.fromLit \"%s\", (%s, %s), (%s, %s))", F, LB, CB, LE, CE)
	 [|
	   ne(RS, nil)
	   WriteFile(";\n")
	   Mark_regions1(RS)
	 |]

  'rule' Mark_regions1(nil):

'action' Add_elsif_regions(ELSIF_BRANCHES)

  'rule' Add_elsif_regions(list(elsif(PB, _, _, PE), ELS)):
	 Add_region(region(PB, PE))
	 Add_elsif_regions(ELS)

  'rule' Add_elsif_regions(nil):


'action' Add_else_region(POS, ELSE_BRANCH)

  'rule' Add_else_region(PEE, else(PEB, _)):
	 Add_region(region(PEB, PEE))

  'rule' Add_else_region(_, nil):

'action' Add_case_regions(CASE_BRANCHES)

  'rule' Add_case_regions(list(case(PB,_,_,PE), PBL)):
	 Add_region(region(PB, PE))
	 Add_case_regions(PBL)

  'rule' Add_case_regions(nil):

'action' Emit_cancel(POS)

  'rule' Emit_cancel(P):
	 PosDecrypt(P -> F, L, C)
	 WriteF3File("R_coverage.cancel(RT_Text.fromLit \"%s\", (%s, %s))", F, L, C)

'action' Emit_value_case_expr(VALUE_EXPR, CASE_BRANCHES, INT)

  'rule' Emit_value_case_expr(V, CBL, N):
         (|
           where(CBL -> list(CB, Tail))
           where(CB -> case(Pos, P, V1, _))
           (|
             eq(N, 0)
             WriteFile("case ")
             Emit_value_expr(V)
             WriteFile(" of ")
           ||
             WriteFile(" | ")
           |)
	   Check_for_equality_pattern(Pos, P)
           Emit_pattern(P)
           WriteFile(" => (")
	   Emit_cancel(Pos)
	   WriteFile("; ")
           Emit_value_expr(V1)
	   WriteFile(")")
           Emit_value_case_expr(no_val, Tail, 1)
         ||
           where(CBL -> nil)
         |)

'action' Emit_value_case_as_if(POS, VALUE_EXPR, TYPE_EXPR, CASE_BRANCHES)

  'rule' Emit_value_case_as_if(P, V, T, list(case(PB, Patt, V1, _), Patts)):
	 Pattern_match(V, Patt -> C, DS)
	 Simplify(C -> C1)
	 (|
	   eq(C1, no_val)
	   WriteFile("(")
	   Emit_cancel(PB)
	   WriteFile("; ")
	   (|
	     eq(DS, nil)
	     Emit_value_expr(V1)
	   ||
	     Emit_value_expr(let_expr(P, DS, V1))
	   |)
	   WriteFile(")")
	 ||  
	   WriteFile("if ")
	   Emit_value_expr(C1)
	   WriteFile(" then (")
	   Emit_cancel(PB)
	   WriteFile("; ")
	   (|
	     eq(DS, nil)
	     Emit_value_expr(V1)
	   ||
	     Emit_value_expr(let_expr(P, DS, V1))
	   |)
	   WriteFile(") else ")
	   Emit_value_case_as_if(P, V, T, Patts)
	 |)
	 
  'rule' Emit_value_case_as_if(P, V, T, nil):
	 PosAsString(P -> PS)
	 Get_defined_alias(T -> TS)
	 WriteF2File("raise RSL.swap (\"%s Case incomplete for value \" ^ %s.toString(", PS, TS)
	 Emit_value_expr(V)
	 WriteFile("))")

'action' Check_for_equality_pattern(POS, PATTERN)
-- not stored as equality pattern but detected by presence
-- of name_pattern when main pattern is not a name_pattern
  'rule' Check_for_equality_pattern(P, Patt):
	 (|
	   where(Patt -> name_occ_pattern(_,_,_))
	 ||
	   [|
	     Find_name_occ_pattern(Patt, nil -> found)
	     Not_support(pos(P), "equality patterns")
	   |]
	 |)

'sweep' Find_name_occ_pattern(ANY, FOUND -> FOUND)

  'rule' Find_name_occ_pattern(name_occ_pattern(_,_,_), _ -> found):
           
'sweep' Find_record_occ_pattern(ANY, FOUND -> FOUND)

  'rule' Find_record_occ_pattern(record_occ_pattern(_,_,_,_), _ -> found):

'action' Emit_comma_delimited_pattern_list(PATTERNS)

  'rule' Emit_comma_delimited_pattern_list(PL):
         (|
           where(PL -> list(P, Tail))
           Emit_pattern(P)
           [|
             where(Tail -> list(_, _))
             WriteFile(", ")
           |]
           Emit_comma_delimited_pattern_list(Tail)
         ||
           where(PL -> nil)
         |)

'action' Emit_colon_delimited_pattern_list(PATTERNS)

  'rule' Emit_colon_delimited_pattern_list(PL):
         (|
           where(PL -> list(P, Tail))
           Emit_pattern(P)
           WriteFile("::")
           Emit_colon_delimited_pattern_list(Tail)
         ||
           where(PL -> nil)
         |)

'action' Check_literal_pattern(POS, VALUE_LITERAL)

  'rule' Check_literal_pattern(Pos, L):
         (|
           where(L -> int(_))
           Not_support(pos(Pos), "integer literal pattern")
         ||
           where(L -> real(_))
           Not_support(pos(Pos), "real literal pattern")
         ||
           where(L -> text(_))
           Not_support(pos(Pos), "text literal pattern")
         ||
         |)

'action' Emit_pattern(PATTERN)

  'rule' Emit_pattern(P):
         (|
           where(P -> literal_pattern(Pos, L))
           Check_literal_pattern(Pos, L)     
           Emit_value_literal_expr(L)
         ||
           where(P -> name_occ_pattern(_, VI, Q))
           Emit_value_val_occ(VI, Q)
         ||
           where(P -> record_occ_pattern(_, VI, Q, PL))
           Emit_value_val_occ(VI, Q)
           LParen
           Emit_comma_delimited_pattern_list(PL)
           RParen
         ||
           where(P -> id_pattern(Pos, Id))
           Overload_pos_id_or_op(Pos, Id -> Id1)
           Id_to_SML_id(Id1, nil -> S)
           WriteFile(S)
         ||
           where(P -> wildcard_pattern(_))
           WriteFile("_")
         ||
           where(P -> product_pattern(_, PL))
           LParen
           Emit_comma_delimited_pattern_list(PL)
           RParen
         ||
           where(P -> enum_list(_, PL))
           WriteFile("[")
           Emit_comma_delimited_pattern_list(PL)
           WriteFile("]")
         ||
           where(P -> conc_list(_, PL, P1))
           Emit_colon_delimited_pattern_list(PL)
           Emit_pattern(P1)
         |)

'action' Emit_value_while_expr(VALUE_EXPR, VALUE_EXPR)

  'rule' Emit_value_while_expr(V1, V2):
         WriteFile("while ")
         Emit_value_expr(V1)
         WriteFile(" do ")
         LParen
         Emit_value_expr(V2)
         RParen

'action' Emit_value_until_expr(VALUE_EXPR, VALUE_EXPR)
        
  'rule' Emit_value_until_expr(V1, V2):
         WriteFile("RSL.C_until ")
         LParen
         WriteFile("fn () => ")
         LParen
         Emit_value_expr(V1)
         RParen
         WriteFile(", ")
         WriteFile("fn () => ")
         LParen
         Emit_value_expr(V2)
         RParen
         RParen

'action' Emit_value_for_expr(LIST_LIMITATION, VALUE_EXPR)

  'rule' Emit_value_for_expr(Limit, V):
         where(Limit -> list_limit(_, B, V1, R))
         Value_to_type(V1 -> T1)
         Get_defined_alias(T1 -> S)
         WriteFFile("%s.R_foldl (fn (x, y) => ", S)
         WriteFile("let val ")
         Overload_binding(B -> B1)
	 -- type binding? TODO
         Emit_binding(B1)
         WriteFile(" = x in ")
         (|
           where(R -> nil)
           LParen
           Emit_value_expr(V)
           WriteFile("; y")
           RParen
         ||
           where(R -> restriction(_, V2))
           WriteFile("if ")
           Emit_value_expr(V2)
           WriteFile(" then ")
           LParen
           Emit_value_expr(V)
           WriteFile("; y")
           RParen
           WriteFile(" else y")
         |)
         WriteFile(" end) () ")
         LParen
         Emit_value_expr(V1)
         RParen

'action' Id_or_cons_or_overload_to_SML_id(POS, ID_OR_OP, Value_id, OPT_QUALIFICATION -> STRING)

  'rule' Id_or_cons_or_overload_to_SML_id(Pos, Id, I, Q -> S):
         (|
           Lookup_data_constructor(I -> S1)
           Id_or_op_to_SML_id(Id, nil -> S2)
           GetF2String("%s.%s", S1, S2 -> S)
         ||
           Overload_pos_id_or_op(Pos, Id -> Id1)
           Id_to_SML_id(Id1, Q -> S)
         |)

'action' Emit_value_val_occ(Value_id, OPT_QUALIFICATION)

  'rule' Emit_value_val_occ(VI, Q):
         VI'Ident -> Id
         (|
           where(Id -> op_op(Op))
           Built_in(Op, VI)
           VI'Type -> T
           Emit_value_op_as_fun(Op, T)
         ||
           VI'Pos -> Pos
	   -- try to fix qualifiers for functions that should be
	   -- qualified but are not (found in subtype conditions)
	   (|
	     eq(Q, nil)
	     VI'Qualifier -> list(H, T)
	     Prune_object_ids(list(H, T) -> Is)
	     (|
	       eq(Is, nil)
	       where(Q -> Q1)
	     ||
	       Object_ids_to_object(Is -> O)
	       where(qualification(O) -> Q1)
	     |)
	   ||
	     where(Q -> Q1)
	   |)
           Id_or_cons_or_overload_to_SML_id(Pos, Id, VI, Q1 -> S)
           WriteFile(S)
         |)

'action' Object_ids_to_object(Object_ids -> OBJECT_EXPR)

  'rule' Object_ids_to_object(list(I, nil) -> obj_occ(P, I)):
	 I'Pos -> P

  'rule' Object_ids_to_object(list(I, Is) -> qual_occ(P, O, I1)):
	 Split_object_ids(list(I, Is) -> Is1, I1)
	 I1'Pos -> P
	 Object_ids_to_object(Is1 -> O)
	 
'action' Split_object_ids(Object_ids -> Object_ids, Object_id)

  'rule' Split_object_ids(list(I, nil) -> nil, I):

  'rule' Split_object_ids(list(I, Ids) -> list(I, Ids1), I1):
	 Split_object_ids(Ids -> Ids1, I1)
	 

'action' Emit_value_var_occ(Variable_id, OPT_QUALIFICATION)
       
  'rule' Emit_value_var_occ(VarI, Q):
         VarI'Ident -> Id
         Id_to_SML_id(Id, Q -> S)
         WriteFFile("!%s", S)

'action' Emit_value_infix_occ(VALUE_EXPR, Value_id, OPT_QUALIFICATION, VALUE_EXPR)

  'rule' Emit_value_infix_occ(V1, VI, Q, V2):
         VI'Ident -> Id
         (|
           where(Id -> op_op(Op))
           Built_in(Op, VI)
	   (| -- check for isin dom, isin elems
	     (| eq(Op, isin) || eq(Op, notisin) |)
	     Dom_or_elems(V2 -> V3)
	     Emit_value_val_infix(V1, Op, VI, V3)
	   ||
             Emit_value_val_infix(V1, Op, VI, V2)
	   |)
         ||
           VI'Pos -> Pos
           Id_or_cons_or_overload_to_SML_id(Pos, Id, VI, Q -> S)
           WriteFile(S)
           WriteFile(" (")
           Emit_value_expr(V1)
           WriteFile(", ")
           Emit_value_expr(V2)
           RParen
         |)

'action' Emit_value_prefix_occ(Value_id, OPT_QUALIFICATION, VALUE_EXPR)
         
  'rule' Emit_value_prefix_occ(VI, Q, V):
         VI'Ident -> Id
         (|
           where(Id -> op_op(Op))
           Built_in(Op, VI)
           Emit_value_val_prefix(Op, V)
         ||
           VI'Pos -> Pos
           Id_or_cons_or_overload_to_SML_id(Pos, Id, VI, Q -> S)
           WriteFile(S)
           WriteFile(" (")
           Emit_value_expr(V)
           RParen
         |)

'action' Emit_value_ass_occ(POS, Variable_id, OPT_QUALIFICATION, VALUE_EXPR)

  'rule' Emit_value_ass_occ(P, VarI, Q, V):
         VarI'Ident -> Id
	 VarI'Type -> T
	 (| -- ignore any disambiguation
	   where(V -> disamb(_, V1, _))
	 ||
	   where(V -> V1)
	 |)
	 Maxtype(T -> Tm)
	 -- get best type
	 Type_of_val(V1, Tm -> T1)
	 string_to_id("z__" -> Z)
	 New_value_id(P, id_op(Z) -> I)
	 I'Type <- T1
	 Isin_subtype(val_occ(P,I,nil), T -> Pred)
	 Simplify(Pred -> Pred1)
         Id_to_SML_id(Id, Q -> S)
	 (|
	   ne(Pred1, no_val)
	   Overload_pos_id_or_op(P, id_op(Z) -> Z1)
	   Id_to_SML_id(Z1, nil -> ZS)
	   WriteFFile("let val %s = ", ZS)
	   Emit_value_expr(V)
	   WriteFile(" in if not(")
	   Emit_value_expr(Pred1)
	   PosAsString(P -> PS)
           SML_id_to_string(Id -> VS)
	   Get_defined_alias(T -> TS)
	   WriteF3File(") then raise RSL.RSL_exception (\"%s Value \" ^ %s.toString(%s) ^ ", PS, TS, ZS)
	   WriteF3File("\" of %s not in subtype\") else %s := %s end", VS, S, ZS)
	 ||
	   WriteFFile("%s := ", S)
	   LParen
	   Emit_value_expr(V)
	   RParen
	 |)	   

'action' Emit_let_def_list(LET_DEFS)

  'rule' Emit_let_def_list(LDL):
         (|
           where(LDL -> list(LD, Tail))
           (|
             where(LD -> explicit(_, binding(_, B), V))
             Overload_binding(B -> B1)
	     -- type binding? TODO
             WriteFile("val ")
             Emit_binding(B1)
             WriteFile(" = ")
             Emit_value_expr(V)
           ||
             where(LD -> explicit(_, pattern(Pos, P), V))
	     (|
	       where(P -> record_occ_pattern(_,_,_,_))
	       Check_for_equality_pattern(Pos, P)
               WriteFile("val ")
	       Emit_pattern(P)
	       WriteFile(" = ")
	       Emit_value_expr(V)
	     ||
	       (| -- prevent disambiguation getting into
	          -- condition
	         where(V -> disamb(_, V1, _))
	       ||
	         where(V -> V1)
	       |)
	       Pattern_match(V1, P -> C, DS)
	       Simplify(C -> C1)
	       (|
	         eq(C1, no_val)
	         Emit_let_def_list(DS)
	       ||
	         WriteFile("if ")
		 Emit_value_expr(C1)
		 WriteFile(" then ")
	         Emit_let_def_list(DS)
		 PosAsString(Pos -> PS)
	         Value_to_type(V1 -> T1)
	         Get_defined_alias(T1 -> TS)
		 WriteF2File(" else raise RSL.swap (\"%s Let pattern does not match value \" ^ %s.toString(", PS, TS)
		 Emit_value_expr(V1)
	         WriteFile("))")
	       |)
	     |)
           ||
             where(LD -> implicit(Pos, TG, R))
             (|
               WriteFile("val ")
               Emit_implicit_let_def(TG, R)
             ||
               Not_support(pos(Pos), "implicit let in general")
             |)
           |)        
           [|
             where(Tail -> list(_, _))
             WriteFile("; ")
             WritelnFile(1)
             Emit_let_def_list(Tail)
           |]
         ||
           where(LDL -> nil)
         |)  

'action' Emit_value_expr(VALUE_EXPR)

  'rule' Emit_value_expr(V):
         (|
           where(V -> literal_expr(_, L))
           Emit_value_literal_expr(L)
         ||
           where(V -> chaos(Pos))
           PosAsString(Pos -> PS)
           WriteFFile("raise RSL.RSL_exception \"%s chaos encountered\"", PS)
         ||
           where(V -> skip(_))
           Emit_value_literal_expr(unit)
         ||
           where(V -> stop(Pos))
           PosAsString(Pos -> PS)
           WriteFFile("raise RSL.RSL_exception \"%s stop encountered\"", PS)
         ||
           where(V -> swap(Pos))
           PosAsString(Pos -> PS)
           WriteFFile("raise RSL.swap \"no choices available at %s\"", PS)
         ||
           where(V -> product(_, VL))
           Emit_value_product(VL)
         ||
           where(V -> ranged_set(_, V1, V2))
           Emit_value_ranged_set(V1, V2)
         ||
           where(V -> enum_set(_, _))
           Emit_value_enum_set(V)
         ||
           where(V -> comp_set(Pos, V1, set_limit(_, TGL, R)))
           (|
             Emit_value_comp_set(V1, TGL, R)
           ||
             Not_support(pos(Pos), "comprehended sets in general")
           |)
         ||
           where(V -> ranged_list(_, V1, V2))
           Emit_value_ranged_list(V1, V2)
         ||
           where(V -> enum_list(_, VL))
           Emit_value_enum_list(VL)
         ||
           where(V -> comp_list(Pos, V1, list_limit(_, B, VL, R)))
           (|
             Emit_value_comp_list(V1, B, VL, R)
           ||
             Not_support(pos(Pos), "comprehended lists in general")
           |)
         ||
           where(V -> enum_map(_, VPL))
           Emit_value_enum_map(V)
         ||
           where(V -> comp_map(Pos, VP, set_limit(_, TGL, R)))
           (|
             Emit_value_comp_map(VP, TGL, R)
           ||
             Not_support(pos(Pos), "comprehended maps in general")
           |)
         ||
           where(V -> function(_, LE, V1))
           Emit_lambda_parameter(LE)
           WriteFile(" => ")
           Emit_value_expr(V1)
         ||
           where(V -> application(Pos, VF, ArgL))
           (|
             -- break into one parameter at a time, since
             -- different arguments may be applications of
             -- functions, lists, maps etc.
             -- Uses basic equivalence f(x)(y) = (f(x))(y)
             where(ArgL -> list(Arg1, Tail1:list(_, _)))
             Emit_value_expr(application(Pos, application(Pos, VF, list(Arg1, nil)), Tail1))
           ||
             Emit_application_function(VF, ArgL)
             Emit_application_arg_list(ArgL)
           |)
         ||
           where(V -> quantified(Pos, Q, TGL, R))
           (|
             Emit_value_quantified(Q, TGL, R)
           ||
             Not_support(pos(Pos), "quantified expressions in general")
-- debug
-- Print_expr(V)
-- Putnl()
-- print(V)
           |)
         ||
           where(V -> post(_, V1, Post, Pre))
           Emit_value_post(V1, Post, Pre)
         ||
           where(V -> disamb(_, V1, T))
           (|
             -- some special cases inserted during resolving
             where(V1 -> enum_set(_, nil))
             Emit_value_empty_set(T)
           ||
             where(V1 -> enum_list(_, nil))
             Emit_value_empty_list(T)
           ||
             where(V1 -> enum_map(_, nil))
             Emit_value_empty_map(T)
           ||
             LParen
             LParen
             Emit_value_expr(V1)
             RParen
             Get_defined_alias(T -> S)
             WriteFFile(":%s.t", S)
             RParen
           |)
         ||
           where(V -> bracket(_, V1))
           LParen
           Emit_value_expr(V1)
           RParen
         ||
           where(V -> ax_infix(P, V1, Conn, V2, PE))
	   [|  -- generated axiom infixes
	       -- (preconditions of built in functions,
	       --  confidence conditions, etc)
	       -- set the two positions the same
	     ne(P, PE)
	     Add_region(region(P, PE))
	   |]
           Emit_value_ax_infix(P, V1, Conn, V2, PE)
         ||
--           where(V -> val_infix(_, V1, InOp, V2))
--           Emit_value_val_infix(V1, InOp, V2)
--         ||
           where(V -> stmt_infix(Pos, V1, int_choice, V2))
	   WriteFile("R_int_choice.choice([\n")
	   Flatten_choices(V2 -> VL)
	   Emit_choices(list(V1, VL))
	   PosAsString(Pos -> PS)
	   WriteFFile("], \"no choices available at %s\")", PS)
	 ||
           where(V -> stmt_infix(_, V1, sequence, V2))
           LParen
           Emit_value_expr(V1)
           WriteFile("; ")
           Emit_value_expr(V2)
           RParen
         ||
           where(V -> ax_prefix(_, Conn, V1))
           Emit_value_ax_prefix(Conn, V1)
         ||
           where(V -> val_prefix(_, PreOp, V1))
           Emit_value_val_prefix(PreOp, V1)
         ||
           where(V -> assignment(_, Na, V1))
           Emit_value_assignment(Na, V1)
         ||
           where(V -> local_expr(_, DL, V1))
           Emit_value_local_expr(DL, V1)
         ||
           where(V -> let_expr(_, LDL, V1))
           Emit_value_let_expr(LDL, V1)
         ||
           where(V -> if_expr(P, V1, V2, RT, ELIF, EL))
           Emit_value_if_expr(P, V1, V2, RT, ELIF, EL)  
         ||
           where(V -> case_expr(P, V1, P1, CBL))
	   Add_case_regions(CBL)
	   LParen
	   (|
	     Find_record_occ_pattern(CBL, nil -> found)
	     Emit_value_case_expr(V1, CBL, 0)
	   ||
	     Value_to_type(V1 -> T1)
	     (|
	       Is_simple_val(V1)
	       Emit_value_case_as_if(P1, V1, T1, CBL)
	     ||
	       string_to_id("v__" -> Z)
	       New_value_id(P, id_op(Z) -> I)
	       I'Type <- T1
	       Overload_pos_id_or_op(P, id_op(Z) -> Z1)
	       Id_to_SML_id(Z1, nil -> ZS)
	       WriteFFile("let val %s = ", ZS)
	       Emit_value_expr(V1)
	       WriteFile(" in ")
	       Emit_value_case_as_if(P1, val_occ(P, I, nil), T1, CBL)
	       WriteFile(" end")
	     |)
	   |)
	   RParen
         ||
           where(V -> while_expr(_, V1, V2))
           Emit_value_while_expr(V1, V2)
         ||
           where(V -> until_expr(_, V1, V2))
           Emit_value_until_expr(V1, V2)           
         ||
           where(V -> for_expr(_, Limit, V1))
           Emit_value_for_expr(Limit, V1)
         ||
           where(V -> val_occ(_, VI, Q))
           Emit_value_val_occ(VI, Q)
         ||
           where(V -> var_occ(_, VarI, Q))
           Emit_value_var_occ(VarI, Q)
         ||
           where(V -> infix_occ(_, V1, VI, Q, V2))
           Emit_value_infix_occ(V1, VI, Q, V2)
         ||
           where(V -> prefix_occ(_, VI, Q, V1))
           Emit_value_prefix_occ(VI, Q, V1)
         ||
           where(V -> ass_occ(P, VarI, Q, V1))
           Emit_value_ass_occ(P, VarI, Q, V1)
         ||
           where(V -> env_local(_, DL, CE, V1))
           Emit_value_env_local(DL, CE, V1)
	 ||
	   Putmsg("Internal error: cannot translate ")
	   Print_expr(V)
	   Putnl()
         |)

'condition' Is_simple_val(VALUE_EXPR)

  'rule' Is_simple_val(val_occ(_,_,_)):

  'rule' Is_simple_val(var_occ(_,_,_)):

  'rule' Is_simple_val(bracket(_, V)):
	 Is_simple_val(V)

  'rule' Is_simple_val(disamb(_,V,_)):
	 Is_simple_val(V)

'action' Flatten_choices(VALUE_EXPR -> VALUE_EXPRS)

  'rule' Flatten_choices(stmt_infix(_, V1, int_choice, V2) -> list(V1, VL)):
	 Flatten_choices(V2 -> VL)

  'rule' Flatten_choices(V -> list(V, nil)):

'action' Emit_choices(VALUE_EXPRS)

  'rule' Emit_choices(list(V, VL)):
	 WriteFile("fn () => ")
	 Emit_value_expr(V)
	 [|
	   ne(VL, nil)
	   WriteFile(",\n")
	   Emit_choices(VL)
	 |]
	 

-- debug
'action' Print_type_aliases

  'rule' Print_type_aliases:
	 Var_aliased_types -> TaL
	 Print_type_aliases1(TaL)

'action' Print_type_aliases1(TYPE_ALIASES)

  'rule' Print_type_aliases1(list(A, AL)):
	 Print_type_alias(A)
	 Print_type_aliases1(AL)

  'rule' Print_type_aliases1(nil):

'action' Print_type_alias(TYPE_ALIAS)

  'rule' Print_type_alias(alias(S, T)):
	 Putmsg(S)
	 Putmsg(" is alias for ")
	 Print_type(T)
	 Putnl

	 
	 
