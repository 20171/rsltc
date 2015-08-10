-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the variables used to store environments
-- plus other global variables
-- plus functions to access and minipulate environments
-- plus lookup functions for objects
-- plus functions for checking static implementation (for actual/formal
-- scheme parameters and implementation relations)


'module' env

'use' ast print ext types values objects sal_global_vars

'export' 

-- Variables
  Globals Parameters Current
  Module_name Extend_paths Polynum Type_numbers 
  Dummy_id1 Dummy_id2 Time_id

  Is_LTL_Wanted
  Set_LTL_Wanted
  Clear_LTL_Wanted
  Has_LTL
  Set_Has_LTL
  Clear_Has_LTL

  Id_of_ge_int Id_of_ge_real Id_of_card Id_of_len
  Id_of_gt_int Id_of_le_int Id_of_lt_int Id_of_minus_inf_int
  Id_of_isin_set Id_of_isin_map Id_of_isin_list
  Id_of_notisin_set Id_of_notisin_map Id_of_notisin_list
  Id_of_eq Id_of_neq
  Id_of_inds Id_of_union_set Id_of_hd_set
  Id_of_hd_list Id_of_tl
  Id_of_subseteq
  Id_of_rsl_is_nat Id_of_rsl_is_int
  Id_of_div_int Id_of_div_real
  Id_of_exp_int Id_of_exp_real
  Id_of_rem_int
  -- For SAL LTL functions:
  Id_of_G
  Id_of_X
  Id_of_F
  Id_of_U
  Id_of_R
  Id_of_W

-- Actions
  Make_op_types Lookup_op_types Lookup_id_types Define_SAL_property_funs
  Make_destructor_definition Make_reconstructor_definition
  Apply_dom Apply_rng
  Lookup_object_in_module Get_object_id  Get_object_id1
  Lookup_object_in_env Lookup_object_in_current_env Split_name
  Object_pos Id_of_object Object_type_check Get_id_of_scheme
  Get_module_pos Set_module_name_and_pos


  Get_current_env Get_current_path_env Set_current_env
  Get_env_types Get_current_types Set_current_types
  Get_env_top_values Get_current_values Set_current_values
  Get_env_variables Get_current_variables Set_current_variables
  Get_env_channels Get_current_channels Set_current_channels
  Get_env_modules Get_current_modules Set_current_modules
  Get_env_axioms Get_current_axioms Set_current_axioms
  Get_env_test_cases Get_current_test_cases Set_current_test_cases
  -- SAL
  Get_env_transition_systems Get_current_transition_systems Set_current_transition_system
  Get_Transition_System
  Get_env_properties Get_current_properties Set_current_property

  Get_current_with Set_current_with
  Get_current_adapts Set_current_adapts
  Get_env_with Set_env_with Get_env_adapts Set_env_adapts
  Get_current_top_values
  Start_extend In_left Left_right Out_right Up1 Out_scope All_left
  Adapt Equal_id_or_op Make_actual_params
  Object_param_type Fit_name
  Unfold_types Check_object_params Check_implementations Check_implementation
  Unadapt_name Unadapt_env_name Concat_adapts
  Qualify_name Concat_objs

  Variable_is_defined_in_current_env Variable_is_defined_in_class_env
  Channel_is_defined_in_current_env Channel_is_defined_in_class_env
  Object_is_defined_in_current_env Object_is_defined_in_class_env

-- Utilities
   Type_of CHECK


--------------------------------------------------------------------
-- Global variables
--------------------------------------------------------------------

-- Context schemes and objects
'var' Globals : MODULE_ENV

-- Parameters when checking a scheme
'var' Parameters : MODULE_ENV

-- The current environment
'var' Current : CURRENT_ENV

-- Current path when checking an extend
'var' Extend_paths : PATHS

-- Note that Current holds a stack of environments and Extend_paths
-- holds a stack of paths.  It is important that these two stacks are
-- always of the same depth.

-- name and position of top level module
'var' Module_name : STRING

'var' Module_pos : POS

-- Different sorts in formal parameters are distinguished by TYPE_NUMBERS
'var' Type_numbers : TYPE_NUMBERS

-- Current number for TYPE_NUMBERS
'var' Polynum : INT

-- Dummy identifiers used in checking implementation relations
'var' Dummy_id1 : IDENT

'var' Dummy_id2 : IDENT

-- Time_id used to check for use of Time (predefined in TRSL)
'var' Time_id : IDENT

'type' Wanted_Type

       true,
       false


'var' LTL_Wanted : Wanted_Type

'condition' Is_LTL_Wanted()

  'rule' Is_LTL_Wanted()
	 LTL_Wanted -> true

'action' Set_LTL_Wanted()

  'rule' Set_LTL_Wanted()
         LTL_Wanted <- true

'action' Clear_LTL_Wanted()

  'rule' Clear_LTL_Wanted()
         LTL_Wanted <- false

'var' Has_LTL_Decl : Wanted_Type

'condition' Has_LTL()

  'rule' Has_LTL():
  	 Has_LTL_Decl -> true

'action' Set_Has_LTL()

  'rule' Set_Has_LTL():
  	 Has_LTL_Decl <- true

'action' Clear_Has_LTL()

  'rule' Clear_Has_LTL():
  	 Has_LTL_Decl <- false

-- Variables to hold Value_ids for built-in operators
'var' Id_of_eq : Value_id
'var' Id_of_neq : Value_id
'var' Id_of_gt_int : Value_id
'var' Id_of_gt_real : Value_id
'var' Id_of_lt_int : Value_id
'var' Id_of_lt_real : Value_id
'var' Id_of_ge_int : Value_id
'var' Id_of_ge_real : Value_id
'var' Id_of_le_int : Value_id
'var' Id_of_le_real : Value_id
'var' Id_of_supset : Value_id
'var' Id_of_subset : Value_id
'var' Id_of_supseteq : Value_id
'var' Id_of_subseteq : Value_id
'var' Id_of_isin_set : Value_id
'var' Id_of_isin_list : Value_id
'var' Id_of_isin_map : Value_id
'var' Id_of_notisin_set : Value_id
'var' Id_of_notisin_list : Value_id
'var' Id_of_notisin_map : Value_id
'var' Id_of_rem_int : Value_id
'var' Id_of_rem_set : Value_id
'var' Id_of_rem_map : Value_id
'var' Id_of_caret : Value_id
'var' Id_of_union_set : Value_id
'var' Id_of_union_map : Value_id
'var' Id_of_override : Value_id
'var' Id_of_mult_int : Value_id
'var' Id_of_mult_real : Value_id
'var' Id_of_div_int : Value_id
'var' Id_of_div_real : Value_id
'var' Id_of_div_map : Value_id
'var' Id_of_hash_fun : Value_id
'var' Id_of_hash_map : Value_id
'var' Id_of_inter : Value_id
'var' Id_of_exp_int : Value_id
'var' Id_of_exp_real : Value_id
'var' Id_of_abs_int : Value_id
'var' Id_of_abs_real : Value_id
'var' Id_of_int : Value_id
'var' Id_of_real : Value_id
'var' Id_of_card : Value_id
'var' Id_of_len : Value_id
'var' Id_of_inds : Value_id
'var' Id_of_elems : Value_id
'var' Id_of_hd_set : Value_id
'var' Id_of_hd_list : Value_id
'var' Id_of_hd_map : Value_id
'var' Id_of_tl : Value_id
'var' Id_of_dom : Value_id
'var' Id_of_rng : Value_id
'var' Id_of_wait_time : Value_id
'var' Id_of_wait_int : Value_id
'var' Id_of_plus_inf_int : Value_id
'var' Id_of_plus_inf_real : Value_id
'var' Id_of_plus_pre_int : Value_id
'var' Id_of_plus_pre_real : Value_id
'var' Id_of_minus_inf_int : Value_id
'var' Id_of_minus_inf_real : Value_id
'var' Id_of_minus_pre_int : Value_id
'var' Id_of_minus_pre_real : Value_id
'var' Id_of_rsl_is_nat : Value_id
'var' Id_of_rsl_is_int : Value_id
-- Prefix functionss for SAL mode:
-- For LTL functionss:
'var' Id_of_G : Value_id
'var' Id_of_F : Value_id
'var' Id_of_X : Value_id
'var' Id_of_U : Value_id
'var' Id_of_R : Value_id
'var' Id_of_W : Value_id

'action' Make_op_types

  'rule' Make_op_types:
         DefaultPos(-> P)
         New_value_id(P, op_op(eq) -> I_eq)
         I_eq'Type <- fun(product(list(poly(1),list(poly(1),nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_eq <- I_eq
         New_value_id(P, op_op(neq) -> I_neq)
         I_neq'Type <- fun(product(list(poly(1),list(poly(1),nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_neq <- I_neq
         New_value_id(P, op_op(gt) -> I_gt_int)
         I_gt_int'Type <- fun(product(list(int,list(int,nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_gt_int <- I_gt_int
         New_value_id(P, op_op(gt) -> I_gt_real)
         I_gt_real'Type <- fun(product(list(real,list(real,nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_gt_real <- I_gt_real
         New_value_id(P, op_op(lt) -> I_lt_int)
         I_lt_int'Type <- fun(product(list(int,list(int,nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_lt_int <- I_lt_int
         New_value_id(P, op_op(lt) -> I_lt_real)
         I_lt_real'Type <- fun(product(list(real,list(real,nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_lt_real <- I_lt_real
         New_value_id(P, op_op(ge) -> I_ge_int)
         I_ge_int'Type <- fun(product(list(int,list(int,nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_ge_int <- I_ge_int
         New_value_id(P, op_op(ge) -> I_ge_real)
         I_ge_real'Type <- fun(product(list(real,list(real,nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_ge_real <- I_ge_real
         New_value_id(P, op_op(le) -> I_le_int)
         I_le_int'Type <- fun(product(list(int,list(int,nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_le_int <- I_le_int
         New_value_id(P, op_op(le) -> I_le_real)
         I_le_real'Type <- fun(product(list(real,list(real,nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_le_real<- I_le_real
         New_value_id(P, op_op(supset) -> I_supset)
         I_supset'Type <- fun(product(list(infin_set(poly(1)),list(infin_set(poly(1)),nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_supset <- I_supset
         New_value_id(P, op_op(subset) -> I_subset)
         I_subset'Type <- fun(product(list(infin_set(poly(1)),list(infin_set(poly(1)),nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_subset <- I_subset
         New_value_id(P, op_op(supseteq) -> I_supseteq)
         I_supseteq'Type <- fun(product(list(infin_set(poly(1)),list(infin_set(poly(1)),nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_supseteq <- I_supseteq
         New_value_id(P, op_op(subseteq) -> I_subseteq)
         I_subseteq'Type <- fun(product(list(infin_set(poly(1)),list(infin_set(poly(1)),nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_subseteq <- I_subseteq
         New_value_id(P, op_op(isin) -> I_isin_set)
         I_isin_set'Type <- fun(product(list(poly(1),list(infin_set(poly(1)),nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_isin_set <- I_isin_set
         New_value_id(P, op_op(isin) -> I_isin_list)
         I_isin_list'Type <- fun(product(list(poly(1),list(infin_list(poly(1)),nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_isin_list <- I_isin_list
         New_value_id(P, op_op(isin) -> I_isin_map)
         I_isin_map'Type <- fun(product(list(poly(1),list(infin_map(poly(1),poly(2)),nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_isin_map <- I_isin_map
         New_value_id(P, op_op(notisin) -> I_notisin_set)
         I_notisin_set'Type <- fun(product(list(poly(1),list(infin_set(poly(1)),nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_notisin_set <- I_notisin_set
         New_value_id(P, op_op(notisin) -> I_notisin_list)
         I_notisin_list'Type <- fun(product(list(poly(1),list(infin_list(poly(1)),nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_notisin_list <- I_notisin_list
         New_value_id(P, op_op(notisin) -> I_notisin_map)
         I_notisin_map'Type <- fun(product(list(poly(1),list(infin_map(poly(1),poly(2)),nil))),total,result(bool,nil,nil,nil,nil))
         Id_of_notisin_map <- I_notisin_map
         New_value_id(P, op_op(rem) -> I_rem_int)
         I_rem_int'Type <- fun(product(list(int,list(int,nil))),partial,result(int,nil,nil,nil,nil))
         Id_of_rem_int <- I_rem_int
         New_value_id(P, op_op(rem) -> I_rem_set)
         I_rem_set'Type <- fun(product(list(infin_set(poly(1)),list(infin_set(poly(1)),nil))),total,result(infin_set(poly(1)),nil,nil,nil,nil))
         Id_of_rem_set <- I_rem_set
         New_value_id(P, op_op(rem) -> I_rem_map)
         I_rem_map'Type <- fun(product(list(infin_map(poly(1),poly(2)),list(infin_set(poly(1)),nil))),total,result(infin_map(poly(1),poly(2)),nil,nil,nil,nil))
         Id_of_rem_map <- I_rem_map
         New_value_id(P, op_op(caret) -> I_caret)
         I_caret'Type <- fun(product(list(fin_list(poly(1)),list(infin_list(poly(1)),nil))),total,result(infin_list(poly(1)),nil,nil,nil,nil))
         Id_of_caret <- I_caret
         New_value_id(P, op_op(union) -> I_union_set)
         I_union_set'Type <- fun(
                product(list(infin_set(poly(1)),list(infin_set(poly(1)),nil))),
                total,
                result(infin_set(poly(1)),nil,nil,nil,nil))
         Id_of_union_set <- I_union_set
         New_value_id(P, op_op(union) -> I_union_map)
         I_union_map'Type <- fun(
                product(list(infin_map(poly(1),poly(2)),list(infin_map(poly(1),poly(2)),nil))),
                total,
                result(infin_map(poly(1),poly(2)),nil,nil,nil,nil))
         Id_of_union_map <- I_union_map
         New_value_id(P, op_op(override) -> I_override)
         I_override'Type <- fun(product(list(infin_map(poly(1),poly(2)),list(infin_map(poly(1),poly(2)),nil))),total,result(infin_map(poly(1),poly(2)),nil,nil,nil,nil))
         Id_of_override <- I_override
         New_value_id(P, op_op(mult) -> I_mult_int)
         I_mult_int'Type <- fun(product(list(int,list(int,nil))),total,result(int,nil,nil,nil,nil))
         Id_of_mult_int <- I_mult_int
         New_value_id(P, op_op(mult) -> I_mult_real)
         I_mult_real'Type <- fun(product(list(real,list(real,nil))),total,result(real,nil,nil,nil,nil))
         Id_of_mult_real <- I_mult_real
         New_value_id(P, op_op(div) -> I_div_int)
         I_div_int'Type <- fun(product(list(int,list(int,nil))),partial,result(int,nil,nil,nil,nil))
         Id_of_div_int <- I_div_int
         New_value_id(P, op_op(div) -> I_div_real)
         I_div_real'Type <- fun(product(list(real,list(real,nil))),partial,result(real,nil,nil,nil,nil))
         Id_of_div_real <- I_div_real
         New_value_id(P, op_op(div) -> I_div_map)
         I_div_map'Type <- fun(product(list(infin_map(poly(1),poly(2)),list(infin_set(poly(1)),nil))),total,result(infin_map(poly(1),poly(2)),nil,nil,nil,nil))
         Id_of_div_map <- I_div_map
         New_value_id(P, op_op(hash) -> I_hash_fun)
         I_hash_fun'Type <- fun(
                product(list(fun(poly(1),partial,result(poly(2),nil,nil,nil,nil)),
                  list(fun(poly(3),partial,result(poly(1),nil,nil,nil,nil)),nil))),
                total,
                result(fun(poly(3),partial,result(poly(2),nil,nil,nil,nil)),nil,nil,nil,nil))
         Id_of_hash_fun <- I_hash_fun
         New_value_id(P, op_op(hash) -> I_hash_map)
         I_hash_map'Type <- fun(
                product(list(infin_map(poly(1),poly(2)),
                  list(infin_map(poly(3),poly(1)),nil))),
                total,
                result(infin_map(poly(3),poly(2)),nil,nil,nil,nil))
         Id_of_hash_map <- I_hash_map
         New_value_id(P, op_op(inter) -> I_inter)
         I_inter'Type <- fun(product(list(infin_set(poly(1)),list(infin_set(poly(1)),nil))),total,result(infin_set(poly(1)),nil,nil,nil,nil))
         Id_of_inter <- I_inter
         New_value_id(P, op_op(exp) -> I_exp_int)
         I_exp_int'Type <- fun(product(list(int,list(int,nil))),partial,result(int,nil,nil,nil,nil))
         Id_of_exp_int <- I_exp_int
         New_value_id(P, op_op(exp) -> I_exp_real)
         I_exp_real'Type <- fun(product(list(real,list(real,nil))),partial,result(real,nil,nil,nil,nil))
         Id_of_exp_real <- I_exp_real
         New_value_id(P, op_op(abs) -> I_abs_int)
         I_abs_int'Type <- fun(int,total,result(nat,nil,nil,nil,nil))
         Id_of_abs_int <- I_abs_int
         New_value_id(P, op_op(abs) -> I_abs_real)
         I_abs_real'Type <- fun(real,total,result(real,nil,nil,nil,nil))
         Id_of_abs_real <- I_abs_real
         New_value_id(P, op_op(int) -> I_int)
         I_int'Type <- fun(real,total,result(int,nil,nil,nil,nil))
         Id_of_int <- I_int
         New_value_id(P, op_op(real) -> I_real)
         I_real'Type <- fun(int,total,result(real,nil,nil,nil,nil))
         Id_of_real <- I_real
         New_value_id(P, op_op(card) -> I_card)
         I_card'Type <- fun(fin_set(any),total,result(nat,nil,nil,nil,nil))
         Id_of_card <- I_card
         New_value_id(P, op_op(len) -> I_len)
         I_len'Type <- fun(fin_list(any),total,result(nat,nil,nil,nil,nil))
         Id_of_len <- I_len
         New_value_id(P, op_op(inds) -> I_inds)
         I_inds'Type <- fun(infin_list(any),total,result(infin_set(nat),nil,nil,nil,nil))
         Id_of_inds <- I_inds
         New_value_id(P, op_op(elems) -> I_elems)
         I_elems'Type <- fun(infin_list(poly(1)),total,result(infin_set(poly(1)),nil,nil,nil,nil))
         Id_of_elems <- I_elems
         New_value_id(P, op_op(hd) -> I_hd_set)
         I_hd_set'Type <- fun(infin_set(poly(1)),partial,result(poly(1),nil,nil,nil,nil))
         Id_of_hd_set <- I_hd_set
         New_value_id(P, op_op(hd) -> I_hd_list)
         I_hd_list'Type <- fun(infin_list(poly(1)),partial,result(poly(1),nil,nil,nil,nil))
         Id_of_hd_list <- I_hd_list
         New_value_id(P, op_op(hd) -> I_hd_map)
         I_hd_map'Type <- fun(infin_map(poly(1),poly(2)),partial,result(poly(1),nil,nil,nil,nil))
         Id_of_hd_map <- I_hd_map
         New_value_id(P, op_op(tl) -> I_tl)
         I_tl'Type <- fun(infin_list(poly(1)),partial,result(infin_list(poly(1)),nil,nil,nil,nil))
         Id_of_tl <- I_tl
         New_value_id(P, op_op(dom) -> I_dom)
         I_dom'Type <- fun(infin_map(poly(1),poly(2)),total,result(infin_set(poly(1)),nil,nil,nil,nil))
         Id_of_dom <- I_dom
         New_value_id(P, op_op(rng) -> I_rng)
         I_rng'Type <- fun(infin_map(poly(1),poly(2)),total,result(infin_set(poly(2)),nil,nil,nil,nil))
         Id_of_rng <- I_rng
         New_value_id(P, op_op(wait) -> I_wait_time)
         I_wait_time'Type <- fun(time,total,result(unit,nil,nil,nil,nil))
         Id_of_wait_time <- I_wait_time
         New_value_id(P, op_op(wait) -> I_wait_int)
         I_wait_int'Type <- fun(nat,total,result(unit,nil,nil,nil,nil))
         Id_of_wait_int <- I_wait_int
         New_value_id(P, op_op(plus) -> I_plus_inf_int)
         I_plus_inf_int'Type <- fun(product(list(int,list(int,nil))),total,result(int,nil,nil,nil,nil))
         Id_of_plus_inf_int <- I_plus_inf_int
         New_value_id(P, op_op(plus) -> I_plus_inf_real)
         I_plus_inf_real'Type <- fun(product(list(real,list(real,nil))),total,result(real,nil,nil,nil,nil))
         Id_of_plus_inf_real <- I_plus_inf_real
	 New_value_id(P, op_op(plus) -> I_plus_pre_int)
	 I_plus_pre_int'Type <- fun(int,total,result(int,nil,nil,nil,nil))
	 Id_of_plus_pre_int <- I_plus_pre_int
	 New_value_id(P, op_op(plus) -> I_plus_pre_real)
	 I_plus_pre_real'Type <- fun(real,total,result(real,nil,nil,nil,nil))
	 Id_of_plus_pre_real <- I_plus_pre_real
         New_value_id(P, op_op(minus) -> I_minus_inf_int)
         I_minus_inf_int'Type <- fun(product(list(int,list(int,nil))),total,result(int,nil,nil,nil,nil))
         Id_of_minus_inf_int <- I_minus_inf_int
         New_value_id(P, op_op(minus) -> I_minus_inf_real)
         I_minus_inf_real'Type <- fun(product(list(real,list(real,nil))),total,result(real,nil,nil,nil,nil))
         Id_of_minus_inf_real <- I_minus_inf_real
         New_value_id(P, op_op(minus) -> I_minus_pre_int)
         I_minus_pre_int'Type <- fun(int,total,result(int,nil,nil,nil,nil))
         Id_of_minus_pre_int <- I_minus_pre_int
         New_value_id(P, op_op(minus) -> I_minus_pre_real)
         I_minus_pre_real'Type <- fun(real,total,result(real,nil,nil,nil,nil))
         Id_of_minus_pre_real <- I_minus_pre_real
	 string_to_id("RSL_is_Nat" -> Is_nat_id)
	 New_value_id(P, id_op(Is_nat_id) -> I_rsl_is_nat)
	 I_rsl_is_nat'Type <- fun(int,total,result(bool,nil,nil,nil,nil))
	 Id_of_rsl_is_nat <- I_rsl_is_nat
	 string_to_id("RSL_is_Int" -> Is_int_id)
	 New_value_id(P, id_op(Is_int_id) -> I_rsl_is_int)
	 I_rsl_is_int'Type <- fun(int,total,result(bool,nil,nil,nil,nil))
	 Id_of_rsl_is_int <- I_rsl_is_int
         -- preconditions; first some abbreviations
         Parameter(P, "x" -> XP)
         Parameter(P, "y" -> YP)
         Occurrence(P, "x" -> X)
         Occurrence(P, "y" -> Y)
         Literal(P, "0" -> Zero_int)
         Literal(P, "0.0" -> Zero_real)
         where(infix_occ(P, Y, I_neq, nil, Zero_int) -> Y_n_z_int)
         where(infix_occ(P, Y, I_neq, nil, Zero_real) -> Y_n_z_real)
         -- remainder
         I_rem_int'Def <-
           expl_fun(list(XP, list(YP, nil)), no_val, nil, pre_cond(P, Y_n_z_int), nil, nil)
         -- map union
         where(prefix_occ(P, I_dom, nil, X) -> DomX)
         where(prefix_occ(P, I_dom, nil, Y) -> DomY)
         where(infix_occ(P, DomX, I_inter, nil, DomY) -> InterXY)
         where(infix_occ(P, InterXY, I_eq, nil, enum_set(P, nil)) -> Inter_empty)
         I_union_map'Def <-
           expl_fun(list(XP, list(YP, nil)), no_val, nil, pre_cond(P, Inter_empty), nil, nil)
         -- integer devision
         I_div_int'Def <-
           expl_fun(list(XP, list(YP, nil)), no_val, nil, pre_cond(P, Y_n_z_int), nil, nil)
         -- real devision
         I_div_real'Def <-
           expl_fun(list(XP, list(YP, nil)), no_val, nil, pre_cond(P, Y_n_z_real), nil, nil)
         -- hash for maps
         where(prefix_occ(P, I_rng, nil, Y) -> RngY)
         where(infix_occ(P, RngY, I_subseteq, nil, DomX) -> RngSubDom)
         I_hash_map'Def <-
           expl_fun(list(XP, list(YP, nil)), no_val, nil, pre_cond(P, RngSubDom), nil, nil)
         -- integer exponentiation
         where(infix_occ(P, Y, I_ge_int, nil, Zero_int) -> Y_ge_z_int)
         where(infix_occ(P, X, I_eq, nil, Zero_int) -> X_z_int)
         where(ax_infix(P, X_z_int, implies, Y_n_z_int, P) -> C1)
         where(ax_infix(P, Y_ge_z_int, and, bracket(P,C1), P) -> C2)
         I_exp_int'Def <-
           expl_fun(list(XP, list(YP, nil)), no_val, nil, pre_cond(P, C2), nil, nil)
         -- real exponentiation
         where(infix_occ(P, Y, I_le_real, nil, Zero_real) -> Y_le_z_real)
         where(infix_occ(P, X, I_neq, nil, Zero_real) -> X_n_z_real)
         where(infix_occ(P, X, I_ge_real, nil, Zero_real) -> X_ge_z_real)
         where(prefix_occ(P, I_int, nil, Y) -> IntY)
         where(prefix_occ(P, I_real, nil, bracket(P,IntY)) -> RealIntY)
         where(infix_occ(P, RealIntY, I_neq, nil, Y) -> NotWholeY)
         where(ax_infix(P, Y_le_z_real, implies, X_n_z_real, P) -> C3)
         where(ax_infix(P, NotWholeY, implies, X_ge_z_real, P) -> C4)
         where(ax_infix(P, bracket(P,C3), and, bracket(P,C4), P) -> C5)
         I_exp_real'Def <-
           expl_fun(list(XP, list(YP, nil)), no_val, nil, pre_cond(P, C5), nil, nil)
         -- hd
         where(infix_occ(P, X, I_neq, nil, enum_set(P, nil)) -> Set_n_empty)
         where(infix_occ(P, X, I_neq, nil, enum_list(P, nil)) -> List_n_empty)
         where(infix_occ(P, X, I_neq, nil, enum_map(P, nil)) -> Map_n_empty)
         I_hd_set'Def <-
           expl_fun(list(XP, nil), no_val, nil, pre_cond(P, Set_n_empty), nil, nil)
         I_hd_list'Def <-
           expl_fun(list(XP, nil), no_val, nil, pre_cond(P, List_n_empty), nil, nil)
         I_hd_map'Def <-
           expl_fun(list(XP, nil), no_val, nil, pre_cond(P, Map_n_empty), nil, nil)
         -- tl
         I_tl'Def <-
           expl_fun(list(XP, nil), no_val, nil, pre_cond(P, List_n_empty), nil, nil)

'action' Define_SAL_property_funs

  'rule' Define_SAL_property_funs:
	 DefaultPos(-> P)
	 string_to_id("G" -> Gid)
	 New_value_id(P, id_op(Gid) -> G_vid)
	 G_vid'Type <- fun(bool, total, result(bool,nil,nil,nil,nil))
	 Id_of_G <- G_vid
	 string_to_id("X" -> Xid)
	 New_value_id(P, id_op(Xid) -> X_vid)
	 X_vid'Type <- fun(bool, total, result(bool,nil,nil,nil,nil))
	 Id_of_X <- X_vid
	 string_to_id("F" -> Fid)
	 New_value_id(P, id_op(Fid) -> F_vid)
	 F_vid'Type <- fun(bool, total, result(bool,nil,nil,nil,nil))
	 Id_of_F <- F_vid
	 string_to_id("U" -> Uid)
	 New_value_id(P, id_op(Uid) -> U_vid)
	 U_vid'Type <- fun(product(list(bool,list(bool,nil))), total, result(bool,nil,nil,nil,nil))
	 Id_of_U <- U_vid
	 string_to_id("R" -> Rid)
	 New_value_id(P, id_op(Rid) -> R_vid)
	 R_vid'Type <- fun(product(list(bool,list(bool,nil))), total, result(bool,nil,nil,nil,nil))
	 Id_of_R <- R_vid
	 string_to_id("W" -> Wid)
	 New_value_id(P, id_op(Wid) -> W_vid)
	 W_vid'Type <- fun(product(list(bool,list(bool,nil))), total, result(bool,nil,nil,nil,nil))
	 Id_of_W <- W_vid
	 

'action' Parameter(POS, STRING -> FORMAL_FUNCTION_PARAMETER)

  'rule' Parameter(P, S -> form_parm(P, list(single(P, id_op(X)), nil))):
         string_to_id(S -> X)

'action' Occurrence(POS, STRING -> VALUE_EXPR)

  'rule' Occurrence(P, S -> named_val(P, name(P, id_op(X)))):
         string_to_id(S -> X)

'action' Literal(POS, STRING -> VALUE_EXPR)

  'rule' Literal(P, S -> literal_expr(P, int(X))):
         string_to_id(S -> X)

-- generates a parameter "x_"
-- and a definition "let con(x1,...,xn) = x in xj end"
-- and, if ARR is partial, a precondition "exists y : T :- x = con(y)"
-- or, if PVSWanted or SALWanted, a precondition "con?(x)"
'action' Make_destructor_definition(Value_id, INT, Value_ids, FUNCTION_ARROW, CONSTANT_CONSTRUCTOR -> VALUE_DEFINITION)

  'rule' Make_destructor_definition(I, J, Ids, ARR, Ccid ->
                                       expl_fun(list(FP,nil), DEF, nil, PREC, nil, nil)):
         I'Type -> fun(T,_,result(T1,_,_,_,_))
         string_to_id("x_" -> Xid)
         DefaultPos(-> P)
         New_value_id(P, id_op(Xid) -> XI)
         XI'Type <- T1
         where(form_parm(P, list(single(P, id_op(Xid)), nil)) -> FP)
         where(val_occ(P, XI, nil) -> X)
         Ids_to_patterns(P, Ids -> PS)
         where(LET_BINDING'pattern(P, record_occ_pattern(P, I, nil, PS)) -> LB)
         where(LET_DEFS'list(explicit(P, LB, X), nil) -> LDS)
         Select_as_id(Ids, J -> XJ)
         where(let_expr(P, LDS, val_occ(P, XJ, nil)) -> DEF)
         (|
           eq(ARR, partial)
           (|
	     (| PVSWanted() || SALWanted() |)
	     I'Ident -> id_op(Ident)
	     id_to_string(Ident -> S)
	     Concatenate(S, "?" -> S1)
	     string_to_id(S1 -> Ident1)
	     New_value_id(P, id_op(Ident1) -> I1)
	     I1'Type <- fun(T1, total, result(bool,nil,nil,nil,nil))
	     where(fun_arg(P, list(val_occ(P, XI, nil), nil)) -> Arg)
	     where(pre_cond(P, application(P, val_occ(P, I1, nil), list(Arg, nil))) -> PREC)
	   ||
             where(Ccid -> cons_id(YI))
             Id_of_neq -> I_neq
             where(pre_cond(P, infix_occ(P, X, I_neq, nil, val_occ(P, YI, nil))) -> PREC)
           ||
             string_to_id("y_" -> Yid)
             New_value_id(P, id_op(Yid) -> YI)
             YI'Type <- T
             where(val_occ(P, YI, nil) -> Y)
             where(application(P, val_occ(P, I, nil), list(fun_arg(P, list(Y, nil)), nil)) -> APP)
             Id_of_eq -> I_eq
             where(infix_occ(P, X, I_eq, nil, APP) -> COND)
             where(TYPING'single(P, BINDING'single(P, id_op(Yid)), T) -> TP)
             where(quantified(P,exists,list(TP,nil),restriction(P,COND)) -> PRE)
             where(pre_cond(P, PRE) -> PREC)
           |)
         ||
           where(PRE_CONDITION'nil -> PREC)
         |)

-- generates a parameter "(z,x)"
-- and a definition "let con(x1,...,xn) = x in con(x1,...,z,...,xn) end"
-- and, if ARR is partial, a precondition "exists y : T :- x = con(y)"
-- or, if PVSWanted or SALWanted, a precondition "con?(x)"
'action' Make_reconstructor_definition(Value_id, INT, Value_ids, FUNCTION_ARROW, TYPE_EXPR, CONSTANT_CONSTRUCTOR -> VALUE_DEFINITION)

  'rule' Make_reconstructor_definition(I, J, Ids, ARR, TZ, Ccid ->
                                          expl_fun(list(FP,nil), DEF, nil, PREC, nil, nil)):
         I'Type -> fun(T,_,result(T1,_,_,_,_))
         string_to_id("x_" -> Xid)
         string_to_id("z_" -> Zid)
         DefaultPos(-> P)
         New_value_id(P, id_op(Xid) -> XI)
         XI'Type <- T1
         New_value_id(P, id_op(Zid) -> ZI)
         ZI'Type <- TZ
         where(form_parm(P, list(single(P, id_op(Zid)), list(single(P, id_op(Xid)), nil))) -> FP)
         where(val_occ(P, XI, nil) -> X)
         Ids_to_patterns(P, Ids -> PS)
         where(LET_BINDING'pattern(P, record_occ_pattern(P, I, nil, PS)) -> LB)
         where(LET_DEFS'list(explicit(P, LB, X), nil) -> LDS)
         Insert_as_expr(P, Ids, 1, J, ZI -> ES)
         where(application(P, val_occ(P, I, nil), list(fun_arg(P, ES), nil)) -> E)
         where(let_expr(P, LDS, E) -> DEF)
         (|
           eq(ARR, partial)
           (|
	     (| PVSWanted() || SALWanted() |)
	     I'Ident -> id_op(Ident)
	     id_to_string(Ident -> S)
	     Concatenate(S, "?" -> S1)
	     string_to_id(S1 -> Ident1)
	     New_value_id(P, id_op(Ident1) -> I1)
	     I1'Type <- fun(T1, total, result(bool,nil,nil,nil,nil))
	     where(fun_arg(P, list(val_occ(P, XI, nil), nil)) -> Arg)
	     where(pre_cond(P, application(P, val_occ(P, I1, nil), list(Arg, nil))) -> PREC)
	   ||
             where(Ccid -> cons_id(YI))
             Id_of_neq -> I_neq
             where(pre_cond(P, infix_occ(P, X, I_neq, nil, val_occ(P, YI, nil))) -> PREC)
           ||
             string_to_id("y_" -> Yid)
             New_value_id(P, id_op(Yid) -> YI)
             YI'Type <- T
             where(val_occ(P, YI, nil) -> Y)
             where(application(P, val_occ(P, I, nil), list(fun_arg(P, list(Y, nil)), nil)) -> APP)
             Id_of_eq -> I_eq
             where(infix_occ(P, X, I_eq, nil, APP) -> COND)
             where(TYPING'single(P, BINDING'single(P, id_op(Yid)), T) -> TP)
             where(quantified(P,exists,list(TP,nil),restriction(P,COND)) -> PRE)
             where(pre_cond(P, PRE) -> PREC)
           |)
         ||
           where(PRE_CONDITION'nil -> PREC)
         |)

'action' Select_as_id(Value_ids, INT -> Value_id)

  'rule' Select_as_id(list(I, Ids), J -> I1):
         (|
           eq(J, 1)
           where(I -> I1)
         ||
           Select_as_id(Ids, J-1 -> I1)
         |)

'action' Ids_to_patterns(POS, Value_ids -> PATTERNS)

  'rule' Ids_to_patterns(P, list(I, Ids) -> list(id_pattern(P, Id), PS)):
         I'Ident -> Id
         Ids_to_patterns(P, Ids -> PS)

  'rule' Ids_to_patterns(_, nil -> nil):

'action' Insert_as_expr(POS, Value_ids, INT, INT, Value_id -> VALUE_EXPRS)

  'rule' Insert_as_expr(P, list(I, Ids), K, J, I1 -> list(val_occ(P, I2, nil), ES)):
         (|
           eq(K, J)
           where(I1 -> I2)
         ||
           where(I -> I2)
         |)
         Insert_as_expr(P, Ids, K+1, J, I1 -> ES)

  'rule' Insert_as_expr(_, nil, _, _, _ -> nil):

'action' Apply_dom(POS, VALUE_EXPR -> VALUE_EXPR)

  'rule' Apply_dom(P, V -> prefix_occ(P, I, nil, V)):
         Id_of_dom -> I

'action' Apply_rng(POS, VALUE_EXPR -> VALUE_EXPR)

  'rule' Apply_rng(P, V -> prefix_occ(P, I, nil, V)):
         Id_of_rng -> I

'action' Lookup_op_types(OP -> Value_ids)

  'rule' Lookup_op_types(eq -> list(I, nil)):
         Id_of_eq -> I

  'rule' Lookup_op_types(neq -> list(I, nil)):
         Id_of_neq -> I

  'rule' Lookup_op_types(eqeq -> nil):

  'rule' Lookup_op_types(gt -> list(I1, list(I2, nil))):
         Id_of_gt_int -> I1
         Id_of_gt_real -> I2

  'rule' Lookup_op_types(lt -> list(I1, list(I2, nil))):
         Id_of_lt_int -> I1
         Id_of_lt_real -> I2

  'rule' Lookup_op_types(ge -> list(I1, list(I2, nil))):
         Id_of_ge_int -> I1
         Id_of_ge_real -> I2

  'rule' Lookup_op_types(le -> list(I1, list(I2, nil))):
         Id_of_le_int -> I1
         Id_of_le_real -> I2

  'rule' Lookup_op_types(supset -> list(I, nil)):
         Id_of_supset -> I

  'rule' Lookup_op_types(subset -> list(I, nil)):
         Id_of_subset -> I

  'rule' Lookup_op_types(supseteq -> list(I, nil)):
         Id_of_supseteq -> I

  'rule' Lookup_op_types(subseteq -> list(I, nil)):
         Id_of_subseteq -> I

  'rule' Lookup_op_types(isin -> list(I1, list(I2, list(I3, nil)))):
         Id_of_isin_set -> I1
         Id_of_isin_list -> I2
	 Id_of_isin_map -> I3

  'rule' Lookup_op_types(notisin -> list(I1, list(I2, list(I3, nil)))):
         Id_of_notisin_set -> I1
         Id_of_notisin_list -> I2
	 Id_of_notisin_map -> I3

  'rule' Lookup_op_types(rem -> list(I1, list(I2, list(I3, nil)))):
         Id_of_rem_int -> I1
         Id_of_rem_set -> I2
         Id_of_rem_map -> I3

  'rule' Lookup_op_types(caret -> list(I, nil)):
         Id_of_caret -> I

  'rule' Lookup_op_types(union -> list(I1, list(I2, nil))):
         Id_of_union_set -> I1
         Id_of_union_map -> I2

  'rule' Lookup_op_types(override -> list(I, nil)):
         Id_of_override -> I

  'rule' Lookup_op_types(mult -> list(I1, list(I2, nil))):
         Id_of_mult_int -> I1
         Id_of_mult_real -> I2

  'rule' Lookup_op_types(div -> list(I1, list(I2, list(I3, nil)))):
         Id_of_div_int -> I1
         Id_of_div_real -> I2
         Id_of_div_map -> I3

  'rule' Lookup_op_types(hash -> list(I1, list(I2, nil))):
         Id_of_hash_fun -> I1
         Id_of_hash_map -> I2

  'rule' Lookup_op_types(inter -> list(I, nil)):
         Id_of_inter -> I

  'rule' Lookup_op_types(exp -> list(I1, list(I2, nil))):
         Id_of_exp_int -> I1
         Id_of_exp_real -> I2

  'rule' Lookup_op_types(abs -> list(I1, list(I2, nil))):
         Id_of_abs_int -> I1
         Id_of_abs_real -> I2

  'rule' Lookup_op_types(int -> list(I, nil)):
         Id_of_int -> I

  'rule' Lookup_op_types(real -> list(I, nil)):
         Id_of_real -> I

  'rule' Lookup_op_types(card -> list(I, nil)):
         Id_of_card -> I

  'rule' Lookup_op_types(len -> list(I, nil)):
         Id_of_len -> I

  'rule' Lookup_op_types(inds -> list(I, nil)):
         Id_of_inds -> I

  'rule' Lookup_op_types(elems -> list(I, nil)):
         Id_of_elems -> I

  'rule' Lookup_op_types(hd -> list(I1, list(I2, list(I3, nil)))):
         Id_of_hd_set -> I1
         Id_of_hd_list -> I2
         Id_of_hd_map -> I3

  'rule' Lookup_op_types(tl -> list(I, nil)):
         Id_of_tl -> I

  'rule' Lookup_op_types(dom -> list(I, nil)):
         Id_of_dom -> I

  'rule' Lookup_op_types(rng -> list(I, nil)):
         Id_of_rng -> I

  'rule' Lookup_op_types(wait -> Ids):
         (|
           IsTimed()
           Id_of_wait_time -> I1
           Id_of_wait_int -> I2
           where(Value_ids'list(I1, list(I2, nil)) -> Ids)
                                   
         ||
           where(Value_ids'nil -> Ids)
         |)

  'rule' Lookup_op_types(plus -> list(I1, list(I2, list(I3, list(I4, nil))))):
         Id_of_plus_inf_int -> I1
         Id_of_plus_inf_real -> I2
         Id_of_plus_pre_int -> I3
         Id_of_plus_pre_real -> I4

  'rule' Lookup_op_types(minus -> list(I1, list(I2, list(I3, list(I4, nil))))):
         Id_of_minus_inf_int -> I1
         Id_of_minus_inf_real -> I2
         Id_of_minus_pre_int -> I3
         Id_of_minus_pre_real -> I4

'action' Lookup_id_types(IDENT -> Value_ids)

  'rule' Lookup_id_types(Id -> list(I, nil)):
	 Is_LTL_Wanted()
	 Id_of_X -> I
	 I'Ident -> id_op(Idx)
	 eq(Idx, Id)

  'rule' Lookup_id_types(Id -> list(I, nil)):
	 Is_LTL_Wanted()
	 Id_of_G -> I
	 I'Ident -> id_op(Idg)
	 eq(Idg, Id)


  'rule' Lookup_id_types(Id -> list(I, nil)):
	 Is_LTL_Wanted()
	 Id_of_F -> I
	 I'Ident -> id_op(Idf)
	 eq(Idf, Id)

-- Abigail added two rules for U and R

'rule' Lookup_id_types(Id -> list(I, nil)):
	 Is_LTL_Wanted()
	 Id_of_U -> I
	 I'Ident -> id_op(Idu)
	 eq(Idu, Id)

'rule' Lookup_id_types(Id -> list(I, nil)):
	 Is_LTL_Wanted()
	 Id_of_R -> I
	 I'Ident -> id_op(Idr)
	 eq(Idr, Id)

-- CWG added W (weak Until)

'rule' Lookup_id_types(Id -> list(I, nil)):
	 Is_LTL_Wanted()
	 Id_of_W -> I
	 I'Ident -> id_op(Idw)
	 eq(Idw, Id)



--------------------------------------------

  'rule' Lookup_id_types(Id -> nil):
         --print("Ikke godt")
/*print(Id)
Id_of_X -> X
         print(X)
X'Ident -> id_op(X3)
print(X3)
--id_to_string(X -> X2)
--print(X2)
Id_of_W -> W
         print(W)
--id_to_string(W -> W2)
--print(W2)
Id_of_R -> R
--id_to_string(R -> R2)
print(R)
--print(R2)
Id_of_U -> U
print(U)
--id_to_string(U -> U2)
--print(U2)
Id_of_G -> G
print(G)
--id_to_string(G -> G2)
--print(G2)
Id_of_F -> F
print(F)
--id_to_string(D -> F2)
--print(F2)*/

--------------------------------------------------------------------
-- Environments
--------------------------------------------------------------------

'type' CHECK
        check, nil

'action' Get_current_env(-> CLASS_ENV)

  'rule' Get_current_env(-> CE1)
         Current -> current_env(CE,C1)
         Extend_paths -> list(Path, Paths)
         Get_current_path_env(CE, Path -> CE1)

'action' Get_current_path_env(CLASS_ENV, PATH -> CLASS_ENV)

  'rule' Get_current_path_env(CE, nil -> CE):

  'rule' Get_current_path_env(instantiation_env(_, CE), Path -> CE1):
         Get_current_path_env(CE, Path -> CE1)

  'rule' Get_current_path_env(extend_env(CE1, CE2, W, AD), left(Path) -> CE):
         Get_current_path_env(CE1, Path -> CE)

  'rule' Get_current_path_env(extend_env(CE1, CE2, W, AD), right(Path) -> CE):
         Get_current_path_env(CE2, Path -> CE)

'action' Set_current_env(CLASS_ENV)

  'rule' Set_current_env(CE1):
         Current -> C
         where(C -> current_env(CE,C1))
         Extend_paths -> list(Path, Paths)
         Set_current_path_env(CE, Path, CE1 -> CE2)
         Current <- current_env(CE2,C1)

'action' Set_current_path_env(CLASS_ENV, PATH, CLASS_ENV -> CLASS_ENV)

  'rule' Set_current_path_env(CE, nil, CE1 -> CE1):

  'rule' Set_current_path_env(instantiation_env(PF, CE), Path, CE1 -> instantiation_env(PF, CE2)):
         Set_current_path_env(CE, Path, CE1 -> CE2)

  'rule' Set_current_path_env(extend_env(CE1, CE2, W, AD), left(Path), CE -> extend_env(CE11, CE2, W, AD)):
         Set_current_path_env(CE1, Path, CE -> CE11)

  'rule' Set_current_path_env(extend_env(CE1, CE2, W, AD), right(Path), CE -> extend_env(CE1, CE21, W, AD)):
         Set_current_path_env(CE2, Path, CE -> CE21)

'action' Get_current_types(-> TYPE_ENV)

  'rule' Get_current_types(-> TYP):
         Get_current_env(-> CE)
         Get_current_env_types(CE -> TYP)

'action' Get_current_env_types(CLASS_ENV -> TYPE_ENV)

  'rule' Get_current_env_types(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC,_, _,WITH, AD) -> TYP):

  'rule' Get_current_env_types(instantiation_env(PF, CE) -> TYP):
         Get_current_env_types(CE -> TYP)

'action' Get_env_types(CLASS_ENV -> TYPE_ENV)

  'rule' Get_env_types(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, _,WITH, AD) -> TYP):

  'rule' Get_env_types(extend_env(CE1, CE2, WITH, AD) -> TYP):
         Get_env_types(CE1 -> TYP1)
         Get_env_types(CE2 -> TYP2)
         Type_env_concat(TYP1, TYP2 -> TYP)

  'rule' Get_env_types(instantiation_env(PF, CE) -> TYP):
         Get_env_types(CE -> TYP)

'action' Type_env_concat(TYPE_ENV, TYPE_ENV -> TYPE_ENV)

  'rule' Type_env_concat(type_env(I, TE1), TE2 -> type_env(I,TE)):
         Type_env_concat(TE1, TE2 -> TE)

  'rule' Type_env_concat(nil, TE -> TE):


'action' Set_current_types(TYPE_ENV)

  'rule' Set_current_types(TYP1):
         Get_current_env(-> CE)
         Set_current_env_types(CE, TYP1 -> CE1)
         Set_current_env(CE1)

'action' Set_current_env_types(CLASS_ENV, TYPE_ENV -> CLASS_ENV)

  'rule' Set_current_env_types(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD), TYP1 ->
                                      basic_env(TYP1, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD)):

  'rule' Set_current_env_types(instantiation_env(PF, CE), TYP -> instantiation_env(PF, CE1)):
         Set_current_env_types(CE, TYP -> CE1)
  
'action' Get_current_values(-> VALUE_ENVS)

  'rule' Get_current_values(-> VAL):
         Get_current_env(-> CE)
         Get_current_env_values(CE -> VAL)


'action' Get_current_env_values(CLASS_ENV -> VALUE_ENVS)

  'rule' Get_current_env_values(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, _, WITH, AD) -> VAL):

  'rule' Get_current_env_values(instantiation_env(PF, CE) -> VAL):
         Get_current_env_values(CE -> VAL)


'action' Get_current_top_values(-> Value_ids)

  'rule' Get_current_top_values(-> VAL):
         Get_current_env(-> CE)
         Get_env_top_values(CE -> VAL)


'action' Get_env_top_values(CLASS_ENV -> Value_ids)

  'rule' Get_env_top_values(basic_env(TYP, list(VE,VES), VAR, CH, MOD, AX, TC, TS, _, WITH, AD) -> VE):

  'rule' Get_env_top_values(extend_env(CE1, CE2, WITH, AD) -> VE):
         Get_env_top_values(CE1 -> VE1)
         Get_env_top_values(CE2 -> VE2)
         Value_env_concat(VE1, VE2 -> VE)

  'rule' Get_env_top_values(instantiation_env(PF, CE) -> VE):
         Get_env_top_values(CE -> VE)

'action' Value_env_concat(Value_ids, Value_ids -> Value_ids)

  'rule' Value_env_concat(list(I, VE1), VE2 -> list(I,VE)):
         Value_env_concat(VE1, VE2 -> VE)

  'rule' Value_env_concat(nil, VE -> VE):

'action' Set_current_values(VALUE_ENVS)

  'rule' Set_current_values(VAL1):
         Get_current_env(-> CE)
         Set_current_env_values(CE, VAL1 -> CE1)
         Set_current_env(CE1)

'action' Set_current_env_values(CLASS_ENV, VALUE_ENVS -> CLASS_ENV)

  'rule' Set_current_env_values(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop,  WITH, AD), VAL1 ->
                                      basic_env(TYP, VAL1, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD)):

  'rule' Set_current_env_values(instantiation_env(PF, CE), VAL -> instantiation_env(PF, CE1)):
         Set_current_env_values(CE, VAL -> CE1)

'action' Get_current_variables(-> VARIABLE_ENV)

  'rule' Get_current_variables(-> VAR):
         Get_current_env(-> CE)
         Get_current_env_variables(CE -> VAR)


'action' Get_current_env_variables(CLASS_ENV -> VARIABLE_ENV)

  'rule' Get_current_env_variables(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS,  _, WITH, AD) -> VAR):

  'rule' Get_current_env_variables(instantiation_env(PF, CE) -> VAR):
         Get_current_env_variables(CE -> VAR)

'action' Get_env_variables(CLASS_ENV -> VARIABLE_ENV)

  'rule' Get_env_variables(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, _, WITH, AD) -> VAR)

  'rule' Get_env_variables(extend_env(CE1, CE2, WITH, AD) -> VAR):
         Get_env_variables(CE1 -> VAR1)
         Get_env_variables(CE2 -> VAR2)
         Variable_env_concat(VAR1, VAR2 -> VAR)

  'rule' Get_env_variables(instantiation_env(PF, CE) -> VAR):
         Get_env_variables(CE -> VAR)

'action' Variable_env_concat(VARIABLE_ENV, VARIABLE_ENV -> VARIABLE_ENV)

  'rule' Variable_env_concat(variable_env(I, VE1), VE2 -> variable_env(I,VE)):
         Variable_env_concat(VE1, VE2 -> VE)

  'rule' Variable_env_concat(nil, VE -> VE):

'action' Set_current_variables(VARIABLE_ENV)

  'rule' Set_current_variables(VAR1):
         Get_current_env(-> CE)
         Set_current_env_variables(CE, VAR1 -> CE1)
         Set_current_env(CE1)

'action' Set_current_env_variables(CLASS_ENV, VARIABLE_ENV -> CLASS_ENV)

  'rule' Set_current_env_variables(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD), VAR1 ->
                                      basic_env(TYP, VAL, VAR1, CH, MOD, AX, TC, TS, Prop, WITH, AD)):

  'rule' Set_current_env_variables(instantiation_env(PF, CE), VAR -> instantiation_env(PF, CE1)):
         Set_current_env_variables(CE, VAR -> CE1)

'action' Get_current_channels(-> CHANNEL_ENV)

  'rule' Get_current_channels(-> CH):
         Get_current_env(-> CE)
         Get_current_env_channels(CE -> CH)


'action' Get_current_env_channels(CLASS_ENV -> CHANNEL_ENV)

  'rule' Get_current_env_channels(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, _, WITH, AD) -> CH):

  'rule' Get_current_env_channels(instantiation_env(PF, CE) -> CH):
         Get_current_env_channels(CE -> CH)

'action' Get_env_channels(CLASS_ENV -> CHANNEL_ENV)

  'rule' Get_env_channels(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, _, WITH, AD) -> CH):

  'rule' Get_env_channels(extend_env(CE1, CE2, WITH, AD) -> CH):
         Get_env_channels(CE1 -> CH1)
         Get_env_channels(CE2 -> CH2)
         Channel_env_concat(CH1, CH2 -> CH)

  'rule' Get_env_channels(instantiation_env(PF, CE) -> CH):
         Get_env_channels(CE -> CH)

'action' Channel_env_concat(CHANNEL_ENV, CHANNEL_ENV -> CHANNEL_ENV)

  'rule' Channel_env_concat(channel_env(I, CHE1), CHE2 -> channel_env(I,CHE)):
         Channel_env_concat(CHE1, CHE2 -> CHE)

  'rule' Channel_env_concat(nil, CHE -> CHE):

'action' Set_current_channels(CHANNEL_ENV)

  'rule' Set_current_channels(CH1):
         Get_current_env(-> CE)
         Set_current_env_channels(CE, CH1 -> CE1)
         Set_current_env(CE1)

'action' Set_current_env_channels(CLASS_ENV, CHANNEL_ENV -> CLASS_ENV)

  'rule' Set_current_env_channels(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD), CH1 ->
                                      basic_env(TYP, VAL, VAR, CH1, MOD, AX, TC, TS, Prop, WITH, AD)):

  'rule' Set_current_env_channels(instantiation_env(PF, CE), CH -> instantiation_env(PF, CE1)):
         Set_current_env_channels(CE, CH -> CE1)

'action' Get_current_modules(-> MODULE_ENV)

  'rule' Get_current_modules(-> MOD):
         Get_current_env(-> CE)
         Get_current_env_modules(CE -> MOD)


'action' Get_current_env_modules(CLASS_ENV -> MODULE_ENV)

  'rule' Get_current_env_modules(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, _, WITH, AD) -> MOD):

  'rule' Get_current_env_modules(instantiation_env(PF, CE) -> MOD):
         Get_current_env_modules(CE -> MOD)

'action' Get_env_modules(CLASS_ENV -> MODULE_ENV)

  'rule' Get_env_modules(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD) -> MOD):

  'rule' Get_env_modules(extend_env(CE1, CE2, WITH, AD) -> MOD):
         Get_env_modules(CE1 -> MOD1)
         Get_env_modules(CE2 -> MOD2)
         Module_env_concat(MOD1, MOD2 -> MOD)

  'rule' Get_env_modules(instantiation_env(PF, CE) -> MOD):
         Get_env_modules(CE -> MOD)

'action' Module_env_concat(MODULE_ENV, MODULE_ENV -> MODULE_ENV)

  'rule' Module_env_concat(object_env(I, ME1), ME2 -> object_env(I,ME)):
         Module_env_concat(ME1, ME2 -> ME)

  'rule' Module_env_concat(nil, ME -> ME):

'action' Set_current_modules(MODULE_ENV)

  'rule' Set_current_modules(MOD1):
         Get_current_env(-> CE)
         Set_current_env_modules(CE, MOD1 -> CE1)
         Set_current_env(CE1)

'action' Set_current_env_modules(CLASS_ENV, MODULE_ENV -> CLASS_ENV)

  'rule' Set_current_env_modules(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD), MOD1 ->
                                      basic_env(TYP, VAL, VAR, CH, MOD1, AX, TC, TS, Prop, WITH, AD)):

  'rule' Set_current_env_modules(instantiation_env(PF, CE), MOD -> instantiation_env(PF, CE1)):
         Set_current_env_modules(CE, MOD -> CE1)

'action' Get_current_axioms(-> AXIOM_ENV)

  'rule' Get_current_axioms(-> AX):
         Get_current_env(-> CE)
         Get_current_env_axioms(CE -> AX)


'action' Get_current_env_axioms(CLASS_ENV -> AXIOM_ENV)

  'rule' Get_current_env_axioms(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, _, WITH, AD) -> AX):

  'rule' Get_current_env_axioms(instantiation_env(PF, CE) -> AX):
         Get_current_env_axioms(CE -> AX)

'action' Get_env_axioms(CLASS_ENV -> AXIOM_ENV)

  'rule' Get_env_axioms(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, _, WITH, AD) -> AX):

  'rule' Get_env_axioms(extend_env(CE1, CE2, WITH, AD) -> AX):
         Get_env_axioms(CE1 -> AX1)
         Get_env_axioms(CE2 -> AX2)
         Axiom_env_concat(AX1, AX2 -> AX)

  'rule' Get_env_axioms(instantiation_env(PF, CE) -> AX):
         Get_env_axioms(CE -> AX)

'action' Axiom_env_concat(AXIOM_ENV, AXIOM_ENV -> AXIOM_ENV)

  'rule' Axiom_env_concat(axiom_env(I, AE1), AE2 -> axiom_env(I,AE)):
         Axiom_env_concat(AE1, AE2 -> AE)

  'rule' Axiom_env_concat(nil, AE -> AE):

'action' Set_current_axioms(AXIOM_ENV)

  'rule' Set_current_axioms(AX1):
         Get_current_env(-> CE)
         Set_current_env_axioms(CE, AX1 -> CE1)
         Set_current_env(CE1)

'action' Set_current_env_axioms(CLASS_ENV, AXIOM_ENV -> CLASS_ENV)

  'rule' Set_current_env_axioms(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD), AX1 ->
                                      basic_env(TYP, VAL, VAR, CH, MOD, AX1, TC, TS, Prop, WITH, AD)):

  'rule' Set_current_env_axioms(instantiation_env(PF, CE), AX -> instantiation_env(PF, CE1)):
         Set_current_env_axioms(CE, AX -> CE1)

'action' Get_current_test_cases(ALL_TOP -> TEST_CASE_ENV)

  'rule' Get_current_test_cases(AT -> TC):
         Get_current_env(-> CE)
         Get_env_test_cases(CE, AT -> TC)


'action' Get_env_test_cases(CLASS_ENV, ALL_TOP -> TEST_CASE_ENV)

  'rule' Get_env_test_cases(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, _, WITH, AD), AT -> TC):

-- ignore first part of extend if it is an instantiation and only top wanted
  'rule' Get_env_test_cases(extend_env(instantiation_env(_,_), CE, WITH, AD), top -> TC):
	 Get_env_test_cases(CE, top -> TC)

  'rule' Get_env_test_cases(extend_env(CE1, CE2, WITH, AD), AT -> TC):
         Get_env_test_cases(CE1, AT -> TC1)
         Get_env_test_cases(CE2, AT -> TC2)
	 -- sml translator assumes test cases in reverse order
         Test_case_env_concat(TC2, TC1 -> TC)

  'rule' Get_env_test_cases(instantiation_env(PF, CE), AT -> TC):
         Get_env_test_cases(CE, AT -> TC)

'action' Test_case_env_concat(TEST_CASE_ENV, TEST_CASE_ENV -> TEST_CASE_ENV)

  'rule' Test_case_env_concat(test_case_env(I, TC1), TC2 -> test_case_env(I,TC)):
         Test_case_env_concat(TC1, TC2 -> TC)

  'rule' Test_case_env_concat(nil, TC -> TC):

'action' Set_current_test_cases(TEST_CASE_ENV)

  'rule' Set_current_test_cases(TC1):
         Get_current_env(-> CE)
         Set_current_env_test_cases(CE, TC1 -> CE1)
         Set_current_env(CE1)

'action' Set_current_env_test_cases(CLASS_ENV, TEST_CASE_ENV -> CLASS_ENV)

  'rule' Set_current_env_test_cases(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD), TC1 ->
                                      basic_env(TYP, VAL, VAR, CH, MOD, AX, TC1, TS, Prop, WITH, AD)):

  'rule' Set_current_env_test_cases(instantiation_env(PF, CE), TC -> instantiation_env(PF, CE1)):
         Set_current_env_test_cases(CE, TC -> CE1)

--------------------------------------------------------------------------------------------------------
-- Transition system environment handling
--------------------------------------------------------------------------------------------------------
'action' Get_current_transition_systems(ALL_TOP -> TRANS_SYS_ENV)

  'rule' Get_current_transition_systems(AT -> TC):
         Get_current_env(-> CE)
         Get_env_transition_systems(CE, AT -> TC)


'action' Get_env_transition_systems(CLASS_ENV, ALL_TOP -> TRANS_SYS_ENV)

  'rule' Get_env_transition_systems(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC,TS, _, WITH, AD), AT -> TS):

-- ignore first part of extend if it is an instantiation and only top wanted
  'rule' Get_env_transition_systems(extend_env(instantiation_env(_,_), CE, WITH, AD), top -> TC):
	 Get_env_transition_systems(CE, top -> TC)

  'rule' Get_env_transition_systems(extend_env(CE1, CE2, WITH, AD), AT -> TC):
         Get_env_transition_systems(CE1, AT -> TC1)
         Get_env_transition_systems(CE2, AT -> TC2)
	 -- sml translator assumes test cases in reverse order
         Trans_sys_env_concat(TC2, TC1 -> TC)

  'rule' Get_env_transition_systems(instantiation_env(PF, CE), AT -> TC):
         Get_env_transition_systems(CE, AT -> TC)

'action' Trans_sys_env_concat(TRANS_SYS_ENV, TRANS_SYS_ENV -> TRANS_SYS_ENV)

  'rule' Trans_sys_env_concat(trans_sys_env(I, TC1), TC2 -> trans_sys_env(I,TC)):
         Trans_sys_env_concat(TC1, TC2 -> TC)

  'rule' Trans_sys_env_concat(nil, TC -> TC):

'action' Set_current_transition_system(TRANS_SYS_ENV)

  'rule' Set_current_transition_system(TC1):
         Get_current_env(-> CE)
         Set_current_env_transition_system(CE, TC1 -> CE1)
         Set_current_env(CE1)

'action' Set_current_env_transition_system(CLASS_ENV, TRANS_SYS_ENV -> CLASS_ENV)

  'rule' Set_current_env_transition_system(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD), TS1 ->
                                      basic_env(TYP, VAL, VAR, CH, MOD, AX, TC,TS1, Prop, WITH, AD)):

  'rule' Set_current_env_transition_system(instantiation_env(PF, CE), TC -> instantiation_env(PF, CE1)):
         Set_current_env_transition_system(CE, TC -> CE1)

-- Transition system look-up (inside environmet)

'action' Get_Transition_System(IDENT, TRANS_SYS_ENV -> OPT_TRANS_SYS_ID)
	 
  'rule' Get_Transition_System(Id, trans_sys_env(TSId, Rest) -> Result)
	 TSId'Ident -> TSIdent
	 (|
		eq(TSIdent, Id)
		where(ts_id(TSId) -> Result)
	 ||
		Get_Transition_System(Id, Rest -> Result)
	 |)

  'rule' Get_Transition_System(_, nil -> nil)

--------------------------------------------------------------------------------------------------------
-- LTL properties environment handling
--------------------------------------------------------------------------------------------------------
'action' Get_current_properties(ALL_TOP -> PROPERTY_ENV)

  'rule' Get_current_properties(AT -> TC):
         Get_current_env(-> CE)
         Get_env_properties(CE, AT -> TC)


'action' Get_env_properties(CLASS_ENV, ALL_TOP -> PROPERTY_ENV)

  'rule' Get_env_properties(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC,TS, Prop, WITH, AD), AT -> Prop):

-- ignore first part of extend if it is an instantiation and only top wanted
  'rule' Get_env_properties(extend_env(instantiation_env(_,_), CE, WITH, AD), top -> Prop):
	 Get_env_properties(CE, top -> Prop)

  'rule' Get_env_properties(extend_env(CE1, CE2, WITH, AD), AT -> TC):
         Get_env_properties(CE1, AT -> TC1)
         Get_env_properties(CE2, AT -> TC2)
	 -- sml translator assumes test cases in reverse order
         Properties_env_concat(TC2, TC1 -> TC)

  'rule' Get_env_properties(instantiation_env(PF, CE), AT -> TC):
         Get_env_properties(CE, AT -> TC)

'action' Properties_env_concat(PROPERTY_ENV, PROPERTY_ENV -> PROPERTY_ENV)

  'rule' Properties_env_concat(prop_env(I, TC1), TC2 -> prop_env(I,TC)):
         Properties_env_concat(TC1, TC2 -> TC)

  'rule' Properties_env_concat(nil, TC -> TC):

'action' Set_current_property(PROPERTY_ENV)

  'rule' Set_current_property(TC1):
         Get_current_env(-> CE)
         Set_current_env_property(CE, TC1 -> CE1)
         Set_current_env(CE1)

'action' Set_current_env_property(CLASS_ENV, PROPERTY_ENV -> CLASS_ENV)

  'rule' Set_current_env_property(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, _, WITH, AD), Prop ->
                                      basic_env(TYP, VAL, VAR, CH, MOD, AX, TC,TS, Prop, WITH, AD)):

  'rule' Set_current_env_property(instantiation_env(PF, CE), Prop -> instantiation_env(PF, CE1)):
         Set_current_env_property(CE, Prop -> CE1)

--------------------------------------------------------------------------------------------------------
'action' Get_current_with(-> OBJECT_EXPRS)

  'rule' Get_current_with(-> WITH):
         Get_current_env(-> CE)
         Get_env_with(CE -> WITH)


'action' Get_env_with(CLASS_ENV -> OBJECT_EXPRS)

  'rule' Get_env_with(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, _, WITH, AD) -> WITH):

  'rule' Get_env_with(extend_env(CE1, CE2, WITH, AD) -> WITH):

  'rule' Get_env_with(instantiation_env(PF, CE) -> WITH):
         Get_env_with(CE -> WITH)

'action' Set_current_with(OBJECT_EXPRS)

  'rule' Set_current_with(WITH1):
         Get_current_env(-> CE)
         Set_env_with(CE, WITH1 -> CE1)
         Set_current_env(CE1)

'action' Set_env_with(CLASS_ENV, OBJECT_EXPRS -> CLASS_ENV)

  'rule' Set_env_with(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD), WITH1 ->
                                      basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH1, AD)):

  'rule' Set_env_with(extend_env(CE1, CE2, WITH, AD), WITH1 ->
                                         extend_env(CE1, CE2, WITH1, AD)):

  'rule' Set_env_with(instantiation_env(PF, CE), WITH -> instantiation_env(PF, CE1)):
         Set_env_with(CE, WITH -> CE1)

'action' Get_current_adapts(-> ADAPTS)

  'rule' Get_current_adapts(-> AD):
         Get_current_env(-> CE)
         Get_env_adapts(CE -> AD)

'action' Get_env_adapts(CLASS_ENV -> ADAPTS)

  'rule' Get_env_adapts(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, _, WITH, AD) -> AD):

  'rule' Get_env_adapts(extend_env(CE1, CE2, WITH, AD) -> AD):

  'rule' Get_env_adapts(instantiation_env(PF, CE) -> AD):
         Get_env_adapts(CE -> AD)

'action' Set_current_adapts(ADAPTS)

  'rule' Set_current_adapts(AD1):
         Get_current_env(-> CE)
         Set_env_adapts(CE, AD1 -> CE1)
         Set_current_env(CE1)

'action' Set_env_adapts(CLASS_ENV, ADAPTS -> CLASS_ENV)

  'rule' Set_env_adapts(basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD), AD1 ->
                                      basic_env(TYP, VAL, VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD1)):

  'rule' Set_env_adapts(extend_env(CE1, CE2, WITH, AD), AD1 ->
                                         extend_env(CE1, CE2, WITH,
                                         AD1)):

  'rule' Set_env_adapts(instantiation_env(PF, CE), AD -> instantiation_env(PF, CE1)):
         Set_env_adapts(CE, AD -> CE1)

--------------------------------------------------------------------
-- Extend
--------------------------------------------------------------------

'action' Start_extend(OBJECT_EXPRS)

  'rule' Start_extend(W):
         Current -> current_env(CE, C)
         Extend_paths -> list(Path, Paths)
         (|
           where(CE -> instantiation_env(PF, CEI))
           Start_extend_env(CEI, W, Path -> CE1)
           Current <- current_env(instantiation_env(PF, CE1), C)
         ||
           Start_extend_env(CE, W, Path -> CE1)
           Current <- current_env(CE1, C)
         |)
         Add_left(Path -> Path1)
         Extend_paths <- list(Path1, Paths)

'action' Start_extend_env(CLASS_ENV, OBJECT_EXPRS, PATH -> CLASS_ENV)

  'rule' Start_extend_env(CE, W, nil -> extend_env(CE, basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,W,nil), W, nil)):

  'rule' Start_extend_env(extend_env(CE1, CE2, W, AD), W1, left(Path) -> extend_env(CE11, CE2, W, AD)):
         Start_extend_env(CE1, W1, Path -> CE11)

  'rule' Start_extend_env(extend_env(CE1, CE2, W, AD), W1, right(Path) -> extend_env(CE1, CE21, W, AD)):
         Start_extend_env(CE2, W1, Path -> CE21)

-- Moving from extend CE1 with CE2 end to CE1
'action' In_left

  'rule' In_left:
         Extend_paths -> list(Path, Paths)
         Add_left(Path -> Path1)
         Extend_paths <- list(Path1, Paths)

-- Within extend CE1 with CE2 end moving from CE1 to CE2
'action' Left_right

  'rule' Left_right:
         Extend_paths -> list(Path, Paths)
         Shift_right(Path -> Path1)
         Extend_paths <- list(Path1, Paths)

-- Within extend CE1 with CE2 end moving out from CE2
'action' Out_right

  'rule' Out_right:
         Extend_paths -> list(Path, Paths)
         Remove_right(Path -> Path1)
         Extend_paths <- list(Path1, Paths)

'action' Add_left(PATH -> PATH)

  'rule' Add_left(nil -> left(nil)):

  'rule' Add_left(left(Path) -> left(Path1)):
         Add_left(Path -> Path1)

  'rule' Add_left(right(Path) -> right(Path1)):
         Add_left(Path -> Path1)

'action' Shift_right(PATH -> PATH)

  'rule' Shift_right(left(nil) -> right(nil)):

  'rule' Shift_right(left(Path) -> left(Path1)):
         Shift_right(Path -> Path1)

  'rule' Shift_right(right(Path) -> right(Path1)):
         Shift_right(Path -> Path1)

'action' Remove_right(PATH -> PATH)

  'rule' Remove_right(right(nil) -> nil):

  'rule' Remove_right(left(Path) -> left(Path1)):
         Remove_right(Path -> Path1)

  'rule' Remove_right(right(Path) -> right(Path1)):
         Remove_right(Path -> Path1)

-- second parameter indicates whether up step was from left or right
'action' Up1(PATH -> PATH, PATH)

  'rule' Up1(left(nil) -> nil, left(nil)):

  'rule' Up1(right(nil) -> nil, right(nil)):

  'rule' Up1(left(Path) -> left(Path1), Path2):
         Up1(Path -> Path1, Path2)

  'rule' Up1(right(Path) -> right(Path1), Path2):
         Up1(Path -> Path1, Path2)

'action' Out_scope(PATH -> PATH)

  'rule' Out_scope(left(Path) -> nil):
         All_left(Path)  

  'rule' Out_scope(left(Path) -> left(Path1)):
         Out_scope(Path -> Path1)

  'rule' Out_scope(right(Path) -> left(nil)):
         All_left(Path)

  'rule' Out_scope(right(Path) -> right(Path1)):
         Out_scope(Path -> Path1)

'condition' All_left(PATH)

  'rule' All_left(left(Path)):
         All_left(Path)

  'rule' All_left(nil):

---------------------------------------------------------------------------
-- Object lookup
---------------------------------------------------------------------------

-- returns object in scope
-- Looks in current environment, 
-- then formal parameters if no fitting encountered, then globals


'action' Get_object_id(OBJECT_EXPR -> OPT_OBJECT_ID, PARAM_FIT)

  'rule' Get_object_id(Obj -> Oid, PF):
         Get_object_id1(Obj, ownenv, ownclass -> Oid, PF)
 
'action' Get_object_id1(OBJECT_EXPR, OWNENV, OWNCLASS -> OPT_OBJECT_ID, PARAM_FIT)

  'rule' Get_object_id1(obj_name(name(P, id_op(Id))), Ownenv, Ownclass -> Oid, PF):
         Current -> C
         Extend_paths -> Paths
         Lookup_object_in_current_env(Id, C, Paths, Ownenv, Ownclass -> Oid1, PF1)
         (|
           ne(Oid1, nil)
           where(Oid1 -> Oid)
           where(PF1 -> PF)
         ||
           (|
             eq(PF1, nil)
             Parameters -> PARMS
             Lookup_object_in_module(Id, PARMS -> Oid2)
             ne(Oid2, nil)
             where(Oid2 -> Oid)
             where(PARAM_FIT'nil -> PF)
           ||
             Globals -> G
             Lookup_object_in_module(Id, G -> Oid)
             where(PARAM_FIT'nil -> PF)
           |)
         |)

  'rule' Get_object_id1(obj_appl(Obj, A), Ownenv, Ownclass -> Oid, PF):
         Get_object_id1(Obj, Ownenv, Ownclass -> Oid, PF)

  'rule' Get_object_id1(obj_array(TS, Obj), Ownenv, Ownclass -> Oid, PF):
         Get_object_id1(Obj, Ownenv, Ownclass -> Oid, PF)

  'rule' Get_object_id1(obj_fit(Obj, F), Ownenv, Ownclass -> Oid, PF):
         Get_object_id1(Obj, Ownenv, Ownclass -> Oid, PF)

  'rule' Get_object_id1(obj_name(qual_name(P, Obj, id_op(Id))), Ownenv, Ownclass -> Oid, PF):
         Split_name(qual_name(P, Obj, id_op(Id)) -> Obj1, N)
-- debug
-- Putmsg("Looking for object ")
-- Print_name(N)
-- Putmsg(" in object ")
-- Print_object(Obj1)
-- Putnl()
         Get_object_id1(Obj1, Ownenv, Ownclass -> Oid1, PF1)
         (|
           where(Oid1 -> object_id(I))
           I'Env -> CE
           (|
             ne(PF1, nil)
             Fit_name(N, I, PF1 -> N1)
           ||
             where(N -> N1)
           |)
-- debug
-- Putmsg("Found object ")
-- Print_object(Obj1)
-- Putnl()
-- print(Obj1)
-- Putnl()
-- Putmsg("with env")
-- Putnl()
-- print(CE)
-- Putmsg("and looking for name ")
-- Print_name(N1)
           Lookup_object_in_env(obj_name(N1), CE, nil -> Oid)
-- (|
-- where(Oid -> object_id(I1))
-- Putmsg(" and found ")
-- print(I1)
-- ||
-- Putmsg(" but not found")
-- |)
-- Putnl()
           where(PARAM_FIT'nil -> PF)
         ||
           where(Oid1 -> Oid)
           where(PF1 -> PF)
         |)

'action' Lookup_object_in_params(IDENT, PARAM_FIT -> OPT_OBJECT_ID, PARAM_FIT)

  'rule' Lookup_object_in_params(Id, no_parms -> nil, no_parms):

  'rule' Lookup_object_in_params(Id, param_fit(OI, I, Obj, AD, PF) -> Oid, PF1):
         OI'Ident -> Id1
         (|
           eq(Id, Id1)
           where(object_id(I) -> Oid)
           where(param_fit(OI, I, Obj, AD, PF) -> PF1)
         ||
           Lookup_object_in_params(Id, PF -> Oid, PF1)
         |)

  'rule' Lookup_object_in_params(Id, nil -> nil, nil):

'action' Object_type_check(OBJECT_EXPR, Object_id)

  'rule' Object_type_check(obj_name(N), I):
         [|
           I'Params -> param_type(T)
           Object_pos(obj_name(N) -> P)
           Puterror(P)
           Putmsg("Only element object expressions may be used as qualifiers")
           Putnl()
         |]
         
  'rule' Object_type_check(obj_fit(Obj, F), I):
         Object_type_check(Obj, I)

  'rule' Object_type_check(obj_appl(Obj, A), I):
         Object_pos(Obj -> P)
         (|
           Object_param_type(Obj, I -> param_type(T))
           (|
             where(A -> list(V, nil))
           ||
             where(VALUE_EXPR'product(P, A) -> V)
           |)
           Make_results(V -> RS)
           Type_check(P, result(T,nil,nil,nil,nil), RS -> RS1)
         ||
           Puterror(P)
           I'Ident -> Id
           Putmsg("Object ")
           Print_id(Id)
           Putmsg(" is not an array object")
           Putnl()
         |)

  'rule' Object_type_check(obj_array(_, Obj), _):
         Object_pos(Obj -> P)
         Puterror(P)
         Putmsg("Only element object expressions may be used as qualifiers")
         Putnl()

'action' Object_param_type(OBJECT_EXPR, Object_id -> PARAM_TYPE)

  'rule' Object_param_type(obj_name(N), I -> PT):
         I'Params -> PT
	 [|
	   where(N -> qual_name(_, Obj1, _))
	   Get_object_id(Obj1 -> object_id(I1), _)
	   Object_type_check(Obj1, I1)
	 |]

  'rule' Object_param_type(obj_fit(Obj, F), I -> PT):
         Object_param_type(Obj, I -> PT)

  'rule' Object_param_type(obj_appl(Obj, A), I -> nil):
         Object_type_check(obj_appl(Obj, A), I)
         
  'rule' Object_param_type(obj_array(TS, Obj), I -> param_type(T1)):
         Make_single_typing(TS -> single(P,B,T))
         Check_type_defined(T -> T1)
         Openenv()
         Define_value_typings(TS)
         Object_type_check(Obj, I)
         Closeenv()
         
-- Separates out the first part of a qualified object name
-- eg Split_name(X.Y.Z -> X, Y.Z)
-- Then Y.Z can be looked up in the environment of X
'action' Split_name(NAME -> OBJECT_EXPR, NAME)

  'rule' Split_name(qual_name(P, Obj, Id) -> Obj1, N):
         (|
           where(Obj -> obj_name(qual_name(P3, Obj3, Id3)))
           Split_name(qual_name(P3, Obj3, Id3) -> Obj1, N1)
           where(qual_name(P, obj_name(N1), Id) -> N)
         ||
           where(Obj -> obj_fit(Obj3, F))
           Split_name(qual_name(P, Obj3, Id) -> Obj4, N)
           where(obj_fit(Obj4, F) -> Obj1)
         ||
           where(Obj -> obj_appl(Obj3, A))
           Split_name(qual_name(P, Obj3, Id) -> Obj4, N)
           where(obj_appl(Obj4, A) -> Obj1)
         ||
           where(Obj -> obj_array(TS, Obj3))
           Split_name(qual_name(P, Obj3, Id) -> Obj4, N)
           where(obj_array(TS, Obj4) -> Obj1)
         ||
           where(Obj -> Obj1)
           where(name(P, Id) -> N)
         |)

-- search stops when found 
-- or when innermost fitting encountered from ownclass
-- since this indicates we are searching from within a scheme instantiation
'action' Lookup_object_in_current_env(IDENT, CURRENT_ENV, PATHS, OWNENV, OWNCLASS -> OPT_OBJECT_ID, PARAM_FIT)

  'rule' Lookup_object_in_current_env(Id, C, Paths, Ownenv, Ownclass -> Oid, PF):
         where(C -> current_env(CE,C1))
         where(Paths -> list(Path, Paths1))
         Get_current_path_env(CE, Path -> CE1)
         (|
           where(CE1 -> instantiation_env(PF1, CE2))
         ||
           where(PARAM_FIT'nil -> PF1)
           where(CE1 -> CE2)
         |)
         DefaultPos(-> P)
         Lookup_object_in_env(obj_name(name(P,id_op(Id))), CE2, Ownenv -> Oid1)
-- debug
-- Putmsg("Looking for ")
-- Print_id(Id)
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
-- Get_env_types(CE1 -> TE2)
-- Print_type_env(TE2)
-- Putnl()
-- print(Path)
-- print(CE2)
         (|
           ne(Oid1,nil)
           where(Oid1 -> Oid)
           where(PARAM_FIT'nil -> PF)
         ||
           (|
             eq(Ownclass, ownclass)
             ne(PF1, nil)
             Lookup_object_in_params(Id, PF1 -> Oid, PF2)
-- debug
-- Putmsg("Looking in params ")
-- print(PF1)
-- Putmsg("for ")
-- Print_id(Id)
-- (|
--   where(Oid -> object_id(I))
--   I'Ident -> Id1
--   Putmsg(" found as ")
--   Print_id(Id1)
-- ||
--   Putmsg(" not found")
-- |)
-- Putnl()
             (|
               eq(Oid, nil)
               -- not found - return whole fitting
               where(PF1 -> PF)
             ||
               -- found - return part of fitting
               -- (will be in first component)
               -- otherwise if actual parameter is repeated
               -- Fit_name can get wrong one
               where(PF2 -> PF)
             |)
           ||
             Lookup_object_in_current_env1(Id, C, Paths, Ownenv, Ownclass -> Oid, PF)
           |)
         |)

  'rule' Lookup_object_in_current_env(Id, nil, Paths, Ownenv, Ownclass -> nil, nil):

'action' Lookup_object_in_current_env1(IDENT, CURRENT_ENV, PATHS, OWNENV, OWNCLASS -> OPT_OBJECT_ID, PARAM_FIT)

  'rule' Lookup_object_in_current_env1(Id, C, Paths, Ownenv, Ownclass -> Oid, PF):
         where(C -> current_env(CE,C1))
         where(Paths -> list(Path, Paths1))
         (|
           eq(Path, nil)
           Lookup_object_in_current_env(Id, C1, Paths1, Ownenv, Ownclass -> Oid, PF)
         ||
           Up1(Path -> Up_path, Up_step)
           -- check left branch if any before moving up
           (|
             where(Up_step -> right(nil))
             Out_scope(Path -> Path1)
             Get_current_path_env(CE, Path1 -> CE3)
             DefaultPos(-> P)
             Lookup_object_in_env(obj_name(name(P,id_op(Id))), CE3, nil -> Oid3)
           ||
             where(OPT_OBJECT_ID'nil -> Oid3)
           |)
           (|
             ne(Oid3, nil)
             where(Oid3 -> Oid)
             where(PARAM_FIT'nil -> PF)
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
               Lookup_object_in_params(Id, PF1 -> Oid, PF2)
               (|
                 eq(Oid, nil)
                 -- not found - return whole fitting
                 where(PF1 -> PF)
               ||
                 -- found - return part of fitting
                 -- (will be in first component)
                 -- otherwise if actual parameter is repeated
                 -- Fit_name can get wrong one
                 where(PF2 -> PF)
               |)
             ||
               Lookup_object_in_current_env1(Id, C, list(Up_path, Paths1), Ownenv, Ownclass -> Oid, PF)
             |)
           |)
         |)

-- lookup object in this environment only

'action' Lookup_object_in_env(OBJECT_EXPR, CLASS_ENV, OWNENV -> OPT_OBJECT_ID)

  'rule' Lookup_object_in_env(Obj, instantiation_env(PF, CE), Ownenv -> Oid): 
         Lookup_object_in_env(Obj, CE, OWNENV'nil -> Oid)

  'rule' Lookup_object_in_env(obj_name(name(P, id_op(Id))), CE, Ownenv -> Oid):
         (|
           where(CE -> basic_env(_,_,_,_,ME,_,_,_,_,_,Ad))
           (|
             ne(Ownenv,ownenv)
             Adapt(id_op(Id), Ad -> Oid1)
           ||
             where(id(id_op(Id)) -> Oid1)
           |)
           (|
             where(Oid1 -> id(id_op(Id1)))
             Lookup_object_in_module(Id1, ME -> Oid)
           ||
             where(OPT_OBJECT_ID'nil -> Oid)
           |)
         ||
           where(CE -> extend_env(CE1, CE2, _, Ad))
           (|
             ne(Ownenv,ownenv)
             Adapt(id_op(Id), Ad -> Oid1)
           ||
             where(id(id_op(Id)) -> Oid1)
           |)
           (|
             where(Oid1 -> id(id_op(Id1)))
             Lookup_object_in_env(obj_name(name(P, id_op(Id1))), CE2, Ownenv -> Oid2)
             (|
               eq(Oid2,nil)
               Lookup_object_in_env(obj_name(name(P, id_op(Id1))), CE1, Ownenv -> Oid)
             ||
               where(Oid2 -> Oid)
             |)
           ||
             where(OPT_OBJECT_ID'nil -> Oid)
           |)
         ||
           where(OPT_OBJECT_ID'nil -> Oid)
         |)

  'rule' Lookup_object_in_env(obj_name(qual_name(P, Obj, id_op(Id))), CE, Ownenv -> Oid):
         Lookup_object_in_env(Obj, CE, Ownenv -> Oid1)
         (|
           where(Oid1 -> object_id(I))
           I'Env -> CE1
           Lookup_object_in_env(obj_name(name(P, id_op(Id))), CE1, nil -> Oid)
         ||
           where(OPT_OBJECT_ID'nil -> Oid)
         |)
         
  'rule' Lookup_object_in_env(obj_appl(Obj, A), CE, Ownenv -> Oid):
         Lookup_object_in_env(Obj, CE, Ownenv -> Oid)
  
  'rule' Lookup_object_in_env(obj_array(TS, Obj), CE, Ownenv -> Oid):
         Lookup_object_in_env(Obj, CE, Ownenv -> Oid)
  
  'rule' Lookup_object_in_env(obj_fit(Obj, F), CE, Ownenv -> Oid):
         Lookup_object_in_env(Obj, CE, Ownenv -> Oid)
  
  'rule' Lookup_object_in_env(Obj, nil, Ownenv -> nil):

'action' Lookup_object_env_in_module(IDENT, MODULE_ENV -> CLASS_ENV)

  'rule' Lookup_object_env_in_module(Id, M -> CE):
         Lookup_object_in_module(Id, M -> Oid)
         (|
           where(Oid -> object_id(I))
           I'Env -> CE
         ||
           where(CLASS_ENV'nil -> CE)
         |)
  
'action' Lookup_object_in_module(IDENT, MODULE_ENV -> OPT_OBJECT_ID)

  'rule' Lookup_object_in_module(Id, scheme_env(I2, ME) -> Oid1):
         Lookup_object_in_module(Id, ME -> Oid1)

  'rule' Lookup_object_in_module(Id, theory_env(I2, ME) -> Oid1):
         Lookup_object_in_module(Id, ME -> Oid1)

  'rule' Lookup_object_in_module(Id, object_env(I2, ME) -> object_id(I2)):
         I2'Ident -> Id2
         eq(Id,Id2)

  'rule' Lookup_object_in_module(Id, object_env(I2, ME) -> Oid):
         Lookup_object_in_module(Id, ME -> Oid)

  'rule' Lookup_object_in_module(Id, nil -> nil):

'action' Lookup_scheme_in_module(IDENT, MODULE_ENV -> OPT_SCHEME_ID)

  'rule' Lookup_scheme_in_module(Id, object_env(I2, ME) -> Oid):
         Lookup_scheme_in_module(Id, ME -> Oid)

  'rule' Lookup_scheme_in_module(Id, theory_env(I2, ME) -> Oid):
         Lookup_scheme_in_module(Id, ME -> Oid)

  'rule' Lookup_scheme_in_module(Id, scheme_env(I2, ME) -> scheme_id(I2)):
         I2'Ident -> Id2
         eq(Id,Id2)

  'rule' Lookup_scheme_in_module(Id, scheme_env(I2, ME) -> Oid):
         Lookup_scheme_in_module(Id, ME -> Oid)

  'rule' Lookup_scheme_in_module(Id, nil -> nil):

-------------------------------------------------------------------
-- Scheme lookup
-------------------------------------------------------------------

-- schemes may only be in globals (no embedded schemes)
'action' Get_id_of_scheme(IDENT -> OPT_SCHEME_ID)

  'rule' Get_id_of_scheme(Id -> Oid):
         Globals -> G
         Lookup_scheme_in_module(Id, G -> Oid)

--------------------------------------------------------------------
-- Set top level module name (and check consistent with file name)
--------------------------------------------------------------------

'action' Set_module_name_and_pos(LIB_MODULE)

  'rule' Set_module_name_and_pos(scheme(P,_,_,sdef(_,Id,_,_))):
         id_to_string(Id -> S)
         Module_name <- S
         Module_pos <- P
         Check_module_name(P,S)  

  'rule' Set_module_name_and_pos(object(P,_,_,odef(_,Id,_,_))):
         id_to_string(Id -> S)
         Module_name <- S
         Module_pos <- P
         Check_module_name(P,S)  

  'rule' Set_module_name_and_pos(theory(P,_,_,theory_def(_,Id,_))):
         id_to_string(Id -> S)
         Module_name <- S
         Module_pos <- P
         Check_module_name(P,S)  

  'rule' Set_module_name_and_pos(devt_relation(P,_,_,devt_relation_def(_,Id,_,_,_))):
         id_to_string(Id -> S)
         Module_name <- S
         Module_pos <- P
         Check_module_name(P,S)  

'action' Get_module_pos(-> POS)

  'rule' Get_module_pos(-> P):
         Module_pos -> P

--------------------------------------------------------------------
-- Adapt
--------------------------------------------------------------------

-- When looking up an ID_OR_OP from outside a class Adapt converts the
-- external name to an internal one according to any renaming
-- Also checks hides, so result is nil if hidden
'action' Adapt(ID_OR_OP, ADAPTS -> OPT_ID_OR_OP)

  'rule' Adapt(Id, hide(Id1,ADS) -> Oid):
         (|
           Equal_id_or_op(Id,Id1)
-- debug
-- where(Id -> id_op(I))
-- id_to_string(I -> S)
-- Putmsg(S)
-- Putmsg(" is hidden")
-- Putnl()
           where(OPT_ID_OR_OP'nil -> Oid)
         ||
           Adapt(Id, ADS -> Oid)
         |)

  'rule' Adapt(Id, rename(Id1,Id2,ADS) -> Oid):
         (|
           Equal_id_or_op(Id,Id1)
-- debug
-- Putmsg("Was looking for ")
-- where(Id -> id_op(I))
-- id_to_string(I -> S)
-- Putmsg(S)
-- Putmsg(", now looking for ")
-- where(Id2 -> id_op(I2))
-- id_to_string(I2 -> S2)
-- Putmsg(S2)
-- Putnl()
           Adapt(Id2, ADS -> Oid)
         ||
           Equal_id_or_op(Id, Id2)
-- debug
-- where(Id -> id_op(I))
-- id_to_string(I -> S)
-- Putmsg(S)
-- Putmsg(" renamed to ")
-- where(Id1 -> id_op(I1))
-- id_to_string(I1 -> S1)
-- Putmsg(S1)
-- Putnl()
           where(OPT_ID_OR_OP'nil -> Oid)
         ||
           Adapt(Id, ADS -> Oid)
         |)

  'rule' Adapt(Id, nil -> id(Id)):

'condition' Equal_id_or_op(ID_OR_OP, ID_OR_OP)

  'rule' Equal_id_or_op(id_op(Id1), id_op(Id2)):
         eq(Id1,Id2)
         
  'rule' Equal_id_or_op(op_op(Op1), op_op(Op2)):
         eq(Op1,Op2)


----------------------------------------------------------------
-- Fitting names
----------------------------------------------------------------

'action' Fit_name(NAME, Object_id, PARAM_FIT -> NAME)

  'rule' Fit_name(N, AI, param_fit(OI, I, Obj2, AD, PF) -> N1):
         (|
           eq(AI, I)
           Adapt_name(N, AD -> N1)
         ||
           Fit_name(N, AI, PF -> N1)
         |)

'action' Adapt_name(NAME, ADAPTS -> NAME)

  'rule' Adapt_name(name(P, Id), AD -> name(P, Id1)):
         Unadapt(Id, AD -> Id1)

  'rule' Adapt_name(qual_name(P, obj_name(N), Id), AD -> qual_name(P, obj_name(N1), Id)):
         Adapt_name(N, AD -> N1)

  'rule' Adapt_name(qual_name(P, obj_appl(Obj, A), Id), AD -> qual_name(P1, obj_appl(Obj1, A), Id1)):
         Adapt_name(qual_name(P, Obj, Id), AD -> qual_name(P1, Obj1, Id1))

  'rule' Adapt_name(qual_name(P, obj_array(TP, Obj), Id), AD -> qual_name(P1, obj_array(TP, Obj1), Id1)):
         Adapt_name(qual_name(P, Obj, Id), AD -> qual_name(P1, Obj1, Id1))

  'rule' Adapt_name(qual_name(P, obj_fit(Obj, RS), Id), AD -> qual_name(P1, obj_fit(Obj1, RS), Id1)):
         Adapt_name(qual_name(P, Obj, Id), AD -> qual_name(P1, Obj1, Id1))

--------------------------------------------------------------------
-- Unadapt
--------------------------------------------------------------------

-- When checking static implementation we need to "unadapt" names
-- defined in the implemented class according to any renaming applied
-- to it
'action' Unadapt(ID_OR_OP, ADAPTS -> ID_OR_OP)

  'rule' Unadapt(Id, nil -> Id):

  'rule' Unadapt(Id, rename(Id1, Id2, RS) -> Id3):
         (|
           Equal_id_or_op(Id, Id2)
           Unadapt(Id1, RS -> Id3)
         ||
           Unadapt(Id, RS -> Id3)
         |)

--------------------------------------------------------------------
-- Actual scheme parameters
--------------------------------------------------------------------

-- Add parameter fitting to current environment
-- On final pass CHECK parameter causes static implementation to be
-- checked
'action' Make_actual_params(POS, MODULE_ENV, OBJECT_EXPRS)

  'rule' Make_actual_params(P, nil, nil):
-- debug
-- Current -> current_env(CEC, _)
-- Extend_paths -> list(Path, _)
-- Putmsg("Making params for current env and path")
-- Putnl()
-- print(CEC)
-- print(Path)
         Get_current_env(-> CE)
-- Putmsg("Found env")
-- Putnl()
-- print(CE)
         Set_current_env(instantiation_env(no_parms, CE))

  'rule' Make_actual_params(P, ME, Objs):
         Get_current_env(-> CE)
         Set_current_env(instantiation_env(nil, CE))
         Make_actual_params1(P, ME, Objs)

'action' Make_actual_params1(POS, MODULE_ENV, OBJECT_EXPRS)

  'rule' Make_actual_params1(P, object_env(I,ME), list(Obj, Objs)):
         Make_actual_param(P, I, Obj)
         Make_actual_params1(P, ME, Objs)

  'rule' Make_actual_params1(P, nil, nil):

  'rule' Make_actual_params1(P, object_env(_,_), nil):
         Puterror(P)
         Putmsg("More formal parameters than actual")
         Putnl()

  'rule' Make_actual_params1(P, nil, list(_,_)):
         Puterror(P)
         Putmsg("More actual parameters than formal")
         Putnl()

'action' Make_actual_param(POS, Object_id, OBJECT_EXPR)

  'rule' Make_actual_param(P, OI, Obj):
         Separate_adapts(Obj -> Obj1, AD)
-- debug
-- Current -> C
         -- temporarily remove fitting so search for
         -- actual parameter can continue outwards
         Get_current_env(-> instantiation_env(PF, CE))
         Set_current_env(CE)
-- Current -> C1
         (|
           Get_object_id(Obj1 -> object_id(I), PF1)
           (|
             ne(PF1, nil)
             -- found in outer fitting; prefix adapts from there
             Prefix_adapts(I, PF1, AD -> AD1)
           ||
             where(AD -> AD1)
           |)
           Set_current_env(instantiation_env(param_fit(OI, I, Obj1, AD1, PF), CE))
         ||
           Object_pos(Obj -> P1)
           Puterror(P1)
           Putmsg("Actual parameter ")
           Print_object(Obj)
           Putmsg(" hidden, renamed, or not defined")
           Putnl()
           Set_current_env(instantiation_env(PF, CE))
-- print(C)
-- print(C1)
         |)

'action' Separate_adapts(OBJECT_EXPR -> OBJECT_EXPR, ADAPTS)

  'rule' Separate_adapts(obj_fit(Obj, RS) -> Obj, AD):
         Add_renames(RS, nil -> AD)

  'rule' Separate_adapts(Obj -> Obj, nil):

'action' Prefix_adapts(Object_id, PARAM_FIT, ADAPTS -> ADAPTS)

  'rule' Prefix_adapts(AI, param_fit(OI, I, _, ADF, PF), AD -> AD1):
         -- assumes AI is an actual in the fitting
         (|
           eq(AI, I)
           Concat_adapts(ADF, AD -> AD1)
         ||
           Prefix_adapts(AI, PF, AD -> AD1)
         |)

-- debug
  'rule' Prefix_adapts(AI, PF, AD -> AD)
-- Putmsg("Actual ")
-- AI'Ident -> Aid
-- Print_id(Aid)
-- Putmsg(" is ")
-- print(AI)
-- Putmsg("Fitting is ")
-- print(PF)



'action' Object_pos(OBJECT_EXPR -> POS)

  'rule' Object_pos(obj_name(name(P,_)) -> P):

  'rule' Object_pos(obj_name(qual_name(P,_,_)) -> P):
  
  'rule' Object_pos(obj_appl(Obj, _) -> P):
         Object_pos(Obj -> P)

  'rule' Object_pos(obj_array(_, Obj) -> P):
         Object_pos(Obj -> P)

  'rule' Object_pos(obj_fit(Obj, _) -> P):
         Object_pos(Obj -> P)

  'rule' Object_pos(obj_occ(P, _) -> P):

  'rule' Object_pos(qual_occ(P, _, _) -> P):

'action' Id_of_object(OBJECT_EXPR -> Object_id)

-- assumes object is resolved (eg in an ACCESS)

  'rule' Id_of_object(obj_appl(Obj, _) -> I):
         Id_of_object(Obj -> I)

  'rule' Id_of_object(obj_array(_, Obj) -> I):
         Id_of_object(Obj -> I)

  'rule' Id_of_object(obj_fit(Obj, _) -> I):
         Id_of_object(Obj -> I)

  'rule' Id_of_object(obj_occ(_, I) -> I):

  'rule' Id_of_object(qual_occ(_, _, I) -> I):

-- To check implementation we:
-- 1. temporarily make current environment just the (new) implementing class
-- 2. make a copy of the (old) implemented class in which all type
--    abbreviations are unfolded 
-- 3. Check that all entities defined in the old are defined in the current
--    environment, ie the implementing class
'action' Check_implementations(PARAM_FIT, PARAM_FIT)

  'rule' Check_implementations(no_parms, PFC):

  'rule' Check_implementations(param_fit(OI, I, Obj, AD, PF), PFC):
         Object_pos(Obj -> P)
	 -- remove instantiation barrier in case actual object Obj has
	 -- parameters to be looked up
	 Get_current_env(-> instantiation_env(PF1, CE1))
	 Set_current_env(CE1)
         Object_param_type(Obj, I -> PT)
         OI'Params -> PT1
	 Set_current_env(instantiation_env(PF1, CE1))
         OI'Env -> Oldenv
	 (|
	   where(PT1 -> param_type(T1))
	   Redefine(T1, Oldenv, PFC -> T2)
	   where(param_type(T2) -> PT2)
	 ||
	   where(PT1 -> PT2)
	 |)
         Check_object_params(P, PT2, PT)
         I'Env -> Newenv
         Current -> C
         Current <- current_env(Newenv, nil)
-- debug
-- Putmsg("Checking that ")
-- I'Ident -> Aid
-- Print_id(Aid)
-- Putnl()
-- Get_env_types(Newenv -> ATE)
-- Print_type_env(ATE)
-- Putmsg(" implements ")
-- OI'Ident -> Oid
-- Print_id(Oid)
-- Putnl()
-- Get_env_types(Oldenv -> OTE)
-- Print_type_env(OTE)
         Extend_paths -> Paths
         Extend_paths <- list(nil,nil)
         Type_numbers -> TF
         Type_numbers <- list(nil, TF)
         Unfold_types(Oldenv, Oldenv, nil, PFC -> Oldenv1)
-- Putmsg(" which unfolds to ")
-- Get_env_types(Oldenv1 -> OTE1)
-- Print_type_env(OTE1)
         Check_implementation(P, AD, Oldenv1, Oldenv1, nil, PFC)
         Current <- C
         Extend_paths <- Paths
         Type_numbers <- TF
         Check_implementations(PF, PFC)

  'rule' Check_implementations(nil, PFC):

'action' Check_implementation(POS, ADAPTS, CLASS_ENV, CLASS_ENV, ADAPTS, PARAM_FIT)

  'rule' Check_implementation(P, Fit, BCE, instantiation_env(_, CE), AD, PFC):
         Check_implementation(P, Fit, BCE, CE, AD, PFC)

  'rule' Check_implementation(P, Fit, BCE, extend_env(CE1, CE2, WITH, AD), AD1, PFC):
         Concat_adapts(AD1, AD -> AD2)
         Check_implementation(P, Fit, BCE, CE1, AD2, PFC)
         Check_implementation(P, Fit, BCE, CE2, AD2, PFC)

  'rule' Check_implementation(P, Fit, BCE, basic_env(TYP, list(VAL,VES), VAR, CH, MOD, AX, TC, TS, _,WITH, AD), AD1, PFC):
         Concat_adapts(AD1, AD -> AD2)
         Check_types_implementation(P, Fit, TYP, AD2)
         Check_values_implementation(P, Fit, VAL, AD2)
         Check_variables_implementation(P, Fit, VAR, AD2)
         Check_channels_implementation(P, Fit, CH, AD2)
         Check_modules_implementation(P, Fit, BCE, MOD, AD2, PFC)

'action' Concat_adapts(ADAPTS, ADAPTS -> ADAPTS)

  'rule' Concat_adapts(nil, AD -> AD):

  'rule' Concat_adapts(hide(Id, AD1), AD2 -> hide(Id, AD)):
         Concat_adapts(AD1, AD2 -> AD)

  'rule' Concat_adapts(rename(Id1, Id2, AD1), AD2 -> rename(Id1, Id2, AD)):
         Concat_adapts(AD1, AD2 -> AD)
         
'action' Check_object_params(POS, PARAM_TYPE, PARAM_TYPE)

  'rule' Check_object_params(P, PT1, PT2):
         (|
           where(PT1 -> param_type(T1))
           (|
             where(PT2 -> param_type(T2))
             (|
               Match(T1, nil, T2)
             ||
               Puterror(P)
               Putmsg("Array parameter type ")
               Print_type(T1)
               Putmsg(" not implemented by type ")
               Print_type(T2)
               Putnl() 
             |)
           ||
             Puterror(P)
             Putmsg("Array object cannot be implemented by element object")
             Putnl()
           |)
         ||
           [|
             where(PT2 -> param_type(T2))
             Puterror(P)
             Putmsg("Element object cannot be implemented by array object")
             Putnl()
           |]
         |)

'action' Unfold_types(CLASS_ENV, CLASS_ENV, ADAPTS, PARAM_FIT -> CLASS_ENV)

  'rule' Unfold_types(OCE, instantiation_env(_, CE), AD, PFC -> CE1):
         Unfold_types(OCE, CE, AD, PFC -> CE1)

  'rule' Unfold_types(OCE, extend_env(CE1, CE2, WITH, AD), AD1, PFC -> extend_env(CE11, CE21, WITH, AD)):
         Concat_adapts(AD1, AD -> AD2)
         Unfold_types(OCE, CE1, AD2, PFC -> CE11)
         Unfold_types(OCE, CE2, AD2, PFC -> CE21)

  'rule' Unfold_types(OCE, CE, AD1, PFC -> basic_env(TYP1, list(VAL1,VES), VAR1, CH1, MOD1, AX, TC, TS, Prop, WITH, AD)):
         where(CE -> basic_env(TYP, list(VAL,VES), VAR, CH, MOD, AX, TC, TS, Prop, WITH, AD))
         Concat_adapts(AD1, AD -> AD2)
         Unfold_type_types(OCE, TYP, PFC -> TYP1)
         Unfold_value_types(OCE, VAL, PFC -> VAL1)
         Unfold_variable_types(OCE, VAR, PFC -> VAR1)
         Unfold_channel_types(OCE, CH, PFC -> CH1)
	 Unfold_module_types(OCE, MOD, AD2, PFC -> MOD1)

'action' Unfold_type_types(CLASS_ENV, TYPE_ENV, PARAM_FIT -> TYPE_ENV)

  'rule' Unfold_type_types(CE, type_env(I, TE), PFC -> type_env(I1, TE1)):
         Copy_type_id(I -> I1)
         (|
           I'Type -> abbrev(T)
           Redefine(T, CE, PFC -> T1)
           I1'Type <- abbrev(T1)
-- debug
-- Putmsg("Type of ")
-- I'Ident -> Id
-- Print_id(Id)
-- Putmsg(" full name ")
-- Print_type(defined(I, nil))
-- Putmsg(" was ")
-- Print_type(T)
-- Putnl()
-- print(T)
-- Putmsg(" now ")
-- Print_type(T1)
-- Putnl()
-- print(T1)
-- Putnl()
         ||
           Type_numbers -> list(TN, TNS)
           Get_polynum(I1, TN -> Num, TN1)
           Type_numbers <- list(TN1, TNS)
           I1'Type <- abbrev(poly(Num)) -- sort: may be implemented by anything
-- debug
-- Putmsg("Type of ")
-- I'Ident -> Id
-- Print_id(Id)
-- Putmsg(" was sort; now ")
-- Print_type(poly(Num))
-- Putnl()
         |)
         Unfold_type_types(CE, TE, PFC -> TE1)

  'rule' Unfold_type_types(CE, nil, PFC -> nil):

'action' Unfold_value_types(CLASS_ENV, Value_ids, PARAM_FIT -> Value_ids)

  'rule' Unfold_value_types(CE, list(I, VE), PFC -> list(I1, VE1)):
         Copy_value_id(I -> I1)
         I'Type -> T
         Redefine(T, CE, PFC -> T1)
         I1'Type <- T1
-- debug
-- Putmsg("Type of ")
-- I'Ident -> Id
-- Print_id_or_op(Id)
-- Putmsg(" was ")
-- Print_type(T)
-- Putnl()
-- print(T)
-- Putmsg(" now ")
-- Print_type(T1)
-- Putnl()
-- print(T1)
-- Putnl()
         Unfold_value_types(CE, VE, PFC -> VE1)

  'rule' Unfold_value_types(CE, nil, PFC -> nil):

'action' Unfold_variable_types(CLASS_ENV, VARIABLE_ENV, PARAM_FIT -> VARIABLE_ENV)

  'rule' Unfold_variable_types(CE, variable_env(I, VE), PFC -> variable_env(I1, VE1)):
         Copy_variable_id(I -> I1)
         I'Type -> T
-- debug
-- Putmsg("Type of variable ")
-- I1'Ident -> Id
-- Print_id(Id)
-- Putmsg(" redefined from ")
-- Print_type(T)
-- print(T)
         Redefine(T, CE, PFC -> T1)
-- Putmsg(" to ")
-- Print_type(T1)
-- print(T1)
         I1'Type <- T1
         Unfold_variable_types(CE, VE, PFC -> VE1)

  'rule' Unfold_variable_types(CE, nil, PFC -> nil):

'action' Unfold_channel_types(CLASS_ENV, CHANNEL_ENV, PARAM_FIT -> CHANNEL_ENV)

  'rule' Unfold_channel_types(CE, channel_env(I, CHE), PFC -> channel_env(I1, CHE1)):
         Copy_channel_id(I -> I1)
         I'Type -> T
         Redefine(T, CE, PFC -> T1)
         I1'Type <- T1
         Unfold_channel_types(CE, CHE, PFC -> CHE1)

  'rule' Unfold_channel_types(CE, nil, PFC -> nil):

'action' Unfold_module_types(CLASS_ENV, MODULE_ENV, ADAPTS, PARAM_FIT -> MODULE_ENV)

  'rule' Unfold_module_types(OCE, object_env(I, ME), AD, PFC -> object_env(I1, ME1)):
	 Copy_object_id(I -> I1)
	 (|
	   I'Params -> param_type(T)
	   Redefine(T, OCE, PFC -> T1)
	   I1'Params <- param_type(T1)
	 ||
	   I1'Params <- nil
	 |)
	 I'Param_env -> PCE
	 Unfold_types(OCE, PCE, nil, PFC -> PCE1)
	 I1'Param_env <- PCE1
         I'Pos -> P
         I'Ident -> Id
	 I'Env -> CE
         Unadapt_name(name(P, id_op(Id)), AD, hide -> ON)
-- Putmsg("Object ")
-- Print_id(Id)
-- Putmsg(" unadapted to ")
         [|
           where(ON -> act_name(name(P1, id_op(Id1))))
-- Print_id(Id1)
-- Putnl()
	   (|
	     where(PFC -> param_fit(_,_,_,Fit,_))
	     Unadapt(id_op(Id1), Fit -> id_op(Id2))
	   ||
	     where(Id1 -> Id2)
	   |)
	   Current -> C1
	   Extend_paths -> Paths1
	   Lookup_object_in_current_env(Id2, C1, Paths1, nil, nil -> object_id(I2), _)
-- Putmsg("found as ")
-- I2'Ident -> Id21
-- Print_id(Id21)
-- Putnl()
	   I2'Env -> CE2
	   Current <- current_env(CE2, C1)
	   Extend_paths <- list(nil,Paths1)
	   Unfold_types(OCE, CE, nil, PFC -> CE1)
	   I1'Env <- CE1
	   Current -> current_env(_, C2)
	   Current <- C2
	   Extend_paths <- Paths1
	 |]
	 Unfold_module_types(OCE, ME, AD, PFC -> ME1)

  'rule' Unfold_module_types(_, nil, _, _ -> nil):

'action' Redefine(TYPE_EXPR, CLASS_ENV, PARAM_FIT -> TYPE_EXPR)

  'rule' Redefine(product(Pr), CE, PFC -> product(Pr1)):
         Redefine_prod(Pr, CE, PFC -> Pr1)

  'rule' Redefine(fin_set(T), CE, PFC -> fin_set(T1)):
         Redefine(T, CE, PFC -> T1)

  'rule' Redefine(infin_set(T), CE, PFC -> infin_set(T1)):
         Redefine(T, CE, PFC -> T1)

  'rule' Redefine(fin_list(T), CE, PFC -> fin_list(T1)):
         Redefine(T, CE, PFC -> T1)

  'rule' Redefine(infin_list(T), CE, PFC -> infin_list(T1)):
         Redefine(T, CE, PFC -> T1)

  'rule' Redefine(fin_map(D,R), CE, PFC -> fin_map(D1,R1)):
         Redefine(D, CE, PFC -> D1)
         Redefine(R, CE, PFC -> R1)

  'rule' Redefine(fun(D,ARR,R), CE, PFC -> fun(D1,ARR,R1)):
         Redefine(D, CE, PFC -> D1)
         Redefine_result(R, CE, PFC -> R1)

  'rule' Redefine(subtype(single(P,B,T),R), CE, PFC -> subtype(single(P,B,T1),R)):
         Redefine(T, CE, PFC -> T1)

  'rule' Redefine(bracket(T), CE, PFC -> bracket(T1)):
         Redefine(T, CE, PFC -> T1)

  'rule' Redefine(defined(I, Q), CE, PFC -> T):
         I'Type -> Type
         where(Type -> abbrev(T1))
         Redefine(T1, CE, PFC -> T)

  'rule' Redefine(defined(I, Q), CE, PFC -> T):
-- debug
-- Putmsg("Redefining ")
-- print(defined(I, Q))
-- print(CE)
         Type_is_defined_in_class_env(I, CE)
         I'Type -> Type
         I'Pos -> P
         I'Ident -> Id
         I'Qualifier -> Is
-- Putmsg("Qualifier is ")
-- Print_qualifier(Is)
-- print(Is)
-- print(CE)
-- print(PFC)
         (|
           where(PFC -> param_fit(_, _, _, Fit, _))
         ||
           where(ADAPTS'nil -> Fit)
         |)
         Make_name(P, id_op(Id), Is, CE -> ON)
         (|
           where(ON -> act_name(N1))
           Redefine_opt_qualification(Q, CE, PFC -> Q1)
           Adapt_name(N1, Fit -> N2)
-- debug
-- Putmsg("So looking for type with name ")
-- Print_name(N2)
-- Putnl()
	   (|
	     where(Q1 -> qualification(Obj))
-- debug
-- Putmsg("Qualified by ")
-- Print_object(Obj)
-- Putnl()
	     (|
	       where(Obj -> obj_occ(_, OI))
	     ||
	       where(Obj -> qual_occ(_, _, OI))
	     |)
	     OI'Env -> OCE
	     Lookup_env_type_name(N2, OCE, nil, nil -> type_id(I1))
	   ||
             Current -> C1
             Extend_paths -> Paths
             Lookup_current_type_name(N2, C1, Paths, nil, nil -> type_id(I1))
	   |)
           where(defined(I1, Q1) -> T)
-- debug
-- Putmsg("and found as ")
-- Print_type(defined(I1, Q1))
-- Putnl()
-- Print_type(T)
-- print(defined(I1, Q1))
         ||
           where(TYPE_EXPR'any -> T)
-- debug
-- Putmsg("and hidden")
-- Putnl()
         |)

  'rule' Redefine(defined(I, Q), CE, PFC -> T):
         Type_defined_in_formals(I, PFC -> Oid, Found)
         (|
           eq(Found, found)
           (|
             where(Oid -> type_id(I1))
             I1'Type -> Type
             (|
               where(Type -> abbrev(T1))
               Redefine(T1, CE, PFC -> T)
             ||
               -- sort
               Redefine_opt_qualification(Q, CE, PFC -> Q1)
               where(defined(I1, Q1) -> T)
-- debug
-- Print_type(defined(I, Q))
-- Putmsg(" redefined as ")
-- Print_type(defined(I1, Q1))
-- Putnl()
             |)
           ||
             -- hidden
             where(TYPE_EXPR'any -> T)
           |)
         ||
           -- defined elsewhere
           where(defined(I, Q) -> T)
-- debug
-- Putmsg("Type ")
-- Print_type(T)
-- Putmsg(" unchanged")
-- Putnl()
         |)

  'rule' Redefine(T, CE, PFC -> T):

'action' Redefine_prod(PRODUCT_TYPE, CLASS_ENV, PARAM_FIT -> PRODUCT_TYPE)

  'rule' Redefine_prod(list(T,PR), CE, PFC -> list(T1,PR1)):
         Redefine(T, CE, PFC -> T1)
         Redefine_prod(PR, CE, PFC -> PR1)

  'rule' Redefine_prod(nil, CE, PFC -> nil):

'action' Redefine_result(RESULT, CLASS_ENV, PARAM_FIT -> RESULT)

  'rule' Redefine_result(result(T,RD,WR,IN,OUT), CE, PFC -> result(T1,RD1,WR1,IN1,OUT1)):
         Redefine(T, CE, PFC -> T1)
         Redefine_accesses(RD, CE, PFC -> RD1)
         Redefine_accesses(WR, CE, PFC -> WR1)
         Redefine_accesses(IN, CE, PFC -> IN1)
         Redefine_accesses(OUT, CE, PFC -> OUT1)

'action' Redefine_accesses(ACCESSES, CLASS_ENV, PARAM_FIT -> ACCESSES)

  'rule' Redefine_accesses(list(A, AS), CE, PFC -> list(A1, AS1)):
         Redefine_access(A, CE, PFC -> A1)
         Redefine_accesses(AS, CE, PFC -> AS1)

  'rule' Redefine_accesses(nil, CE, PFC -> nil):

'action' Redefine_access(ACCESS, CLASS_ENV, PARAM_FIT -> ACCESS)

  'rule' Redefine_access(enumerated_access(P, AS), CE, PFC -> enumerated_access(P, AS1)):
	 Redefine_accesses(AS, CE, PFC -> AS1)

  'rule' Redefine_access(completed_access(P, Q), CE, PFC -> completed_access(P, Q1)):
         Redefine_opt_qualification(Q, CE, PFC -> Q1)

  'rule' Redefine_access(comprehended_access(P, A, L), CE, PFC -> comprehended_access(P, A1, L)):
	 Redefine_access(A, CE, PFC -> A1)

  'rule' Redefine_access(variable(P, I, Q), CE, PFC -> A):
-- debug
-- Putmsg("Looking for variable ")
-- print(I)
         Variable_is_defined_in_class_env(I, CE)
         I'Ident -> Id
-- print(I)
-- Putmsg("Variable ")
-- Print_id(Id)
-- Putmsg(" found in class\n")
         I'Qualifier -> Is
         (|
           where(PFC -> param_fit(_, _, _, Fit, _))
         ||
           where(ADAPTS'nil -> Fit)
         |)
         Make_name(P, id_op(Id), Is, CE -> ON)
-- print(Is)
-- [|
--   where(Is -> list(OI,_))
--   OI'Ident -> OID
--   Print_id(OID)
--   Putnl()
-- |]
-- print(ON)
         (|
           where(ON -> act_name(N1))
           Adapt_name(N1, Fit -> N2)
-- Putmsg("Now looking for ")
-- Print_name(N2)
           Current -> C
           Extend_paths -> Paths
           Lookup_current_variable_name(N2, C, Paths, nil, nil -> variable_id(I1))
           Redefine_opt_qualification(Q, CE, PFC -> Q1)
           where(ACCESS'variable(P, I1, Q1) -> A)
-- Putmsg(" found\n")
         ||
           where(ON -> hidden(N1))
           Adapt_name(N1, Fit -> N2)
           Get_object_id1(obj_name(N2), nil, nil -> object_id(I1),_)
           where(completed_access(P, qualification(obj_occ(P,I1))) -> A)
         ||
           where(completed_access(P, nil) -> A)
         |)
         
  'rule' Redefine_access(variable(P, I, Q), CE, PFC -> A):
         Variable_defined_in_formals(I, PFC -> Oidv, Oido, Found)
         (|
           eq(Found, found)
           (|
             where(Oidv -> variable_id(I1))
             Redefine_opt_qualification(Q, CE, PFC -> Q1)
             where(ACCESS'variable(P, I1, Q1) -> A)
           ||
             where(Oido -> object_id(I2))
             where(completed_access(P, qualification(obj_occ(P,I2))) -> A)
           ||
             where(completed_access(P, nil) -> A)
           |)
         ||
           where(ACCESS'variable(P, I, Q) -> A)
         |)


  'rule' Redefine_access(channel(P, I, Q), CE, PFC -> A):
-- debug
-- Putmsg("Looking for channel ")
-- print(I)
         Channel_is_defined_in_class_env(I, CE)
         I'Ident -> Id
         I'Qualifier -> Is
-- print(I)
-- Putmsg("Channel ")
-- Print_id(Id)
-- Putmsg(" found in class\n")
         (|
           where(PFC -> param_fit(_, _, _, Fit, _))
         ||
           where(ADAPTS'nil -> Fit)
         |)
         Make_name(P, id_op(Id), Is, CE -> ON)
-- print(Is)
-- [|
--   where(Is -> list(OI,_))
--   OI'Ident -> OID
--   Print_id(OID)
--   Putnl()
-- |]
-- print(ON)
         (|
           where(ON -> act_name(N1))
           Adapt_name(N1, Fit -> N2)
-- Putmsg("Now looking for ")
-- Print_name(N2)
           Current -> C
           Extend_paths -> Paths
           Lookup_current_channel_name(N2, C, Paths, nil, nil -> channel_id(I1))
           Redefine_opt_qualification(Q, CE, PFC -> Q1)
           where(ACCESS'channel(P, I1, Q1) -> A)
-- Putmsg(" found\n")
         ||
           where(ON -> hidden(N1))
           Adapt_name(N1, Fit -> N2)
           Get_object_id1(obj_name(N2), nil, nil -> object_id(I1),_)
           where(completed_access(P, qualification(obj_occ(P,I1))) -> A)
         ||
           where(completed_access(P, nil) -> A)
         |)
         
  'rule' Redefine_access(channel(P, I, Q), CE, PFC -> A):
         Channel_defined_in_formals(I, PFC -> Oidc, Oido, Found)
         (|
           eq(Found, found)
           (|
             where(Oidc -> channel_id(I1))
             Redefine_opt_qualification(Q, CE, PFC -> Q1)
             where(ACCESS'channel(P, I1, Q1) -> A)
           ||
             where(Oido -> object_id(I2))
             where(completed_access(P, qualification(obj_occ(P,I2))) -> A)
           ||
             where(completed_access(P, nil) -> A)
           |)
         ||
           where(ACCESS'channel(P, I, Q) -> A)
         |)

  'rule' Redefine_access(A, CE, PFC -> A):

'action' Redefine_object(OBJECT_EXPR, CLASS_ENV, PARAM_FIT -> OBJECT_EXPR)

  'rule' Redefine_object(Obj, CE, PFC -> Obj1):
         Id_of_object(Obj -> I)
         Object_is_defined_in_class_env(I, CE)
         I'Pos -> P
         I'Ident -> Id
         I'Qualifier -> Is
-- debug
-- Putmsg("Redefining object ")
-- Print_id(Id)
-- Putnl()
-- print(I)
         (|
           where(PFC -> param_fit(_, _, _, Fit, _))
         ||
           where(ADAPTS'nil -> Fit)
         |)
         Make_name(P, id_op(Id), Is, CE -> ON)
-- Putmsg("Make_name gives ")
-- print(ON)
	 (|
           (| where(ON -> act_name(N1)) || where(ON -> hidden(N1)) |)
-- Print_name(N1)
-- Putmsg(" fitted to ")
	   Adapt_name(N1, Fit -> N2)
-- Print_name(N2)
	   Get_object_id1(obj_name(N2), nil, nil -> object_id(I1),_)
	   where(obj_occ(P,I1) -> Obj1)
-- Putmsg(" found as ")
-- Print_object(Obj1)
-- Putnl()
-- print(I1)
         ||
	   where(Obj -> Obj1)
	 |)
         
  'rule' Redefine_object(Obj, CE, PFC -> Obj1):
         Id_of_object(Obj -> I)
         Object_defined_in_formals(I, PFC -> Oid, Found)
         (|
           eq(Found, found)
           (|
             where(Oid -> object_id(I1))
             Object_pos(Obj -> P)
             where(obj_occ(P,I1) -> Obj1)
           ||
             where(Obj -> Obj1)
           |)
         ||
           where(Obj -> Obj1)
         |)

'action' Redefine_opt_qualification(OPT_QUALIFICATION, CLASS_ENV, PARAM_FIT -> OPT_QUALIFICATION)

  'rule' Redefine_opt_qualification(nil, _, _ -> nil):

  'rule' Redefine_opt_qualification(qualification(Obj), CE, PFC -> Q):
         Redefine_object(Obj, CE, PFC -> Obj1)
	 (|
	   eq(Obj, Obj1) -- object is hidden
	   where(OPT_QUALIFICATION'nil -> Q)
	 ||
	   where(qualification(Obj1) -> Q)
	 |)
	   

'condition' Type_is_defined_in_current_env(Type_id, CURRENT_ENV)

  'rule' Type_is_defined_in_current_env(I, current_env(CE, C)):
         (|
           Type_is_defined_in_class_env(I, CE)
         ||
           Type_is_defined_in_current_env(I, C)
         |)

'condition' Type_is_defined_in_class_env(Type_id, CLASS_ENV)

  'rule' Type_is_defined_in_class_env(I, instantiation_env(_, CE)):
         Type_is_defined_in_class_env(I, CE)

  'rule' Type_is_defined_in_class_env(I, basic_env(TYP,_,_,_,MOD,_,_,_,_,_,_)):
         (|
           Type_is_defined_in_type_env(I, TYP)
         ||
           Type_is_defined_in_module_env(I, MOD)
         |)

  'rule' Type_is_defined_in_class_env(I, extend_env(CE1, CE2, _, _)):
         (|
           Type_is_defined_in_class_env(I, CE1)
         ||
           Type_is_defined_in_class_env(I, CE2)
         |)

'condition' Type_is_defined_in_type_env(Type_id, TYPE_ENV)

  'rule' Type_is_defined_in_type_env(I, type_env(I1, TE)):
         (|
           eq(I,I1)
         ||
           Type_is_defined_in_type_env(I, TE)
         |)

'condition' Type_is_defined_in_module_env(Type_id, MODULE_ENV)

  'rule' Type_is_defined_in_module_env(I, object_env(I1, ME)):
         (|
           I1'Env -> CE
           Type_is_defined_in_class_env(I, CE)
         ||
           Type_is_defined_in_module_env(I, ME)
         |)

'condition' Variable_is_defined_in_current_env(Variable_id, CURRENT_ENV)

  'rule' Variable_is_defined_in_current_env(I, current_env(CE, C)):
         (|
           Variable_is_defined_in_class_env(I, CE)
         ||
           Variable_is_defined_in_current_env(I, C)
         |)

'condition' Variable_is_defined_in_class_env(Variable_id, CLASS_ENV)

  'rule' Variable_is_defined_in_class_env(I, instantiation_env(_, CE)):
         Variable_is_defined_in_class_env(I, CE)

  'rule' Variable_is_defined_in_class_env(I, basic_env(_,_,VARS,_,MOD,_,_,_,_,_,_)):
         (|
           Variable_is_defined_in_variable_env(I, VARS)
         ||
           Variable_is_defined_in_module_env(I, MOD)
         |)

  'rule' Variable_is_defined_in_class_env(I, extend_env(CE1, CE2, _, _)):
         (|
           Variable_is_defined_in_class_env(I, CE1)
         ||
           Variable_is_defined_in_class_env(I, CE2)
         |)

'condition' Variable_is_defined_in_variable_env(Variable_id, VARIABLE_ENV)

  'rule' Variable_is_defined_in_variable_env(I, variable_env(I1, VARS)):
         (|
           eq(I,I1)
         ||
           Variable_is_defined_in_variable_env(I, VARS)
         |)

'condition' Variable_is_defined_in_module_env(Variable_id, MODULE_ENV)

  'rule' Variable_is_defined_in_module_env(I, object_env(I1, ME)):
         (|
           I1'Env -> CE
           Variable_is_defined_in_class_env(I, CE)
         ||
           Variable_is_defined_in_module_env(I, ME)
         |)

'condition' Channel_is_defined_in_current_env(Channel_id, CURRENT_ENV)

  'rule' Channel_is_defined_in_current_env(I, current_env(CE, C)):
         (|
           Channel_is_defined_in_class_env(I, CE)
         ||
           Channel_is_defined_in_current_env(I, C)
         |)

'condition' Channel_is_defined_in_class_env(Channel_id, CLASS_ENV)

  'rule' Channel_is_defined_in_class_env(I, instantiation_env(_, CE)):
         Channel_is_defined_in_class_env(I, CE)

  'rule' Channel_is_defined_in_class_env(I, basic_env(_,_,_,CHS,MOD,_,_,_,_,_,_)):
         (|
           Channel_is_defined_in_channel_env(I, CHS)
         ||
           Channel_is_defined_in_module_env(I, MOD)
         |)

  'rule' Channel_is_defined_in_class_env(I, extend_env(CE1, CE2, _, _)):
         (|
           Channel_is_defined_in_class_env(I, CE1)
         ||
           Channel_is_defined_in_class_env(I, CE2)
         |)

'condition' Channel_is_defined_in_channel_env(Channel_id, CHANNEL_ENV)

  'rule' Channel_is_defined_in_channel_env(I, channel_env(I1, CHS)):
         (|
           eq(I,I1)
         ||
           Channel_is_defined_in_channel_env(I, CHS)
         |)

'condition' Channel_is_defined_in_module_env(Channel_id, MODULE_ENV)

  'rule' Channel_is_defined_in_module_env(I, object_env(I1, ME)):
         (|
           I1'Env -> CE
           Channel_is_defined_in_class_env(I, CE)
         ||
           Channel_is_defined_in_module_env(I, ME)
         |)

'condition' Object_is_defined_in_current_env(Object_id, CURRENT_ENV)

  'rule' Object_is_defined_in_current_env(I, current_env(CE, C)):
         (|
           Object_is_defined_in_class_env(I, CE)
         ||
           Object_is_defined_in_current_env(I, C)
         |)

'condition' Object_is_defined_in_class_env(Object_id, CLASS_ENV)

  'rule' Object_is_defined_in_class_env(I, instantiation_env(_, CE)):
         Object_is_defined_in_class_env(I, CE)

  'rule' Object_is_defined_in_class_env(I, basic_env(_,_,_,_,MOD,_,_,_,_,_,_)):
         Object_is_defined_in_module_env(I, MOD)

  'rule' Object_is_defined_in_class_env(I, extend_env(CE1, CE2, _, _)):
         (|
           Object_is_defined_in_class_env(I, CE1)
         ||
           Object_is_defined_in_class_env(I, CE2)
         |)

'condition' Object_is_defined_in_module_env(Object_id, MODULE_ENV)

  'rule' Object_is_defined_in_module_env(I, object_env(I1, ME)):
         (|
           eq(I,I1)
         ||
           I1'Env -> CE
           Object_is_defined_in_class_env(I, CE)
         ||
           Object_is_defined_in_module_env(I, ME)
         |)

'action' Type_defined_in_formals(Type_id, PARAM_FIT -> OPT_TYPE_ID, FOUND)

  'rule' Type_defined_in_formals(TI, param_fit(OI, I, Obj, AD, PF) -> Oid, Found):
         OI'Env -> CE
         (|
           Type_is_defined_in_class_env(TI, CE)
           where(found -> Found)
           TI'Qualifier -> Is
           TI'Ident -> Id
-- debug
-- Print_type(defined(TI, nil))
-- Putmsg(" defined in formal ")
-- OI'Ident -> OId
-- Print_id(OId)
           TI'Pos -> P
           Make_name(P, id_op(Id), Is, CE -> ON)
           (|
             where(ON -> act_name(N))
             I'Env -> CE1
             Lookup_env_type_name(N, CE1, nil, nil -> Oid)
-- debug
-- (|
-- where(Oid -> type_id(TI1))
-- Putmsg(" and found as ")
-- Print_type(defined(TI1, nil))
-- ||
-- Putmsg(" but not found")
-- |)
-- Putnl()
           ||
             where(OPT_TYPE_ID'nil -> Oid)
-- debug
-- Putmsg(" but hidden")
-- Putnl()
           |)
         ||
           Type_defined_in_formals(TI, PF -> Oid, Found)
         |)

  'rule' Type_defined_in_formals(TI, nil -> nil, nil):

'action' Object_defined_in_formals(Object_id, PARAM_FIT -> OPT_OBJECT_ID, FOUND)

  'rule' Object_defined_in_formals(TI, param_fit(OI, I, Obj, AD, PF) -> Oid, Found):
         TI'Ident -> Id
         (|
           eq(TI, OI)
           where(object_id(I) -> Oid)
           where(found -> Found)
-- debug
-- Putmsg("Object ")
-- Print_id(Id)
-- print(TI)
-- Putmsg(" found as formal ")
-- print(OI)
-- Putmsg(" rebound to ")
-- print(I)
-- Putnl()
         ||
           OI'Env -> CE
           (|
             Object_is_defined_in_class_env(TI, CE)
             where(found -> Found)
             TI'Qualifier -> Is
             TI'Pos -> P
             Make_name(P, id_op(Id), Is, CE -> ON)
             (|
               where(ON -> act_name(N))
               I'Env -> CE1
               Lookup_object_in_env(obj_name(N), CE1, nil -> Oid)
             ||
               where(OPT_OBJECT_ID'nil -> Oid)
             |)
           ||
             Object_defined_in_formals(TI, PF -> Oid, Found)
           |)
         |)

  'rule' Object_defined_in_formals(TI, nil -> nil, nil):

-- returns Variable_id if found and not hidden, 
-- nil and Object_id if hidden in object
'action' Variable_defined_in_formals(Variable_id, PARAM_FIT -> OPT_VARIABLE_ID, OPT_OBJECT_ID, FOUND)

  'rule' Variable_defined_in_formals(TI, param_fit(OI, I, Obj, AD, PF) -> Oidv, Oido, Found):
         OI'Env -> CE
         (|
           Variable_is_defined_in_class_env(TI, CE)
           where(found -> Found)
           TI'Qualifier -> Is
           TI'Ident -> Id
           TI'Pos -> P
           Make_name(P, id_op(Id), Is, CE -> ON)
           (|
             where(ON -> act_name(N))
             I'Env -> CE1
             Lookup_env_variable_name(N, CE1, nil, nil -> Oidv)
             where(OPT_OBJECT_ID'nil -> Oido)
           ||
             where(ON -> hidden(N))
             I'Env -> CE1
             Lookup_object_in_env(obj_name(N), CE1, nil -> Oido)
             where(OPT_VARIABLE_ID'nil -> Oidv)
           ||
             where(OPT_VARIABLE_ID'nil -> Oidv)
             where(OPT_OBJECT_ID'nil -> Oido)
           |)
         ||
           Variable_defined_in_formals(TI, PF -> Oidv, Oido, Found)
         |)

  'rule' Variable_defined_in_formals(TI, nil -> nil, nil, nil):

-- returns Channel_id if found and not hidden, 
-- nil and Object_id if hidden in object
'action' Channel_defined_in_formals(Channel_id, PARAM_FIT -> OPT_CHANNEL_ID, OPT_OBJECT_ID, FOUND)

  'rule' Channel_defined_in_formals(TI, param_fit(OI, I, Obj, AD, PF) -> Oidc, Oido, Found):
         OI'Env -> CE
         (|
           Channel_is_defined_in_class_env(TI, CE)
           where(found -> Found)
           TI'Qualifier -> Is
           TI'Ident -> Id
           TI'Pos -> P
           Make_name(P, id_op(Id), Is, CE -> ON)
           (|
             where(ON -> act_name(N))
             I'Env -> CE1
             Lookup_env_channel_name(N, CE1, nil, nil -> Oidc)
             where(OPT_OBJECT_ID'nil -> Oido)
           ||
             where(ON -> hidden(N))
             I'Env -> CE1
             Lookup_object_in_env(obj_name(N), CE1, nil -> Oido)
             where(OPT_CHANNEL_ID'nil -> Oidc)
           ||
             where(OPT_CHANNEL_ID'nil -> Oidc)
             where(OPT_OBJECT_ID'nil -> Oido)
           |)
         ||
           Channel_defined_in_formals(TI, PF -> Oidc, Oido, Found)
         |)

  'rule' Channel_defined_in_formals(TI, nil -> nil, nil, nil):

-- no longer used
'action' Make_name_depth(POS, ID_OR_OP, Object_ids, INT, CLASS_ENV -> OPT_NAME)

  'rule' Make_name_depth(P, Id, Is, N, CE -> ON):
         Cut_to_depth(Is, N -> Is1)
         Make_name_depth1(P, Id, Is1, CE -> ON)

'action' Make_name_depth1(POS, ID_OR_OP, Object_ids, CLASS_ENV -> OPT_NAME)

  'rule' Make_name_depth1(P, Id, nil, CE -> ON):
         Unadapt_env_name(name(P, Id), CE -> ON)

  'rule' Make_name_depth1(P, Id, list(I2, Is), CE -> ON):
         I2'Ident -> Id2
         Unadapt_env_name(name(P, id_op(Id2)), CE -> ON2)
         (|
           where(ON2 -> act_name(N2))
           I2'Env -> CE2
           Make_name_depth1(P, Id, Is, CE2 -> ON1)
           (|
             where(ON1 -> act_name(N1))
             Qualify_name(obj_name(N2), N1 -> N)
             where(act_name(N) -> ON)
           ||
             where(ON1 -> hidden(N1))
             Qualify_name(obj_name(N2), N1 -> N)
             where(hidden(N) -> ON)
           ||
             where(hidden(N2) -> ON)
           |)
         ||
           where(ON2 -> ON)
         |)

'action' Cut_to_depth(Object_ids, INT -> Object_ids)

  'rule' Cut_to_depth(Ids, N -> Ids1):
         Length_ids(Ids -> L)
         Prune(Ids, L-N -> Ids1)

'action' Length_ids(Object_ids -> INT)

  'rule' Length_ids(list(H,T) -> N+1):
         Length_ids(T -> N)

  'rule' Length_ids(nil -> 0):

'action' Prune(Object_ids, INT -> Object_ids)

  'rule' Prune(Is, N -> Is):
         le(N, 0)

  'rule' Prune(list(_, Is), N -> Is1):
         Prune(Is, N-1 -> Is1)

  'rule' Prune(nil, _ -> nil):

-- first qualifier ignored as it is the formal object
-- (or, for implementation_expr, dummy)
-- and we will search within the corresponding actual class
'action' Make_name(POS, ID_OR_OP, Object_ids, CLASS_ENV -> OPT_NAME)

  'rule' Make_name(P, Id, list(_, nil), CE -> ON):
         Unadapt_env_name(name(P, Id), CE -> ON)

  'rule' Make_name(P, Id, list(_, list(I2, Is)), CE -> ON):
         I2'Ident -> Id2
         Unadapt_env_name(name(P, id_op(Id2)), CE -> ON2)
         (|
           where(ON2 -> act_name(N2))
           I2'Env -> CE2
           Make_name(P, Id, list(I2, Is), CE2 -> ON1)
           (|
             where(ON1 -> act_name(N1))
             Qualify_name(obj_name(N2), N1 -> N)
             where(act_name(N) -> ON)
           ||
             where(ON1 -> hidden(N1))
             Qualify_name(obj_name(N2), N1 -> N)
             where(hidden(N) -> ON)
           ||
             where(hidden(N2) -> ON)
           |)
         ||
           where(ON2 -> ON)
         |)

'action' Unadapt_env_name(NAME, CLASS_ENV -> OPT_NAME)

  'rule' Unadapt_env_name(N, instantiation_env(_, CE) -> ON):
         Unadapt_env_name(N, CE -> ON)

  'rule' Unadapt_env_name(N, basic_env(_,_,_,_,_,_,_,_,_,_,AD) -> ON):
         Unadapt_name(N, AD, hide -> ON)

  'rule' Unadapt_env_name(N, extend_env(_, CE2, _, AD) -> ON):
         (|
           Unadapt_env_name(N, CE2 -> act_name(N1))
           Unadapt_name(N1, AD, hide -> ON)
         ||
           where(OPT_NAME'nil -> ON)
         |)

'action' Unadapt_name(NAME, ADAPTS, HIDE -> OPT_NAME)

  'rule' Unadapt_name(N, hide(Id, Ads), hide -> ON):
         Unadapt_name(N, Ads, hide -> ON1)
         (|
           where(ON1 -> act_name(N1))
           Hide_name(N1, Id -> ON)
         ||
           where(OPT_NAME'nil -> ON)
         |)

  'rule' Unadapt_name(N, hide(Id, Ads), no_hide -> ON):
         Unadapt_name(N, Ads, no_hide -> ON)

  'rule' Unadapt_name(N, rename(Id1, Id2, Ads), Hide -> ON):
         Unadapt_name(N, Ads, Hide -> ON1)
         (|
           where(ON1 -> act_name(N1))
           Rename_name(N1, Id1, Id2 -> ON)
         ||
           where(OPT_NAME'nil -> ON)
         |)       

  'rule' Unadapt_name(N, nil, _ -> act_name(N)):

'action' Hide_name(NAME, ID_OR_OP -> OPT_NAME)

  'rule' Hide_name(name(P, Id), Id1 -> ON):
         (|
           eq(Id, Id1)
           where(OPT_NAME'nil -> ON)
         ||
           where(act_name(name(P, Id)) -> ON)
         |)

'action' Rename_name(NAME, ID_OR_OP, ID_OR_OP -> OPT_NAME)

  'rule' Rename_name(name(P, Id), Id1, Id2 -> act_name(name(P, Id3))):
         (|
           eq(Id, Id2)
           where(Id1 -> Id3)
         ||
           where(Id -> Id3)
         |)                

'action' Qualify_name(OBJECT_EXPR, NAME -> NAME) 

  'rule' Qualify_name(Obj, name(P,Id) -> qual_name(P,Obj,Id)):
         
  'rule' Qualify_name(Obj1, qual_name(P,Obj2,Id) -> qual_name(P,Obj3,Id)):
         Concat_objs(Obj1, Obj2 -> Obj3)

'action' Concat_objs(OBJECT_EXPR, OBJECT_EXPR ->  OBJECT_EXPR)

  'rule' Concat_objs(Obj1, obj_appl(Obj2, A) -> obj_appl(Obj3, A)):
         Concat_objs(Obj1, Obj2 -> Obj3)

  'rule' Concat_objs(Obj1, obj_fit(Obj2, F) -> obj_fit(Obj3, F)):
         Concat_objs(Obj1, Obj2 -> Obj3)

  'rule' Concat_objs(Obj, obj_name(name(P,Id)) -> obj_name(qual_name(P, Obj, Id))):

  'rule' Concat_objs(Obj1, obj_name(qual_name(P, Obj2, Id)) -> obj_name(qual_name(P, Obj3, Id))):
         Concat_objs(Obj1, Obj2 -> Obj3)

'action' Check_types_implementation(POS, ADAPTS, TYPE_ENV, ADAPTS)

  'rule' Check_types_implementation(EP, Fit, type_env(I, TE), Ads):
         I'Ident -> Id
         I'Pos -> P
	 Type_of(I -> T)
-- debug
-- Putmsg("Looking for type ")
-- Print_id(Id)
-- Putmsg(" full name ")
-- Print_type(defined(I, nil))
         Unadapt_name(name(P, id_op(Id)), Ads, hide -> ON)
         [|
           where(ON -> act_name(name(P1, id_op(Id1))))
           Unadapt(id_op(Id1), Fit -> id_op(Id2))
-- debug
-- Putmsg(" with adapts ")
-- Print_adapts(Ads)
-- Putmsg(" unadapted to ")
-- Print_id(Id1)
-- Putmsg(" with fits ")
-- Print_adapts(Fit)
-- Putmsg(" and fitted to ")
-- Print_id(Id2)
-- Putnl()
           Current -> C
-- print(C)
           Extend_paths -> Paths
           (|
             Lookup_current_type_name(name(P1, id_op(Id2)), C, Paths, nil, nil -> type_id(I1))
-- print(I1)
	     Type_of(I1 -> T1)
             (|
               Match(T, nil, T1)
-- Putmsg("Matching ")
-- Print_type(T)
-- Putnl()
-- print(T)
-- Putmsg(" to ")
-- Print_type(T1)
-- Putnl()
-- print(T1)
             ||
               Puterror(EP)
               Putmsg("Type identifier ")
               Print_id(Id1)
               Putmsg(" of type ")
               Print_type(T)
               Putnl()
-- debug
-- print(T)
               Putmsg(" is not implemented by type ")
               Print_type(T1)
               Putnl()
-- debug
-- print(T1)
             |)
           ||
             Puterror(EP)
             Putmsg("Type identifier ")
             Print_id(Id1)
             Putmsg(" is not implemented")
             Putnl()
           |)
         |]
         Check_types_implementation(EP, Fit, TE, Ads)    

  'rule' Check_types_implementation(EP, Fit, nil, Ads):

'action' Check_values_implementation(POS, ADAPTS, Value_ids, ADAPTS)

  'rule' Check_values_implementation(EP, Fit, list(I, VE), Ads):
         I'Ident -> Id
         I'Pos -> P
         I'Type -> T
-- debug
-- Putmsg("Looking for value ")
-- Print_id_or_op(Id)
         Unadapt_name(name(P, Id), Ads, hide -> ON)
         [|
           where(ON -> act_name(name(P1, Id1)))
           Unadapt(Id1, Fit -> Id2)
-- debug
-- Putmsg(" with adapts ")
-- Print_adapts(Ads)
-- Putmsg(" unadapted to ")
-- Print_id_or_op(Id1)
-- Putmsg(" and fitted to ")
-- Print_id_or_op(Id2)
-- Putnl()
           Current -> C
           Extend_paths -> Paths
           Lookup_current_value_name(name(P1, Id2), C, Paths, nil, nil -> Ids)
           (|
             where(Id2 -> op_op(Op))
             Lookup_op_types(Op -> Ids1)
             Union_ids(Ids1, Ids -> Ids2) 
           ||
             where(Ids -> Ids2)
           |)
           (|
	     ne(Ids2, nil)  
             (|
	       Supertype_of_vals(T, Ids2)
	     ||
	       Puterror(EP)
	       Putmsg("Value identifier ")
	       Print_id_or_op(Id1)
	       Putmsg(" with expected type ")
	       Print_type(T)
	       Putmsg(" not found")
	       Putnl()
-- debug
-- Putmsg("Expected_type ")
-- Print_type(T)
-- Putnl()
-- print(T)
-- [|
--   where(Ids2 -> list(I1, Ids3))
--   Putmsg(" actual type ")
--   I1'Type -> T2
--   Print_type(T2)
--   Putnl()
--   print(T2)
-- |]
-- Putmsg("Fitting is\n")
-- print(Fit)
-- debug
-- print(T)
-- print(Ids2)
-- Current -> Curr
-- print(Curr)
-- Get_current_types(-> TE)
-- Print_type_env(TE)
             |)
	   ||
	     Puterror(EP)
	     Putmsg("Value identifier ")
	     Print_id_or_op(Id1)
	     Putmsg(" is not implemented")
	     Putnl()
           |)
         |]
         Check_values_implementation(EP, Fit, VE, Ads)   

  'rule' Check_values_implementation(EP, Fit, nil, Ads):

'action' Check_variables_implementation(POS, ADAPTS, VARIABLE_ENV, ADAPTS)

  'rule' Check_variables_implementation(EP, Fit, variable_env(I, VE), Ads):
         I'Ident -> Id
         I'Pos -> P
         I'Type -> T
         Unadapt_name(name(P, id_op(Id)), Ads, hide -> ON)
         [|
           where(ON -> act_name(name(P1, Id1)))
           Unadapt(Id1, Fit -> Id2)
           Current -> C
           Extend_paths -> Paths
           (|
             Lookup_current_variable_name(name(P1, Id2), C, Paths, nil, nil -> variable_id(I1))
             I1'Type -> T1
-- debug
-- Putmsg("For variable ")
-- Print_id(Id)
-- Putmsg(" old type ")
-- Print_type(T)
-- Putnl()
-- print(T)
-- Putmsg("new type ")
-- Print_type(T1)
-- Putnl()
-- print(T1)
             (|
	       Match(T1, nil, T)
	     ||
	       Puterror(EP)
	       Putmsg("Variable identifier ")
	       Print_id_or_op(Id1)
	       Putmsg(" with expected type ")
	       Print_type(T)
	       Putmsg(" not found")
	       Putnl()
	     |)
           ||
             Puterror(EP)
             Putmsg("Variable identifier ")
             Print_id_or_op(Id1)
             Putmsg(" is not implemented")
             Putnl()
           |)
         |]
         Check_variables_implementation(EP, Fit, VE, Ads)

  'rule' Check_variables_implementation(EP, Fit, nil, Ads):

'action' Check_channels_implementation(POS, ADAPTS, CHANNEL_ENV, ADAPTS)

  'rule' Check_channels_implementation(EP, Fit, channel_env(I, CHE), Ads):
         I'Ident -> Id
         I'Pos -> P
         I'Type -> T
         Unadapt_name(name(P, id_op(Id)), Ads, hide -> ON)
         [|
           where(ON -> act_name(name(P1, Id1)))
           Unadapt(Id1, Fit -> Id2)
           Current -> C
           Extend_paths -> Paths
           (|
             Lookup_current_channel_name(name(P1, Id2), C, Paths, nil, nil -> channel_id(I1))
             I1'Type -> T1
             (|
               Match(T1, nil, T)
	     ||
	       Puterror(EP)
	       Putmsg("Channel identifier ")
	       Print_id_or_op(Id1)
	       Putmsg(" with expected type ")
	       Print_type(T)
	       Putmsg(" not found")
	       Putnl()
	     |)
           ||
             Puterror(EP)
             Putmsg("Channel identifier ")
             Print_id_or_op(Id1)
             Putmsg(" is not implemented")
             Putnl()
           |)
         |]
         Check_channels_implementation(EP, Fit, CHE, Ads)        

  'rule' Check_channels_implementation(EP, Fit, nil, Ads):

'action' Check_modules_implementation(POS, ADAPTS, CLASS_ENV, MODULE_ENV, ADAPTS, PARAM_FIT)

  'rule' Check_modules_implementation(EP, Fit, BCE, object_env(I, ME), Ads, PFC):
         I'Pos -> P
         I'Ident -> Id
         I'Env -> CE
         Unadapt_name(name(P, id_op(Id)), Ads, hide -> ON)
         [|
           where(ON -> act_name(name(P1, id_op(Id1))))
           Unadapt(id_op(Id1), Fit -> id_op(Id2))
           (|
             Current -> C1
             Extend_paths -> Paths1
             Lookup_object_in_current_env(Id2, C1, Paths1, nil, nil -> object_id(I1), _)
             I1'Env -> CE1
             Current <- current_env(CE1, C1)
             Extend_paths <- list(nil,Paths1)
             -- Unfold_types(BCE, CE, PFC -> CE2)
             Check_implementation(EP, nil, BCE, CE, nil, PFC)
             Current -> current_env(_, C2)
             Current <- C2
             Extend_paths <- Paths1
           ||
             Puterror(EP)
             Putmsg("Object identifier ")
             Print_id(Id1)
             Putmsg(" is not implemented")
             Putnl()
           |)
         |]
         Check_modules_implementation(EP, Fit, BCE, ME, Ads, PFC)

  'rule' Check_modules_implementation(EP, Fit, BCE, nil, Ads, PFC):


'action' Get_polynum(Type_id, TYPE_NUMBER -> INT, TYPE_NUMBER)

  'rule' Get_polynum(I, type_number(I1, Num, TN) -> Num, TN):
         eq(I,I1)

  'rule' Get_polynum(I, type_number(I1, Num, TN) -> Num1, type_number(I1, Num, TN1)):
         Get_polynum(I, TN -> Num1, TN1)

  'rule' Get_polynum(I, nil -> Num, type_number(I, Num, nil)):
         Polynum -> Num
         Polynum <- Num+1


-------------------------------------------------------------------------
-- Utilities
-------------------------------------------------------------------------

'action' Type_of(Type_id -> TYPE_EXPR)

  'rule' Type_of(I -> T)
         I'Type -> T1
         (|
           where(T1 -> abbrev(T))
         ||
           where(T1 -> sort(_))
           where(defined(I, nil) -> T)
         ||
           where(TYPE_EXPR'any -> T) -- should be none?
         |)


