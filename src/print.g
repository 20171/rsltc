-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines various print functions

'module' print

'use' ast ext types env pp fdr_ast

'export'

   Print_id
   Print_ids
   Print_name
   Print_opt_qualification
   Print_object
   Print_type
   Print_expr
   Print_post_condition
   Print_id_or_op
   Print_objects
   Print_class
   Print_bindings
   Print_binding
   Print_op
   Print_qualifier
   Print_coercions
   Print_typing
   Print_typings
   Print_types
   Print_id_types
   Print_product_results_as_list
   Print_result
   Print_results
   Print_accesses
   Print_type_env
   Print_adapts
   Print_module_env
   Print_value_envs
   Print_value_env
   Print_module_deps
   Print_actual_function_parameters
   Print_actual_function_parameter
   Print_formal_function_parameters
   Print_formal_function_parameter
   Print_let_defs
   Print_let_def
   Print_decl
   Print_Extra_Guard

Print_type_def -- TODO: Debug delete

   Print_transition
   Print_assertion

   Op_to_print_string

   Is_dummy

   Lower_type_precedence
   Lower_expr_precedence
   Connective_precedence
   Operator_precedence

   Make_dependency_graph
   Remove_context_id

   Print_axiom_env
   Print_test_case_env

   Print_value_def	-- J890724, Univan
   Add_id		-- J890918, Univan
   Print_combinator	-- J891008, Univan
   Print_pattern	-- J891011, Univan
   Print_exprs		-- J891026, Univan
   Print_components
   Print_patterns

--Abigail added
  Get_module_id
  Find_module
  Op_to_print_string
  Print_alphabet
  

-------------------------------------------------
-- Modules
-------------------------------------------------

'action' Print_scheme_def(SCHEME_DEF)

  'rule' Print_scheme_def(sdef(P, ID, PARMS, C)):
         Putmsg("scheme ")
         Print_id(ID)
         [|
           ne(PARMS, nil)
           Putmsg("(")
           Print_object_defs(PARMS)
           Putmsg(")")
         |]
         Putmsg(" = ")
         Print_class(C)

'action' Print_object_defs(OBJECT_DEFS)

  'rule' Print_object_defs(list(H, nil)):
         Print_object_def(H)

  'rule' Print_object_defs(list(H, T)):
         Print_object_def(H)
         Putmsg(", ")
         Print_object_defs(T)

'action' Print_object_def(OBJECT_DEF)

  'rule' Print_object_def(odef(P, ID, PARMS, C)):
         Putmsg("object ")
         Print_id(ID)
         [|
           ne(PARMS, nil)
           Putmsg("[")
           Print_typings(PARMS)
           Putmsg("]")
         |]
         Putmsg(" : ")
         Print_class(C)

'action' Print_module_deps(LIB_MODULE, LIB_MODULES)

  'rule' Print_module_deps(M, G):
         Get_module_id(M -> Id)
         id_to_string(Id -> S)
         Putstdmsg(S)
         Putstdnl()
         Print_deps(1, M, G)

'action' Get_module_id(LIB_MODULE -> IDENT)

  'rule' Get_module_id(M -> Id):
         Get_module_id_kind(M -> Id, _)

'action' Get_module_id_kind(LIB_MODULE -> IDENT, MODULE_KIND)

  'rule' Get_module_id_kind(scheme(_, _, _, sdef(_, Id, _, _)) -> Id, scheme):

  'rule' Get_module_id_kind(object(_, _, _, odef(_, Id, _, _)) -> Id, object):

  'rule' Get_module_id_kind(theory(_, _, _, theory_def(_, Id, _)) -> Id, theory):

  'rule' Get_module_id_kind(devt_relation(_, _, _, devt_relation_def(_, Id, _, _, _)) -> Id, devt_relation):

-- debug
  'rule' Get_module_id_kind(M -> Id, scheme):
print(M)
         string_to_id("dummy" -> Id)

'action' Print_deps(INT, LIB_MODULE, LIB_MODULES)

  'rule' Print_deps(N, scheme(_, C, _, _), G):
         Print_context_deps(N, C, G)

  'rule' Print_deps(N, object(_, C, _, _), G):
         Print_context_deps(N, C, G)

  'rule' Print_deps(N, theory(_, C, _, _), G):
         Print_context_deps(N, C, G)

  'rule' Print_deps(N, devt_relation(_, C, _, _), G):
         Print_context_deps(N, C, G)

'action' Print_context_deps(INT, FILE_NAMES, LIB_MODULES)

  'rule' Print_context_deps(N, list(F, FS), G):
         Print_tabs(N)
         PrintFileId(F)
         Putstdnl()
         [|
           BaseName(F -> Id)
           Find_module(Id, G -> lib_mod(M))
           Print_deps(N+1, M, G)
         |]
         Print_context_deps(N, FS, G)
         
  'rule' Print_context_deps(_, nil, _):

'action' Print_tabs(INT)

  'rule' Print_tabs(N)
         (|
           eq(N, 0)
         ||
           Putstdmsg("\t")
           where(N-1 -> N1)
           Print_tabs(N1)
         |)

'action' Find_module(IDENT, LIB_MODULES -> OPT_LIB_MODULE)

  'rule' Find_module(Id, list(M1, M2) -> OM):
         (|
           Find_module1(Id, M1 -> lib_mod(M))
           where(lib_mod(M) -> OM)
         ||
           Find_module(Id, M2 -> OM)
         |)

  'rule' Find_module(Id, nil -> nil):

'action' Find_module1(IDENT, LIB_MODULE -> OPT_LIB_MODULE)

  'rule' Find_module1(Id, M -> lib_mod(M)):
         Get_module_id(M -> Id1)
         EqualFileId(Id, Id1)

  'rule' Find_module1(_, _ -> nil):
         

-------------------------------------------------
-- Class expressions
-------------------------------------------------

'action' Print_class(CLASS)

  'rule' Print_class(basic(DS)):
         Putmsg("class ")
         Print_decls(DS)
         Putmsg(" end")

  'rule' Print_class(extend(L, R)):
         Putmsg("extend ")
         Print_class(L)
         Putmsg(" with ")
         Print_class(R)

  'rule' Print_class(hide(DEFS, C)):
         Putmsg("hide ")
         Print_defineds(DEFS)
         Putmsg(" in ")
         Print_class(C)

  'rule' Print_class(rename(RS, C)):
         Putmsg("use ")
         Print_renames(RS)
         Putmsg(" in ")
         Print_class(C)

  'rule' Print_class(with(P, OS, C)):
         Putmsg("with ")
         Print_objects(OS)
         Putmsg(" in ")
         Print_class(C)

  'rule' Print_class(instantiation(N, nil)):
         Print_name(N)

  'rule' Print_class(instantiation(N, OS)):
         Print_name(N)
         Putmsg("(")
         Print_objects(OS)
         Putmsg(")")

'action' Print_renames(RENAMES)

  'rule' Print_renames(list(H, nil)):
         Print_rename(H)
         
  'rule' Print_renames(list(H, T)):
         Print_rename(H)
         Putmsg(", ")
         Print_renames(T)
        
'action' Print_rename(RENAME)

  'rule' Print_rename(rename(L, R)):
         Print_defined(L)
         Putmsg(" for ")
         Print_defined(R)

'action' Print_defineds(DEFINEDS)

  'rule' Print_defineds(list(H, nil)):
         Print_defined(H)

  'rule' Print_defineds(list(H, T)):
         Print_defined(H)
         Putmsg(", ")
         Print_defineds(T)

'action' Print_defined(DEFINED)

  'rule' Print_defined(def_name(P, ID)):
         Print_id_or_op(ID)

  'rule' Print_defined(disamb(P, ID, T)):
         Print_id_or_op(ID)
         Putmsg(" : ")
         Print_type(T)

-----------------------------------------------------------------------------
-- Declarations
-----------------------------------------------------------------------------

'action' Print_decls(DECLS)

  'rule' Print_decls(list(H, nil)):
         Print_decl(H)

  'rule' Print_decls(list(H, T)):
         Print_decl(H)
         Putmsg(", ")
         Print_decls(T)

  'rule' Print_decls(nil):

'action' Print_decl(DECL)

  'rule' Print_decl(type_decl(P, DS)):
         Putmsg("type ")
         Print_type_defs(DS)

  'rule' Print_decl(value_decl(P, DS)):
         Putmsg("value ")
         Print_value_defs(DS)

  'rule' Print_decl(variable_decl(P, DS)):
         Putmsg("variable ")
         Print_variable_defs(DS)

  'rule' Print_decl(channel_decl(P, DS)):
         Putmsg("channel ")
         Print_channel_defs(DS)

  'rule' Print_decl(object_decl(P, DS)):
         Putmsg("object ")
         Print_object_defs(DS)

  'rule' Print_decl(axiom_decl(P, DS)):
         Putmsg("axiom ")
         Print_axiom_defs(DS)

  'rule' Print_decl(test_case_decl(P, DS)):
         Putmsg("test_case ")
         Print_test_case_defs(DS)

  'rule' Print_decl(trans_system_decl(P, DS))
	 Putmsg("transition_system ")
	 Print_transition(DS)

  'rule' Print_decl(property_decl(P, DS))
	 Putmsg("ltl_assertion ")
	 Print_assertion(DS)

'action' Print_type_defs(TYPE_DEFS)

  'rule' Print_type_defs(list(H, nil)):
         Print_type_def(H)

  'rule' Print_type_defs(list(H, T)):
         Print_type_def(H)
         Putmsg(", ")
         Print_type_defs(T)

'action' Print_type_def(TYPE_DEF)

  'rule' Print_type_def(sort(P, ID)):
         Print_id(ID)

  'rule' Print_type_def(abbrev(P, ID, T)):
         Print_id(ID)
         Putmsg(" = ")
         Print_type(T)

  'rule' Print_type_def(variant(P, ID, VS)):
         Print_id(ID)
         Putmsg(" == ")
         Print_variants(VS)

  'rule' Print_type_def(record(P, ID, CS)):
         Print_id(ID)
         Putmsg(" :: ")
         Print_components(CS)

  'rule' Print_type_def(union(P, ID, CS)):
         Print_id(ID)
         Putmsg(" = ")
         Print_choices(CS)

'action' Print_variants(VARIANTS)

  'rule' Print_variants(list(H, nil)):
         Print_variant(H)

  'rule' Print_variants(list(H, T)):
         Print_variant(H)
         Putmsg(" | ")
         Print_variants(T)

'action' Print_variant(VARIANT)

  'rule' Print_variant(record(P, C, CS)):
         Print_constructor(C)
         Putmsg("(")
         Print_components(CS)
         Putmsg(")")

'action' Print_components(COMPONENTS)

  'rule' Print_components(list(H, nil)):
         Print_component(H)

  'rule' Print_components(list(H, T)):
         Print_component(H)
         Putmsg(", ")
         Print_components(T)

  'rule' Print_components(nil):

'action' Print_component(COMPONENT)

  'rule' Print_component(component(P, D, T, R)):
         [|
           ne(D, nil)
           Print_destructor(D)
           Putmsg(" : ")
         |]
         Print_type(T)
         [|
           ne(R, nil)
           Putmsg(" <-> ")
           Print_reconstructor(R)
         |]

'action' Print_constructor(CONSTRUCTOR)

  'rule' Print_constructor(constructor(P, ID)):
         Print_id_or_op(ID)

  'rule' Print_constructor(con_ref(I))
	 I'Ident -> ID
         Print_id_or_op(ID)

  'rule' Print_constructor(wildcard):
         Putmsg("_")

'action' Print_destructor(DESTRUCTOR)

  'rule' Print_destructor(destructor(P, ID)):
         Print_id_or_op(ID)

  'rule' Print_destructor(dest_ref(I))
	 I'Ident -> ID
         Print_id_or_op(ID)

'action' Print_reconstructor(RECONSTRUCTOR)

  'rule' Print_reconstructor(reconstructor(P, ID)):
         Print_id_or_op(ID)

  'rule' Print_reconstructor(recon_ref(I))
	 I'Ident -> ID
         Print_id_or_op(ID)

'action' Print_choices(CHOICES)

  'rule' Print_choices(list(H, nil)):
         Print_choice(H)

  'rule' Print_choices(list(H, T)):
         Print_choice(H)
         Putmsg(" | ")
         Print_choices(T)

'action' Print_choice(CHOICE)

  'rule' Print_choice(choice(P, N)):
         Print_name(N)
  
  'rule' Print_choice(nil):
         Putmsg("_")

--------------------------------------------------------
-- Value definitions
--------------------------------------------------------

           
'action' Print_value_defs(VALUE_DEFS)

  'rule' Print_value_defs(list(H, nil)):
         Print_value_def(H)

  'rule' Print_value_defs(list(H, T)):
         Print_value_def(H)
         Putmsg(", ")
         Print_value_defs(T)

'action' Print_value_def(VALUE_DEF)

  'rule' Print_value_def(typing(P, T)):
         Print_typing(T)

  'rule' Print_value_def(exp_val(P, T, E)):
         Print_typing(T)
         Putmsg(" = ")
         Print_expr(E)

  'rule' Print_value_def(imp_val(P, T, R)):
         Print_typing(T)
         Print_restriction(R)

  'rule' Print_value_def(exp_fun(P, T, A, E, POST, PRE, _)):
         Print_typing(T)
         Putmsg(" ")
         Print_formal_function_application(A)
         Putmsg(" is ")
	 (|
	   Lower_expr_precedence(E, 14)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
         Print_expr(E1)
	 Print_opt_post_condition(POST)
         Print_pre_condition(PRE)

  'rule' Print_value_def(imp_fun(P, T, A, POST, PRE)):
         Print_typing(T)
         Putmsg(" ")
         Print_formal_function_application(A)
         Print_post_condition(POST)
         Print_pre_condition(PRE)

'action' Print_formal_function_application(FORMAL_FUNCTION_APPLICATION)

  'rule' Print_formal_function_application(form_appl(P, id_op(ID), PARMS)):
         Print_id(ID)
         Print_formal_function_parameters(PARMS)

  'rule' Print_formal_function_application(form_appl(P, op_op(OP), PARMS)):
         where(PARMS -> list(PS, nil))
         (|
           where(PS -> form_parm(P1, list(B, nil)))
           Print_op(OP)
           Putmsg(" ")
           Print_binding(B)
         ||
           where(PS -> form_parm(P1, list(L, list(R, nil))))
           Print_binding(L)
           Putmsg(" ")
           Print_op(OP)
           Putmsg(" ")
           Print_binding(R)
         |)

'action' Print_formal_function_parameters(FORMAL_FUNCTION_PARAMETERS)

  'rule' Print_formal_function_parameters(list(H, T)):
         Print_formal_function_parameter(H)
         Print_formal_function_parameters(T)

  'rule' Print_formal_function_parameters(nil):


'action' Print_formal_function_parameter(FORMAL_FUNCTION_PARAMETER)

  'rule' Print_formal_function_parameter(form_parm(P, BS)):
         Putmsg("(")
         Print_bindings(BS)
         Putmsg(")")

-------------------------------------------------
-- Variable definitions
-------------------------------------------------

'action' Print_variable_defs(VARIABLE_DEFS)

  'rule' Print_variable_defs(list(H, nil)):
         Print_variable_def(H)

  'rule' Print_variable_defs(list(H, T)):
         Print_variable_def(H)
         Putmsg(", ")
         Print_variable_defs(T)

'action' Print_variable_def(VARIABLE_DEF)

  'rule' Print_variable_def(single(P, ID, T, INIT)):
         Print_id(ID)
         Putmsg(" : ")
         Print_type(T)
         Print_initialisation(INIT)

  'rule' Print_variable_def(multiple(P, IDS, T)):
         Print_ids(IDS)
         Putmsg(" : ")
         Print_type(T)

'action' Print_initialisation(INITIALISATION)

  'rule' Print_initialisation(initial(E)):
         Putmsg(" := ")
         Print_expr(E)

  'rule' Print_initialisation(nil):

-------------------------------------------------
-- Channel definitions
-------------------------------------------------

'action' Print_channel_defs(CHANNEL_DEFS)

  'rule' Print_channel_defs(list(H, nil)):
         Print_channel_def(H)

  'rule' Print_channel_defs(list(H, T)):
         Print_channel_def(H)
         Putmsg(", ")
         Print_channel_defs(T)

'action' Print_channel_def(CHANNEL_DEF)

  'rule' Print_channel_def(single(P, ID, T)):
         Print_id(ID)
         Putmsg(" : ")
         Print_type(T)

  'rule' Print_channel_def(multiple(P, IDS, T)):
         Print_ids(IDS)
         Putmsg(" : ")
         Print_type(T)

-------------------------------------------------
-- Transition systems and assertions
-------------------------------------------------
'action' Print_transition(TRANSITION_SYS_DEFS)

  'rule' Print_transition(list(trans_sys_def(_, Ident,_), Rest)):
	 Putnl()
	 Putmsg("[")
	 Print_id(Ident)
         Putmsg("]")
	 Print_transition(Rest)

  'rule' Print_transition(nil):

'action' Print_assertion(PROPERTY_DECLS)

  'rule' Print_assertion(list(property_def(_, Id,_,_), Rest)):
	 Putnl()
	 Putmsg("[")
	 Print_id(Id)
         Putmsg("]")
	 Print_assertion(Rest)

  'rule' Print_assertion(nil):
-------------------------------------------------
-- Axiom definitions
-------------------------------------------------

'action' Print_axiom_defs(AXIOM_DEFS)

  'rule' Print_axiom_defs(list(H, nil)):
         Print_axiom_def(H)

  'rule' Print_axiom_defs(list(H, T)):
         Print_axiom_def(H)
         Putmsg(", ")
         Print_axiom_defs(T)

'action' Print_axiom_def(AXIOM_DEF)

  'rule' Print_axiom_def(axiom_def(P, ON, E)):
         [|
           where(ON -> ident(ID))
           Putmsg("[")
           Print_id(ID)
           Putmsg("] ")
         |]
         Print_expr(E)

-------------------------------------------------
-- Test_case definitions
-------------------------------------------------

'action' Print_test_case_defs(TEST_CASE_DEFS)

  'rule' Print_test_case_defs(list(H, nil)):
         Print_test_case_def(H)

  'rule' Print_test_case_defs(list(H, T)):
         Print_test_case_def(H)
         Putmsg(", ")
         Print_test_case_defs(T)

'action' Print_test_case_def(TEST_CASE_DEF)

  'rule' Print_test_case_def(test_case_def(P, ON, E)):
         [|
           where(ON -> ident(ID))
           Putmsg("[")
           Print_id(ID)
           Putmsg("] ")
         |]
         Print_expr(E)

-------------------------------------------------
-- Object expressions
-------------------------------------------------

'action' Print_objects(OBJECT_EXPRS)

  'rule' Print_objects(list(Object,nil)):
         Print_object(Object)

  'rule' Print_objects(list(Object,Objects)):
         Print_object(Object)
         Putmsg(", ")
         Print_objects(Objects)

  'rule' Print_objects(nil):

'action' Print_object(OBJECT_EXPR)

  'rule' Print_object(obj_name(N)):
         Print_name(N)

  'rule' Print_object(obj_appl(Obj, A)):
         Print_object(Obj)
         Putmsg("[")
         Print_exprs(A)
         Putmsg("]")

  'rule' Print_object(obj_array(TS, Obj)):
         Putmsg("[|")
         Print_typings(TS)
         Putmsg(" :- ")
         Print_object(Obj)
         Putmsg("|]")

  'rule' Print_object(obj_fit(Obj, F)):
         Print_object(Obj)
         Putmsg("{")
         Print_renames(F)
         Putmsg("}")

  'rule' Print_object(obj_occ(_, I)):
--	 [|
--	   I'Qualifier -> list(Id,Ids)
--	   Print_qualifier(list(Id,Ids))
--	 |]
         I'Ident -> ID
         Print_id(ID)

  'rule' Print_object(qual_occ(_, Obj, I)):
         Print_object(Obj)
         Putmsg(".")
         I'Ident -> ID
         Print_id(ID)    


-------------------------------------------------
-- Type expressions
-------------------------------------------------

'action' Print_type(TYPE_EXPR)

  'rule' Print_type(unit):
         Putmsg("Unit")

  'rule' Print_type(bool):
         Putmsg("Bool")

  'rule' Print_type(int):
         Putmsg("Int")

  'rule' Print_type(nat):
         Putmsg("Nat")

  'rule' Print_type(real):
         Putmsg("Real")

  'rule' Print_type(text):
         Putmsg("Text")

  'rule' Print_type(char):
         Putmsg("Char")

  'rule' Print_type(time):
         Putmsg("Time")

  'rule' Print_type(named_type(N)):
         Print_name(N)

  'rule' Print_type(defined(I, Q)):
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id,Ids)
	   Print_qualifier(list(Id,Ids))
	 ||
           Print_opt_qualification(Q)
	 |)
         I'Ident -> Id
         Print_id(Id)
         [|
           HasErrors()
           I'Type -> abbrev(_)
           Unfold_type_id(I -> T1)
           (|
             where(T1 -> poly(N))
           ||
             Putmsg(" (i.e. ")
             Print_type(T1)
             Putmsg(")")
           |)
         |]

  'rule' Print_type(product(PR)):
         Print_type_prod(PR)

  'rule' Print_type(fin_set(T)):
         (|
           Lower_type_precedence(T, 1)
           where(T -> T1)
         ||
           where(TYPE_EXPR'bracket(T) -> T1)
         |)
         Print_type(T1)
         Putmsg("-set")

  'rule' Print_type(infin_set(T)):
         (|
           Lower_type_precedence(T, 1)
           where(T -> T1)
         ||
           where(TYPE_EXPR'bracket(T) -> T1)
         |)
         Print_type(T1)
         Putmsg("-infset")

  'rule' Print_type(fin_list(T)):
         (|
           Lower_type_precedence(T, 1)
           where(T -> T1)
         ||
           where(TYPE_EXPR'bracket(T) -> T1)
         |)
         Print_type(T1)
         Putmsg("-list")

  'rule' Print_type(infin_list(T)):
         (|
           Lower_type_precedence(T, 1)
           where(T -> T1)
         ||
           where(TYPE_EXPR'bracket(T) -> T1)
         |)
         Print_type(T1)
         Putmsg("-inflist")

  'rule' Print_type(fin_map(D,R)):
         (|
           Lower_type_precedence(D, 3)
           where(D -> D1)
         ||
           where(TYPE_EXPR'bracket(D) -> D1)
         |)
         Print_type(D1)
         Putmsg(" -m-> ") 
         Print_type(R)

  'rule' Print_type(infin_map(D,R)):
         (|
           Lower_type_precedence(D, 3)
           where(D -> D1)
         ||
           where(TYPE_EXPR'bracket(D) -> D1)
         |)
         Print_type(D1)
         Putmsg(" -~m-> ") 
         Print_type(R)

  'rule' Print_type(function(D,A,R)):
         (|
           Lower_type_precedence(D, 3)
           where(D -> D1)
         ||
           where(TYPE_EXPR'bracket(D) -> D1)
         |)
         Print_type(D1)
         Print_arrow(A) 
         Print_type_res(R)

  'rule' Print_type(fun(D,A,R)):
         (|
           Lower_type_precedence(D, 3)
           where(D -> D1)
         ||
           where(TYPE_EXPR'bracket(D) -> D1)
         |)
         Print_type(D1)
         Print_arrow(A) 
         Print_result(R)

-- Subtypes are elided to make error messages more readable
  'rule' Print_type(subtype(single(P,B,T),R)):
         Putmsg("{|.")
         Print_type(T)
--       Print_restriction(R)
         Putmsg(".|}")

  'rule' Print_type(bracket(T)):
         Putmsg("(")
         Print_type(T)
         Putmsg(")")

  'rule' Print_type(any):
         Putmsg("any")

  'rule' Print_type(none):
         Putmsg("none")

  'rule' Print_type(array(D,R)):
         Putmsg("array with index-type ")
         Print_type(D)
         Putmsg(" and value-type ")
         Print_type(R)

  'rule' Print_type(poly(N)):
-- debug
-- Putint(N)
	 Print_poly(N)

'action' Print_type_prod(PRODUCT_TYPE)

  'rule' Print_type_prod(nil):

  'rule' Print_type_prod(list(H,nil)):
         (|
           Lower_type_precedence(H, 2)
           where(H -> H1)
         ||
           where(TYPE_EXPR'bracket(H) -> H1)
         |)
         Print_type(H1)

  'rule' Print_type_prod(list(H,T)):
         (|
           Lower_type_precedence(H, 2)
           where(H -> H1)
         ||
           where(TYPE_EXPR'bracket(H) -> H1)
         |)
         Print_type(H1)
         Putmsg(" >< ")
         Print_type_prod(T)

'action' Print_arrow(FUNCTION_ARROW)

  'rule' Print_arrow(partial):
         Putmsg(" -~-> ")

  'rule' Print_arrow(total):
         Putmsg(" -> ")

'action' Print_type_res(RESULT_DESC)

  'rule' Print_type_res(result(ADS,T))
         Print_access_descs(ADS)
         Print_type(T)

'action' Print_access_descs(ACCESS_DESCS)

  'rule' Print_access_descs(list(AD, nil)):
	 Print_access_desc(AD)
	 Putmsg(" ")

  'rule' Print_access_descs(list(AD,ADS)):
	 Print_access_desc(AD)
	 Putmsg(" ")
	 Print_access_descs(ADS)

  'rule' Print_access_descs(nil):

'action' Print_access_desc(ACCESS_DESC)

  'rule' Print_access_desc(access(M, AS)):
	 Print_access_mode(M)
	 Print_accesses(AS)

'action' Print_access_mode(ACCESS_MODE)

  'rule' Print_access_mode(read):
	 Putmsg("read ")

  'rule' Print_access_mode(write):
	 Putmsg("write ")

  'rule' Print_access_mode(in):
	 Putmsg("in ")

  'rule' Print_access_mode(out):
	 Putmsg("out ")

'action' Print_accesses(ACCESSES)

  'rule' Print_accesses(list(A, nil)):
         Print_access(A)

  'rule' Print_accesses(list(A, AS)):
         Print_access(A)
         Putmsg(", ")
         Print_accesses(AS)

  'rule' Print_accesses(nil):

'action' Print_access(ACCESS)

  'rule' Print_access(named_access(_, N)):
	 Print_name(N)

  'rule' Print_access(enumerated_access(_, AS)):
	 Putmsg("{")
	 Print_accesses(AS)
	 Putmsg("}")

  'rule' Print_access(completed_access(_, Q)):
	 Print_opt_qualification(Q)
	 Putmsg("any")

  'rule' Print_access(comprehended_access(_, A, L)):
	 Putmsg("{")
	 Print_access(A)
         Putmsg(" | ")
         Print_set_limitation(L)
         Putmsg("}")

  'rule' Print_access(variable(_, I, Q)):
         Print_opt_qualification(Q)
         I'Ident -> Id
         Print_id(Id)

  'rule' Print_access(channel(_, I, Q)):
         Print_opt_qualification(Q)
         I'Ident -> Id
         Print_id(Id)

  'rule' Print_access(free):
         Putmsg("free")







-------------------------------------------------
-- Value expressions
-------------------------------------------------

'action' Print_exprs(VALUE_EXPRS)

  'rule' Print_exprs(list(H, nil)):
         Print_expr(H)

  'rule' Print_exprs(list(H, T)):
         Print_expr(H)
         Putmsg(",")
         Print_exprs(T)

  'rule' Print_exprs(nil):

'action' Print_expr(VALUE_EXPR)

  'rule' Print_expr(literal_expr(P, E)):
         Print_value_literal(E)

  'rule' Print_expr(named_val(P, N)):
         Print_name(N)

  'rule' Print_expr(pre_name(P, N)):
         Print_name(N)
         Putmsg("`")

  'rule' Print_expr(chaos):
         Putmsg("chaos")

  'rule' Print_expr(skip):
         Putmsg("skip")

  'rule' Print_expr(stop):
         Putmsg("stop")

  'rule' Print_expr(swap):
         Putmsg("swap")

  'rule' Print_expr(product(P, ES)):
         Putmsg("(")
         Print_exprs(ES)
         Putmsg(")")

  'rule' Print_expr(ranged_set(P, L, R)):
         Putmsg("{")
         Print_expr(L)
         Putmsg("..")
         Print_expr(R)
         Putmsg("}")

  'rule' Print_expr(enum_set(P, ES)):
         Putmsg("{")
         Print_exprs(ES)
         Putmsg("}")

  'rule' Print_expr(comp_set(P, E, L)):
         Putmsg("{")
         Print_expr(E)
         Putmsg(" | ")
         Print_set_limitation(L)
         Putmsg("}")

  'rule' Print_expr(enum_list(P, ES)):
         Putmsg("<.")
         Print_exprs(ES)
         Putmsg(".>")

  'rule' Print_expr(ranged_list(P, L, R)):
         Putmsg("<.")
         Print_expr(L)
         Putmsg("..")
         Print_expr(R)
         Putmsg(".>")

  'rule' Print_expr(comp_list(P, E, L)):
         Putmsg("<.")
         Print_expr(E)
         Putmsg(" | ")
         Print_list_limitation(L)
         Putmsg(".>")

  'rule' Print_expr(enum_map(P, PS)):
         Putmsg("[")
         Print_value_expr_pairs(PS)
         Putmsg("]")

  'rule' Print_expr(comp_map(P, PR, L)):
         Putmsg("[")
         Print_value_expr_pair(PR)
         Putmsg(" | ")
         Print_set_limitation(L)
         Putmsg("]")

  'rule' Print_expr(function(P, PARM, E)):
         Putmsg("-\\")
         Print_lambda_parameter(PARM)
         Putmsg(":-")
         Print_expr(E)

-- special code for printing U, R, and W in LTL as infix
  'rule' Print_expr(application(P, E, ARGS)):
  	 Is_LTL_Wanted()
	 where(E -> val_occ(_, I, _))
	 Id_of_U -> U
	 Id_of_R -> R
	 Id_of_W -> W
	 (| eq(I, U) || eq(I, R) || eq(I, W) |)
	 where(ARGS -> list(ARG, nil))
	 where(ARG -> fun_arg(_,list(A1, list(A2, nil))))
	 Print_expr(bracket(P,A1))
	 Putmsg(" ")
	 Print_expr(E)
	 Putmsg(" ")
	 Print_expr(bracket(P,A2))
	 

  'rule' Print_expr(application(P, E, ARGS)):
	 (|
	   Lower_expr_precedence(E, 1)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
         Print_expr(E1)
         Print_actual_function_parameters(ARGS)

  'rule' Print_expr(quantified(P, Q, TS, R)):
         Print_quantifier(Q)
         Print_typings(TS)
         Print_restriction(R)
         
  'rule' Print_expr(equivalence(P, L, R, PRE)):
	 (|
	   Lower_expr_precedence(L, 14)
	   where(L -> L1)
	 ||
	   where(VALUE_EXPR'bracket(P,L) -> L1)
	 |)
         Print_expr(L1)
         Putmsg(" is ")
	 (|
	   Lower_expr_precedence(R, 14)
	   where(R -> R1)
	 ||
	   where(VALUE_EXPR'bracket(P,R) -> R1)
	 |)
         Print_expr(R1)
         Print_pre_condition(PRE)

  'rule' Print_expr(post(P, E, POST, PRE)):
	 (|
	   Lower_expr_precedence(E, 14)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
         Print_expr(E1)
         Print_post_condition(POST)
         Print_pre_condition(PRE)

  'rule' Print_expr(disamb(P, E, T)):
	 (|
	   Lower_expr_precedence(E, 3)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
         Print_expr(E1)
         Putmsg(" : ")
         Print_type(T)

  'rule' Print_expr(bracket(P, E)):
         Putmsg("(")
         Print_expr(E)
         Putmsg(")")

  'rule' Print_expr(ax_infix(P, L, C, R, _)):
	 Connective_precedence(C -> N)
	 (|
	   Lower_expr_precedence(L, N)
	   where(L -> L1)
	 ||
	   where(VALUE_EXPR'bracket(P,L) -> L1)
	 |)
         Print_expr(L1)
         Putmsg(" ")
         Print_connective(C)
         Putmsg(" ")
	 (|
	   Lower_expr_precedence(R, N)
	   where(R -> R1)
	 ||
	   where(VALUE_EXPR'bracket(P,R) -> R1)
	 |)
         Print_expr(R1)

  'rule' Print_expr(val_infix(P, L, O, R)):
	 Operator_precedence(O -> N)
	 (|
	   Lower_expr_precedence(L, N)
	   where(L -> L1)
	 ||
	   where(VALUE_EXPR'bracket(P,L) -> L1)
	 |)
         Print_expr(L1)
         Putmsg(" ")
         Print_op(O)
         Putmsg(" ")
	 (|
	   Lower_expr_precedence(R, N)
	   where(R -> R1)
	 ||
	   where(VALUE_EXPR'bracket(P,R) -> R1)
	 |)
         Print_expr(R1)

  'rule' Print_expr(stmt_infix(P, L, C, R)):
	 (|
	   eq(C,sequence)
	   where(12 -> N)
	 ||
	   where(13 -> N)
	 |)
	 (|
	   Lower_expr_precedence(L, N)
	   where(L -> L1)
	 ||
	   where(VALUE_EXPR'bracket(P,L) -> L1)
	 |)
         Print_expr(L1)
         Putmsg(" ")
         Print_combinator(C)
         Putmsg(" ")
	 (|
	   Lower_expr_precedence(R, N)
	   where(R -> R1)
	 ||
	   where(VALUE_EXPR'bracket(P,R) -> R1)
	 |)
         Print_expr(R1)

  'rule' Print_expr(always(P, E)):
         Putmsg("always ")
         Print_expr(E)

  'rule' Print_expr(ax_prefix(P, C, E)):
         Print_connective(C)
	 (|
	   Lower_expr_precedence(E, 3)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
         Print_expr(E1)

  'rule' Print_expr(val_prefix(P, O, E)):
         Print_op(O)
         (|
           (| eq(O, plus) || eq(O, minus) |)
         ||
           Putmsg(" ")
         |)
	 (|
	   Lower_expr_precedence(E, 3)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
         Print_expr(E1)

  'rule' Print_expr(comprehended(P, C, E, L)):
         Print_combinator(C)
         Putmsg("{")
         Print_expr(E)
         Putmsg(" | ")
         Print_set_limitation(L)
         Putmsg("}")

  'rule' Print_expr(initialise(P,O)):
         Print_opt_qualification(O)
         Putmsg("initialise")

  'rule' Print_expr(assignment(P, N, E)):
         Print_name(N)
         Putmsg(" := ")
	 (|
	   Lower_expr_precedence(E, 11)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
         Print_expr(E1)

  'rule' Print_expr(input(P, N)):
         Print_name(N)
         Putmsg("?")

  'rule' Print_expr(output(P, N, E)):
         Print_name(N)
         Putmsg("!")
	 (|
	   Lower_expr_precedence(E, 11)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
         Print_expr(E1)

  'rule' Print_expr(local_expr(P, DS, E)):
         Putmsg("local ")
         Print_decls(DS)
         Putmsg(" in ")
         Print_expr(E)
         Putmsg(" end")
         

  'rule' Print_expr(let_expr(P, DS, E)):
         Putmsg("let ")
         Print_let_defs(DS)
         Putmsg(" in ")
         Print_expr(E)
         Putmsg(" end")

  'rule' Print_expr(if_expr(P, E, THEN, RT, ELSIF, ELSE)):
         Putmsg("if ")
         Print_expr(E)
         Putmsg(" then ")
         Print_expr(THEN)
         Print_elsif_branches(ELSIF)
         Print_else_branch(ELSE)
         Putmsg(" end")

  'rule' Print_expr(case_expr(P, E, _, CS)):
         Putmsg("case ")
         Print_expr(E)
         Putmsg(" of ")
         Print_case_branches(CS)
         Putmsg(" end")

  'rule' Print_expr(while_expr(P, E, DO)):
         Putmsg("while ")
         Print_expr(E)
         Putmsg(" do ")
         Print_expr(DO)
         Putmsg(" end")

  'rule' Print_expr(until_expr(P, DO, E)):
         Putmsg("do ")
         Print_expr(DO)
         Putmsg(" until ")
         Print_expr(E)
         Putmsg(" end")

  'rule' Print_expr(for_expr(P, L, E)):
         Putmsg("for ")
         Print_list_limitation(L)
         Putmsg(" do ")
         Print_expr(E)
         Putmsg(" end")

  'rule' Print_expr(class_scope_expr(P, C, T)):
         Putmsg("in ")
         Print_class(C)
         Putmsg(" |- ")
         Print_expr(T)

  'rule' Print_expr(env_class_scope(P, C, _, T)):
	 Print_expr(class_scope_expr(P, C, T))

  'rule' Print_expr(implementation_relation(P, L, R)):
         Putmsg("|- ")
         Print_class(L)
         Putmsg(" {= ")
         Print_class(R)
         
  'rule' Print_expr(implementation_expr(P, L, R)):
         Putmsg("|- ")
         Print_object(L)
         Putmsg(" {= ")
         Print_object(R)

  'rule' Print_expr(val_occ(P, I, Q)):
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id,Ids)
	   Print_qualifier(list(Id,Ids))
	 ||
           Print_opt_qualification(Q)
	 |)
         I'Ident -> Id
         Print_id_or_op(Id)
         
  'rule' Print_expr(var_occ(P, I, Q)):
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id,Ids)
	   Print_qualifier(list(Id,Ids))
	 ||
           Print_opt_qualification(Q)
	 |)
         I'Ident -> Id
         Print_id(Id)
         
  'rule' Print_expr(pre_occ(P, I, Q)):
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id,Ids)
	   Print_qualifier(list(Id,Ids))
	 ||
           Print_opt_qualification(Q)
	 |)
         I'Ident -> Id
         Print_id(Id)
         Putmsg("`")

  'rule' Print_expr(ass_occ(P, I, Q, V)):
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id,Ids)
	   Print_qualifier(list(Id,Ids))
	 ||
           Print_opt_qualification(Q)
	 |)
         I'Ident -> Id
         Print_id(Id)
         Putmsg(" := ")
	 (|
	   Lower_expr_precedence(V, 11)
	   where(V -> V1)
	 ||
	   where(VALUE_EXPR'bracket(P,V) -> V1)
	 |)
         Print_expr(V1)

  'rule' Print_expr(infix_occ(P,L,I,Q,R)):
         I'Ident -> Id
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id1,Ids)
	   Ids_to_object(P, list(Id1,Ids) -> Obj)
	   where(qualification(Obj) -> Q1)
	 ||
	   where(Q -> Q1)
	 |)
         (|
           eq(Q1, nil)
	   where(Id -> op_op(O))
	   Operator_precedence(O -> N)
	   (|
	     Lower_expr_precedence(L, N)
	     where(L -> L1)
	   ||
	     where(VALUE_EXPR'bracket(P,L) -> L1)
	   |)
           Print_expr(L1)
           Putmsg(" ")
           Print_id_or_op(Id)
           Putmsg(" ")
	   (|
	     Lower_expr_precedence(R, N)
	     where(R -> R1)
	   ||
	     where(VALUE_EXPR'bracket(P,R) -> R1)
	   |)
           Print_expr(R1)
         ||
           Putmsg("(")
           Print_opt_qualification(Q1)
           Print_id_or_op(Id)
           Putmsg(")(")
           Print_expr(L)
           Putmsg(",")
           Print_expr(R)
           Putmsg(")")
         |)      

  'rule' Print_expr(prefix_occ(P,I,Q,V)):
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id,Ids)
	   Print_qualifier(list(Id,Ids))
	 ||
           Print_opt_qualification(Q)
	 |)
         I'Ident -> Id
         Print_id_or_op(Id)
         Putmsg(" ")
	 (|
	   Lower_expr_precedence(V, 3)
	   where(V -> V1)
	 ||
	   where(VALUE_EXPR'bracket(P,V) -> V1)
	 |)
         Print_expr(V1)   

  'rule' Print_expr(input_occ(P, I, Q)):
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id,Ids)
	   Print_qualifier(list(Id,Ids))
	 ||
           Print_opt_qualification(Q)
	 |)
         I'Ident -> Id
         Print_id(Id)
         Putmsg("?")

  'rule' Print_expr(output_occ(P, I, Q, V)):
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id,Ids)
	   Print_qualifier(list(Id,Ids))
	 ||
           Print_opt_qualification(Q)
	 |)
         I'Ident -> Id
         Print_id(Id)
         Putmsg("!")
	 (|
	   Lower_expr_precedence(V, 11)
	   where(V -> V1)
	 ||
	   where(VALUE_EXPR'bracket(P,V) -> V1)
	 |)
         Print_expr(V1)

  'rule' Print_expr(chan_occ(P, I, Q)):
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id,Ids)
	   Print_qualifier(list(Id,Ids))
	 ||
           Print_opt_qualification(Q)
	 |)
         I'Ident -> Id
         Print_id(Id)
         

  'rule' Print_expr(env_local(P, DS, _, E)):
         Print_expr(local_expr(P, DS, E))

  'rule' Print_expr(no_val):
         Putmsg("??")

  'rule' Print_expr(cc_expr(P, STR, _, E)):
         Putmsg("-- ")
         Putmsg(STR)
         Putnl()
         Print_expr(E)

  'rule' Print_expr(array_access(P, N, I)):
         Print_expr(N)
         Putmsg("[")
         Print_expr(I)
         Putmsg("]")

  'rule' Print_expr(array_assignment(P, N, I, V)):
         Print_name(N)
         Print_array_accesses(I)
         /*Putmsg("[")
         Print_expr(I)
         Putmsg("]")*/
         Putmsg(" = ")
         Print_expr(V)

  'rule' Print_expr(array_expr(P, S, V)):
         Putmsg("[|[")
         Print_typing(S)
         Putmsg("]")
         Print_expr(V)
         Putmsg("|]")

  'rule' Print_expr(local_val_occ(P,I,Q)):
         Print_expr(val_occ(P,I,Q))       
         
'action' Print_array_accesses(VALUE_EXPRS)
  'rule' Print_array_accesses(nil)

  'rule' Print_array_accesses(list(H,T))
         Putmsg("[")
         Print_expr(H)
         Putmsg("]")         

'action' Print_value_literal(VALUE_LITERAL)

  'rule' Print_value_literal(unit):
         Putmsg("()")

  'rule' Print_value_literal(bool_true):
         Putmsg("true")

  'rule' Print_value_literal(bool_false):
         Putmsg("false")

  'rule' Print_value_literal(delta):
         Putmsg("Delta")

  'rule' Print_value_literal(int(X)):
         id_to_string(X -> S)
         Putmsg(S)

  'rule' Print_value_literal(real(X)):
         id_to_string(X -> S)
         Putmsg(S)

  'rule' Print_value_literal(text(S)):
         Putstr(S)

  'rule' Print_value_literal(char(C)):
         Putchar(C)

'action' Print_set_limitation(SET_LIMITATION)

  'rule' Print_set_limitation(set_limit(P, TS, R)):
         Print_typings(TS)
         Print_restriction(R)

'action' Print_restriction(RESTRICTION)

  'rule' Print_restriction(restriction(P, E)):
         Putmsg(" :- ")
         Print_expr(E)

  'rule' Print_restriction(nil):

'action' Print_list_limitation(LIST_LIMITATION)

  'rule' Print_list_limitation(list_limit(P, B, E, R)):
         Print_binding(B)
         Putmsg(" in ")
         Print_expr(E)
         Print_restriction(R)
  
'action' Print_value_expr_pairs(VALUE_EXPR_PAIRS)

  'rule' Print_value_expr_pairs(list(E, nil)):
         Print_value_expr_pair(E)

  'rule' Print_value_expr_pairs(list(E, L)):
         Print_value_expr_pair(E)
         Putmsg(",")
         Print_value_expr_pairs(L)

  'rule' Print_value_expr_pairs(nil):


'action' Print_value_expr_pair(VALUE_EXPR_PAIR)

  'rule' Print_value_expr_pair(pair(L, R)):
         Print_expr(L)
         Putmsg(" +> ")
         Print_expr(R)

'action' Print_lambda_parameter(LAMBDA_PARAMETER)

  'rule' Print_lambda_parameter(l_typing(P, TS)):
         Putmsg("(")
         Print_typings(TS)
         Putmsg(")")

  'rule' Print_lambda_parameter(s_typing(P, T)):
         Print_typing(T)
         
'action' Print_actual_function_parameters(ACTUAL_FUNCTION_PARAMETERS)

  'rule' Print_actual_function_parameters(list(H, T)):
         Putmsg("(")
         Print_actual_function_parameter(H)
         Putmsg(")")
         Print_actual_function_parameters(T)

  'rule' Print_actual_function_parameters(nil):

'action' Print_actual_function_parameter(ACTUAL_FUNCTION_PARAMETER)

  'rule' Print_actual_function_parameter(fun_arg(P, ES)):
         Print_exprs(ES)

'action' Print_quantifier(QUANTIFIER)

  'rule' Print_quantifier(all):
         Putmsg("all ")

  'rule' Print_quantifier(exists):
         Putmsg("exists ")

  'rule' Print_quantifier(exists1):
         Putmsg("exists! ")

'action' Print_pre_condition(PRE_CONDITION)

  'rule' Print_pre_condition(pre_cond(P, E)):
         Putmsg(" pre ")
	 (|
	   Lower_expr_precedence(E, 14)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
         Print_expr(E1)

  'rule' Print_pre_condition(nil):

'action' Print_opt_post_condition(OPT_POST_CONDITION)

  'rule' Print_opt_post_condition(post(P)):
	 Print_post_condition(P)

  'rule' Print_opt_post_condition(nil):

'action' Print_post_condition(POST_CONDITION)

  'rule' Print_post_condition(post_cond(P, R, E)):
         Print_result_naming(R)
         Putmsg(" post ")
         Print_expr(E)

'action' Print_result_naming(RESULT_NAMING)

  'rule' Print_result_naming(result(P, B)):
         Putmsg(" as ")
         Print_binding(B)

  'rule' Print_result_naming(nil):

'action' Print_let_defs(LET_DEFS)

  'rule' Print_let_defs(list(H, nil)):
         Print_let_def(H)

  'rule' Print_let_defs(list(H, T)):
         Print_let_def(H)
         Putmsg(", ")
         Print_let_defs(T)

'action' Print_let_def(LET_DEF)

  'rule' Print_let_def(explicit(P, B, E)):
         Print_let_binding(B)
         Putmsg(" = ")
         Print_expr(E)

  'rule' Print_let_def(implicit(P, T, R)):
         Print_typing(T)
         Print_restriction(R)


'action' Print_let_binding(LET_BINDING)

  'rule' Print_let_binding(binding(P, B)):
         Print_binding(B)

  'rule' Print_let_binding(pattern(P, PATT)):
         Print_pattern(PATT)

'action' Print_elsif_branches(ELSIF_BRANCHES)

  'rule' Print_elsif_branches(list(H, T)):
         Print_elsif_branch(H)
         Print_elsif_branches(T)

  'rule' Print_elsif_branches(nil):

'action' Print_elsif_branch(ELSIF_BRANCH)

  'rule' Print_elsif_branch(elsif(P, E, THEN, _)):
         Putmsg(" elsif ")
         Print_expr(E)
         Putmsg(" then ")
         Print_expr(THEN)

'action' Print_else_branch(ELSE_BRANCH)

  'rule' Print_else_branch(else(P, E)):
         Putmsg(" else ")
         Print_expr(E)

'action' Print_case_branches(CASE_BRANCHES)

  'rule' Print_case_branches(list(H, nil)):
         Print_case_branch(H)

  'rule' Print_case_branches(list(H, T)):
         Print_case_branch(H)
         Putmsg(", ")
         Print_case_branches(T)


'action' Print_case_branch(CASE_BRANCH)

  'rule' Print_case_branch(case(P, PATT, E, _)):
         Print_pattern(PATT)
         Putmsg(" -> ")
         Print_expr(E)

--------------------------------------------------------------
-- Typings and bindings
--------------------------------------------------------------

'action' Print_typings(TYPINGS)

  'rule' Print_typings(list(T, nil))
         Print_typing(T)

  'rule' Print_typings(list(T, TS))
         Print_typing(T)
         Putmsg(", ")
         Print_typings(TS)

  'rule' Print_typings(nil):
         
'action' Print_typing(TYPING)

  'rule' Print_typing(single(P,B,T)):
         Print_binding(B)
         Putmsg(" : ")
         Print_type(T)

  'rule' Print_typing(multiple(P,BS,T)):
         Print_bindings(BS)
         Putmsg(" : ")
         Print_type(T)

'action' Print_bindings(BINDINGS)

  'rule' Print_bindings(nil):

  'rule' Print_bindings(list(H,nil)):
         Print_binding(H)

  'rule' Print_bindings(list(H,T)):
         Print_binding(H)
         Putmsg(", ")
         Print_bindings(T)

'action' Print_binding(BINDING)

  'rule' Print_binding(single(P,Id_or_op)):
         Print_id_or_op(Id_or_op)

  'rule' Print_binding(product(P,BS)):
         Putmsg("(")
         Print_bindings(BS)
         Putmsg(")")


-----------------------------------------------------------------------------
-- Patterns, names and operators
-----------------------------------------------------------------------------

'action' Print_pattern(PATTERN)

  'rule' Print_pattern(literal_pattern(P, L)):
         Print_value_literal(L)

  'rule' Print_pattern(name_pattern(P,N)):
         Print_name(N)

  'rule' Print_pattern(record_pattern(P, N, ARGS)):
         Print_name(N)
         Putmsg("(")
         Print_patterns(ARGS)
         Putmsg(")")

  'rule' Print_pattern(id_pattern(P, Id)):
         Print_id_or_op(Id)

  'rule' Print_pattern(wildcard_pattern(P)):
         Putmsg("_")

  'rule' Print_pattern(product_pattern(P, PATTS)):
         Putmsg("(")
         Print_patterns(PATTS)
         Putmsg(")")

  'rule' Print_pattern(enum_list(P, PATTS)):
         Putmsg("<.")
         Print_patterns(PATTS)
         Putmsg(".>")

  'rule' Print_pattern(conc_list(P, L, R)):
         Putmsg("<.")
         Print_patterns(L)
         Putmsg(".> ^ ")
         Print_pattern(R)

  'rule' Print_pattern(name_occ_pattern(P, I, Q)):
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id,Ids)
	   Print_qualifier(list(Id,Ids))
	 ||
           Print_opt_qualification(Q)
	 |)
         I'Ident -> Id
         Print_id_or_op(Id)

  'rule' Print_pattern(record_occ_pattern(P, I, Q, ARGS)):
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id,Ids)
	   Print_qualifier(list(Id,Ids))
	 ||
           Print_opt_qualification(Q)
	 |)
         I'Ident -> Id
         Print_id_or_op(Id)
         Putmsg("(")
         Print_patterns(ARGS)
         Putmsg(")")

'action' Print_patterns(PATTERNS)

  'rule' Print_patterns(list(H, nil)):
         Print_inner_pattern(H)

  'rule' Print_patterns(list(H, T)):
         Print_inner_pattern(H)
         Putmsg(",")
         Print_patterns(T)

  'rule' Print_patterns(nil):

'action' Print_inner_pattern(PATTERN)

  'rule' Print_inner_pattern(literal_pattern(P, L)):
         Print_value_literal(L)

  'rule' Print_inner_pattern(name_pattern(P,N)):
         Putmsg("=")
         Print_name(N)

  'rule' Print_inner_pattern(record_pattern(P, N, ARGS)):
         Print_name(N)
         Putmsg("(")
         Print_patterns(ARGS)
         Putmsg(")")

  'rule' Print_inner_pattern(id_pattern(P, Id)):
         Print_id_or_op(Id)

  'rule' Print_inner_pattern(wildcard_pattern(P)):
         Putmsg("_")

  'rule' Print_inner_pattern(product_pattern(P, PATTS)):
         Putmsg("(")
         Print_patterns(PATTS)
         Putmsg(")")

  'rule' Print_inner_pattern(enum_list(P, PATTS)):
         Putmsg("(")
         Print_patterns(PATTS)
         Putmsg(")")

  'rule' Print_inner_pattern(conc_list(P, L, R)):
         Print_patterns(L)
         Putmsg(" ^ ")
         Print_inner_pattern(R)

  'rule' Print_inner_pattern(name_occ_pattern(P,I,Q)):
         Putmsg("=")
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id,Ids)
	   Print_qualifier(list(Id,Ids))
	 ||
           Print_opt_qualification(Q)
	 |)
         I'Ident -> Id
         Print_id_or_op(Id)

  'rule' Print_inner_pattern(record_occ_pattern(P, I, Q, ARGS)):
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id,Ids)
	   Print_qualifier(list(Id,Ids))
	 ||
           Print_opt_qualification(Q)
	 |)
         I'Ident -> Id
         Print_id_or_op(Id)
         Putmsg("(")
         Print_patterns(ARGS)
         Putmsg(")")

'action' Print_names(NAMES)

  'rule' Print_names(list(N,nil)):
         Print_name(N)

  'rule' Print_names(list(N,NS)):
         Print_name(N)
         Putmsg(", ")
         Print_names(NS)

  'rule' Print_names(nil):

'action' Print_name(NAME)

  'rule' Print_name(name(P,id_op(Id))):
         Print_id(Id)

  'rule' Print_name(name(P,op_op(Op))):
         Putmsg("(")
         Print_op(Op)
         Putmsg(")")

  'rule' Print_name(qual_name(P, Obj,N)):
         Print_object(Obj)
         Putmsg(".")
         (|
           where(N -> op_op(Op))
           Putmsg("(")
           Print_op(Op)
           Putmsg(")")
         ||
           where(N -> id_op(Id))
           Print_id(Id)
         |)

'action' Print_opt_qualification(OPT_QUALIFICATION)

  'rule' Print_opt_qualification(qualification(OBJ)):
	 (|
	   Is_dummy(OBJ)
	 ||
           Print_object(OBJ)
	   Putmsg(".")
	 |)

  'rule' Print_opt_qualification(nil):

'condition' Is_dummy(OBJECT_EXPR)

  'rule' Is_dummy(obj_occ(_,I)):
	 I'Ident -> Id
	 (|
	   Dummy_id1 -> Dummy_id1
	   eq(Id, Dummy_id1)
	 ||
	   Dummy_id2 -> Dummy_id2
	   eq(Id, Dummy_id2)
	 |)
	 
'action' Print_id_or_op(ID_OR_OP)

  'rule' Print_id_or_op(id_op(Id)):
         Print_id(Id)

  'rule' Print_id_or_op(op_op(Op)):
         Print_op(Op)

'action' Print_ids(IDENTS)

  'rule' Print_ids(list(Id,nil)):
         Print_id(Id)

  'rule' Print_ids(list(Id,Ids)):
         Print_id(Id)
         Putmsg(", ")
         Print_ids(Ids)

  'rule' Print_ids(nil):

'action' Print_id(IDENT)

  'rule' Print_id(Id)
         id_to_string(Id -> X)
         Putmsg(X)

-- Dummy_ids can only occur at start of qualifier, so only check there
'action' Print_qualifier(Object_ids)

  'rule' Print_qualifier(nil):

  'rule' Print_qualifier(list(I, Is)):
         I'Ident -> Id
         [|
           Dummy_id1 -> Dummy_id1
           ne(Id, Dummy_id1)
           Dummy_id2 -> Dummy_id2
           ne(Id, Dummy_id2)
           Print_id(Id)
           Putmsg(".")
         |]
         Print_qualifier1(Is)

'action' Print_qualifier1(Object_ids)

  'rule' Print_qualifier1(nil):
         
  'rule' Print_qualifier1(list(I, Is)):
         I'Ident -> Id
         Print_id(Id)
         Putmsg(".")
         Print_qualifier(Is)

'action' Print_op(OP)

  'rule' Print_op(Op):
         Op_to_print_string(Op -> Str)
         Putmsg(Str)

'action' Op_to_print_string(OP -> STRING)

  'rule' Op_to_print_string(eq -> "=")
  'rule' Op_to_print_string(neq -> "~=")
  'rule' Op_to_print_string(eqeq -> "==")
  'rule' Op_to_print_string(gt -> ">")
  'rule' Op_to_print_string(lt -> "<")
  'rule' Op_to_print_string(ge -> ">=")
  'rule' Op_to_print_string(le -> "<=")
  'rule' Op_to_print_string(supset -> ">>")
  'rule' Op_to_print_string(subset -> "<<")
  'rule' Op_to_print_string(supseteq -> ">>=")
  'rule' Op_to_print_string(subseteq -> "<<=")
  'rule' Op_to_print_string(isin -> "isin")
  'rule' Op_to_print_string(notisin -> "~isin")
  'rule' Op_to_print_string(rem -> "\\")
  'rule' Op_to_print_string(caret -> "^")
  'rule' Op_to_print_string(union -> "union")
  'rule' Op_to_print_string(override -> "!!")
  'rule' Op_to_print_string(mult -> "*")
  'rule' Op_to_print_string(div -> "/")
  'rule' Op_to_print_string(hash -> "#")
  'rule' Op_to_print_string(inter -> "inter")
  'rule' Op_to_print_string(exp -> "**")
  'rule' Op_to_print_string(abs -> "abs")
  'rule' Op_to_print_string(int -> "int")
  'rule' Op_to_print_string(real -> "real")
  'rule' Op_to_print_string(card -> "card")
  'rule' Op_to_print_string(len -> "len")
  'rule' Op_to_print_string(inds -> "inds")
  'rule' Op_to_print_string(elems -> "elems")
  'rule' Op_to_print_string(hd -> "hd")
  'rule' Op_to_print_string(tl -> "tl")
  'rule' Op_to_print_string(dom -> "dom")
  'rule' Op_to_print_string(rng -> "rng")
  'rule' Op_to_print_string(wait -> "wait")
  'rule' Op_to_print_string(plus -> "+")
  'rule' Op_to_print_string(minus -> "-")

'action' Print_combinator(COMBINATOR)

  'rule' Print_combinator(int_choice):          Putmsg("|^|")
  'rule' Print_combinator(ext_choice):          Putmsg("|=|")
  'rule' Print_combinator(parallel):            Putmsg("||")
  'rule' Print_combinator(interlock):           Putmsg("++")
  'rule' Print_combinator(sequence):            Putmsg(";")

'action' Print_connective(CONNECTIVE)

  'rule' Print_connective(implies):             Putmsg("=>")
  'rule' Print_connective(or):                  Putmsg("\\/")
  'rule' Print_connective(and):                 Putmsg("/\\")
  'rule' Print_connective(not):                 Putmsg("~")


-------------------------------
-- precedences
-- we need to use these in pretty printing because
-- expressions and types can be
-- generated internally that need bracketting when printed
-------------------------------
'condition' Lower_expr_precedence(VALUE_EXPR, INT)

  'rule' Lower_expr_precedence(T, I):
         Expr_precedence(T -> P)
         lt(P,I)

'action' Expr_precedence(VALUE_EXPR -> INT)

  'rule' Expr_precedence(literal_expr(_,_) -> 0):

  'rule' Expr_precedence(named_val(_,_) -> 0):

  'rule' Expr_precedence(pre_name(_,_) -> 0):

  'rule' Expr_precedence(chaos(_) -> 0):

  'rule' Expr_precedence(skip(_) -> 0):

  'rule' Expr_precedence(stop(_) -> 0):

  'rule' Expr_precedence(swap(_) -> 0):

  'rule' Expr_precedence(product(_,_) -> 0):

  'rule' Expr_precedence(ranged_set(_,_,_) -> 0):

  'rule' Expr_precedence(enum_set(_,_) -> 0):

  'rule' Expr_precedence(comp_set(_,_,_) -> 0):

  'rule' Expr_precedence(ranged_list(_,_,_) -> 0):

  'rule' Expr_precedence(enum_list(_,_) -> 0):

  'rule' Expr_precedence(comp_list(_,_,_) -> 0):

  'rule' Expr_precedence(enum_map(_,_) -> 0):

  'rule' Expr_precedence(comp_map(_,_,_) -> 0):

  'rule' Expr_precedence(function(_,_,_) -> 15):

  'rule' Expr_precedence(application(_,_,_) -> 1):

  'rule' Expr_precedence(quantified(_,_,_,_) -> 15):

  'rule' Expr_precedence(equivalence(_,_,_,_) -> 14):

  'rule' Expr_precedence(post(_,_,_,_) -> 14):

  'rule' Expr_precedence(disamb(_,_,_) -> 3):

  'rule' Expr_precedence(bracket(_,_) -> 0):

  'rule' Expr_precedence(ax_infix(_,_,C,_,_) -> P):
         Connective_precedence(C -> P)

  'rule' Expr_precedence(val_infix(_,_,O,_) -> P):
         Operator_precedence(O -> P)

  'rule' Expr_precedence(stmt_infix(_,_,sequence,_) -> 12):

  'rule' Expr_precedence(stmt_infix(_,_,_,_) -> 13):

  'rule' Expr_precedence(always(_,_) -> 15):

  'rule' Expr_precedence(ax_prefix -> 2):

  'rule' Expr_precedence(val_prefix -> 2):

  'rule' Expr_precedence(comprehended(_,_,_,_) -> 0):

  'rule' Expr_precedence(initialise(_,_) -> 0):

  'rule' Expr_precedence(assignment(_,_,_) -> 11):

  'rule' Expr_precedence(input(_,_) -> 0):

  'rule' Expr_precedence(output(_,_,_) -> 11):

  'rule' Expr_precedence(local_expr(_,_,_) -> 0):

  'rule' Expr_precedence(let_expr(_,_,_) -> 0):

  'rule' Expr_precedence(if_expr(_,_,_,_,_,_) -> 0):

  'rule' Expr_precedence(case_expr(_,_,_,_) -> 0):

  'rule' Expr_precedence(while_expr(_,_,_) -> 0):

  'rule' Expr_precedence(until_expr(_,_,_) -> 0):

  'rule' Expr_precedence(for_expr(_,_,_) -> 0):

  'rule' Expr_precedence(class_scope_expr(_,_,_) -> 15):

  'rule' Expr_precedence(env_class_scope(_,_,_,_) -> 15):

  'rule' Expr_precedence(implementation_relation(_,_,_) -> 15):

  'rule' Expr_precedence(implementation_expr(_,_,_) -> 15):

  'rule' Expr_precedence(val_occ(_,_,_) -> 0):

  'rule' Expr_precedence(var_occ(_,_,_) -> 0):

  'rule' Expr_precedence(pre_occ(_,_,_) -> 0):

  'rule' Expr_precedence(infix_occ(_,_,Id,_,_) -> P):
         Id'Ident -> op_op(O)
         Operator_precedence(O -> P)

  'rule' Expr_precedence(prefix_occ(_,_,_,_) -> 2):

  'rule' Expr_precedence(ass_occ(_,_,_,_) -> 11):

  'rule' Expr_precedence(input_occ(_,_,_) -> 0):

  'rule' Expr_precedence(output_occ(_,_,_,_) -> 11):

  'rule' Expr_precedence(chan_occ(_,_,_) -> 0):

  'rule' Expr_precedence(env_local(_,_,_,_) -> 0):

  'rule' Expr_precedence(no_val -> 0):

  'rule' Expr_precedence(cc_expr(_,_,_,E) -> N):
         Expr_precedence(E -> N)

  'rule' Expr_precedence(array_access(_,_,_) -> 0)


'action' Connective_precedence(CONNECTIVE -> INT)

  'rule' Connective_precedence(implies -> 10):

  'rule' Connective_precedence(or -> 9):

  'rule' Connective_precedence(and -> 8):

'action' Operator_precedence(OP -> INT)

  'rule' Operator_precedence(eq -> 7):

  'rule' Operator_precedence(neq -> 7):

  'rule' Operator_precedence(eqeq -> 7):

  'rule' Operator_precedence(gt -> 7):

  'rule' Operator_precedence(lt -> 7):

  'rule' Operator_precedence(ge -> 7):

  'rule' Operator_precedence(le -> 7):

  'rule' Operator_precedence(supset -> 7):

  'rule' Operator_precedence(subset -> 7):

  'rule' Operator_precedence(supseteq -> 7):

  'rule' Operator_precedence(subseteq -> 7):

  'rule' Operator_precedence(isin -> 7):

  'rule' Operator_precedence(notisin -> 7):

  'rule' Operator_precedence(rem -> 6):

  'rule' Operator_precedence(caret -> 6):

  'rule' Operator_precedence(union -> 6):

  'rule' Operator_precedence(override -> 6):

  'rule' Operator_precedence(mult -> 5):

  'rule' Operator_precedence(div -> 5):

  'rule' Operator_precedence(hash -> 5):

  'rule' Operator_precedence(inter -> 5):

  'rule' Operator_precedence(exp -> 4):

  'rule' Operator_precedence(plus -> 6):

  'rule' Operator_precedence(minus -> 6):

'condition' Lower_type_precedence(TYPE_EXPR, INT)

  'rule' Lower_type_precedence(T, I):
         Type_precedence(T -> P)
         lt(P,I)

'action' Type_precedence(TYPE_EXPR -> INT)

  'rule' Type_precedence(fun(_,_,_) -> 3)

  'rule' Type_precedence(infin_map(_,_) -> 3):

  'rule' Type_precedence(fin_map(_,_) -> 3):

  'rule' Type_precedence(product(_) -> 2):

  'rule' Type_precedence(infin_set(_) -> 1):

  'rule' Type_precedence(fin_set(_) -> 1):

  'rule' Type_precedence(infin_list(_) -> 1):

  'rule' Type_precedence(fin_list(_) -> 1):

  'rule' Type_precedence(subtype(_,_) -> 1):

  'rule' Type_precedence(_ -> 0):

----------------------------------------------------
-- Dependency graph
----------------------------------------------------

'action' Make_dependency_graph(LIB_MODULE, LIB_MODULES)

  'rule' Make_dependency_graph(_, nil):
         ErrorUsage("There is only one module: no graph to draw")

  'rule' Make_dependency_graph(M, G):
         Check_circular(G, nil, nil)
         Get_module_id_kind(M -> Id, K)
         Add_module(Id, K, nil -> Dep1, Found)
         (|
           ne(Found, found)
           Add_deps(Id, M, G, Dep1 -> Dep2)
         ||
           where(Dep1 -> Dep2)
         |)
         Prune_dep(Dep2, Dep2 -> Dep3)
         Output_dep(Id, Dep3 -> S)
-- debug
--       Print_dep(Dep3)
         Putmsg("Graph for displaying with vcg is in file ")
         Putmsg(S)
         Putnl()

-- same algorithm as used in Make_globals1
'action' Check_circular(todo:LIB_MODULES, waiting:LIB_MODULES, found:FOUND)

  'rule' Check_circular(list(Mod, M), W, F):
         (|
           where(Mod -> scheme(_,C,_,sdef(_, Id, _, _)))
         ||
           where(Mod -> object(_,C,_,odef(_, Id, _, _)))
         ||
           where(Mod -> theory(_,C,_,theory_def(_, Id, _)))
         ||
           where(Mod -> devt_relation(_,C,_,devt_relation_def(_, Id, _, _, _)))
         |)
         (|
           eq(C, nil)
           Remove_context_id(Id, M -> M1)
           Remove_context_id(Id, W -> W1)
           Check_circular(M1, W1, found)
         ||
           Check_circular(M, list(Mod, W), F)
         |)

  'rule' Check_circular(nil, nil, F):

  'rule' Check_circular(nil, W, F):
         (|
           eq(F, found)
           Check_circular(W, nil, nil)    
         ||
           (|
             where(W -> list(scheme(_,_,_,sdef(_,Id,_,_)),_))
           ||
             where(W -> list(object(_,_,_,odef(_,Id,_,_)),_))
           ||
             where(W -> list(theory(_,_,_,theory_def(_,Id,_)),_))
           ||
             where(W -> list(devt_relation(_,_,_,devt_relation_def(_,Id,_,_,_)),_))
           |)
           Putmsg("Dependencies for module ")
           Print_id(Id)
           ErrorUsage(" are circular")
         |)

'action' Remove_context_id(IDENT, LIB_MODULES -> LIB_MODULES)

  'rule' Remove_context_id(Id, list(scheme(P,C,CO,D),M) -> list(scheme(P,C1,CO,D),M1)):
         Remove_id(Id, C -> C1)
         Remove_context_id(Id, M -> M1)
         
  'rule' Remove_context_id(Id, list(object(P,C,CO,D),M) -> list(object(P,C1,CO,D),M1)):
         Remove_id(Id, C -> C1)
         Remove_context_id(Id, M -> M1)
         
  'rule' Remove_context_id(Id, list(theory(P,C,CO,D),M) -> list(theory(P,C1,CO,D),M1)):
         Remove_id(Id, C -> C1)
         Remove_context_id(Id, M -> M1)
         
  'rule' Remove_context_id(Id, list(devt_relation(P,C,CO,D),M) -> list(devt_relation(P,C1,CO,D),M1)):
         Remove_id(Id, C -> C1)
         Remove_context_id(Id, M -> M1)
         
  'rule' Remove_context_id(Id, nil -> nil):

'action' Remove_id(IDENT, FILE_NAMES -> FILE_NAMES)
         
  'rule' Remove_id(Id, list(F,FS1) -> FS2):
         (|
           BaseName(F -> Fid)
           EqualFileId(Id, Fid)
           Remove_id(Id, FS1 -> FS2)
         ||
           Remove_id(Id, FS1 -> FS3)
           where(FILE_NAMES'list(F,FS3) -> FS2)
         |)  

  'rule' Remove_id(Id, nil -> nil):

'action' Add_module(IDENT, MODULE_KIND, DEPENDENCY -> DEPENDENCY, FOUND)

  'rule' Add_module(Id, K, dependency(Id1, K1, Ids, Dep) -> Dep1, Found):
         (|
           EqualFileId(Id, Id1)
           where(dependency(Id1, K1, Ids, Dep) -> Dep1)
           where(found -> Found)
         ||
           Add_module(Id, K, Dep -> Dep2, Found1)
           where(dependency(Id1, K1, Ids, Dep2) -> Dep1)
           where(Found1 -> Found)
         |)

  'rule' Add_module(Id, K, nil -> dependency(Id, K, nil, nil), nil):

'action' Add_deps(IDENT, LIB_MODULE, LIB_MODULES, DEPENDENCY -> DEPENDENCY)

  'rule' Add_deps(Id, scheme(_, C, _, _), G, Dep -> Dep1):
         Add_context_deps(Id, C, G, Dep -> Dep1)

  'rule' Add_deps(Id, object(_, C, _, _), G, Dep -> Dep1):
         Add_context_deps(Id, C, G, Dep -> Dep1)

  'rule' Add_deps(Id, theory(_, C, _, _), G, Dep -> Dep1):
         Add_context_deps(Id, C, G, Dep -> Dep1)

  'rule' Add_deps(Id, devt_relation(_, C, _, _), G, Dep -> Dep1):
         Add_context_deps(Id, C, G, Dep -> Dep1)

'action' Add_context_deps(IDENT, FILE_NAMES, LIB_MODULES, DEPENDENCY -> DEPENDENCY)

  'rule' Add_context_deps(Id, list(F, FS), G, Dep -> Dep1):
         BaseName(F -> Id1)
         (|
           Find_module(Id1, G -> lib_mod(M))
           Get_module_id_kind(M -> _, K)
           Add_module(Id1, K, Dep -> Dep2, Found)
           (|
             ne(Found, found)
             Add_deps(Id1, M, G, Dep2 -> Dep3)
           ||
             where(Dep2 -> Dep3)
           |)
         ||
           where(Dep -> Dep3)
         |)
         Add_dep(Id, Id1, Dep3 -> Dep4)
         Add_context_deps(Id, FS, G, Dep4 -> Dep1)
         
  'rule' Add_context_deps(_, nil, _, Dep -> Dep):

'action' Add_dep(IDENT, IDENT, DEPENDENCY -> DEPENDENCY)

  'rule' Add_dep(Id, Id1, dependency(Id2, K, Ids, Dep) -> Dep1):
         (|
           EqualFileId(Id, Id2)
           Add_id(Id1, Ids -> Ids1)
           where(dependency(Id2, K, Ids1, Dep) -> Dep1)
         ||
           Add_dep(Id, Id1, Dep -> Dep2)
           where(dependency(Id2, K, Ids, Dep2) -> Dep1)
         |)

-- allow for missing modules
  'rule' Add_dep(Id, Id1, nil -> nil)

'action' Add_id(IDENT, IDENTS -> IDENTS)

  'rule' Add_id(Id, list(Id1, Ids) -> Ids1):
         (|
           EqualFileId(Id, Id1)
           where(IDENTS'list(Id1, Ids) -> Ids1)
         ||
           Add_id(Id, Ids -> Ids2)
           where(IDENTS'list(Id1, Ids2) -> Ids1)
         |)

  'rule' Add_id(Id, nil -> list(Id, nil)):

-- Removes link when there is a longer path.
-- Result should have same transitive closure as original
-- but with minimal edges.
'action' Prune_dep(DEPENDENCY, DEPENDENCY -> DEPENDENCY)

  'rule' Prune_dep(dependency(Id, K, Ids, Dep), Dep1 -> Dep3):
         Prune_deps(nil, Ids, Dep1 -> Ids1)
         Prune_dep(Dep, Dep1 -> Dep2)
         where(dependency(Id, K, Ids1, Dep2) -> Dep3)

  'rule' Prune_dep(nil, _ -> nil):

'action' Prune_deps(IDENTS, IDENTS, DEPENDENCY -> IDENTS)

  'rule' Prune_deps(Done, list(Id, Todo), Dep -> Ids):
         (|
           (| Reachable_id(Id, Done, Dep) || Reachable_id(Id, Todo, Dep) |)
           Prune_deps(Done, Todo, Dep -> Ids)
         ||
           Prune_deps(IDENTS'list(Id, Done), Todo, Dep -> Ids)
         |)

  'rule' Prune_deps(Done, nil, _ -> Done):

'condition' Reachable_id(IDENT, IDENTS, DEPENDENCY)

  'rule' Reachable_id(Id, list(Id1, Ids), Dep):
         (|
           EqualFileId(Id, Id1)
         ||
           Get_deps(Id1, Dep -> Ids1)
           Reachable_id(Id, Ids1, Dep)
         ||
           Reachable_id(Id, Ids, Dep)
         |)

'action' Get_deps(IDENT, DEPENDENCY -> IDENTS)

  'rule' Get_deps(Id, dependency(Id1, _, Ids, Dep) -> Ids1):
         (|
           EqualFileId(Id, Id1)
           where(Ids -> Ids1)
         ||
           Get_deps(Id, Dep -> Ids1)
         |)

  'rule' Get_deps(Id, nil -> nil):

'action' Output_dep(IDENT, DEPENDENCY -> STRING)

  'rule' Output_dep(Id, Dep -> S):
         OpenGraphFile(Id -> S)
         WriteGraphString("graph: {\ntitle: \"")
         WriteGraphId(Id)
         WriteGraphString("\"\nmanhatten_edges: yes\n")
         WriteGraphString("port_sharing: no\n")
         WriteGraphString("edge.thickness: 1\n")
         WriteGraphString("node.borderwidth: 1\n")
         WriteGraphString("node.color: red\n")
	 WriteGraphString("node.shape: box\n")
         Output_nodes(Dep)
         Output_edges(Dep)
         WriteGraphString("}\n")
         CloseGraphFile()

'action' Output_nodes(DEPENDENCY)

  'rule' Output_nodes(dependency(Id, K, _, Dep)):
         WriteGraphString("node: {title: \"")
         WriteGraphId(Id)
         WriteGraphString("\"")
         Output_color(K)
         WriteGraphString("}\n")
         Output_nodes(Dep)

  'rule' Output_nodes(nil):

'action' Output_edges(DEPENDENCY)

  'rule' Output_edges(dependency(Id, _, Ids, Dep)):
         Output_dep_edges(Id, Ids)
         Output_edges(Dep)

  'rule' Output_edges(nil):

'action' Output_dep_edges(IDENT, IDENTS)

  'rule' Output_dep_edges(Id, list(Id1, Ids)):
         WriteGraphString("edge: {sourcename: \"")
         WriteGraphId(Id)
         WriteGraphString("\" targetname: \"")
         WriteGraphId(Id1)
         WriteGraphString("\"}\n")
         Output_dep_edges(Id, Ids)
         
  'rule' Output_dep_edges(_, nil):

'action' Output_color(MODULE_KIND)

  'rule' Output_color(scheme):
	 -- defaults red box set at start
         WriteGraphString("")

  'rule' Output_color(object):
         WriteGraphString(" color: lightblue shape: box")

  'rule' Output_color(theory):
         WriteGraphString(" color: yellow shape: rhomb")

  'rule' Output_color(devt_relation):
         WriteGraphString(" color: cyan shape: triangle")

----------------------------------------------------
-- Debug and error messages
----------------------------------------------------

'action' Print_type_env(TYPE_ENV)

  'rule' Print_type_env(TE)
         Putmsg("Type environment:")
         Putnl()
         Print_type_env1(TE)

'action' Print_type_env1(TYPE_ENV)

  'rule' Print_type_env1(type_env(I,E)):
         I'Ident -> Id
         Print_id(Id)
         Putmsg(" has type ")
         Type_of(I -> T)
         Print_type(T)
         Putnl()
print(I)
print(T)
         Print_type_env1(E)

  'rule' Print_type_env1(nil):


'action' Print_adapts(ADAPTS)

  'rule' Print_adapts(hide(Id,nil)):
         Putmsg(" hide ")
         Print_id_or_op(Id)

  'rule' Print_adapts(rename(Id1,Id2,nil)):
         Print_id_or_op(Id1)
         Putmsg(" for ")
         Print_id_or_op(Id2)

  'rule' Print_adapts(hide(Id,Ads)):
         Putmsg(" hide ")
         Print_id_or_op(Id)
         Putmsg(",")
         Print_adapts(Ads)

  'rule' Print_adapts(rename(Id1,Id2,Ads)):
         Print_id_or_op(Id1)
         Putmsg(" for ")
         Print_id_or_op(Id2)
         Putmsg(", ")
         Print_adapts(Ads)

  'rule' Print_adapts(nil):


'action' Print_module_env(MODULE_ENV)

  'rule' Print_module_env(object_env(I, ME)):
         I'Ident -> Id
         Putmsg("Object: ")
         Print_id(Id)
         Putnl()
         I'Env -> CE
         Get_env_types(CE -> TE)
         Print_type_env(TE)
         Putnl()
--       print(CE)
         Print_module_env(ME)

  'rule' Print_module_env(nil):

'action' Print_results(RESULTS)

  'rule' Print_results(list(R, nil)):
         Print_result(R)

  'rule' Print_results(list(R, RS)):
         Print_result(R)
         Putmsg(" or")
         Putnl()
         Print_results(RS)
         
  'rule' Print_results(nil):

'action' Print_result(RESULT)

  'rule' Print_result(result(T,RD,WR,IN,OUT)):
         [|
           ne(RD, nil)
           Putmsg("read ")
           Print_accesses(RD)
           Putmsg(" ")
         |]
         [|
           ne(WR, nil)
           Putmsg("write ")
           Print_accesses(WR)
           Putmsg(" ")
         |]
         [|
           ne(IN, nil)
           Putmsg("in ")
           Print_accesses(IN)
           Putmsg(" ")
         |]
         [|
           ne(OUT, nil)
           Putmsg("out ")
           Print_accesses(OUT)
           Putmsg(" ")
         |]
         Print_type(T)

'action' Print_accs(ACCS)

  'rule' Print_accs(accesses(A, nil)):
         Print_acc(A)

  'rule' Print_accs(accesses(A, AS)):
         Print_acc(A)
         Putmsg(", ")
         Print_accs(AS)

  'rule' Print_accs(nil):

'action' Print_acc(ACC)

  'rule' Print_acc(free):
         Putmsg("free")

  'rule' Print_acc(any):
         Putmsg("any")

  'rule' Print_acc(qualany(Obj)):
         Print_object(Obj)
         Putmsg(".any")
         
  'rule' Print_acc(variable(I, Q)):
         Print_opt_qualification(Q)
         I'Ident -> Id
         Print_id(Id)

  'rule' Print_acc(channel(I, Q)):
         Print_opt_qualification(Q)
         I'Ident -> Id
         Print_id(Id)

'action' Print_types(TYPE_EXPRS)

  'rule' Print_types(list(H,nil)):
         Print_type(H)

  'rule' Print_types(list(H,T)):
         Print_type(H)
         Putmsg(" or")
         Putnl()
         Print_types(T)

  'rule' Print_types(nil):

'action' Print_id_types(Value_ids)

  'rule' Print_id_types(list(I,nil)):
         I'Type -> T
         Print_type(T)

  'rule' Print_id_types(list(I,Ids)):
         I'Type -> T
         Print_type(T)
         Putmsg(" or")
         Putnl()
         Print_id_types(Ids)

  'rule' Print_id_types(nil):

'action' Print_product_results_as_list(RESULTS)

  'rule' Print_product_results_as_list(list(result(product(PR),_,_,_,_), nil)):
         Print_product_type_as_list(PR)

  'rule' Print_product_results_as_list(list(result(product(PR),_,_,_,_), TS)):
         Print_product_type_as_list(PR)
         Putmsg(" or")
         Putnl()
         Print_product_results_as_list(TS)

'action' Print_product_type_as_list(PRODUCT_TYPE)

  'rule' Print_product_type_as_list(list(T, nil)):
         Print_type(T)

  'rule' Print_product_type_as_list(list(T, PR)):
         Print_type(T)
         Putmsg(" and ")
         Print_product_type_as_list(PR)

'action' Print_value_envs(VALUE_ENVS)

  'rule' Print_value_envs(list(E, ES)):
         Putmsg("Value environment:")
         Putnl()
         Print_value_env(E)
         Print_value_envs(ES)

  'rule' Print_value_envs(nil):

'action' Print_value_env(Value_ids)

  'rule' Print_value_env(list(I,E)):
         I'Ident -> Id_or_op
         Print_id_or_op(Id_or_op)
         Putmsg(" has type ")
         I'Type -> T
         Print_type(T)
[|
I'Def -> expl_val(V, _)
Putmsg(" and value ")
Print_expr(V)
|]
         Putnl()
         Print_value_env(E)

  'rule' Print_value_env(nil):

'action' Print_coercions(COERCIONS)

  'rule' Print_coercions(coercions(C, CS)):
         Print_coercion(C)
         Putnl()
         Print_coercions(CS)

  'rule' Print_coercions(nil):

'action' Print_coercion(COERCION)

  'rule' Print_coercion(coercion(I,nil)):
         I'Qualifier -> Q
         Print_qualifier(Q)
         I'Ident -> Id
         Print_id(Id)

  'rule' Print_coercion(coercion(I,C)):
         I'Qualifier -> Q
         Print_qualifier(Q)
         I'Ident -> Id
         Print_id(Id)
         Putmsg(",")
         Print_coercion(C)

  'rule' Print_coercion(nil):

'action' Print_dep(DEPENDENCY)

  'rule' Print_dep(dependency(Id, K, Ids, Dep)):
         Print_id(Id)
         Putmsg("\t")
         Print_module_kind(K)
         Putmsg("\t{")
         Print_ids(Ids)
         Putmsg("}\n")
         Print_dep(Dep)
         
  'rule' Print_dep(nil):

'action' Print_module_kind(MODULE_KIND)

  'rule' Print_module_kind(scheme):
         Putmsg("scheme")

  'rule' Print_module_kind(object):
         Putmsg("object")

  'rule' Print_module_kind(theory):
         Putmsg("theory")

  'rule' Print_module_kind(devt_relation):
         Putmsg("devt_relation")

'action' Print_axiom_env(AXIOM_ENV)

  'rule' Print_axiom_env(axiom_env(I, AX)):
	 Putmsg("[")
	 [|
	   I'Ident -> ident(Id)
	   Print_id(Id)
	 |]
	 Putmsg("]")
	 [|
	   ne(AX, nil)
	   Putmsg(",")
	   Print_axiom_env(AX)
	 |]

  'rule' Print_axiom_env(nil):

'action' Print_test_case_env(TEST_CASE_ENV)

  'rule' Print_test_case_env(test_case_env(I, AX)):
	 Putmsg("[")
	 [|
	   I'Ident -> ident(Id)
	   Print_id(Id)
	 |]
	 Putmsg("]")
	 [|
	   ne(AX, nil)
	   Putmsg(",")
	   Print_test_case_env(AX)
	 |]

  'rule' Print_test_case_env(nil):

'action' Print_alphabet(FDR_ALPHA_EXPR)

  'rule' Print_alphabet(fdr_named_alpha(Id,_,A)):
  	 Print_alphabet(A)

  'rule' Print_alphabet(fdr_enum_alpha(ES))
  	 Putmsg("{|")
	 Print_enum_alphabets(ES)
	 Putmsg("|}")

  'rule' Print_alphabet(fdr_fun_alpha1(F,A)):
  	 Print_fdr_fun(F)
	 Putmsg("(")
	 Print_alphabet(A)
	 Putmsg(")")

  'rule' Print_alphabet(fdr_fun_alpha2(F,A1,A2)):
  	 Print_fdr_fun(F)
	 Putmsg("(")
	 Print_alphabet(A1)
	 Putmsg(", ")
	 Print_alphabet(A2)
	 Putmsg(")")

  'rule' Print_alphabet(fdr_comp_alpha(_,_,_)):
  	 Putmsg("{|...|...|}") -- TODO

  'rule' Print_alphabet(fdr_empty):
  	 Putmsg("{||}")


'action' Print_Extra_Guard(EXTRA_GUARD)
  'rule' Print_Extra_Guard(guard(Val,Pos))
         Print_expr(Val)

  'rule' Print_Extra_Guard(nil)


'action' Print_enum_alphabets(FDR_ENUM_ALPHA_EXPRS)

  'rule' Print_enum_alphabets(list(fdr_enum_alpha_expr(Id, _), AS)):
  	 Print_id(Id)
	 [|
	   ne(AS, nil)
	   Putmsg(",")
	 |]
	 Print_enum_alphabets(AS)

  'rule' Print_enum_alphabets(nil):

'action' Print_fdr_fun(FDR_FUN)

  'rule' Print_fdr_fun(fdr_length): Putmsg(" length")

  'rule' Print_fdr_fun(fdr_null): Putmsg(" null")

  'rule' Print_fdr_fun(fdr_head): Putmsg(" head")

  'rule' Print_fdr_fun(fdr_tail): Putmsg(" tail")

  'rule' Print_fdr_fun(fdr_concat): Putmsg(" concat")

  'rule' Print_fdr_fun(fdr_elem): Putmsg(" elem")

  'rule' Print_fdr_fun(fdr_union): Putmsg(" union")

  'rule' Print_fdr_fun(fdr_inter): Putmsg(" inter")

  'rule' Print_fdr_fun(fdr_diff): Putmsg(" diff")

  'rule' Print_fdr_fun(fdr_Union): Putmsg(" Union")

  'rule' Print_fdr_fun(fdr_Inter): Putmsg(" Inter")

  'rule' Print_fdr_fun(fdr_card): Putmsg(" card")

  'rule' Print_fdr_fun(fdr_empty): Putmsg(" empty")

  'rule' Print_fdr_fun(fdr_set): Putmsg(" set")

  'rule' Print_fdr_fun(fdr_Set): Putmsg(" Set")

  'rule' Print_fdr_fun(fdr_Seq): Putmsg(" Seq")

  'rule' Print_fdr_fun(fdr_member): Putmsg(" member")

  'rule' Print_fdr_fun(nil):
