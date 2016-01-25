-- This module defines the rsl -> RT-Tester(ASCII) translator

'module' rtt

'use' ast ext env

'export' gen_rtt_ascii



'action' gen_rtt_ascii(LIB_MODULE)

  'rule' gen_rtt_ascii(scheme(_, _, _, S)): 
          Module_name -> N
          string_to_id(N -> Id)
          OpenRTTFile(Id -> _) 
          gen_scheme(S)
          CloseOutputFile


'action' gen_scheme(SCHEME_DEF)

  'rule' gen_scheme(sdef(_, _, _, C)): 
          gen_class(C)


'action' gen_class(CLASS)

  'rule' gen_class(basic(Ds)): 
          check_enums_for_duplicates(Ds, nil)
          WriteFile("SYM_TABLE_DECL") 
          gen_sym_table_decls(Ds) 
          WriteFile("\nSYM_TABLE_DECL_END\n\nINIT_VAL") 
          gen_init_values(Ds) 
          WriteFile("\nINIT_VAL_END\n\nTRANS_REL") 
          gen_transition_relations(Ds) 
          WriteFile("\nTRANS_REL_END\n\nPROP_SPEC") 
          gen_property_specifications(Ds) 
          WriteFile("\nPROP_SPEC_END")
  
  'rule' gen_class(_):
          ErrorUsage("Error: only basic classes are accepted")


'action' gen_sym_table_decls(DECLS)

  'rule' gen_sym_table_decls(nil):

  'rule' gen_sym_table_decls(list(type_decl(_, TDs), Ds)): 
          gen_type_declarations(TDs) 
          gen_sym_table_decls(Ds)

  'rule' gen_sym_table_decls(list(value_decl(_, VDs), Ds)):
          gen_value_declarations(VDs)
          gen_sym_table_decls(Ds)

  'rule' gen_sym_table_decls(list(trans_system_decl(_, TSs), Ds)):
          gen_transition_systems(TSs, sym_table_decl)
          gen_sym_table_decls(Ds)

  'rule' gen_sym_table_decls(list(D, Ds)):
          gen_sym_table_decls(Ds)


'action' gen_init_values(DECLS)

  'rule' gen_init_values(nil):

  'rule' gen_init_values(list(trans_system_decl(_, TSs), Ds)):
          gen_transition_systems(TSs, init_val)
          gen_init_values(Ds)

  'rule' gen_init_values(list(D, Ds)):
          gen_init_values(Ds)


'action' gen_transition_relations(DECLS)

  'rule' gen_transition_relations(nil):

  'rule' gen_transition_relations(list(trans_system_decl(_, TSs), Ds)):
          gen_transition_systems(TSs, trans_rel)

  'rule' gen_transition_relations(list(D, Ds)):
          gen_transition_relations(Ds)


'action' gen_property_specifications(DECLS)

  'rule' gen_property_specifications(nil):

  'rule' gen_property_specifications(list(property_decl(_, P), Ds)):
          gen_properties(P)

  'rule' gen_property_specifications(list(D, Ds)):
          gen_property_specifications(Ds)


'action' gen_type_declarations(TYPE_DEFS)

  'rule' gen_type_declarations(nil):

  'rule' gen_type_declarations(list(D, Ds)):
          gen_type_declaration(D)
          gen_type_declarations(Ds)


'action' gen_type_declaration(TYPE_DEF)

  'rule' gen_type_declaration(variant(_, ID, Vs)):
          WriteFile("\n")
          id_to_string(ID -> S)
          WriteFile(S)
          WriteFile(" == ")
          gen_variants(Vs)

  'rule' gen_type_declaration(abbrev(_, ID, TE)):
          WriteFile("\n")
          id_to_string(ID -> S)
          WriteFile(S)
          WriteFile(" == ")
          gen_type_expr(TE)


'action' gen_variants(VARIANTS)

  'rule' gen_variants(nil):

  'rule' gen_variants(list(V, nil)):
          gen_variant(V)

  'rule' gen_variants(list(V, Vs)):
          gen_variant(V)
          WriteFile(" | ")
          gen_variants(Vs)


'action' gen_variant(VARIANT)

  'rule' gen_variant(record(_, C, _)):
          gen_constructor(C)


'action' gen_constructor(CONSTRUCTOR)

  'rule' gen_constructor(constructor(_, IOO)):
          gen_id_or_op(IOO)


'action' gen_value_declarations(VALUE_DEFS)

  'rule' gen_value_declarations(nil):

  'rule' gen_value_declarations(list(D, Ds)):
          gen_value_declaration(D)
          gen_value_declarations(Ds)


'action' gen_value_declaration(VALUE_DEF)

  'rule' gen_value_declaration(exp_val(_, T, E)):
          WriteFile("\nconst ")
          gen_typing(T)
          WriteFile(" == ")
          gen_value_expr(E)

  'rule' gen_value_declaration(typing(_, T)):
          WriteFile("\n")
          gen_typing(T)

  'rule' gen_value_declaration(exp_fun(P, single(P2, B, TE), FFA, VE, _, _, _)):
          WriteFile("\n")
          gen_return_type(TE)
          WriteFile(" ")
          gen_binding(B)
          WriteFile(" (")
          gen_function_parameters_defs(TE, FFA)
          WriteFile(") {return ")
          gen_value_expr(VE)
          WriteFile("}")


'action' gen_return_type(TYPE_EXPR)

  'rule' gen_return_type(function(_, _, result(_, TE))):
          gen_type_expr(TE)


'action' gen_function_parameters_defs(TYPE_EXPR, FORMAL_FUNCTION_APPLICATION)

  'rule' gen_function_parameters_defs(function(product(P), _, _), form_appl(_, _, list(form_parm(_, Bs), nil))):
          get_parameters_as_list(Bs, nil -> IDs)
          gen_function_parameter_defs(P, IDs)

  'rule' gen_function_parameters_defs(function(TE, _, _), form_appl(_, _, list(form_parm(_, list(B, nil)), nil))):
          gen_type_expr(TE)
          WriteFile(" ")
          gen_binding(B)


'action' gen_function_parameter_defs(PRODUCT_TYPE, IDENTS)

  'rule' gen_function_parameter_defs(nil, nil):

  'rule' gen_function_parameter_defs(list(TE, nil), list(ID, nil)):
          gen_type_expr(TE) 
          WriteFile(" ")
          id_to_string(ID -> S) 
          WriteFile(S)

  'rule' gen_function_parameter_defs(list(TE, P), list(ID, IDs)):
          gen_type_expr(TE) 
          WriteFile(" ")
          id_to_string(ID -> S)
          WriteFile(S)
          WriteFile(", ")
          gen_function_parameter_defs(P, IDs)


'action' get_parameters_as_list(BINDINGS, IDENTS -> IDENTS)

  'rule' get_parameters_as_list(nil, IDs -> RevIDs):
          reverse_ids(IDs , nil -> RevIDs)  --the otherwise the idents are in reverse order compared to their types

  'rule' get_parameters_as_list(list(single(_, id_op(ID)), Bs), IDs -> ID3s):
          where(IDENTS'list(ID, IDs) -> ID2s)
          get_parameters_as_list(Bs, ID2s -> ID3s)


'action' reverse_ids(IDENTS, IDENTS -> IDENTS)

  'rule' reverse_ids(nil, IDs -> IDs):

  'rule' reverse_ids(list(ID, IDs), IDs2 -> IDs4): 
          where(IDENTS'list(ID, IDs2) -> IDs3)
          reverse_ids(IDs, IDs3 -> IDs4)


'action' gen_typing(TYPING)

  'rule' gen_typing(single(_, B, T)):
          gen_type_expr(T)
          WriteFile(" ")
          gen_binding(B)

  'rule' gen_typing(multiple(_, Bs, T)):
          gen_type_expr(T)


'action' gen_binding(BINDING)

  'rule' gen_binding(single(_, IOO)): gen_id_or_op(IOO)


'action' gen_transition_systems(TRANSITION_SYS_DEFS, CONTEXT)

  'rule' gen_transition_systems(nil, _):

  'rule' gen_transition_systems(list(TS, TSs), CK):
          gen_transition_system(TS, CK)
          gen_transition_systems(TSs, CK)


'action' gen_transition_system(TRANSITION_SYS_DEF, CONTEXT)

  'rule' gen_transition_system(trans_sys_def(_, _, S), CK):
          gen_system(S, CK)


'action' gen_system(SYSTEM_DESCRIPTION, CONTEXT)

  'rule' gen_system(no_input(L, TR), trans_rel):
          get_idents_from_local_decls(L -> Is)
          gen_transition_relation(TR, Is) 

  'rule' gen_system(no_input(L, _), CK):
          gen_local_decls(L, CK)


'action' gen_local_decls(DECL, CONTEXT)

  'rule' gen_local_decls(variable_decl(_, VD), CK):
          gen_variable_defs(VD, CK)


'action' gen_variable_defs(VARIABLE_DEFS, CONTEXT)

  'rule' gen_variable_defs(nil, _):

  'rule' gen_variable_defs(list(VD, VDs), CK):
          gen_variable_def(VD, CK)
          gen_variable_defs(VDs, CK)


'action' gen_variable_def(VARIABLE_DEF, CONTEXT)

  'rule' gen_variable_def(single(_, Id, Type, _), sym_table_decl):
          WriteFile("\n")
          gen_type_expr(Type)
          WriteFile(" ")
          id_to_string(Id -> S)
          WriteFile(S)

  'rule' gen_variable_def(single(_, Id, _, initial(VE)), init_val):
          WriteFile("\n")
          id_to_string(Id -> S)
          WriteFile(S)
          WriteFile(" == ")
          gen_value_expr(VE)


'action' get_idents_from_local_decls(DECL -> IDENTS)

  'rule' get_idents_from_local_decls(variable_decl(_, VD) -> Is):
          get_idents_from_var_defs(VD, nil -> Is)


'action' get_idents_from_var_defs(VARIABLE_DEFS, IDENTS -> IDENTS)

  'rule' get_idents_from_var_defs(nil, Ids -> Ids):

  'rule' get_idents_from_var_defs(list(VD, VDs), Ids1 -> Ids3):
          get_idents_from_var_def(VD, Ids1 -> Ids2)
          get_idents_from_var_defs(VDs, Ids2 -> Ids3)


'action' get_idents_from_var_def(VARIABLE_DEF, IDENTS -> IDENTS)

  'rule' get_idents_from_var_def(single(_, Id, _, _), Ids -> Ids2):
          where(IDENTS'list(Id, Ids) -> Ids2)


'action' gen_transition_relation(TRANSITION_OPERATOR, IDENTS)

  'rule' gen_transition_relation(equal_priority(L, R, _), Is):
          gen_transition_relation(L, Is)
          WriteFile(" ||")
          gen_transition_relation(R, Is)

  'rule' gen_transition_relation(guarded_command(C, _), Is):
          WriteFile("\n(")
          gen_transition(C, Is)
          WriteFile(")")


'action' gen_transition(GUARDED_COMMAND, IDENTS)

  'rule' gen_transition(guarded_cmd(_, G, U), Is):
          gen_transition_final(G, U, Is)


'action' gen_transition_final(VALUE_EXPR, COMMANDS, IDENTS)

  'rule' gen_transition_final(VE, Cs, Is):
          (| has_if_expr(VE)
             rewrite_if_expr(VE -> VE2)
             gen_value_expr(VE2)
          || gen_value_expr(VE) |)
          WriteFile(" && ")
          gen_commands(Cs)
          gen_remaining_variables(Cs, Is)


'action' gen_commands(COMMANDS)

  'rule' gen_commands(nil):

  'rule' gen_commands(list(C, nil)):
          gen_command(C)
         
  'rule' gen_commands(list(C, Cs)):
          gen_command(C)
          WriteFile(" && ")
          gen_commands(Cs)


'action' gen_command(COMMAND)

  'rule' gen_command(cmd(P, N, VE)):
          (| has_if_expr(VE)
            rewrite_if_expr(val_infix(P, named_val(P, N), eq, VE) -> VE2)
            gen_value_expr(VE2)
          || gen_name(N)
            WriteFile(" == ")
            gen_value_expr(VE) |)


'action' gen_value_exprs(VALUE_EXPRS)

  'rule' gen_value_exprs(nil):

  'rule' gen_value_exprs(list(VE, VEs)):
          gen_value_expr(VE)
          gen_value_exprs(VEs)


'action' gen_value_expr(VALUE_EXPR)

  'rule' gen_value_expr(val_infix(_, Left, eq, Right)):
          gen_value_expr(Left)
          WriteFile(" == ")
          gen_value_expr(Right)

  'rule' gen_value_expr(val_infix(_, Left, neq, Right)):
          gen_value_expr(Left)
          WriteFile(" != ")
          gen_value_expr(Right)

  'rule' gen_value_expr(val_infix(_, Left, eqeq, Right)):
          gen_value_expr(Left)
          WriteFile(" == ")
          gen_value_expr(Right)

  'rule' gen_value_expr(val_infix(_, Left, gt, Right)):
          gen_value_expr(Left)
          WriteFile(" > ")
          gen_value_expr(Right)

  'rule' gen_value_expr(val_infix(_, Left, lt, Right)):
          gen_value_expr(Left)
          WriteFile(" < ")
          gen_value_expr(Right)

  'rule' gen_value_expr(val_infix(_, Left, ge, Right)):
          gen_value_expr(Left)
          WriteFile(" >= ")
          gen_value_expr(Right)

  'rule' gen_value_expr(val_infix(_, Left, le, Right)):
          gen_value_expr(Left)
          WriteFile(" <= ")
          gen_value_expr(Right)

  'rule' gen_value_expr(val_infix(_, Left, plus, Right)):
          gen_value_expr(Left)
          WriteFile(" + ")
          gen_value_expr(Right)

  'rule' gen_value_expr(val_infix(_, Left, minus, Right)):
          gen_value_expr(Left)
          WriteFile(" - ")
          gen_value_expr(Right)

  'rule' gen_value_expr(val_infix(_, Left, mult, Right)):
          gen_value_expr(Left)
          WriteFile(" * ")
          gen_value_expr(Right)

  'rule' gen_value_expr(val_infix(_, Left, div, Right)):
          gen_value_expr(Left)
          WriteFile(" / ")
          gen_value_expr(Right)

  'rule' gen_value_expr(literal_expr(_, VL)):
          gen_value_literal(VL)

  'rule' gen_value_expr(named_val(_, N)):
          gen_name(N)

  'rule' gen_value_expr(application(_, VE, FP)): 
         (| is_ltl_pathformula(VE)
            gen_pathformula(VE, FP)
         || gen_value_expr(VE)
            WriteFile("(")
            gen_function_parameters(FP)
            WriteFile(")") |)

  'rule' gen_value_expr(case_expr(P, VE, P2, Bs)):
          convert_case_to_if(case_expr(P, VE, P2, Bs) -> IF)
          gen_value_expr(IF)

  'rule' gen_value_expr(if_expr(_, G, T, _, EIs, E)):
          gen_if(G, T, EIs, E)

  'rule' gen_value_expr(equivalence(_, Left, Right, _)):
          gen_value_expr(Left) WriteFile(" == ")
          gen_value_expr(Right)

  'rule' gen_value_expr(bracket(_, VE)):
          WriteFile("(")
          gen_value_expr(VE)
          WriteFile(")")

  'rule' gen_value_expr(ax_infix(_, Left, or, Right, _)):
          gen_value_expr(Left)
          WriteFile(" || ")
          gen_value_expr(Right)

  'rule' gen_value_expr(ax_infix(_, Left, and, Right, _)):
          gen_value_expr(Left)
          WriteFile(" && ")
          gen_value_expr(Right)

  'rule' gen_value_expr(ax_prefix(_, not, VE)):
          WriteFile("!")
          gen_value_expr(VE)


'action' rewrite_if_expr(VALUE_EXPR -> VALUE_EXPR)

  'rule' rewrite_if_expr(if_expr(P, G, T, P2, nil, else(P3, E)) -> if_expr(P, G2, T2, P2, nil, else(P3,E2))):
          rewrite_if_expr(G -> G2)
          rewrite_if_expr(T -> T2)
          rewrite_if_expr(E -> E2)

  'rule' rewrite_if_expr(if_expr(P, G, T, P2, EIs, else(P3, E)) -> NewIf): 
          rewrite_expr_with_elsif(if_expr(P, G, T, P2, EIs, else(P3, E)) -> NewIf)

  'rule' rewrite_if_expr(val_infix(_, if_expr(Pl, Gl, Tl, P2l, EIsl, El), Op, if_expr(Pr, Gr, Tr, P2r, EIsr, Er)) -> NewIf): 
          rewrite_if_expr(if_expr(Pl, Gl, Tl, P2l, EIsl, El) -> FixedIfLeft) 
          where(FixedIfLeft -> if_expr(_, _, _, _, _, else(P3l, E2l)))             
          rewrite_if_expr(if_expr(Pr, Gr, Tr, P2r, EIsr, Er) -> FixedIfRight) 
          where(FixedIfRight -> if_expr(_, _, _, _, _, else(P3r, E2r)))          
          where(if_expr(Pl, ax_infix(Pl, Gl, and, Gr, Pl), val_infix(Pl, Tl, Op, Tr), P2l, nil, 
                 else(P3l, if_expr(Pl, ax_infix(Pl, Gl, and, ax_prefix(Pl, not, Gr), Pl), val_infix(Pl, Tl, Op, E2r), P2l, nil, 
                  else(P3l, if_expr(Pl, ax_infix(Pl, ax_prefix(Pl, not, Gl), and, Gr, Pl), val_infix(Pl, E2l, Op, Tr), P2l, nil, else(P3l, val_infix(Pl, E2l, Op, E2r))))))) -> NewIf)

  'rule' rewrite_if_expr(val_infix(_, if_expr(P, G, T, P2, EIs, else(P4, E)), Op, Right) -> NewIf): 
         (| has_if_expr(Right) 
            rewrite_if_expr(Right -> Right2)
            rewrite_if_expr(if_expr(P, G, T, P2, EIs, else(P4, E)) -> FixedIf) 
            where(FixedIf -> if_expr(_, _, _, _, _, else(P3, E2)))
            rewrite_if_expr(val_infix(P, T, Op, Right2) -> NewThen)
            rewrite_if_expr(val_infix(P, E2, Op, Right2) -> NewElse)
            where(if_expr(P, G, NewThen, P2, nil, else(P3, NewElse)) -> NewIf) 
         ||
            rewrite_if_expr(if_expr(P, G, T, P2, EIs, else(P4, E)) -> FixedIf)
            where(FixedIf -> if_expr(_, _, _, _, _, else(P3, E2))) 
            rewrite_if_expr(val_infix(P, T, Op, Right) -> NewThen)
            rewrite_if_expr(val_infix(P, E2, Op, Right) -> NewElse)
            where(if_expr(P, G, NewThen, P2, nil, else(P3, NewElse)) -> NewIf) |)

  'rule' rewrite_if_expr(val_infix(_, Left, Op, if_expr(P, G, T, P2, EIs, else(P4, E))) -> NewIf): 
         (| has_if_expr(Left) 
            rewrite_if_expr(Left -> Left2)
            rewrite_if_expr(if_expr(P, G, T, P2, EIs, else(P4, E)) -> FixedIf) 
            where(FixedIf -> if_expr(_, _, _, _, _, else(P3, E2))) 
            rewrite_if_expr(val_infix(P, Left2, Op, T) -> NewThen)
            rewrite_if_expr(val_infix(P, Left2, Op, E2) -> NewElse)
            where(if_expr(P, G, NewThen, P2, nil, else(P3, NewElse)) -> NewIf) 
         ||
            rewrite_if_expr(if_expr(P, G, T, P2, EIs, else(P4, E)) -> FixedIf)
            where(FixedIf -> if_expr(_, _, _, _, _, else(P3, E2))) 
            rewrite_if_expr(val_infix(P, Left, Op, T) -> NewThen)
            rewrite_if_expr(val_infix(P, Left, Op, E2) -> NewElse)
            where(if_expr(P, G, NewThen, P2, nil, else(P3, NewElse)) -> NewIf) |)

  'rule' rewrite_if_expr(ax_prefix(P, not, VE) -> ax_prefix(P, not, VE2)):
         (| has_if_expr(VE)
            rewrite_if_expr(VE -> VE2)
         ||
            where(VE -> VE2) |)
            
  'rule' rewrite_if_expr(val_infix(P, Left, Op, Right) -> NewIf): 
         (| has_if_expr(Left)
            has_if_expr(Right)
            rewrite_if_expr(Left -> Left2)
            rewrite_if_expr(Right -> Right2)
            rewrite_if_expr(val_infix(P, Left2, Op, Right2) -> NewIf)
         ||
            has_if_expr(Left)
            rewrite_if_expr(Left -> Left2)
            rewrite_if_expr(val_infix(P, Left2, Op, Right) -> NewIf)
         ||
            has_if_expr(Right)
            rewrite_if_expr(Right -> Right2)
            rewrite_if_expr(val_infix(P, Left, Op, Right2) -> NewIf)
         ||
            where(val_infix(P, Left, Op, Right) -> NewIf) |)

  'rule' rewrite_if_expr(case_expr(P, VE, P2, Bs) -> IF):
         convert_case_to_if(case_expr(P, VE, P2, Bs) -> IF)

  'rule' rewrite_if_expr(VE -> VE): 


'action' rewrite_expr_with_elsif(VALUE_EXPR -> VALUE_EXPR)

  'rule' rewrite_expr_with_elsif(if_expr(P, G, T, P2, nil, else(P3, E)) -> if_expr(P, G, T, P2, nil, else(P3, E))):

  'rule' rewrite_expr_with_elsif(if_expr(P, G, T, P2, list(EI, EIs), else(P3, E)) -> if_expr(P, G, T, P2, nil, else(P3, NewElse))): 
          where(EI -> elsif(_, G2, T2, _))
          rewrite_expr_with_elsif(if_expr(P, G2, T2, P2, EIs, else(P3, E)) -> NewElse)


'action' gen_if(VALUE_EXPR, VALUE_EXPR, ELSIF_BRANCHES, ELSE_BRANCH)

  'rule' gen_if(G, T, EIs, else(_, VE)):
          WriteFile("((")
          gen_value_expr(G)
          WriteFile(" && ")
          gen_value_expr(T)
          WriteFile(")")
          gen_elsifs(EIs)
          WriteFile(" || (!(")
          gen_value_expr(G)
          WriteFile(") && ")
          gen_value_expr(VE)
          WriteFile("))")


'action' gen_elsifs(ELSIF_BRANCHES)

  'rule' gen_elsifs(nil):
  'rule' gen_elsifs(list(B, Bs)): gen_elsif(B) gen_elsifs(Bs)


'action' gen_elsif(ELSIF_BRANCH)

  'rule' gen_elsif(elsif(_, G, T, _)):
          WriteFile(" || (")
          gen_value_expr(G)
          WriteFile(" && ")
          gen_value_expr(T)
          WriteFile(")")


'action' convert_case_to_if(VALUE_EXPR -> VALUE_EXPR)

  'rule' convert_case_to_if(case_expr(P, VE, P2, Bs) -> if_expr(P, G, T, region(P, P2), EIs, E)):
          get_guard(VE, Bs -> G)
          get_then(Bs -> Bs2, T)
          get_elsif(VE, Bs2, nil -> EIs)
          get_else(Bs2 -> E)


'action' get_guard(VALUE_EXPR, CASE_BRANCHES -> VALUE_EXPR)

  'rule' get_guard(VE, list(case(P, literal_pattern(_, VL), _, _), _) -> val_infix(P, VE, eq, literal_expr(P, VL))):

  'rule' get_guard(VE, list(case(P, name_pattern(_, N), _, _), _) -> val_infix(P, VE, eq, named_val(P, N))):


'action' get_then(CASE_BRANCHES -> CASE_BRANCHES, VALUE_EXPR)

  'rule' get_then(list(case(_, _, VE, _), Bs) -> Bs, VE):


'action' get_elsif(VALUE_EXPR, CASE_BRANCHES, ELSIF_BRANCHES -> ELSIF_BRANCHES)

  'rule' get_elsif(VE, list(case(P, literal_pattern(P2, VL), VE2, _), Bs), EIs -> EIs3):
          where(ELSIF_BRANCHES'list(elsif(P, val_infix(P, VE, eq, literal_expr(P2, VL)), VE2, P), EIs) -> EIs2)
          get_elsif(VE, Bs, EIs2 -> EIs3)

  'rule' get_elsif(VE, list(case(P, name_pattern(P2, N), VE2, _), Bs), EIs -> EIs3):
          where(ELSIF_BRANCHES'list(elsif(P, val_infix(P, VE, eq, named_val(P2, N)), VE2, P), EIs) -> EIs2)
          get_elsif(VE, Bs, EIs2 -> EIs3)

  'rule' get_elsif(_, list(case(P, wildcard_pattern(_), _, _), _), EIs -> EIs): 


'action' get_else(CASE_BRANCHES -> ELSE_BRANCH)

  'rule' get_else(list(case(P, wildcard_pattern(_), VE, _), _) -> else(P, VE)):

  'rule' get_else(list(B, Bs) -> E):
          get_else(Bs -> E)


'action' gen_value_literal(VALUE_LITERAL)

  'rule' gen_value_literal(int(I)):
          id_to_string(I -> S)
          WriteFile(S)

  'rule' gen_value_literal(bool_true):
          WriteFile("true")

  'rule' gen_value_literal(bool_false):
          WriteFile("false")

  'rule' gen_value_literal(real(R)):
          id_to_string(R -> S)
          WriteFile(S)


'action' gen_properties(PROPERTY_DECLS)

  'rule' gen_properties(nil):

  'rule' gen_properties(list(PD, PDs)):
          gen_property(PD)
          gen_properties(PDs)


'action' gen_pathformula(VALUE_EXPR, ACTUAL_FUNCTION_PARAMETERS)

  'rule' gen_pathformula(named_val(_, name(_, id_op(ID))), FPs): 
          id_to_string(ID -> S) 
          (| eq(S, "U")
             where(FPs->list(FP,_))
             gen_ltl_until(FP)
          || 
            (| eq(S, "G")
               WriteFile("Globally")
            || eq(S, "F")
               WriteFile("Finally")
            || eq(S, "X")
               WriteFile("Next") 
            |)
            WriteFile("[")
            gen_function_parameters(FPs)
            WriteFile("]") 
          |)

'action' gen_ltl_until(ACTUAL_FUNCTION_PARAMETER)

  'rule' gen_ltl_until(fun_arg(P, list(VE,nil))):
          WriteFile("Until")
          WriteFile("[")
          gen_value_expr(VE)
          WriteFile("]") 

  'rule' gen_ltl_until(fun_arg(P, list(VE,VEs))):
          WriteFile("[")
          gen_value_expr(VE)
          WriteFile("]") 
          gen_ltl_until(fun_arg(P, VEs))


'action' gen_property(PROPERTY_DECL)

  'rule' gen_property(property_def(_, _, _, P)):
          WriteFile("\n")
          gen_value_expr(P)


'action' gen_id_or_op(ID_OR_OP)

  'rule' gen_id_or_op(id_op(I)):
          id_to_string(I -> S)
          WriteFile(S)


'action' gen_name(NAME)

  'rule' gen_name(name(_, IOO)):
          gen_id_or_op(IOO)


'action' gen_type_expr(TYPE_EXPR)

  'rule' gen_type_expr(int):
          WriteFile("int")

  'rule' gen_type_expr(bool):
          WriteFile("bool")

  'rule' gen_type_expr(nat):
          WriteFile("nat")

  'rule' gen_type_expr(real):
          WriteFile("real")

  'rule' gen_type_expr(subtype(T, R)):
          gen_typing(T)
          WriteFile(" where ")
          gen_restriction(R)

  'rule' gen_type_expr(named_type(N)):
          gen_name(N)


'action' gen_restriction(RESTRICTION)

  'rule' gen_restriction(nil):

  'rule' gen_restriction(restriction(_, VE)):
          gen_value_expr(VE)


'action' gen_function_parameters(ACTUAL_FUNCTION_PARAMETERS)

  'rule' gen_function_parameters(nil):

  'rule' gen_function_parameters(list(FP, nil)):
          gen_function_parameter(FP)

  'rule' gen_function_parameters(list(FP, FPs)):
          gen_function_parameter(FP)
          gen_function_parameters(FPs)


'action' gen_function_parameter(ACTUAL_FUNCTION_PARAMETER)

  'rule' gen_function_parameter(fun_arg(_, list(VE,nil))):
          gen_value_expr(VE)

  'rule' gen_function_parameter(fun_arg(P, list(VE,VEs))):
          gen_value_expr(VE)
          WriteFile(",")
          gen_function_parameter(fun_arg(P, VEs))


'action' gen_remaining_variables(COMMANDS, IDENTS)

  'rule' gen_remaining_variables(Cs, nil):

  'rule' gen_remaining_variables(Cs, list(I, Is)): 
          id_to_string(I -> S)
          (| is_part_of_commands(S, Cs)
          || WriteFile(" && ")
             WriteFile(S) 
             WriteFile("' == ")
             WriteFile(S) |)
          gen_remaining_variables(Cs, Is)


'action' check_enums_for_duplicates(DECLS, IDENTS)

  'rule' check_enums_for_duplicates(nil, _):

  'rule' check_enums_for_duplicates(list(type_decl(_, TDs), Ds), IDs):
          get_enum_ids_from_type_defs(TDs, nil -> IDs2)
          append_ident_lists(IDs, IDs2 -> IDs3)
          check_enums_for_duplicates(Ds, IDs3) 

  'rule' check_enums_for_duplicates(list(D, Ds), IDs):
          check_enums_for_duplicates(Ds, IDs)


'action' get_enum_ids_from_type_defs(TYPE_DEFS, IDENTS -> IDENTS)

  'rule' get_enum_ids_from_type_defs(nil, IDs -> IDs):

  'rule' get_enum_ids_from_type_defs(list(variant(_, _, Vs), TDs), IDs -> IDs4):
          get_ids_from_variants(Vs, nil -> IDs2)
          append_ident_lists(IDs, IDs2 -> IDs3)
          get_enum_ids_from_type_defs(TDs, IDs3 -> IDs4)

  'rule' get_enum_ids_from_type_defs(list(TD, TDs), IDs -> IDs2):
          get_enum_ids_from_type_defs(TDs, IDs -> IDs2)


'action' get_ids_from_variants(VARIANTS, IDENTS -> IDENTS)

  'rule' get_ids_from_variants(nil, IDs -> IDs):

  'rule' get_ids_from_variants(list(record(_, constructor(_, id_op(ID)), _), Vs), IDs -> IDs3):
          check_id_for_duplicate(ID, IDs)
          where(IDENTS'list(ID, IDs) -> IDs2)
          get_ids_from_variants(Vs, IDs2 -> IDs3)

  'rule' get_ids_from_variants(list(V, Vs), IDs -> IDs2):
          get_ids_from_variants(Vs, IDs -> IDs2)


'action' append_ident_lists(IDENTS, IDENTS -> IDENTS)

  'rule' append_ident_lists(nil, IDs -> IDs):

  'rule' append_ident_lists(list(ID, IDs), IDs2 -> IDs4):
          where(IDENTS'list(ID, IDs2) -> IDs3)
          append_ident_lists(IDs, IDs3 -> IDs4)


'condition' is_part_of_commands(STRING, COMMANDS)

  'rule' is_part_of_commands(S, nil):

  'rule' is_part_of_commands(S, list(C, Cs)):
          is_part_of_command(S, C)
          is_part_of_commands(S, Cs)


'condition' is_part_of_command(STRING, COMMAND)

  'rule' is_part_of_command(S, C): 
          where(C -> cmd(_, N, _))
          where(N -> name(_, IOO))
          where(IOO -> id_op(I))
          id_to_string(I -> SP)
          Remove_Prime(SP -> S1)
          eq(S1, S)


'condition' has_if_expr(VALUE_EXPR)

  'rule' has_if_expr(if_expr(_, _, _, _, _, _)):

  'rule' has_if_expr(case_expr(_, _, _, _)):

  'rule' has_if_expr(val_infix(_, Left, _, Right)):
          (| has_if_expr(Left)
          || has_if_expr(Right) |)

  'rule' has_if_expr(application(_, VE, _)):
          has_if_expr(VE)

  'rule' has_if_expr(equivalence(_, Left, Right, _)):
          (| has_if_expr(Left) 
          || has_if_expr(Right) |)


'condition' is_ltl_pathformula(VALUE_EXPR)

  'rule' is_ltl_pathformula(named_val(_, name(_, id_op(ID)))): 
          id_to_string(ID -> S) 
          (| eq(S, "G") 
          || eq(S, "F") 
          || eq(S, "X")
          || eq(S, "U") |)


'condition' check_id_for_duplicate(IDENT, IDENTS)

  'rule' check_id_for_duplicate(_, nil):

  'rule' check_id_for_duplicate(ID, list(ID2, IDs)): 
          (| ne(ID, ID2) 
             check_id_for_duplicate(ID, IDs) 
          || ErrorUsage("Error: enum is used more than once") |)


'type' CONTEXT

       sym_table_decl
       init_val
       trans_rel
