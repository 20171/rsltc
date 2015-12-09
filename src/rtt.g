-- This module defines the rsl -> RT-Tester(ASCII) translator

'module' rtt

'use' ast ext env

'export' gen_rtt_ascii



'action' gen_rtt_ascii(LIB_MODULE)

  'rule' gen_rtt_ascii(scheme(_,_,_,S)): 
         Module_name -> N
         string_to_id(N -> Id)
         OpenRTTFile(Id -> _) 
         gen_scheme(S)
         CloseOutputFile


'action' gen_scheme(SCHEME_DEF)

  'rule' gen_scheme(sdef(_,_,_,C)): gen_class(C)


'action' gen_class(CLASS)

  'rule' gen_class(basic(Ds)): 
          WriteFile("TYPES") 
          gen_types(Ds) 
          WriteFile("\nTYPES_END\nVAR_DECL") 
          gen_var_decls(Ds) 
          WriteFile("\nVAR_DECL_END\nINIT_VAL") 
          gen_init_values(Ds) 
          WriteFile("\nINIT_VAL_END\nTRANS_REL") 
          gen_transition_relations(Ds) 
          WriteFile("\nTRANS_REL_END\nPROP_SPEC") 
          gen_property_specifications(Ds) 
          WriteFile("\nPROP_SPEC_END")


'action' gen_types(DECLS)

  'rule' gen_types(nil):
  'rule' gen_types(list(type_decl(_,TDs),Ds)): gen_type_declarations(TDs) gen_types_decls(Ds)


'action' gen_var_decls(DECLS)

  'rule' gen_var_decls(nil):
  'rule' gen_var_decls(list(value_decl(_,VDs),Ds)): gen_value_declarations(VDs) gen_var_decls(Ds)
  'rule' gen_var_decls(list(trans_system_decl(_,TSs),Ds)): gen_transition_systems(TSs,var_decl) gen_var_decls(Ds)
  'rule' gen_var_decls(list(D,Ds)): gen_var_decls(Ds)


'action' gen_init_values(DECLS)

  'rule' gen_init_values(nil):
  'rule' gen_init_values(list(trans_system_decl(_,TSs),Ds)): gen_transition_systems(TSs,init_val) gen_init_values(Ds)
  'rule' gen_init_values(list(axiom_decl(_,ADs),Ds)): gen_axiom_declarations(ADs) gen_init_values(Ds)
  'rule' gen_init_values(list(D,Ds)): gen_init_values(Ds)


'action' gen_transition_relations(DECLS)

  'rule' gen_transition_relations(nil):
  'rule' gen_transition_relations(list(trans_system_decl(_,TSs),Ds)): gen_transition_systems(TSs,trans_rel)
  'rule' gen_transition_relations(list(D,Ds)): gen_transition_relations(Ds)


'action' gen_property_specifications(DECLS)

  'rule' gen_property_specifications(nil):
  'rule' gen_property_specifications(list(property_decl(_,P),Ds)): gen_properties(P)
  'rule' gen_property_specifications(list(D,Ds)): gen_property_specifications(Ds)


'action' gen_axiom_declarations(AXIOM_DEFS)

  'rule' gen_axiom_declarations(nil):
  'rule' gen_axiom_declarations(list(D,Ds)): gen_axiom_declaration(D) gen_axiom_declarations(Ds)


'action' gen_axiom_declaration(AXIOM_DEF)

  'rule' gen_axiom_declaration(axiom_def(_,_,VE)): WriteFile("\n") gen_value_expr(VE)


'action' gen_value_declarations(VALUE_DEFS)

  'rule' gen_value_declarations(nil):
  'rule' gen_value_declarations(list(D,Ds)): gen_value_declaration(D) gen_value_declarations(Ds)


'action' gen_value_declaration(VALUE_DEF)

  'rule' gen_value_declaration(exp_val(_,T,E)): WriteFile("\nconst ") gen_typing(T) WriteFile(" == ") gen_value_expr(E)
  'rule' gen_value_declaration(typing(_,T)): WriteFile("\n") gen_typing(T)


'action' gen_typing(TYPING)

  'rule' gen_typing(single(_,B,T)): gen_type_expr(T) WriteFile(" ") gen_binding(B)
  'rule' gen_typing(multiple(_,Bs,T)): gen_type_expr(T)


'action' gen_binding(BINDING)

  'rule' gen_binding(single(_,IOO)): gen_id_or_op(IOO)


'action' gen_transition_systems(TRANSITION_SYS_DEFS,CONTROLKEY)

  'rule' gen_transition_systems(nil,_):
  'rule' gen_transition_systems(list(TS,TSs),CK): gen_transition_system(TS,CK) gen_transition_systems(TSs,CK)


'action' gen_transition_system(TRANSITION_SYS_DEF,CONTROLKEY)

  'rule' gen_transition_system(trans_sys_def(_,_,S),CK): gen_system(S,CK)


'action' gen_system(SYSTEM_DESCRIPTION,CONTROLKEY)

  'rule' gen_system(no_input(L,TR),trans_rel): get_idents_from_local_decls(L->Is) gen_transition_relation(TR,Is) 
  'rule' gen_system(no_input(L,_),CK): gen_local_decls(L,CK)


'action' gen_local_decls(DECL,CONTROLKEY)

  'rule' gen_local_decls(variable_decl(_,VD),CK): gen_variable_defs(VD,CK)


'action' gen_variable_defs(VARIABLE_DEFS,CONTROLKEY)

  'rule' gen_variable_defs(nil,_):
  'rule' gen_variable_defs(list(VD,VDs),CK): gen_variable_def(VD,CK) gen_variable_defs(VDs,CK)


'action' gen_variable_def(VARIABLE_DEF,CONTROLKEY)

  'rule' gen_variable_def(single(_,Id,Type,_),var_decl): WriteFile("\n") gen_type_expr(Type) WriteFile(" ") id_to_string(Id->S) WriteFile(S)
  'rule' gen_variable_def(single(_,Id,_,initial(VE)),init_val): WriteFile("\n") id_to_string(Id->S) WriteFile(S) WriteFile(" == ") gen_value_expr(VE)


'action' get_idents_from_local_decls(DECL->IDENTS)

  'rule' get_idents_from_local_decls(variable_decl(_,VD)->Is): get_idents_from_var_defs(VD,nil->Is)


'action' get_idents_from_var_defs(VARIABLE_DEFS,IDENTS->IDENTS)

  'rule' get_idents_from_var_defs(nil,Ids->Ids):
  'rule' get_idents_from_var_defs(list(VD,VDs),Ids1->Ids3): get_idents_from_var_def(VD,Ids1->Ids2) get_idents_from_var_defs(VDs,Ids2->Ids3)


'action' get_idents_from_var_def(VARIABLE_DEF,IDENTS->IDENTS)

  'rule' get_idents_from_var_def(single(_,Id,_,_),Ids->Ids2): where(IDENTS'list(Id,Ids)->Ids2)


'action' gen_transition_relation(TRANSITION_OPERATOR,IDENTS)

  'rule' gen_transition_relation(equal_priority(L,R,_),Is): WriteFile("\n(") gen_transition_relation(L,Is) WriteFile(") ||\n(") gen_transition_relation(R,Is) WriteFile(")")
  'rule' gen_transition_relation(guarded_command(C,_),Is): gen_transition(C,Is)


'action' gen_transition(GUARDED_COMMAND,IDENTS)

  'rule' gen_transition(guarded_cmd(_,G,U),Is): gen_transition_final(G,U,Is)


'action' gen_transition_final(VALUE_EXPR,COMMANDS,IDENTS)

  'rule' gen_transition_final(VE,Cs,Is): (| has_if_statement(VE) rewrite_if_expr(VE->VE2) gen_value_expr(VE2) || gen_value_expr(VE) |) WriteFile(" && ") gen_commands(Cs) gen_remaining_variables(Cs,Is)


'action' gen_commands(COMMANDS)

  'rule' gen_commands(nil):
  'rule' gen_commands(list(C,Cs)): gen_command(C) gen_commands(Cs)


'action' gen_command(COMMAND)

  'rule' gen_command(cmd(P,N,VE)): (| has_if_statement(VE) rewrite_if_expr(val_infix(P,named_val(P,N),eq,VE)->VE2) gen_value_expr(VE2) || gen_name(N) WriteFile(" == ") gen_value_expr(VE) |)


'action' gen_value_exprs(VALUE_EXPRS)

  'rule' gen_value_exprs(nil):
  'rule' gen_value_exprs(list(VE,VEs)): gen_value_expr(VE) gen_value_exprs(VEs)


'action' gen_value_expr(VALUE_EXPR)

  'rule' gen_value_expr(val_infix(_,Left,eq,Right)): gen_value_expr(Left) WriteFile(" == ") gen_value_expr(Right)
  'rule' gen_value_expr(val_infix(_,Left,neq,Right)): gen_value_expr(Left) WriteFile(" != ") gen_value_expr(Right)
  'rule' gen_value_expr(val_infix(_,Left,eqeq,Right)): gen_value_expr(Left) WriteFile(" == ") gen_value_expr(Right)
  'rule' gen_value_expr(val_infix(_,Left,gt,Right)): gen_value_expr(Left) WriteFile(" > ") gen_value_expr(Right)
  'rule' gen_value_expr(val_infix(_,Left,lt,Right)): gen_value_expr(Left) WriteFile(" < ") gen_value_expr(Right)
  'rule' gen_value_expr(val_infix(_,Left,ge,Right)): gen_value_expr(Left) WriteFile(" >= ") gen_value_expr(Right)
  'rule' gen_value_expr(val_infix(_,Left,le,Right)): gen_value_expr(Left) WriteFile(" <= ") gen_value_expr(Right)
  'rule' gen_value_expr(val_infix(_,Left,plus,Right)): gen_value_expr(Left) WriteFile(" + ") gen_value_expr(Right)
  'rule' gen_value_expr(val_infix(_,Left,minus,Right)): gen_value_expr(Left) WriteFile(" - ") gen_value_expr(Right)
  'rule' gen_value_expr(val_infix(_,Left,mult,Right)): gen_value_expr(Left) WriteFile(" * ") gen_value_expr(Right)
  'rule' gen_value_expr(val_infix(_,Left,div,Right)): gen_value_expr(Left) WriteFile(" / ") gen_value_expr(Right)
  'rule' gen_value_expr(literal_expr(_,VL)): gen_value_literal(VL)
  'rule' gen_value_expr(named_val(_,N)): gen_name(N)
  'rule' gen_value_expr(application(_,VE,FP)): gen_value_expr(VE) WriteFile("(") gen_function_parameters(FP) WriteFile(")")
  'rule' gen_value_expr(case_expr(_,VE,_,Bs)): get_patterns_from_branches(Bs,nil->Ps) gen_case_expr(VE,Bs,Ps)
  'rule' gen_value_expr(if_expr(_,G,T,_,EIs,E)): gen_if(G,T,EIs,E)
  'rule' gen_value_expr(equivalence(_,Left,Right,_)): gen_value_expr(Left) WriteFile(" == ") gen_value_expr(Right)
  'rule' gen_value_expr(bracket(_,VE)): WriteFile("(") gen_value_expr(VE) WriteFile(")")
  'rule' gen_value_expr(ax_infix(_,Left,or,Right,_)): gen_value_expr(Left) WriteFile(" || ") gen_value_expr(Right)
  'rule' gen_value_expr(ax_infix(_,Left,and,Right,_)): gen_value_expr(Left) WriteFile(" && ") gen_value_expr(Right)
  'rule' gen_value_expr(ax_prefix(_,not,VE)): WriteFile("!") gen_value_expr(VE)


'action' rewrite_if_expr(VALUE_EXPR->VALUE_EXPR)

  'rule' rewrite_if_expr(if_expr(P,G,T,P2,nil,E)->if_expr(P,G,T,P2,nil,E)):
  'rule' rewrite_if_expr(if_expr(P,G,T,P2,EIs,else(P3,E))->NewIf): rewrite_expr_with_elsif(if_expr(P,G,T,P2,EIs,else(P3,E))->NewIf)
  'rule' rewrite_if_expr(val_infix(_,if_expr(Pl,Gl,Tl,P2l,EIsl,El),Op,if_expr(Pr,Gr,Tr,P2r,EIsr,Er))->NewIf): 
         rewrite_if_expr(if_expr(Pl,Gl,Tl,P2l,EIsl,El)->FixedIfLeft) 
         where(FixedIfLeft->if_expr(_,_,_,_,_,else(P3l,E2l)))             
         rewrite_if_expr(if_expr(Pr,Gr,Tr,P2r,EIsr,Er)->FixedIfRight) 
         where(FixedIfRight->if_expr(_,_,_,_,_,else(P3r,E2r)))          
         where(if_expr(Pl,ax_infix(Pl,Gl,and,Gr,Pl),val_infix(Pl,Tl,Op,Tr),P2l,nil,
                 else(P3l,if_expr(Pl,ax_infix(Pl,Gl,and,ax_prefix(Pl,not,Gr),Pl),val_infix(Pl,Tl,Op,E2r),P2l,nil,
                   else(P3l,if_expr(Pl,ax_infix(Pl,ax_prefix(Pl,not,Gl),and,Gr,Pl),val_infix(Pl,E2l,Op,Tr),P2l,nil,else(P3l,val_infix(Pl,E2l,Op,E2r)))))))->NewIf)
  'rule' rewrite_if_expr(val_infix(_,if_expr(P,G,T,P2,EIs,else(P4,E)),Op,Right)->NewIf): 
         (| 
            has_if_statement(Right) 
            rewrite_if_expr(Right->Right2)
            rewrite_if_expr(if_expr(P,G,T,P2,EIs,else(P4,E))->FixedIf) 
            where(FixedIf->if_expr(_,_,_,_,_,else(P3,E2)))
            rewrite_if_expr(val_infix(P,T,Op,Right2)->NewThen)
            rewrite_if_expr(val_infix(P,E2,Op,Right2)->NewElse)
            where(if_expr(P,G,NewThen,P2,nil,else(P3,NewElse))->NewIf) 
         ||
            rewrite_if_expr(if_expr(P,G,T,P2,EIs,else(P4,E))->FixedIf)
            where(FixedIf->if_expr(_,_,_,_,_,else(P3,E2))) 
            rewrite_if_expr(val_infix(P,T,Op,Right)->NewThen)
            rewrite_if_expr(val_infix(P,E2,Op,Right)->NewElse)
            where(if_expr(P,G,NewThen,P2,nil,else(P3,NewElse))->NewIf) 
         |)
  'rule' rewrite_if_expr(val_infix(_,Left,Op,if_expr(P,G,T,P2,EIs,else(P4,E)))->NewIf): 
         (| 
            has_if_statement(Left) 
            rewrite_if_expr(Left->Left2)
            rewrite_if_expr(if_expr(P,G,T,P2,EIs,else(P4,E))->FixedIf) 
            where(FixedIf->if_expr(_,_,_,_,_,else(P3,E2))) 
            rewrite_if_expr(val_infix(P,Left2,Op,T)->NewThen)
            rewrite_if_expr(val_infix(P,Left2,Op,E2)->NewElse)
            where(if_expr(P,G,NewThen,P2,nil,else(P3,NewElse))->NewIf) 
         ||
            rewrite_if_expr(if_expr(P,G,T,P2,EIs,else(P4,E))->FixedIf)
            where(FixedIf->if_expr(_,_,_,_,_,else(P3,E2))) 
            rewrite_if_expr(val_infix(P,Left,Op,T)->NewThen)
            rewrite_if_expr(val_infix(P,Left,Op,E2)->NewElse)
            where(if_expr(P,G,NewThen,P2,nil,else(P3,NewElse))->NewIf) 
         |)
  'rule' rewrite_if_expr(val_infix(P,Left,Op,Right)->NewIf): 
         (|
            has_if_statement(Left)
            has_if_statement(Right)
            rewrite_if_expr(Left->Left2)
            rewrite_if_expr(Right->Right2)
            rewrite_if_expr(val_infix(P,Left2,Op,Right2)->NewIf)
         ||
            has_if_statement(Left)
            rewrite_if_expr(Left->Left2)
            rewrite_if_expr(val_infix(P,Left2,Op,Right)->NewIf)
         ||
            has_if_statement(Right)
            rewrite_if_expr(Right->Right2)
            rewrite_if_expr(val_infix(P,Left,Op,Right2)->NewIf)
         ||
            where(val_infix(P,Left,Op,Right)->NewIf)
         |)
  'rule' rewrite_if_expr(VE->VE): 


'action' rewrite_expr_with_elsif(VALUE_EXPR->VALUE_EXPR)

  'rule' rewrite_expr_with_elsif(if_expr(P,G,T,P2,nil,else(P3,E))->if_expr(P,G,T,P2,nil,else(P3,E))):
  'rule' rewrite_expr_with_elsif(if_expr(P,G,T,P2,list(EI,EIs),else(P3,E))->if_expr(P,G,T,P2,nil,else(P3,NewElse))): 
         where(EI->elsif(_,G2,T2,_))
         rewrite_expr_with_elsif(if_expr(P,G2,T2,P2,EIs,else(P3,E))->NewElse)


'action' gen_if(VALUE_EXPR,VALUE_EXPR,ELSIF_BRANCHES,ELSE_BRANCH)

  'rule' gen_if(G,T,EIs,else(_,VE)): WriteFile("((") gen_value_expr(G) WriteFile(" && ") gen_value_expr(T) WriteFile(")") gen_elsifs(EIs) WriteFile(" || (!(") gen_value_expr(G) WriteFile(") && ") gen_value_expr(VE) WriteFile("))")


'action' gen_elsifs(ELSIF_BRANCHES)

  'rule' gen_elsifs(nil):
  'rule' gen_elsifs(list(B,Bs)): gen_elsif(B) gen_elsifs(Bs)


'action' gen_elsif(ELSIF_BRANCH)

  'rule' gen_elsif(elsif(_,G,T,_)): WriteFile(" || (") gen_value_expr(G) WriteFile(" && ") gen_value_expr(T) WriteFile(")")


'action' gen_case_expr(VALUE_EXPR,CASE_BRANCHES,PATTERNS)

  'rule' gen_case_expr(VE,nil,Ps):
  'rule' gen_case_expr(VE,list(B,nil),Ps): gen_branch(VE,B,Ps)
  'rule' gen_case_expr(VE,list(B,Bs),Ps): gen_branch(VE,B,Ps) WriteFile(" || ") gen_case_expr(VE,Bs,Ps)


'action' gen_branch(VALUE_EXPR,CASE_BRANCH,PATTERNS)

  'rule' gen_branch(VE1,case(_,wildcard_pattern(_),VE2,_),Ps): WriteFile("(") gen_wildcard(VE1,VE2,Ps) WriteFile(")")
  'rule' gen_branch(VE1,case(_,P,VE2,_),_): WriteFile("(") gen_value_expr(VE1) WriteFile(" == ") gen_pattern(P) WriteFile(" && ") gen_value_expr(VE2) WriteFile(")")


'action' gen_pattern(PATTERN)

  'rule' gen_pattern(literal_pattern(_,VL)): gen_value_literal(VL)
  'rule' gen_pattern(name_pattern(_,N)): gen_name(N)
  'rule' gen_pattern(id_pattern(_,IOO)): gen_id_or_op(IOO)


'action' get_patterns_from_branches(CASE_BRANCHES,PATTERNS->PATTERNS)

  'rule' get_patterns_from_branches(nil,Ps->Ps):
  'rule' get_patterns_from_branches(list(case(_,wildcard_pattern(_),_,_),Bs),Ps->Ps):
  'rule' get_patterns_from_branches(list(case(_,P,_,_),Bs),Ps1->Ps3): where(PATTERNS'list(P,Ps1) -> Ps2) get_patterns_from_branches(Bs,Ps2->Ps3)


'action' gen_wildcard(VALUE_EXPR,VALUE_EXPR,PATTERNS)

  'rule' gen_wildcard(_,VE2,nil): gen_value_expr(VE2)
  'rule' gen_wildcard(VE1,VE2,list(P,Ps)): gen_value_expr(VE1) WriteFile(" != ") gen_pattern(P) WriteFile(" && ") gen_wildcard(VE1,VE2,Ps)


'action' gen_value_literal(VALUE_LITERAL)

  'rule' gen_value_literal(int(I)): id_to_string(I->S) WriteFile(S)
  'rule' gen_value_literal(bool_true): WriteFile("true")
  'rule' gen_value_literal(bool_false): WriteFile("false")
  'rule' gen_value_literal(real(R)): id_to_string(R->S) WriteFile(S)


'action' gen_properties(PROPERTY_DECLS)

  'rule' gen_properties(nil):
  'rule' gen_properties(list(PD,PDs)): gen_property(PD) gen_properties(PDs)


'action' gen_property(PROPERTY_DECL)

  'rule' gen_property(property_def(_,_,_,P)): WriteFile("\n") gen_value_expr(P)


'action' gen_id_or_op(ID_OR_OP)

  'rule' gen_id_or_op(id_op(I)): id_to_string(I->S) WriteFile(S)


'action' gen_name(NAME)

  'rule' gen_name(name(_,IOO)): gen_id_or_op(IOO)


'action' gen_type_expr(TYPE_EXPR)

  'rule' gen_type_expr(int): WriteFile("int")
  'rule' gen_type_expr(bool): WriteFile("bool")
  'rule' gen_type_expr(nat): WriteFile("nat")
  'rule' gen_type_expr(real): WriteFile("real")


'action' gen_function_parameters(ACTUAL_FUNCTION_PARAMETERS)

  'rule' gen_function_parameters(nil):
  'rule' gen_function_parameters(list(FP,FPs)): gen_function_parameter(FP) gen_function_parameters(FPs)


'action' gen_function_parameter(ACTUAL_FUNCTION_PARAMETER)

  'rule' gen_function_parameter(fun_arg(_,VEs)): gen_value_exprs(VEs)


'action' gen_remaining_variables(COMMANDS,IDENTS)

  'rule' gen_remaining_variables(Cs,nil):
  'rule' gen_remaining_variables(Cs,list(I,Is)): 
         id_to_string(I->S)
         (|
	   is_part_of_commands(S,Cs)
         ||
           WriteFile(" && ") WriteFile(S) WriteFile("' == ") WriteFile(S)
         |)
         gen_remaining_variables(Cs,Is)


'condition' is_part_of_commands(STRING,COMMANDS)

  'rule' is_part_of_commands(S,nil):
  'rule' is_part_of_commands(S,list(C,Cs)): is_part_of_command(S,C) is_part_of_commands(S,Cs)


'condition' is_part_of_command(STRING,COMMAND)

  'rule' is_part_of_command(S,C): where(C->cmd(_,N,_)) where(N->name(_,IOO)) where(IOO->id_op(I)) id_to_string(I->SP) Remove_Prime(SP->S1) eq(S1,S)


'condition' has_if_statement(VALUE_EXPR)

  'rule' has_if_statement(if_expr(_,G,T,_,EIs,E)):
  'rule' has_if_statement(val_infix(_,Left,_,Right)): (| has_if_statement(Left) || has_if_statement(Right) |)
  'rule' has_if_statement(application(_,VE,_)): has_if_statement(VE)
  'rule' has_if_statement(case_expr(_,VE,_,_)): has_if_statement(VE)         ------ CHECK CASE-BRANCHES FOR IF-STATEMENTS ------
  'rule' has_if_statement(equivalence(_,Left,Right,_)): (| has_if_statement(Left) || has_if_statement(Right) |)


'type' CONTROLKEY

       var_decl
       init_val
       trans_rel
