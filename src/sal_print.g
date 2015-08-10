'module' sal_print

'use' ast print ext env objects values 
      sal_ast
      pvs_aux
'export' 
 
      Print_Namespace_Stack
      Print_Namespace
      Print_Namespace_Elem
      Print_Fixed_Point
      SAL_Print_Vid
      SAL_Print_IdOp
      SAL_Print_Decl
      SAL_Print_Vids
      SAL_Print_Tids
      SAL_Print_Tid
      SAL_Print_Contexts
      SAL_Print_Cid
      SAL_Print_Context
      SAL_Print_Formal_Params

      SAL_Print_Declareds_s
      SAL_Print_Declareds
      SAL_Print_Sorted

      SAL_Print_Constants
      SAL_Print_Constant
      SAL_Print_Expr
      SAL_Print_Reconstructors

'action' SAL_Print_Reconstructors(SAL_RECONSTRUCTORS)

  'rule' SAL_Print_Reconstructors(list(H, T)):
	 where(H -> sal_reconstructor(Id, _, _, _, _))
	 SAL_Print_IdOp(Id)
	 Putnl()
	 SAL_Print_Reconstructors(T)

  'rule' SAL_Print_Reconstructors(nil):

'action' SAL_Print_Constants(SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Print_Constants(list(C, CS))
	 SAL_Print_Constant(C)
	 [|
	    ne(CS, nil)
	    Putnl()
	    Putnl()
	    SAL_Print_Constants(CS)
	 |]

  'rule' SAL_Print_Constants(nil)

'action' SAL_Print_Constant(SAL_CONTEXT_CONSTANT)
  
  'rule' SAL_Print_Constant(sal_type_decl(Id, Tid, Typ))
	 Putmsg("Type declaration: ")
	 SAL_Print_Tid(Tid)
--print(Tid)
--print(Typ)
	 Putnl()

  'rule' SAL_Print_Constant(sal_object_decl(Id, _, _, _, _))
	 Putmsg("Object declaration: ")
	 Print_id(Id)
	 Putnl()

  'rule' SAL_Print_Constant(sal_const_decl(Decl))
	 Putmsg("Constant declaration: ")
	 SAL_Print_Constant_Decl(Decl)

  'rule' SAL_Print_Constant(assertion_decl(P, Id, Mod, Body))
	 Putmsg("Assertion: ")
	 SAL_Print_Expr(Body)

  'rule' SAL_Print_Constant(module_decl(Id, _, _, _, _, _))
	 Putmsg("Module declaration: ")
	 Print_id(Id)

  'rule' SAL_Print_Constant(T)
	 Putmsg("Debugging predicate activated in SAL_Print_Constant\n")
	 print(T)

'action' SAL_Print_Constant_Decl(SAL_CONSTANT_DECL)

  'rule' SAL_Print_Constant_Decl(sal_expl_const(_, Vid,_, Def))
	 SAL_Print_Vid(Vid)
	 Putmsg(": ")
	 SAL_Print_Expr(Def)
	 Putnl()

  'rule' SAL_Print_Constant_Decl(sal_fun_const(_, Vid,_,Params, ResultType,_, Body, _))
	 SAL_Print_Vid(Vid)
	 Putmsg("(")
	 SAL_Print_Params(Params)
	 Putmsg(") =\n")
	 SAL_Print_Expr(Body)
	 Putnl()

  'rule' SAL_Print_Constant_Decl(T)

'action' SAL_Print_Params(SAL_FORMAL_FUN_PARAMETERS)

  'rule' SAL_Print_Params(list(Param, Rest))
	 SAL_Print_Param(Param)
	 [|
	    ne(Rest, nil)
	    Putmsg(", ")	 
	    SAL_Print_Params(Rest)
	 |]

  'rule' SAL_Print_Params(nil)

'action' SAL_Print_Param(SAL_FORMAL_FUN_PARAMETER)

  'rule' SAL_Print_Param(formal_param(Id,_,_))
	 Print_id(Id)

'action' SAL_Print_Expr(SAL_VALUE_EXPR)

  'rule' SAL_Print_Expr(unit)

  'rule' SAL_Print_Expr(sal_literal(VL))
	 SAL_Print_Value_Literal(VL)

  'rule' SAL_Print_Expr(sal_resolved_literal(VL, _))
	 SAL_Print_Value_Literal(VL)

  'rule' SAL_Print_Expr(sal_product(VEs))
	 Putmsg("(")
	 SAL_Print_Value_Exprs(VEs)
	 Putmsg(")")

  'rule' SAL_Print_Expr(sal_ranged_set(LE,RE,T))
	 Putmsg("{|")
	 SAL_Print_Expr(LE)
	 Putmsg("..")
	 SAL_Print_Expr(RE)
	 Putmsg("|}")

  'rule' SAL_Print_Expr(sal_ranged_cc_set(Id, _, _, Restriction, T))
	 Putmsg("{|")
	 Print_id(Id)
	 Putmsg(" :- ")
	 SAL_Print_Expr(Restriction)
	 Putmsg("|}")

  'rule' SAL_Print_Expr(sal_enum_set(_,_, VEs))
	 Putmsg("{|")
	 SAL_Print_Value_Exprs(VEs)
	 Putmsg("|}")

  'rule' SAL_Print_Expr(sal_comp_simp_set(_,_))
	 Putmsg("COMP SIMPLE SET ")

  'rule' SAL_Print_Expr(sal_comp_set(_,_,_,_))
	 Putmsg("COMP SET ")

  'rule' SAL_Print_Expr(sal_enum_map(_,_,_,_))
	 Putmsg("ENUM MAP ")

  'rule' SAL_Print_Expr(sal_comp_rng_map(_,_,_,_,_))
	 Putmsg("SAL COMPREHENDED RNG MAP ")

  'rule' SAL_Print_Expr(sal_comp_map(_,_,_,_))
	 Putmsg("SAL COMPREHENDED MAP ")

  'rule' SAL_Print_Expr(sal_funct_applic(Fun, Args))
	 SAL_Print_Expr(Fun)
	 Putmsg("(")
	 SAL_Print_Args(Args)
	 Putmsg(")")

  'rule' SAL_Print_Expr(sal_destr_applic(Name, Field))
	 SAL_Print_Expr(Name)
	 Putmsg(".")
	 SAL_Print_Expr(Field)

  'rule' SAL_Print_Expr(sal_quantified(_,_,_))
	 Putmsg("SAL QUANTIFIED ")

  'rule' SAL_Print_Expr(sal_bracket(VE))
	 Putmsg("(")
	 SAL_Print_Expr(VE)
	 Putmsg(")")

  'rule' SAL_Print_Expr(sal_funct_expr(Op,_, LE, RE))
	 SAL_Print_Expr(LE)
	 SAL_Print_Value_Id(Op)
	 SAL_Print_Expr(RE)

  'rule' SAL_Print_Expr(sal_ax_infix(LE, LogicConn, RE))
	 SAL_Print_Expr(LE)
	 SAL_Print_Logic_Connective(LogicConn)
	 SAL_Print_Expr(RE)

  'rule' SAL_Print_Expr(sal_ax_prefix(LogicConn, RE))
	 SAL_Print_Logic_Connective(LogicConn)
	 SAL_Print_Expr(RE)

  'rule' SAL_Print_Expr(sal_let_expr(Id, _, _, _, Init, Body))
	 Putmsg("LET ")
	 Print_id(Id)
	 Putmsg(" = ")
	 SAL_Print_Expr(Init)
	 Putmsg(" IN ")
	 SAL_Print_Expr(Body)

  'rule' SAL_Print_Expr(sal_esp_let_expr(_, _,_,_))
	 Putmsg("ESPECIAL LET EXPRESSION ")

  'rule' SAL_Print_Expr(sal_if_expr(Condition, Then, Elsifs, Else))
	 Putmsg("IF ")
	 SAL_Print_Expr(Condition)
	 Putmsg(" THEN ")
	 SAL_Print_Expr(Then)
	 SAL_Print_Elsifs(Elsifs)
	 [|
	     where(Else -> else(ElseExpr))
	     Putmsg(" ELSE ")
	     SAL_Print_Expr(ElseExpr)
	 |]
	 Putmsg(" ENDIF")
	 
  'rule' SAL_Print_Expr(sal_value_occ(ValId, _))
	 SAL_Print_Value_Id(ValId)

  'rule' SAL_Print_Expr(sal_esp_value_occ(Vid))
	 SAL_Print_Vid(Vid)

  'rule' SAL_Print_Expr(sal_recogniser(Vid, Args))
	 SAL_Print_Vid(Vid)
	 Putmsg("?(")
	 SAL_Print_Args(Args) 
	 Putmsg(")")

  'rule' SAL_Print_Expr(sal_infix_occ(LE, IdOp, RE))
	 SAL_Print_Expr(LE)
	 Putmsg(" ")
	 SAL_Print_Value_Id(IdOp)
	 Putmsg(" ")
	 SAL_Print_Expr(RE)

  'rule' SAL_Print_Expr(sal_esp_prefix_occ(IdOp, LE, RE))
	 SAL_Print_Value_Id(IdOp)
	 Putmsg("(")
	 SAL_Print_Expr(LE)
	 Putmsg(", ")	 
	 SAL_Print_Expr(RE)
	 Putmsg(")")

  'rule' SAL_Print_Expr(sal_esp_unary_prefix_occ(IdOp, LE))
	 SAL_Print_Value_Id(IdOp)
	 Putmsg("(")
	 SAL_Print_Expr(LE)
	 Putmsg(")")

  'rule' SAL_Print_Expr(sal_esp_ternary_occ(IdOp, E1, E2, E3))
	 SAL_Print_Value_Id(IdOp)
	 Putmsg("(")
	 SAL_Print_Expr(E1)
	 Putmsg(", ")	 
	 SAL_Print_Expr(E2)
	 Putmsg(", ")	 
	 SAL_Print_Expr(E3)
	 Putmsg(")")

  'rule' SAL_Print_Expr(sal_prefix_occ(IdOp, _, RE))
	 SAL_Print_Value_Id(IdOp)
	 Putmsg(" ")
	 SAL_Print_Expr(RE)

  'rule' SAL_Print_Expr(sal_assignment(Id, RE)):
	 Print_id(Id)
	 Putmsg(" := ")
	 SAL_Print_Expr(RE)

  'rule' SAL_Print_Expr(sal_var_occ(_, VId)):
	 VId'Ident -> Id
	 Print_id(Id)

  'rule' SAL_Print_Expr(stop)

  'rule' SAL_Print_Expr(not_supported)

  'rule' SAL_Print_Expr(no_val)

  'rule' SAL_Print_Expr(nil)

  'rule' SAL_Print_Expr(X)
print(X)

'action' SAL_Print_Value_Id(SAL_VALUE_ID)

  'rule' SAL_Print_Value_Id(val_id(IdOp))
	 SAL_Print_Id_Op(IdOp)

  'rule' SAL_Print_Value_Id(record_val_id(_,IdOp, Index))
	 SAL_Print_Id_Op(IdOp)
	 Putmsg(".")
	 Int_to_string(Index -> IndexStr)
	 Putmsg(IndexStr)

  'rule' SAL_Print_Value_Id(complex_val_id(_,_,_))
	 Putmsg("COMPLEX VALUE ID ")

'action' SAL_Print_Args(SAL_ARGS)

  'rule' SAL_Print_Args(sal_argument(VEs))
	 SAL_Print_Value_Exprs(VEs)

'action' SAL_Print_Value_Exprs(SAL_VALUE_EXPRS)

  'rule' SAL_Print_Value_Exprs(list(VE, Rest))
	 SAL_Print_Expr(VE)
	 [|
	     ne(Rest, nil)
	     Putmsg(", ")
	     SAL_Print_Value_Exprs(Rest)
	 |]

  'rule' SAL_Print_Value_Exprs(nil)

'action' SAL_Print_Elsifs(SAL_ELSIF_BRANCHES)

  'rule' SAL_Print_Elsifs(list(Elsif, Rest))
	 SAL_Print_Elsif(Elsif)
	 SAL_Print_Elsifs(Rest)

  'rule' SAL_Print_Elsifs(nil)

'action' SAL_Print_Elsif(SAL_ELSIF_BRANCH)

  'rule' SAL_Print_Elsif(elsif(Cond, Then))
	 Putmsg("ELSIF (")
	 SAL_Print_Expr(Cond)
	 Putmsg(") THEN ")
	 SAL_Print_Expr(Then)

  'rule' SAL_Print_Elsif(nil)

'action' SAL_Print_Logic_Connective(SAL_LOGIC_CONNECTIVE)

  'rule' SAL_Print_Logic_Connective(implies)
	 Putmsg(" IMPLIES ")

  'rule' SAL_Print_Logic_Connective(or)
	 Putmsg(" OR ")

  'rule' SAL_Print_Logic_Connective(and)
	 Putmsg(" AND ")

  'rule' SAL_Print_Logic_Connective(not)
	 Putmsg(" NOT ")

'action' SAL_Print_Id_Op(SAL_ID_OP)

  'rule' SAL_Print_Id_Op(id(Id))
	 Print_id(Id)

  'rule' SAL_Print_Id_Op(sal_op_symb(Op))
	 SAL_Print_Op(Op)

  'rule' SAL_Print_Id_Op(sal_int_op(Op, Tid))
	 Tid'Cid -> cid(Cid)
	 Cid'Ident -> Id
	 Print_id(Id)
	 Putmsg("!")
	 SAL_Print_Op(Op)

  'rule' SAL_Print_Id_Op(sal_cc_op(Op, Tid))
	 Tid'Cid -> cid(Cid)
	 Cid'Ident -> Id
	 Print_id(Id)
	 Putmsg("!")
	 SAL_Print_Op(Op)

  'rule' SAL_Print_Id_Op(sal_set_op(Op, _, Tid))
	 Tid'Cid -> cid(Cid)
	 Cid'Ident -> Id
	 Print_id(Id)
	 Putmsg("!")
	 SAL_Print_Op(Op)

  'rule' SAL_Print_Id_Op(sal_map_op(Op, _,_,Tid))
	 Tid'Cid -> cid(Cid)
	 Cid'Ident -> Id
	 Print_id(Id)
	 Putmsg("!")
	 SAL_Print_Op(Op)

'action' SAL_Print_Op(SAL_OP)

  'rule' SAL_Print_Op(sal_infix_op(eq))
	 Putmsg(" = ")

  'rule' SAL_Print_Op(sal_infix_op(neq))
	 Putmsg(" /= ")

  'rule' SAL_Print_Op(sal_infix_op(gt))
	 Putmsg(" > ")

  'rule' SAL_Print_Op(sal_infix_op(lt))
	 Putmsg(" < ")

  'rule' SAL_Print_Op(sal_infix_op(ge))
	 Putmsg(" >= ")

  'rule' SAL_Print_Op(sal_infix_op(le))
	 Putmsg(" <= ")

  'rule' SAL_Print_Op(sal_infix_op(mult))
	 Putmsg(" * ")

  'rule' SAL_Print_Op(sal_infix_op(div))
	 Putmsg(" \ ")

  'rule' SAL_Print_Op(sal_infix_op(plus))
	 Putmsg(" + ")

  'rule' SAL_Print_Op(sal_infix_op(minus))
	 Putmsg(" - ")

  'rule' SAL_Print_Op(sal_infix_op(int_div))
	 Putmsg(" \ ")

  'rule' SAL_Print_Op(sal_infix_op(and))
	 Putmsg(" AND ")

  'rule' SAL_Print_Op(sal_infix_op(implies))
	 Putmsg(" IMPLIES ")

  'rule' SAL_Print_Op(sal_infix_op(or))
	 Putmsg(" OR ")

  'rule' SAL_Print_Op(sal_prefix_op(minus))
	 Putmsg("-")

  'rule' SAL_Print_Op(sal_prefix_op(not))
	 Putmsg("NOT ")

  'rule' SAL_Print_Op(sal_prefix_op(g))
	 Putmsg("G")

  'rule' SAL_Print_Op(sal_prefix_op(f))
	 Putmsg("F")

  'rule' SAL_Print_Op(sal_prefix_op(x))
	 Putmsg("X")

  'rule' SAL_Print_Op(sal_function_op(supset))
	 Putmsg("supset")

  'rule' SAL_Print_Op(sal_function_op(subset))
	 Putmsg("subset")

  'rule' SAL_Print_Op(sal_function_op(supseteq))
	 Putmsg("supseteq")

  'rule' SAL_Print_Op(sal_function_op(subseteq))
	 Putmsg("subseteq")

  'rule' SAL_Print_Op(sal_function_op(isin))
	 Putmsg("isin")

  'rule' SAL_Print_Op(sal_function_op(notisin))
	 Putmsg("~isin")

  'rule' SAL_Print_Op(sal_function_op(rem))
	 Putmsg("rem")

  'rule' SAL_Print_Op(sal_function_op(difference))
	 Putmsg("difference")

  'rule' SAL_Print_Op(sal_function_op(restriction_by))
	 Putmsg("restriction_by")

  'rule' SAL_Print_Op(sal_function_op(restriction_to))
	 Putmsg("restriction_to")

  'rule' SAL_Print_Op(sal_function_op(caret))
	 Putmsg("caret")

  'rule' SAL_Print_Op(sal_function_op(union))
	 Putmsg("union")

  'rule' SAL_Print_Op(sal_function_op(override))
	 Putmsg("override")

  'rule' SAL_Print_Op(sal_function_op(hash))
	 Putmsg("hash")

  'rule' SAL_Print_Op(sal_function_op(inter))
	 Putmsg("inter")

  'rule' SAL_Print_Op(sal_function_op(inds))
	 Putmsg("inds")

  'rule' SAL_Print_Op(sal_function_op(elems))
	 Putmsg("elems")

  'rule' SAL_Print_Op(sal_function_op(dom))
	 Putmsg("dom")

  'rule' SAL_Print_Op(sal_function_op(rng))
	 Putmsg("rng")

  'rule' SAL_Print_Op(sal_function_op(hd_set))
	 Putmsg("hd_set")

  'rule' SAL_Print_Op(sal_function_op(hd_map))
	 Putmsg("hd_map")

  'rule' SAL_Print_Op(sal_function_op(add_set))
	 Putmsg("add_set")

  'rule' SAL_Print_Op(sal_function_op(add_map))
	 Putmsg("add_map")

  'rule' SAL_Print_Op(sal_function_op())
	 Putmsg("")

  'rule' SAL_Print_Op(sal_function_op(is_true))
	 Putmsg("is_true")

'action' SAL_Print_Value_Literal(SAL_VALUE_LITERAL)

  'rule' SAL_Print_Value_Literal(bool_true)
	 Putmsg("TRUE")

  'rule' SAL_Print_Value_Literal(bool_false)
	 Putmsg("FALSE")

  'rule' SAL_Print_Value_Literal(integ(Id))
	 Print_id(Id)

  'rule' SAL_Print_Value_Literal(nil)

-------------------------------

'action' Print_Namespace_Stack(BINDING_NAMESPACE_STACK)

  'rule' Print_Namespace_Stack(list(NS, Rest))
	 Print_Namespace(NS)
	 [|
	    ne(Rest,nil)
	    Print_Namespace_Stack(Rest)
	 |]

'action' Print_Namespace_Elem(BINDING_ELEM)

  'rule' Print_Namespace_Elem(binding_elem(Index, IdOp, Name))
	 Putmsg("Indice: ")
	 Int_to_string(Index -> Str)
	 Putmsg(Str)
	 Putmsg(" asignado al valor ")
	 (|
	    where(Name -> id_op(IdOp1))
	    where(IdOp1 -> id(Ident1))
	    Print_id(Ident1)
	 ||
	    Putmsg(" nil")
	 |)
	 Putmsg(" del nombre ")
	 where(IdOp -> id(Ident))
	 Print_id(Ident)
	 Putnl()

'rule' Print_Namespace_Elem(nested_elem(Index, Name, BElem))
	 Putmsg("Indice: ")
	 Int_to_string(Index -> Str)
	 Putmsg(Str)
	 Putmsg(" asignado al valor ")
	 (|
	    where(Name -> id_op(IdOp1))
	    where(IdOp1 -> id(Ident1))
	    Print_id(Ident1)
	 ||
	    Putmsg(" nil")
	 |)
	 Putmsg(" del elemento\n    ")
	 Print_Namespace_Elem(BElem)

'action' Print_Namespace(BINDING_NAMESPACE)

  'rule' Print_Namespace(list(NamespaceElem, Rest))
	 Print_Namespace_Elem(NamespaceElem)
	 Print_Namespace(Rest)

  'rule' Print_Namespace(nil)

-----------------------------
'action' Print_Fixed_Point(SAL_CONTEXT_CONSTANTS)

  'rule' Print_Fixed_Point(list(D1, Rest))
	 SAL_Print_Decl(D1)
	 Putnl()
	 Print_Fixed_Point(Rest)

  'rule' Print_Fixed_Point(nil)

'action' Print_Macros(MACRO_CONSTANTS)

  'rule' Print_Macros(list(M, MS))
	 Print_Macro(M)
	 Putnl()
	 Print_Macros(MS)

  'rule' Print_Macros(nil):

'action' Print_Macro(MACRO_CONSTANT)

  'rule' Print_Macro(macro_set_cmd(Tid, _))
	 Putmsg("Set ")
	 Tid'Ident -> Id
	 Print_id(Id)

  'rule' Print_Macro(macro_map_cmd(Tid, _, _, _, _, _))
	 Putmsg("Map ")
	 Tid'Ident -> Id
	 Print_id(Id)

  'rule' Print_Macro(macro_int_cmd(Tid))
	 Putmsg("Int ")
	 Tid'Ident -> Id
	 Print_id(Id)

  'rule' Print_Macro(macro_cc_set_cmd(Tid, _, _))
	 Putmsg("CC set ")
	 Tid'Ident -> Id
	 Print_id(Id)

  'rule' Print_Macro(macro_cc_map_cmd(Tid, _, _, _, _, _, _, _, _, _, _))
	 Putmsg("CC map ")
	 Tid'Ident -> Id
	 Print_id(Id)

  'rule' Print_Macro(macro_int_cc_cmd(Tid,_,_))
	 Putmsg("Int CC type ")
	 Tid'Ident -> Id
	 Print_id(Id)

  'rule' Print_Macro(macro_bool_cc_cmd(Tid))
	 Putmsg("Bool CC type ")
	 Tid'Ident -> Id
	 Print_id(Id)

  'rule' Print_Macro(macro_type_cc_cmd(Tid))
	 Putmsg("CC type ")
	 Tid'Ident -> Id
	 Print_id(Id)

-- 
'action' SAL_Print_Vid(SAL_value_id)

  'rule' SAL_Print_Vid(Vid)
--	 Vid'Pos -> P
--	 PrintPos(P)
	 Vid'Cid -> cid(Cid)
	 Cid'Ident -> CidId
	 Print_id(CidId)
	 Putmsg("!")
	 Vid'IdOp -> IdOp
	 where(IdOp -> id(Ident))
	 Print_id(Ident)
------
'action' SAL_Print_IdOp(SAL_ID_OP)

  'rule' SAL_Print_IdOp(id(Ident))
	 Print_id(Ident)

  'rule' SAL_Print_IdOp(P)
	 print(P)
------
'action' SAL_Print_Decl(SAL_CONTEXT_CONSTANT)

  'rule' SAL_Print_Decl(sal_const_decl(sal_nodef(IdOp,_,_)))
	 SAL_Print_IdOp(IdOp)

  'rule' SAL_Print_Decl(sal_const_decl(sal_expl_const(IdOp,_,_,_)))
	 Putmsg("Declaration of constant: ")
	 SAL_Print_IdOp(IdOp)
	 Putnl()

  'rule' SAL_Print_Decl(sal_const_decl(sal_fun_const(IdOp,_,_,_,_,_,_,_)))
	 Putmsg("Declaration of function: ")
	 SAL_Print_IdOp(IdOp)
	 Putnl()
  
  'rule' SAL_Print_Decl(sal_const_decl(sal_param_decl(_,_)))
	 Putmsg("Declaracion de params")

  'rule' SAL_Print_Decl(sal_const_decl(nil))
	 Putmsg("Nil constant declaration")
 
  'rule' SAL_Print_Decl(sal_type_decl(Id, Tid, TExpr))
	 Putmsg("Declaration of type: ")
	 Print_id(Id)
	 Putnl()
--print(TExpr)

  'rule' SAL_Print_Decl(sal_object_decl(Id, _, _, _, _))
	 Putmsg("Declaration of object: ")
	 Print_id(Id)
	 Putnl()

  'rule' SAL_Print_Decl(module_decl(Id, _, _, _, _, _))
	 Putmsg("Declaration of module: ")
	 Print_id(Id)
	 Putnl()

  'rule' SAL_Print_Decl(assertion_decl(_, Id, _, _))
	 Putmsg("Declaration of assertion: ")
	 Print_id(Id)
	 Putnl()

  'rule' SAL_Print_Decl(nil)
	 Putmsg("nil")

  'rule' SAL_Print_Decl(D)
	 print(D)

------------

'action' SAL_Print_Vids(SAL_VALUE_IDS)

  'rule' SAL_Print_Vids(list(H,T))
	 SAL_Print_Vid(H)
	 Putnl()
	 SAL_Print_Vids(T)

  'rule' SAL_Print_Vids(nil)
-------------
'action' SAL_Print_Tids(SAL_TYPE_IDS)

  'rule' SAL_Print_Tids(list(H,T))
	 SAL_Print_Tid(H)
	 Putnl()
	 SAL_Print_Tids(T)

  'rule' SAL_Print_Tids(nil)
-------------
'action' SAL_Print_Tid(SAL_type_id)

  'rule' SAL_Print_Tid(Tid)
--	 Putmsg("Tid: ")
	 [|
	   Tid'Cid -> cid(Cid)
	   Cid'Ident -> CidId
	   Print_id(CidId)
	   Putmsg("!")
	 |]
	 Tid'Ident -> Ident
	 Print_id(Ident)
--	 Putmsg(" at pos: ")
--	 Tid'Pos -> P
--	 PrintPos(P)
--[|
--	 Tid'Declaration -> Decl
--	 ne(Decl, nil)
--	 Putmsg(": ")
--	 SAL_Print_Decl(Decl)
--|]
--------------
'action' SAL_Print_Contexts(SAL_CONTEXTS)

  'rule' SAL_Print_Contexts(list(H,T))
	 where(H -> context(Ident,Cid,CC))
	 Putmsg("Context: ")
	 Print_id(Ident)
	 Putnl()
	 Print_Fixed_Point(CC)
	 SAL_Print_Contexts(T)

  'rule' SAL_Print_Contexts(list(H,T))
	 where(H -> macro_context(Ident,Cid,MC))
	 Putmsg("Macro context: ")
	 Print_id(Ident)
	 Putnl()
	 Print_Macros(MC)
	 SAL_Print_Contexts(T)
 
  'rule' SAL_Print_Contexts(nil)
---------------
'action' SAL_Print_Opt_Cid(OPT_CONTEXT_ID)

  'rule' SAL_Print_Opt_Cid(nil):
  	 Putmsg("nil")

  'rule' SAL_Print_Opt_Cid(cid(Cid)):
  	 SAL_Print_Cid(Cid)

---------------
'action' SAL_Print_Cid(SAL_context_id)

  'rule' SAL_Print_Cid(Cid)
	 Cid'Ident -> Ident
	 Print_id(Ident)

-----------------
'action' SAL_Print_Context(SAL_CONTEXT)

  'rule' SAL_Print_Context(context(Id,_,Elems))
	 Putmsg("Imprimiendo contenido del contexto: ")
	 Print_id(Id)
	 Putnl()
	 Print_Fixed_Point(Elems)
------------------
'action' SAL_Print_Formal_Params(SAL_FORMAL_FUN_PARAMETERS)

  'rule' SAL_Print_Formal_Params(list(Param, Rest))
	 where(Param -> formal_param(ID,_,RSLT))
	 Print_id(ID)
	 Putmsg(" of type: ")
	 Print_type(RSLT)
	 Putnl()
	 SAL_Print_Formal_Params(Rest)

  'rule' SAL_Print_Formal_Params(nil)

--------------------
'action' SAL_Print_Declareds_s(SORTED_DECLS_S)

  'rule' SAL_Print_Declareds_s(list(Declareds, Declareds_sTail)):
	 SAL_Print_Declareds(Declareds)
	 SAL_Print_Declareds_s(Declareds_sTail)

  'rule' SAL_Print_Declareds_s(nil):


'action' SAL_Print_Declareds(SORTED_DECLS)

  'rule' SAL_Print_Declareds(list(Declared, DeclaredsTail)):
	 SAL_Print_Sorted(Declared)
	 [|
	   ne(DeclaredsTail, nil)
	   Putmsg(", ")
	   SAL_Print_Declareds(DeclaredsTail)
         |]

	 -- no more Declareds
  'rule' SAL_Print_Declareds(nil):
	 Putnl()



--------------------------------------------------
'action' SAL_Print_Sorted(SORTED_DECL_ITEM)

  'rule' SAL_Print_Sorted(type_item(Typeid)):
	 Putmsg("type ")
	 Typeid'Ident -> Id
	 Print_id(Id)
--	 Print_Type_id(Typeid, "type_item in DECLARED")

  'rule' SAL_Print_Sorted(value_item(Valueid)):
	 Putmsg("value ")
	 Valueid'Ident -> Id
	 Print_id_or_op(Id)
	 Putnl()
--print(Id)
--	 Print_Value_id(Valueid, "value_item in DECLARED")

  'rule' SAL_Print_Sorted(axiom_item(Axiomid)):
	 Putmsg("axiom")
--	 Putmsg(" axiom_item in DECLARED")
--	 Putnl()
--[|
--  Axiomid'Ident -> ident(Id)
--  Putmsg("[")
--  Print_id(Id)
--  Putmsg("]\n")
--|]
--Axiomid'Axiom -> A
--Print_expr(A)
--Putnl()

  'rule' SAL_Print_Sorted(lemma_item(AxiomDefs)):
	 Print_Axiom_id(AxiomDefs, " lemma_item in DECLARED")

  'rule' SAL_Print_Sorted(rec_fun_item(Valueid)):
	 Print_Value_id(Valueid, "rec_fun_item in DECLARED")

  'rule' SAL_Print_Sorted(mut_rec_fun_item(Valueid)):
	 Print_Value_id(Valueid, "mut_rec_fun_item in DECLARED")

  'rule' SAL_Print_Sorted(rec_item(Declareds)):
	 Putmsg("---- BEGIN rec_item in DECLARED ----")
	 Putnl()
	 SAL_Print_Declareds(Declareds)
	 Putmsg("----  END rec_item in DECLARED  ----")
	 Putnl()

  'rule' SAL_Print_Sorted(prop_item(Pid))
	 Putmsg("Property: ")
	 Pid'Ident -> Ident
	 Print_id(Ident)
	 Putnl()

  'rule' SAL_Print_Sorted(ts_item(TSid))
	 Putmsg("Transition system: ")
	 TSid'Ident -> Ident
	 Print_id(Ident)
	 Putnl()

  'rule' SAL_Print_Sorted(mark_item(String)):
	 Putmsg("mark_item in DECLARED")
	 Putnl()
	 Putmsg(String)
	 Putnl()

  'rule' SAL_Print_Sorted(nil):
	 Putmsg("nil in DECLARED")
	 Putnl()

  'rule' SAL_Print_Sorted(object_item(_,_,_,_))
	 
