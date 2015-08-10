-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the unparser for C++

'module' c_unparse

'use' ast print ext env objects values types pp cc c_ast c_decl

'export'

	C_Expr_to_string
	C_Type_to_string
	C_Decl_to_string	C_Decls_to_string
	C_Decl_to_string_h	C_Decls_to_string_h
	C_Decl_to_string_cc	C_Decls_to_string_cc
	C_Op_to_string		C_Statements_to_string

	CPP_Statement_to_string Qualifier_to_string

	Append_decl Concatenate_decls C_Name_to_string

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

'action' C_Exprs_to_string(C_EXPRS -> STRING)

  'rule' C_Exprs_to_string(list(E, Es) -> S):
	 C_Expr_to_string(E -> S1)
	 (|
	   eq(Es, nil)
	   where(S1 -> S)
	 ||
	   C_Exprs_to_string(Es -> S2)
	   Concatenate3(S1, ", ", S2 -> S)
	 |)

  'rule' C_Exprs_to_string(nil -> "")

'action' C_Expr_to_string(C_EXPR -> STRING)

  'rule' C_Expr_to_string(nil -> ""):

  'rule' C_Expr_to_string(multiple(Es) -> S):
	 C_Exprs_to_string(Es -> S)

  'rule' C_Expr_to_string(literal(text(Txt)) -> S):
	 Text_to_c_string(Txt -> S1)
	 Concatenate3("RSL_string(", S1, ")" -> S)

  'rule' C_Expr_to_string(literal(char(C)) -> S):
         Char_to_string(C -> S1)
	 Concatenate3("RSL_char(", S1, ")" -> S)

  'rule' C_Expr_to_string(literal(int(Id)) -> S)
	 -- C++ interprets an integer in exponent form as a double
	 -- so need to cast to integer
	 id_to_string(Id -> S0)
	 (|
	   Contains_E(S0)
	   Concatenate("(int)", S0 -> S)
	 ||
	   where(S0 -> S)
         |)

  'rule' C_Expr_to_string(literal(unit) -> ""):
	 
  'rule' C_Expr_to_string(literal(Expr) -> S):
	 Literal_to_string(Expr -> S)

  'rule' C_Expr_to_string(text_literal(Txt) -> S):
	 Text_to_c_string(Txt -> S)

  'rule' C_Expr_to_string(this -> "this"):

  'rule' C_Expr_to_string(bracket(Expr) -> S):
	 (| -- don't bracket twice
	   where(Expr -> bracket(E))
	   C_Expr_to_string(Expr -> S)
	 ||
	   C_Expr_to_string(Expr -> S1)
	   Concatenate3("(", S1, ")" -> S)
	 |)

  'rule' C_Expr_to_string(name(N) -> S):
	 C_Name_to_string(N -> S)

  'rule' C_Expr_to_string(unary(Op, Expr) -> S):
	 C_Expr_to_string(Expr -> S2)
	 C_Op_to_string(Op -> S1)
	 Concatenate(S1, S2 -> S)

  'rule' C_Expr_to_string(binary(Expr1, literal(S0), Expr2) -> S):
	 C_Expr_to_string(Expr1 -> S1)
	 C_Expr_to_string(Expr2 -> S2)
	 Concatenate3(S0, "(", S1 -> S01)
	 Concatenate3(S01, ", ", S2 -> S12)
	 Concatenate(S12, ")" -> S)
	 

  'rule' C_Expr_to_string(binary(Expr1, Op, Expr2) -> S):
	 C_Expr_to_string(Expr1 -> S1)
	 C_Expr_to_string(Expr2 -> S3)
	 C_Op_to_string(Op -> S2)
	 Concatenate3(S1, " ", S2 -> S4)
	 Concatenate3(S4, " ", S3 -> S)

  'rule' C_Expr_to_string(conditional(Expr1, Expr2, Expr3) -> S):
	 (|  -- don't bracket twice
	   where(Expr1 -> bracket(E))
	   C_Expr_to_string(conditional(E, Expr2, Expr3) -> S)
	 ||
	   C_Expr_to_string(bracket(Expr1) -> S1)
	   C_Expr_to_string(Expr2 -> S2)
	   C_Expr_to_string(Expr3 -> S3)
	   Concatenate3(S1, " ? ", S2 -> S4)
	   Concatenate3(S4, " : ", S3 -> S)
	 |)

  'rule' C_Expr_to_string(pm(Expr1, PtrOp, Expr2) -> S):
	 C_Expr_to_string(Expr1 -> S1)
	 C_Expr_to_string(Expr2 -> S2)
	 C_Op_to_string(PtrOp -> S3)
	 Concatenate3(S1, S3, S2 -> S)

  'rule' C_Expr_to_string(cast(Tid, Expr) -> S):
	 C_id_to_string(Tid -> S1)
	 C_Expr_to_string(Expr -> S2)
	 Concatenate3("(", S1, ")" -> S3)
	 Concatenate(S3, S2 -> S)

  'rule' C_Expr_to_string(ptr_cast(Tid, Expr) -> S):
	 C_id_to_string(Tid -> S1)
	 C_Expr_to_string(Expr -> S2)
	 Concatenate3("(", S1, "*)" -> S3)
	 Concatenate(S3, S2 -> S)

  'rule' C_Expr_to_string(postfix(Expr, Suffix) -> S):
	 C_Expr_to_string(Expr -> S1)
	 C_Postfix_to_string(Suffix -> S2)
	 Concatenate(S1, S2 -> S)

  'rule' C_Expr_to_string(statements(Ss) -> S):
	 C_Statements_to_string(Ss -> S)

  'rule' C_Expr_to_string(with_statements(E, Ss) -> S):
	 C_Statements_to_string(Ss -> S1)
	 C_Expr_to_string(E -> S2)
	 Concatenate(S1, S2 -> S)

  'rule' C_Expr_to_string(E -> "/*TODO: expression unparser*/"):
	 Putmsg("[TODO: expression unparser]\n")
	 print(E)
	 
'action' C_Postfix_to_string(C_POSTFIX -> STRING)

  'rule' C_Postfix_to_string(inc -> "++")
  'rule' C_Postfix_to_string(dec -> "--")

  'rule' C_Postfix_to_string(arrow(Name) -> S):
	 C_Name_to_string(Name -> S1)
	 Concatenate("->", S1 -> S)

  'rule' C_Postfix_to_string(dot(Name) -> S):
	 C_Name_to_string(Name -> S1)
	 Concatenate(".", S1 -> S)

  'rule' C_Postfix_to_string(bracket(Exprs) -> S):
	 (| -- don't bracket arg twice
	   where(Exprs -> list(bracket(E),nil))
	   C_Postfix_to_string(bracket(list(E,nil)) -> S)
	 ||
	   C_Exprs_to_string(Exprs -> S1)
	   Concatenate3("(", S1, ")" -> S)
	 |)

  'rule' C_Postfix_to_string(index(Expr) -> S):
	 C_Expr_to_string(Expr -> S1)
	 Concatenate3("[", S1, "]" -> S)


'action' C_Name_to_string(C_NAME -> STRING)

  'rule' C_Name_to_string(id(I) -> S):
	 C_id_to_string(I -> S)

  'rule' C_Name_to_string(local_id(P, I) -> S):
	 C_id_to_string(I -> S1)
	 Pos_to_string(P -> S2)
	 Concatenate3(S1, "_", S2 -> S)

  'rule' C_Name_to_string(op_fun(Op) -> S):
	 C_Op_to_string(Op -> S1)
	 Concatenate("operator", S1 -> S)

  'rule' C_Name_to_string(destr_call(ClassId) -> S):
	 C_id_to_string(ClassId -> S1)
	 Concatenate("~", S1 -> S)

  'rule' C_Name_to_string(conv_fun(Types, Ptr) -> S):
	 C_Types_to_string(Types, space -> S1)
	 C_Ptr_op_to_string(Ptr -> S2)
	 Concatenate3("operator", S1, S2 -> S)

  'rule' C_Name_to_string(qualified(Name, Qual) -> S):
	 Qualifier_to_string(Qual -> S1)
	 C_Name_to_string(Name -> S2)
	 Concatenate3(S1, "::", S2 -> S)

  'rule' C_Name_to_string(template(Id, Ts) -> S):
	 C_id_to_string(Id -> S1)
	 C_Types_to_string(Ts, comma -> S2)
	 Concatenate3(S1, "<", S2 -> S3)
	 Concatenate(S3, ">" -> S)
	 

  'rule' C_Name_to_string(template_member(Id, Ts, Name) -> S):
	 C_Type_to_string(template(Id, Ts) -> S1)
	 C_Name_to_string(Name -> S2)
	 Concatenate3(S1, "::", S2 -> S)
	 

'action' Qualifier_to_string(IDENTS -> STRING)

  'rule' Qualifier_to_string(list(Id, nil) -> S):
	 C_id_to_string(Id -> S)

  'rule' Qualifier_to_string(list(Id, Ids) -> S):
	 C_id_to_string(Id -> S1)
	 Qualifier_to_string(Ids -> S2)
	 Concatenate3(S1, "::", S2 -> S)


'action' C_Op_to_string(C_OP -> STRING)

  'rule' C_Op_to_string(assign -> "=")
  'rule' C_Op_to_string(mult_assign -> "*=")
  'rule' C_Op_to_string(div_assign -> "/=")
  'rule' C_Op_to_string(modulo_assign -> "%=")
  'rule' C_Op_to_string(plus_assign -> "+=")
  'rule' C_Op_to_string(minus_assign -> "-=")
  'rule' C_Op_to_string(shr_assign -> ">>=")
  'rule' C_Op_to_string(shl_assign -> "<<=")
  'rule' C_Op_to_string(and_assign -> "&=")
  'rule' C_Op_to_string(xor_assign -> "^=")
  'rule' C_Op_to_string(or_assign -> "|=")
  'rule' C_Op_to_string(logical_or -> "||")
  'rule' C_Op_to_string(logical_and -> "&&")
  'rule' C_Op_to_string(bitwise_or -> "|")
  'rule' C_Op_to_string(bitwise_xor -> "^")
  'rule' C_Op_to_string(eq -> "==")
  'rule' C_Op_to_string(neq -> "!=")
  'rule' C_Op_to_string(lt -> "<")
  'rule' C_Op_to_string(gt -> ">")
  'rule' C_Op_to_string(le -> "<=")
  'rule' C_Op_to_string(ge -> ">=")
  'rule' C_Op_to_string(shl -> "<<")
  'rule' C_Op_to_string(shr -> ">>")
  'rule' C_Op_to_string(plus -> "+")
  'rule' C_Op_to_string(minus -> "-")
  'rule' C_Op_to_string(mult -> "*")
  'rule' C_Op_to_string(div -> "/")
  'rule' C_Op_to_string(modulo -> "%")
  'rule' C_Op_to_string(not -> "!")
  'rule' C_Op_to_string(tilde -> "~")
  'rule' C_Op_to_string(comma -> ",")
  'rule' C_Op_to_string(new -> "new ")
  'rule' C_Op_to_string(delete -> "delete ")
  'rule' C_Op_to_string(member -> ".")
  'rule' C_Op_to_string(member_ptr -> ".*")
  'rule' C_Op_to_string(indirect_member -> "->")
  'rule' C_Op_to_string(indirect_member_ptr -> "->*")
  'rule' C_Op_to_string(sizeof -> "sizeof")
  'rule' C_Op_to_string(address_of -> "&")
  'rule' C_Op_to_string(deref -> "*")
  'rule' C_Op_to_string(inc -> "++")
  'rule' C_Op_to_string(dec -> "--")
  'rule' C_Op_to_string(literal(S) -> S)

'action' C_Ptr_op_to_string(C_PTR_OP -> STRING)

  'rule' C_Ptr_op_to_string(nil -> "")
  'rule' C_Ptr_op_to_string(ptr -> "*")
  'rule' C_Ptr_op_to_string(ref -> "&")

  'rule' C_Ptr_op_to_string(class_member_ptr(C) -> S):
	 C_Name_to_string(C -> S1)
	 Concatenate(S1, "::*" -> S)

  'rule' C_Ptr_op_to_string(cv_qualified(PtrOp, CVs) -> S):
	 C_Ptr_op_to_string(PtrOp -> S1)
	 C_Cvqs_to_string(CVs -> S2)
	 Concatenate3(S1, " ", S2 -> S)

'action' C_Cvqs_to_string(C_CV_QUALIFIERS -> STRING)

  'rule' C_Cvqs_to_string(list(CV, CVs) -> S):
	 (|
	   eq(CV, const)
	   where(" const" -> S1)
	 ||
	   where(" volatile" -> S1)
	 |)
	 (|
	   eq(CVs, nil)
	   where(S1 -> S)
	 ||
	   C_Cvqs_to_string(CVs -> S2)
	   Concatenate(S1, S2 -> S)
	 |)

  'rule' C_Cvqs_to_string(nil -> "")


-----------------------------------------------------------------------------
-- Declarations
-----------------------------------------------------------------------------

'action' C_Decls_to_string(C_DECLS -> STRING)

  'rule' C_Decls_to_string(list(D, Ds) -> S):
	 C_Decl_to_string(D -> S1)
	 C_Decls_to_string(Ds -> S2)
	 Concatenate3(S1, "\n", S2 -> S)

  'rule' C_Decls_to_string(nil -> "")

'action' C_Decls_to_string_h(C_DECLS -> STRING)

  'rule' C_Decls_to_string_h(list(D, Ds) -> S):
	 C_Decl_to_string_h(D -> S1)
	 C_Decls_to_string_h(Ds -> S2)
	 Concatenate3(S1, "\n", S2 -> S)

  'rule' C_Decls_to_string_h(nil -> "")

'action' C_Decls_to_string_cc(C_DECLS -> STRING)

  'rule' C_Decls_to_string_cc(list(D, Ds) -> S):
	 C_Decl_to_string_cc(D -> S1)
	 C_Decls_to_string_cc(Ds -> S2)
	 Concatenate3(S1, "\n", S2 -> S)

  'rule' C_Decls_to_string_cc(nil -> "")


'action' C_Decl_to_string(C_DECL -> STRING)

  'rule' C_Decl_to_string(decl(DSs, Ds) -> S):
	 C_Decl_specifiers_to_string(DSs -> S1)
	 (|
	   eq(Ds, nil)
	   where(S1 -> S3)
	 ||
	   C_Declarators_to_string(Ds -> S2)
	   Concatenate3(S1, " ", S2 -> S3)
	 |)
	 Concatenate(S3, ";\n" -> S)

  'rule' C_Decl_to_string(func_def(Name, Attrs, Args, Cvqs, Inits, Body) -> S):
	 C_Decl_specifiers_to_string(Attrs -> SAttrs)
	 C_Declarator_to_string(Name -> SName)
	 C_Args_to_string(Args -> SArgs)
	 C_Cvqs_to_string(Cvqs -> SCvqs)
	 Concatenate3(SAttrs, " ", SName -> S1)
	 Concatenate3("(", SArgs, ")" -> S2)
	 Concatenate3(S1, S2, SCvqs -> S3)
	 (|
	   eq(Inits, nil)
	   where(S3 -> S4)
	 ||
	   C_Member_initializers_to_string(Inits -> SInits)
	   Concatenate3(S3, " : ", SInits -> S4)
	 |)
	 C_Statement_to_string(compound(Body) -> SBody)
	 Concatenate3(S4, SBody, "\n\n" -> S)

  'rule'  C_Decl_to_string(nil -> "")
  
  'rule' C_Decl_to_string(_ -> "/*TODO: declaration unparser*/;\n")


'action' C_Decl_to_string_cc(C_DECL -> STRING)	-- declaration (not definition)

  'rule' C_Decl_to_string_cc(D -> S):
	 C_Filter_decl_for_cc(D -> Ds)
	 C_Decls_to_string(Ds -> S)

'action' C_Filter_decl_for_cc(C_DECL -> C_DECLS)

  'rule' C_Filter_decl_for_cc(D -> Ds):
	 where(D -> decl(DSs, _))
	 C_Class_to_decls(DSs -> Ds)
	 --C_Filter_decl_for_cc(D -> Ds2)
	 --Concatenate_decls(Ds1, Ds2 -> Ds)

  'rule' C_Filter_decl_for_cc(D -> nil)

'action' Concatenate_decls(C_DECLS, C_DECLS -> C_DECLS)

  'rule' Concatenate_decls(Ds, list(D, Ds1) -> Ds2)
	 Append_decl(Ds, D -> Ds0)
	 Concatenate_decls(Ds0, Ds1 -> Ds2)

  'rule' Concatenate_decls(Ds, nil -> Ds)

'action' Append_decl(C_DECLS, C_DECL -> C_DECLS)

  'rule' Append_decl(list(D, Ds), D1 -> list(D, Ds2)):
	 Append_decl(Ds, D1 -> Ds2)

  'rule' Append_decl(nil, D -> list(D, nil))

'action' C_Class_to_decls(C_DECL_SPECIFIERS -> C_DECLS)

  'rule' C_Class_to_decls(list(type(class(_, id(Id), _, Ms)), DSs) -> Ds):
	 C_Filter_members_for_cc(Id, Ms -> Ds)

  'rule' C_Class_to_decls(list(_, DSs) -> Ds):
	 C_Class_to_decls(DSs -> Ds)

  'rule' C_Class_to_decls(nil -> nil):

'action' C_Filter_members_for_cc(IDENT, C_MEMBER_DECLS -> C_DECLS)

  'rule' C_Filter_members_for_cc(Id, by_access_group(A, Ms) -> Ms1):
	 C_Filter_members_for_cc(Id, Ms -> Ms1)

  'rule' C_Filter_members_for_cc(Id, list(M, Ms) -> Ds1):
	 C_Filter_member_for_cc(Id, M -> D)
	 (|
	   where(D -> decl(D1))
	   C_Filter_members_for_cc(Id, Ms -> Ds)
	   where(C_DECLS'list(D1, Ds) -> Ds1)
	 ||
	   C_Filter_members_for_cc(Id, Ms -> Ds1)
	 |)

  'rule' C_Filter_members_for_cc(_, nil -> nil)


'type'	 C_OPT_DECL

	 decl(C_DECL)
	 nil


'action' C_Filter_member_for_cc(IDENT, C_MEMBER_DECL -> C_OPT_DECL)

  'rule' C_Filter_member_for_cc(Cid, member(func_def(Name, Attrs, Args, Cvqs, Inits, Body)) -> D):
	 (|
	   -- skip inline function definitions
	   Is_inline(Attrs)
	   where(C_OPT_DECL'nil -> D)
	 ||
	   -- put the class member function definitions in .cc files
	   where(Name -> dname(Fid))
	   where(C_OPT_DECL'decl(func_def(dname(qualified(Fid, list(Cid,nil))), Attrs, Args, Cvqs, Inits, Body)) -> D)
	 |)

  'rule' C_Filter_member_for_cc(_, _ -> nil)


'action' C_Decl_to_string_h(C_DECL -> STRING)	-- declaration (not definition)

  'rule' C_Decl_to_string_h(D -> S):
	 C_Filter_decl_for_h(D -> D1)
	 C_Decl_to_string(D1 -> S)
--	 Concatenate("\n", S1 -> S)

'action' C_Filter_decl_for_h(C_DECL -> C_DECL)

  'rule' C_Filter_decl_for_h(decl(DSs, Ds) -> decl(DSsNew, Ds)): -- class definition
	 C_Filter_class_for_h(DSs -> DSsNew)

  'rule' C_Filter_decl_for_h(D -> D): -- inline function definitions: no touch
	 where(D ->func_def(_, Attrs, _, _, _, _))
	 Is_inline(Attrs)

  'rule' C_Filter_decl_for_h(D -> nil): -- static function definitions: remove from .h
	 where(D ->func_def(_, Attrs, _, _, _, _))
	 Is_static(Attrs)

  'rule' C_Filter_decl_for_h(func_def(Name, Attrs, Args, Cvqs, _, _) ->
			     decl(Attrs1, list(with_args(Name, Args, Cvqs), nil))):
			     -- non inline functions: prototype declaration
	 Add_extern(Attrs -> Attrs1)

  'rule' C_Filter_decl_for_h(decl(DSs, Ds) -> decl(DSsNew, DsNew)): -- others (mainly variable declarations)
	 Remove_static(DSs -> DSs1)
	 Add_extern(DSs1 -> DSsNew)
	 Remove_init(Ds -> DsNew)

  'rule' C_Filter_decl_for_h(D -> D)

'condition' C_Filter_class_for_h(C_DECL_SPECIFIERS -> C_DECL_SPECIFIERS)

  'rule' C_Filter_class_for_h(list(DS, DSs) -> DSsNew):
	 (|
	   where(DS -> type(class(K, id(Id), Bs, Ms)))
	   C_Filter_members_for_h(Id, Ms -> Ms1)
	   where(type(class(K, id(Id), Bs, Ms1)) -> DS1)
	   (|
	     eq(DSs, nil)
	     where(C_DECL_SPECIFIERS'list(DS1, nil) -> DSsNew)
	   ||
	     C_Filter_class_for_h(DSs -> DSs1)
	     where(C_DECL_SPECIFIERS'list(DS1, DSs1) -> DSsNew)
	   |)
	 ||
	   C_Filter_class_for_h(DSs -> DSsNew)
	 |)

'action' C_Filter_members_for_h(IDENT, C_MEMBER_DECLS -> C_MEMBER_DECLS)

  'rule' C_Filter_members_for_h(Id, by_access_group(A, Ms) -> Ms1):
	 C_Filter_members_for_h(Id, Ms -> Ms1)

  'rule' C_Filter_members_for_h(Id, list(M, Ms) -> list(M1, Ms1)):
	 C_Filter_member_for_h(Id, M -> M1)
	 C_Filter_members_for_h(Id, Ms -> Ms1)

  'rule' C_Filter_members_for_h(_, nil -> nil)

'action' C_Filter_member_for_h(IDENT, C_MEMBER_DECL -> C_MEMBER_DECL)

  'rule' C_Filter_member_for_h(Id, member(func_def(Name, Attrs, Args, Cvqs, Inits, Body)) -> M):
	 (|
	   Is_inline(Attrs)
	   Remove_inline(Attrs -> Attrs1)
	   where(C_MEMBER_DECL'member(func_def(Name, Attrs1, Args, Cvqs, Inits, Body)) -> M)
	 ||
	   where(C_MEMBER_DECL'member(decl(Attrs, list(with_args(Name, Args, Cvqs), nil))) -> M)
	 |)

  'rule' C_Filter_member_for_h(Id, M -> M)

'condition' Is_inline(C_DECL_SPECIFIERS)

  'rule' Is_inline(list(DS, DSs)):
	 (|
	   eq(DS, fct(inline))
	 ||
	   Is_inline(DSs)
	 |)

'condition' Is_static(C_DECL_SPECIFIERS)

  'rule' Is_static(list(DS, DSs)):
	 (|
	   eq(DS, storage(static))
	 ||
	   Is_static(DSs)
	 |)

'action' Remove_inline(C_DECL_SPECIFIERS -> C_DECL_SPECIFIERS)

  'rule' Remove_inline(list(fct(inline), Ds) -> Ds1):
	 Remove_inline(Ds -> Ds1)

  'rule' Remove_inline(list(D, Ds) -> list(D, Ds1)):
	 Remove_inline(Ds -> Ds1)

  'rule' Remove_inline(nil -> nil)

'action' Add_extern(C_DECL_SPECIFIERS -> C_DECL_SPECIFIERS)

  'rule' Add_extern(DSs -> DSs1):
	 where(DSs -> list(H, T))
	 (|
	   eq(H, storage(extern))
	   where(DSs -> DSs1)
	 ||
	   where(C_DECL_SPECIFIERS'list(storage(extern), DSs) -> DSs1)
	 |)

'action' Remove_static(C_DECL_SPECIFIERS -> C_DECL_SPECIFIERS)

  'rule' Remove_static(list(storage(static), Ds) -> Ds1):
	 Remove_static(Ds -> Ds1)

  'rule' Remove_static(list(D, Ds) -> list(D, Ds1)):
	 Remove_static(Ds -> Ds1)

  'rule' Remove_static(nil -> nil)

'action' Remove_init(C_DECLARATORS -> C_DECLARATORS)

  'rule' Remove_init(list(with_init(D, _), Ds) -> list(D, Ds1)):
	 Remove_init(Ds -> Ds1)

  'rule' Remove_init(list(D, Ds) -> list(D, Ds1)):
	 Remove_init(Ds -> Ds1)

  'rule' Remove_init(nil -> nil)


'action' C_Decl_specifiers_to_string(C_DECL_SPECIFIERS -> STRING)

  'rule' C_Decl_specifiers_to_string(list(DS, DSs) -> S)
	 C_Decl_specifier_to_string(DS -> S1)
	 (|
	   eq(DSs, nil)
	   where(S1 -> S)
	 ||
	   C_Decl_specifiers_to_string(DSs -> S2)
	   Concatenate3(S1, " ", S2 -> S)
	 |)

  'rule' C_Decl_specifiers_to_string(nil -> "")

'action' C_Decl_specifier_to_string(C_DECL_SPECIFIER -> STRING)

  'rule' C_Decl_specifier_to_string(friend -> "friend")

  'rule' C_Decl_specifier_to_string(typedef -> "\ntypedef")

  'rule' C_Decl_specifier_to_string(storage(SC) -> S):
	 C_Storage_class_to_string(SC -> S)

  'rule' C_Decl_specifier_to_string(type(T) -> S):
	 C_Type_to_string(T -> S)

  'rule' C_Decl_specifier_to_string(fct(F) -> S):
	 C_Fct_specifier_to_string(F -> S)


'action' C_Declarators_to_string(C_DECLARATORS -> STRING)

  'rule' C_Declarators_to_string(list(D, Ds) -> S):
	 C_Declarator_to_string(D -> S1)
	 (|
	   eq(Ds, nil)
	   where(S1 -> S)
	 ||
	   C_Declarators_to_string(Ds -> S2)
	   Concatenate3(S1, ", ", S2 -> S)
	 |)

  'rule' C_Declarators_to_string(nil -> "")

'action' C_Declarator_to_string(C_DECLARATOR -> STRING)

  'rule' C_Declarator_to_string(nil -> "")

  'rule' C_Declarator_to_string(dname(Name) -> S):
	 C_Name_to_string(Name -> S)

  'rule' C_Declarator_to_string(with_init(D, I) -> S):
	 C_Declarator_to_string(D -> S1)
	 C_Initializer_to_string(I -> S2)
	 Concatenate(S1, S2 -> S)

  'rule' C_Declarator_to_string(ptr_to(PtrOp, D) -> S):
	 C_Ptr_op_to_string(PtrOp -> S1)
	 C_Declarator_to_string(D -> S2)
	 Concatenate3(S1, " ", S2 -> S)

  'rule' C_Declarator_to_string(with_args(D, Args, CVs) -> S):
	 C_Declarator_to_string(D -> S1)
	 C_Args_to_string(Args -> S2)
	 Concatenate3(S1, "(", S2 -> S3)
	 (|
	   eq(CVs, nil)
	   Concatenate(S3, ")"  -> S)
	 ||
	   C_Cvqs_to_string(CVs -> S4)
	   Concatenate3(S3, ") ", S4 -> S)
	 |)

  'rule' C_Declarator_to_string(with_index(D, Expr) -> S):
	 C_Declarator_to_string(D -> S1)
	 (|
	   eq(Expr, nil)
	   Concatenate(S1, "[]" -> S)
	 ||
	   C_Expr_to_string(Expr -> S2)
	   Concatenate3(S1, "[", S2 -> S3)
	   Concatenate(S3, "]" -> S)
	 |)

  'rule' C_Declarator_to_string(with_bracket(D) -> S)
	 C_Declarator_to_string(D -> S1)
	 Concatenate3("(", S1, ")" -> S)


'action' C_Initializers_to_string(C_INITIALIZERS -> STRING)

  'rule' C_Initializers_to_string(in_brace(Is) -> S):
	 C_Initializers_to_string(Is -> S1)
	 Concatenate3("{ ", S1, "/*optional?,*/ }\n" -> S)

  'rule' C_Initializers_to_string(list(I, Is) -> S):
	 C_Initializer_to_string(I -> S1)
	 (|
	   eq(Is, nil)
	   where(S1 -> S)
	 ||
	   C_Initializers_to_string(Is -> S2)
	   Concatenate3(S1, ", ", S2 -> S)
	 |)

  'rule' C_Initializers_to_string(nil -> "")

'action' C_Initializer_to_string(C_INITIALIZER -> STRING)

  'rule' C_Initializer_to_string(nil -> "")

  'rule' C_Initializer_to_string(assign(Expr) -> S):
	 C_Expr_to_string(Expr -> S1)
	 Concatenate(" = ", S1 -> S)

  'rule' C_Initializer_to_string(brace(Is) -> S):
	 C_Initializers_to_string(Is -> S1)
	 Concatenate3(" = { ", S1, "/*optional?,*/}" -> S)

  'rule' C_Initializer_to_string(bracket(Exprs) -> S):
	 C_Exprs_to_string(Exprs -> S1)
	 Concatenate3("(", S1, ")" -> S)


'action' C_Args_to_string(C_ARG_DECLS -> STRING)

  'rule' C_Args_to_string(with_elipse(As) -> S):
	 C_Args_to_string(As -> S1)
	 Concatenate(S1, ", ..." -> S)

  'rule' C_Args_to_string(list(A, As) -> S):
	 C_Arg_to_string(A -> S1)
	 (|
	   eq(As, nil)
	   where(S1 -> S)
	 ||
	   C_Args_to_string(As -> S2)
	   Concatenate3(S1, ", ", S2 -> S)
	 |)

  'rule' C_Args_to_string(nil -> "")

'action' C_Arg_to_string(C_ARG_DECL -> STRING)

  'rule' C_Arg_to_string(arg(DSs, D, V) -> S):
	 C_Decl_specifiers_to_string(DSs -> S1)
	 C_Declarator_to_string(D -> S2)
	 Concatenate3(S1, " ", S2 -> S3)
	 (|
	   eq(V, nil)
	   where(S3 -> S)
	 ||
	   C_Expr_to_string(V -> S4)
	   Concatenate3(S3, " = ", S4 -> S)
	 |)

'action' C_Storage_class_to_string(C_STORAGE_CLASS_SPECIFIER -> STRING)
  'rule' C_Storage_class_to_string(auto -> "auto")
  'rule' C_Storage_class_to_string(register -> "register")
  'rule' C_Storage_class_to_string(static -> "static")
  'rule' C_Storage_class_to_string(extern -> "extern")
  'rule' C_Storage_class_to_string(nil -> "")

'action' C_Fct_specifier_to_string(C_FCT_SPECIFIER -> STRING)
  'rule' C_Fct_specifier_to_string(inline -> "inline")
  'rule' C_Fct_specifier_to_string(virtual -> "virtual")


----------------------------------------------------------------------
-- Type specifiers
----------------------------------------------------------------------

'type'	DELIMITER
	space
	comma
	nil

'action' C_Types_to_string(C_TYPE_SPECIFIERS, DELIMITER -> STRING)

  'rule' C_Types_to_string(list(T, Ts), D -> S):
	 C_Type_to_string(T -> S1)
	 (|
	   eq(Ts, nil)
	   where(S1 -> S)
	 ||
	   C_Types_to_string(Ts, D -> S2)
	   (|
	     eq(D, space)
	     where(" " -> SD)
	   ||
	     eq(D, nil)
	     where(" " -> SD)
	   ||
	     eq(D, comma)
	     where(", " -> SD)
	   |)
	   Concatenate3(S1, SD, S2 -> S)
	 |)

  'rule' C_Types_to_string(nil, _ -> "")

'action' C_Type_to_string(C_TYPE_SPECIFIER -> STRING)

  'rule' C_Type_to_string(char -> "char"):
  'rule' C_Type_to_string(rsl_char -> "RSL_char"):
  'rule' C_Type_to_string(string -> "string"):
  'rule' C_Type_to_string(rsl_string -> "RSL_string"):
  'rule' C_Type_to_string(short -> "short"):
  'rule' C_Type_to_string(int -> "int"):
  'rule' C_Type_to_string(bool -> "bool"):
  'rule' C_Type_to_string(long -> "long"):
  'rule' C_Type_to_string(signed -> "signed"):
  'rule' C_Type_to_string(unsigned -> "unsigned"):
  'rule' C_Type_to_string(float -> "float"):
  'rule' C_Type_to_string(double -> "double"):
  'rule' C_Type_to_string(void -> "void"):
  'rule' C_Type_to_string(const -> "const"):
  'rule' C_Type_to_string(volatile -> "volatile"):
  'rule' C_Type_to_string(template(Id, Ts) -> S):
	 C_id_to_string(Id -> S1)
	 C_Types_to_string(Ts, comma -> S2)
	 Concatenate3(S1, "<", S2 -> S3)
	 Concatenate(S3, ">" -> S)

  'rule' C_Type_to_string(class(Key, Opt_id, Bases, Members) -> S):
	 C_Class_key_to_string(Key -> S0)
	 (|
	   eq(Opt_id, nil)
	   Concatenate(S0, " " -> S2)
	 ||
	   where(Opt_id -> id(Name))
	   C_id_to_string(Name -> S1)
	   Concatenate3(S0, " ", S1 -> S2)
	 |)
	 (|
	   eq(Bases, nil)
	   where(S2 -> S3)
	 ||
	   C_Bases_to_string(Bases -> S21)
	   Concatenate3(S2, " : ", S21 -> S3)
	 |)
	 C_Members_to_string(Members -> S4)
	 Concatenate3(S3, "{\n", S4 -> S5)
	 Concatenate(S5, "}" -> S)
	
  'rule' C_Type_to_string(enum(Opt_Id, Enums) -> S):
	 (|
	   where(Opt_Id -> id(Id))
	   C_id_to_string(Id -> S1)
	   Concatenate3("enum ", S1, " { " -> S2)
	 ||
	   where("enum { " -> S2)
	 |)
	 C_Enums_to_string(Enums -> S3)
	 Concatenate3(S2, S3, " }" -> S)

  'rule' C_Type_to_string(named_type(Id) -> S):
	 C_id_to_string(Id -> S)

  'rule' C_Type_to_string(qualified(T, Q) -> S):
	 Qualifier_to_string(Q -> S1)
	 C_Type_to_string(T -> S2)
	 Concatenate3(S1, "::", S2 -> S)

  'rule' C_Type_to_string(elaborated(K, Id) -> S):
	 C_Keyword_to_string(K -> S1)
	 C_id_to_string(Id -> S2)
	 Concatenate3(S1, " ", S2 -> S)

  'rule' C_Type_to_string(ptr_to(T) -> S):
	 C_Type_to_string(T -> S1)
	 Concatenate(S1, "*" -> S)

  'rule' C_Type_to_string(ref_to(T) -> S):
	 C_Type_to_string(T -> S1)
	 Concatenate(S1, "&" -> S)


'action' C_Enums_to_string(C_ENUMERATORS -> STRING)

  'rule' C_Enums_to_string(list(E, Es) -> S):
	 C_Enum_to_string(E -> S1)
	 (|
	   eq(Es, nil)
	   where(S1 -> S)
	 ||
	   C_Enums_to_string(Es -> S2)
	   Concatenate3(S1, ", ", S2 -> S)
	 |)

  'rule' C_Enums_to_string(nil -> ""):

'action' C_Enum_to_string(C_ENUMERATOR -> STRING)

  'rule' C_Enum_to_string(enumerator(Id, nil) -> S)
	 C_id_to_string(Id -> S)

  'rule' C_Enum_to_string(enumerator(Id, E) -> S)
	 C_id_to_string(Id -> S1)
	 C_Expr_to_string(E -> S2)
	 Concatenate3(S1, " = ", S2 -> S)

'action' Idents_to_string(IDENTS -> STRING)

  'rule' Idents_to_string(list(I, Is) -> S):
	 C_id_to_string(I -> S1)
	 (|
	   eq(Is, nil)
	   where(S1 -> S)
	 ||
	   Idents_to_string(Is -> S2)
	   Concatenate3(S1, ", ", S2 -> S)
	 |)

  'rule' Idents_to_string(nil -> "")


-----------------------------------------------------------------------------
-- Class Declarations
-----------------------------------------------------------------------------

'action' C_Bases_to_string(C_BASE_SPECS -> STRING)

  'rule' C_Bases_to_string(list(B, Bs) -> S):
	 C_Base_to_string(B -> S1)
	 (|
	   eq(Bs, nil)
	   where(S1 -> S)
	 ||
	   C_Bases_to_string(Bs -> S3)
	   Concatenate3(S1, ", ", S3 -> S)
	 |)

  'rule' C_Bases_to_string(nil -> "")

'action' C_Base_to_string(C_BASE_SPEC -> STRING)

  'rule' C_Base_to_string(base(Name, nil) -> S):
	 C_Name_to_string(Name -> S)

  'rule' C_Base_to_string(base(Name, Access) -> S):
	 C_Access_to_string(Access -> S1)
	 C_Name_to_string(Name -> S2)
	 Concatenate3(S1, " ", S2 -> S)

  'rule' C_Base_to_string(template_base(Id, Ts, nil) -> S):
	 C_Type_to_string(template(Id, Ts) -> S)

  'rule' C_Base_to_string(template_base(Id, Ts, Access) -> S):
	 C_Access_to_string(Access -> S1)
	 C_Type_to_string(template(Id, Ts) -> S2)
	 Concatenate3(S1, " ", S2 -> S)

  'rule' C_Base_to_string(virtual(Base) -> S):
	 C_Base_to_string(Base -> S1)
	 Concatenate("virtual ", S1 -> S)


'action' C_Access_to_string(C_ACCESS_SPEC -> STRING)

  'rule' C_Access_to_string(nil -> "")
  'rule' C_Access_to_string(private -> "private")
  'rule' C_Access_to_string(protected -> "protected")
  'rule' C_Access_to_string(public -> "public")


'action' C_Member_initializers_to_string(C_MEMBER_INITIALIZERS -> STRING)

  'rule' C_Member_initializers_to_string(list(I, Is) -> S):
	 C_Member_initializer_to_string(I -> S1)
	 (|
	   eq(Is, nil)
	   where(S1 -> S)
	 ||
	   C_Member_initializers_to_string(Is -> S2)
	   Concatenate3(S1, ", ", S2 -> S)
	 |)

  'rule' C_Member_initializers_to_string(nil -> "")

'action' C_Member_initializer_to_string(C_MEMBER_INITIALIZER -> STRING)

  'rule' C_Member_initializer_to_string(init(Name, Exprs) -> S)
	 C_Name_to_string(Name -> S1)
	 C_Exprs_to_string(Exprs -> S2)
	 Concatenate3(S1, "(", S2 -> S3)
	 Concatenate(S3, ")" -> S)


'action' C_Members_to_string(C_MEMBER_DECLS -> STRING)

  'rule' C_Members_to_string(by_access_group(A, Ms) -> S):
	 C_Access_to_string(A -> S1)
	 C_Members_to_string(Ms -> S2)
	 Concatenate3(S1, ":\n", S2 -> S)
	 
  'rule' C_Members_to_string(list(D, Ds) -> S):
	 C_Member_to_string(D -> S1)
	 (|
	   eq(Ds, nil)
	   where(S1 -> S)
	 ||
	   C_Members_to_string(Ds -> S2)
	   Concatenate(S1, S2 -> S)
	 |)

  'rule' C_Members_to_string(nil -> "")

'action' C_Member_to_string(C_MEMBER_DECL -> STRING)

  'rule' C_Member_to_string(decl(DSs, MDs) -> "/*TODO: member declaration unparser*/"):
	 C_Decl_specifiers_to_string(DSs -> S1)
	 C_Member_declarators_to_string(MDs -> S2)
	 Concatenate3(S1, " ", S2 -> S)

  'rule' C_Member_to_string(member(D) -> S):
	 where(D -> func_def(Name, Attrs, Args, Cvqs, Inits, Body))
	 Remove_inline(Attrs -> Attrs1)
	 C_Decl_to_string(func_def(Name, Attrs1, Args, Cvqs, Inits, Body) -> S)

  'rule' C_Member_to_string(member(D) -> S):
	 C_Decl_to_string(D -> S)

'action' C_Member_declarators_to_string(C_MEMBER_DECLARATORS -> STRING)

  'rule' C_Member_declarators_to_string(list(MD, MDs) -> S):
	 C_Member_declarator_to_string(MD -> S1)
	 (|
	   eq(MDs, nil)
	   where(S1 -> S)
	 ||
	   C_Member_declarators_to_string(MDs -> S2)
	   Concatenate3(S1, ", ", S2 -> S)
	 |)

  'rule' C_Member_declarators_to_string(nil -> "")

'action' C_Member_declarator_to_string(C_MEMBER_DECLARATOR -> STRING)

  'rule' C_Member_declarator_to_string(declarator(D) -> S):
	 C_Declarator_to_string(D -> S)

  'rule' C_Member_declarator_to_string(pure(D) -> S):
	 C_Declarator_to_string(D -> S1)
	 Concatenate(S1, " = 0" -> S)
	 
  'rule' C_Member_declarator_to_string(bit_field(OptId, Width) -> S):
	 (|
	   where(OptId -> id(I))
	   C_id_to_string(I -> S1)
	 ||
	   where("" -> S1)
	 |)
	 C_Expr_to_string(Width -> S2)
	 Concatenate3(S1, " : ", S2 -> S)

'action' C_Class_key_to_string(C_CLASS_KEY -> STRING)

  'rule' C_Class_key_to_string(class -> "class")
  'rule' C_Class_key_to_string(struct -> "struct")
  'rule' C_Class_key_to_string(union -> "union")


'condition' C_Keyword_to_string(C_KEYWORD -> STRING)

  'rule' C_Keyword_to_string(class -> "class")
  'rule' C_Keyword_to_string(enum -> "enum")
  'rule' C_Keyword_to_string(struct -> "struct")
  'rule' C_Keyword_to_string(union -> "union")


-----------------------------------------------------------------------------
-- Statements
-----------------------------------------------------------------------------

'action' C_Statements_to_string(C_STATEMENTS -> STRING)

  'rule' C_Statements_to_string(list(Stmnt, Stmnts) -> S):
	 C_Statement_to_string(Stmnt -> S1)
	 C_Statements_to_string(Stmnts -> S2)
	 Concatenate3(S1, "\n", S2 -> S)

  'rule' C_Statements_to_string(nil -> ""):


'action' C_Statement_to_string(C_STATEMENT -> STRING)

  'rule' C_Statement_to_string(nil -> ""):

  'rule' C_Statement_to_string(labeled(Label, Stmnt) -> S):
	 C_id_to_string(Label -> S1)
	 C_Statement_to_string(Stmnt -> S2)
	 Concatenate3(S1, ":\t", S2 -> S)

  'rule' C_Statement_to_string(case(Case) -> S):
	 C_Expr_to_string(Case -> S1)
	 Concatenate3("case ", S1, ":" -> S)

  'rule' C_Statement_to_string(default -> "default:")

  'rule' C_Statement_to_string(expr(nil) -> "")

  'rule' C_Statement_to_string(expr(Expr) -> S):
	 C_Expr_to_string(Expr -> S1)
	 (|
	   eq(S1, "")
	   where(S1 -> S)
	 ||
	   Concatenate(S1, ";" -> S)
	 |)

  'rule' C_Statement_to_string(compound(nil) -> "{}"):

  'rule' C_Statement_to_string(compound(list(nil,nil)) -> "{}"):

  'rule' C_Statement_to_string(compound(Stmnts) -> S):
	 C_Statements_to_string(Stmnts -> S1)
	 Concatenate3("{\n", S1, "}" -> S)
			   
  'rule' C_Statement_to_string(if(Cond, Then, Else) -> S):
	 C_Expr_to_string(Cond -> S1)
	 (|
	   where(Then -> compound(_))
	   where(Then -> Then1)
	 ||
	   where(compound(list(Then, nil)) -> Then1)
	 |)
	 C_Statement_to_string(Then1 -> S2)
	 Concatenate3("if (", S1, ")\n" -> S3)
	 Concatenate(S3, S2 -> S4)
	 (|
	   eq(Else, nil)
	   where(S4 -> S)
	 ||
	   (|
	     where(Else -> compound(_))
	     where(Else -> Else1)
	   ||
	     where(compound(list(Else, nil)) -> Else1)
	   |)
	   C_Statement_to_string(Else1 -> S5)
	   Concatenate3(S4, "\nelse\n", S5 -> S)
	 |)

  'rule' C_Statement_to_string(switch(Cond, Stmnt) -> S):
	 C_Expr_to_string(Cond -> S1)
	 C_Statement_to_string(Stmnt -> S2)
	 Concatenate3("switch (", S1, ") " -> S3)
	 Concatenate(S3, S2 -> S)

  'rule' C_Statement_to_string(while(Cond, Stmnt) -> S):
	 C_Expr_to_string(Cond -> S1)
	 C_Statement_to_string(Stmnt -> S2)
	 Concatenate3("while (", S1, ") " -> S3)
	 Concatenate(S3, S2 -> S)
  
  'rule' C_Statement_to_string(do_while(Stmnt, Cond) -> S):
	 C_Statement_to_string(Stmnt -> S1)
	 C_Expr_to_string(Cond -> S2)
	 Concatenate3("do ", S1, " while (" -> S3)
	 Concatenate3(S3, S2, ");" -> S)
  
  'rule' C_Statement_to_string(for(Init, Term, Loop, Stmt) -> S):
	 C_Statement_to_string(Init -> Sinit)
	 C_Expr_to_string(Term -> Sterm)
	 C_Expr_to_string(Loop -> Sloop)
	 C_Statement_to_string(Stmt -> Sstmt)
	 (|
	   eq(Init, nil)
	   where("for ( ; " -> S0)
	 ||
	   Concatenate3("for (", Sinit, " " -> S0)
	 |)
	 Concatenate3(S0, Sterm, "; " -> S1)
	 Concatenate3(S1, Sloop, ") " -> S2)
	 Concatenate(S2, Sstmt -> S)

  'rule' C_Statement_to_string(break -> "break;")

  'rule' C_Statement_to_string(continue -> "continue;")

  'rule' C_Statement_to_string(return(Value) -> S):
	 (|
	   eq(Value, nil)
	   where("return;" -> S)
	 ||
	   C_Expr_to_string(Value -> S1)
	   Concatenate3("return ", S1, ";" -> S)
	 |)

  'rule' C_Statement_to_string(goto(Label) -> S):
	 C_id_to_string(Label -> S1)
	 Concatenate3("goto ", S1, ";" -> S)

  'rule' C_Statement_to_string(decl(Decl) -> S):
	 C_Decl_to_string(Decl -> S)

  'rule' C_Statement_to_string(cpp(ST) -> S):
	 CPP_Statement_to_string(ST -> S)

  'rule' C_Statement_to_string(cond_warn(E, ST) -> S):
	 C_Expr_to_string(E -> ES)
	 Concatenate3("if (!(", ES,  ")) RSL_warn(" -> S1)
	 C_Expr_to_string(ST -> S2)
	 Concatenate3(S1, S2, ");" -> S)


-----------------------------------------------------------------------------
-- Preprocessor
-----------------------------------------------------------------------------

'action' CPP_Statement_to_string(CPP_STATEMENT -> STRING)

  'rule' CPP_Statement_to_string(include(Header) -> S):
	 Concatenate3("#include \"", Header, "\"\n" -> S)

  'rule' CPP_Statement_to_string(std_include(Header) -> S):
	 Concatenate3("#include <", Header, ">\n" -> S)

  'rule' CPP_Statement_to_string(ifdef(D) ->S):
	 Concatenate3("#ifdef ", D, "\n" -> S)

  'rule' CPP_Statement_to_string(ifndef(D) ->S):
	 Concatenate3("#ifndef ", D, "\n" -> S)

  'rule' CPP_Statement_to_string(else(D) -> S):
	 Concatenate3("#else //not ", D, "\n" -> S)

  'rule' CPP_Statement_to_string(endif(D) ->S):
	 Concatenate3("#endif //", D, "\n" -> S)
