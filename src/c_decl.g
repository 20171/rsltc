-- RSL Type Checker
-- Copyright (C) 2000 UNU/IIST

-- raise@iist.unu.edu

-- This module defines support stuff for C++ translator

'module' c_decl

'use' ast print ext env objects values types pp cc c_ast c_unparse sml

'export'

	C_Init

	C_Begin_decl
	  C_Add_decl_specifier
	  C_Add_declarator
	  C_Add_ids_to_declarators
	C_End_decl
	
	Mk_temp_id

	C_Begin_func_def
	  C_Add_arg_decls
	  C_Add_member_initializer
	  C_Arg_decl_specifier
	  C_Arg_def_val
	  C_Arg_declarator 
	  C_Add_cv_qualifier
	  C_Add_function_body
	C_End_func_def 
	C_Set_function_body
	C_Prefix_function_body
	C_Get_arg_decls
	Append_statement
	Concatenate_statements
	
	C_Begin_class_def
	  C_Class_add_base
	  C_Add_member
	  C_Class_id_current
	  C_Class_num_data_members_current
	C_End_class_def
	C_Class_id
	C_Class_num_data_members
	Set_num_data_members

	Register_declared_type	Lookup_declared_type
	Register_declared_id	Not_yet_declared_id
	
	Namespace_init Push_namespace Pop_namespace
	Open_namespaces_h Close_namespaces_h
	Open_namespaces Close_namespaces
	Open_qual_namespaces Close_qual_namespaces
	Prune_by_namespace Namespaces_to_idents
	Object_ids_to_idents Object_to_idents
	Type_name_to_c_name
	Conc_c_types

-----------------------------------------------------------------------

'action' C_Init(Modname:STRING, HeaderFile:STRING, SourceFile:STRING)

  'rule' C_Init(S, Sh, Scc):
	 Concatenate3("#ifndef ",S, "_RSL\n" -> IF)		WriteHString(IF)
	 Concatenate3("#define ",S, "_RSL\n\n" -> DEF)		WriteHString(DEF)
	 CPP_Statement_to_string(include("RSL_typs.h") -> S1)	WriteHString(S1)
	 --
	 CPP_Statement_to_string(include(Sh) -> S2)		WriteCcString(S2)
	 CPP_Statement_to_string(include("RSL_typs.cc") -> S3)	WriteCcString(S3)
	 --
	 Init_decl_stack()
	 Init_class_def_stack()
	 Init_fdef_stack()
	 Init_arg_decls()
	 TempCounter <- 0

-----------------------------------------------------------------------
-- Auxilliary functions for making the C++ declarations easy
-- (implement a declaration stack to enable nesting of declarations)
-----------------------------------------------------------------------

'type'	C_DECL_SPECIFIERS_LIST

	list	(head	:	C_DECL_SPECIFIERS,
		 tail	:	C_DECL_SPECIFIERS_LIST)
	nil

'type'	C_DECLARATORS_LIST

	list	(head	:	C_DECLARATORS,
		 tail	:	C_DECLARATORS_LIST)
	nil

'var' CDeclSpecifiersList : C_DECL_SPECIFIERS_LIST
'var' CDeclaratorsList : C_DECLARATORS_LIST

'var' CDeclSpecifiers : C_DECL_SPECIFIERS
'var' CDeclarators : C_DECLARATORS

'action' Init_decl_stack()

  'rule' Init_decl_stack():
	 DeclaredTypes <- nil
	 DefinedIds <- nil
	 CDeclSpecifiersList <- nil
	 CDeclSpecifiers <- nil
	 CDeclaratorsList <- nil
	 CDeclarators <- nil

'action' Push_decl_specifiers()

  'rule' Push_decl_specifiers():
	 CDeclSpecifiersList -> DSsL
	 CDeclSpecifiers -> DSs
	 CDeclSpecifiersList <- list(DSs, DSsL)

'action' Pop_decl_specifiers()

  'rule' Pop_decl_specifiers():
	 CDeclSpecifiersList -> DSsL
	 [|
	   where(DSsL -> list(DSs, DSsL1))
	   CDeclSpecifiers <- DSs
	   CDeclSpecifiersList <- DSsL1
	 |]

'action' Push_declarators()

  'rule' Push_declarators():
	 CDeclaratorsList -> DsL
	 CDeclarators -> Ds
	 CDeclaratorsList <- list(Ds, DsL)

'action' Pop_declarators()

  'rule' Pop_declarators():
	 CDeclaratorsList -> DsL
	 [|
	   where(DsL -> list(Ds, DsL1))
	   CDeclarators <- Ds
	   CDeclaratorsList <- DsL1
	 |]

'action' C_Begin_decl()

  'rule' C_Begin_decl():
	 Push_decl_specifiers()
	 Push_declarators()
	 CDeclSpecifiers <- nil
	 CDeclarators <- nil

'action' C_End_decl(-> C_DECL)

  'rule' C_End_decl(-> decl(DSs, Ds)):
	 CDeclSpecifiers -> DSs
	 CDeclarators -> Ds
	 Pop_decl_specifiers()
	 Pop_declarators()
	 
'action' C_Add_decl_specifier(C_DECL_SPECIFIER)

  'rule' C_Add_decl_specifier(DS):
	 CDeclSpecifiers -> DSs
	 Append_decl_specifier(DSs, DS -> DSs1)
	 CDeclSpecifiers <- DSs1

'action' Append_decl_specifier(C_DECL_SPECIFIERS, C_DECL_SPECIFIER -> C_DECL_SPECIFIERS)

  'rule' Append_decl_specifier(list(DS, DSs), DS1 -> list(DS, DSs1))
	 Append_decl_specifier(DSs, DS1 -> DSs1)

  'rule' Append_decl_specifier(nil, DS -> list(DS, nil))

'action' C_Add_declarator(C_DECLARATOR)

  'rule' C_Add_declarator(D):
	 CDeclarators -> Ds
	 Append_declarator(Ds, D -> Ds1)
	 CDeclarators <- Ds1

'action' Append_declarator(C_DECLARATORS, C_DECLARATOR -> C_DECLARATORS)

  'rule' Append_declarator(list(D, Ds), D1 -> list(D, Ds1))
	 Append_declarator(Ds, D1 -> Ds1)

  'rule' Append_declarator(nil, D -> list(D, nil))

'action' C_Add_ids_to_declarators(IDENTS)

  'rule' C_Add_ids_to_declarators(list(ID, IDs)):
	 C_Add_declarator(dname(id(ID)))
	 C_Add_ids_to_declarators(IDs)

  'rule' C_Add_ids_to_declarators(nil)


'var' TempCounter : INT

'action' Mk_temp_id(OPT_IDENT -> IDENT)

  'rule' Mk_temp_id(nil -> TempId):
	 TempCounter -> N
	 Int_to_string(N -> S)
	 Concatenate("RSL_Temp_", S -> S1)
	 string_to_id(S1 -> TempId)
	 TempCounter <- N + 1

  'rule' Mk_temp_id(ident(Id) -> TempId):
	 id_to_string(Id -> S1)
	 Concatenate(S1, "_" -> S)
	 string_to_id(S -> TempId)

-------------------------------------------------------------------------
-- Auxilliary functions for making the C++ class declarations easy
-- (implement a declaration stack to enable nesting of class definitions)
-------------------------------------------------------------------------

'type'	CLASS_DEF	
	class_def	(key		:	C_CLASS_KEY,
			 opt_id		:	C_OPT_IDENT,
			 bases		:	C_BASE_SPECS,
			 members	:	C_MEMBER_DECLS,
			 num_members	:	INT)

'type'	C_CLASS_DEF_LIST
	list	(head	:	CLASS_DEF,
		 tail	:	C_CLASS_DEF_LIST)
	nil

'var' CClassDefList : C_CLASS_DEF_LIST	-- the whole stack
'var' CClassDef : CLASS_DEF		-- work variable (stack top)
'var' NumMembersLast : INT
'var' ClassIdLast : C_OPT_IDENT

'action' Init_class_def_stack()

  'rule' Init_class_def_stack():
	 CClassDefList <- nil
	 where(class_def(struct, nil, nil, nil, 0) -> D)
	 CClassDef <- D

'action' Push_class_def()

  'rule' Push_class_def():
	 CClassDefList -> Ds
	 CClassDef -> D
	 CClassDefList <- list(D, Ds)

'action' Pop_class_def()

  'rule' Pop_class_def():
	 CClassDefList -> Ds
	 [|
	   where(Ds -> list(D, Ds1))
	   CClassDef <- D
	   CClassDefList <- Ds1
	 |]

'action' C_Begin_class_def(C_CLASS_KEY, C_OPT_IDENT)

  'rule' C_Begin_class_def(K, I):
	 Push_class_def()
	 where(class_def(K, I, nil, nil, 0) -> D)
	 CClassDef <- D
	 ClassIdLast <- I

'action' C_End_class_def(-> C_TYPE_SPECIFIER)

  'rule' C_End_class_def(-> class(K, I, Bs, Ms)):
	 CClassDef -> D
	 where(D -> class_def(K, I, Bs, Ms, _))
	 Pop_class_def()

'action' C_Class_id(-> C_OPT_IDENT)

  'rule' C_Class_id(-> I):
	 --CClassDefSave -> D
	 --where(D -> class_def(_, I, _, _, _))
	 ClassIdLast -> I

'action' C_Class_id_current(-> C_OPT_IDENT)

  'rule' C_Class_id_current(-> I):
	 CClassDef -> D
	 where(D -> class_def(_, I, _, _, _))

'action' Set_num_data_members(INT)

  'rule' Set_num_data_members(N):
	 NumMembersLast <- N

'action' C_Class_num_data_members(-> INT)

  'rule' C_Class_num_data_members(-> N):
	 --CClassDefSave -> D
	 --where(D -> class_def(_, _, _, _, N))
	 NumMembersLast -> N

'action' C_Class_num_data_members_current(-> INT)

  'rule' C_Class_num_data_members_current(-> N):
	 CClassDef -> D
	 where(D -> class_def(_, _, _, _, N))

'action' C_Class_add_base(C_BASE_SPEC)

  'rule' C_Class_add_base(B):
	 CClassDef -> D
	 where(D -> class_def(K, I, Bs, Ms, N))
	 Add_class_base(Bs, B -> Bs1)
	 where(class_def(K, I, Bs1, Ms, N) -> D1)
	 CClassDef <- D1

'action' C_Add_member(C_MEMBER_DECL)

  'rule' C_Add_member(M):
	 CClassDef -> D
	 where(D -> class_def(K, I, Bs, Ms, N))
	 Add_class_member(Ms, M -> Ms1)
	 (|
	   Is_function_member(M)
	   where(N -> N1)
	 ||
	   where(N + 1 -> N1)
	 |)
	 where(class_def(K, I, Bs, Ms1, N1) -> D1)
	 CClassDef <- D1
	 NumMembersLast <- N1

'action' Add_class_base(C_BASE_SPECS, C_BASE_SPEC -> C_BASE_SPECS)

  'rule' Add_class_base(list(B, Bs), B1 -> list(B, Bs1)):
	 (|
	   eq(B, B1)
	   where(Bs -> Bs1)
	 ||
	   Add_class_base(Bs, B1 -> Bs1)
	 |)

  'rule' Add_class_base(nil, B -> list(B, nil))

'action' Add_class_member(C_MEMBER_DECLS, C_MEMBER_DECL -> C_MEMBER_DECLS)

  'rule' Add_class_member(list(M, Ms), M1 -> list(M, Ms1)):
	 (|
	   eq(M, M1)
	   where(Ms -> Ms1)
	 ||
	   Add_class_member(Ms, M1 -> Ms1)
	 |)

  'rule' Add_class_member(nil, M -> list(M, nil)):

'condition' Is_function_member(C_MEMBER_DECL)

  'rule' Is_function_member(decl(DSs, list(D, _))):
	 (|
	   where(D -> pure(_))
	 ||
	   where(D -> declarator(with_args(_, _, _)))
	 |)

  'rule' Is_function_member(member(Decl)):
	 (|
	   where(Decl -> func_def(_, _, _, _, _, _))
	 ||
	   where(Decl -> decl(_, list(with_args(_, _, _), _)))
	 |)

-----------------------------------------------------------------------
-- Auxilliary functions for making the C++ function definitions easy
-----------------------------------------------------------------------

'type'	C_FDEF -- just same as C_DECL'func_def(...)
	fdef	(name	:	C_DECLARATOR,
		 attr	:	C_DECL_SPECIFIERS,
		 args	:	C_ARG_DECLS,
		 cvqs	:	C_CV_QUALIFIERS,
		 init	:	C_MEMBER_INITIALIZERS,
		 body	:	C_STATEMENTS)
	
'type'	C_FDEF_LIST
	list	(head	:	C_FDEF,
		 tail	:	C_FDEF_LIST)
	nil

'var' CFdefList : C_FDEF_LIST
'var' CFdef	: C_FDEF


'action' Init_fdef_stack()

  'rule' Init_fdef_stack():
	 CFdefList <- nil
	 string_to_id("##dummy##" -> Fid)
	 where(fdef(dname(id(Fid)), nil, nil, nil, nil, nil) -> Fdef)
	 CFdef <- Fdef
	 

'action' Push_fdef()

  'rule' Push_fdef():
	 CFdefList -> Ds
	 CFdef -> D
	 CFdefList <- list(D, Ds)
	 
'action' Pop_fdef()

  'rule' Pop_fdef():
	 CFdefList -> Ds
	 [|
	   where(Ds -> list(D, Ds1))
	   CFdef <- D
	   CFdefList <- Ds1
	 |]

'action' C_Begin_func_def(C_NAME)

  'rule' C_Begin_func_def(FuncID):
	 Push_fdef()
	 where(dname(FuncID) -> Fid)
	 where(fdef(Fid, nil, nil, nil, nil, nil) -> D)
	 CFdef <- D
	 C_Begin_decl()
	 C_Begin_arg_decls()

'action' C_End_func_def(-> C_DECL)

  'rule' C_End_func_def(-> Decl)
	 CFdef -> D
	 where(D -> fdef(FID, DSs, /*Args*/_, CVs, Inits, Body))
	 C_End_arg_decls(-> Args)
	 C_Add_declarator(with_args(/*dname(FID)*/FID, Args, CVs))
	 C_End_decl(-> FuncHeader)
	 (|
	   eq(Body, nil)
	   where(FuncHeader -> Decl) -- declaration only
	 ||
	   where(FuncHeader -> decl(DSs1, Ds))
	   where(func_def(/*dname(FID)*/FID, DSs1, Args, CVs, Inits, Body) -> Decl)
	 |)
	 Pop_fdef()

'action' C_Add_member_initializer(C_MEMBER_INITIALIZER)

  'rule' C_Add_member_initializer(I):
	 CFdef -> D
 	 where(D -> fdef(FID, DSs, Args, CVs, Is, Body))
	 Append_member_initializers(Is, I -> Is1)
 	 where(fdef(FID, DSs, Args, CVs, Is1, Body) -> D1)
	 CFdef <- D1

'action' Append_member_initializers(C_MEMBER_INITIALIZERS, C_MEMBER_INITIALIZER -> C_MEMBER_INITIALIZERS)

  'rule' Append_member_initializers(list(I, Is), I1 -> list(I, Is1)):
	 Append_member_initializers(Is, I1 -> Is1)

  'rule' Append_member_initializers(nil, I -> list(I, nil))

'action' C_Add_cv_qualifier(C_CV_QUALIFIER)
	 
  'rule' C_Add_cv_qualifier(CV):
	 CFdef -> D
 	 where(D -> fdef(FID, DSs, Args, Cvqs, Is, Body))
	 Append_cv_qualifiers(Cvqs, CV -> Cvqs1)
	 where(fdef(FID, DSs, Args, Cvqs1, Is, Body) -> D1)
	 CFdef <- D1

'action' Append_cv_qualifiers(C_CV_QUALIFIERS, C_CV_QUALIFIER -> C_CV_QUALIFIERS)

  'rule' Append_cv_qualifiers(list(CV, CVS), CV1 -> list(CV, CVS1))
	 Append_cv_qualifiers(CVS, CV1 -> CVS1)

  'rule' Append_cv_qualifiers(nil, CV -> list(CV, nil))

'action' C_Add_function_body(C_STATEMENT)

  'rule' C_Add_function_body(S):
	 CFdef -> D
 	 where(D -> fdef(FID, DSs, Args, CVqs, Is, Ss))
	 Append_statement(Ss, S -> Ss1)
 	 where(fdef(FID, DSs, Args, CVqs, Is, Ss1) -> D1)
	 CFdef <- D1

'action' C_Set_function_body(C_STATEMENTS)

  'rule' C_Set_function_body(Ss):
	 CFdef -> D
 	 where(D -> fdef(FID, DSs, Args, CVqs, Is, _))
 	 where(fdef(FID, DSs, Args, CVqs, Is, Ss) -> D1)
	 CFdef <- D1

'action' C_Prefix_function_body(C_STATEMENTS)

  'rule' C_Prefix_function_body(Ss):
	 CFdef -> D
 	 where(D -> fdef(FID, DSs, Args, CVqs, Is, Ss1))
	 Concatenate_statements(Ss, Ss1 -> Ss2)
 	 where(fdef(FID, DSs, Args, CVqs, Is, Ss2) -> D1)
	 CFdef <- D1
	 

'action' Append_statement(C_STATEMENTS, C_STATEMENT -> C_STATEMENTS)

  'rule' Append_statement(list(S, Ss), S1 -> list(S, Ss1)):
	 Append_statement(Ss, S1 -> Ss1)

  'rule' Append_statement(nil, S -> list(S, nil)):

'action' Concatenate_statements(C_STATEMENTS, C_STATEMENTS -> C_STATEMENTS)

  'rule' Concatenate_statements(nil, Ss -> Ss):

  'rule' Concatenate_statements(Ss, nil -> Ss):

  'rule' Concatenate_statements(list(S, Ss1), Ss2 -> list(S, Ss)):
	 Concatenate_statements(Ss1, Ss2 -> Ss)


--
-- Argument declarations
--

'type'	C_ARG_DECLS_LIST
	list	(head	:	C_ARG_DECLS,
		 tail	:	C_ARG_DECLS_LIST)
	nil

'var' CArgDeclsList : C_ARG_DECLS_LIST
'var' CArgDeclSpecifiersList : C_DECL_SPECIFIERS_LIST
'var' CArgDeclaratorList : C_DECLARATORS
'var' CArgDefValList : C_EXPRS

'var' CArgDecls : C_ARG_DECLS
'var' CArgDeclSpecifiers : C_DECL_SPECIFIERS
'var' CArgDeclarator : C_DECLARATOR
'var' CArgDefVal : C_EXPR

'action' Init_arg_decls()

  'rule' Init_arg_decls():
	 CArgDeclsList <- nil
	 CArgDecls <- nil
	 CArgDeclSpecifiersList <- nil
	 CArgDeclSpecifiers <- nil
	 CArgDeclaratorList <- nil
	 CArgDeclarator <- nil
	 CArgDefValList <- nil
	 CArgDefVal <- nil

'action' Push_arg_decls()

  'rule' Push_arg_decls():
	 CArgDeclsList -> AsL
	 CArgDecls -> As
	 CArgDeclsList <- list(As, AsL)

'action' Pop_arg_decls()

  'rule' Pop_arg_decls():
	 CArgDeclsList -> Ds
	 [|
	   where(Ds -> list(D, Ds1))
	   CArgDecls <- D
	   CArgDeclsList <- Ds1
	 |]

'action' Push_arg_decl_specifiers()

  'rule' Push_arg_decl_specifiers():
	 CArgDeclSpecifiersList -> DSsL
	 CArgDeclSpecifiers -> DSs
	 CArgDeclSpecifiersList <- list(DSs, DSsL)

'action' Pop_arg_decl_specifiers()

  'rule' Pop_arg_decl_specifiers():
	 CArgDeclSpecifiersList -> DSsL
	 [|
	   where(DSsL -> list(DSs, DSsL1))
	   CArgDeclSpecifiers <- DSs
	   CArgDeclSpecifiersList <- DSsL1
	 |]

'action' Push_arg_declarator()

  'rule' Push_arg_declarator():
	 CArgDeclaratorList -> DL
	 CArgDeclarator -> D
	 CArgDeclaratorList <- list(D, DL)

'action' Pop_arg_declarator()

  'rule' Pop_arg_declarator():
	 CArgDeclaratorList -> DL
	 [|
	   where(DL -> list(D, DL1))
	   CArgDeclarator <- D
	   CArgDeclaratorList <- DL1
	 |]

'action' Push_arg_def_val()

  'rule' Push_arg_def_val():
	 CArgDefValList -> DL
	 CArgDefVal -> D
	 CArgDefValList <- list(D, DL)

'action' Pop_arg_def_val()

  'rule' Pop_arg_def_val():
	 CArgDefValList -> DL
	 [|
	   where(DL -> list(D, DL1))
	   CArgDefVal <- D
	   CArgDefValList <- DL1
	 |]

'action' C_Begin_arg_decls()

  'rule' C_Begin_arg_decls():
	 Push_arg_decls()
	 Push_arg_decl_specifiers()
	 Push_arg_declarator()
	 Push_arg_def_val()
	 CArgDecls <- nil
	 CArgDeclSpecifiers <- nil
	 CArgDeclarator <- nil
	 CArgDefVal <- nil

'action' C_End_arg_decls(-> C_ARG_DECLS)

  'rule' C_End_arg_decls(-> Args):
	 CArgDecls -> Args
	 Pop_arg_decls()
	 Pop_arg_decl_specifiers()
	 Pop_arg_declarator()
	 Pop_arg_def_val()

'action' C_Arg_decl_specifier(C_DECL_SPECIFIER)

  'rule' C_Arg_decl_specifier(DS):
	 CArgDeclSpecifiers -> DSs
	 Append_decl_specifier(DSs, DS -> DSs1)
	 CArgDeclSpecifiers <- DSs1

'action' C_Arg_declarator(C_DECLARATOR) -- terminator of an argument declaration

  'rule' C_Arg_declarator(Arg):
	 CArgDeclSpecifiers -> DSs
	 CArgDefVal -> Expr
	 C_Add_arg_decl(arg(DSs, Arg, Expr))
	 CArgDeclSpecifiers <- nil
	 CArgDeclarator <- nil
	 CArgDefVal <- nil

'action' C_Arg_def_val(C_EXPR) -- NOTE: should be BEFORE C_Arg_declarator()

  'rule' C_Arg_def_val(Expr):
	 ne(Expr, nil)
	 CArgDefVal <- Expr

'action' C_Add_arg_decls(C_ARG_DECLS)

  'rule' C_Add_arg_decls(list(A, As)):
	 C_Add_arg_decl(A)
	 C_Add_arg_decls(As)

  'rule' C_Add_arg_decls(nil)

'action' C_Add_arg_decl(C_ARG_DECL)

  'rule' C_Add_arg_decl(A):
	 CArgDecls -> As
	 Append_arg_decl(As, A -> As1)
	 CArgDecls <- As1

'action' Append_arg_decl(C_ARG_DECLS, C_ARG_DECL -> C_ARG_DECLS)

  'rule' Append_arg_decl(list(A, As), A1 -> list(A, As1)):
	 Append_arg_decl(As, A1 -> As1)

  'rule' Append_arg_decl(nil, A -> list(A, nil))

'action' C_Get_arg_decls(-> C_ARG_DECLS)

  'rule' C_Get_arg_decls(-> As):
	 CArgDecls -> As




-----------------------------------------------------------------------
-- Auxilliary functions for making the C++ statements collection easy
-----------------------------------------------------------------------

--TODO

-----------------------------------------------------------------------
-- Universal type id support
-----------------------------------------------------------------------

'type'   DECLARED_TYPES

	 list	(type		:	C_TYPE_SPECIFIER,
		 tail		:	DECLARED_TYPES)
	 nil

'var' DeclaredTypes : DECLARED_TYPES

'action' Register_declared_type(C_TYPE_SPECIFIER)

-- CT must be named_type(UId) or qualified(named_type(UId), Ids))
-- where UId is a universal type identifier
-- and not yet registered
  'rule' Register_declared_type(CT):
	 DeclaredTypes -> DTS
	 DeclaredTypes <- list(CT, DTS)

-- searches by id since universal ids are unique
'condition' Lookup_declared_type(IDENT -> C_TYPE_SPECIFIER)

  'rule' Lookup_declared_type(Id -> CT):
	 DeclaredTypes -> DTS
	 Lookup_declared_type1(Id, DTS -> CT)

'condition' Lookup_declared_type1(IDENT, DECLARED_TYPES -> C_TYPE_SPECIFIER)

  'rule' Lookup_declared_type1(Id, list(CT, DTS) -> CT1):
	 (| where(CT -> named_type(UId)) ||
	    where(CT -> qualified(named_type(UId), _)) |)
	 (|
	   eq(Id, UId)
	   where(CT -> CT1)
	 ||
	   Lookup_declared_type1(Id, DTS -> CT1)
	 |)
	 
--------------

'var' DefinedIds : IDENTS

'action' Register_declared_id(IDENT)

  'rule' Register_declared_id(Id):
	 DefinedIds -> Ids
	 Add_id(Id, Ids -> Ids1)
	 DefinedIds <- Ids1

'condition' Not_yet_declared_id(IDENT)

  'rule' Not_yet_declared_id(Id):
	 DefinedIds -> Ids
	 Lookup_declared_id(Id, Ids -> Id1)
	 eq(Id1, nil)

'action' Lookup_declared_id(IDENT, IDENTS -> OPT_IDENT)

  'rule' Lookup_declared_id(X, list(Id, Ids) -> Id1):
	 (|
	   eq(X, Id)
	   where(ident(Id) -> Id1)
	 ||
	   Lookup_declared_id(X, Ids -> Id1)
	 |)

  'rule' Lookup_declared_id(_, nil -> nil):

-----------------------------------------------------------
-- namespaces
-----------------------------------------------------------


-- current stack of namespaces 
-- held with top last for use as qualifier
'var' Namespaces : Object_ids

'action' Namespace_init

  'rule' Namespace_init:
	 Namespaces <- nil

'action' Push_namespace(Object_id)

  'rule' Push_namespace(I)
	 Namespaces -> Is
	 Append_object_id(Is, I -> Is1)
	 Namespaces <- Is1

'action' Pop_namespace

  'rule' Pop_namespace:
	 Namespaces -> Is
	 Remove_last_object(Is -> Is1)
	 Namespaces <- Is1

'action' Append_object_id(Object_ids, Object_id -> Object_ids)

  'rule' Append_object_id(list(I, Is), I1 -> list(I, Is1)):
	 Append_object_id(Is, I1 -> Is1)

  'rule' Append_object_id(nil, I -> list(I, nil)):

'action' Remove_last_object(Object_ids -> Object_ids)

  'rule' Remove_last_object(list(I, nil) -> nil):

  'rule' Remove_last_object(list(I, Is) -> list(I, Is1)):
	 Remove_last_object(Is -> Is1)

'action' Prune_by_namespace(Object_ids -> Object_ids)

  'rule' Prune_by_namespace(Is -> Is1)
	 Namespaces -> NIs
	 Prune_object_ids1(Is, NIs -> Is1)

'action' Namespaces_to_idents(-> IDENTS)

  'rule' Namespaces_to_idents(-> Ids):
	 Namespaces -> Is
	 Object_ids_to_idents(Is -> Ids)

'action' Object_ids_to_idents(Object_ids -> IDENTS)

  'rule' Object_ids_to_idents(list(I, Is)-> list(Id, Ids)):
	 I'Ident -> Id
	 Object_ids_to_idents(Is -> Ids)

  'rule' Object_ids_to_idents(nil -> nil):

'action' Object_to_idents(OBJECT_EXPR -> IDENTS)

  'rule' Object_to_idents(obj_occ(_, I) -> list(Id, nil)):
	 I'Ident -> Id

  'rule' Object_to_idents(qual_occ(P, Obj1, I) -> Ids):
	 Object_to_idents(Obj1 -> Ids1)
	 I'Ident -> Id
	 Append_id(Ids1, Id -> Ids)

  'rule' Object_to_idents(obj_appl(Obj, _) -> Ids):
	 Object_to_idents(Obj -> Ids)

  'rule' Object_to_idents(obj_array(_, Obj) -> Ids):
	 Object_to_idents(Obj -> Ids)

  'rule' Object_to_idents(obj_fit(Obj, _) -> Ids):
	 Object_to_idents(Obj -> Ids)

'action' Append_id(IDENTS, IDENT -> IDENTS)

  'rule' Append_id(list(Id, Ids), Id1 -> list(Id, Ids1)):
	 Append_id(Ids, Id1 -> Ids1)

  'rule' Append_id(nil, Id -> list(Id, nil)):

'action' Close_namespaces_h

  'rule' Close_namespaces_h:
	 Namespaces -> NIs
	 Close_namespaces1(NIs, h_file)

'action' Close_namespaces

  'rule' Close_namespaces:
	 Namespaces -> NIs
	 Close_namespaces1(NIs, h_and_cc_file)

'action' Close_namespaces1(Object_ids, C_OUTFILE)

-- top of stack is the innermost, so close first
  'rule' Close_namespaces1(list(I, Is), File):
	 Close_namespaces1(Is, File)
	 I'Ident -> Id
	 C_id_to_string(Id -> S)
	 Concatenate3("\n} // end of namespace ", S, "\n" -> S1)
	 [|
	   (| eq(File, h_file) || eq(File, h_and_cc_file) |)
	   WriteHString(S1)
	 |]
	 [|
	   (| eq(File, cc_file) || eq(File, h_and_cc_file) |)
	   WriteCcString(S1)
	 |]

  'rule' Close_namespaces1(nil, _):

'action' Open_namespaces_h

  'rule' Open_namespaces_h:
	 Namespaces -> NIs
	 Open_namespaces1(NIs, h_file)

'action' Open_namespaces

  'rule' Open_namespaces:
	 Namespaces -> NIs
	 Open_namespaces1(NIs, h_and_cc_file)

'action' Open_namespaces1(Object_ids, C_OUTFILE)

-- top of stack is the innermost, so open last
  'rule' Open_namespaces1(list(I, Is), File):
	 I'Ident -> Id
	 C_id_to_string(Id -> S)
	 Concatenate3("namespace ", S, " {\n" -> S1)
	 [|
	   (| eq(File, h_file) || eq(File, h_and_cc_file) |)
	   WriteHString(S1)
	 |]
	 [|
	   (| eq(File, cc_file) || eq(File, h_and_cc_file) |)
	   WriteCcString(S1)
	 |]
	 Open_namespaces1(Is, File)

  'rule' Open_namespaces1(nil, _):

-- open namespaces as necessary to define a qualified type
'action' Open_qual_namespaces(Object_ids, C_OUTFILE -> Object_ids)

  'rule' Open_qual_namespaces(Is, File -> Is1):
	 Prune_by_namespace(Is -> Is1)
	 Open_qual_namespaces1(Is1, File)

'action' Open_qual_namespaces1(Object_ids, C_OUTFILE)

-- if qualifier is A.B then open A followed by B
  'rule' Open_qual_namespaces1(list(I, Is), File):
	 I'Ident -> Id
	 C_id_to_string(Id -> S)
	 Concatenate3("namespace ", S, " {\n" -> S1)
	 [|
	   (| eq(File, h_file) || eq(File, h_and_cc_file) |)
	   WriteHString(S1)
	 |]
	 [|
	   (| eq(File, cc_file) || eq(File, h_and_cc_file) |)
	   WriteCcString(S1)
	 |]
	 Push_namespace(I)
	 Open_qual_namespaces1(Is, File)

  'rule' Open_qual_namespaces1(nil, _):

'action' Close_qual_namespaces(Object_ids, C_OUTFILE)

-- if qualifier is A.B then close B followed by A
  'rule' Close_qual_namespaces(list(I, Is), File):
	 Close_qual_namespaces(Is, File)
	 I'Ident -> Id
	 C_id_to_string(Id -> S)
	 Concatenate3("\n} // end of namespace ", S, "\n" -> S1)
	 [|
	   (| eq(File, h_file) || eq(File, h_and_cc_file) |)
	   WriteHString(S1)
	 |]
	 [|
	   (| eq(File, cc_file) || eq(File, h_and_cc_file) |)
	   WriteCcString(S1)
	 |]
	 Pop_namespace

  'rule' Close_qual_namespaces(nil, _):



'action' Type_name_to_c_name(C_TYPE_SPECIFIER -> C_NAME)

  'rule' Type_name_to_c_name(named_type(Id) -> id(Id)):

  'rule' Type_name_to_c_name(qualified(named_type(Id), Ids) ->
				qualified(id(Id), Ids)):

'action' Conc_c_types(C_TYPE_SPECIFIERS, C_TYPE_SPECIFIERS -> C_TYPE_SPECIFIERS)

  'rule' Conc_c_types(nil, Ts -> Ts):

  'rule' Conc_c_types(list(T, Ts1), Ts2 -> list(T, Ts)):
	 Conc_c_types(Ts1, Ts2 -> Ts)

