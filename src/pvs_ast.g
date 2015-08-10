-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the abstract syntax for PVS
-- plus some auxiliary types


'module' pvs_ast


'use' ast print ext env objects values types pp cc


'export'

	SPECIFICATION
	THEORY
	DATATYPE

	THEORY_FORMALS
	THEORY_FORMAL
	THEORY_FORMAL_DECL

	THEORY_ELEMENTS
	THEORY_ELEMENT

	IMPORTING

	THEORY_NAMES
	THEORY_NAME

	ACTUALS
	ACTUAL

	THEORY_DECLS
	THEORY_DECL
	CONSTANT_DECL

	DATA_TYPE_PARTS
	DATA_TYPE_PART
	PVS_CONSTRUCTOR
	ACCESORS
	ACCESOR

	PVS_TYPE_EXPRS
	PVS_TYPE_EXPR

	TUPLE_LIST
	TUPLE

	PVS_POST_COND

	PVS_EXPRS
	PVS_EXPR
	PVS_VALUE_LITERAL

	PVS_EXPR_PAIRS
	PVS_EXPR_PAIR

	PVS_FORMAL_FUN_PARAMETERS

	SETBINDINGS
	SETBINDING

	LETBINDINGS
	LETBINDING
	LETBINDS
	LETBIND

	LAMBDABINDINGS
	LAMBDABINDING

	PVS_BINDINGS
	PVS_BINDING
	PROJECTION_LIST

	LIST_LIMIT

	ARGUMENTS_LIST
	ARGUMENTS

	IDENTS_S

	ID_OP_S
	ID_OP
	VAL_ID

	PVS_NAME
	NAME_QUALIF
	ID_AT

	FORMULA_NAME

	FIELD_DECLS
	FIELD_DECL

	PVS_ELSIF_BRANCHES
	PVS_ELSIF_BRANCH
	PVS_ELSE_BRANCH

	RESTRICTION_EXPR

	PVS_OP
	INFIX_OP
	PREFIX_OP
	FUNCTION_OP

	PVS_CONNECTIVE
	BINDING_OP

	EQUAL_FROM

	POS_LIST
	PVS_OPT_POS
	PVS_OPT_POS_S

	-- Auxiliary types
	-- for sorting declares
	DECLAREDS_S
	DECLAREDS
	DECLARED

	RECURSIVE   -- for recognising recursive functions

	RECURSIVE_SUBTYPE -- recursive functions returning a subtype

        ISTHEORY    -- distinguishing when axioms need to be treated
		    -- as lemmas

        THEORY_ID_MAP   -- for renaming theories

--------------------------------------------------
-- RSL Declares structure

-- <-------------------- DECLS -------------------->
--   <----DECL/_DEFS--->       <----DECL/_DEFS--->
-- { {_Def1, ..., _Defi}, ..., {_Defj, ..., _Defn} }

--------------------------------------------------

-----------------------------------------------------------------------------
-- PVS Abstract Syntax
-----------------------------------------------------------------------------

'type' SPECIFICATION

       theory	(THEORY)

       datatype (DATATYPE)


-----------------------------------------------------------------------------

'type' THEORY

       theory		(id		:	IDENT,
			 theoryformals	:	THEORY_FORMALS,
			 theorypart	:	THEORY_ELEMENTS)

       nil	


-----------------------------------------------------------------------------

'type' DATATYPE

       nil	


-----------------------------------------------------------------------------

'type'	THEORY_FORMALS

	list		(head	:	THEORY_FORMAL,
			 tail	:	THEORY_FORMALS)
	nil	


-----------------------------------------------------------------------------

'type'	THEORY_FORMAL

	theory_formal	(importing		:	IMPORTING,
			 theoryformaldecl	:	THEORY_FORMAL_DECL)
	nil	


-----------------------------------------------------------------------------

'type'	THEORY_FORMAL_DECL

	theory_formal_type	(ids		:	IDENTS,
				 typeexpr	:	PVS_TYPE_EXPR)

	theory_formal_const	(idops		:	ID_OP_S,
				 typeexpr	:	PVS_TYPE_EXPR)

	nil	



-----------------------------------------------------------------------------

'type'	THEORY_ELEMENTS

	list		(head	:	THEORY_ELEMENT,
			 tail	:	THEORY_ELEMENTS)
	nil	


-----------------------------------------------------------------------------
'type'	THEORY_ELEMENT

	importing	(IMPORTING)
	theory_decl	(THEORY_DECL)
	-- Used to be able to handle recursive functions.
	-- They are put all here to translate them
	-- at the end of the file.
	-- Included the simple recursive ones.
	-- Another solution would be to solve the
	-- mutual recursion preserving the groups of mutually
	-- recursive functions, each group occupying a rec_decl
	-- in the list of decls instead of only one rec_decl
	-- for all the recursive functions. This solution needs
	-- more work though.
	rec_decl	(THEORY_ELEMENTS)

	mark_decl	(STRING)  -- for debugging

	nil	


-----------------------------------------------------------------------------
'type'	IMPORTING

	theory_name	(THEORY_NAMES)

	theory_map	(dom		:	PVS_TYPE_EXPR,
			 rng		:	PVS_TYPE_EXPR)

	theory_ranged_set	(PVS_TYPE_EXPR)

	theory_ranged_list	(PVS_TYPE_EXPR)

	-- not needed: map function generated ad hoc
	theory_comp_list	(PVS_TYPE_EXPR)

	nil	


-----------------------------------------------------------------------------
'type'	THEORY_NAMES

	list		(head	:	THEORY_NAME,
			 tail	:	THEORY_NAMES)
	nil	


-----------------------------------------------------------------------------
'type'	THEORY_NAME

	theory_name		(id		:	IDENT,
				 actuals	:	ACTUALS)

	nil	


-----------------------------------------------------------------------------
'type'	ACTUALS

	list		(head	:	ACTUAL,
			 tail	:	ACTUALS)
	nil	


-----------------------------------------------------------------------------
'type'	ACTUAL

	expr			(PVS_EXPR)

	type_expr		(PVS_TYPE_EXPR)

	nil	



------------------------------------------------------------------
'type'	THEORY_DECLS

	list		(head	:	THEORY_DECL,
			 tail	:	THEORY_DECLS)

	nil	




------------------------------------------------------------------
'type'	THEORY_DECL

	type_decl	(ids		:	IDENTS,
			 bindings	:	PVS_BINDINGS,
			 eq_from	:	EQUAL_FROM,
			 type_expr	:	PVS_TYPE_EXPR,
			 containing	:	PVS_EXPR)

	var_decl	(idops		:	ID_OP_S,
			 type_expr	:	PVS_TYPE_EXPR)

	const_decl	(CONSTANT_DECL)

	formula_decl	(ids		:	STRING,
			 formula_name	:	FORMULA_NAME,
			 expr		:	PVS_EXPR)

	judgement_decl  (ids		:	STRING,
			 id		:	ID_OP,
			 params		:	PVS_FORMAL_FUN_PARAMETERS,
			 type		:	PVS_TYPE_EXPR,
			 pre_cond	:	PVS_EXPR) 

	post_decl       (ids		:	STRING,
			 id		:	ID_OP,
			 params		:	PVS_FORMAL_FUN_PARAMETERS,
			 type		:	PVS_TYPE_EXPR,
			 post_cond	:	PVS_POST_COND, 
			 pre_cond	:	PVS_EXPR) 

	inline_datatype	(id		:	IDENT,
			 datatypepart	:	DATA_TYPE_PARTS)

	nil


------------------------------------------------------------------
'type' DATA_TYPE_PARTS


	list		(head	:	DATA_TYPE_PART,
			 tail	:	DATA_TYPE_PARTS)

	nil	


------------------------------------------------------------------
'type' DATA_TYPE_PART

       part		(const	:	PVS_CONSTRUCTOR,
			 idop	:	ID_OP,
			 opt_id	:	OPT_IDENT)


------------------------------------------------------------------
'type' PVS_CONSTRUCTOR

       construct	(idop		: ID_OP,
			 acc		: ACCESORS)


------------------------------------------------------------------
'type' ACCESORS


	list		(head	:	ACCESOR,
			 tail	:	ACCESORS)

	nil	


------------------------------------------------------------------
'type' ACCESOR

       accesor		(idops		: ID_OP_S,
			 typeexpr	: PVS_TYPE_EXPR)




------------------------------------------------------------------
-- for translation RSL to PVS
'type'	CONSTANT_DECL

	nodef		(ids		:	ID_OP_S,
			 type_expr	:	PVS_TYPE_EXPR,
			 containing	:	PVS_EXPR)

	expl_const	(ids		:	ID_OP_S,
			 type_expr	:	PVS_TYPE_EXPR,
			 containing	:	PVS_EXPR)

	impl_const	(ids		:	ID_OP_S,
			 type_expr	:	PVS_TYPE_EXPR,
			 containing	:	PVS_EXPR)


	expl_fun_const	(id		:	ID_OP,
			 recursive	:	RECURSIVE,
			 params		:	PVS_FORMAL_FUN_PARAMETERS,
			 type_expr	:	PVS_TYPE_EXPR,
			 expr		:	PVS_EXPR,
			 pre_cond	:	PVS_EXPR)

	impl_fun_const	(id		:	ID_OP,
			 params		:	PVS_FORMAL_FUN_PARAMETERS,
			 type_expr	:	PVS_TYPE_EXPR,
			 post_expr	:	PVS_POST_COND,
			 pre_cond	:	PVS_EXPR)
	
	nil




------------------------------------------------------------------
'type'	PVS_POST_COND

	postcond	(result		:	PVS_BINDINGS,
			 expr		:	PVS_EXPR)
	nil



------------------------------------------------------------------
'type'	EQUAL_FROM

	equal

	from

	nil


------------------------------------------------------------------
'type'	PVS_TYPE_EXPRS

	list		(head	:	PVS_TYPE_EXPR,
			 tail	:	PVS_TYPE_EXPRS)
	nil	



------------------------------------------------------------------
'type'	PVS_TYPE_EXPR

	bool
	int
	nat
	real
	text
	char

	defined		(id	:	IDENT,
			 type	:	PVS_TYPE_EXPR,
			 qualif	:	NAME_QUALIF)

	named_type	(idop	:	ID_OP,
			 qualif	:	NAME_QUALIF)

	tuple_type	(TUPLE_LIST)

	finite_set	(PVS_TYPE_EXPR)

	infinite_set	(PVS_TYPE_EXPR)

	list_type	(PVS_TYPE_EXPR)

	finite_map	(dom		:	PVS_TYPE_EXPR,
			 rng		:	PVS_TYPE_EXPR)

	infinite_map	(dom		:	PVS_TYPE_EXPR,
			 rng		:	PVS_TYPE_EXPR)

	fun_type	(idop		:	ID_OP,
			 domain		:	PVS_TYPE_EXPR,
			 result		:	PVS_TYPE_EXPR)

	subtype		(set_bindings		:	SETBINDING,
			 restriction		:	PVS_EXPR)

	bracket_type	(PVS_TYPE_EXPR)

	record_type	(FIELD_DECLS)

	union_type

	undefined_type

	uninterpreted_type

	not_supported

	any

	none

	poly

	nil	




------------------------------------------------------------------
'type'	TUPLE_LIST

	list		(head	:	TUPLE,
			 tail	:	TUPLE_LIST)
	nil	




------------------------------------------------------------------
'type'	TUPLE

	tuple		(idop		:	ID_OP,
			 type_expr	:	PVS_TYPE_EXPR)
	nil	



------------------------------------------------------------------
'type'	PVS_EXPR_PAIRS

	list		(head	:	PVS_EXPR_PAIR,
			 tail	:	PVS_EXPR_PAIRS)
	nil	




------------------------------------------------------------------
'type'	PVS_EXPR_PAIR

	pair		(left	:	PVS_EXPR,
			 right	:	PVS_EXPR)
	nil	





------------------------------------------------------------------
'type'	PVS_EXPRS

	list		(head	:	PVS_EXPR,
			 tail	:	PVS_EXPRS)
	nil	




------------------------------------------------------------------
'type'	PVS_EXPR

        literal_expr	(lit	:	PVS_VALUE_LITERAL)

	named_val	(name	:	PVS_NAME)

	product		(exprs	:	PVS_EXPRS)

	ranged_set	(left	:	PVS_EXPR,
			 right	:	PVS_EXPR)

	enum_set	(exprs	:	PVS_EXPRS)

	comp_simp_set	(setbinding	:	SETBINDING,
			 restric_expr	:	PVS_EXPR)

	comp_set	(expr		:	PVS_EXPR,
			 type_expr	:	PVS_TYPE_EXPR,
			 setbinding	:	SETBINDING,
			 restric_expr	:	PVS_EXPR)

	ranged_list	(left	:	PVS_EXPR,
			 right	:	PVS_EXPR)

	enum_list	(exprs	:	PVS_EXPRS)

	comp_list	(expr	:	PVS_EXPR,
			 limit	:	LIST_LIMIT)

	enum_map	(exprs	:	PVS_EXPR_PAIRS)

	comp_rng_map	(rng_expr	:	PVS_EXPR,
			 type_expr_dom	:	PVS_TYPE_EXPR,
			 type_expr_rng	:	PVS_TYPE_EXPR,
			 setbinding	:	SETBINDING,
			 restric_expr	:	PVS_EXPR)

	comp_map	(expr_pair	:	PVS_EXPR_PAIR,
			 type_expr_dom	:	PVS_TYPE_EXPR,
			 type_expr_rng	:	PVS_TYPE_EXPR,
			 setbinding	:	SETBINDING,
			 restric_expr	:	PVS_EXPR)

	function	(lambdabindings	:	LAMBDABINDINGS,
			 expr		:	PVS_EXPR)

	list_applic	(list	:	PVS_EXPR,
			 args	:	ARGUMENTS)

	map_applic	(map	:	PVS_EXPR,
			 args	:	ARGUMENTS)

	funct_applic	(fun	:	PVS_EXPR,
			 args	:	ARGUMENTS)

	quantified	(binding_op	:	BINDING_OP,
			 setbinding	:	SETBINDING,
			 restriction	:	PVS_EXPR)

	equivalence	(left	:	PVS_EXPR,
			 right	:	PVS_EXPR,
			 pre	:	PVS_EXPR)

	post		(expr		:	PVS_EXPR,
			 typeexpr	:	PVS_TYPE_EXPR,
			 post		:	PVS_POST_COND,
			 pre		:	PVS_EXPR)

	disamb		(expr	:	PVS_EXPR,
			 type	:	PVS_TYPE_EXPR)

	bracket		(expr	:	PVS_EXPR)

	ax_infix	(left	:	PVS_EXPR,
			 conn	:	PVS_CONNECTIVE,
			 right	:	PVS_EXPR) 

	funct_expr	(op		:	VAL_ID,
			 qualif		:	NAME_QUALIF,
			 expr1		:	PVS_EXPR,
			 expr2		:	PVS_EXPR) 

	ax_prefix	(conn	:	PVS_CONNECTIVE,
			 expr	:	PVS_EXPR) 

	let_expr	(defs	:	LETBINDINGS,
			 expr	:	PVS_EXPR)

	if_expr		(expr	:	PVS_EXPR, 
			 then	:	PVS_EXPR,
			 elsif	:	PVS_ELSIF_BRANCHES,
			 else	:	PVS_ELSE_BRANCH)

	val_occ		(valid		:	VAL_ID,
			 qualif		:	NAME_QUALIF)

	infix_occ	(left		:	PVS_EXPR,
			 idop		:	VAL_ID,
			 right		:	PVS_EXPR)

	prefix_occ	(idop	:	VAL_ID,
			 expr	:	PVS_EXPR)

	env_local	(--decls	:	DECLS,
--			 env	:	CLASS_ENV,
			 expr	:	PVS_EXPR)

	no_val

	no_def

	not_supported

	nil	


------------------------------------------------------------------
'type' PVS_FORMAL_FUN_PARAMETERS

       list		(head	:	PVS_BINDINGS,
			 tail	:	PVS_FORMAL_FUN_PARAMETERS)
       nil	


------------------------------------------------------------------
'type' SETBINDINGS

       -- serves for RSL typing list

       list		(head	:	SETBINDING,
			 tail	:	SETBINDINGS)
       nil	


------------------------------------------------------------------
'type' SETBINDING

       bindings		(PVS_BINDINGS)


------------------------------------------------------------------
'type'	PVS_BINDINGS  -- Binding++

	list		(head	:	PVS_BINDING,
			 tail	:	PVS_BINDINGS)
	nil	


------------------------------------------------------------------
'type'	PVS_BINDING  -- Binding

	-- next two Not legal in PVS, but used in translation to
	-- model RSL's nested product bindings
	prod_binding	(bindings	:	PVS_BINDINGS) -- all untyped

	typed_prod	(bindings	:	PVS_BINDINGS,
			 type_expr	:	PVS_TYPE_EXPR)

	-- PVS real binding values
	typed_id	(idop		:	ID_OP,
			 type_expr	:	PVS_TYPE_EXPR)  -- optional


------------------------------------------------------------------
'type'	PROJECTION_LIST

	list		(head	:	INT,
			 tail	:	PROJECTION_LIST)
	nil	


------------------------------------------------------------------
'type' LAMBDABINDINGS

       list		(head	:	LAMBDABINDING,
			 tail	:	LAMBDABINDINGS)
       nil	


------------------------------------------------------------------
'type' LAMBDABINDING

       bindings			(PVS_BINDINGS)


------------------------------------------------------------------
'type' LETBINDINGS  -- LetBinding++

       list		(head	:	LETBINDING,
			 tail	:	LETBINDINGS)
       nil	


------------------------------------------------------------------
'type' LETBINDING  -- LetBinding

       let_bind	      (letbind	:	LETBIND,
		       expr	:	PVS_EXPR)

       let_binds      (letbinds	:	LETBINDS,
		       expr	:	PVS_EXPR)
       nil	


------------------------------------------------------------------
'type' LETBINDS  -- LetBind++

       list		(head	:	LETBIND,
			 tail	:	LETBINDS)
       nil	


------------------------------------------------------------------
'type' LETBIND  -- LetBind

       let_idop		(idop		:	ID_OP,
			 -- 0 or more
			 bindings	:	PVS_BINDINGS,
			 -- Optional
			 type		:	PVS_TYPE_EXPR)


------------------------------------------------------------------
'type' RESTRICTION_EXPR

       restric_expr		(pos	:	POS,
				 expr	:	PVS_EXPR)

       nil


------------------------------------------------------------------
'type' LIST_LIMIT

       limit		(bindings	:	PVS_BINDINGS,
			 expr		:	PVS_EXPR,
			 restrict	:	PVS_EXPR)

       nil


------------------------------------------------------------------
'type' PVS_VALUE_LITERAL

        bool_true
	bool_false
	int		(val	:	IDENT)
	real		(val	:	IDENT) 
	text		(val	:	STRING) 
	char		(val	:	CHAR)

	nil	



------------------------------------------------------------------
'type' 	PVS_ELSIF_BRANCHES

	list		(head	:	PVS_ELSIF_BRANCH,
			 tail	:	PVS_ELSIF_BRANCHES)

	nil	




------------------------------------------------------------------
'type' 	PVS_ELSIF_BRANCH

	elsif		(if	:	PVS_EXPR,
			 then	:	PVS_EXPR)

	nil	




------------------------------------------------------------------
'type' 	PVS_ELSE_BRANCH

	else		(PVS_EXPR)

	nil	



------------------------------------------------------------------
'type'	FIELD_DECLS

	list		(head	:	FIELD_DECL,
			 tail	:	FIELD_DECLS)

	nil	


------------------------------------------------------------------
'type'	FIELD_DECL

	field		(ids		:	IDENTS,
			 type_expr	:	PVS_TYPE_EXPR)

	nil	


------------------------------------------------------------------
'type'	IDENTS_S

	list		(head	:	IDENTS,
			 tail	:	IDENTS_S)
	nil	


------------------------------------------------------------------
'type'	ID_OP_S

	list		(head	:	ID_OP,
			 tail	:	ID_OP_S)
	nil	


------------------------------------------------------------------
'type'	ID_OP

	id		(IDENT)

	op_symb		(PVS_OP)

        nil



------------------------------------------------------------------
'type'	VAL_ID

	val_id		(pos	:	POS,
			 idop	:	ID_OP)

--	nil	



------------------------------------------------------------------
'type'	FORMULA_NAME

	axiom

	lemma

	nil


------------------------------------------------------------------
'type' PVS_OP

       infix_op(INFIX_OP)

       prefix_op(PREFIX_OP)

       function_op(FUNCTION_OP)

       identity

       not_supported



------------------------------------------------------------------
'type' INFIX_OP

        eq
	neq
	gt
	lt
	ge
	le
	mult
	div
	plus
	minus



------------------------------------------------------------------
'type' PREFIX_OP

       minus



------------------------------------------------------------------
'type' FUNCTION_OP

       supset
	subset
	supseteq
	subseteq
	isin
	notisin
	isin_map
	notisin_map
	rem
	difference
	restriction_by
	int_div
	restriction_to
	caret
	union
	override
	add_in_map
	hash
	inter
	exp
	abs
	card
	len
	append
	inds
	elems
	hd
	hd_set
	hd_map
	tl
	dom
	rng



------------------------------------------------------------------
'type' PVS_CONNECTIVE

        implies,
	or,
	and,
	not


------------------------------------------------------------------
'type' BINDING_OP

       lambda,
       forall,
       exists,
       exists1,
       nil


------------------------------------------------------------------
'type' ARGUMENTS_LIST

	list		(head	:	ARGUMENTS,
			 tail	:	ARGUMENTS_LIST)
	nil	




------------------------------------------------------------------
'type' ARGUMENTS

       argument		(pos		:	POS,
			 exprs		:	PVS_EXPRS)


       


------------------------------------------------------------------
'type'	PVS_NAME

	id_op		(idop		:	ID_OP)

	qual_name	(idop		:	ID_OP,
			 qualif		:	NAME_QUALIF)
	nil	



------------------------------------------------------------------
'type'	NAME_QUALIF

	qualif		(id_at		:	ID_AT,
			 qual_id	:	ID_OP,
			 actuals	:	ACTUALS)

	nil	



------------------------------------------------------------------
'type'	ID_AT
	
	id(IDENT)

	nil	

		


------------------------------------------------------------------
'type' POS_LIST

       list	       (head    :   POS,
                        tail    :   POS_LIST)
       nil      



------------------------------------------------------------------
'type' PVS_OPT_POS_S

       list	       (head    :   PVS_OPT_POS,
                        tail    :   PVS_OPT_POS_S)
       nil      


	


------------------------------------------------------------------
'type' PVS_OPT_POS

       pos(POS)

       no_pos

       nil	


--------------------------------------------------
-- Auxiliary Types
--------------------------------------------------

-- Auxiliary types for sorting declares

--------------------------------------------------
'type' DECLAREDS_S
       list	       (head    :   DECLAREDS,
                        tail    :   DECLAREDS_S)
       nil      

--------------------------------------------------
'type' DECLAREDS
       list	       (head    :   DECLARED,
                        tail    :   DECLAREDS)
       nil      

--------------------------------------------------
'type' DECLARED
       type_item		(Type_id)
       value_item		(Value_id)
       axiom_item		(Axiom_id)
       lemma_item		(Axiom_id)
--       object_item		(pos	     : POS,
--				 id	     : IDENT,
--				 typings     : TYPINGS,
--				 class	     : CLASS)
--       import_item		(IMPORTING) 
       rec_fun_item		(Value_id)
       mut_rec_fun_item		(Value_id)
       rec_item			(DECLAREDS)
       mark_item		(STRING)  -- for debugging

       nil      


--------------------------------------------------
'type' RECURSIVE

       recursive

       nil      


--------------------------------------------------
'type' RECURSIVE_SUBTYPE

       recursive_subtype

       nil      


--------------------------------------------------
'type' ISTHEORY

       theory
       nil

--------------------------------------------------
-- Renaming theories for duplicate object names

'type' THEORY_ID_MAP
       theory_map		(orig	:	Object_id,
				 new	:	IDENT,
				 rest	:	THEORY_ID_MAP)
       nil
