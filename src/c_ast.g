-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the abstract syntax for C++

'module' c_ast

'use' ast print ext env objects values types pp cc

'export'

BOOL

C_KEYWORD
C_NAME C_OPT_IDENT

C_EXPRS C_EXPR

C_POSTFIX
C_INITIALIZERS C_INITIALIZER
C_ABSTRACT_DECLARATOR
C_OP

C_DECLS C_DECL

C_TEMPL_DEF
C_DECL_SPECIFIERS C_DECL_SPECIFIER
C_STORAGE_CLASS_SPECIFIER
C_FCT_SPECIFIER

C_DECLARATORS C_DECLARATOR
C_PTR_OP
C_ARG_DECLS C_ARG_DECL
C_CV_QUALIFIERS C_CV_QUALIFIER

C_MEMBER_INITIALIZERS C_MEMBER_INITIALIZER
C_TYPE_SPECIFIERS C_TYPE_SPECIFIER
C_CLASS_KEY
C_BASE_SPECS C_BASE_SPEC
C_MEMBER_DECLS C_MEMBER_DECL
C_MEMBER_DECLARATORS C_MEMBER_DECLARATOR
C_ACCESS_SPEC

C_ENUMERATORS C_ENUMERATOR
C_STATEMENTS C_STATEMENT

CPP_STATEMENT

C_OUTFILE

'type'	BOOL
	true
	false

'type'	C_KEYWORD

	asm class delete enum for goto if new private protected public
	struct template union


'type'	C_NAME

	id		(IDENT)
	local_id	(POS, IDENT)	-- for making unique ids 
	op_fun		(C_OP)
	conv_fun	(C_TYPE_SPECIFIERS,
			 C_PTR_OP)
	destr_call	(class	:	IDENT)
	qualified	(name	:	C_NAME,
			 qual	:	IDENTS)
	template	(id	:	IDENT,
			 parms	:	C_TYPE_SPECIFIERS)
	template_member	(templ	:	IDENT,
			 parms	:	C_TYPE_SPECIFIERS,
			 name	:	C_NAME)

'type'	C_OPT_IDENT

	id		(IDENT)
	nil


-----------------------------------------------------------------------------
-- Expressions
-----------------------------------------------------------------------------

'type'	C_EXPRS

	list		(head	:	C_EXPR,
			 tail	:	C_EXPRS)
	nil

'type'	C_EXPR

	nil						-- for 'opt'
	multiple	(exprs	:	C_EXPRS)	-- rather redundant, for product expression
	-- primary expression
	literal		(lit	:	VALUE_LITERAL/*is of RSL's AST*/)
	this
	bracket		(C_EXPR)
	name		(name	:	C_NAME)
	--
	pm		(--pos	:	POS,
			 expr1	:	C_EXPR,
			 ptr_op	:	C_OP,
			 expr2	:	C_EXPR)
	cast		(--pos	:	POS,
			 type	:	IDENT,
			 expr	:	C_EXPR)
	ptr_cast	(--pos	:	POS)	-- Univan added (there was only the cast expression)
			 type	:	IDENT,
			 expr	:	C_EXPR)
	unary		(--pos	:	POS,
			 op	:	C_OP,
			 expr	:	C_EXPR)
	binary		(--pos	:	POS,
			 expr1	:	C_EXPR,
			 op	:	C_OP,
			 expr2	:	C_EXPR)
	conditional	(expr1	:	C_EXPR,
			 expr2	:	C_EXPR,
			 expr3	:	C_EXPR)
	postfix		(--pos	:	POS,
			 expr	:	C_EXPR,
			 suffix	:	C_POSTFIX)
	--
	--TODO:	allocation & deallocation

	-- Univan's (for RSLTC only)
	statements	(ss	:	C_STATEMENTS)
	with_statements	(expr	:	C_EXPR,
			 ss	:	C_STATEMENTS)
	text_literal	(text	:	STRING)

'type'	C_POSTFIX

	index		(expr	:	C_EXPR)
	bracket		(exprs	:	C_EXPRS)
	dot		(membrid:	C_NAME)
	arrow		(membrid:	C_NAME)
	inc
	dec


'type'	C_OP

	-- assignment operators
	assign
	mult_assign
	div_assign
	modulo_assign
	plus_assign
	minus_assign
	shr_assign
	shl_assign
	and_assign
	xor_assign
	or_assign
	-- logical and bitwise operators
	logical_or
	logical_and
	bitwise_or
	bitwise_xor
	bitwise_and
	-- relational operators
	eq
	neq
	lt
	gt
	le
	ge
	-- shift operators
	shl
	shr
	-- arithmetic operators
	plus
	minus
	mult
	div
	modulo
	-- unary operators
	not
	tilde
	inc
	dec	
	--
	comma
	--
	new
	delete
	--
	member
	member_ptr
	indirect_member
	indirect_member_ptr
	--
	sizeof
	--
	address_of
	deref
	-- special for rsltc, no correspondents in C++
	literal(STRING)

-----------------------------------------------------------------------------
-- Declarations
-----------------------------------------------------------------------------

'type'	C_DECLS

	list		(head	:	C_DECL,
			 tail	:	C_DECLS)
	nil	

'type'	C_DECL

	decl		(C_DECL_SPECIFIERS,
			 C_DECLARATORS)
	func_def	(name	:	C_DECLARATOR,
			 attr	:	C_DECL_SPECIFIERS,
			 args	:	C_ARG_DECLS,
			 cvqs	:	C_CV_QUALIFIERS,
			 init	:	C_MEMBER_INITIALIZERS,
			 body	:	C_STATEMENTS)
	template	(C_TEMPL_DEF)
	linkage		(C_DECLS)	-- extern "C" { decls }
	namespace	(ident	:	IDENT,
			 decls	:	C_DECLS)
	nil

'type'	C_TEMPL_DEF

	--TODO

'type'	C_DECL_SPECIFIERS

	list		(head	:	C_DECL_SPECIFIER,
			 tail	:	C_DECL_SPECIFIERS)
	nil

'type'	C_DECL_SPECIFIER

	storage		(C_STORAGE_CLASS_SPECIFIER)
	type		(C_TYPE_SPECIFIER)
	fct		(C_FCT_SPECIFIER)
	friend
	typedef

'type'	C_STORAGE_CLASS_SPECIFIER

	auto
	register
	static
	extern
	nil			-- default

'type'	C_TYPE_SPECIFIERS

	list		(head	:	C_TYPE_SPECIFIER,
			 tail	:	C_TYPE_SPECIFIERS)
	nil

'type'	C_TYPE_SPECIFIER

	-- simple type name
	named_type      (id	:	IDENT)
	qualified	(type	:	C_TYPE_SPECIFIER,
			 qual	:	IDENTS)
	char
	rsl_char
	string
	rsl_string
	short
	int
	bool
	long
	signed
	unsigned
	float
	double
	void
	--
	class		(clskey	:	C_CLASS_KEY,
			 name	:	C_OPT_IDENT,
			 bases	:	C_BASE_SPECS,
			 members:	C_MEMBER_DECLS)
	enum		(id	:	C_OPT_IDENT,
			 enums	:	C_ENUMERATORS)
	elaborated	(ckey	:	C_KEYWORD,
			 name	:	IDENT)
	const
	volatile
	--
	--function	(result	:	C_DECL_SPECIFIERS,
	--		 parms	:	C_ARG_DECLS)
	-- Univan's
	ptr_to		(C_TYPE_SPECIFIER)
	ref_to		(C_TYPE_SPECIFIER)
	template	(id	:	IDENT,
			 parms	:	C_TYPE_SPECIFIERS)

'type'	C_FCT_SPECIFIER

	inline
	virtual

'type'	C_ENUMERATORS

	list		(head	:	C_ENUMERATOR,
			 tail	:	C_ENUMERATORS)
	nil

'type'	C_ENUMERATOR

	enumerator	(id	:	IDENT,
			 value	:	C_EXPR)


-----------------------------------------------------------------------------
-- Declarators
-----------------------------------------------------------------------------

'type'	C_DECLARATORS

	list		(head	:	C_DECLARATOR,
			 tail	:	C_DECLARATORS)
	nil

'type'	C_DECLARATOR

	dname		(C_NAME)
	with_init	(C_DECLARATOR,
			 C_INITIALIZER)
	ptr_to		(C_PTR_OP,
			 C_DECLARATOR)
	with_args	(C_DECLARATOR,
			 C_ARG_DECLS,
			 C_CV_QUALIFIERS)
	with_index	(C_DECLARATOR,
			 C_EXPR)
	with_bracket	(C_DECLARATOR)
	nil				-- for some special cases (like some arguments)

'type'	C_ABSTRACT_DECLARATOR

	nil			-- for 'opt'
	with_ptr_op	(C_PTR_OP,
			 C_ABSTRACT_DECLARATOR)
	with_args	(C_ABSTRACT_DECLARATOR,
			 C_ARG_DECLS,
			 C_CV_QUALIFIERS)
	with_index	(C_ABSTRACT_DECLARATOR,
			 C_EXPR)
	with_bracket	(C_ABSTRACT_DECLARATOR)

'type'	C_PTR_OP

	nil					-- for 'opt'
	ptr					-- *
	ref					-- &
	class_member_ptr(class	:	C_NAME)	-- complete-class-name::*
	cv_qualified	(C_PTR_OP,
			 C_CV_QUALIFIERS)

'type'	C_ARG_DECLS

	list		(head	:	C_ARG_DECL,
			 tail	:	C_ARG_DECLS)
	nil
	with_elipse	(C_ARG_DECLS)

'type'	C_ARG_DECL

	arg		(attr	:	C_DECL_SPECIFIERS,
			 id	:	C_DECLARATOR,
			 def_val:	C_EXPR)

'type'	C_CV_QUALIFIERS

	list		(head	:	C_CV_QUALIFIER,
			 tail	:	C_CV_QUALIFIERS)
	nil

'type'	C_CV_QUALIFIER

	const
	volatile

'type'	C_OPT_INITIALIZERS

	init		(C_INITIALIZERS)
	nil

'type'	C_INITIALIZERS

	list		(head	:	C_INITIALIZER,
			 tail	:	C_INITIALIZERS)
	nil
	in_brace	(C_INITIALIZERS)

'type'	C_INITIALIZER

	nil			-- for 'opt'
	assign		(C_EXPR)
	brace		(C_INITIALIZERS)
	bracket		(C_EXPRS)


-----------------------------------------------------------------------------
-- Class Declarations
-----------------------------------------------------------------------------

'type'	C_CLASS_KEY

	struct
	union
	class

'type'	C_BASE_SPECS

	list		(head	:	C_BASE_SPEC,
			 tail	:	C_BASE_SPECS)
	nil

'type'	C_BASE_SPEC

	base		(name	:	C_NAME,
			 access	:	C_ACCESS_SPEC)
	template_base	(id	:	IDENT,
			 parms	:	C_TYPE_SPECIFIERS,
			 access	:	C_ACCESS_SPEC)
	virtual		(base	:	C_BASE_SPEC)

'type'	C_ACCESS_SPEC

	nil			-- for 'optional' or 'default'
	private
	protected
	public


'type'	C_MEMBER_DECLS

	list		(head	:	C_MEMBER_DECL,
			 tail	:	C_MEMBER_DECLS)
	nil
	by_access_group	(access	:	C_ACCESS_SPEC,
			 members:	C_MEMBER_DECLS)

'type'	C_MEMBER_DECL

	decl		(C_DECL_SPECIFIERS,
			 C_MEMBER_DECLARATORS)
	member		(decl	:	C_DECL)

'type'	C_MEMBER_DECLARATORS

	list		(head	:	C_MEMBER_DECLARATOR,
			 tail	:	C_MEMBER_DECLARATORS)
	nil

'type'	C_MEMBER_DECLARATOR

	pure		(d	:	C_DECLARATOR)
	declarator	(d	:	C_DECLARATOR)
	bit_field	(id	:	C_OPT_IDENT,
			 width	:	C_EXPR)

'type'	C_MEMBER_INITIALIZERS

	list		(head	:	C_MEMBER_INITIALIZER,
			 tail	:	C_MEMBER_INITIALIZERS)
	nil

'type'	C_MEMBER_INITIALIZER

	init		(id	:	C_NAME,
			 exprs	:	C_EXPRS)


-----------------------------------------------------------------------------
-- Statements
-----------------------------------------------------------------------------

'type'	C_STATEMENTS

	list		(head	:	C_STATEMENT,
			 tail	:	C_STATEMENTS)
	nil


'type'	C_STATEMENT

	nil
	labeled		(label	:	IDENT,
			 stmt	:	C_STATEMENT)
	case		(case	:	C_EXPR)
	default
	--
	expr		(expr	:	C_EXPR)
	compound	(stmts	:	C_STATEMENTS)
	-- selection statements
	if		(cond	:	C_EXPR,
			 then	:	C_STATEMENT,
			 else	:	C_STATEMENT)
	switch		(cond	:	C_EXPR,
			 body	:	C_STATEMENT)
	-- iteration statements
	while		(cond	:	C_EXPR,
			 body	:	C_STATEMENT)
	do_while	(body	:	C_STATEMENT,
			 cond	:	C_EXPR)
	for		(init	:	C_STATEMENT,
			 term	:	C_EXPR,
			 loop	:	C_EXPR,
			 body	:	C_STATEMENT)
	-- jump statements
	break
	continue
	return		(value	:	C_EXPR)
	goto		(label	:	IDENT)
	--
	decl		(decl	:	C_DECL)
	-- preprocessor
	cpp		(cppst	:	CPP_STATEMENT)
	-- warn unless condition
	cond_warn	(cond	:	C_EXPR,
			 string	:	C_EXPR)



-----------------------------------------------------------------------------
-- Preprocessor
-----------------------------------------------------------------------------

'type'	CPP_STATEMENT

	define		(id	:	IDENT,
			 parms	:	IDENTS,
			 val	:	STRING)
	std_include	(header	:	STRING)
	include		(header	:	STRING)
	if		(cond	:	C_EXPR)
	ifdef		(id	:	STRING)
	ifndef		(id	:	STRING)
	else		(id	:	STRING)
	endif		(id	:	STRING)

-----------------------------------------------------------------------------
-- Output
-----------------------------------------------------------------------------


'type' C_OUTFILE

       h_file
       cc_file
       h_and_cc_file

