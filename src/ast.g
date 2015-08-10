-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the abstract syntax for RSL
-- plus the global tables Type_id, Value_id, etc
-- plus the types for the global environment variables defined in env.g
-- plus miscellaneous types used elsewhere

'module' ast

'use' ext, fdr_ast

'export'
	-- Modules
	LIB_MODULES LIB_MODULE SCHEME_DEF OBJECT_DEFS OBJECT_DEF
	THEORY_DEF DEVT_RELATION_DEF

	-- Class expressions
	CLASS RENAMES RENAME DEFINEDS DEFINED DEFINED

	-- Declarations
	DECLS DECL TYPE_DEFS TYPE_DEF VARIANTS VARIANT COMPONENTS
	COMPONENT CONSTRUCTOR DESTRUCTOR RECONSTRUCTOR CHOICES CHOICE
	VALUE_DEFS
	VALUE_DEF FORMAL_FUNCTION_APPLICATION
	FORMAL_FUNCTION_PARAMETERS FORMAL_FUNCTION_PARAMETER
	VARIABLE_DEFS VARIABLE_DEF INITIALISATION
	CHANNEL_DEFS CHANNEL_DEF
	AXIOM_DEFS AXIOM_DEF OPT_IDENT
	TEST_CASE_DEFS TEST_CASE_DEF
	-- Added for Model Checking (transition systems description)
	TRANSITION_SYS_DEFS TRANSITION_SYS_DEF
	SYSTEM_DESCRIPTION
	RESOLVED_SYSTEM_DESCRIPTION
	/*TRANSITION_SETS*/
	TRANSITION_OPERATOR
	/*GUARDED_COMMANDS*/
	GUARDED_COMMAND
	EXTRA_GUARD
        EXTRA_ASSERTION
	COMMANDS
	COMMAND

	PROPERTY_DECLS
	PROPERTY_DECL
	RESOLVED_PROPERTY
	LTL_PROPERTY

        -- Object expressions
	OBJECT_EXPR OBJECT_EXPRS

	-- Type expressions
	TYPE_EXPR PRODUCT_TYPE FUNCTION_ARROW RESULT_DESC
	ACCESS_DESCS ACCESS_DESC ACCESS_MODE ACCESSES ACCESS

	-- Value expressions
	VALUE_EXPRS VALUE_EXPR VALUE_LITERAL SET_LIMITATION
	RESTRICTION LIST_LIMITATION VALUE_EXPR_PAIRS VALUE_EXPR_PAIR
	LAMBDA_PARAMETER ACTUAL_FUNCTION_PARAMETERS
	ACTUAL_FUNCTION_PARAMETER QUANTIFIER PRE_CONDITION
	OPT_POST_CONDITION POST_CONDITION RESULT_NAMING
	LET_DEFS LET_DEF LET_BINDING
	ELSIF_BRANCHES ELSIF_BRANCH ELSE_BRANCH CASE_BRANCHES CASE_BRANCH

	-- Bindings and typings
	BINDINGS BINDING TYPINGS TYPING

	-- Patterns, names and operators
	PATTERN PATTERNS NAME NAMES OPT_QUALIFICATION
	ID_OR_OP IDENTS OP CONNECTIVE
	COMBINATOR IDENT

        -- File names
	FILE_NAMES FILE_NAME

	-- Identifiers
	Type_id TYPE SORT_KIND New_type_id Copy_type_id
	TYPE_DEFINITION OPT_FUN
	OPT_VARIABLE_ID OPT_CHANNEL_ID 
	OPT_TYPE_ID Type_ids
	OPT_OBJECT_ID OPT_SCHEME_ID
	Value_id OPT_VALUE_ID Value_ids New_value_id Copy_value_id
	VALUE_DEFINITION OPT_CONDITION
	Variable_id Variable_ids New_variable_id Copy_variable_id
	Channel_id Channel_ids New_channel_id Copy_channel_id
	Scheme_id Scheme_ids New_scheme_id
	Object_id Object_ids New_object_id Copy_object_id
	Axiom_id New_axiom_id 
	Test_case_id New_test_case_id 
	PARAM_TYPE
	Theory_id New_theory_id
	-- Extension for SAL support:
	Transition_system_id New_transition_system_id
	OPT_TRANS_SYS_ID
	Property_id New_property_id

	-- Environments
	MODULE_ENV CLASS_ENV TYPE_ENV VALUE_ENVS
	VARIABLE_ENV
	CHANNEL_ENV AXIOM_ENV TEST_CASE_ENV
	-- SAL transition systems' env:
	TRANS_SYS_ENV
	PROPERTY_ENV
	CURRENT_ENV
	ADAPTS COERCION COERCIONS

	-- Miscellaneous
	FOUND OPT_ID_OR_OP CONSTANT_CONSTRUCTOR INTS
	OWNENV OWNCLASS
	OPT_NAME PATH PATHS DIRECTION
	PARAM_FIT TYPE_NUMBER TYPE_NUMBERS
	RESULTS RESULT ACCS ACC READONLY
	MODULE_CATEGORY OPT_LIB_MODULE
	IN_ARRAY ALL_TOP

	-- implementation fittings
	IMP_FIT TYPE_FITS VALUE_FITS VARIABLE_FITS CHANNEL_FITS OBJECT_FITS
	OBJECT_FIT_KIND OPT_POS HIDE

	-- Pretty printing
	BOX BOXES BOX_TYPE INTE_REP POSN

	-- Dependency graph
	DEPENDENCY MODULE_KIND

        -- Coverage
	REGION  REGIONS

-----------------------------------------------------------------------------
-- Modules
-----------------------------------------------------------------------------

'type' LIB_MODULES
        list		(head	:	LIB_MODULE,
			 tail	:	LIB_MODULES)
	nil

'type' LIB_MODULE
        scheme		(pos	:	POS,
			 context:	FILE_NAMES,
			 orig_context:	FILE_NAMES,
			 def	:	SCHEME_DEF)
        object		(pos	:	POS,
			 context:	FILE_NAMES,
			 orig_context:	FILE_NAMES,
			 def	:	OBJECT_DEF)
	theory		(pos	:	POS,
			 context:	FILE_NAMES,
			 orig_context:	FILE_NAMES,
			 def	:	THEORY_DEF)
	devt_relation	(pos	:	POS,
			 context:	FILE_NAMES,
			 orig_context:	FILE_NAMES,
			 def	:	DEVT_RELATION_DEF)

'type' OPT_LIB_MODULE

       lib_mod(LIB_MODULE)
       nil

'type' SCHEME_DEF

	sdef		(pos	:	POS,
			 id	:	IDENT,
			 parms  :       OBJECT_DEFS,
			 class	:	CLASS)

'type' OBJECT_DEFS

        list		(head	:	OBJECT_DEF,
			 tail	:	OBJECT_DEFS)
	nil

'type' OBJECT_DEF

        odef		(pos	:	POS,
			 id	:	IDENT,
			 params :	TYPINGS,
			 class	:	CLASS)

'type' THEORY_DEF

        theory_def	(pos	:	POS,
			 id	:	IDENT,
			 axs	:	AXIOM_DEFS)

'type' DEVT_RELATION_DEF

        devt_relation_def(pos	:	POS,
			 id	:	IDENT,
			 new	:	IDENT,
			 old	:	IDENT,
			 theory	:	VALUE_EXPR)

'type' CLASS

        basic		(decls	:	DECLS)
	extend		(left	:	CLASS,
			 right	:	CLASS)
	hide		(hides	:	DEFINEDS,
			 class	:	CLASS)
	rename		(renames:	RENAMES,
			 class	:	CLASS)
	with		(pos	:	POS,
			 objects:	OBJECT_EXPRS,
			 class  :	CLASS)
	instantiation	(name	:	NAME,
			 parm	:	OBJECT_EXPRS)
        nil

'type' RENAMES

        list		(head	:	RENAME,
			 tail	:	RENAMES)
	nil

'type' RENAME

        rename		(new	:	DEFINED,
			 old	:	DEFINED)

'type' DEFINEDS

        list		(head	:	DEFINED,
			 tail	:	DEFINEDS)
	nil

'type' DEFINED

        def_name	(pos	:	POS,
			 id_or_op:	ID_OR_OP)
	disamb		(pos	:	POS,
			 id_or_op:	ID_OR_OP,
			 type	:	TYPE_EXPR)
	

-----------------------------------------------------------------------------
-- Declarations
-----------------------------------------------------------------------------


'type' DECLS

        list		(head	:	DECL,
			 tail	:	DECLS)
	nil

'type' DECL

	type_decl	(pos	:	POS,
			 defs	:	TYPE_DEFS)
	value_decl	(pos	:	POS,
			 defs	:	VALUE_DEFS)
	variable_decl	(pos	:	POS,
			 defs	:	VARIABLE_DEFS)
	channel_decl	(pos	:	POS,
			 defs	:	CHANNEL_DEFS)
	object_decl	(pos	:	POS,
			 defs	:	OBJECT_DEFS)
	axiom_decl	(pos	:	POS,
			 defs	:	AXIOM_DEFS)
	test_case_decl	(pos	:	POS,
			 defs	:	TEST_CASE_DEFS)

	trans_system_decl (pos	:	POS,
			   defs	:	TRANSITION_SYS_DEFS)

	property_decl	  (pos	:	POS,
			   defs	:	PROPERTY_DECLS)

'type' TYPE_DEFS

        list		(head	:	TYPE_DEF,
			 tail	:	TYPE_DEFS)
	nil

'type' TYPE_DEF

        sort		(pos	:	POS,
			 id	:	IDENT)
	abbrev		(pos	:	POS,
			 id	:	IDENT,
			 type	:	TYPE_EXPR)
	variant		(pos	:	POS,
			 id	:	IDENT,
			 choices:	VARIANTS)
	record		(pos	:	POS,
			 id	:	IDENT,
			 comps	:	COMPONENTS)
	union		(pos	:	POS,
			 id	:	IDENT,
			 choices:	CHOICES)

'type' VARIANTS

        list		(head	:	VARIANT,
			 tail	:	VARIANTS)
	nil

'type' VARIANT

        record		(pos	:	POS,
			 cons	:	CONSTRUCTOR,
			 comps	:	COMPONENTS)

'type' COMPONENTS

        list		(head	:	COMPONENT,
			 tail	:	COMPONENTS)
	nil

'type' COMPONENT

        component	(pos	:	POS,
			 dest	:	DESTRUCTOR,
			 type	:	TYPE_EXPR,
			 recon	:	RECONSTRUCTOR)

'type' CONSTRUCTOR

        constructor	(pos	:	POS,
			 id_or_op:	ID_OR_OP)
	con_ref		(id	:	Value_id)

	wildcard

'type' DESTRUCTOR

        destructor	(pos	:	POS,
			 id_or_op:	ID_OR_OP)
	dest_ref	(id	:	Value_id)

	nil

'type' RECONSTRUCTOR

        reconstructor	(pos	:	POS,
			 id_or_op:	ID_OR_OP)
	recon_ref	(id	:	Value_id)

	nil
			 
'type' CHOICES

        list		(head	:	CHOICE,
			 tail	:	CHOICES)
	nil

'type' CHOICE

        choice		(pos	:	POS,
			 name	:	NAME)
	choice_ref	(id	:	Type_id,
			 qual	:	OPT_QUALIFICATION)
	nil
        
'type' VALUE_DEFS

        list		(head	:	VALUE_DEF,
			 tail	:	VALUE_DEFS)
	nil

'type' VALUE_DEF

        typing		(pos	:	POS,
			 typing	:	TYPING)
	exp_val		(pos	:	POS,
			 typing	:	TYPING,
			 expr	:	VALUE_EXPR)
	imp_val		(pos	:	POS,
			 typing	:	TYPING,
			 cond	:	RESTRICTION)
	exp_fun		(pos	:	POS,
			 typing	:	TYPING,
			 appl	:	FORMAL_FUNCTION_APPLICATION,
			 expr	:	VALUE_EXPR,
			 post	:	OPT_POST_CONDITION,
			 pre	:	PRE_CONDITION,
			 reg	:	REGION)
	imp_fun		(pos	:	POS,
			 typing	:	TYPING,
			 appl	:	FORMAL_FUNCTION_APPLICATION,
			 post	:	POST_CONDITION,
			 pre	:	PRE_CONDITION)

'type' FORMAL_FUNCTION_APPLICATION

       form_appl	(pos	:	POS,
			 id_or_op:	ID_OR_OP,
			 params	:	FORMAL_FUNCTION_PARAMETERS)

'type' FORMAL_FUNCTION_PARAMETERS

        list		(head	:	FORMAL_FUNCTION_PARAMETER,
			 tail	:	FORMAL_FUNCTION_PARAMETERS)
	nil  
 
'type' FORMAL_FUNCTION_PARAMETER

        form_parm	(pos	:	POS,
			 bindings:	BINDINGS)

'type' VARIABLE_DEFS

        list		(head	:	VARIABLE_DEF,
			 tail	:	VARIABLE_DEFS)
	nil

'type' VARIABLE_DEF

        single		(pos	:	POS,
			 id	:	IDENT,
			 type	:	TYPE_EXPR,
			 init	:	INITIALISATION)
	multiple	(pos	:	POS,
			 ids	:	IDENTS,
			 type	:	TYPE_EXPR)

'type' INITIALISATION

        initial		(expr	:	VALUE_EXPR)
	nil

'type' CHANNEL_DEFS

        list		(head	:	CHANNEL_DEF,
			 tail	:	CHANNEL_DEFS)
	nil

'type' CHANNEL_DEF

        single		(pos	:	POS,
			 id	:	IDENT,
			 type	:	TYPE_EXPR)
	multiple	(pos	:	POS,
			 ids	:	IDENTS,
			 type	:	TYPE_EXPR)

'type' AXIOM_DEFS

        list		(head	:	AXIOM_DEF,
			 tail	:	AXIOM_DEFS)
	nil

'type' AXIOM_DEF

        axiom_def	(pos	:	POS,
			 name	:	OPT_IDENT,
			 expr	:	VALUE_EXPR)

'type' OPT_IDENT

        ident		(id	:	IDENT)
	nil

'type' TEST_CASE_DEFS

        list		(head	:	TEST_CASE_DEF,
			 tail	:	TEST_CASE_DEFS)
	nil

'type' TEST_CASE_DEF

        test_case_def	(pos	:	POS,
			 name	:	OPT_IDENT,
			 expr	:	VALUE_EXPR)


'type' TRANSITION_SYS_DEFS

        list		(head	:	TRANSITION_SYS_DEF,
			 tail	:	TRANSITION_SYS_DEFS)
	nil

'type' TRANSITION_SYS_DEF

        trans_sys_def	(pos	:	POS,
			 name	:	IDENT,
			 sys	:	SYSTEM_DESCRIPTION)

'type' PROPERTY_DECLS
       
       list		(head	:	PROPERTY_DECL,
			 tail	:	PROPERTY_DECLS)

       nil

'type' PROPERTY_DECL	
       
       property_def	(pos	:	POS,
			 name	:	IDENT,
			 TS	:	IDENT,
			 prop	:	VALUE_EXPR) --LTL_PROPERTY
-----------------------------------------------------------------------------
-- Object expressions
-----------------------------------------------------------------------------
'type' OBJECT_EXPRS

        list		(head	:	OBJECT_EXPR,
			 tail	:	OBJECT_EXPRS)
	nil

'type' OBJECT_EXPR

        obj_name	(n	:	NAME)
	obj_appl	(object	:	OBJECT_EXPR,
			 params	:	VALUE_EXPRS)
	obj_array	(params :	TYPINGS,
			 object	:	OBJECT_EXPR)
	obj_fit		(object	:	OBJECT_EXPR,
			 fitting:	RENAMES)
	obj_occ		(pos	:	POS,
			 id	:	Object_id)
	qual_occ	(pos	:	POS,
			 qual	:	OBJECT_EXPR,
			 id	:	Object_id)

-----------------------------------------------------------------------------
-- Type expressions
-----------------------------------------------------------------------------

'type' TYPE_EXPR

        unit
        bool
	int
	nat
	real
	text
	char
	time		-- only used in TRSL
	defined		(id	:	Type_id,
			 qual	:	OPT_QUALIFICATION)
	named_type	(name	:	NAME)
	product		(types	:	PRODUCT_TYPE)
	fin_set		(type	:	TYPE_EXPR)
	infin_set	(type	:	TYPE_EXPR)
	fin_list	(type	:	TYPE_EXPR)
	infin_list	(type	:	TYPE_EXPR)
	fin_map		(dom_type:	TYPE_EXPR,
			 rng_type:	TYPE_EXPR)
	infin_map	(dom_type:	TYPE_EXPR,
			 rng_type:	TYPE_EXPR)
	function	(par_type:	TYPE_EXPR,
			 arrow:		FUNCTION_ARROW,
			 result	:	RESULT_DESC)
	fun		(par_type:	TYPE_EXPR,
			 arrow:		FUNCTION_ARROW,
			 result	:	RESULT)
	subtype		(typing :	TYPING,
			 restr	:	RESTRICTION)
	bracket		(type	:	TYPE_EXPR)
	any
	none
	poly		(num	:	INT)
        array           (dom_type:	TYPE_EXPR,
                         rng_type:	TYPE_EXPR)

'type' PRODUCT_TYPE

        list		(head	:	TYPE_EXPR,
			 tail	:	PRODUCT_TYPE)
	nil

'type' FUNCTION_ARROW

        partial, total	

'type' RESULT_DESC

        result		(accesses:	ACCESS_DESCS,
			 type	:	TYPE_EXPR)
 
'type' ACCESS_DESCS

        list		(head	:	ACCESS_DESC,
			 tail	:	ACCESS_DESCS)
        nil

'type' ACCESS_DESC

        access		(mode	:	ACCESS_MODE,
			 access	:	ACCESSES)

'type' ACCESS_MODE

        read,
	write,
	in,
	out

'type'	ACCESSES

        list		(head	:	ACCESS,
			 tail	:	ACCESSES)
        nil

'type' ACCESS

        named_access	(pos	:	POS,
			 name	:	NAME)
	enumerated_access(pos	:	POS,
			  accesses:	ACCESSES)
	completed_access(pos	:	POS,
			 qual	:	OPT_QUALIFICATION)
	comprehended_access
			(pos	:	POS,
			 access	:	ACCESS,
			 limit	:	SET_LIMITATION)
	variable	(pos	:	POS,
			 var	:	Variable_id, 
			 qual	:	OPT_QUALIFICATION)
	channel		(pos	:	POS, 
			 chan	:	Channel_id, 
			 qual	:	OPT_QUALIFICATION)
	free		 

-----------------------------------------------------------------------------
-- Value expressions
-----------------------------------------------------------------------------

'type' VALUE_EXPRS

        list		(head	:	VALUE_EXPR,
			 tail	:	VALUE_EXPRS)
	nil

'type' VALUE_EXPR

        literal_expr	(pos	:	POS,
			 lit	:	VALUE_LITERAL)
	named_val	(pos	:	POS,
			 name	:	NAME)
	pre_name	(pos	:	POS,
			 name	:	NAME)
	chaos		(pos	:	POS)
	skip		(pos	:	POS)
	stop		(pos	:	POS)
	swap		(pos	:	POS)
	product		(pos	:	POS,
			 exprs	:	VALUE_EXPRS)
	ranged_set	(pos	:	POS,
			 left	:	VALUE_EXPR,
			 right	:	VALUE_EXPR)
	enum_set	(pos	:	POS,
			 exprs	:	VALUE_EXPRS)
	comp_set	(pos	:	POS,
			 expr	:	VALUE_EXPR,
			 limit	:	SET_LIMITATION)
	ranged_list	(pos	:	POS,
			 left	:	VALUE_EXPR,
			 right	:	VALUE_EXPR)
	enum_list	(pos	:	POS,
			 exprs	:	VALUE_EXPRS)
	comp_list	(pos	:	POS,
			 expr	:	VALUE_EXPR,
			 limit	:	LIST_LIMITATION)
	enum_map	(pos	:	POS,
			 exprs	:	VALUE_EXPR_PAIRS)
	comp_map	(pos	:	POS,
			 expr	:	VALUE_EXPR_PAIR,
			 limit	:	SET_LIMITATION)
	function	(pos	:	POS,
			 parm	:	LAMBDA_PARAMETER,
			 expr	:	VALUE_EXPR)
	application	(pos	:	POS,
			 fun	:	VALUE_EXPR,
			 args	:	ACTUAL_FUNCTION_PARAMETERS)
	quantified	(pos	:	POS,
			 quant	:	QUANTIFIER,
			 typings:	TYPINGS,
			 restr	:	RESTRICTION)
	equivalence	(pos	:	POS,
			 left	:	VALUE_EXPR,
			 right	:	VALUE_EXPR,
			 pre	:	PRE_CONDITION)
	post		(pos	:	POS,
			 expr	:	VALUE_EXPR,
			 postcond:	POST_CONDITION,
			 pre	:	PRE_CONDITION)
	disamb		(pos	:	POS,
			 expr	:	VALUE_EXPR,
			 type	:	TYPE_EXPR)
	bracket		(pos	:	POS,
			 expr	:	VALUE_EXPR)
	ax_infix	(pos	:	POS,
			 left	:	VALUE_EXPR,
			 conn	:	CONNECTIVE,
			 right	:	VALUE_EXPR,
			 pre	:	POS) 
	val_infix	(pos	:	POS,
			 left	:	VALUE_EXPR,
			 op	:	OP,
			 right	:	VALUE_EXPR) 
	stmt_infix	(pos	:	POS,
			 left	:	VALUE_EXPR,
			 comb	:	COMBINATOR,
			 right	:	VALUE_EXPR)
	always		(pos	:	POS,
			 expr	:	VALUE_EXPR) 
	ax_prefix	(pos	:	POS,
			 conn	:	CONNECTIVE,
			 expr	:	VALUE_EXPR) 
	val_prefix	(pos	:	POS,
			 op	:	OP,
			 expr	:	VALUE_EXPR)
	comprehended	(pos	:	POS,
			 comb	:	COMBINATOR,
			 expr	:	VALUE_EXPR,
			 limit	:	SET_LIMITATION)
	initialise	(pos	:	POS,
			 qual	:	OPT_QUALIFICATION)
	assignment	(pos	:	POS,
			 name	:	NAME,
			 expr	:	VALUE_EXPR)
	input		(pos	:	POS,
			 name	:	NAME)
	output		(pos	:	POS,
			 name	:	NAME,
			 expr	:	VALUE_EXPR)
	local_expr	(pos	:	POS,
			 decls	:	DECLS,
			 expr	:	VALUE_EXPR) 
	let_expr	(pos	:	POS,
			 defs	:	LET_DEFS,
			 expr	:	VALUE_EXPR)
	if_expr		(pos	:	POS,
			 expr	:	VALUE_EXPR, 
			 then	:	VALUE_EXPR,
			 thenrg	:	REGION,
			 elsif	:	ELSIF_BRANCHES,
			 else	:	ELSE_BRANCH)
	case_expr	(pos	:	POS,
			 expr	:	VALUE_EXPR,
			 exp_pos:	POS, 
			 cases	:	CASE_BRANCHES)
	while_expr	(pos	:	POS,
			 expr	:	VALUE_EXPR, 
			 do	:	VALUE_EXPR)
	until_expr	(pos	:	POS,
			 do	:	VALUE_EXPR, 
			 expr	:	VALUE_EXPR)
	for_expr	(pos	:	POS,
			 limit	:	LIST_LIMITATION, 
			 expr	:	VALUE_EXPR)
	class_scope_expr(pos	:	POS,
			 class	:	CLASS,
			 theory	:	VALUE_EXPR)
	implementation_relation
			(pos	:	POS,
			 new	:	CLASS,
			 old	:	CLASS)	 
	implementation_expr
			(pos	:	POS,
			 new	:	OBJECT_EXPR,
			 old	:	OBJECT_EXPR)
	val_occ		(pos	:	POS,
			 id	:	Value_id,
			 qual	:	OPT_QUALIFICATION)
        local_val_occ	(pos	:	POS,
     			 id	:	Value_id,
			 qual	:	OPT_QUALIFICATION)
	var_occ		(pos	:	POS,
			 id	:	Variable_id,
			 qual	:	OPT_QUALIFICATION)
	pre_occ		(pos	:	POS,
			 id	:	Variable_id,
			 qual	:	OPT_QUALIFICATION)
	infix_occ	(pos	:	POS,
			 left	:	VALUE_EXPR,
			 op	:	Value_id,
			 qual	:	OPT_QUALIFICATION,
			 right	:	VALUE_EXPR)
	prefix_occ	(pos	:	POS,
			 op	:	Value_id,
			 qual	:	OPT_QUALIFICATION,
			 expr	:	VALUE_EXPR)
	ass_occ		(pos	:	POS,
			 id	:	Variable_id,
			 qual	:	OPT_QUALIFICATION,
			 expr	:	VALUE_EXPR)
	input_occ	(pos	:	POS,
			 id	:	Channel_id,
			 qual	:	OPT_QUALIFICATION)
	output_occ	(pos	:	POS,
			 id	:	Channel_id,
			 qual	:	OPT_QUALIFICATION,
			 expr	:	VALUE_EXPR)
	-- added for channels in CSP LTL assertions
	chan_occ	(pos	:	POS,
			 id	:	Channel_id,
			 qual	:	OPT_QUALIFICATION)
	env_local	(pos	:	POS,
			 decls	:	DECLS,
			 env	:	CLASS_ENV,
			 expr	:	VALUE_EXPR)
	env_class_scope (pos	:	POS,
			 class	:	CLASS,
			 env	:	CLASS_ENV,
			 theory	:	VALUE_EXPR)
	no_val
	cc_expr		(pos	:	OPT_POS,
			 string :	STRING,
			 id	:	OPT_IDENT,
			 expr	:	VALUE_EXPR)
        array_access    (pos    :	POS,
			 name	:	VALUE_EXPR,
			 index	:	VALUE_EXPR),
        array_assignment(pos	:	POS,
			 name	:	NAME,
			 indexes	:	VALUE_EXPRS,
			 new_val:	VALUE_EXPR)
        array_expr	(pos	:	POS,
			 sub	:	TYPING,
			 val	:	VALUE_EXPR)
        array_ass_occ	(pos	:	POS,
			 id	:	Variable_id,
			 qual	:	OPT_QUALIFICATION,
			 indexes	:	VALUE_EXPRS,
			 new_val:	VALUE_EXPR)

'type' VALUE_LITERAL

        unit 
        bool_true
	bool_false
	int		(val	:	IDENT)
	real		(val	:	IDENT) 
	text		(val	:	STRING) 
	char		(val	:	CHAR)
	-- for LTL_delta
	delta

'type' SET_LIMITATION

        set_limit	(pos	:	POS,
			 typings:	TYPINGS,
			 restr	:	RESTRICTION)

'type' RESTRICTION

        restriction	(pos	:	POS,
			 expr	:	VALUE_EXPR)
	nil 

'type' LIST_LIMITATION

        list_limit	(pos	:	POS,
			 binding:	BINDING,
			 expr	:	VALUE_EXPR,
			 restr	:	RESTRICTION)

'type' VALUE_EXPR_PAIRS

        list		(head	:	VALUE_EXPR_PAIR,
			 tail	:	VALUE_EXPR_PAIRS)
	nil

'type' VALUE_EXPR_PAIR

        pair		(left	:	VALUE_EXPR,
			 right	:	VALUE_EXPR)

'type' LAMBDA_PARAMETER

       l_typing		(pos	:	POS,
			 typings:	TYPINGS)
       s_typing		(pos	:	POS,
			 typing	:	TYPING)

'type' ACTUAL_FUNCTION_PARAMETERS

        list		(head	:	ACTUAL_FUNCTION_PARAMETER,
			 tail	:	ACTUAL_FUNCTION_PARAMETERS)
	nil

'type' ACTUAL_FUNCTION_PARAMETER

       fun_arg		(pos	:	POS,
			 exprs	:	VALUE_EXPRS)

'type' QUANTIFIER

       all,
       exists,
       exists1

'type' PRE_CONDITION

        pre_cond	(pos	:	POS,
			 expr	:	VALUE_EXPR)
	nil

'type' OPT_POST_CONDITION

        post		(cond	:	POST_CONDITION)
	nil

'type' POST_CONDITION

        post_cond	(pos	:	POS,
			 res	:	RESULT_NAMING,
			 expr	:	VALUE_EXPR)

'type' RESULT_NAMING

        result		(pos	:	POS,
			 binding:	BINDING)
	nil

'type' LET_DEFS

        list		(head	:	LET_DEF,
			 tail	:	LET_DEFS)
	nil

'type' LET_DEF

        explicit	(pos	:	POS,
			 bind	:	LET_BINDING,
			 expr	:	VALUE_EXPR)
        implicit	(pos	:	POS,
			 typing	:	TYPING,
			 restr	:	RESTRICTION)

'type' LET_BINDING

        binding		(pos	:	POS,
			 bind	:	BINDING)
	pattern		(pos	:	POS,
			 patt   :	PATTERN)

'type' ELSIF_BRANCHES

        list		(head	:	ELSIF_BRANCH,
			 tail	:	ELSIF_BRANCHES)
	nil

'type' ELSIF_BRANCH

        elsif		(pos	:	POS,
			 if	:	VALUE_EXPR,
			 then	:	VALUE_EXPR,
			 pe	:	POS)
			 
'type' ELSE_BRANCH

        else		(pos	:	POS,
			 expr	:	VALUE_EXPR)
	nil
			 
'type' CASE_BRANCHES

        list		(head	:	CASE_BRANCH,
			 tail	:	CASE_BRANCHES)
	nil

'type' CASE_BRANCH

        case		(pos	:	POS,
			 pattern:	PATTERN,
			 expr	:	VALUE_EXPR,
			 pe	:	POS)
        
-----------------------------------------------------------------------------
-- Bindings and typings
-----------------------------------------------------------------------------

'type' BINDINGS

        list		(head	:	BINDING,
			 tail	:	BINDINGS)
	nil

'type' BINDING

        single		(pos	:	POS,
			 id_or_op:	ID_OR_OP)
	product		(pos	:	POS,
			 bindings:	BINDINGS)

'type' TYPINGS

        list		(head	:	TYPING,
			 tail	:	TYPINGS)
	nil

'type' TYPING

        single		(pos	:	POS,
			 binding:	BINDING,
			 type	:	TYPE_EXPR)
	multiple	(pos	:	POS,
			 bindings:	BINDINGS,
			 type	:	TYPE_EXPR)

-----------------------------------------------------------------------------
-- Patterns, names and operators
-----------------------------------------------------------------------------

'type' PATTERN

        literal_pattern	(pos	:	POS,
			 literal:	VALUE_LITERAL)
	name_pattern	(pos	:	POS,
			 name	:	NAME)
	record_pattern  (pos	:	POS,
			 name	:	NAME,
			 args	:	PATTERNS)
	id_pattern	(pos	:	POS,
			 id	:	ID_OR_OP)
	wildcard_pattern(pos	:	POS)
	product_pattern (pos	:	POS,
			 patterns:	PATTERNS)
	enum_list	(pos	:	POS,
			 patterns:	PATTERNS)
	conc_list	(pos	:	POS,
			 left	:	PATTERNS,
			 right	:	PATTERN)
	name_occ_pattern(pos	:	POS,
			 id	:	Value_id,
			 qual	:	OPT_QUALIFICATION)
	record_occ_pattern
			(pos	:	POS,
			 id	:	Value_id,
			 qual	:	OPT_QUALIFICATION,
			 args	:	PATTERNS)
			 
'type' PATTERNS

        list		(head	:	PATTERN,
			 tail	:	PATTERNS)
	nil

'type' NAMES

        list		(head	:	NAME,
			 tail	:	NAMES)
	nil

'type' NAME

        name		(pos	:	POS,
			 id_or_op:	ID_OR_OP) 
	qual_name	(pos	:	POS,
			 qual	:	OBJECT_EXPR,
			 id_or_op:	ID_OR_OP)

'type' OPT_QUALIFICATION

        qualification	(object	:	OBJECT_EXPR)
	nil
       
'type' ID_OR_OP

        id_op		(id	:	IDENT)
        op_op		(op	:	OP)

'type' IDENTS

        list		(head	:	IDENT,
			 tail	:	IDENTS)
	nil

'type' OP

        eq,
	neq,
	eqeq,
	gt,
	lt,
	ge,
	le,
	supset,
	subset,
	supseteq,
	subseteq,
	isin,
	notisin,
	rem,
	caret,
	union
	override,
	mult,
	div,
	hash,
	inter,
	exp,
	abs,
	int,
	real,
	card,
	len,
	inds,
	elems,
	hd,
	tl,
	dom,
	rng,
	wait,	-- only used in TRSL
	plus,
	minus

'type' CONNECTIVE

        implies,
	or,
	and,
	not

'type' COMBINATOR

        ext_choice,
	int_choice,
	parallel,
	interlock,
	sequence
	

'type' IDENT

'type' FILE_NAMES

        list		(head	:	FILE_NAME,
			 tail	:	FILE_NAMES)
	nil

'type' FILE_NAME

----------------------------------------------------------------
-- Identifiers
----------------------------------------------------------------

'table' Type_id		(Pos		:	POS,
			 Ident		:	IDENT,
			 Qualifier	:	Object_ids,
			 Type		:	TYPE,
			 Def		:	TYPE_DEFINITION,
			 Subtype	:	OPT_FUN,
			 Coercions_up	:	COERCIONS,
			 Coercions_down	:	COERCIONS)

'type' TYPE
       undef_type
       sort	(SORT_KIND)
       abbrev	(TYPE_EXPR)

'type' SORT_KIND
       abstract
       record(COMPONENTS)
       variant(VARIANTS)
       union(CHOICES)

-- for resolved abbreviations
'type' TYPE_DEFINITION
       no_def
       abbreviation	(TYPE_EXPR)

'type' OPT_FUN

       nil
       funct		(Value_id)

'type' COERCION

        coercion	(Type_id,
			 COERCION)
	nil

'type' COERCIONS

        coercions	(COERCION,
			 COERCIONS)
	nil

'type' OPT_TYPE_ID

       type_id (Type_id)
       nil

'type' Type_ids

        list		(head		:	Type_id,
			 tail		:	Type_ids)
	nil

'action' New_type_id(POS, IDENT -> Type_id)

  'rule' New_type_id(P, Id -> New):
	 New::Type_id
	 New'Pos <- P
	 New'Ident <- Id
	 New'Qualifier <- nil
	 New'Def <- no_def
	 New'Subtype <- nil
	 New'Coercions_up <- nil
	 New'Coercions_down <- nil

'action' Copy_type_id(Type_id -> Type_id)

  'rule' Copy_type_id(I -> I1):
	 I1::Type_id
	 I'Pos -> Pos
	 I1'Pos <- Pos
	 I'Ident -> Ident
	 I1'Ident <- Ident
	 I'Qualifier -> Qualifier
	 I1'Qualifier <- Qualifier
	 I'Type -> Type
	 I1'Type <- Type
	 I'Def -> Def
	 I1'Def <- Def
	 I'Subtype -> Subtype
	 I1'Subtype <- Subtype
	 I'Coercions_up -> Coercions
	 I1'Coercions_up <- Coercions
	 I'Coercions_down -> Coercions1
	 I1'Coercions_down <- Coercions1

'table' Value_id	(Pos		:	POS,
			 Ident		:	ID_OR_OP,
			 Qualifier	:	Object_ids,
			 Type		:	TYPE_EXPR,
			 Def		:	VALUE_DEFINITION,
			 Type_alpha	:	FDR_FLAG_PROCESS_OPE,
			 Type_alpha_ltl	:	LTL_FLAG_PROCESS_OPE)

'type' OPT_VALUE_ID

       value_id (Value_id)
       nil

'type' Value_ids

        list		(head		:	Value_id,
			 tail		:	Value_ids)
	nil

-- for resolved definitions
'type' VALUE_DEFINITION

       no_def
       expl_val		(expr		:	VALUE_EXPR,
			 subtype	:	OPT_CONDITION)
       impl_val		(expr		:	VALUE_EXPR)
       expl_fun		(parms		:	FORMAL_FUNCTION_PARAMETERS,
			 expr		:	VALUE_EXPR,
			 post		:	OPT_POST_CONDITION,
			 pre		:	PRE_CONDITION,
			 subtype_args	:	OPT_CONDITION,
			 subtype_res	:	OPT_CONDITION)
       impl_fun		(parms		:	FORMAL_FUNCTION_PARAMETERS,
			 post		:	POST_CONDITION,
			 pre		:	PRE_CONDITION,
			 subtype_args	:	OPT_CONDITION)

'type' OPT_CONDITION

        condition	(expr		:	VALUE_EXPR)
	nil



'action' New_value_id(POS, ID_OR_OP -> Value_id)

  'rule' New_value_id(P, Id -> New):
	 New::Value_id
	 New'Pos <- P
	 New'Ident <- Id
	 New'Qualifier <- nil
	 New'Def <- no_def 
	 New'Type_alpha <-fdr_Access

'action' Copy_value_id(Value_id -> Value_id)

  'rule' Copy_value_id(I -> I1):
	 I1::Value_id
	 I'Pos -> Pos
	 I1'Pos <- Pos
	 I'Ident -> Ident
	 I1'Ident <- Ident
	 I'Qualifier -> Qualifier
	 I1'Qualifier <- Qualifier
	 I'Type -> Type
	 I1'Type <- Type
	 I'Def -> Def
	 I1'Def <- Def
	 I'Type_alpha -> TypeAlpha
	 I1'Type_alpha <- TypeAlpha

'table' Variable_id	(Pos		:	POS,
			 Ident		:	IDENT,
			 Qualifier	:	Object_ids,
			 Type		:	TYPE_EXPR,
			 Init		:	INITIALISATION,
			 Subtype	:	OPT_CONDITION)

'type' Variable_ids

        list		(head		:	Variable_id,
			 tail		:	Variable_ids)
	nil

'type' OPT_VARIABLE_ID

       variable_id (Variable_id)
       nil

'action' New_variable_id(POS, IDENT -> Variable_id)

  'rule' New_variable_id(P, Id -> New):
	 New::Variable_id
	 New'Pos <- P
	 New'Ident <- Id
	 New'Qualifier <- nil
	 New'Init <- nil 
	 New'Subtype <- nil 

'action' Copy_variable_id(Variable_id -> Variable_id)

  'rule' Copy_variable_id(I -> I1):
	 I1::Variable_id
	 I'Pos -> Pos
	 I1'Pos <- Pos
	 I'Ident -> Ident
	 I1'Ident <- Ident
	 I'Qualifier -> Qualifier
	 I1'Qualifier <- Qualifier
	 I'Type -> Type
	 I1'Type <- Type
	 I'Init -> Init
	 I1'Init <- Init
	 I'Subtype -> Subtype
	 I1'Subtype <- Subtype

'table' Channel_id	(Pos		:	POS,
			 Ident		:	IDENT,
			 Qualifier	:	Object_ids,
			 Type		:	TYPE_EXPR)

'type' Channel_ids

        list		(head		:	Channel_id,
			 tail		:	Channel_ids)
	nil

'type' OPT_CHANNEL_ID

       channel_id (Channel_id)
       nil

'action' New_channel_id(POS, IDENT -> Channel_id)

  'rule' New_channel_id(P, Id -> New):
	 New::Channel_id
	 New'Pos <- P
	 New'Ident <- Id
	 New'Qualifier <- nil 

'action' Copy_channel_id(Channel_id -> Channel_id) 

  'rule' Copy_channel_id(I -> I1):
	 I1::Channel_id
	 I'Pos -> Pos
	 I1'Pos <- Pos
	 I'Ident -> Ident
	 I1'Ident <- Ident
	 I'Qualifier -> Qualifier
	 I1'Qualifier <- Qualifier
	 I'Type -> Type
	 I1'Type <- Type

'table' Scheme_id	(Pos		:	POS,
			 Ident		:	IDENT,
			 Qualifier	:	Object_ids,
			 Params		:	MODULE_ENV,
			 Class		:	CLASS,
			 With		:	OBJECT_EXPRS,
			 Context	:	FILE_NAMES,
			 Env		:	CLASS_ENV)


'type' Scheme_ids

        list		(head		:	Scheme_id,
			 tail		:	Scheme_ids)
	nil

'type' OPT_SCHEME_ID

       scheme_id (Scheme_id)
       nil

'action' New_scheme_id(POS, IDENT, FILE_NAMES -> Scheme_id)

  'rule' New_scheme_id(P, Id, Cont -> New):
	 New::Scheme_id
	 New'Pos <- P
	 New'Ident <- Id
	 New'Qualifier <- nil
	 New'Context <- Cont 
	 New'Env <- nil 

'table' Object_id	(Pos		:	POS,
			 Ident		:	IDENT,
			 Qualifier	:	Object_ids,
			 Params		:	PARAM_TYPE,
			 Param_env	:	CLASS_ENV,
			 Env		:	CLASS_ENV)

'type' PARAM_TYPE

        param_type	(type		:	TYPE_EXPR)
	nil

'type' Object_ids

        list		(head		:	Object_id,
			 tail		:	Object_ids)
	nil

'type' OPT_OBJECT_ID

       object_id (Object_id)
       nil

'action' New_object_id(POS, IDENT -> Object_id)

  'rule' New_object_id(P, Id -> New):
	 New::Object_id
	 New'Pos <- P
	 New'Ident <- Id
	 New'Qualifier <- nil
	 New'Params <- nil
	 New'Param_env <- nil
	 New'Env <- nil 

'action' Copy_object_id(Object_id -> Object_id) 

  'rule' Copy_object_id(I -> I1):
	 I1::Object_id
	 I'Pos -> Pos
	 I1'Pos <- Pos
	 I'Ident -> Ident
	 I1'Ident <- Ident
	 I'Qualifier -> Qualifier
	 I1'Qualifier <- Qualifier
	 I'Params -> Params
	 I1'Params <- Params
	 I'Param_env -> Param_env
	 I1'Param_env <- Param_env
	 I'Env -> Env
	 I1'Env <- Env

'table' Axiom_id	(Pos		:	POS,
			 Ident		:	OPT_IDENT,
			 Axiom		:	VALUE_EXPR)

'action' New_axiom_id(POS, OPT_IDENT -> Axiom_id)

  'rule' New_axiom_id(P, OId -> New):
	 New::Axiom_id
	 New'Pos <- P
	 New'Ident <- OId
	 New'Axiom <- no_val

'table' Test_case_id	(Pos		:	POS,
			 Ident		:	OPT_IDENT,
			 Paths		:	PATHS,
			 Test_case	:	VALUE_EXPR,
			 Type		:	TYPE_EXPR)

'action' New_test_case_id(POS, OPT_IDENT, PATHS -> Test_case_id)

  'rule' New_test_case_id(P, OId, Paths -> New):
	 New::Test_case_id
	 New'Pos <- P
	 New'Ident <- OId
	 New'Paths <- Paths

'table' Theory_id	(Pos		:	POS,
			 Ident		:	IDENT,
			 Env		:	CLASS_ENV)

'action' New_theory_id(POS, IDENT -> Theory_id)

  'rule' New_theory_id(P, Id -> New):
	 New::Theory_id
	 New'Pos <- P
	 New'Ident <- Id


-- for Model Checking (SAL)
'table' Transition_system_id	(Pos		:	POS,
				 Ident		:	IDENT,
				 Paths		:	PATHS,
				 System		:	SYSTEM_DESCRIPTION,
				 -- Resolved
				 Trans_sys	:	RESOLVED_SYSTEM_DESCRIPTION)

'action' New_transition_system_id(POS, IDENT,  PATHS-> Transition_system_id)

  'rule' New_transition_system_id(P, OId, Paths -> New):
	 New::Transition_system_id
	 New'Pos <- P
	 New'Ident <- OId
	 New'Paths <- Paths
	 New'Trans_sys <- nil


'type' OPT_TRANS_SYS_ID

       ts_id (Transition_system_id)

       nil

'table' Property_id		(Pos		:	POS,
				 Ident		:	IDENT,
				 Paths		:	PATHS,
				 -- Resolved:
				 Resolved_Prop	:	RESOLVED_PROPERTY)

'action' New_property_id(POS, IDENT, PATHS -> Property_id)

  'rule' New_property_id(Pos, Ident, Paths -> New):
	 New::Property_id
	 New'Pos <- Pos
	 New'Ident <- Ident
	 New'Paths <- Paths
	 New'Resolved_Prop <- nil

'type' RESOLVED_PROPERTY

       r_prop(Pos	:	POS,
		 Ident	:	IDENT,
		 TS	:	Transition_system_id,
		 Prop	:	VALUE_EXPR)

       r_prop_csp(Pos	:	POS,
		 Ident	:	IDENT,
		 val    :	Value_id,
		 Prop	:	VALUE_EXPR)

       nil
-------------------------------------------------------------------
-- Environments
-------------------------------------------------------------------

'type' MODULE_ENV
        scheme_env	(Scheme_id,
			 MODULE_ENV)
        object_env	(Object_id,
 			 MODULE_ENV)
        theory_env	(Theory_id,
 			 MODULE_ENV)
	nil

'type' CURRENT_ENV

	current_env	(CLASS_ENV,
			 CURRENT_ENV)
	nil


'type' CLASS_ENV
 
       basic_env	(types		:	TYPE_ENV,
			 values		:	VALUE_ENVS,
			 variables	:	VARIABLE_ENV,
			 channels	:	CHANNEL_ENV,
			 modules	:	MODULE_ENV,
			 axioms		:	AXIOM_ENV,
			 test_cases	:	TEST_CASE_ENV,
			 trans_sys	:	TRANS_SYS_ENV,
			 properties	:	PROPERTY_ENV,
			 with		:	OBJECT_EXPRS,
			 adapts		:	ADAPTS)

        extend_env	(first		:	CLASS_ENV,
			 second		:	CLASS_ENV,
			 with		:	OBJECT_EXPRS,
			 adapts		:	ADAPTS)

	instantiation_env
			(fit		:	PARAM_FIT,
			 env		:	CLASS_ENV)

	nil

'type' TYPE_ENV
        type_env	(Type_id,
			 TYPE_ENV)
	nil

'type' VALUE_ENVS
        list		(Value_ids,
			 VALUE_ENVS)
	nil

'type' VARIABLE_ENV
        variable_env	(Variable_id,
			 VARIABLE_ENV)
	nil

'type' CHANNEL_ENV
        channel_env	(Channel_id,
			 CHANNEL_ENV)
	nil

'type' AXIOM_ENV

        axiom_env	(Axiom_id,
			 AXIOM_ENV)
	nil

'type' TEST_CASE_ENV

        test_case_env	(Test_case_id,
			 TEST_CASE_ENV)
	nil

'type' TRANS_SYS_ENV
       
       trans_sys_env	(Transition_system_id,
			 TRANS_SYS_ENV)
       nil

'type' PROPERTY_ENV
       
       prop_env		(Property_id,
			 PROPERTY_ENV)

       nil

'type' ADAPTS

        hide		(ID_OR_OP,
			 ADAPTS)
	rename		(new	:	ID_OR_OP,
			 old	:	ID_OR_OP,
			 ADAPTS)
	nil


------------------------------------------------------------------
-- Miscellaneous
------------------------------------------------------------------	

'type' FOUND
       found, nil

'type' OPT_ID_OR_OP

        id	(ID_OR_OP)
	nil

'type' INTS

        list	(INT,
		 INTS)
	nil

'type' CONSTANT_CONSTRUCTOR

       cons	(ID_OR_OP)
       cons_id	(Value_id)
       nil

-- OWNENV is used to tell if a lookup is still within the original
-- smallest class expression.  It is used to determine if names should
-- be adapted.
'type' OWNENV
       ownenv, nil

-- OWNCLASS is used to tell if a lookup is still within the original
-- class expression.  It is used to test if the lookup should continue
-- into an enclosing class when the current class is an instantiation.
'type' OWNCLASS
       ownclass, nil

'type' OPT_NAME

        act_name	(name	:	NAME)
	hidden		(obj	:	NAME)
	nil

'type' PATH
        left	(PATH)
	right	(PATH)
	nil

'type' PATHS
        list	(PATH,
		 PATHS)
	nil

'type' DIRECTION
       up, down, nil

--'type' PARAM_FITS

--        list	(PARAM_FIT,
--		 PARAM_FITS)
--	nil

'type' PARAM_FIT

        param_fit	(formal	:	Object_id,
			 actual_id:	Object_id,
			 actual	:	OBJECT_EXPR,
			 fitting:	ADAPTS,
			 PARAM_FIT)
	no_parms
	nil

'type' TYPE_NUMBERS
        list	(TYPE_NUMBER,
		 TYPE_NUMBERS)
	nil

'type' TYPE_NUMBER
        type_number	(Type_id,
			 INT,
			 TYPE_NUMBER)
	nil

'type' RESULTS

        list		(head	:	RESULT,
			 tail	:	RESULTS)
	nil

'type' RESULT

        result		(type	:	TYPE_EXPR,
			 read	:	ACCESSES,
			 write	:	ACCESSES,
			 in	:	ACCESSES,
			 out	:	ACCESSES)

'type' ACCS

        accesses	(ACC,
			 ACCS)
	nil

'type' ACC

        free
	any
	qualany		(OBJECT_EXPR)
	variable	(Variable_id, OPT_QUALIFICATION)
	channel		(Channel_id, OPT_QUALIFICATION)
	nil

'type' READONLY

       readonly
       nil

'type' MODULE_CATEGORY

       top
       lower

'type' IN_ARRAY

       in_array
       nil

'type' ALL_TOP

       all, top


'type' IMP_FIT

       imp_fit		(type_fits	:	TYPE_FITS,
			 value_fits	:	VALUE_FITS,
			 variable_fits	:	VARIABLE_FITS,
			 channel_fits	:	CHANNEL_FITS,
			 object_fits	:	OBJECT_FITS)

'type' TYPE_FITS

       type_fit		(old		:	Type_id,
			 new		:	OPT_TYPE_ID,
			 rest		:	TYPE_FITS)
       nil

'type' VALUE_FITS

       value_fit	(old		:	Value_id,
			 new		:	OPT_VALUE_ID,
			 rest		:	VALUE_FITS)
       nil

'type' VARIABLE_FITS

       variable_fit	(old		:	Variable_id,
			 new		:	OPT_VARIABLE_ID,
			 rest		:	VARIABLE_FITS)
       nil

'type' CHANNEL_FITS

       channel_fit	(old		:	Channel_id,
			 new		:	OPT_CHANNEL_ID,
			 rest		:	CHANNEL_FITS)
       nil

'type' OBJECT_FITS

       object_fit	(old		:	Object_id,
			 new		:	OPT_OBJECT_ID,
			 kind		:	OBJECT_FIT_KIND,
			 rest		:	OBJECT_FITS)
       nil

'type' OBJECT_FIT_KIND

       form_act, embedded

'type' OPT_POS

       pos(POS)
       no_pos

'type' HIDE

       hide, no_hide


-------------------------------------------------------------------------
-- Pretty Printing
-------------------------------------------------------------------------

'type' BOX

       box		(start	:	STRING,
			 boxes	:	BOXES,
			 sep	:	STRING,
			 end	:	STRING,
			 typ	:	BOX_TYPE)
       string		(str	:	STRING)
       block_comm	(s	:	STRING,
			 f_type :	INT,
			 b_type :	INT)
       line_comm	(s	:	STRING,
			 s_type :	INT) 

'type' BOXES

       list		(head	:	BOX,
			 tail	:	BOXES)
       nil

'type' BOX_TYPE

       v_box
       h_box
       i_box
       hv_box
       hov_box

'type' INTE_REP

       combine		(left	:	INTE_REP,
			 right	:	INTE_REP)
       at		(str	:	STRING,
			 pos	:	POSN,
			 len	:	INT)
       inden		(IR	:	INTE_REP)
       adjust		(IR	:	INTE_REP,
			 P	:	POSN)
       nil	

'type' POSN

       coord		(line	:	INT,
			 col	:	INT)
       
-------------------------------------------------------------------------
-- Dependency graph
-------------------------------------------------------------------------

'type' DEPENDENCY

        dependency	(module	:	IDENT,
			 kind	:	MODULE_KIND,
			 deps	:	IDENTS,
			 rest	:	DEPENDENCY)
	nil

'type' MODULE_KIND

       scheme
       object
       theory
       devt_relation

-------------------------------------------------------------------------
-- Coverage
-------------------------------------------------------------------------

'type' REGION

       region		(start	:	POS,
			 finish	:	POS)

'type' REGIONS

       list		(head	:	REGION,
			 tail	:	REGIONS)

       nil

---------------------------------------------------------------------------
-- Transition systems description
---------------------------------------------------------------------------

'type' SYSTEM_DESCRIPTION

       desc	(InputVarDecls	:	DECL,		-- only variable_decls are allowed here!
		 LocalVarDecls	:	DECL,		-- here too!
                 --GreaterPriorities:	int,
		 Transition	:	TRANSITION_OPERATOR)

       no_input (LocalVarDecls	:	DECL,		-- here too!
                 --GreaterPriorities:	int,
		 Transition	:	TRANSITION_OPERATOR)

       nil

'type' RESOLVED_SYSTEM_DESCRIPTION

       desc	(InputVarDecls	:	DECL,		-- only variable_decls are allowed here!
		 LocalVarDecls	:	DECL,		-- here too!
		 PrimedInput	:	DECL,
		 PrimedLocal	:	DECL,
		 Transition	:	TRANSITION_OPERATOR,
                 ExtraProps	:	EXTRA_ASSERTION)

      no_input	(LocalVarDecls	:	DECL,		-- here too!
		 PrimedLocal	:	DECL,
		 Transition	:	TRANSITION_OPERATOR,
                 ExtraProps	:	EXTRA_ASSERTION)
       

       nil

/*'type' TRANSITION_SETS

	list	(head	:	GUARDED_COMMANDS,
		tail	:	TRANSITION_SETS)

	nil*/

'type' TRANSITION_OPERATOR

	equal_priority	(left	:	TRANSITION_OPERATOR,
			right	:	TRANSITION_OPERATOR,
			guard	:	EXTRA_GUARD)

	greater_priority	(left	:	TRANSITION_OPERATOR,
			right	:	TRANSITION_OPERATOR,
			guard	:	EXTRA_GUARD)

	bracketed	(operator	:	TRANSITION_OPERATOR,
			guard	:	EXTRA_GUARD)

	guarded_command(command : 	GUARDED_COMMAND,
			guard	:	EXTRA_GUARD)

	/*guarded_commands	(commands	:	GUARDED_COMMANDS,
				guard	:	EXTRA_GUARD)*/

-- Used for storing the guards of a set of transitions. Used for priorities
'type' EXTRA_GUARD 

	guard 	(val	:	VALUE_EXPR,
		pos	: 	POS)

	nil

'type' EXTRA_ASSERTION
	assertion(expr	:	VALUE_EXPR)

	nil


/*'type' GUARDED_COMMANDS

       list	(head	:	GUARDED_COMMAND,
		 tail	:	GUARDED_COMMANDS)
       nil*/

'type' GUARDED_COMMAND

       guarded_cmd	(opt_desc	:	OPT_IDENT,
			 guard		:	VALUE_EXPR,	-- Has to be a boolean expr!
			 commands	:	COMMANDS)
		 

       else_cmd		(opt_desc	:	OPT_IDENT,
			 commands	:	COMMANDS)

       comprehended_cmd (typings	:	TYPINGS,
			 pos		:	POS,
			 cmd		:	GUARDED_COMMAND)

'type' COMMANDS

       list	(head	:	COMMAND,
		 rest	:	COMMANDS)

       nil

'type' COMMAND

       cmd	(pos		:	POS,
		 name		:	NAME,
		 update_expr	:	VALUE_EXPR)

       array_cmd	(pos	:	POS,
			name	:	NAME,
			indexes	:	VALUE_EXPRS,
			update_expr:	VALUE_EXPR)

       r_cmd    (update		:	VALUE_EXPR) -- resolved: in practice an ass_occ


--------------------------------------------------------
'type' LTL_PROPERTY
/*
       ltl_prop		(ltl_op		:	OP,  -- LTL op
			 prop		:	LTL_PROPERTY)

       quantif_prop	(ltl_op		:	VALUE_EXPR,  --quantif_expr
			 prop		:	LTL_PROPERTY)

       imply_prop	(antecedent	:	VALUE_EXPR,
			 consequent	:	LTL_PROPERTY)
*/
       prop		(VALUE_EXPR)
