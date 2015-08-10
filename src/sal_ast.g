-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the abstract syntax for SAL
-- plus some auxiliary types


'module' sal_ast


'use' ast print ext env objects values types pp cc
      sal	  -- SAL_Current_Cid (global var)
      sal_aux     -- SAL_Concatenate_Context_Args
      sal_gen_ast -- SAL_Global_Cid
      sal_global_vars
      sal_cc_aux
      sal_print

'export'
	SAL_MODEL
   -- CONTEXT:	
	SAL_CONTEXTS
	SAL_CONTEXT
	SAL_CONTEXT_CONSTANTS
	SAL_CONTEXT_CONSTANT

	MACRO_CONSTANTS
	MACRO_CONSTANT	

	SAL_CONSTANT_DECLS
	SAL_CONSTANT_DECL
	SAL_RECURSIVE
	SAL_RECURSIVE_SUBTYPE
	SAL_FORMAL_FUN_PARAMETERS
	SAL_FORMAL_FUN_PARAMETER
   -- CONTEXT decls:
	SAL_VAR_DECLS
	SAL_VAR_DECL
	SAL_INITIALIZATIONS
	SAL_INITIALIZATION
	SAL_TRANSITIONS
	SAL_TRANSITION
   -- TYPE system:
        SAL_TYPE_DECL_CLASS
	SAL_TYPE_LIST
	SAL_BASIC
	SAL_TYPE_EXPRS
	SAL_TYPE_EXPR
	RSL_BUILTIN_TYPE
	USER_DEFINED_TYPE
	TYPE_REFERENCES
	EXPR_CONTEXT
	UNFOLD_SUBTYPES
	NUM_ARG
	SAL_LIST_TYPES
	SAL_LIST_TYPE
	SAL_FIXED_POINT_STATUS
	SAL_CONTEXT_ARGS
	SAL_CONTEXT_ARG
	SAL_TUPLE_ELEMS
	SAL_TUPLE_ELEM
	SAL_FIELD_DECLS
	SAL_FIELD_DECL
	SAL_DATA_TYPE_PARTS
	SAL_DATA_TYPE_PART
	SAL_CONSTRUCTOR
	SAL_DESTRUCTORS
	SAL_DESTRUCTOR
	SAL_RECONSTRUCTORS
	SAL_RECONSTRUCTOR
  -- SAL expressions:
	SAL_VALUE_EXPRS
	SAL_VALUE_EXPR
	SAL_MACRO_EXPR
	SAL_VALUE_LITERAL
	SAL_NAME
	SAL_OBJ_QUALIF
	SAL_SET_BINDING
	SAL_BINDINGS  
	SAL_BINDING  
	SAL_LIST_LIMIT
	SAL_VALUE_EXPR_PAIRS
	SAL_VALUE_EXPR_PAIR
	SAL_LAMBDA_BINDINGS
	SAL_LAMBDA_BINDING
	SAL_ARGS
	SAL_BINDING_OP
	SAL_LOGIC_CONNECTIVE
	SAL_LET_BINDINGS
	SAL_LET_BINDING
	SAL_LETBINDS 
	SAL_LETBIND  
	BINDING_NAMESPACE_STACK
	BINDING_NAMESPACE
	BINDING_ELEM
	REMAINING_BINDINGS
	REMAINING_BINDING
	SAL_ELSIF_BRANCHES
	SAL_ELSIF_BRANCH
	SAL_ELSE_BRANCH
	SAL_VALUE_ID
	SAL_ID_OP
	SAL_OP
	SAL_INFIX_OP
	SAL_PREFIX_OP
	SAL_FUNCTION_OP
	
	-- cc
	SAL_RESTRICTIONS
	SAL_RESTRICTION
-- Misc
	VAR_DECL_TYPE
	CID_STACK
	CONSTANT_DATA_LIST
	CONSTANT_DATA


-- Auxiliary decls for sorting:
	SORTED_DECLS_S
	SORTED_DECLS
	SORTED_DECL_ITEM
	

	OPT_CONTEXT_ID

	SAL_TYPE_IDS
	OPT_SAL_TYPE_ID

	SAL_VALUE_IDS
	OPT_SAL_VALUE_ID

	SAL_OBJECT_IDS
	OPT_SAL_OBJECT_ID

	SAL_VARIABLE_IDS
	OPT_SAL_VARIABLE_ID	

	SAL_TRANSYS_IDS
	OPT_SAL_TRANSYS_ID

	-- used to distinguish functions (RSL_is_in_<> against all others)
	SAL_IS_IN_VALUE

-- Identifiers:
	SAL_CONTEXT_IDS
	SAL_context_id
	SAL_type_id
	SAL_value_id
	-- Vid type:
	   VALUE_TYPE
	SAL_object_id
	-- variables
	SAL_variable_id
	-- transition systems
	SAL_TranSys_id

-- Functions:
   -- For Cids:
	Init_SAL_AST
	add_tid_to_global
        New_SAL_context_id
	New_SAL_single_context_id
	New_SAL_unnamed_context_id
	Collect_Tid_in_Cid
	Extend_Static_in_Cid_Decls
	Extend_Static_in_Cid_Decl
	Extend_State_in_Cid_Decls
	Extend_State_in_Cid
	Remove_Decl_from_Static
	LookUp_Context
   -- For Tids:
	New_SAL_type_id
	New_SAL_type_id_with_Cid
	New_SAL_NAV_type_id
	Extend_Decl_Cid_in_Tid
	Update_Ident_in_Tid
	Update_Cid_in_Tid
	Update_Args_in_Tid
	Update_Macro_in_Tid
	look_up_type_id
	add_tid_to_lifted_global
   -- For Vids:
	New_SAL_value_id
	New_UnRegistered_Vid	
	Update_Cid_in_Vid
	Extend_Decl_Cid_in_Vid	
	New_SAL_special_value_id
	look_up_value_id
	SAL_Remove_Vid_from_Globals
   -- For Oids:
	New_SAL_object_id		
	look_up_object_id	
	ident_oid_look_up
   -- For variables:
	New_SAL_variable_id		
	look_up_variable_id
   -- For Transition Systems:
        New_SAL_TranSys_id
        look_up_TranSys_id

-----------------------------------------------------------------------------
-- SAL Abstract Syntax
-----------------------------------------------------------------------------
'type' SAL_MODEL

       model	(SAL_CONTEXTS)

'type' SAL_CONTEXTS

       list	(head	: SAL_CONTEXT,
		 tail	: SAL_CONTEXTS)

       nil


'type' SAL_CONTEXT

       context		(ident	:	IDENT,
			 cid	:	OPT_CONTEXT_ID,
			 elems 	:	SAL_CONTEXT_CONSTANTS)

       macro_context    (ident	:	IDENT,
			 cid	:	OPT_CONTEXT_ID,
			 elems 	:	MACRO_CONSTANTS)

       nil	
-----------------------------------------------------------------------------

'type'	SAL_CONTEXT_CONSTANTS

	list		(head	:	SAL_CONTEXT_CONSTANT,
			 tail	:	SAL_CONTEXT_CONSTANTS)
	nil	


-----------------------------------------------------------------------------

'type'	SAL_CONTEXT_CONSTANT

	sal_type_decl		(id	:	IDENT,
				 Tid	:	SAL_type_id,
				 type	:	SAL_TYPE_EXPR)

	sal_object_decl		(id	:	IDENT,
				 pos	:	POS,
				 oid	:	SAL_object_id,
			-- Used for class attributes (vars) if any:
				 state	:	SAL_CONTEXT_CONSTANTS,
			-- Used for methods and type decls:
				 comp	:	SAL_CONTEXT_CONSTANTS)


	sal_const_decl		(SAL_CONSTANT_DECL)
				 
	assertion_decl		(pos		:	POS,
				 id		:	IDENT,
				 module_ref	:	SAL_TranSys_id,
				 body		:	SAL_VALUE_EXPR)
	
	module_decl		(id		:	IDENT,
				 TS_Id		:	SAL_TranSys_id,
				 input_decls	:	SAL_VAR_DECLS,
				 local_decls	:	SAL_VAR_DECLS,
				 initialization	:	SAL_INITIALIZATIONS,
				 transition	:	SAL_TRANSITIONS)
	nil

'type' MACRO_CONSTANTS

       list	(head	:	MACRO_CONSTANT,
		 tail	:	MACRO_CONSTANTS)

       nil

'type' MACRO_CONSTANT

	-- used for generating files that will be expanded later with the macro processor:
	macro_set_cmd		(Tid		:	SAL_type_id,
				 element_type	:	SAL_TYPE_EXPR)

	macro_map_cmd		(Tid		:	SAL_type_id,
				 element_type	:	SAL_TYPE_EXPR,
				 OpsdomSet	:	SAL_context_id,
				 OpsrngSet	:	SAL_context_id,
				 domSetTid	:	SAL_type_id,
				 rngSetTid	:	SAL_type_id)

	macro_array_cmd		(Tid		:	SAL_type_id,
				 element_type	:	SAL_TYPE_EXPR,
				 OpsdomSet	:	SAL_context_id,
				 OpsrngSet	:	SAL_context_id,
				 domSetTid	:	SAL_type_id,
				 rngSetTid	:	SAL_type_id)

	macro_int_cmd		(Tid		:	SAL_type_id)

	-- cc counterparts:
	macro_cc_set_cmd	(Tid		:	SAL_type_id,
				 -- non-lifted
				 element_type	:	SAL_TYPE_EXPR,
				 -- lifted
				 lifted_el_type	:	SAL_TYPE_EXPR)

	macro_cc_map_cmd	(MapTid		:	SAL_type_id,
				 domTid		:	SAL_type_id,
				 rngTid		:	SAL_type_id,
				 domSetTid	:	SAL_type_id,
				 rngSetTid	:	SAL_type_id,
				 invApplVid	:	SAL_value_id,
				 dom		:	SAL_TYPE_EXPR,
                                 rng		:	SAL_TYPE_EXPR,
				 maxdom		:	SAL_TYPE_EXPR,
				 maxrng		:	SAL_TYPE_EXPR,
				 MapRangeTid	:	SAL_type_id)

	macro_cc_array_cmd	(MapTid		:	SAL_type_id,
				 domTid		:	SAL_type_id,
				 rngTid		:	SAL_type_id,
				 domSetTid	:	SAL_type_id,
				 rngSetTid	:	SAL_type_id,
				 invApplVid	:	SAL_value_id,
				 dom		:	SAL_TYPE_EXPR,
                                 range		:	SAL_TYPE_EXPR,
				 maxdom		:	SAL_TYPE_EXPR,
				 maxrng		:	SAL_TYPE_EXPR)

	macro_int_cc_cmd	(Int_Tid	:	SAL_type_id,
				 Bool_Tid	:	SAL_type_id,
				 div_by_zero	:	SAL_value_id)

	macro_bool_cc_cmd	(Tid		:	SAL_type_id)
	
	macro_type_cc_cmd	(Tid		:	SAL_type_id)
------------------------------------------------------------------
-- Additional defs:
------------------------------------------------------------------
'type' SAL_CONSTANT_DECLS
       
       list			(head	:	SAL_CONSTANT_DECL,
				 tail	:	SAL_CONSTANT_DECLS)
       
       nil


'type' SAL_CONSTANT_DECL

       	sal_nodef	(ids		:	SAL_ID_OP,
			 type_expr	:	SAL_TYPE_EXPR,
			 containing	:	SAL_VALUE_EXPR)

	sal_expl_const	(ids		:	SAL_ID_OP,
			 Vid		:	SAL_value_id,
			 type_expr	:	SAL_TYPE_EXPR,
			 containing	:	SAL_VALUE_EXPR)

	sal_fun_const	(id			:	SAL_ID_OP,
			 Vid			:	SAL_value_id,
			 recursive		:	SAL_RECURSIVE,
			 params			:	SAL_FORMAL_FUN_PARAMETERS,
			 resultType		:	SAL_TYPE_EXPR,
			 namespace		:	BINDING_NAMESPACE,
			 expr			:	SAL_VALUE_EXPR,
			 WFC_violation_Vid	:	OPT_SAL_VALUE_ID)

	sal_param_decl  (constans	:	SAL_CONSTANT_DECLS,
			 type		:	SAL_type_id)
			 	
	nil

'type' SAL_RECURSIVE

       sal_recursive

       nil  


'type' SAL_RECURSIVE_SUBTYPE

       sal_recursive_subtype

       nil 


'type' SAL_FORMAL_FUN_PARAMETERS

       list		(head	:	SAL_FORMAL_FUN_PARAMETER,
			 tail	:	SAL_FORMAL_FUN_PARAMETERS)
       nil	

'type' SAL_FORMAL_FUN_PARAMETER

       formal_param	(Id	:	IDENT,
			 type	:	SAL_TYPE_EXPR,
			 origType:	TYPE_EXPR) -- Used for
						   -- matching when
						   -- binding with actuals
						   

'type' SAL_VAR_DECLS
       
       list		(head	:	SAL_VAR_DECL,
			 tail	:	SAL_VAR_DECLS)
       nil

'type' SAL_VAR_DECL
       var_decl		(pos	:	POS,
			 id	:	IDENT,
			 VarId	:	SAL_variable_id,
			 type	:	SAL_TYPE_EXPR)       

'type' SAL_INITIALIZATIONS

       list		(head	:	SAL_INITIALIZATION,
			 tail	:	SAL_INITIALIZATIONS)
       nil

'type' SAL_INITIALIZATION
       
       init		(VarId		:	SAL_variable_id,
       			 value		:	SAL_VALUE_EXPR)

'type' SAL_TRANSITIONS

       list		(head	:	SAL_TRANSITION,
			 tail	:	SAL_TRANSITIONS)
       nil

'type' SAL_TRANSITION
       
       transition	(optIdent	:	OPT_IDENT,
			 guard		:	SAL_VALUE_EXPR,
			 commands       :	SAL_VALUE_EXPRS)

       else_trans	(optIdent	:	OPT_IDENT,
			 commands       :	SAL_VALUE_EXPRS)

       comprehended     (bindings	:	SAL_BINDINGS,
			 pos		:	POS,
			 trans		:	SAL_TRANSITION)

       cc_comprehended  (bindings	:	SAL_BINDINGS,
			 let		:	SAL_VALUE_EXPR)

nil

'type' VAR_DECL_TYPE
       
       local,
       input,
       comprehended

'type' CID_STACK

       list	(cid	:	SAL_context_id,
		 tail	:	CID_STACK)

       nil
	
'type' CONSTANT_DATA_LIST
       
       list	(head	:	CONSTANT_DATA,
		 rest	:	CONSTANT_DATA_LIST)

       nil

'type' CONSTANT_DATA

       info	(vid	:	SAL_value_id,
		 type	:	SAL_type_id)
------------------------------------------------------------------
-- SAL TYPE SYSTEM...
------------------------------------------------------------------
'type'  SAL_TYPE_DECL_CLASS
	
	top_level,
	internal_level
	


'type'  SAL_TYPE_LIST

	list		(head	:	TYPE_EXPR,
			 rest	:	SAL_TYPE_LIST)

	nil


'type'  SAL_BASIC
	
	sal_integer
	sal_boolean

	sal_rectricted_integer	(lowerLimit	:	SAL_VALUE_EXPR,
				 upperLimit	:	SAL_VALUE_EXPR)

	sal_type		 -- used in type-parametrized context

	sal_total_function	(Domain	 :  SAL_TYPE_EXPR,
				 Range	 :  SAL_TYPE_EXPR)

	sal_array	(Domain	 :  SAL_TYPE_EXPR,
				 Range	 :  SAL_TYPE_EXPR)

'type'	SAL_TYPE_EXPRS

	list		(head	:	SAL_TYPE_EXPR,
			 tail	:	SAL_TYPE_EXPRS)
	nil


'type'	SAL_TYPE_EXPR

	rsl_built_in	(RSL_BUILTIN_TYPE)
	
	user_defined	(USER_DEFINED_TYPE)

	type_refs	(TYPE_REFERENCES)
	
	sal_basic	(SAL_BASIC)

	unsupported_type	

	poly

        lifted_int

	nil


'type' RSL_BUILTIN_TYPE

	boolean		(Tid		:	SAL_type_id)

	integer		(Tid		:	SAL_type_id)

	natural		(Tid		:	SAL_type_id)

	unit

	sal_finite_set	(Tid		:	SAL_type_id,
			 Type		:	SAL_TYPE_EXPR)

	sal_list_type	(Tid		:	SAL_type_id,
			 ElemsType	:	SAL_TYPE_EXPR)

	sal_finite_map	(Tid		:	SAL_type_id,
			 dom		:	SAL_TYPE_EXPR,
			 rng		:	SAL_TYPE_EXPR)

        sal_array	(Tid		:	SAL_type_id,
			 dom		:	SAL_TYPE_EXPR,
			 rng		:	SAL_TYPE_EXPR)


'type' USER_DEFINED_TYPE

        sal_tuple_type	(SAL_TUPLE_ELEMS)

	sal_abbrev	(type		:	SAL_TYPE_EXPR)

	sal_fun_type	(domain		:	SAL_TYPE_EXPR,
			 result		:	SAL_TYPE_EXPR)

	sal_ranged_type (left		:	SAL_VALUE_EXPR,
			 right		:	SAL_VALUE_EXPR)	

        sal_scalar_type (ids		:	SAL_VALUE_IDS)	

	sal_subtype	(id		:	SAL_ID_OP,
			 type		:	SAL_TYPE_EXPR,
			 namespace	:	BINDING_NAMESPACE,
			 restriction	:	SAL_VALUE_EXPR)

	sal_record_type	(SAL_DATA_TYPE_PARTS) --(SAL_FIELD_DECLS)

	sal_variant_type(SAL_DATA_TYPE_PARTS)

	sal_bracket_type(SAL_TYPE_EXPR)

	-- Not allowed, for error recovery only...
	sal_sort	(Tid		:	SAL_type_id)

	-- for cc only:
	sal_cc_type	(LiftedType	:	SAL_TYPE_EXPR,
			 OrigType	:	TYPE_EXPR)

'type' TYPE_REFERENCES
	
	-- REFERENCES TO ABBREVIATIONS ONLY!
	sal_defined	(pos	        :       POS,
			 ident		:	IDENT,
			 referredTid	:	SAL_type_id)



'type' EXPR_CONTEXT

       normal,
       argument


'type' UNFOLD_SUBTYPES
       yes,
       no

'type'	SAL_TUPLE_ELEMS

	list		(head	:	SAL_TUPLE_ELEM,
			 tail	:	SAL_TUPLE_ELEMS)
	nil	


'type'	SAL_TUPLE_ELEM

	sal_tuple		(SAL_TYPE_EXPR)

	nil

'type'	SAL_FIELD_DECLS

	list		(head	:	SAL_FIELD_DECL,
			 tail	:	SAL_FIELD_DECLS)

	nil	

'type'	SAL_FIELD_DECL

	field		(id		:	IDENT,
        -- As types can be moved, the fields in the record must have a
	-- value id (global) in order to enable proper look-up when
	-- the field name is used in other contexts (require context
	-- qualif that, generally, does not match with the qualif used
	-- in RSL)
			 vid		:	SAL_value_id,
			 type_expr	:	SAL_TYPE_EXPR)

	nil

'type' SAL_DATA_TYPE_PARTS


	list		(head	:	SAL_DATA_TYPE_PART,
			 tail	:	SAL_DATA_TYPE_PARTS)

	nil	


'type' SAL_DATA_TYPE_PART

       sal_part		(const	:	SAL_CONSTRUCTOR,
			 type	:	SAL_TYPE_EXPR)



----------
'type' SAL_CONSTRUCTOR

       sal_construc	(idop		: SAL_ID_OP,
			 vid		: SAL_value_id,
			 acc		: SAL_DESTRUCTORS,
			 reconstructor	: SAL_RECONSTRUCTORS)


'type' SAL_DESTRUCTORS


	list		(head	:	SAL_DESTRUCTOR,
			 tail	:	SAL_DESTRUCTORS)

	nil	


'type' SAL_DESTRUCTOR

       sal_destructor	(idops		: SAL_ID_OP,
			 Vid		: SAL_value_id,
			 type		: SAL_TYPE_EXPR,
			 OriginalType	: TYPE_EXPR)

'type' SAL_RECONSTRUCTORS

       list		(head	:	SAL_RECONSTRUCTOR,
			 tail	:	SAL_RECONSTRUCTORS)

       nil

'type' SAL_RECONSTRUCTOR

       sal_reconstructor (idops		:	SAL_ID_OP,
			  Vid		:	SAL_value_id,
			  type		:	SAL_TYPE_EXPR,
			  origType	:	TYPE_EXPR,
			  asoc_pos	:	POS)
------------------------------------------------------------------
-- SAL expressions...
------------------------------------------------------------------

'type'	SAL_VALUE_EXPRS

	list		(head	:	SAL_VALUE_EXPR,
			 tail	:	SAL_VALUE_EXPRS)
	nil	


'type'	SAL_VALUE_EXPR

	unit

        sal_literal		(lit	:	SAL_VALUE_LITERAL)

	sal_resolved_literal	(lit	:	SAL_VALUE_LITERAL,
				 tid	:	SAL_type_id)

	sal_named_val		(name	:	SAL_NAME)

	sal_product		(exprs	:	SAL_VALUE_EXPRS)

	sal_ranged_set		(left	:	SAL_VALUE_EXPR,
				 right	:	SAL_VALUE_EXPR,
                                 domtype	:	SAL_TYPE_EXPR)

	sal_ranged_cc_set	(id		:	IDENT,
				 type		:	SAL_TYPE_EXPR,
				 elemtype	:	SAL_TYPE_EXPR,
				 restriction	:	SAL_VALUE_EXPR,
                                 dom_type	:	SAL_TYPE_EXPR)

	sal_enum_set		(Tid	:	SAL_type_id,
				 Expr	:	SAL_TYPE_EXPR,
				 exprs	:	SAL_VALUE_EXPRS)

	sal_comp_simp_set	(setbinding	:	SAL_SET_BINDING,
				 restric_expr	:	SAL_VALUE_EXPR)

	sal_comp_set		(expr		:	SAL_VALUE_EXPR,
				 type_expr	:	SAL_TYPE_EXPR,
				 setbinding	:	SAL_SET_BINDING,
				 restric_expr	:	SAL_VALUE_EXPR)

	sal_comp_cc_set		(id		:	IDENT,
				 type_expr	:	SAL_TYPE_EXPR,
				 setbinding	:	SAL_SET_BINDING,
				 restric_expr	:	SAL_VALUE_EXPR)

	sal_ranged_list		(left	:	SAL_VALUE_EXPR,
				 right	:	SAL_VALUE_EXPR)

	sal_enum_list		(exprs	:	SAL_VALUE_EXPRS)

	sal_comp_list		(expr	:	SAL_VALUE_EXPR,
				 limit	:	SAL_LIST_LIMIT)

	sal_enum_map		(Tid	:	SAL_type_id,
				 Dom	:	SAL_TYPE_EXPR,
				 Rng	:	SAL_TYPE_EXPR,
				 exprs	:	SAL_VALUE_EXPR_PAIRS)

	sal_comp_rng_map	(rng_expr	:	SAL_VALUE_EXPR,
				 rngtid		:	SAL_value_id,
				 niltid		:	SAL_value_id,
				 setbinding	:	SAL_SET_BINDING,
				 restric_expr	:	SAL_VALUE_EXPR)

	sal_comp_map		(expr_pair	:	SAL_VALUE_EXPR_PAIR,
				 tid		:	SAL_type_id, -- the Tid of the map type
				 setbinding	:	SAL_SET_BINDING,
				 restric_expr	:	SAL_VALUE_EXPR)

	sal_function		(lambdabindings	:	SAL_LAMBDA_BINDINGS,
				 expr		:	SAL_VALUE_EXPR)

	sal_list_applic		(list	:	SAL_VALUE_EXPR,
				 args	:	SAL_ARGS)

	sal_map_applic		(MapTid	:	SAL_type_id,
				 map	:	SAL_VALUE_EXPR,
				 args	:	SAL_ARGS)

	sal_cc_map_applic	(MapTid	:	SAL_type_id,
				 map	:	SAL_VALUE_EXPR,
				 args	:	SAL_ARGS)

	sal_funct_applic	(fun	:	SAL_VALUE_EXPR,
				 args	:	SAL_ARGS)

	sal_destr_applic	(recordName	:	SAL_VALUE_EXPR,
				 destr		:	SAL_VALUE_EXPR)

	sal_quantified		(binding_op	:	SAL_BINDING_OP,
				 setbinding	:	SAL_SET_BINDING,
				 restriction	:	SAL_VALUE_EXPR)

	sal_ranged_set_quantified	(binding_op	:	SAL_BINDING_OP,
				 	setbinding	:	SAL_SET_BINDING,
				 	restriction	:	SAL_VALUE_EXPR)

	sal_equivalence		(left	:	SAL_VALUE_EXPR,
				 right	:	SAL_VALUE_EXPR,
				 pre	:	SAL_VALUE_EXPR)

	sal_bracket		(expr	:	SAL_VALUE_EXPR)

        sal_array_expr		(sub	:	SAL_BINDINGS,
                                 type	:	SAL_TYPE_EXPR,
				 val	:	SAL_VALUE_EXPR)

        sal_array_access	(name	:	SAL_VALUE_EXPR,
				 index	:	SAL_VALUE_EXPR)

        sal_cc_array_access	(name	:	SAL_VALUE_EXPR,
				 index	:	SAL_VALUE_EXPR,
				 type_id:	SAL_type_id)


	-- This functor is used for built-in RSL operators (like
	-- equal). The idea of separating them from the normal
	-- functions is based on:
	--    a) Future need for model-checking preconditions and type
	--	 wellformedness	
	--    b) Infix operators when the lifted type system is not in
	--	 use can be replaced by SAL built-in operators.   
	sal_funct_expr		(op	:	SAL_VALUE_ID,
				 qualif	:	SAL_OBJ_QUALIF,
				 expr1	:	SAL_VALUE_EXPR,
				 expr2	:	SAL_VALUE_EXPR)  
				 -- Consider including the type here! 

	sal_ax_infix		(left	:	SAL_VALUE_EXPR,
				 idop	:	SAL_LOGIC_CONNECTIVE,
				 right	:	SAL_VALUE_EXPR)

	sal_ax_prefix		(conn	:	SAL_LOGIC_CONNECTIVE,
				 expr	:	SAL_VALUE_EXPR) 

	sal_let_expr		(ident	:	IDENT,
				 type	:	SAL_TYPE_EXPR,
				 names	:	BINDING_NAMESPACE,
				 defs	:	SAL_LET_BINDINGS, -- kept here for compatible and possible future need...
				 init	:	SAL_VALUE_EXPR,
				 expr	:	SAL_VALUE_EXPR)

	sal_esp_let_expr	(ident	:	IDENT,
				 type	:	SAL_TYPE_EXPR,
				 init	:	SAL_VALUE_EXPR,
				 body	:	SAL_TRANSITION)

	sal_if_expr		(expr	:	SAL_VALUE_EXPR, 
				 then	:	SAL_VALUE_EXPR,
				 elsif	:	SAL_ELSIF_BRANCHES,
				 else	:	SAL_ELSE_BRANCH)

	-- Used for local bindings and other kind
	-- of introduced names (local,reduced scope)
	sal_value_occ		(valid	:	SAL_VALUE_ID,
				 qualif	:	SAL_OBJ_QUALIF)

	-- Used for ocurrences of CONSTANT ELEMENTS like:
	--   Functions (globally available)
	--   Type constructors
	--   Type reconstructors
	--   Type destructors
	--   Constants (also global)
	sal_esp_value_occ       (Vid	:	SAL_value_id)


	-- used for record patterns (in cases)
	-- It is needed because, even though is a function, it must be handled differently
	sal_recogniser		(Vid	:	SAL_value_id,
				 arg	:	SAL_ARGS)

	sal_infix_occ		(left	:	SAL_VALUE_EXPR,
				 idop	:	SAL_VALUE_ID,
				 right	:	SAL_VALUE_EXPR)

	sal_esp_prefix_occ	(idop	:	SAL_VALUE_ID,
				 left	:	SAL_VALUE_EXPR,
				 right	:	SAL_VALUE_EXPR)

	sal_esp_unary_prefix_occ(idop	:	SAL_VALUE_ID,
				 left	:	SAL_VALUE_EXPR)

	-- for add_map
	sal_esp_ternary_occ	(idop	:	SAL_VALUE_ID,
				 arg1	:	SAL_VALUE_EXPR,
				 arg2	:	SAL_VALUE_EXPR,
				 arg3	:	SAL_VALUE_EXPR)

	sal_prefix_occ		(idop	:	SAL_VALUE_ID,
				 qualif	:	SAL_OBJ_QUALIF,
				 expr	:	SAL_VALUE_EXPR)

	sal_assignment		(id	:	IDENT,
				 right	:	SAL_VALUE_EXPR)

	sal_var_occ		(Pos	:	POS,
				 VarId	:	SAL_variable_id)

	sal_array_var_occ	(Pos	:	POS,
				 VarId	:	SAL_variable_id,
				 Indexes	:	SAL_VALUE_EXPRS)
        /*sal_cc_array_var_occ	(Pos	:	POS,
				 VarId	:	SAL_variable_id,
				 Indexes	:	SAL_VALUE_EXPRS)*/

        sal_cc_array_set	(Pos	:	POS,
				 --VarId	:	SAL_variable_id,
				 Array	:	SAL_VALUE_EXPR,
                                 Type	:	SAL_TYPE_EXPR,
				 Indexes	:	SAL_VALUE_EXPRS,
				 Value	:	SAL_VALUE_EXPR)

	stop -- nothing else is needed for the moment here...

	not_supported

	no_val

	no_def --????	

	nil	

	-- Macro processor expressions (for macro expansion)
	macro	(SAL_MACRO_EXPR)

'type' SAL_MACRO_EXPR

       macro_list	(SAL_VALUE_EXPR)

------------------------------------------------------------------
-- SAL additional expr. defs:
------------------------------------------------------------------

'type' SAL_VALUE_LITERAL

        bool_true
	bool_false
	integ		(val	:	IDENT)
	nil

'type'	SAL_NAME

	id_op		(idop		:	SAL_ID_OP)

	nil

'type' SAL_OBJ_QUALIF

       qualif		(oid	:	SAL_object_id)

       nil

'type' SAL_SET_BINDING

       bindings		(SAL_BINDINGS)


'type' SAL_BINDINGS  

	list		(head	:	SAL_BINDING,
			 tail	:	SAL_BINDINGS)
	nil	


'type'	SAL_BINDING  

	sal_prod_binding(pos		:	POS,
			 bindings	:	SAL_BINDINGS)

	sal_typed_prod	(pos		:	POS,
			 bindings	:	SAL_BINDINGS,
			 type_expr	:	SAL_TYPE_EXPR)

	sal_typed_id	(pos		:	POS,
		         id_op		:	SAL_ID_OP,
			 type		:	SAL_TYPE_EXPR)

'type' SAL_LIST_LIMIT

       sal_limit	(bindings	:	SAL_BINDINGS,
			 expr		:	SAL_VALUE_EXPR,
			 restrict	:	SAL_VALUE_EXPR)

       nil

'type'	SAL_VALUE_EXPR_PAIRS

	list		(head	:	SAL_VALUE_EXPR_PAIR,
			 tail	:	SAL_VALUE_EXPR_PAIRS)
	nil	


'type'	SAL_VALUE_EXPR_PAIR

	pair		(left	:	SAL_VALUE_EXPR,
			 right	:	SAL_VALUE_EXPR)
	nil


'type' SAL_LAMBDA_BINDINGS

       list		(head	:	SAL_LAMBDA_BINDING,
			 tail	:	SAL_LAMBDA_BINDINGS)

       nil

'type' SAL_LAMBDA_BINDING

       bindings		(SAL_BINDINGS)


'type' SAL_ARGS

       sal_argument	(exprs		:	SAL_VALUE_EXPRS)

'type' SAL_BINDING_OP

       lambda, 
       forall,
       exists,
       exists1,
       nil

'type' SAL_LOGIC_CONNECTIVE
        implies,
	or,
	and,
	not


'type' SAL_LET_BINDINGS
       
       list	(head	:	SAL_LET_BINDING,
		 tail	:	SAL_LET_BINDINGS)

       nil

'type' SAL_LET_BINDING
       
       sal_let_bind   (letbind	:	SAL_LETBIND,
		       expr	:	SAL_VALUE_EXPR)

       sal_let_binds  (letbinds	:	SAL_LETBINDS,
		       expr	:	SAL_VALUE_EXPR)
       nil	  

'type' SAL_LETBINDS 

       list		(head	:	SAL_LETBIND,
			 tail	:	SAL_LETBINDS)
       nil	


'type' SAL_LETBIND  

       sal_let_idop	(idop		:	SAL_ID_OP,
			 bindings	:	SAL_BINDINGS,
			 type		:	SAL_TYPE_EXPR)

'type' BINDING_NAMESPACE_STACK

       list	(head		:	BINDING_NAMESPACE,
		 rest		:	BINDING_NAMESPACE_STACK)

       nil	

'type' BINDING_NAMESPACE

       list	(binding_elem	:	BINDING_ELEM,
		 rest		:	BINDING_NAMESPACE)

       nil


'type' BINDING_ELEM
       
       binding_elem	(index		:	INT,
			-- Record name:
			 id		:	SAL_ID_OP,
		        -- Binding (name assoc. with the field)
			 bound_name	:	SAL_NAME)

       nested_elem	(index		:	INT,
			 bound_name	:	SAL_NAME,
			 ref		:	BINDING_ELEM)
       nil


'type' REMAINING_BINDINGS

       list	(head	:	REMAINING_BINDING,
		 tail	:	REMAINING_BINDINGS)

       nil
	

'type' REMAINING_BINDING

       remaining	(pos	:	POS,
			 idop	:	SAL_ID_OP,
			 index	:	INT,
			 binding:	BINDINGS,
			 typr	:	TYPE_EXPR)--,
			 --expr	:	VALUE_EXPR)

'type' 	SAL_ELSIF_BRANCHES

	list	(head	:	SAL_ELSIF_BRANCH,
		 tail	:	SAL_ELSIF_BRANCHES)

	nil	


'type' 	SAL_ELSIF_BRANCH

	elsif		(if	:	SAL_VALUE_EXPR,
			 then	:	SAL_VALUE_EXPR)

	nil	


'type' 	SAL_ELSE_BRANCH

	else		(SAL_VALUE_EXPR)

	nil	

'type'	SAL_VALUE_ID

	val_id		(idop	:	SAL_ID_OP)

	record_val_id	(pos	:	POS,
			 idop	:	SAL_ID_OP,
			 field	:	INT)

	-- this is used to more complex record expressions
	-- i.e. (f(x)).1 (the actual record is not an ident but the result of a function)
	complex_val_id	(pos	:	POS,
			 name	:	SAL_VALUE_EXPR,
			 field	:	INT)

'type'	SAL_ID_OP

	id		(IDENT)

	sal_op_symb	(SAL_OP)

	sal_list_op	(operation	:	SAL_OP,
			 type		:	SAL_type_id)



-------------------------------------------------------------------------------
-- Special operator indicators
-------------------------------------------------------------------------------
-- The following are operators that are signaled as 'sal_op_symb' in the non-cc
-- version but that will be transformed into prefix (non built-in) operations
-- in the cc versions. In order to cope with the conextualization of them, they
-- have different functors:
-------------------------------------------------------------------------------
	-- The 'sal_int_op' functor is also used in for the MOD operation in the
	-- non-cc version. This is an exception and is due to the semantic 
	-- difference between the built-in modulo in SAL and in RSL
	sal_int_op	(operation	:	SAL_OP,
			 type		:	SAL_type_id),

	sal_cc_op	(operation	:	SAL_OP,
			 type		:	SAL_type_id),

-------------------------------------------------------------------------------
-- Collection operators
-------------------------------------------------------------------------------
-- These ones are used in both, the non-cc and cc versions, due to the lack
-- of support for collections (and their operations) in SAL.
-------------------------------------------------------------------------------

	sal_set_op	(operation	:	SAL_OP,
			 type_expr	:	SAL_TYPE_EXPR,
			 setTid		:	SAL_type_id)

	sal_map_op	(operation	:	SAL_OP,
			 dom_type_expr	:	SAL_TYPE_EXPR,
			 rng_type_expr	:	SAL_TYPE_EXPR,
			 mapTid		:	SAL_type_id)

        nil

'type' SAL_OP

       sal_infix_op(SAL_INFIX_OP)

       sal_prefix_op(SAL_PREFIX_OP)

       sal_function_op(SAL_FUNCTION_OP)

       sal_identity

       not_supported

'type' SAL_INFIX_OP

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
	int_div

	-- testing this:
	and
	implies
	or
-- LTL operators:
        u
        w
	r

'type' SAL_PREFIX_OP

        minus
	not -- for the cc version	
 -- LTL operators:
	g
	f
	x

'type' SAL_FUNCTION_OP

        supset
	subset
	supseteq
	subseteq
	isin
	notisin
	rem
	difference
	restriction_by
	restriction_to
	caret
	union
	override
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

	-- used for optimisation
	add_set
	add_map
	
	-- used in the cc version:
	is_true
        is_bool

'type' SAL_RESTRICTIONS
       
       list	(head	:	SAL_RESTRICTION,
		 rest	:	SAL_RESTRICTIONS)

       nil

'type' SAL_RESTRICTION

       cc_restriction	(ident				:	IDENT,
			 non_nav_constructor_check	:	SAL_VALUE_EXPR,
			 value_wfc			:	SAL_VALUE_EXPR)

       nil

'type' SAL_LIST_TYPES
       
       list	(head	:	SAL_LIST_TYPE,
		 rest	:	SAL_LIST_TYPES)

       nil

'type' SAL_LIST_TYPE

       list_type	(type	:	TYPE_EXPR,
			 tid	:	SAL_type_id)
    -- ^^^^ also used for sets

       map_type		(dom	:	TYPE_EXPR,
			 rng	:	TYPE_EXPR,
			 tid	:	SAL_type_id) 

       array_type	(index	:	TYPE_EXPR,
			 value	:	TYPE_EXPR,
			 tid	:	SAL_type_id)

       -- used for lifted types:
       lifted_type	(type	:	TYPE_EXPR,
			 tid	:	SAL_type_id)
-------------------------------------------------------
'type' SAL_FIXED_POINT_STATUS
       not_calculated
       calculated

-------------------------------------------------------

'type' NUM_ARG
       defLowInt,
       defHighInt,
       defHighNat,
       defListSize,
       numbered		(index	: INT)

'type' SAL_CONTEXT_ARGS
       
       list		(head	: SAL_CONTEXT_ARG,
			 tail	: SAL_CONTEXT_ARGS)

       nil

'type' SAL_CONTEXT_ARG
       value_arg	(SAL_value_id)

       type_arg		(SAL_type_id)


--------------------------------------------------
-- Auxiliary Types
--------------------------------------------------

-- Auxiliary types for sorting declarations

--------------------------------------------------
'type' SORTED_DECLS_S
       list	       (head    :   SORTED_DECLS,
                        tail    :   SORTED_DECLS_S)
       nil      

--------------------------------------------------
'type' SORTED_DECLS
       list	       (head    :   SORTED_DECL_ITEM,
                        tail    :   SORTED_DECLS)
       nil      

--------------------------------------------------
'type' SORTED_DECL_ITEM
       type_item		(Type_id)
       value_item		(Value_id)
       axiom_item		(Axiom_id)
       lemma_item		(Axiom_id)
       object_item		(pos	     : POS,
				 id	     : IDENT,
				 typings     : TYPINGS,
				 class	     : CLASS)
--       import_item		(IMPORTING) 
       rec_fun_item		(Value_id)
       mut_rec_fun_item		(Value_id)
       rec_item			(SORTED_DECLS)
       mark_item		(STRING)  -- for debugging
       ts_item			(Transition_system_id)
       prop_item		(Property_id)
       nil      



------------------------------------------------------
'type' VALUE_TYPE
       
       regular_value
       record_field
       constructor_value
       reconstructor_value
       constant
       global_parameter

'type' SAL_IS_IN_VALUE

       is_in_function
       cc_mk_function
       destructor_function
       reconstructor_function
       normal_function

'action' Init_SAL_AST

  'rule' Init_SAL_AST:
	 Global_Cid_Table <- nil
	 Global_Tid_Table <- nil
	 Global_CC_Tid_Table <- nil
	 Global_Vid_Table <- nil
	 Global_Oid_Table <- nil
	 Global_Var_Table <- nil
	 Global_TS_Table  <- nil

-------------------------------------------------------------------
-- Identifiers
-------------------------------------------------------------------

-------------------------------------------------------------------
-- SAL_context_id
-------------------------------------------------------------------
-- Used for context related information storage. The Cids are
-- particularly used for type qualification (each type_id has a
-- reference to the corresponding Cid)
-------------------------------------------------------------------

'type' SAL_CONTEXT_IDS

       list	(head	:	SAL_context_id,
		 tail	:	SAL_CONTEXT_IDS)

       nil

'table' SAL_context_id  (Ident	:	IDENT,
			 ArgNo	:	INT,
			 Args	:	SAL_CONTEXT_ARGS,
		         Types	:	SAL_TYPE_IDS,
			 State	:	SAL_CONTEXT_CONSTANTS,
			 Static	:	SAL_CONTEXT_CONSTANTS,
			 -- cc version:
			 Lifted_Cid	:	OPT_CONTEXT_ID)

'action' Make_SAL_context_id(IDENT, INT -> SAL_context_id)

  'rule' Make_SAL_context_id(Id, ArgNo -> New):
	 New::SAL_context_id
	 New'Ident <- Id
	 New'ArgNo <- ArgNo
	 New'Args <- nil
	 New'Types <- nil
	 New'State <- nil
	 New'Static <- nil
	 New'Lifted_Cid <- nil
  	 

'action' New_SAL_single_context_id(IDENT,INT  -> SAL_context_id)

  'rule' New_SAL_single_context_id(Id, ArgNo -> New):
	 Make_SAL_context_id(Id, ArgNo -> New)
	 add_cid_to_global(New)	 

-- Basic functions over SAL_context_id:

'action' New_SAL_context_id(IDENT,INT  -> SAL_context_id)

  'rule' New_SAL_context_id(Id, ArgNo -> New):
	 New_SAL_single_context_id(Id, ArgNo -> New)
	 -- generating the lifted version:
	 SAL_Gen_CC_id(Id -> CC_Id)
	 Make_SAL_context_id(CC_Id, ArgNo -> New1)
	 -- Updating the ref. info:
	 New'Lifted_Cid <- cid(New1)
	 New1'Lifted_Cid <- cid(New1)

'action' New_SAL_unnamed_context_id(INT  -> SAL_context_id)

  'rule' New_SAL_unnamed_context_id(ArgNo -> New):
	 string_to_id("Unnamed" -> Id)
	 Make_SAL_context_id(Id, ArgNo -> New)
	 -- The cid is not collected in the global structure!

'action' Collect_Tid_in_Cid(SAL_context_id, SAL_type_id)

  'rule' Collect_Tid_in_Cid(Cid, Tid):
	 Cid'Types -> TList
	 where(SAL_TYPE_IDS'list(Tid, TList) -> NewList)
	 Cid'Types <- NewList

'action' Extend_Static_in_Cid_Decls(SAL_context_id, SAL_CONTEXT_CONSTANTS)

  'rule' Extend_Static_in_Cid_Decls(Cid, Consts):
	 Cid'Static -> Static
	 SAL_Concatenate_Context_Constants(Static, Consts -> ExtendedStatic)
	 Cid'Static <- ExtendedStatic

'action' Extend_Static_in_Cid_Decl(SAL_context_id, SAL_CONTEXT_CONSTANT)

  'rule' Extend_Static_in_Cid_Decl(Cid, Const):
	 Cid'Static -> State
	 where(SAL_CONTEXT_CONSTANTS'list(Const, State) -> ExtendedState)
	 Cid'State <- ExtendedState

'action' Extend_State_in_Cid_Decls(SAL_context_id, SAL_CONTEXT_CONSTANTS)

  'rule' Extend_State_in_Cid_Decls(Cid, Consts):
	 Cid'State -> State
	 SAL_Concatenate_Context_Constants(State, Consts -> ExtendedState)
	 Cid'State <- ExtendedState

'action' Extend_State_in_Cid(SAL_context_id, SAL_CONTEXT_CONSTANT)

  'rule' Extend_State_in_Cid(Cid, Const):
	 Cid'State -> State
	 where(SAL_CONTEXT_CONSTANTS'list(Const,State) -> ExtendedState)
	 Cid'State <- ExtendedState

'action' Remove_Decl_from_Static(SAL_context_id, SAL_CONTEXT_CONSTANT)

  'rule' Remove_Decl_from_Static(Cid, Const):
	 Cid'Static -> Static
	 Remove_Decl_from_Static1(Static,Const -> NewStatic)
	 Cid'Static <- NewStatic

'action' Remove_Decl_from_Static1(SAL_CONTEXT_CONSTANTS,
			SAL_CONTEXT_CONSTANT -> SAL_CONTEXT_CONSTANTS)

  'rule' Remove_Decl_from_Static1(
	   list(Const1, Rest), Const -> Result):
	 Remove_Decl_from_Static1(Rest, Const -> Res1)
	 (|
	    eq(Const1,Const)
	    where(Res1 -> Result)
	 ||
	    where(SAL_CONTEXT_CONSTANTS'list(Const, Res1) -> Result)
	 |)	 

  'rule' Remove_Decl_from_Static1(
	   list(_, Rest), Const -> Result):
	 Remove_Decl_from_Static1(Rest, Const -> Result)

  'rule' Remove_Decl_from_Static1(nil, _ -> nil)


'action' add_cid_to_global(SAL_context_id)

  'rule' add_cid_to_global(Cid)
	 Global_Cid_Table -> Global
	 where(SAL_CONTEXT_IDS'list(Cid, Global) -> Extended)
	 Global_Cid_Table <- Extended

'type' OPT_CONTEXT_ID

       cid	(SAL_context_id)

       nil

'action' LookUp_Context(IDENT -> OPT_CONTEXT_ID)

  'rule' LookUp_Context(Id -> OptContext)
	 Global_Cid_Table -> Global
	 internal_context_look_up(Id, Global -> OptContext)

'action' internal_context_look_up(IDENT, SAL_CONTEXT_IDS -> OPT_CONTEXT_ID)

  'rule' internal_context_look_up(Id, list(H, Rest) -> Result)
	 H'Ident -> Id1
	 (|
	    eq(Id, Id1)
	    where(cid(H) -> Result)
	 ||
	    internal_context_look_up(Id,Rest -> Result)
	 |)

  'rule' internal_context_look_up(Id, nil -> nil)
 

-------------------------------------------------------------------
-- SAL_type_id
-------------------------------------------------------------------
-- Used for type related information storage. Every non basic type
-- declaration generates a new Tid stored globally in the system. Type
-- references are mainly driven by holding a reference to the proper
-- tid.
-------------------------------------------------------------------

'table' SAL_type_id	(Pos		:	POS,
			 Ident		:	IDENT,
			 TExpr		:	SAL_TYPE_EXPR,
			 Cid		:	OPT_CONTEXT_ID,
			 OperationsCid	:	OPT_CONTEXT_ID,
			 Args		:	SAL_VALUE_IDS,
			 MacroArgs	:	SAL_VALUE_IDS,
			 FPStatus	:	SAL_FIXED_POINT_STATUS,
			 FixedPoint	:	SAL_CONTEXT_CONSTANTS,
			 Declaration	:	SAL_CONTEXT_CONSTANT,
			 DeclCids	:	SAL_CONTEXT_IDS,
			 -- Added for the cc-version:
			 ----------------------------
			 -- This is used to store non-empty conditions for the type (when appropriate)
			 ConfidenceExpr :	SAL_VALUE_EXPR,
			 -- Used in the non-lifted types to have a way to directly
			 -- acces their lifted version... In the case of a tid that is
			 -- of a lifted type already, this field points to SELF!
			 Lifted_Tid	:	OPT_SAL_TYPE_ID,
			 -- This field stores the constructor of the (lifted) type, the field is nil
			 -- in the case of the non-lifted types
			 Constructor	:       OPT_SAL_VALUE_ID,
			 -- This field stores, when needed, the default (non descriptive) nav
			 -- value. This is used (and declared) ONLY when the type is involved on
			 -- a result product and it is not the first element in the product.
			 -- In this case, all other types in the product (but the first) will not be
			 -- lifted with new speciall nav values but with an 'UNIVERSAL ' nav (due to 
			 -- the fact that a speciall nav reporting value will be asigned ONLY to the
			 -- first element in the tuple. This is an attempt to reduce the size of the 
			 -- lifted type system for model checking...
			 DefaultNav	:	OPT_SAL_VALUE_ID,
			 -- Collects the variant fields in the lifted type to allow the generation
			 -- of the proper type declaration in 'Refine_SAL_cc_ast' (this field is nil
			 -- when the tid refers to a non-lifted type).
			 Lifted_fields	:	SAL_DATA_TYPE_PARTS)
			 

'type' OPT_SAL_TYPE_ID

       tid	(SAL_type_id)
      
       nil


'type' SAL_TYPE_IDS

       list	(head	: SAL_type_id,
		 tail	: SAL_TYPE_IDS)
       nil

'action' add_tid_to_global(SAL_type_id)

  'rule' add_tid_to_global(Tid)
	 Global_Tid_Table -> Curr
	 where(SAL_TYPE_IDS'list(Tid, Curr) -> Res)
	 Global_Tid_Table <- Res
--Tid'Ident -> Id
--Putmsg("Adding ")
--Print_id(Id)
--Putmsg(" at ")
--Tid'Pos -> P
--PrintPos(P)
--Putnl
--Global_Tid_Table -> X
--print(X)

'action' Make_SAL_type_id(POS, IDENT -> SAL_type_id)

  'rule' Make_SAL_type_id(P, Id -> New):
  	 New::SAL_type_id
	 New'Pos <- P
	 New'Ident <- Id
	 New'TExpr <- nil
	 New'Cid <- nil
	 New'OperationsCid <- nil
	 New'Args <- nil
	 New'MacroArgs <- nil
	 New'FPStatus <- not_calculated
	 New'FixedPoint <- nil
	 New'Declaration <- nil
	 New'DeclCids <- nil
	 New'Lifted_fields <- nil
	 New'Constructor <- nil
	 New'DefaultNav <- nil
	 New'ConfidenceExpr <- no_val
	 New'Lifted_Tid <- nil
	 New'Constructor <- nil
	 New'DefaultNav <- nil
	 New'Lifted_fields <- nil


'action' add_tid_to_lifted_global(SAL_type_id)

  'rule' add_tid_to_lifted_global(Tid)
	 Global_CC_Tid_Table -> Curr
	 where(SAL_TYPE_IDS'list(Tid, Curr) -> Res)
	 Global_CC_Tid_Table <- Res

-- Basic functions over sal_type_id:

'action' New_SAL_type_id(POS, IDENT, TYPE_EXPR  -> SAL_type_id)

  'rule' New_SAL_type_id(P, Id, _ -> New):
	 -- Avoids the creation of multiple Tids when
	 -- there are multiple instantiations of one scheme with
	 -- type declarations...
	 look_up_type_id(P -> tid(New))

  'rule' New_SAL_type_id(P, Id, TypeExpr -> New)
  	 Make_SAL_type_id(P, Id -> New)
	 SAL_Current_Cid -> Cid
	 New'Cid <- cid(Cid)
	 -- Collecting the Tid:
	 add_tid_to_global(New)
	 -- cc
	 -- Generating the lifted tid:
	 -- Increasing the Pos
	 IncreaseCol(P -> NewPos)
	 SAL_Gen_CC_id(Id -> CC_Id)
	 -- cannot later make reference to CC_New in the function that
	 -- creates it, as corrupts Global_Tid_Table, 
	 -- so use an auxiliary function 
	 New_SAL_type_id_new(NewPos, CC_Id -> CC_New)
	 New'Lifted_Tid <- tid(CC_New)
	 -- Generating the first (and known so far) variant field (the non-nav values...):
	 DefaultPos( -> NewPosII)
	 id_to_string(Id -> IdStr)
	 Concatenate(IdStr, "_val" -> AccStr)
	 string_to_id(AccStr -> AccId)
	 New_SAL_value_id(NewPosII, id(AccId), Cid, type_refs(sal_defined(P, Id, New)), record_field -> AccesorVid)
	 where(SAL_DESTRUCTORS'list(sal_destructor(id(AccId),AccesorVid,type_refs(sal_defined(P, Id, New)),TypeExpr),nil)-> Accesor)
	 New_SAL_value_id(NewPos, id(CC_Id), Cid, type_refs(sal_defined(NewPos, CC_Id, CC_New)), constructor_value -> ConstructorVid)
	 where(sal_construc(id(CC_Id), ConstructorVid, Accesor,nil) -> Constructor)
	 -- Generating the constructor for the nav field:
	 DefaultPos( -> NewPosIII)
	 Concatenate(IdStr, "_nav_val" -> NavAccStr)
	 string_to_id(NavAccStr -> NavAccId)
	 SAL_Nav_Tid -> NavTid
	 NavTid'Pos -> NavPos
	 NavTid'Ident -> NavId
	 New_SAL_value_id(NewPosIII, id(NavAccId), Cid, type_refs(sal_defined(NavPos, NavId, NavTid)), record_field -> NavVid)
--Putmsg("0 for ")
--Print_id(Id)
--Putnl()
--Global_Tid_Table -> W
--print(W)
	 where(type_refs(sal_defined(NavPos, NavId, NavTid)) -> TR)
--print(TR)
--Putmsg("1\n")
--Global_Tid_Table -> X
--print(X)
	 where(sal_destructor(id(NavAccId), NavVid, TR, TypeExpr) -> SD)
--print(SD)
--Putmsg("2\n")
--Global_Tid_Table -> Z
--print(Z)
	 where(SAL_DESTRUCTORS'list(SD,nil) -> NavAccesor)
	 Concatenate(IdStr, "_nav" -> NavConstStr)
	 string_to_id(NavConstStr -> NavConstId)
	 where(type_refs(sal_defined(NewPosII, NavConstId, CC_New)) -> TR2)
--Putmsg("3\n")
--Global_Tid_Table -> Y
--print(Y)
	 New_SAL_value_id(NewPosII, id(NavConstId), Cid, TR2, constructor_value -> NavConstVid)
--Putmsg("4\n")
--Global_Tid_Table -> Y1
--print(Y1)
	 where(sal_construc(id(NavConstId), NavConstVid, NavAccesor,nil) -> NavConstructor)
	 -- Generating the data part:
	 -- Putting type_refs(sal_defined(P, Id, New)) as the type
	 -- can cause problems.  Make it nil for now; fix later
	 where(type_refs(sal_defined(P, Id, New)) -> T)
	 where(sal_part(Constructor, T) -> ConsPart)
	 where(sal_part(NavConstructor, T) -> NavPart)
	 where(SAL_DATA_TYPE_PARTS'list(ConsPart, 
				   list(NavPart, nil)) -> DataPart)
	 CC_New'Constructor <- vid(ConstructorVid)
	 CC_New'DefaultNav <- vid(NavConstVid)
	 CC_New'Lifted_fields <- DataPart

'action' New_SAL_type_id_new(POS, IDENT  -> SAL_type_id)

  'rule' New_SAL_type_id_new(NewPos, CC_Id -> CC_New):
	 Make_SAL_type_id(NewPos, CC_Id -> CC_New)
	 -- Points to self
	 CC_New'Lifted_Tid <- tid(CC_New)
	 SAL_Current_Cid -> Cid
	 CC_New'Cid <- cid(Cid)
  	 

'action' New_SAL_type_id_with_Cid(POS, IDENT, SAL_context_id, TYPE_EXPR  -> SAL_type_id)

  'rule' New_SAL_type_id_with_Cid(P, Id, Cid, _ -> New):
	 -- Avoids the creation of multiple Tids when
	 -- there are multiple instantiations of one scheme with
	 -- type declarations...
	 look_up_type_id(P -> tid(New))

  'rule' New_SAL_type_id_with_Cid(P, Id, Cid, TypeExpr -> New)
  	 Make_SAL_type_id(P, Id -> New)
	 New'Cid <- cid(Cid)

	 -- cc
	 -- Generating the lifted tid:
	 -- Increasing the Pos
	 IncreaseCol(P -> NewPos)
	 SAL_Gen_CC_id(Id -> CC_Id)
	 Make_SAL_type_id(NewPos, CC_Id -> CC_New)
	 New'Lifted_Tid <- tid(CC_New)
	 -- Points to self
	 CC_New'Lifted_Tid <- tid(CC_New)
	 CC_New'Cid <- cid(Cid)
	 -- Generating the first (and known so far) variant field (the non-nav values...):
	 IncreaseCol(NewPos -> NewPosII)
	 id_to_string(Id -> IdStr)
	 Concatenate(IdStr, "_val" -> AccStr)
	 string_to_id(AccStr -> AccId)
	 New_SAL_value_id(NewPosII, id(AccId), Cid, type_refs(sal_defined(P, Id, New)), record_field -> AccesorVid)
	 where(SAL_DESTRUCTORS'list(sal_destructor(id(AccId),AccesorVid,type_refs(sal_defined(P, Id, New)),TypeExpr),nil)-> Accesor)
	 New_SAL_value_id(NewPos, id(CC_Id), Cid, type_refs(sal_defined(NewPos, CC_Id, CC_New)), constructor_value -> ConstructorVid)
	 where(sal_construc(id(CC_Id), ConstructorVid, Accesor,nil) -> Constructor)
	 -- Generating the constructor for the nav field:
	 IncreaseCol(NewPosII -> NewPosIII)
	 Concatenate(IdStr, "_nav_val" -> NavAccStr)
	 string_to_id(NavAccStr -> NavAccId)
	 SAL_Nav_Tid -> NavTid
	 NavTid'Pos -> NavPos
	 NavTid'Ident -> NavId
	 New_SAL_value_id(NewPosIII, id(NavAccId), Cid, type_refs(sal_defined(NavPos, NavId, NavTid)), record_field -> NavVid)
	 where(SAL_DESTRUCTORS'list(sal_destructor(id(NavAccId), NavVid, type_refs(sal_defined(NavPos, NavId, NavTid)), TypeExpr),nil) -> NavAccesor)
	 Concatenate(IdStr, "_nav" -> NavConstStr)
	 string_to_id(NavConstStr -> NavConstId)
	 New_SAL_value_id(NewPosII, id(NavConstId), Cid, type_refs(sal_defined(NewPosII, NavConstId, CC_New)), constructor_value -> NavConstVid)
	 where(sal_construc(id(NavConstId), NavConstVid, NavAccesor,nil) -> NavConstructor)
	 -- Generating the data part:
	 where(type_refs(sal_defined(P, Id, New)) -> T)
	 where(SAL_DATA_TYPE_PARTS'list(sal_part(Constructor, T), 
				   list(sal_part(NavConstructor, T), nil)) -> DataPart)
	 CC_New'Constructor <- vid(ConstructorVid)
	 CC_New'DefaultNav <- vid(NavConstVid)
	 CC_New'Lifted_fields <- DataPart




'action' New_SAL_NAV_type_id(POS, IDENT, SAL_context_id, TYPE_EXPR  -> SAL_type_id)

  'rule' New_SAL_NAV_type_id(P, Id,Cid, TypeExpr -> New):
	 Make_SAL_type_id(P, Id -> New)
	 New'Cid <- cid(Cid)
	 New'Lifted_Tid <- tid(New)

'action' Extend_Decl_Cid_in_Tid(SAL_type_id, SAL_context_id)

  'rule' Extend_Decl_Cid_in_Tid(Tid,Cid)
	 Tid'DeclCids -> List
	 where(SAL_CONTEXT_IDS'list(Cid,List) -> NewList)
	 Tid'DeclCids <- NewList

'action' Update_Ident_in_Tid(SAL_type_id, IDENT)

  'rule' Update_Ident_in_Tid(Tid, Ident):
	 Tid'Ident <- Ident

'action' Update_Cid_in_Tid(SAL_type_id, SAL_context_id)

  'rule' Update_Cid_in_Tid(Tid, Cid):
	 Tid'Cid <- cid(Cid)

'action' Update_Args_in_Tid(SAL_type_id, SAL_VALUE_IDS)

  'rule' Update_Args_in_Tid(Tid, Args):
	 Tid'Args -> OldArgs
	 SAL_Concatenate_Context_Args(OldArgs, Args -> NewArgs)
	 Tid'Args <- NewArgs

'action' Update_Macro_in_Tid(SAL_type_id, SAL_VALUE_IDS)

  'rule' Update_Macro_in_Tid(Tid, Args):
	 Tid'MacroArgs -> OldArgs
	 SAL_Concatenate_Context_Args(OldArgs, Args -> NewArgs)
	 Tid'MacroArgs <- NewArgs

'action' look_up_type_id(POS -> OPT_SAL_TYPE_ID)

  'rule' look_up_type_id(P -> Result):
	 Global_Tid_Table -> Table
--Putmsg("Entrando a buscar tipo en pos: ")
--PrintPos(P)
--Putnl()
--print(Table)
	 internal_look_up_type_id(P, Table -> Result)

'action' internal_look_up_type_id(POS, SAL_TYPE_IDS -> OPT_SAL_TYPE_ID)
	 
  'rule' internal_look_up_type_id(P, list(H,T) -> Result)
	 H'Pos -> Pos
--Putmsg("Comparando con: ")
--PrintPos(Pos)
--Putnl()
	 (|
	     eq(Pos, P)
	     where(tid(H) -> Result)
	 ||
	     internal_look_up_type_id(P, T -> Result)
	 |)

  'rule' internal_look_up_type_id(P , nil -> nil)


-------------------------------------------------------------------
-- SAL_value_id
-------------------------------------------------------------------
-- Used for especial value related information storage. In particular,
-- the only values that has an associated vid are the ones that can be
-- referenced by other contexts:
-- a) Global constant declarations
-- b) Global function declarations
-------------------------------------------------------------------


'table' SAL_value_id	(Pos		:	POS,
			 IdOp		:	SAL_ID_OP,
			 Type		:	SAL_TYPE_EXPR,
			 Cid		:	OPT_CONTEXT_ID,
			 -- Used for functions only:
			 Params		:	SAL_FORMAL_FUN_PARAMETERS,
			 VType		:	VALUE_TYPE,
			 FPStatus	:	SAL_FIXED_POINT_STATUS,
			 FixedPoint	:	SAL_CONTEXT_CONSTANTS,
			 Declaration	:	SAL_CONTEXT_CONSTANT,
			 DeclCids	:	SAL_CONTEXT_IDS,
			 -- used in the cc version
			 Lifted_Vid	:	SAL_value_id)

'action' Make_SAL_value_id(POS, SAL_ID_OP, SAL_context_id, VALUE_TYPE
	 				   		   -> SAL_value_id)
  'rule' Make_SAL_value_id(P, IdOp, Cid, VT -> New):
  	 New::SAL_value_id
	 New'Pos <- P
	 New'IdOp <- IdOp
	 New'Type <- nil
	 New'Cid <- cid(Cid)
	 New'Params <- nil
	 New'VType <- VT
	 New'FPStatus <- not_calculated
	 New'FixedPoint <- nil
	 New'Declaration <- nil
	 New'DeclCids <- nil


'action' New_SAL_value_id(POS, SAL_ID_OP, 
	   SAL_context_id,SAL_TYPE_EXPR ,VALUE_TYPE -> SAL_value_id)

  'rule' New_SAL_value_id(P, IdOp, Cid, TElem, VT -> New):
	 Make_SAL_value_id(P, IdOp, Cid, VT -> New)
	 New'Type <- TElem
	 -- Adding this new Vid to the global table:
	 add_vid_to_global(New)
	 -- Creating the lifted Vid:
	 IncreaseCol(P -> IncP)
	 Make_SAL_value_id(IncP, IdOp, Cid, VT -> New2)
	 Cid'Lifted_Cid -> LCid
	 New2'Cid <- LCid

	 -- Updating the information in the vid:
	 New'Lifted_Vid <- New2
	 New2'Lifted_Vid <- New2

'action' New_UnRegistered_Vid(SAL_ID_OP, SAL_context_id,SAL_TYPE_EXPR ,VALUE_TYPE -> SAL_value_id)

  'rule' New_UnRegistered_Vid(IdOp,Cid,TElem,VT -> New):
  	 DefaultPos(-> P)
  	 Make_SAL_value_id(P, IdOp, Cid, VT -> New)
	 New'Type <- TElem

----------------------------------------------------------------------------
-- New_SAL_special_value_id
----------------------------------------------------------------------------
-- This procedure is used for especial Vid generation (the ones that
-- are added during the translation process as global constants used
-- for lifted types boundaries).
----------------------------------------------------------------------------

'action' New_SAL_special_value_id(SAL_ID_OP,
					SAL_TYPE_EXPR  -> SAL_value_id)

  'rule' New_SAL_special_value_id(IdOp,TElem -> New):
	 New::SAL_value_id
      -- The POS field is deliberately omitted
      -- because there is NO position for this args (in the orignal code)
	 New'IdOp <- IdOp
	 New'Type <- TElem
      -- Note that this values are not collected in the global vid
      -- table (they dont have a valid POS value for looking up) and,
      -- furthermore, will never be searched!
      -----------------
      -- The context where this Vid belongs is the special file
      -- SAL_GLOBAL:
	 SAL_GLOBAL_Cid -> GlobalCid
	 -- It is not a function:
	 New'Params <- nil
	 -- Belongs to the global context:
         New'Cid <- cid(GlobalCid)
	 -- It's a constant (global_parameter):
	 New'VType <- global_parameter
	 -- Initialization:
	 New'FixedPoint <- nil
	 New'Declaration <- nil
	 -- No fixed point involved
	 -- (As this is a translator-generated constant
	 --  its type (INTEGER) is known and no fixed point
	 --  calculation is needed)
	 New'FPStatus <- calculated
	 New'DeclCids <- nil

'action' Update_Cid_in_Vid(SAL_value_id, SAL_context_id)

  'rule' Update_Cid_in_Vid(Vid, Cid):
--[|
--Vid'Cid -> cid(Old)
--Vid'IdOp -> IdOp
--SAL_Print_IdOp(IdOp)
--Putmsg(" changed from ")
--SAL_Print_Cid(Old)
--Putmsg(" to ")
--SAL_Print_Cid(Cid)
--Putnl()
--|]
	 Vid'Cid <- cid(Cid)
	 -- Updating the lifted Vid too:
--	 Cid'Lifted_Cid -> LCid
--	 Vid'Lifted_Vid -> LVid
--	 LVid'Cid <- LCid

'action' Extend_Decl_Cid_in_Vid(SAL_value_id, SAL_context_id)

  'rule' Extend_Decl_Cid_in_Vid(Vid,Cid)
	 Vid'DeclCids -> List
	 where(SAL_CONTEXT_IDS'list(Cid,List) -> NewList)
	 Vid'DeclCids <- NewList


'type' SAL_VALUE_IDS

       list	(head	: SAL_value_id,
		 tail	: SAL_VALUE_IDS)
       nil


'type' OPT_SAL_VALUE_ID

       vid	(SAL_value_id)
      
       nil

'action' add_vid_to_global(SAL_value_id)

  'rule' add_vid_to_global(Vid)
	 Global_Vid_Table -> Curr
	 where(SAL_VALUE_IDS'list(Vid, Curr) -> Res)
	 Global_Vid_Table <- Res

'action' SAL_Remove_Vid_from_Globals(SAL_value_id)

  'rule' SAL_Remove_Vid_from_Globals(Vid)
	 Global_Vid_Table -> Curr
	 SAL_Remove_Vid_from_Globals_(Vid, Curr -> NewTable)
	 Global_Vid_Table <- NewTable

'action' SAL_Remove_Vid_from_Globals_(SAL_value_id, SAL_VALUE_IDS -> SAL_VALUE_IDS)

  'rule' SAL_Remove_Vid_from_Globals_(Vid, list(Vid1, Rest) -> list(Vid, NewRest))
	 ne(Vid, Vid1)
	 SAL_Remove_Vid_from_Globals_(Vid, Rest -> NewRest)

  'rule' SAL_Remove_Vid_from_Globals_(Vid, list(Vid1, Rest) -> Rest)
	 eq(Vid, Vid1)

  'rule' SAL_Remove_Vid_from_Globals_(_, nil -> nil)
	 Putmsg("Internal error: No Vid found in the global collection to remove\nRoutine: SAL_Remove_Vid_from_Globals_ on sal_ast.g\n")

'action' look_up_value_id(POS -> OPT_SAL_VALUE_ID)

  'rule' look_up_value_id(P -> Result):
	 Global_Vid_Table -> Table
	 internal_look_up_value_id(P, Table -> Result)

'action' internal_look_up_value_id(POS, SAL_VALUE_IDS -> OPT_SAL_VALUE_ID)
	 
  'rule' internal_look_up_value_id(P, list(H,T) -> Result)
	 H'Pos -> Pos
	 (|
             eq(Pos,P)
	     where(vid(H) -> Result)
	 ||
	     internal_look_up_value_id(P, T -> Result)
	 |)

  'rule' internal_look_up_value_id(P , nil -> nil)

-------------------------------------------------------------------
-- SAL_object_id
-------------------------------------------------------------------
-- Used for object related information storage. This table resembles
-- the Object_id used in rsltc. The difference with the latter is that
-- the qualification information is stored in a different way (cids
-- rather names). This approach provides higher homogeneity and
-- support for later modifications.
-------------------------------------------------------------------

'table' SAL_object_id	(Pos		:	POS,
			 Ident		:	IDENT,
			 -- Declaration schema (context)
			 Cid		:	SAL_context_id,
			 -- Instantiated context:
			 -- Used only for scheme instances for
			 -- recording the id of the instantiated
			 -- context
			 ICid		:	OPT_CONTEXT_ID,
			 State		:	SAL_CONTEXT_CONSTANTS,
			 NonState	:	SAL_CONTEXT_CONSTANTS,
			 -- Information for the cc-version:
			 CCState	:	SAL_CONTEXT_CONSTANTS,
			 CCNonState	:	SAL_CONTEXT_CONSTANTS)
			 



'type' SAL_OBJECT_IDS

       list	(head	: SAL_object_id,
		 tail	: SAL_OBJECT_IDS)
       nil


'type' OPT_SAL_OBJECT_ID

       oid	(SAL_object_id)
      
       nil


'action' New_SAL_object_id(POS, IDENT, SAL_context_id,OPT_CONTEXT_ID
				       -> SAL_object_id)

  'rule' New_SAL_object_id(P, Id,Cid, OptICid -> New):
	 New::SAL_object_id
	 New'Pos <- P
	 New'Ident <- Id
	 New'Cid <- Cid
	 New'State <- nil
	 New'NonState <- nil
	 New'ICid <- OptICid
	 -- Adding this new Oid to the global table:
	 add_oid_to_global(New) 


'action' add_oid_to_global(SAL_object_id)

  'rule' add_oid_to_global(Oid)
	 Global_Oid_Table -> Curr
	 where(SAL_OBJECT_IDS'list(Oid, Curr) -> Res)
	 Global_Oid_Table <- Res


'action' look_up_object_id(POS -> OPT_SAL_OBJECT_ID)

  'rule' look_up_object_id(P -> Result):
	 Global_Oid_Table -> Table
	 internal_look_up_object_id(P, Table -> Result)


'action' internal_look_up_object_id(POS, SAL_OBJECT_IDS -> OPT_SAL_OBJECT_ID)
	 
  'rule' internal_look_up_object_id(P, list(H,T) -> Result)
	 H'Pos -> Pos
	 (|
	     eq(Pos, P)
	     where(oid(H) -> Result)
	 ||
	     internal_look_up_object_id(P, T -> Result)
	 |)

  'rule' internal_look_up_object_id(P , nil -> nil)

'action' ident_oid_look_up(IDENT -> OPT_SAL_OBJECT_ID)

  'rule' ident_oid_look_up(Id -> Result):
	 Global_Oid_Table -> Table
	 internal_look_up_object_id_by_id(Id, Table -> Result)


'action' internal_look_up_object_id_by_id(IDENT, SAL_OBJECT_IDS -> OPT_SAL_OBJECT_ID)
	 
  'rule' internal_look_up_object_id_by_id(Id, list(H,T) -> Result)
	 H'Ident -> Id1
	 (|
	     eq(Id, Id1)
	     where(oid(H) -> Result)
	 ||
	     internal_look_up_object_id_by_id(Id, T -> Result)
	 |)

  'rule' internal_look_up_object_id_by_id(_ , nil -> nil)

------------------------------------------------------------------------

'table' SAL_variable_id	(Pos		:	POS,
			 Ident		:	IDENT,
			 Type		:	SAL_TYPE_EXPR)

'type' SAL_VARIABLE_IDS

       list	(head	: SAL_variable_id,
		 tail	: SAL_VARIABLE_IDS)
       nil

'type' OPT_SAL_VARIABLE_ID

       var	(SAL_variable_id)
       nil

'action' New_SAL_variable_id(POS, IDENT, SAL_TYPE_EXPR -> SAL_variable_id)

  'rule' New_SAL_variable_id(Pos, Ident, Type -> New)
	 New::SAL_variable_id
	 New'Pos <- Pos
	 New'Ident <- Ident
	 New'Type <- Type
	 add_varId_to_global(New) 

'action' add_varId_to_global(SAL_variable_id)

  'rule' add_varId_to_global(VarId)
	 Global_Var_Table -> Curr
	 where(SAL_VARIABLE_IDS'list(VarId, Curr) -> Res)
	 Global_Var_Table <- Res


'action' look_up_variable_id(POS -> OPT_SAL_VARIABLE_ID)

  'rule' look_up_variable_id(P -> Result):
	 Global_Var_Table -> Table
	 internal_look_up_variable_id(P, Table -> Result)


'action' internal_look_up_variable_id(POS, SAL_VARIABLE_IDS -> OPT_SAL_VARIABLE_ID)
	 
  'rule' internal_look_up_variable_id(P, list(H,T) -> Result)
	 H'Pos -> Pos
	 (|
	     eq(Pos, P)
	     where(var(H) -> Result)
	 ||
	     internal_look_up_variable_id(P, T -> Result)
	 |)

  'rule' internal_look_up_variable_id(P , nil -> nil)

-------------------------------------------------------------------

'table' SAL_TranSys_id	(Pos		:	POS,
			 Ident		:	IDENT,
			 Input_decls	:	SAL_VAR_DECLS,
			 Local_decls	:	SAL_VAR_DECLS,
			 Initialization	:	SAL_INITIALIZATIONS,
			 CC_Init	:	SAL_INITIALIZATIONS,
			 Transition	:	SAL_TRANSITIONS)

'type' SAL_TRANSYS_IDS

       list	(head	: SAL_TranSys_id,
		 tail	: SAL_TRANSYS_IDS)
       nil

'type' OPT_SAL_TRANSYS_ID

       ts	(SAL_TranSys_id)
       nil

'action' New_SAL_TranSys_id(POS, IDENT -> SAL_TranSys_id)

  'rule' New_SAL_TranSys_id(Pos, Ident -> New)
	 New::SAL_TranSys_id
	 New'Pos <- Pos
	 New'Ident <- Ident
	 add_TS_to_global(New) 

'action' add_TS_to_global(SAL_TranSys_id)

  'rule' add_TS_to_global(TSId)
	 Global_TS_Table -> Curr
	 where(SAL_TRANSYS_IDS'list(TSId, Curr) -> Res)
	 Global_TS_Table <- Res


'action' look_up_TranSys_id(POS -> OPT_SAL_TRANSYS_ID)

  'rule' look_up_TranSys_id(P -> Result):
	 Global_TS_Table -> Table
	 internal_look_up_TranSys_id(P, Table -> Result)


'action' internal_look_up_TranSys_id(POS, SAL_TRANSYS_IDS -> OPT_SAL_TRANSYS_ID)
	 
  'rule' internal_look_up_TranSys_id(P, list(H,T) -> Result)
	 H'Pos -> Pos
	 (|
	     eq(Pos, P)
	     where(ts(H) -> Result)
	 ||
	     internal_look_up_TranSys_id(P, T -> Result)
	 |)

  'rule' internal_look_up_TranSys_id(P , nil -> nil)
