-- RSL Type Checker
-- Copyright (C) 1998 - 2005 UNU/IIST

-- raise@iist.unu.edu

-- This module contains the global variables used in the translation process

'module' sal_global_vars

'use'
	sal_ast sal_print
	ast ext

'export'
	Current_LBS_Env
	SAL_Current_Cid
	SAL_Current_CC_Cid
	-- Holds the current translated parts...
	Global_Model
	Global_CC_Model
        -- Special contexts' Ids
        -- for special constant initialization.
	SAL_GLOBAL_Cid
	SAL_TYPES_Cid
	SAL_CC_GLOBAL_Cid
	SAL_CC_TYPES_Cid

	-- For identifier generation
	LetIndex
	ParamIndex
	TypeIndex
	SortIndex
	
	-- For type parameter collection:
	Generated_Constants

	-- For generated contexts collection:
	Generated_Contexts
	Generated_CC_Contexts

	-- For generated contexts for Collections (set,map,list):
	Generated_CC_Operation_Contexts
	Generated_Operation_Contexts

	-- Functions for Operation Context handling:
	Init_Operation_Context
	SAL_Add_Operation_Context
	SAL_Add_CC_Operation_Context
	Get_Operation_Contexts
	Get_CC_Operation_Contexts

	Default_Int_Cid	
	Default_Int_Tid
	IntHighIdent
	IntHighVal
	IntLowIdent
	IntLowVal

	Default_Bool_Cid
	Default_Bool_Tid
	
	Default_Nat_Cid	
	Default_Nat_Tid
	NatHighIdent
	NatHighVal

	Current_List_Types
	Current_Set_Types
	Current_Map_Types
	Current_Array_Types

	Current_CC_Lifted_Types	

	SAL_Nav_Tid
	
	Global_Cid_Table 
	Global_Tid_Table
	Global_CC_Tid_Table -- same as the one above but including the lifted types...
	Global_Vid_Table
	Global_Oid_Table
	Global_Var_Table
	Global_TS_Table

	Global_Constant_Table
	Init_Constant_Table
	Insert_Constant

	Disamb_Stack

	SAL_Types_Extra_Defs
	-- not used cwg
	-- SAL_Types_Extra_CC_Defs

	SAL_TYPES_Constants

	Current_cid_stack	

	-- Functions for cc-type checking for basic types (Int and Nat)
	SAL_RSL_is_Int_Vid
	SAL_RSL_is_Nat_Vid

	MapApplicationNav
        ArrayApplicationNav
	Collected_Reconstructors
	Collected_Is_Type_Functions
	Collected_Lifted_Constructors
	Collected_Lifted_Destructors
	SAL_Current_Reconstructor
	InvalidCollectionInsertionNav
	SwapNav

'var' SAL_GLOBAL_Cid	      : SAL_context_id
'var' SAL_TYPES_Cid	      : SAL_context_id
'var' SAL_CC_GLOBAL_Cid	      : SAL_context_id
'var' SAL_CC_TYPES_Cid	      : SAL_context_id

'var' Global_Model		 : SAL_MODEL
'var' Global_CC_Model		 : SAL_MODEL

'var' SAL_Current_Cid		 : SAL_context_id
'var' SAL_Current_CC_Cid	 : SAL_context_id

--------------------------------------------------
-- This environment is used during function body 
-- generation. In this case, all the
-- bindings introduced in the function signature, 
-- like in:
--
-- next : Int >< Lift -> Lift
-- next(x, (a,b,c)) is ...
--
-- where a, b and c are names for the values 
-- inside the Lift 3-uple. 
-- As it is not possible to introduce this kind of
-- bindings in SAL, it is necessary to convert 
   -- this identifiers into the proper field number 
-- (i.e. a = 1, b = 2, c = 3).
-------------------------------------------------- 

'var' Current_LBS_Env : BINDING_NAMESPACE_STACK

-- Used for Let identifier generation:
'var' LetIndex : INT

'var' ParamIndex : INT

'var' TypeIndex : INT

'var' SortIndex : INT

-- Used for created type boundaries temporal storage
-- (They'll be collected later in the second pass and moved into the
-- SAL_GLOBAL context)
'var' Generated_Constants    :	SAL_CONSTANT_DECLS

'var' Generated_Contexts      : SAL_CONTEXTS
'var' Generated_CC_Contexts   : SAL_CONTEXTS

'var' Generated_Operation_Contexts    : SAL_CONTEXTS
'var' Generated_CC_Operation_Contexts : SAL_CONTEXTS
-- Global Collections:
'var' Global_Cid_Table    : SAL_CONTEXT_IDS
'var' Global_Tid_Table    : SAL_TYPE_IDS
'var' Global_CC_Tid_Table : SAL_TYPE_IDS
'var' Global_Vid_Table	  : SAL_VALUE_IDS
'var' Global_Oid_Table	  : SAL_OBJECT_IDS
'var' Global_Var_Table	  : SAL_VARIABLE_IDS
'var' Global_TS_Table	  : SAL_TRANSYS_IDS

'var' Global_Constant_Table : CONSTANT_DATA_LIST
-- Default type's context- and type-ids:
'var' Default_Int_Cid	      : SAL_context_id
'var' Default_Int_Tid	      : SAL_type_id

'var' Default_Nat_Cid	      : SAL_context_id
'var' Default_Nat_Tid	      : SAL_type_id

'var' NatHighIdent	      : IDENT
'var' NatHighVal	      : IDENT
'var' IntHighIdent	      : IDENT
'var' IntHighVal	      : IDENT
'var' IntLowIdent	      : IDENT
'var' IntLowVal	      	      : IDENT

'var' Default_Bool_Cid	      : SAL_context_id
'var' Default_Bool_Tid	      : SAL_type_id

'var' Current_List_Types      : SAL_LIST_TYPES
'var' Current_Set_Types	      :	SAL_LIST_TYPES
'var' Current_Map_Types	      :	SAL_LIST_TYPES
'var' Current_Array_Types	      :	SAL_LIST_TYPES
'var' Current_CC_Lifted_Types : SAL_LIST_TYPES

'var' Default_Set_Cid	      : SAL_context_id
'var' Default_Set_Tid	      : SAL_type_id

'var' Default_Map_Cid	      : SAL_context_id
'var' Default_Map_Tid	      : SAL_type_id

'var' SAL_Nav_Tid	      :	SAL_type_id

'var' Disamb_Stack	      : VALUE_EXPRS

'var' SAL_Types_Extra_Defs    :	SAL_CONTEXT_CONSTANTS
-- not used cwg
-- 'var' SAL_Types_Extra_CC_Defs :	SAL_CONTEXT_CONSTANTS
'var' Collected_Reconstructors: SAL_CONTEXT_CONSTANTS
'var' Collected_Is_Type_Functions : SAL_CONTEXT_CONSTANTS
'var' Collected_Lifted_Constructors : SAL_CONTEXT_CONSTANTS
'var' Collected_Lifted_Destructors : SAL_CONTEXT_CONSTANTS
'var' SAL_Current_Reconstructor : OPT_VALUE_ID

'var' Current_cid_stack	      : CID_STACK

'var' MapApplicationNav	      : OPT_SAL_VALUE_ID
'var' ArrayApplicationNav	: OPT_SAL_VALUE_ID
'var' InvalidCollectionInsertionNav : OPT_SAL_VALUE_ID
'var' SwapNav : OPT_SAL_VALUE_ID
------------------------
'var' SAL_RSL_is_Int_Vid : SAL_value_id
'var' SAL_RSL_is_Nat_Vid : SAL_value_id

--added CWG 13/4/08 to save types and constants defined in SAL_TYPES
'var' SAL_TYPES_Constants	 : SAL_CONTEXT_CONSTANTS


--------------------------------------------------------------------------------------
-- OPERATIONS
--------------------------------------------------------------------------------------

'action' Init_Operation_Context()

  'rule' Init_Operation_Context()
	 Generated_Operation_Contexts <- nil
	 Generated_CC_Operation_Contexts <- nil

'action' SAL_Add_Operation_Context(SAL_CONTEXT)

  'rule' SAL_Add_Operation_Context(Context)
	 Generated_Operation_Contexts -> List
	 where(SAL_CONTEXTS'list(Context,List) -> NewList)
	 Generated_Operation_Contexts <- NewList

'action' SAL_Add_CC_Operation_Context(SAL_CONTEXT)

  'rule' SAL_Add_CC_Operation_Context(Context)
	 Generated_CC_Operation_Contexts -> List
	 where(SAL_CONTEXTS'list(Context,List) -> NewList)
	 Generated_CC_Operation_Contexts <- NewList

'action' Get_Operation_Contexts(-> SAL_CONTEXTS)

  'rule' Get_Operation_Contexts(-> Contexts)
	 Generated_Operation_Contexts -> Contexts

'action' Get_CC_Operation_Contexts(-> SAL_CONTEXTS)

  'rule' Get_CC_Operation_Contexts(-> Contexts)
	 Generated_CC_Operation_Contexts -> Contexts

'action' Init_Constant_Table()

  'rule' Init_Constant_Table()
	 Global_Constant_Table <- nil

'action' Insert_Constant(SAL_value_id, SAL_type_id)

  'rule' Insert_Constant(Vid,Tid)
	 Global_Constant_Table  -> Table
	 Global_Constant_Table <- list(info(Vid,Tid), Table)
--Vid'IdOp -> Id
--SAL_Print_IdOp(Id)
--Putmsg(" added\n")
