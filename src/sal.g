-- RSL Type Checker
-- Copyright (C) 2005 UNU/IIST

-- raise@iist.unu.edu

-- This module is the main module for
-- the RSL to SAL translator
-- It calls all the other modules

'module' sal


'use' ast print ext env objects values types pp cc sml 
      sal_ast          -- SAL Abstract Syntax
      sal_aux          -- Auxiliary SAL Actions
      sal_cc_aux       -- Auxiliary actions for the SAL-cc generation...
      pvs_aux	       -- Auxiliary PVS actions:
			  -- Insert_Ident
      pvs_ast
      sal_decl_sort    -- Collects and Sorts the Declareds (define before use)
      sal_gen_ast      -- Generates SAL Abstract Syntax Tree
      sal_gen_code     -- Generates SAL code
		       -- SAL_Init_Var_Gen_Code
      sal_print

      sal_global_vars  -- SAL_Current_Cid

'export' SAL_init  -- init and open SAL output file

	 SAL_Process_Top_Level_Scheme

	 SAL_Process_Top_Level_Object
	 SAL_Process_Object

	 SAL_Translate
--	 SAL_IsCurrentContext
--	 SAL_IsCurrentObject

	 -- Exported for re-use in sal_gen_ast (when processing object instantiations)
	 SAL_Trans_Class


--------------------------------------------------
-- variables
--------------------------------------------------

'var' Filename_sal               : STRING
'var' SAL_Current_object	 : OPT_OBJECT_ID
--------------------------------------------------
-- Actions
--------------------------------------------------

--------------------------------------------------
'action' SAL_init

  'rule' SAL_init:
	 Init_SAL_file
	 Init_SAL_vars
 	 SAL_Init_Aux
	 SAL_Init_Gen_ast

--------------------------------------------------
'action' Init_SAL_vars

  'rule' Init_SAL_vars:
	 -- Initialize variable TotalDeclareds
	 SAL_Init_TotalDeclareds
--	 Init_Indexes
	 Global_Model <- model(nil)
	 Global_CC_Model <- model(nil)
	 string_to_id("NatHigh" -> NatHighId)
	 NatHighIdent <- NatHighId
	 string_to_id("4" -> NatHighValId)
	 NatHighVal <- NatHighValId
	 string_to_id("IntHigh" -> IntHighId)
	 IntHighIdent <- IntHighId
	 string_to_id("4" -> IntHighValId)
	 IntHighVal <- IntHighValId
	 string_to_id("IntLow" -> IntLowId)
	 IntLowIdent <- IntLowId
	 string_to_id("-4" -> IntLowValId)
	 IntLowVal <- IntLowValId

---------------------------------------------------------------------------------
-- SAL_Process_Global_Scheme
---------------------------------------------------------------------------------
-- Process each RSL Scheme individually, filling the SAL model with
-- the information derived from there.
-- The generated SAL-AST (intermediate form) is stored in the var:
-- Global_model
---------------------------------------------------------------------------------

'action' SAL_Process_Top_Level_Scheme(IDENT, FILE_NAMES, OBJECT_DEFS, CLASS)

  'rule' SAL_Process_Top_Level_Scheme(Ident, Context, Params, ClassExpr):
         (|
           HasErrors()  -- no need for message: ???
         ||
	   -- Handled as if it were a global OBJECT (schemes do not generate context in the general case,
	   -- they are translated only when instantiated...)
           eq(Params, nil)
	   -- translate parameterless global schemes
--         Putmsg("Processing Global scheme ")
--	   Print_id(Ident)
--	   Putmsg(" ... ")
--	   Putnl()

	   -- Generating the Cid for the context:
	     -- (Context arg. number set to zero initially)
	   New_SAL_context_id(Ident, 0 -> Cid)
	   -- Making the current context globaly available
	     -- (used by the sal-constants generators)
	   SAL_Current_Cid <- Cid

	   -- Generating the Cid for the context:
	   Cid'Lifted_Cid -> cid(CC_Cid)
	   CC_Cid'Ident -> CC_Id
	   -- Making the current context globaly available
	     -- (used by the sal-constants generators)
	   SAL_Current_CC_Cid <- CC_Cid

	   -- Process the context (generating the SAL_CONTEXT_ELEMENTS):
	   SAL_Trans_Class_expr(ClassExpr -> Context_Decls, CC_Decls)

	   -- Generating the context:
	   where(context(Ident,cid(Cid), Context_Decls) -> Current_Context)
	   -- Updating the Data and Static part in the CId:
	   SAL_Separate_Decls(Context_Decls -> Data, Static)
	   Cid'State <- Data
	   Cid'Static <- Static
	   -- Adding the new context to the SAL-MODEL:
	   Global_Model -> Model
	   where(Model -> model(Context_list))
	   where(SAL_CONTEXTS'list(Current_Context, Context_list) -> Extended_model)
	   Global_Model <- model(Extended_model)

	   -- CC version book-keeping: (same as above but with name modifications:
	   -- Generating the context:
	   where(context(CC_Id,cid(CC_Cid), CC_Decls) -> CC_Context)
	   -- Updating the Data and Static part in the CId:
	   SAL_Separate_Decls(CC_Decls -> CCData, CCStatic)
	   CC_Cid'State <- CCData
	   CC_Cid'Static <- CCStatic
	   -- Adding the new context to the SAL-MODEL:
	   Global_CC_Model -> Model1
	   where(Model1 -> model(Context_list1))
	   where(SAL_CONTEXTS'list(CC_Context, Context_list1) -> Extended_model1)
	   Global_CC_Model <- model(Extended_model1)
         ||
           -- Puterror(Pos)
	   Putmsg("Parametric Schemes are not allowed")
	   Putnl()
         |)

---------------------------------------------------------------------------

'action' SAL_Process_Top_Level_Object(IDENT, FILE_NAMES, Object_id, CLASS)	-- level 1

  'rule' SAL_Process_Top_Level_Object(Ident, Context, Objectid, ClassExpr):
         (|
           HasErrors()  -- no need for message: generated in Translate_to_SAL
         ||
--	   Putmsg("Processing ")
--	   Print_id(Ident)
--	   Putmsg(" ... ")
--	   Putnl()

	   Objectid'Pos -> Pos
	   -- Generating the Cid for the context:
	   New_SAL_context_id(Ident, 0 -> Cid)
	   -- Making the current context globaly available
	     -- (used by the sal-constants generators)
	   SAL_Current_Cid <- Cid

   	   Cid'Lifted_Cid -> cid(CC_Cid)
	   CC_Cid'Ident -> CC_Id
	   -- Making the current context globaly available
	     -- (used by the sal-constants generators)
	   SAL_Current_CC_Cid <- CC_Cid

	   -- Process the context (generating the SAL_CONTEXT_ELEMENTS):
	   SAL_Trans_Class_expr(ClassExpr -> Context_Decls, CC_Decls)
	   -- Generating the context:
	   where(context(Ident,cid(Cid), Context_Decls) -> Current_Context)
	   -- Updating the Data and Static part in the CId:
	   SAL_Separate_Decls(Context_Decls -> Data, Static)
	   Cid'State <- Data
	   Cid'Static <- Static
	   -- Adding the new context to the SAL-MODEL:
	   Global_Model -> Model
	   where(Model -> model(Context_list))
	   where(SAL_CONTEXTS'list(Current_Context, Context_list) -> Extended_model)
	   Global_Model <- model(Extended_model)

	   -- cc version:
	   -- Generating the context:
	   where(context(CC_Id,cid(CC_Cid), CC_Decls) -> Current_CC_Context)
	   -- Updating the Data and Static part in the CId:
	   SAL_Separate_Decls(CC_Decls -> CCData, CCStatic)
	   CC_Cid'State <- CCData
	   CC_Cid'Static <- CCStatic
	   -- Adding the new context to the SAL-MODEL:
	   Global_CC_Model -> Model1
	   where(Model1 -> model(Context_list1))
	   where(SAL_CONTEXTS'list(Current_CC_Context, Context_list1) -> Extended_model1)
	   Global_CC_Model <- model(Extended_model1)

	   -- Generating the instantiation in the current environment:
	   New_SAL_object_id(Pos,Ident,Cid,cid(Cid) -> Oid) -- The object is defining an schema at the same time, that's why
							    -- the definition and instantiation Cids are the same here...
	   Oid'State <- Data
	   Oid'NonState <- Static
	   -- Updating the cc-info in the Oid (Not used so far...)
	   Oid'CCState <- CCData
	   Oid'CCNonState <- CCStatic

         ||
           Objectid'Pos -> Pos
	   Puterror(Pos)
	   Putmsg("object arrays not supported")
	   Putnl()
         |)


---------------------------------------------------------------------------
'action' SAL_Process_Object(IDENT, FILE_NAMES, CLASS)

  'rule' SAL_Process_Object(Ident, Context, ClassExpr):
         (|
           HasErrors()  -- no need for message: generated in Translate_to_SAL
         ||
--	   Putmsg("Processing ")
--	   Print_id(Ident)
--	   Putmsg(" ... ")
--	   Putnl()

	   -- Generating the Cid for the context:
	   New_SAL_context_id(Ident, 0 -> Cid)
	   -- Making the current context globaly available
	     -- (used by the sal-constants generators)
	   SAL_Current_Cid <- Cid

	   Cid'Lifted_Cid -> cid(CC_Cid)
	   CC_Cid'Ident -> CC_Id
	   -- Making the current context globaly available
	     -- (used by the sal-constants generators)
	   SAL_Current_CC_Cid <- CC_Cid

	   -- Process the context (generating the SAL_CONTEXT_ELEMENTS):
	   SAL_Trans_Class_expr(ClassExpr -> Context_Decls, CC_Decls)
	   -- Generating the context:
	   where(context(Ident,cid(Cid), Context_Decls) -> Current_Context)
	   -- Updating the Data and Static part in the CId:
	   SAL_Separate_Decls(Context_Decls -> Data, Static)
	   Cid'State <- Data
	   Cid'Static <- Static
	   -- Adding the new context to the SAL-MODEL:
	   Global_Model -> Model
	   where(Model -> model(Context_list))
	   where(SAL_CONTEXTS'list(Current_Context, Context_list) -> Extended_model)
	   Global_Model <- model(Extended_model)

	   -- cc-version:
	   -- Generating the context:
	   where(context(CC_Id,cid(CC_Cid), CC_Decls) -> Current_CC_Context)
	   -- Updating the Data and Static part in the CId:
	   SAL_Separate_Decls(CC_Decls -> CC_Data, CC_Static)
	   CC_Cid'State <- CC_Data
	   CC_Cid'Static <- CC_Static
	   -- Adding the new context to the SAL-MODEL:
	   Global_CC_Model -> Model1
	   where(Model1 -> model(Context_list1))
	   where(SAL_CONTEXTS'list(Current_CC_Context, Context_list1) -> Extended_model1)
	   Global_CC_Model <- model(Extended_model1)
         |)


---------------------------------------------------------------------------------------
-- SAL_Translate
---------------------------------------------------------------------------------------
-- This function invokes the different routines for transforming the
-- AST:
--     * Type definition reordering (SAL_TYPES generation).
--     * SAL_GLOBAL context generation (collect type boundaries)
-- And for code generation.
---------------------------------------------------------------------------------------
'action' SAL_Translate

  'rule' SAL_Translate:
	 Global_Model -> Current_Model
	 where(Current_Model -> model(Contexts))
	 SAL_Refine_ast(Contexts,nil -> Sorted_Contexts)
	 where(model(Sorted_Contexts) -> Sorted_Model)
	 -- Outputs the translation:
	 (|
	     HasErrors()
	 ||
	     SAL_Out_Model(Sorted_Model)
	 |)
Putmsg("Done with the non-cc version\n")
	 -- CC model processing:
	 Global_CC_Model -> Current_CC_Model
	 where(Current_CC_Model -> model(CC_Contexts))
	 SAL_Refine_CC_ast(CC_Contexts,nil -> Sorted_CC_Contexts)
	 where(model(Sorted_CC_Contexts) -> Sorted_CC_Model)
	 -- Outputs the translation:
	 (|
	     HasErrors()
	 ||
	     SAL_Out_Model(Sorted_CC_Model)
	 |)
Putmsg("Done with the complex cc version\n")
	 SAL_Refine_Simple_CC_ast(CC_Contexts,nil -> Simple_CC_Contexts)
	 where(model(Simple_CC_Contexts) -> Simple_CC_Model)
	 -- Outputs the translation:
	 (|
	     HasErrors()
	 ||
	     SAL_Out_Model(Simple_CC_Model)
	 |)
Putmsg("Done with the simple cc version\n")

--------------------------------------------------
--            TRANSLATION FUNCTIONS             --
--------------------------------------------------

'action' SAL_Trans_Class_expr(CLASS -> SAL_CONTEXT_CONSTANTS,  -- normal version (assumming cc satisfaction)
				       SAL_CONTEXT_CONSTANTS)  -- cc-version

  'rule' SAL_Trans_Class_expr(Class -> Context_Decls, CC_Decls):
	 Resolve_class(Class)
	 SAL_Trans_Class(Class -> Context_Decls, CC_Decls)


'action' SAL_Trans_Class(CLASS -> SAL_CONTEXT_CONSTANTS,  -- normal version (assumming cc satisfaction)
				  SAL_CONTEXT_CONSTANTS)  -- cc-version

  'rule' SAL_Trans_Class(basic(Decls) -> Context_Decls, CC_Decls):
	 SAL_Process_Decls(Decls -> Context_Decls, CC_Decls)

  'rule' SAL_Trans_Class(extend(Class1, Class2) -> Context_Decls, CC_Decls):
	 In_left
	 SAL_Trans_Class(Class1 -> Decls1, CC_Decls1)
	 Left_right
	 SAL_Trans_Class(Class2 -> Decls2, CC_Decls2)
	 Out_right
	 -- Building the non cc-result:
	 SAL_Concatenate_Context_Constants(Decls1, Decls2 -> Context_Decls)
	 -- Building the cc-version:
	 SAL_Concatenate_Context_Constants(CC_Decls1, CC_Decls2 -> CC_Decls)

  'rule' SAL_Trans_Class(instantiation(name(Pos,
                                             id_op(Id)),
                                             Objs) -> Context_Decls, CC_Decls):

	 Get_id_of_scheme(Id -> scheme_id(Schemeid))
         Schemeid'With -> With 
         Set_current_with(With)
         Schemeid'Class -> ClassExpr

	 -- Just translate the class expression:
	 SAL_Trans_Class(ClassExpr -> Context_Decls, CC_Decls)


  'rule' SAL_Trans_Class(hide(Defnds, ClassExpr) -> Context_Decls, CC_Decls):
	 [|
	   where(Defnds -> list(Def, _))
	   (|
             where(Def -> def_name(Pos, _))
           ||
             where(Def -> disamb(Pos, _, _))
           |)
	   Putwarning(Pos)
	   Putmsg("hidings are ignored")
	   Putnl()
	 |]
	 SAL_Trans_Class(ClassExpr -> Context_Decls, CC_Decls)

  'rule' SAL_Trans_Class(rename(Renames, ClassExpr) -> Context_Decls, CC_Decls):
	 [|
	   where(Renames -> list(rename(Def, _), _))
	   (|
             where(Def -> def_name(Pos, _))
           ||
             where(Def -> disamb(Pos, _, _))
           |) 
	   Putwarning(Pos)
	   Putmsg("renamings are ignored")
	   Putnl()
	 |]
	 SAL_Trans_Class(ClassExpr -> Context_Decls, CC_Decls)

  'rule' SAL_Trans_Class(with(_, _, ClassExpr) -> Context_Decls, CC_Decls):
	 SAL_Trans_Class(ClassExpr -> Context_Decls, CC_Decls)

  'rule' SAL_Trans_Class(nil -> nil,nil):

  'rule' SAL_Trans_Class(T -> nil,nil):
	 Putmsg("Debugging activated in SAL_Trans_Class\n")
--	 print(T)

--------------------------------------------------
'action' SAL_Process_Decls(DECLS -> SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Process_Decls(DeclsRSL -> ContextElements, CC_Elems):

	 -- The sorting rules are the same for both versions...
	 SAL_Gen_Declareds(DeclsRSL, nil -> Declareds)
	 SAL_Sort_Declareds(Declareds,      -- ToDo 
                       nil,            -- Waiting
                       nil,            -- Done
                       nil             -- Found
                       -> SortedDeclareds)
	 SAL_Gen_ast(SortedDeclareds, nil, nil -> ContextElements, CC_Elems)

/*
'condition' SAL_IsCurrentContext(IDENT)

  'rule' SAL_IsCurrentContext(Id):
--	 SAL_Current_context -> CId
	 eq(Id, Id)

'condition' SAL_IsCurrentObject(Object_id)

  'rule' SAL_IsCurrentObject(I):
	 SAL_Current_object -> object_id(OI)
	 eq(I, OI)	   	
*/
'action' Init_SAL_file

  'rule' Init_SAL_file:
         Module_name -> S	-- in env.g (STRING)
         string_to_id(S -> Id)  -- in idents.c
         SetFileIndentSpace(4)  -- in files.c
