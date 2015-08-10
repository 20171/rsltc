-- RSL Type Checker
-- Copyright (C) 2005 UNU/IIST

-- raise@iist.unu.edu

-- This module generates SAL abstract syntax tree
-- from the sorted declareds
-- Implementation:
-- First pass: SAL_Gen_ast
-- Second pass: SAL_Refine_ast

'module' sal_gen_ast

'use' ast print ext env objects values 
      types	   -- Make_function_type
      pp 

      sal          -- Reuse of SAL_Trans_Class (to translate the CLASS expr in object instantiations)
      cc	   -- Pattern_match  
		   -- Split_fun_type
      cpp	   -- Rearrange_application
      sml	   -- Matches_binding
      sal	   -- main translation file
      sal_ast	   -- AST for SAL language
      sal_aux	   -- auxiliar definitions
      sal_cc_aux
      pvs_aux	   -- Collect_Value_ids
		   -- Is_Recursive_Function


      sal_global_vars
      sal_print
      sal_decl_sort
     
      sal_gen_code

      sal_type_fixed_point

      pvs_ast	   -- type declarations for SORTING ONLY 
		   -- SAL AST is defined in "sal_ast.g"

      pvs_gen_ast  -- Debracket_abbrev
		   -- Get_Type_of_Value_Expr

      pvs_gen_code -- Gen_Prod_Ident


'export' 
      -- Init:
      SAL_Init_Gen_ast
      -- First pass: (RSL-AST -> SAL-AST v1)
      SAL_Gen_ast
      -- Second pass: (SAL-AST v1 -> SAL-AST v2)
      SAL_Refine_CC_ast
      SAL_Refine_Simple_CC_ast
      SAL_Refine_ast

      -- Routine used for splitting context decls.
      -- Exported to be used in sal.g
      SAL_Separate_Decls

      -- Exported for reuse in sal_aux.g
      SAL_Gen_Type_Expr
      Gen_SAL_Id_Op
      Gen_SAL_literal_expr

      -- For reuse in sal_cc_aux
      SAL_Generate_Context

'var' Global_TYPES_Cid	      : SAL_context_id



------------------------------------------------------------------------------
-- SAL_Init_Gen_ast
------------------------------------------------------------------------------
-- Initialization rules for the AST
------------------------------------------------------------------------------
'action' SAL_Init_Gen_ast

  'rule' SAL_Init_Gen_ast:
 	 Init_SAL_AST

	 -- SAL_GLOBAL Context:
 	 -- Generate the context id:
	 string_to_id("SAL_GLOBAL" -> Ident)
	 -- Generate the Cid:
	 New_SAL_context_id(Ident,0 -> SAL_Global)
	 -- The static part of this context (constant declarations for
	 -- type boundaries) will be collected in the second pass...
	 SAL_GLOBAL_Cid <- SAL_Global

	 string_to_id("SAL_TYPES" -> TYPESId)
	 -- Generate the Cid for the new context:
	 New_SAL_context_id(TYPESId, 0 -> TypesCid)
	 SAL_TYPES_Cid <- TypesCid	 

	 string_to_id("Not_a_value_type" -> Nav_Id)
	 DefaultPos(-> P)
	 New_SAL_NAV_type_id(P, Nav_Id, TypesCid, unit -> Nav_Tid)
	 SAL_Nav_Tid <- Nav_Tid


	 SAL_Gen_CC_id(TYPESId -> CC_TYPESId)
	 -- Generate the Cid for the new context:
	 TypesCid'Lifted_Cid -> cid(CC_TypesCid)
	 SAL_CC_TYPES_Cid <- CC_TypesCid
	 
	 -- Generated contexts due to object declarations:
	 Generated_CC_Contexts <- nil
	 Generated_Contexts <- nil
	 -- Generated constant decls. for type boundaries:
	 Generated_Constants <- nil

	 -- Used to collect value declarations used for type decls:
	 -- not used cwg
	 -- SAL_Types_Extra_CC_Defs <- nil
	 SAL_Types_Extra_Defs <- nil
	 -- Used to collect side declarations in the cc version:
	 Collected_Reconstructors <- nil
	 Collected_Is_Type_Functions <- nil
	 Collected_Lifted_Constructors <- nil
	 Collected_Lifted_Destructors <- nil
	 SAL_Current_Reconstructor <- nil
	 InvalidCollectionInsertionNav <- nil
	 SwapNav <- nil
	 SAL_TYPES_Constants <- nil

	 -- Initialising the list of operation contexts:
	 Init_Operation_Context
	 Init_Constant_Table

	 SAL_Init_Var_Gen_Code

     -- Basic types context initialization:
	 -- BOOLEAN:
	 SAL_Gen_Bool_Context_and_Tid
	 -- INTEGER:
	 SAL_Gen_Int_Context_and_Tid
	 -- NATURAL
	 SAL_Gen_Nat_Context_and_Tid

	 -- Init the CC type collection:
	 Init_SAL_CC_Collection

	 -- Initialize the current stack cid:
	 Current_cid_stack <- nil

	 MapApplicationNav <- nil

         ArrayApplicationNav <- nil
-------------------------------------------------------------------------------
-- SAL_Gen_ast
-------------------------------------------------------------------------------
-- Interface of the first pass...
-- Generates the conversion Sorted_declarations --> SAL_ast (first version)
-------------------------------------------------------------------------------
'action' SAL_Gen_ast(SORTED_DECLS,	    -- Sorted RSL declarations
		     SAL_CONTEXT_CONSTANTS, -- Already translated constructions (non CC version) 
		     SAL_CONTEXT_CONSTANTS  -- Already translated constructions (CC version) 
				  -> SAL_CONTEXT_CONSTANTS,  -- SAL's AST elements (non CC) 
				     SAL_CONTEXT_CONSTANTS)-- SAL's AST elements (CC version)

  'rule' SAL_Gen_ast(list(Declared, DeclaredsTail), ContextElems, CC_ContextElems -> ExtendedContextElems, CC_ExtendedContextElems):

	 SAL_Process_Declared(Declared, ContextElems, CC_ContextElems -> ContextElems1, CC_ContextElems1)
	 SAL_Gen_ast(DeclaredsTail, ContextElems1, CC_ContextElems1 -> ExtendedContextElems, CC_ExtendedContextElems)


  'rule' SAL_Gen_ast(nil, ContextElements, CC_ContextElems -> ContextElements, CC_ContextElems):
--Putmsg("Ordinary elements:\n")
--SAL_Print_Constants(ContextElements)
--Putmsg("Cc elements:\n")
--SAL_Print_Constants(CC_ContextElems)


---------------------------------------------------------------------------------
-- SAL_Process_Declared
---------------------------------------------------------------------------------
-- Actual processing of the declarations....
---------------------------------------------------------------------------------
'action' SAL_Process_Declared(SORTED_DECL_ITEM, SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS 
				       -> SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Process_Declared(type_item(Typeid), ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut):
  	 -- No longer necessary: added for SAL in values.g, resolved
  	 -- in cc.g CWG 12/4/08
	 -- SAL_Add_destructors(Typeid)
	 Typeid'Type -> Type
	 SAL_Process_Type_id(Type, Typeid, ContextElements,
	 CC_ContextElements -> ContextElementsout,
	 CC_ContextElementsOut)


  'rule' SAL_Process_Declared(value_item(Valueid), ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut):
	 Valueid'Def -> Def
	 SAL_Process_Value_id(Valueid, Def, normal_function, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut)

  'rule' SAL_Process_Declared(object_item(Pos,Id,Params,Class), 
					ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut):
	 SAL_Process_Object_Decl(object_item(Pos,Id,Params,Class),
					ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut)

  'rule' SAL_Process_Declared(ts_item(TSid), ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut)
	 SAL_Process_Transition_System(TSid, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut)

  'rule' SAL_Process_Declared(prop_item(Pid), ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut)
	 SAL_Process_Property(Pid,  ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut)	 

         -- Skipping the non translatable items (errors have already been reported)
	 -- Cases: recursive items, mutually-rec items
	 -- Ignoring other elements: Axioms, lemmas... 
  'rule' SAL_Process_Declared(T, ContextElements, CC_ContextElements  -> ContextElements, CC_ContextElements):
       
-----------------------------------------------------------------------
-- SAL_Process_Type_id
-----------------------------------------------------------------------
-- Type declaration processing...
-----------------------------------------------------------------------
'action' SAL_Process_Type_id(TYPE, Type_id, SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

	 -- Skipping undefined types (previous error in the resolver)
	 -- this rule is to avoid the 'undefined rule' msg...
  'rule' SAL_Process_Type_id(undef_type, Typeid, ContextElements, CC_ContextElements  -> ContextElements, CC_ContextElements): 
	 
  'rule' SAL_Process_Type_id(sort(SortKind), Typeid, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut):
	 Typeid'Pos -> Pos
	 SAL_Process_Sort_Kind(Pos,SortKind, Typeid, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut)

  'rule' SAL_Process_Type_id(abbrev(TypeExpr), Typeid, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut):
	 Typeid'Def -> Def
	 SAL_Process_abbrev(Typeid, Def, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut)

------------------------------------------------------------------------
-- SAL_Process_Value_id
------------------------------------------------------------------------
-- Value declarations processing...
------------------------------------------------------------------------

'action' SAL_Process_Value_id(Value_id, VALUE_DEFINITION, SAL_IS_IN_VALUE, SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS 
					-> SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

	 -- No Value Definition
  'rule' SAL_Process_Value_id(Valueid, no_def, _, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut):
	 -- Processing the declaration...
	 -- if it is an undef value of basic type (like Max : Int)
	 -- it can be initialized (with a warning) to a default value...
	 -- otherwise (it is an undefined function) the error is reported but
	 -- the declaration is processed anyway (error recovery)
	 Valueid'Pos -> Pos
	 Valueid'Ident -> Ident
	 Gen_SAL_Id_Op(Pos, Ident,none,none -> IdOp, _) -- the idOp is, in this case, a name, so no difference with the cc version
	 Valueid'Type -> TypeExpr
	 SAL_Gen_Type_Expr(Pos, TypeExpr -> SALTypeExpr, LiftedType)
	 -- Generating the Value Id:
	 where(Ident -> id_op(Ident1))
	 SAL_Current_Cid -> Cid
	 (|
	    where(SALTypeExpr -> rsl_built_in(integer(_)))
	    New_SAL_value_id(Pos, IdOp, Cid, SALTypeExpr, constant -> Vid)
	    id_to_string(Ident1 -> IdStr)
	    Concatenate("Assuming constant declaration (",IdStr -> Str1)
	    Concatenate(Str1, "), initializing with default value\n" -> Str)
	    Putwarning(Pos)
	    Putmsg(Str)
	    SAL_Gen_Init_Expr(SALTypeExpr -> InitExpr)
	    where(sal_const_decl(sal_expl_const(IdOp,Vid, SALTypeExpr, InitExpr)) -> ContextElement)
	    -- getting the lifted vid:
	    Vid'Lifted_Vid -> LVid
	    where(sal_const_decl(sal_expl_const(IdOp,LVid, LiftedType, InitExpr)) -> CC_ContextElement)
	 ||
	    Puterror(Pos)
	    Putmsg("Implicit/undefined value definitions not supported")
	    Putnl()
	    where(sal_const_decl(sal_nodef(IdOp,SALTypeExpr, no_def)) -> ContextElement)
	    where(ContextElement -> CC_ContextElement)
	 |)
	 Insert_Context_Element(ContextElement, ContextElements -> ContextElementsout)

	 -- Confidence condition version:
	 Insert_Context_Element(CC_ContextElement, CC_ContextElements -> CC_ContextElementsOut)

	 -- Explicit Value Definition
  'rule' SAL_Process_Value_id(Valueid, expl_val(ValExpr, Cond), _, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> Ident
-- CWG debug
--Putmsg("Constant: ")
--Print_id_or_op(Ident)
--Putnl()
--[|
--where(Cond -> condition(C))
--Putmsg("Condition: ")
--Print_expr(C)
--Putnl()
--|]
	 (| -- explicit values stored as disambiguations (from cpp)
	   where(ValExpr -> disamb(Pos2, ValExprDis, _))
	 ||
	   where(ValExpr -> ValExprDis)
	 |)
--Putmsg(" = ")
--Print_expr(ValExprDis)
--Putnl()
--print(ValExprDis)
	 Gen_SAL_Id_Op(Pos, Ident,none,none -> IdOp, _) -- The idOp is just a name here (uses de id part of the IdOp) 
						        -- and names are shared among the cc and non-cc versions
	 Valueid'Type -> TypeExpr
	 SAL_Gen_Type_Expr(Pos, TypeExpr -> SALTypeExpr, CC_SALType)
	 Gen_SAL_Expr(ValExprDis,normal,TypeExpr -> SALExpr,
	 SAL_CC_Expr)
	 SAL_Current_Cid -> Cid
	 SAL_Convert_Id_Op(Ident -> Id)
	 New_SAL_value_id(Pos, Id,Cid,SALTypeExpr,regular_value -> Vid)
	 where(sal_const_decl(sal_expl_const(IdOp,Vid,SALTypeExpr, SALExpr))-> ContextElement)
	 Insert_Context_Element(ContextElement, ContextElements -> ContextElementsout)

	 [|
	   where(Ident -> id_op(IdentId))
	   where(ValExprDis -> literal_expr(_, int(ValId)))
	   Match(TypeExpr, up, int)
	   [|
	     -- check for NatHigh
	     NatHighIdent -> NHI
	     eq(IdentId, NHI)
	     NatHighVal <- ValId
	     id_to_string(NHI -> NHString)
	     Concatenate("Default", NHString -> DNHString)
	     string_to_id(DNHString -> DNHI)
	     Update_Global_Constant(DNHI, ValId)
	     Putmsg("DefaultNatHigh set to ")
	     Print_id(ValId)
	     Putnl()
	   |]
	   [|
	     -- check for IntHigh
	     IntHighIdent -> IHI
	     eq(IdentId, IHI)
	     IntHighVal <- ValId
	     id_to_string(IHI -> IHString)
	     Concatenate("Default", IHString -> DIHString)
	     string_to_id(DIHString -> DIHI)
	     Update_Global_Constant(DIHI, ValId)
	     Putmsg("DefaultIntHigh set to ")
	     Print_id(ValId)
	     Putnl()
	   |]
	   [|
	     -- check for IntLow
	     IntLowIdent -> ILI
	     eq(IdentId, ILI)
	     IntLowVal <- ValId
	     id_to_string(ILI -> ILString)
	     Concatenate("Default", ILString -> DILString)
	     string_to_id(DILString -> DILI)
	     Update_Global_Constant(DILI, ValId)
	     Putmsg("DefaultIntLow set to ")
	     Print_id(ValId)
	     Putnl()
           |]
         |]

-- CWG added
         (|
	   IncreaseCol(Pos -> PosII) -- it is necessary, otherwise, when looking up the
				      -- tid on a function occ, the Vid of the violation is found
				      -- rather the function's vid 
	   where(Cond -> condition(RSLSubtypeCond))
	   -- note RSLSubtypeCond has RSL_res_ as a free variable
	   -- cc version is
	   -- let RSL_res_ = SAL_CC_Expr in 
           --   if is_true(SubtypeCond) then RSL_res_ else nav end
	   -- generate Value_id for RSL_res_
	   string_to_id("RSL_res_" -> ResId)
	   -- turn into a namespace
	   where(BINDING'single(PosII, id_op(ResId)) -> Bind) --jiperna (changed Pos with PosII)
	   SAL_Gen_Type_List(list(Bind, nil), TypeExpr -> T11)
	   SAL_Prepare_Bindings(list(Bind,nil), T11 -> PreparedBS)
	   Gen_SALFormal_Parameter(PreparedBS, T11 -> _, Namespace1, CC_Args)
	   -- make is_true operator
	   Default_Bool_Tid -> BTid
	   BTid'Lifted_Tid -> tid(LBTid)
	   where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	   -- Generating the string for the nav
	   where(Ident -> id_op(Ident1))
	   id_to_string(Ident1 -> IdStr)
	   Cid'Ident -> CidId
	   id_to_string(CidId -> CidIdStr)
	   Concatenate3(CidIdStr, "_", IdStr -> NameStr) 
	   
	   Concatenate("Value_", NameStr -> SubtypeStr1)
	   Concatenate(SubtypeStr1, "_not_in_subtypeBla1" -> SubtypeStr)
	   -- Extending the lifted type with the proper constructor:
	   Extend_Nav_Type(PosII,  SubtypeStr -> SubtypeNavId)
	   where(sal_esp_value_occ(SubtypeNavId) -> Expr1)
	   SAL_Gen_Type_Expr(PosII, TypeExpr -> _, LiftedType)

	   SAL_Generate_Result_for_Violation(LiftedType, Expr1 -> SubtypeViolationExpr)
	   -- Translate SubtypeCond
	   Gen_SAL_Expr(RSLSubtypeCond, normal, bool -> _, SubtypeCond)
	   -- add is_true
	   where(sal_esp_unary_prefix_occ(val_id(SAL_Op), SubtypeCond) -> Is_true_Expr)
	   -- make if expression
	   where(sal_value_occ(val_id(id(ResId)),nil) -> Expr2)
	   where(sal_if_expr(Is_true_Expr, Expr2, nil, else(SubtypeViolationExpr)) -> IfExpr)
	   -- make let expression
	   where(sal_let_expr(ResId, LiftedType, Namespace1, nil, SAL_CC_Expr, IfExpr) -> CCBody)
	 ||
	   where(SAL_CC_Expr -> CCBody)
	 |)
	 -- getting the lifted vid:
	 Vid'Lifted_Vid -> LVid
	 where(sal_const_decl(sal_expl_const(IdOp,LVid,CC_SALType, CCBody)) -> CC_ContextElement)
	 Insert_Context_Element(CC_ContextElement, CC_ContextElements
	 -> CC_ContextElementsOut)
	 -- Adding the constant to the global collection (will automatically generate an ltl_assertion at the end)
	 where(CC_SALType -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)), _)))
	 Insert_Constant(LVid, Tid)


	 -- Implicit Value Definition
  'rule' SAL_Process_Value_id(Valueid, impl_val(ValExpr), _, ContextElements, CC_ContextElements -> ContextElements, CC_ContextElements):
	 Valueid'Pos -> Pos
	 Puterror(Pos)
	 Putmsg("Implicit value definitions not supported")
	 Putnl()

  -- Excluding overloaded operators (for the moment)
  'rule' SAL_Process_Value_id(Valueid, expl_fun(_, _, _, _, _, _), _,
                          ContextElements, CC_ContextElements -> ContextElements, CC_ContextElements):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> op_op(Op)
	 Puterror(Pos)
	 Putmsg("For the moment, overloaded operators are not supported in the translator to SAL\n")

	 -- Explicit Function Signature (from mutual recursion)
	 -- (also used for explicit functions)
  'rule' SAL_Process_Value_id(Valueid, expl_fun(Params, no_val,
				            PostCond, PreCond,
				            _, _), _,
                          ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut):

	 Valueid'Pos -> PosVid
	 Puterror(PosVid)
	 Putmsg("Functions without definition are not accepted\n")

	 -- The rest is for error recovery...
	 Valueid'Ident -> Ident
	 Gen_SAL_Id_Op(PosVid, Ident,none,none -> IdOp, _) -- The idOp is just a name here (uses de id part of the IdOp) 
						           -- and names are shared among the cc and non-cc versions
	 Valueid'Type -> TypeExpr
	 -- Generate the arguments:
	 Gen_SALFormal_Parameters(Params, TypeExpr -> SALParams,Namespace, SAL_CC_Params)
	 -- Generate the result type:
	 Gen_SAL_Result_Type(PosVid, TypeExpr -> RSL_Result, ResultType, CC_ResultType)
	 -- The precondition is processed and translated (it's ignored when generating code)	 
	 (|
	   where(PreCond -> pre_cond(Pos, Pre))
	   Gen_SAL_Expr(Pre,normal,bool -> _, SALPreCond)
	 ||
	   where(SAL_VALUE_EXPR'nil -> SALPreCond)
	 |)
	 SAL_Current_Cid -> Cid
	 SAL_Convert_Id_Op(Ident -> Id)
	 -- SAL value id for the function:
	 New_SAL_value_id(PosVid, Id,Cid,ResultType,regular_value -> Vid)
	 -- Storing the arguments in the Vid:
	 Vid'Params <- SALParams
	 -- getting the lifted vid:
	 Vid'Lifted_Vid -> LVid
	 LVid'Params <- SAL_CC_Params
  	 where(sal_const_decl(sal_fun_const(IdOp, LVid,nil, 
	   SALParams, ResultType, Namespace, nil, nil)) -> ContextElement)
	 Insert_Context_Element(ContextElement, ContextElements ->
						ContextElementsout)
	 -- Confidence condition version:
	 -- Nothing to be done here in the CC version, (also error recovery):
	 Insert_Context_Element(ContextElement, CC_ContextElements -> CC_ContextElementsOut)					
						
	 -- Explicit Function Definition
  'rule' SAL_Process_Value_id(Valueid, expl_fun(Params, ValExpr,
				            PostCond, PreCond,
				            OptCond, F), Is_In_Type_Function,
                          ContextElements, CC_ContextElements -> 
ContextElementsout, CC_ContextElementsOut):
--ContextElements, CC_ContextElements):


         -- Detection of recursive functions:
	 Valueid'Pos -> PosVid
	 Collect_Value_ids(ValExpr, nil -> DeclaredsValVE) --pvs_aux.g
	 (|
	   Is_Recursive_Function(Valueid, DeclaredsValVE) --pvs_aux.g
	   where(sal_recursive -> Recursive)
	   Puterror(PosVid)
	   Putmsg("Recursive function declaration\n")
	 ||
	   where(SAL_RECURSIVE'nil -> Recursive)
	 |)

	 Valueid'Type -> T
	 Make_function_type(T -> fun(D, ARR, result(R,RD,WR,IN,OUT)))--types.g
	 (|
	   (| Maximal(R) || eq(Recursive, nil) |)
	   where(SAL_RECURSIVE_SUBTYPE'nil -> RecSub)
	   where(T -> TypeExpr)
	 ||
	   Maxtype(R -> RM)
	   where(fun(D, ARR, result(RM,RD, WR,IN,OUT)) -> TypeExpr)
	   Puterror(PosVid)
	   Putmsg("Recursive subtype found in function declaration\n")
	   where(sal_recursive_subtype -> RecSub) 
	 |)

	 Valueid'Ident -> Ident
-- CWG debug
--PrintPos(PosVid)
--Putmsg("Function: ")
--Print_id_or_op(Ident)
--Putnl()

	 Gen_SAL_Id_Op(PosVid, Ident,none,none -> IdOp, _) -- The idOp is just a name here (uses de id part of the IdOp) 
						           -- and names are shared among the cc and non-cc versions
	 -- Generate the parameters:
	 (|
	    where(Params -> list(ParamsHead, nil))
	    Gen_SALFormal_Parameters(Params, TypeExpr -> SALParams,Namespace, SAL_CC_Params)
	    -- The function is not curried, generate a normal body:
	    -- Generate the result type:
	    Gen_SAL_Result_Type(PosVid, TypeExpr -> RSL_Result,FunType, LiftedResult)
	    SAL_Current_Cid -> Cid
	    SAL_Convert_Id_Op(Ident -> Id)
	    (|
	       eq(Is_In_Type_Function, reconstructor_function)
	       New_SAL_value_id(PosVid, Id,Cid,FunType,reconstructor_value -> Vid)
	    ||
	       New_SAL_value_id(PosVid, Id,Cid,FunType,regular_value -> Vid)
	    |)
	    -- Storing the arguments in the Vid:
	    Vid'Params <- SALParams
where(ValExpr -> ValExpr2)
--Set_Valoccs_As_Locals(ValExpr -> ValExpr2) -- TODO: This is a Hack to ensure input values are treated as local values
Gen_SAL_Expr(ValExpr,normal,RSL_Result -> SALExpr, SAL_CC_Expr)
--Gen_SAL_Expr(ValExpr2,normal,RSL_Result -> _, SAL_CC_Expr)
	    --Gen_SAL_Expr(ValExpr2,normal,RSL_Result -> SALExpr, SAL_CC_Expr)
	 || 
	    -- Curried function detected... Unfolding and generating LAMBDA...
	    where(Params -> list(ParamsHead, ParamsTail))
	    Gen_SALFormal_Parameters(list(ParamsHead,nil), TypeExpr -> SALParams,Namespace, SAL_CC_Params)
	    Putwarning(PosVid)
	    Putmsg("Curried function detected, generating lambda abstraction\n")
	    Gen_SAL_Result_Type(PosVid, TypeExpr -> RSL_Result,FunType, LiftedResult)
	    SAL_Gen_Lambda_Param_from_Parameters(ParamsTail, RSL_Result, ValExpr -> RSLExpr)
	    SAL_Current_Cid -> Cid
	    SAL_Convert_Id_Op(Ident -> Id)
	    (|
	       eq(Is_In_Type_Function, reconstructor_function)
	       New_SAL_value_id(PosVid, Id,Cid,FunType,reconstructor_value -> Vid)
	    ||
	       New_SAL_value_id(PosVid, Id,Cid,FunType,regular_value -> Vid)
	    |)
	    -- Storing the arguments in the Vid:
	    Vid'Params <- SALParams
	    Gen_SAL_Expr(RSLExpr,normal,RSL_Result -> SALExpr, SAL_CC_Expr)
	 |)
	 where(sal_const_decl(sal_fun_const(IdOp, Vid,Recursive,
	    SALParams, FunType,  Namespace, SALExpr, nil)) -> ContextElement)

	 (|
	    eq(Is_In_Type_Function, is_in_function)
	    -- Do not add this function in the non-cc version
	    where(ContextElements -> ContextElementsout)
	    Vid'Lifted_Vid -> LVid
	    LVid'Params <- SAL_CC_Params

	    -- Do not add:
	    -- (a) Argument nav check: this kind of function is always invoked after nav checking, so no need to check that
	    -- (b) Postcondition check: this functions do not have post conditions
	    -- (c) Result-in-subtype check: this functions are MADE by the translation and are meant to produce the proper result. No need to check that
	    -- Furthermore: EFFICIENCY here is a MUST (given that these family of functions are invoked everywhere)
	    where(sal_const_decl(sal_fun_const(IdOp, LVid,Recursive,
	      SAL_CC_Params, LiftedResult,  Namespace, SAL_CC_Expr, nil)) -> CC_ContextElement) 
	    -- Adding the cc element to the colection...
	    Insert_Context_Element(CC_ContextElement, CC_ContextElements -> CC_ContextElementsOut)
/*         ||
            where(ValExpr -> array_val_occ(_,_,_,_))
            Insert_Context_Element(ContextElement, ContextElements -> ContextElementsout)
	    Vid'Lifted_Vid -> LVid

	    -- Do not add:
	    -- (a) Argument nav check: this kind of function is always invoked after nav checking, so no need to check that
	    -- (b) Postcondition check: this functions do not have post conditions
	    -- (c) Result-in-subtype check: this functions are MADE by the translation and are meant to produce the proper result. No need to check that
	    -- Furthermore: EFFICIENCY here is a MUST (given that these family of functions are invoked everywhere)
	    where(sal_const_decl(sal_fun_const(IdOp, LVid,Recursive,
	      SAL_CC_Params, LiftedResult,  Namespace, SAL_CC_Expr, nil)) -> CC_ContextElement) 
	    Insert_Context_Element(CC_ContextElement, CC_ContextElements -> CC_ContextElementsOut)*/
         ||
	    (|
	       eq(Is_In_Type_Function, cc_mk_function)
	       -- This is a lifted mk function meant to check before creating variants, records or 
	       -- reconstructing them...
	       -- This function shouldn't be added to the non-cc version either:
	       where(ContextElements -> ContextElementsout)
	       -- If this is a mk_function (record constructor) then we are translating the lifted
	       -- constructor...
	       -- This means, that the arguments to the constructor are lifted and also that
	       -- the actual body is expecting un-lifted arguments...
	       -- The function currently has the form:
	       --    mk_<id> : Lifted(T1) >< ... >< Lifted(Tn) -> Lifted(Tx)
	       --    mk_<id>(a1,...,an) is
	       --      mk_<id>(a1,...,an)
	       -- We must translate the function application in the body as
	       --      Tx_cc(SAL_TYPES!mk_<id>(T1_val(a1),...,Tn_val(an)));
	       -- The checks for nav arguments and subtypes are added below.
	       ---------------------------------------------------------------------------------
	       where(LiftedResult -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)), _)))
	       Tid'Constructor -> vid(ConstVid)
	       -- CWG 13/4/08
	       -- we need to replace the lifted constructor in the body
	       -- with the unlifted one
Set_Valoccs_As_Locals(ValExpr -> ValExpr2)
--where(ValExpr -> ValExpr2)
Gen_SAL_Expr(ValExpr2,normal,RSL_Result -> _, SAL_CC_Expr2)
	       where(SAL_CC_Expr2 -> sal_funct_applic(X, sal_argument(Exprs)))
	       where(SALExpr -> sal_funct_applic(Mk, _))
	       SAL_Lower_Exprs(Exprs, SAL_CC_Params -> Exprs1)
	       where(sal_argument(list(sal_funct_applic(Mk, sal_argument(Exprs1)), nil)) -> Arg)
	       where(sal_funct_applic(sal_esp_value_occ(ConstVid), Arg) -> SAL_CC_Expr1)

	    ||
	       eq(Is_In_Type_Function, destructor_function)
	       where(ContextElements -> ContextElementsout)
	       -- This is the case of a destructor like pool or berths in
	       -- Harbour :: 
	       --	 pool : T.Ship-set <-> update_pool 
	       --        berths : T.Index -m-> T.Ship <-> update_berths
	       -- In this case, the cc version will translate this as:
	       --   Harbour: TYPE = DATATYPE  
	       --              mk_Harbour(pool: Int_set, berths: Int_Int__cc_map)
	       --            END;
	       -- And then generate wrapping functions over pool and berth that will act as the
	       -- destructors invoked all over the code (the lifted versions of pool_ and berth_)
	       -- The problem here is that pool and berth can not be invoked with the same arguments than
	       -- the lifted pool and berth. To see why, consider the code for pool that follows:
	       --  pool(x_ : Harbour_cc): Int__cc_set_cc = 
	       --    IF Harbour_nav?(x_)
	       --    THEN Int__cc_set_nav(Harbour_nav_val(x_))
	       --    ELSE pool(x_)
	       --    ENDIF;
	       -- The problem here arises on the invocation of the inner pool_. In this case, the argument (x_) is
	       -- of type Harbour_cc but the function pool is defined
	       -- over the type Harbour (the unlifted type), 
               -- and returns an unlifted value.
	       -- The translation is therefore:
	       -- pool(x_ : Harbour_cc): Int__cc_set_cc = 
	       --    IF Harbour_nav?(x_)
	       --    THEN Int__cc_set_nav(Harbour_nav_val(x_))
	       --    ELSE Int__cc_set_cc(pool(SAL_TYPES_cc!Harbour_cc_val(x_)))
	       --    ENDIF;
	       ------------------------------------------------------------------------------
	       where(LiftedResult -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)), _)))
	       Tid'Constructor -> vid(ConstVid)
	       -- CWG 13/4/08
	       -- we need to replace the lifted constructor in the body
	       -- with the unlifted one
	       where(SAL_CC_Expr -> sal_funct_applic(_, sal_argument(Exprs)))
	       where(SALExpr -> sal_funct_applic(Dest, _))
	       SAL_Lower_Exprs(Exprs, SAL_CC_Params -> Exprs1)
	       where(sal_argument(list(sal_funct_applic(Dest, sal_argument(Exprs1)), nil)) -> Arg)
	       where(sal_funct_applic(sal_esp_value_occ(ConstVid), Arg) -> SAL_CC_Expr1)
	       -- Turning the arguments of the function into lets:
	       -- SAL_Turn_Params_into_Lets(SAL_CC_Params, SAL_CC_Expr -> SAL_CC_Expr1)
	    ||
	       -- THIS IS A NORMAL (user defined) function, adding the function in the non-cc version
	       Insert_Context_Element(ContextElement, ContextElements -> ContextElementsout)
	       where(SAL_CC_Expr -> SAL_CC_Expr1)
	    |)


	    -- Adding the checkings in the cc-version:
	    -- Confidence condition version:
	    -- Extend the lifted result type
	    Select_CC_Result_Type(LiftedResult -> SelectedTid)
	    where(Ident -> id_op(Ident1))
	    id_to_string(Ident1 -> IdStr)
-- stuff added by CWG
	    string_to_id("RSL_res_" -> ResId) -- TODO: Der skal ændres noget her.
	    IncreaseCol(PosVid -> ResPos)
	    New_value_id(ResPos, id_op(ResId) -> ResI)
	    ResI'Type <- R
	    where(BINDING'single(ResPos, id_op(ResId)) -> Bind)
	    Type_is_fun(TypeExpr -> _,_, RSLResultType)
	    SAL_Gen_Type_List(list(Bind, nil), RSLResultType -> T11) -- jiperna: the type expression was 'TypeExpr '
	    SAL_Prepare_Bindings(list(Bind,nil), T11 -> PreparedBS)
	    Gen_SALFormal_Parameter(PreparedBS, T11 -> _, Namespace1, CC_Args)
	    Default_Bool_Tid -> BTid
	    BTid'Lifted_Tid -> tid(LBTid)
	    where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	    
	    Cid'Ident -> CidId
	    id_to_string(CidId -> CidIdStr)
	    Concatenate3(CidIdStr, "_", IdStr -> NameStr) 
	    (|
	        -- Processing postcondition...
		where(PostCond -> post(post_cond(Pos1, RNaming, RSLPostCondition)))
		-- make RSL postcondition check 
		(|
		    where(RNaming -> result(Pos2, Binding))
		    -- make let Binding = RSL_res_ in RSLPostCondition end
		    where(explicit(Pos2, binding(Pos2, Binding), val_occ(Pos2, ResI, nil)) -> LDS)
		    where(VALUE_EXPR'let_expr(Pos2, list(LDS, nil), RSLPostCondition) -> RSLPostCond)
	        ||
	            -- no result naming
		    where(RSLPostCondition -> RSLPostCond)
	        |)
-- CWG debug
--Putmsg("Post: ")
--Print_expr(RSLPostCond)
--Putnl()
	        -- Generating the string that describes the post violation...
		Gen_SAL_Expr(RSLPostCond, normal, bool -> _, PostCondition)
		Concatenate("Postcondition_of_function_", NameStr -> PostcondStr1)
		Concatenate(PostcondStr1, "_not_satisfied" -> PostcondStr)
		-- Extending the lifted type with the proper constructor: 
		Extend_Nav_Type(Pos1,  PostcondStr -> PostNavId)
		-- Construct the result for the function when the postcond is violated
		-- (this function will generate an expression suitable as result for the
		-- function evaluation when this condition is violated (i.e. the proper navs)).
		where(sal_esp_value_occ(PostNavId) -> Expr1)
		SAL_Generate_Result_for_Violation(LiftedResult, Expr1 -> PostViolationExpr)
		-- adding the 'is_true' in front of the condition:
		where(sal_esp_unary_prefix_occ(val_id(SAL_Op), PostCondition) -> Is_true_Expr1)
		-- generating the if expression:
		where(sal_if_expr(Is_true_Expr1, sal_value_occ(val_id(id(ResId)),nil), nil, else(PostViolationExpr)) -> Expr2)
--where(PostCondition -> Expr2)
	    ||
	        -- no postcondition
		where(sal_value_occ(val_id(id(ResId)),nil) -> Expr2)
	    |)  
   
	    (|
	        -- Processing result subtype
		where(F -> condition(RSLResSubtype))
-- CWG debug
--Putmsg("Result subtype: ")
--Print_expr(RSLResSubtype)
--Putnl()
		-- Generating the string that describes the type violation...
		Gen_SAL_Expr(RSLResSubtype, normal, bool -> _, ResSubtype)
		Concatenate("Result_of_function_", NameStr -> ResSubtypeStr1)
		Concatenate(ResSubtypeStr1, "_not_in_subtype" -> ResSubtypeStr)
		-- Extending the lifted type with the proper constructor:
		IncreaseCol(PosVid -> PosII) -- A different position for this value is needed because
					     -- the Vid of the whole function already uses the PosVid position
					     -- If they share the position information, the look-up by position
					     -- on the function application will fail (will find this error value instead of
					     -- of the function's one)
	        Extend_Nav_Type(PosII,  ResSubtypeStr -> ResSubNavId)
		where(sal_esp_value_occ(ResSubNavId) -> Expr3)
		SAL_Generate_Result_for_Violation(LiftedResult, Expr3 -> ResSubViolationExpr)
		where(sal_esp_unary_prefix_occ(val_id(SAL_Op), ResSubtype) -> Is_true_Expr2)
		where(sal_if_expr(Is_true_Expr2, Expr2, nil, else(ResSubViolationExpr)) -> IfExpr)
		where(sal_let_expr(ResId, LiftedResult, Namespace1, nil, SAL_CC_Expr1, IfExpr) -> ExtendedCCBody)
	    ||
	        (|
	             where(Expr2 -> sal_if_expr(_, _, _, _))
		     where(sal_let_expr(ResId, LiftedResult, Namespace1, nil, SAL_CC_Expr1, Expr2) -> ExtendedCCBody) 
	        ||
	             where(SAL_CC_Expr1 -> ExtendedCCBody)
	        |)  
	    |)	
	    (|
	        -- Processing precondition:
		where(PreCond -> pre_cond(Pos, Pre))
		Gen_SAL_Expr(Pre,normal, bool -> _, SAL_CC_Precond)    
		-- Generating the string that describes the cc violation...
		Concatenate("Precondition_of_function_", NameStr -> PrecondStr1)
		Concatenate(PrecondStr1, "_not_satisfied" -> PrecondStr)
		-- Extending the lifted type with the proper constructor:
		Extend_Nav_Type(Pos, PrecondStr -> NavId)
		-- Construct the result for the function when the precond is violated
		-- (this function will generate an expression suitable as result for the
		-- function evaluation when this condition is violated (i.e. the proper navs)).
		where(sal_esp_value_occ(NavId) -> Expr4)
		SAL_Generate_Result_for_Violation(LiftedResult, Expr4 -> PreViolationExpr)
		-- adding the 'is_true' in front of the condition:
		where(sal_esp_unary_prefix_occ(val_id(SAL_Op), SAL_CC_Precond) -> Is_true_Expr3)
		-- Extending the body of the function...
		-- Using the template IF <precond> THEN <old_body> ELSE ResultViolationExpr ENDIF
		where(sal_if_expr(Is_true_Expr3, ExtendedCCBody, nil, else(PreViolationExpr)) -> ExtendedCCBody2)
-- CWG debug
--Putmsg("Pre: ")
--Print_expr(Pre)
--Putnl()
	    ||
	        where(ExtendedCCBody -> ExtendedCCBody2)
	    |)
            (|
	        -- processing argument subtypes
		where(OptCond -> condition(Sub2))
Set_Valoccs_As_Locals(Sub2 -> Sub) -- TODO: Hack to ensure they are treated as local variables
--where(Sub2 -> Sub)
--where(VALUE_EXPR'nil -> Sub)
		(|
/*                  where(Sub -> array_val_occ(_,_,_,_))
                  where(ExtendedCCBody2 -> ExtendedCCBody3)
                ||*/
                  where(Sub -> val_occ(_,VId,_))
                  VId'Type -> Type
                  Remove_Brackets(Type -> Type1)
                  where(Type1 -> array(_,_))
                  where(ExtendedCCBody2 -> ExtendedCCBody3)
                ||
		  Gen_SAL_Expr(Sub,normal, bool -> _, SAL_CC_Sub)
		  -- Generating the string that describes the cc violation...
		  Concatenate("Argument_of_function_", NameStr -> SubStr1)
		  Concatenate(SubStr1, "_not_in_subtype" -> SubStr)
		  -- Extending the lifted type with the proper constructor: 
		  IncreaseCol(PosVid -> PosII) -- A different position for this value is needed because
					     -- the Vid of the whole function already uses the PosVid position
					     -- If they share the position information, the look-up by position
					     -- on the function application will fail (will find this error value instead of
					     -- of the function's one)
		  Extend_Nav_Type(PosII, SubStr -> SubNavId)
		  -- Construct the result for the function when the precond is violated
		  -- (this function will generate an expression suitable as result for the
		  -- function evaluation when this condition is violated (i.e. the proper navs)).
		  where(sal_esp_value_occ(SubNavId) -> Expr5)
		  SAL_Generate_Result_for_Violation(LiftedResult, Expr5 -> SubViolationExpr)
		  -- adding the 'is_true' in front of the condition:
		  where(sal_esp_unary_prefix_occ(val_id(SAL_Op), SAL_CC_Sub) -> Is_true_Expr4)
		  -- Extending the body of the function...
		  -- Using the template IF <precond> THEN <old_body> ELSE ResultViolationExpr ENDIF
		  where(sal_if_expr(Is_true_Expr4, ExtendedCCBody2, nil, else(SubViolationExpr)) -> ExtendedCCBody3)
--where(sal_if_expr(sal_literal(bool_true), ExtendedCCBody2, nil, else(SubViolationExpr)) -> ExtendedCCBody3)
-- CWG debug
--Putmsg("Argument subtype: ")
--Print_expr(Sub)
--Putnl()
              |)
	    ||
	        where(ExtendedCCBody2 -> ExtendedCCBody3)
	    |)
-- TODO: Do something here
	    -- insert code for checking nav parameters
	    Add_nav_params_check(SAL_CC_Params, ExtendedCCBody3, LiftedResult -> Function_CC_Body)
--where(ExtendedCCBody -> Function_CC_Body)

      	    -- getting the lifted vid:
	    Vid'Lifted_Vid -> LVid
            --where(Vid -> LVid)
	    --Vid'Params <- SAL_CC_Params
	    where(sal_const_decl(sal_fun_const(IdOp, LVid,Recursive,
	      SAL_CC_Params, LiftedResult,  Namespace, Function_CC_Body, nil)) -> CC_ContextElement) 
	    -- Adding the cc element to the colection...
	    Insert_Context_Element(CC_ContextElement, CC_ContextElements -> CC_ContextElementsOut)
         |)

	 -- Implicit Function Definition
  'rule' SAL_Process_Value_id(Valueid, impl_fun(Params, Post,
				            PreCond,
					    OptCond),_,
			    ContextElements, CC_ContextElements -> ContextElements, CC_ContextElements):
	 Valueid'Pos -> Pos
	 Puterror(Pos)
	 Putmsg("Implicit function definitions not supported")
	 Putnl()


--------------------------------------------------------------------
-- SAL_Turn_Params_into_Lets
--------------------------------------------------------------------
-- This function will generate let expressions from formal parameters.
--------------------------------------------------------------------
'action' SAL_Turn_Params_into_Lets(SAL_FORMAL_FUN_PARAMETERS, SAL_VALUE_EXPR -> SAL_VALUE_EXPR)

  'rule' SAL_Turn_Params_into_Lets(list(formal_param(Id, CC_Type, _), Rest), Body -> Expr)
	 SAL_Turn_Params_into_Lets(Rest, Body -> ExtendedBody)
	 DefaultPos(-> P)
	 where(CC_Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 Tid'Constructor -> vid(Const)
	 Tid'Lifted_fields -> Fields
	 SAL_Find_Accesor_in_Fields(Fields, Const -> AccVid)
	 AccVid'Type -> Type
	 where(sal_funct_applic(sal_esp_value_occ(AccVid), sal_argument(list(sal_value_occ(val_id(id(Id)),nil), nil))) -> InitExpr)
	 where(sal_let_expr(Id, Type, nil, nil, InitExpr, Body) -> Expr)


  'rule' SAL_Turn_Params_into_Lets(nil, Body -> Body)

--------------------------------------------------------------------
-- SAL_Lift_Bindings
--------------------------------------------------------------------
-- Introduce LET expressions to lift the bindings

'action' SAL_Lift_Bindings(SAL_BINDINGS, PRODUCT_TYPE, SAL_VALUE_EXPR -> SAL_VALUE_EXPR)

  -- 3rd parameter is a restriction, which may be nil: nothing to do
  'rule' SAL_Lift_Bindings(_, _, nil -> nil):

  'rule' SAL_Lift_Bindings(list(B, BS), list(T, TS), E -> E2):
	 SAL_Lift_Binding(B, T, E -> E1)
	 SAL_Lift_Bindings(BS, TS, E1 -> E2)

  'rule' SAL_Lift_Bindings(nil, _, E -> E):

'action' SAL_Lift_Binding(SAL_BINDING, TYPE_EXPR, SAL_VALUE_EXPR -> SAL_VALUE_EXPR)

  'rule' SAL_Lift_Binding(sal_prod_binding(_, BS), T, E -> E1):
	 (|
	   Type_is_product(T -> TS)
	 ||
           where(PRODUCT_TYPE'list(T, nil) -> TS)
	 |)
	 SAL_Lift_Bindings(BS, TS, E -> E1)

  'rule' SAL_Lift_Binding(sal_typed_prod(_, BS, ST), T, E -> E):
	 SAL_Gen_Prod_Ident("" -> IdProd)
	 -- TODO

  'rule' SAL_Lift_Binding(sal_typed_id(P, id(Id), ST), T, E -> E1):
	 SAL_Check_Defined_Maximal_Type(T -> tid(LTId))
	 LTId'Ident -> TId
	 where(type_refs(sal_defined(P, TId, LTId)) -> LST)
	 LTId'Constructor -> vid(Const)
	 where(sal_esp_value_occ(Const) -> LiftExpr)
	 where(sal_named_val(id_op(id(Id))) -> N)
	 where(sal_argument(list(N, nil)) -> Args)
	 where(sal_funct_applic(LiftExpr, Args) -> LiftedExpr)
	 where(sal_let_expr(Id, LST, nil, nil, LiftedExpr, E) -> E1)
	 

--------------------------------------------------------------------
-- Add_nav_params_check
--------------------------------------------------------------------
-- if result type of function is R
-- essentially for each parameter P of type T insert
-- IF T_nav?(P) THEN R_nav(T_nav_val(P)) ELSE
--------------------------------------------------------------------
'action' Add_nav_params_check(SAL_FORMAL_FUN_PARAMETERS, SAL_VALUE_EXPR, SAL_TYPE_EXPR -> SAL_VALUE_EXPR)

  'rule' Add_nav_params_check(list(Parm, Parms), V, R -> V2):
-- later parameters take inner positions, so first is checked first
	 Add_nav_params_check(Parms, V, R -> V1)
	 Add_nav_param_check(Parm, V1, R -> V2)

  'rule' Add_nav_params_check(nil, V, R -> V):

'action' Add_nav_param_check(SAL_FORMAL_FUN_PARAMETER, SAL_VALUE_EXPR, SAL_TYPE_EXPR -> SAL_VALUE_EXPR)

  'rule' Add_nav_param_check(formal_param(_, T, _), V, _ -> V):
	 where(T -> rsl_built_in(unit))

  'rule' Add_nav_param_check(formal_param(Id, T, _), V, R -> V1):
	 Get_lifted_constructor(T -> NavConst)
	 where(NavConst -> sal_construc(_, NavConstVid, NavAccessor, _))
	 where(NavAccessor -> list(sal_destructor(_, NavAccVid, _, _), _))
	 DefaultPos(-> P)
	 where(sal_argument(list(sal_value_occ(val_id(id(Id)), nil), nil)) -> Arg)
	 where(sal_recogniser(NavConstVid, Arg) -> Cond)
	 where(sal_funct_applic(sal_esp_value_occ(NavAccVid), Arg) -> Expr)
	 where(sal_argument(list(Expr, nil)) -> Arg1)
	 Get_lifted_constructor(R -> RNavConst)
	 where(RNavConst -> sal_construc(_, RNavConstVid, _, _))
	 where(sal_funct_applic(sal_esp_value_occ(RNavConstVid), Arg1) -> Nav) 
	 where(sal_if_expr(Cond, Nav, nil, else(V)) -> V1)

'action' Get_lifted_constructor(SAL_TYPE_EXPR -> SAL_CONSTRUCTOR)
-- we assume the argument is a lifted type

  'rule' Get_lifted_constructor(rsl_built_in(sal_list_type(Tid,_)) -> Constructor):
	 Get_lifted_constructor_from_Tid(Tid -> Constructor)

  'rule' Get_lifted_constructor(rsl_built_in(sal_finite_set(Tid,_)) -> Constructor):
	 Get_lifted_constructor_from_Tid(Tid -> Constructor)

  'rule' Get_lifted_constructor(rsl_built_in(sal_finite_map(Tid,_,_)) -> Constructor):
	 Get_lifted_constructor_from_Tid(Tid -> Constructor)

  'rule' Get_lifted_constructor(rsl_built_in(boolean(Tid)) -> Constructor):
	 Get_lifted_constructor_from_Tid(Tid -> Constructor)

  'rule' Get_lifted_constructor(rsl_built_in(integer(Tid)) -> Constructor):
	 Get_lifted_constructor_from_Tid(Tid -> Constructor)

  'rule' Get_lifted_constructor(rsl_built_in(natural(Tid)) -> Constructor):
	 Get_lifted_constructor_from_Tid(Tid -> Constructor)

  'rule' Get_lifted_constructor(rsl_built_in(sal_array(Tid,_,_)) -> Constructor):
         Get_lifted_constructor_from_Tid(Tid -> Constructor)

  'rule' Get_lifted_constructor(user_defined(sal_abbrev(TExpr)) -> Constructor):
	 Get_lifted_constructor(TExpr -> Constructor)

  'rule' Get_lifted_constructor(user_defined(sal_subtype(_,T,_,_)) -> Constructor):
	 Get_lifted_constructor(T -> Constructor)

  'rule' Get_lifted_constructor(user_defined(sal_bracket_type(T)) -> Constructor):
	 Get_lifted_constructor(T -> Constructor)

  'rule' Get_lifted_constructor(type_refs(sal_defined(_,_,Tid)) -> Constructor):
	 Get_lifted_constructor_from_Tid(Tid -> Constructor)

  'rule' Get_lifted_constructor(user_defined(sal_cc_type(T,_)) -> Constructor):
	 Get_lifted_constructor(T -> Constructor)

  --'rule' Get_lifted_constructor(user_defined(sal_fun_type(_,T)) -> Constructor):
    --     Get_lifted_constructor(T -> Constructor)

--debug
  'rule' Get_lifted_constructor(X -> Constructor)
Putmsg("Internal error: Cannot generate lifted constructor\n")
	 Default_Bool_Tid -> BTid
	 Get_lifted_constructor_from_Tid(BTid -> Constructor)

'action' Get_lifted_constructor_from_Tid(SAL_type_id -> SAL_CONSTRUCTOR)

  'rule' Get_lifted_constructor_from_Tid(TI -> Constructor):
	 TI'Lifted_Tid -> tid(LTI)
	 LTI'Lifted_fields -> TLF
	 where(TLF -> list(_, list(sal_part(Constructor,_),_)))

------------------------------------------------------------------------------------
-- SAL_Process_Object_Decl
------------------------------------------------------------------------------------
-- This function processes object declarations... (instantiations)
-- It essentially completes the translation of schemes (only instantiated schemes are
-- translated).
-------------------------------------------------------------------------------------

'action' SAL_Process_Object_Decl(SORTED_DECL_ITEM,
				SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Process_Object_Decl(object_item(Pos,Ident,Params,ClassExpr), 
				ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut):

           -- This function will, temporarly change the Current_Cid (while processing and translating the instantiation)
	   -- Save it in order to restore it at the end (using an stack-like construction to handle nesting):
	   SAL_Current_Cid -> OldCid
	   -- Push into the stack:
	   Current_cid_stack -> OldStack
	   Current_cid_stack <- list(OldCid, OldStack)

	   -- Generating the Cid for the context:
	   New_SAL_context_id(Ident, 0 -> Cid)
	   -- Making the current context globaly available
	     -- (used by the sal-constants generators)
	   SAL_Current_Cid <- Cid
	   
	   Cid'Lifted_Cid -> cid(CC_Cid)
	   -- Making the current context globaly available
	     -- (used by the sal-constants generators)
	   SAL_Current_CC_Cid <- CC_Cid
	   -- Process the context (generating the SAL_CONTEXT_ELEMENTS):

	   Get_current_modules(-> ME)
	   Lookup_object_in_module(Ident, ME -> object_id(I))
	   Current -> C
	   I'Param_env -> PCE
	   I'Env -> CE
	   Current <- current_env(CE,current_env(PCE, C))
	   Extend_paths -> Paths
	   Extend_paths <- list(nil,list(nil,Paths))

	   SAL_Trans_Class(ClassExpr -> Context_Decls, CC_Decls)

	   Current -> current_env(CE1,current_env(PCE1,C1))
	   Current <- C1
	   Extend_paths <- Paths

	   -- Restoring the current Cid:
	   Current_cid_stack -> list(StoredCid, NewStack)
	   Current_cid_stack <- NewStack
	   SAL_Current_Cid <- StoredCid

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

	   -- Generating the CC-context:
	   CC_Cid'Ident -> CC_Id
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
	   SAL_Current_Cid -> SchCid
	   New_SAL_object_id(Pos,Ident,SchCid,cid(Cid) -> Oid)
	   Oid'State <- Data
	   Oid'NonState <- Static
	   Oid'CCState <- CCData
	   Oid'CCNonState <- CCStatic
	   -- Adding the object to the AST (to both, the cc and non-cc versions)
	   -- Note that in both cases, no further action is taken with the
	   -- object instantiations... (future extension when working on other spec styles?)
	   where(sal_object_decl(Ident, Pos, Oid, Data, Static) -> ContextElement)
	   Insert_Context_Element(ContextElement, ContextElements -> ContextElementsout)  
	   -- cc version:
	   Insert_Context_Element(ContextElement, CC_ContextElements -> CC_ContextElementsOut)  

-- This funtion separates the declarations from one context into state and non-state components...
-- This information will be usefull when translating imperative styled specifications (due to the fact
-- that objects DO NOT EXIST in SAL, the static (data part) of an instantiated scheme will be collected 
-- separatelly in a global state. On the other hand, the non-state components can be shared among
-- all instances if needed)

'action' SAL_Separate_Decls(SAL_CONTEXT_CONSTANTS ->
			          SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Separate_Decls(list(Constant, Tail) -> Data, Beh):
	 SAL_Separate_Decls(Tail -> Data1, Beh1)
	 (|
	    (|
	       where(Constant -> sal_type_decl(_,_,_))
	    ||
	       where(Constant -> sal_const_decl(_))
	    ||
	       where(Constant -> module_decl(_,_,_,_,_,_))
	    ||
	       where(Constant -> assertion_decl(_,_,_,_))
	    |)
	    where(Data1 -> Data)
	    where(SAL_CONTEXT_CONSTANTS'list(Constant, Beh1) -> Beh)
	 ||
---	    (|
		where(Constant ->sal_object_decl(_,_,_,_,_))
--	    ||
-- variables here!	    
---	    |)
	    where(SAL_CONTEXT_CONSTANTS'list(Constant, Data1) -> Data)
	    where(Beh1 -> Beh)
	 |)

  'rule' SAL_Separate_Decls(nil -> nil,nil)


-----------------------------------------------------------------------------------------
-- SAL_Process_Transition_System
-----------------------------------------------------------------------------------------
-- This functions deals with the translation of transition systems....
-----------------------------------------------------------------------------------------

'action' SAL_Process_Transition_System(Transition_system_id, SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS 
							   -> SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Process_Transition_System(TSid, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut):
	 TSid'Trans_sys -> Def
	 where(Def -> desc(Input, Local, InputPrime, LocalPrime, Transition, ExtraProps))
	 TSid'Ident -> Ident
	 TSid'Pos -> Pos
	 New_SAL_TranSys_id(Pos,Ident -> SAL_TSid)
	 -- For the cc version, the initialization expressions must be modified (to use the proper variant field)
	 SAL_Process_TS_var_decls(input, Input -> SAL_Input_Var_Decls, SAL_CC_Input_Var_Decls, SAL_Input_Vars_Init, CC_SAL_Input_Vars_Init)
	 SAL_Process_TS_var_decls(local, Local -> SAL_Local_Var_Decls, SAL_CC_Local_Var_Decls, SAL_Local_Vars_Init, CC_SAL_Local_Vars_Init)
	 SAL_Concatenate_Initializations(SAL_Input_Vars_Init, SAL_Local_Vars_Init -> SAL_Init)
	 -- Add the primed versions in SAL:
	 SAL_Process_TS_primed_vars(InputPrime)
	 SAL_Process_TS_primed_vars(LocalPrime)
	 -- Update the information in the TS-id:
	 SAL_TSid'Input_decls <- SAL_Input_Var_Decls
	 SAL_TSid'Local_decls <- SAL_Local_Var_Decls
	 SAL_TSid'Initialization <- SAL_Init
	 -- Translate the transition part:
	 -- Only the local variables (the transition system's state variables) must be checked for non-nav values in the guards
	 SAL_Process_Transitions(SAL_CC_Local_Var_Decls, SAL_CC_Input_Var_Decls, Transition -> SAL_Transitions, SAL_CC_Transitions1)
	 -- Add nav transitions in the cc version:
	 SAL_Gen_Nav_Transitions(SAL_CC_Local_Var_Decls, SAL_CC_Local_Var_Decls -> NavTransitions)
	 SAL_Concatenate_Transitions(SAL_CC_Transitions1, NavTransitions -> SAL_CC_Transitions)
	 -- Generate the new SAL element:
	 where(module_decl(Ident, SAL_TSid, SAL_Input_Var_Decls, SAL_Local_Var_Decls, SAL_Init, SAL_Transitions) -> ContextElement)
	 -- Generate the result:
	 Insert_Context_Element(ContextElement, ContextElements -> ContextElementsout1)

         (|
           where(ExtraProps -> nil)
           where(ContextElementsout1 -> ContextElementsout)
         ||
           where(ExtraProps -> assertion(PropExpr))
           Gen_SAL_Expr(PropExpr, normal, bool -> SALPropExpr, _)
           string_to_id("Possible_Vars_Prop" -> ExtraPropId)
	   where(sal_funct_applic(sal_value_occ(val_id(sal_op_symb(sal_prefix_op(g))),nil),sal_argument(list(SALPropExpr,nil))) -> ExtraProperty)
	   where(assertion_decl(Pos, ExtraPropId, SAL_TSid, ExtraProperty) -> ExtraPropertyDecl)
	   Insert_Context_Element(ExtraPropertyDecl, ContextElementsout1 -> ContextElementsout)

         |)

	 -- CC version:
	 -- CC Transition_system_Id update:
	 SAL_Concatenate_Initializations(CC_SAL_Input_Vars_Init, CC_SAL_Local_Vars_Init -> SAL_CC_Init)
	 SAL_TSid'CC_Init <- SAL_CC_Init
	 (|
	     Global_Constant_Table -> Table
	     ne(Table, nil)
	     -- Adding an empty transition system and ltl properties to check the constants:
	     SAL_Generate_Empty_TS(-> TSDecl, TSId)
	     SAL_Generate_Constant_Assertions(TSId -> AssertionDecls)
--print(AssertionDecls)
	     where(SAL_CONTEXT_CONSTANTS'list(TSDecl, AssertionDecls) -> NewCCDecls)
	     Insert_Context_Elements(NewCCDecls, CC_ContextElements -> CC_ContextElements0)
	     -- A verification for the constants have already being made... cleaning the collection...
	     Global_Constant_Table <- nil
	 ||
	     where(CC_ContextElements -> CC_ContextElements0)
	 |)
	 -- Generating the transition system:
	 where(module_decl(Ident, SAL_TSid, SAL_CC_Input_Var_Decls, SAL_CC_Local_Var_Decls,
			   SAL_CC_Init, SAL_CC_Transitions) -> CC_ContextElement)
	 Insert_Context_Element(CC_ContextElement, CC_ContextElements0 -> CC_ContextElementsOut1)
	 -- Adding the cc properties from this transition system:
	 id_to_string(Ident -> TsIdStr)
	 SAL_Current_Cid -> Cid
	 Cid'Ident -> CidId
	 id_to_string(CidId -> CidIdStr)
	 Concatenate3(CidIdStr, "_", TsIdStr -> NameStr) 
	 Concatenate(NameStr, "_cc_check" -> AssertionIdStr)
	 string_to_id(AssertionIdStr -> AssertionId)
	 SAL_Generate_CC_Check_for_Vars(SAL_CC_Local_Var_Decls -> Condition)
	 where(sal_funct_applic(sal_value_occ(val_id(sal_op_symb(sal_prefix_op(g))),nil),sal_argument(list(Condition,nil))) -> Property)
	 where(assertion_decl(Pos, AssertionId, SAL_TSid, Property) -> AssertionDecl)
	 Insert_Context_Element(AssertionDecl, CC_ContextElementsOut1 -> CC_ContextElementsOut2)

         Concatenate(NameStr, "_cc_check_guards" -> AssertionIdStrGuards)
	 string_to_id(AssertionIdStrGuards -> AssertionIdGuard)
	 SAL_Generate_CC_Check_for_Guards(SAL_CC_Transitions -> ConditionGuard)
         where(sal_funct_applic(sal_value_occ(val_id(sal_op_symb(sal_prefix_op(g))),nil),sal_argument(list(ConditionGuard,nil))) -> PropertyGuard)
	 where(assertion_decl(Pos, AssertionIdGuard, SAL_TSid, PropertyGuard) -> AssertionDeclGuard)
	 Insert_Context_Element(AssertionDeclGuard, CC_ContextElementsOut2 -> CC_ContextElementsOut)


  'rule' SAL_Process_Transition_System(TSid, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsOut):
	 TSid'Trans_sys -> Def
	 where(Def -> no_input(Local, LocalPrime, Transition, ExtraProps))
	 TSid'Ident -> Ident
	 TSid'Pos -> Pos
	 New_SAL_TranSys_id(Pos,Ident -> SAL_TSid)
	 SAL_Process_TS_var_decls(local, Local -> SAL_Local_Var_Decls, SAL_CC_Local_Var_Decls, SAL_Init, SAL_CC_Init)
	 -- Add the primed versions in SAL:
	 SAL_Process_TS_primed_vars(LocalPrime)
	 -- Update the information in the TS-id:
	 SAL_TSid'Input_decls <- nil
	 SAL_TSid'Local_decls <- SAL_Local_Var_Decls
	 SAL_TSid'Initialization <- SAL_Init
	 -- Translate the transition part:
	 SAL_Process_Transitions(SAL_CC_Local_Var_Decls, nil, Transition -> SAL_Transitions, SAL_CC_Transitions)
	 -- Generate the new SAL element:
	 where(module_decl(Ident, SAL_TSid, nil , SAL_Local_Var_Decls, SAL_Init, SAL_Transitions) -> ContextElement)
	 -- Generate the result:
	 Insert_Context_Element(ContextElement, ContextElements -> ContextElementsout1)

         (|
           where(ExtraProps -> nil)
           where(ContextElementsout1 -> ContextElementsout)
         ||
           where(ExtraProps -> assertion(PropExpr))
           Gen_SAL_Expr(PropExpr, normal, bool -> SALPropExpr, _)
           string_to_id("Possible_Vars_Prop" -> ExtraPropId)
	   where(sal_funct_applic(sal_value_occ(val_id(sal_op_symb(sal_prefix_op(g))),nil),sal_argument(list(SALPropExpr,nil))) -> ExtraProperty)
	   where(assertion_decl(Pos, ExtraPropId, SAL_TSid, ExtraProperty) -> ExtraPropertyDecl)
	   Insert_Context_Element(ExtraPropertyDecl, ContextElementsout1 -> ContextElementsout)
         |)

	  -- CC version:
	 -- CC Transition_system_Id update:
	 SAL_TSid'CC_Init <- SAL_CC_Init
	 (|
	     Global_Constant_Table -> Table
	     ne(Table, nil)
	     -- Adding an empty transition system and ltl properties to check the constants:
	     SAL_Generate_Empty_TS(-> TSDecl, TSId)
	     SAL_Generate_Constant_Assertions(TSId -> AssertionDecls)
	     where(SAL_CONTEXT_CONSTANTS'list(TSDecl, AssertionDecls) -> NewCCDecls)
	     Insert_Context_Elements(NewCCDecls, CC_ContextElements -> CC_ContextElements0)
	     -- A verification for the constants have already being made... cleaning the collection...
	     Global_Constant_Table <- nil
	 ||
	     where(CC_ContextElements -> CC_ContextElements0)
	 |)
	 -- Generating the transition system:
	 where(module_decl(Ident, SAL_TSid, nil, SAL_CC_Local_Var_Decls,
			   SAL_CC_Init, SAL_CC_Transitions) -> CC_ContextElement)
	 Insert_Context_Element(CC_ContextElement, CC_ContextElements0 -> CC_ContextElementsOut1)
	 -- Adding the cc properties from this transition system:
	 id_to_string(Ident -> TsIdStr)
	 SAL_Current_Cid -> Cid
	 Cid'Ident -> CidId
	 id_to_string(CidId -> CidIdStr)
	 Concatenate3(CidIdStr, "_", TsIdStr -> NameStr) 
	 Concatenate(NameStr, "_cc_check" -> AssertionIdStr)
	 string_to_id(AssertionIdStr -> AssertionId)
	 SAL_Generate_CC_Check_for_Vars(SAL_CC_Local_Var_Decls -> Condition)
         where(sal_funct_applic(sal_value_occ(val_id(sal_op_symb(sal_prefix_op(g))),nil),sal_argument(list(Condition,nil))) -> Property)
	 where(assertion_decl(Pos, AssertionId, SAL_TSid, Property) -> AssertionDecl)
	 Insert_Context_Element(AssertionDecl, CC_ContextElementsOut1 -> CC_ContextElementsOut2)

         Concatenate(NameStr, "_cc_check_guards" -> AssertionIdStrGuards)
	 string_to_id(AssertionIdStrGuards -> AssertionIdGuard)
	 SAL_Generate_CC_Check_for_Guards(SAL_CC_Transitions -> ConditionGuard)
         where(sal_funct_applic(sal_value_occ(val_id(sal_op_symb(sal_prefix_op(g))),nil),sal_argument(list(ConditionGuard,nil))) -> PropertyGuard)
	 where(assertion_decl(Pos, AssertionIdGuard, SAL_TSid, PropertyGuard) -> AssertionDeclGuard)
	 Insert_Context_Element(AssertionDeclGuard, CC_ContextElementsOut2 -> CC_ContextElementsOut)

'action' SAL_Generate_CC_Check_for_Vars(SAL_VAR_DECLS -> SAL_VALUE_EXPR)

/*  'rule' SAL_Generate_CC_Check_for_Vars(list(var_decl(_, _, _, rsl_built_in(sal_array(_,_, _))), Rest) -> Condition)
         SAL_Generate_CC_Check_for_Vars(Rest -> Condition)*/

  'rule' SAL_Generate_CC_Check_for_Vars(list(var_decl(_, _, VarId, Type), Rest) -> Condition)
  	 Select_CC_Result_Type(Type -> Tid)
	 Tid'Constructor -> vid(ConstVid)
	 DefaultPos(-> P)
	 where(sal_recogniser(ConstVid, sal_argument(SAL_VALUE_EXPRS'list(sal_var_occ(P, VarId), nil))) -> Cond0)
	 (|
	     ne(Rest, nil)
	     SAL_Generate_CC_Check_for_Vars(Rest -> Cond1)
             ne(Cond1, nil)
	     where(sal_ax_infix(Cond0, and, Cond1) -> Condition)
	 ||
	     where(Cond0 -> Condition)
	 |)

  'rule' SAL_Generate_CC_Check_for_Vars(nil -> nil)

'action' SAL_Generate_CC_Check_for_Guards(SAL_TRANSITIONS -> SAL_VALUE_EXPR)
  'rule' SAL_Generate_CC_Check_for_Guards(list(transition(_,Guard,_),Rest) -> Condition)
         SAL_Generate_CC_Check_for_Guard(Guard -> CC_Check_Guard)
         SAL_Generate_CC_Check_for_Guards(Rest -> RestCond)
         (|
           eq(RestCond,nil)
           where(CC_Check_Guard -> Condition)
         ||
           where(sal_ax_infix(CC_Check_Guard, and, RestCond) -> Condition)
         |)

  'rule' SAL_Generate_CC_Check_for_Guards(list(comprehended(Bindings,_,Trans),Rest) -> Condition)
         SAL_Generate_CC_Check_for_Guards(list(Trans, nil) -> CC_Check_Guard)
         SAL_Generate_CC_Check_for_Guards(Rest -> RestCond)
         (|
           eq(RestCond,nil)
           where(sal_quantified(forall, bindings(Bindings), CC_Check_Guard) -> Condition)
         ||
           where(sal_ax_infix(sal_quantified(forall, bindings(Bindings), CC_Check_Guard), and, RestCond) -> Condition)
         |)

  'rule' SAL_Generate_CC_Check_for_Guards(list(cc_comprehended(Bindings,Guard),Rest) -> Condition)
         SAL_Generate_CC_Check_for_Guard(Guard -> CC_Check_Guard)
         SAL_Generate_CC_Check_for_Guards(Rest -> RestCond)
         (|
           eq(RestCond,nil)
           where(sal_quantified(forall, bindings(Bindings), CC_Check_Guard) -> Condition)
         ||
           where(sal_ax_infix(sal_quantified(forall, bindings(Bindings), CC_Check_Guard), and, RestCond) -> Condition)
         |)

  'rule' SAL_Generate_CC_Check_for_Guards(nil -> nil)

  'rule' SAL_Generate_CC_Check_for_Guards(list(else_trans(_,_), Rest) -> Condition)
         SAL_Generate_CC_Check_for_Guards(Rest -> Condition)

'action' SAL_Generate_CC_Check_for_Guard(SAL_VALUE_EXPR -> SAL_VALUE_EXPR)
  'rule' SAL_Generate_CC_Check_for_Guard(Expr -> ResExpr)
           where(Expr -> sal_ax_infix(_,and,sal_esp_unary_prefix_occ(_,Guard)))
           --Get_Inner_Guard_Non_Let(Expr -> Expr1)
           Default_Bool_Tid -> BTid
	   BTid'Lifted_Tid -> tid(LBTid)
	   where(sal_cc_op(sal_function_op(is_bool), LBTid) -> SAL_Op)
	   where(sal_esp_unary_prefix_occ(val_id(SAL_Op), Guard) -> ResExpr)

  'rule' SAL_Generate_CC_Check_for_Guard(Expr -> ResExpr)
         where(Expr -> sal_let_expr(Ident,Type,Names,Defs,Init,sal_ax_infix(_,and,sal_esp_unary_prefix_occ(_,Guard))))
         Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 where(sal_cc_op(sal_function_op(is_bool), LBTid) -> SAL_Op)
	 where(sal_esp_unary_prefix_occ(val_id(SAL_Op), Guard) -> ResTemp)
         DefaultPos(-> P)
         where(sal_let_expr(Ident, Type, Names, Defs, Init, ResTemp) -> ResExpr)
         --where(sal_quantified(forall, bindings(Bindings), sal_let_expr(Ident, Type, Names, Defs, Init, ResTemp)) -> ResExpr)

  'rule' SAL_Generate_CC_Check_for_Guard(Expr -> ResExpr)
         where(Expr -> sal_let_expr(Ident, Type, Names, Defs, Init, Expr2))
         SAL_Generate_CC_Check_for_Guard(Expr2 -> ResExprTemp)
         where(sal_let_expr(Ident, Type, Names, Defs, Init, ResExprTemp) -> ResExpr)
         --where(sal_quantified(forall, bindings(Bindings), ResExprTemp) -> ResExpr)
         --where(ResExprTemp -> sal_quantified(forall, Bindings2, Expr3))
         --where(sal_quantified(forall, Bindings2, sal_let_expr(Ident, Type, Names, Defs, Init, Expr3)) -> ResExpr)

-- Gets the real cc-version of the guard, not including the checks of the vars
'action' Get_Inner_Guard_Non_Let(SAL_VALUE_EXPR -> SAL_VALUE_EXPR)

  'rule' Get_Inner_Guard_Non_Let(sal_ax_infix(_,and,sal_esp_unary_prefix_occ(_,Guard)) -> Guard)

'action' Get_Inner_Guard_Let(SAL_VALUE_EXPR -> SAL_VALUE_EXPR, IDENT, SAL_TYPE_EXPR)

  'rule' Get_Inner_Guard_Let(sal_let_expr(Ident,Type,Names,Defs,Init,sal_ax_infix(_,and,sal_esp_unary_prefix_occ(_,Guard))) -> --sal_let_expr(Ident,Type,Names,Defs,Init,Guard))
--sal_quantified(forall, bindings(list(sal_typed_id(P,id(Ident),Type),nil)), Guard))
Guard, Ident, Type)

  DefaultPos(-> P)

'action' SAL_Generate_Empty_TS(-> SAL_CONTEXT_CONSTANT, SAL_TranSys_id)

  'rule' SAL_Generate_Empty_TS(-> TSDecl, TSId)
	 string_to_id("_dummy_TS" -> Ident)
	 DefaultPos(-> Pos)
	 New_SAL_TranSys_id(Pos,Ident -> TSId)
	 where(module_decl(Ident, TSId, nil, nil,nil,nil) -> TSDecl)

'action' SAL_Generate_Constant_Assertions(SAL_TranSys_id -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Generate_Constant_Assertions(TSId -> AssertionDecls)
	 Global_Constant_Table -> Table
	 SAL_Generate_Assertions(Table, TSId -> AssertionDecls)

'action' SAL_Generate_Assertions(CONSTANT_DATA_LIST, SAL_TranSys_id -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Generate_Assertions(list(info(Vid, Tid), T), TSId -> list(A1, RA))
	 Vid'IdOp -> id(Ident)
--	 Vid'Cid -> cid(Cid)
	 SAL_Current_Cid -> Cid
  	 -- Adding the cc property to check this constant for nav values:
	 id_to_string(Ident -> IdStr)
	 Cid'Ident -> CidId
	 id_to_string(CidId -> CidIdStr)
	 Concatenate3(CidIdStr, "_", IdStr -> NameStr) 
	 Concatenate(NameStr, "_cc_check" -> AssertionIdStr)
	 string_to_id(AssertionIdStr -> AssertionId)
	 Tid'Constructor -> vid(ConstVid)
	 DefaultPos(-> Pos)
	 where(sal_recogniser(ConstVid, sal_argument(SAL_VALUE_EXPRS'list(sal_esp_value_occ(Vid), nil))) -> Condition)
	 -- G applied to constant assertions is not necessary
	 -- where(sal_funct_applic(sal_value_occ(val_id(sal_op_symb(sal_prefix_op(g))),nil),sal_argument(list(Condition,nil))) -> Property)
	 where(assertion_decl(Pos, AssertionId, TSId, Condition) -> A1)
	 SAL_Generate_Assertions(T, TSId -> RA)

  'rule' SAL_Generate_Assertions(nil, _ -> nil)
--------------------------------------------------
'action' SAL_Process_TS_var_decls(VAR_DECL_TYPE, DECL -> SAL_VAR_DECLS, SAL_VAR_DECLS, SAL_INITIALIZATIONS, SAL_INITIALIZATIONS)

  'rule' SAL_Process_TS_var_decls(DeclType, variable_decl(P, Defs) -> VariableDecls, CCVariableDecls, Inits, CC_Init)
	 SAL_Process_variables(DeclType, Defs -> VariableDecls, CCVariableDecls, Inits, CC_Init)

'action' SAL_Process_variables(VAR_DECL_TYPE, VARIABLE_DEFS -> SAL_VAR_DECLS, SAL_VAR_DECLS, SAL_INITIALIZATIONS, SAL_INITIALIZATIONS)

  'rule' SAL_Process_variables(DeclType, list(H, Rest) -> list(SAL_H, SAL_Rest), list(SAL_H_CC, SAL_CC_Rest), InitList, CC_InitList)
	 where(H -> single(Pos,Ident,Type,Init))
	 -- Generate the variable id for the declaration:
	 -- Translate the type:
	 SAL_Gen_Type_Expr(Pos, Type -> SalType, CC_SALType1)
	 New_SAL_variable_id(Pos,Ident,SalType -> VarId)
	 where(SAL_VAR_DECL'var_decl(Pos,Ident,VarId,SalType) -> SAL_H)
	 -- Process the rest of the list:
	 SAL_Process_variables(DeclType, Rest -> SAL_Rest, SAL_CC_Rest, SAL_I_Rest, SAL_CC_I_Rest)
	 -- Process the initialization:
	 (|
            eq(DeclType, local)
	    where(CC_SALType1 -> CC_SALType)
	    -- Generating the type expression for the cc-version,
	    -- the local variables must have the lifted type (they will be modified by the Transition System)
	    (|
	        where(Init -> initial(VE))
		Gen_SAL_Expr(VE, normal, Type -> SAL_I_Expr, SAL_CC_I_Expr)
		where(init(VarId, SAL_I_Expr) -> SAL_I_H)
		where(SAL_INITIALIZATIONS'list(SAL_I_H, SAL_I_Rest) -> InitList)
		-- cc init generation:
		where(init(VarId, SAL_CC_I_Expr) -> SAL_I_H_CC)
		where(SAL_INITIALIZATIONS'list(SAL_I_H_CC, SAL_CC_I_Rest) -> CC_InitList)
	    ||
		eq(DeclType, local)
		Putwarning(Pos)
		Putmsg("Local variable not initialized (")
		Print_id(Ident)
		Putmsg("). The model checker will initialize it to a random value\n")
		where(SAL_I_Rest -> InitList)
		where(SAL_CC_I_Rest -> CC_InitList)
	    |)
	 ||
	    eq(DeclType, comprehended)
	    -- Translate the type:
	    where(CC_SALType1 -> CC_SALType)
	    [|
	        where(Init -> initial(VE))
	        Puterror(Pos)
		Putmsg("Variables used in comprehended transitions can not be initialized\n")
	    |]	    
	    where(SAL_I_Rest -> InitList)
	    where(SAL_CC_I_Rest -> CC_InitList)
	 ||
	    -- Input variables:
	    -- The type for the input variables must be the basic (non-lifted) type (the input
	    -- variables are handled by the model checker to manipulate the transition system.
	    -- It wouldn't be correct to allow the model checker to feed the transition system
	    -- with navs...
	    -- The type must be the base type before lifting in the comprehended declaration:
	    where(CC_SALType1 -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	    Tid'Constructor -> vid(Const)
	    Tid'Lifted_fields -> Fields
	    SAL_Find_Accesor_in_Fields(Fields, Const -> AccVid)
	    AccVid'Type -> CC_SALType
	    [|
	        where(Init -> initial(VE))
	        Puterror(Pos)
		Putmsg("Input variables can not be initialized\n")
	    |]
	    where(SAL_I_Rest -> InitList)
	    where(SAL_CC_I_Rest -> CC_InitList)
	 |)
	 -- Building the CC part:
	 (|
	    eq(DeclType, comprehended)
	    -- The type must be the base type before lifting in the comprehended declaration:
	    where(CC_SALType1 -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	    Tid'Constructor -> vid(Const)
	    Tid'Lifted_fields -> Fields
	    SAL_Find_Accesor_in_Fields(Fields, Const -> AccVid)
	    AccVid'Type -> Esp_CC_SALType
	    where(SAL_VAR_DECL'var_decl(Pos,Ident,VarId,Esp_CC_SALType) -> SAL_H_CC)
	 ||
	    where(SAL_VAR_DECL'var_decl(Pos,Ident,VarId,CC_SALType) -> SAL_H_CC)
	 |)

  'rule' SAL_Process_variables(DeclType, list(H, Rest) -> SAL_Rest, SAL_CC_Rest, InitList,CC_InitList)
	 where(H -> multiple(Pos,Idents,Type))
	 Puterror(Pos)
	 Putmsg("Multiple variable declarations not allowed\n")
	 -- This is not allowed because there is only one pos for all the variables
	 -- That will make imposible to distinguish later on among them.
	 SAL_Process_variables(DeclType, Rest -> SAL_Rest, SAL_CC_Rest, InitList,CC_InitList)

  'rule' SAL_Process_variables(_, nil -> nil,nil,nil,nil)
--------------------------------------------------
'action' SAL_Process_TS_primed_vars(DECL)

  'rule' SAL_Process_TS_primed_vars(variable_decl(P, Defs))
	 SAL_Process_primed_variables(Defs)

'action' SAL_Process_primed_variables(VARIABLE_DEFS)

  'rule' SAL_Process_primed_variables(list(H, Rest))
	 where(H -> single(Pos,Ident,Type,_))
	 -- Translate the type:
	 SAL_Gen_Type_Expr(Pos, Type -> SalType, _)
	 -- Generate the variable id for the declaration:
	 New_SAL_variable_id(Pos,Ident,SalType -> VarId)
	 SAL_Process_primed_variables(Rest)

  'rule' SAL_Process_primed_variables(nil)
--------------------------------------------------
'action' SAL_Process_Transitions(SAL_VAR_DECLS, SAL_VAR_DECLS, TRANSITION_OPERATOR -> SAL_TRANSITIONS, SAL_TRANSITIONS)

  'rule' SAL_Process_Transitions(VarDecls, InputDecls, TO -> Res1, ResCC)
        SAL_Process_Transitions_With_Guard(VarDecls, InputDecls, TO, nil -> Res1, ResCC, _)

/*'action' Concat_ExtraGuards(EXTRA_GUARD, EXTRA_GUARD -> EXTRA_GUARD)
  'rule' Concat_ExtraGuards(nil, E -> E)
  'rule' Concat_ExtraGuards(E, nil -> E)
  'rule' Concat_ExtraGuards(guard(Val1,P1), guard(Val2,P2) -> guard(ax_infix(P1,Val1,or,Val2,P2),P1))*/

'action' SAL_Process_Transitions_With_Guard(SAL_VAR_DECLS, SAL_VAR_DECLS, TRANSITION_OPERATOR, EXTRA_GUARD -> SAL_TRANSITIONS, SAL_TRANSITIONS, EXTRA_GUARD)

  'rule' SAL_Process_Transitions_With_Guard(VarDecls, InputDecls, equal_priority(L,R,G), ExtraGuard -> SH, CC_SH, G)
	SAL_Process_Transitions_With_Guard(VarDecls, InputDecls, L, ExtraGuard -> SH1, CC_SH1, _)
	SAL_Process_Transitions_With_Guard(VarDecls, InputDecls, R, ExtraGuard -> SH2, CC_SH2, _)
        SAL_Concatenate_Lists(SH1, SH2 -> SH)
	SAL_Concatenate_Lists(CC_SH1, CC_SH2 -> CC_SH)

  'rule' SAL_Process_Transitions_With_Guard(VarDecls, InputDecls, greater_priority(L,R,G), ExtraGuard -> SH, CC_SH, G)
        SAL_Process_Transitions_With_Guard(VarDecls, InputDecls, L, ExtraGuard -> SH1, CC_SH1, LG)
	--CheckExtraGuard(LG ->)
Concat_Extra_Guards(ExtraGuard, LG -> LG2)
        SAL_Process_Transitions_With_Guard(VarDecls, InputDecls, R, LG2 -> SH2, CC_SH2, _)
        SAL_Concatenate_Lists(SH1, SH2 -> SH)
	SAL_Concatenate_Lists(CC_SH1, CC_SH2 -> CC_SH)

  'rule' SAL_Process_Transitions_With_Guard(VarDecls, InputDecls, bracketed(O,G), ExtraGuard -> SH, CC_SH, G)
        SAL_Process_Transitions_With_Guard(VarDecls, InputDecls, O, ExtraGuard -> SH, CC_SH, _)

  'rule' SAL_Process_Transitions_With_Guard(VarDecls, InputDecls, guarded_command(CM,G), ExtraGuard -> list(SH,nil), list(CC_SH,nil), G)
        SAL_Process_Transition(VarDecls, InputDecls, CM, ExtraGuard -> SH, CC_SH)
	--CheckExtraGuard(G ->) -- Fails, when just trying to check the extra guard

'action' SAL_Concatenate_Lists(SAL_TRANSITIONS, SAL_TRANSITIONS -> SAL_TRANSITIONS)

  'rule' SAL_Concatenate_Lists(nil, nil -> nil)

  'rule' SAL_Concatenate_Lists(A, nil -> A)

  'rule' SAL_Concatenate_Lists(nil, B -> B)

  'rule' SAL_Concatenate_Lists(list(H,T), B -> list(H,C))
         SAL_Concatenate_Lists(T, B -> C)

'action' SAL_Process_Transition(SAL_VAR_DECLS, SAL_VAR_DECLS, GUARDED_COMMAND, EXTRA_GUARD -> SAL_TRANSITION, SAL_TRANSITION)

  'rule' SAL_Process_Transition(VarDecls, InputDecls, guarded_cmd(OptIdent, GuardOrg, Cmds), ExtraGuard -> 
					transition(OptIdent, SAL_Guard, SAL_Cmds),
					transition(OptIdent, SAL_CC_Guard,SAL_CC_Cmds))
         GetGuardValueExpression(GuardOrg, ExtraGuard -> Guard)
	 Gen_SAL_Expr(Guard, normal, bool -> SAL_Guard, SAL_CC_Guard1)
         Gen_SAL_Cmds(Cmds, nil, nil -> SAL_Cmds, SAL_CC_Cmds1Temp)
         Concat_cc_array_sets(SAL_CC_Cmds1Temp -> SAL_CC_Cmds1)
	 -- Adding the is_true at the beginning of the guard in the cc-version:
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid) -- TODO: Tjek nav på guards
	 where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	 where(sal_esp_unary_prefix_occ(val_id(SAL_Op), SAL_CC_Guard1) -> SAL_CC_Guard2)
	 -- Extend the guard: (this will include the checking for non-nav values for all variables in the
	 -- guard condition)
	 Extend_SAL_Guard(VarDecls, nil -> SAL_CC_Guard3) -- this should also receive the local variables (it is a stub for the moment)
         where(sal_ax_infix(SAL_CC_Guard3, and, SAL_CC_Guard2) -> SAL_CC_Guard4)
	 SAL_Replace_Vars_in_Expr(InputDecls, SAL_CC_Guard4 -> SAL_CC_Guard)
	 SAL_Replace_Vars_in_Exprs(InputDecls, SAL_CC_Cmds1 -> SAL_CC_Cmds)

  'rule' SAL_Process_Transition(VarDecls, InputDecls, else_cmd(OptIdent,Cmds), ExtraGuard -> 
					  else_trans(OptIdent, SAL_Cmds), 
					  transition(OptIdent,
					  SAL_CC_Guard,SAL_CC_Cmds))
	 Gen_SAL_Cmds(Cmds, nil, nil -> SAL_Cmds, SAL_CC_Cmds1Temp)
         Concat_cc_array_sets(SAL_CC_Cmds1Temp -> SAL_CC_Cmds1)
	 -- The varDecls can not be nil (we don't accept TSs without local decls)
	 Extend_SAL_Guard(VarDecls, nil -> SAL_CC_Guard1)
	 SAL_Replace_Vars_in_Expr(InputDecls, SAL_CC_Guard1 -> SAL_CC_Guard)
	 SAL_Replace_Vars_in_Exprs(InputDecls, SAL_CC_Cmds1 -> SAL_CC_Cmds)

  'rule' SAL_Process_Transition(VarDecls, InputDecls, comprehended_cmd(TPS, Pos, Trans), ExtraGuard -> comprehended(SALBindings, Pos, SAL_Trans), comprehended(SALBindings, Pos, SAL_CC_Trans1))
         Gen_SALBindings_from_Typings(TPS -> SALBindings, SAL_CC_Bindings, TypeList)
	 SAL_Process_Transition(VarDecls, InputDecls, Trans, ExtraGuard -> SAL_Trans, SAL_CC_Trans)
         --SAL_Set_Lets_Transition(SAL_CC_Trans, SALBindings, TypeList -> SAL_CC_Trans)
         (|
	   where(SAL_CC_Trans -> transition(OptId, Guard, Cmds))
	   SAL_Turn_Bindings_into_Lets(SALBindings, Guard, TypeList -> Guard1, SAL_CC_Bindings1)
	   NumTypings(TPS -> N) 
	   Add_Lets_to_Commands(N, Guard1, Cmds -> Cmds1)
	   where(transition(OptId, Guard1, Cmds1) -> SAL_CC_Trans1)
         ||
           where(SAL_CC_Trans -> comprehended(BindingsIn, PosIn, TransIn))
           SAL_Process_Transition(VarDecls, InputDecls, Trans, ExtraGuard -> _, SAL_CC_Trans2)
           Get_Inner_Transition(SAL_CC_Trans2 -> SAL_CC_Trans3)
           where(SAL_CC_Trans3 -> transition(OptId, Guard, Cmds))
	   SAL_Turn_Bindings_into_Lets(SALBindings, Guard, TypeList -> Guard1, SAL_CC_Bindings1)
	   NumTypings(TPS -> N) -- TODO: Max type should not be used.
	   Add_Lets_to_Commands(N, Guard1, Cmds -> Cmds1)
           Set_Inner_Command(SAL_CC_Trans, Cmds1, Guard1 -> SAL_CC_Trans1)
	   --where(transition(OptId, Guard1, Cmds1) -> SAL_CC_Trans1)
         |)


'action' Set_Inner_Command(SAL_TRANSITION, SAL_VALUE_EXPRS, SAL_VALUE_EXPR -> SAL_TRANSITION)
  'rule' Set_Inner_Command(transition(Id, Guard, Cmds), NewCmds, NewGuard -> transition(Id, NewGuard, NewCmds))

  'rule' Set_Inner_Command(comprehended(SALBindings, Pos, Trans), Cmds, Guard -> comprehended(SALBindings, Pos, NewTrans)) 
         Set_Inner_Command(Trans, Cmds, Guard -> NewTrans)

'action' Get_Inner_Transition(SAL_TRANSITION -> SAL_TRANSITION)
  'rule' Get_Inner_Transition(comprehended(_,_,Trans) -> Res)
         Get_Inner_Transition(Trans -> Res)

  'rule' Get_Inner_Transition(Trans -> Trans)

/*'action' SAL_Set_Lets_Transition(SAL_TRANSITION, SAL_BINDINGS, PRODUCT_TYPE -> SAL_TRANSITION)
  'rule' SAL_Set_Lets_Transition(transition(Id,G,Cmd), SALBindings, Guard, TypeList -> SAL_CC_Trans1)
         SAL_Turn_Bindings_into_Lets(SALBindings, Guard, TypeList -> Guard1, SAL_CC_Bindings1)
	 NumTypings(TPS -> N) -- TODO: Max type should not be used.
	 Add_Lets_to_Commands(N, Guard1, Cmds -> Cmds1)
	 where(transition(OptId, Guard1, Cmds1) -> SAL_CC_Trans1)


  'rule' SAL_Set_Lets_Transition(comprehended_cmd(Bindings, Pos, Trans), SALBindings, TypeList -> SAL_CC_Trans)*/



'action' NumTypings(TYPINGS -> INT)

  'rule' NumTypings(list(_,TPS) -> N+1):
         NumTypings(TPS -> N)

  'rule' NumTypings(nil -> 0):


'action' Add_Lets_to_Commands(INT, SAL_VALUE_EXPR, SAL_VALUE_EXPRS -> SAL_VALUE_EXPRS)
	 
  'rule' Add_Lets_to_Commands(N, Expr, list(Cmd, Cmds) -> list(Cmd1, Cmds1)):
  	 Add_Lets_to_Command(N, Expr, Cmd -> Cmd1)
	 Add_Lets_to_Commands(N, Expr, Cmds -> Cmds1)

  'rule' Add_Lets_to_Commands(_, _, nil -> nil):

'action' Add_Lets_to_Command(INT, SAL_VALUE_EXPR, SAL_VALUE_EXPR -> SAL_VALUE_EXPR)

  'rule' Add_Lets_to_Command(N, Expr, Cmd -> Cmd1):
  	 where(Cmd -> sal_infix_occ(V, Op, E))
	 where(Op -> val_id(sal_op_symb(sal_infix_op(eq))))
	 Add_Lets_to_Expr(N, Expr, E -> E1)
	 where(sal_infix_occ(V, Op, E1) -> Cmd1)

  'rule' Add_Lets_to_Command(N,Expr, Cmd -> Cmd):
         where(Cmd -> sal_cc_array_set(P,Id,Ty,Index,Value))
         Add_Lets_to_Exprs(N, Expr, Index -> Index1)
         Add_Lets_to_Expr(N, Expr, Value -> Value1)
         --Add_Lets_to_Expr(N, Expr, 
         where(sal_cc_array_set(P,Id,Ty,Index1,Value1) -> Cmd1)

'action' Add_Lets_to_Exprs(INT, SAL_VALUE_EXPR, SAL_VALUE_EXPRS -> SAL_VALUE_EXPRS)
  'rule' Add_Lets_to_Exprs(_, _, nil -> nil)

  'rule' Add_Lets_to_Exprs(N, Expr, list(H,T) -> list(HRes,TRes))
         Add_Lets_to_Expr(N, Expr, H -> HRes)
         Add_Lets_to_Exprs(N, Expr, T -> TRes)

'action' Add_Lets_to_Expr(INT, SAL_VALUE_EXPR, SAL_VALUE_EXPR -> SAL_VALUE_EXPR)

  'rule' Add_Lets_to_Expr(N, _, E -> E):
  	 eq(N, 0)

  'rule' Add_Lets_to_Expr(N, Let, E -> E2):
	 where(Let -> sal_let_expr(Id, T, Names, Defs, Init, Expr))
	 Add_Lets_to_Expr(N-1, Expr, E -> E1)
  	 where(sal_let_expr(Id, T, Names, Defs, Init, E1) -> E2)

 -- 'rule' Add_Lets_to_Expr(N, Infix




-------------------------------------------------------------------------------------
-- Extend_SAL_Guard
-------------------------------------------------------------------------------------
-- This function extends the guard for a given guarded command in order to include 
-- non-nav checkings for the transition system state variables
-------------------------------------------------------------------------------------
'action' Extend_SAL_Guard(SAL_VAR_DECLS, SAL_VALUE_EXPR -> SAL_VALUE_EXPR)

  'rule' Extend_SAL_Guard(list(var_decl(_, _, _, rsl_built_in(sal_array(_,_,_))), Rest), OrigCond -> ExtendedGuard)
         Extend_SAL_Guard(Rest, OrigCond -> ExtendedGuard)

  'rule' Extend_SAL_Guard(list(var_decl(_, _, _, rsl_built_in(sal_array(_,_,_))), nil), OrigCond -> OrigCond)

	 -- Deals with the case where we are extending the guard for an 'else ' transition:
  'rule' Extend_SAL_Guard(list(var_decl(_, _, VarId, Type), nil), nil -> ExtendedGuard)
         where(Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)), _)))
	 Tid'Constructor -> vid(ConstVid)
	 DefaultPos(-> P)
	 where(sal_recogniser(ConstVid, sal_argument(SAL_VALUE_EXPRS'list(sal_var_occ(P, VarId), nil))) -> ExtendedGuard)

  'rule' Extend_SAL_Guard(list(var_decl(_, _, VarId, Type), Rest), OrigCond -> ExtendedGuard)
         Extend_SAL_Guard(Rest, OrigCond -> NewGuard)
	 Select_CC_Result_Type(Type -> Tid)
	 Tid'Constructor -> vid(ConstVid)
	 DefaultPos(-> P)
	 where(sal_recogniser(ConstVid, sal_argument(SAL_VALUE_EXPRS'list(sal_var_occ(P, VarId), nil))) -> NewProp)
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 where(sal_ax_infix(NewProp, and, NewGuard) -> ExtendedGuard)

  'rule' Extend_SAL_Guard(nil, OrigCond -> OrigCond)

-------------------------------------------------------------------------------------
-- SAL_Generate_Lets_from_Vars
-------------------------------------------------------------------------------------
-- This function generates the let expressions needed to lift the variables introduced
-- in a comprehended transition in RSL.
-- For example:
--     [=] b : T.Berth :-
--             [dock]
--             can_dock(ship,b,harb) ==>
--             harb' = dock(ship, b, harb))
--
-- Can not be translated declaring b of the lifted type for Berth (because transitions
-- for the nav values would be generated by the model checker expansion of comprehended
-- transitions). To avoid this, variables in the comprehended transitions are declared of
-- the base type before lifting and lifted with a let. With this approach, the code above
-- would be translated as:
-- ([] (    b : SAL_TYPES_CC!Int__):   <-- NOTE THE NON-LIFTED TYPE HERE
--        dock :
--           LET b : L_BUILTIN!Int__cc = lifted_constructor(b) 
--         IN
--               can_dock(ship, b, harb) --> harb' = dock(ship, b, harb))
-- This function will generate the LET declaration(s) as needed
-------------------------------------------------------------------------------------
'action' SAL_Generate_Lets_from_Vars(VARIABLE_DEFS, SAL_TRANSITION -> SAL_VALUE_EXPR)

  'rule' SAL_Generate_Lets_from_Vars(list(single(Pos,Id, Type, _), nil), Body -> sal_esp_let_expr(Id, CC_Type, InitExpr, Body))
	 SAL_Gen_Type_Expr(Pos, Type -> _, CC_Type)
	 where(CC_Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)), _)))
	 Tid'Constructor -> vid(ConstVid)
	 DefaultPos(-> P)
	 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Id)), nil), nil))) -> InitExpr)

  'rule' SAL_Generate_Lets_from_Vars(list(single(Pos,Id, Type, _), Rest), Body -> sal_let_expr(Id, CC_Type, nil,nil, InitExpr, NewBody))
	 SAL_Generate_Lets_from_Vars(Rest, Body -> NewBody)
	 SAL_Gen_Type_Expr(Pos, Type -> _, CC_Type)
	 where(CC_Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)), _)))
	 Tid'Constructor -> vid(ConstVid)
	 DefaultPos(-> P)
	 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Id)), nil), nil))) -> InitExpr)
 
-------------------------------------------------------------------------------------
'action' Concat_cc_array_sets(SAL_VALUE_EXPRS -> SAL_VALUE_EXPRS)
  'rule' Concat_cc_array_sets(nil -> nil)

  'rule' Concat_cc_array_sets(list(H,T) -> Res)
         Append_to_SAL_array(H, T -> NewExpr, Rest)
         Concat_cc_array_sets(Rest -> NewRest)
         where(SAL_VALUE_EXPRS'list(NewExpr, NewRest) -> Res)

'action' Append_to_SAL_array(SAL_VALUE_EXPR, SAL_VALUE_EXPRS -> SAL_VALUE_EXPR, SAL_VALUE_EXPRS)

  'rule' Append_to_SAL_array(sal_infix_occ(ArN,Op,sal_cc_array_set(P,Ar,Ty,In,Va)), list(H,T) -> NewExpr, Others)
         eq(ArN, Ar)
         (|
           where(H -> sal_infix_occ(ArN2,Op2,sal_cc_array_set(P2,Ar2,Ty2,In2,Va2)))
           --where(Ar2 -> sal_var_occ(_,N1))
           --where(Ar -> sal_var_occ(_,N2))
           where(ArN -> sal_var_occ(_,N3))
           where(ArN2 -> sal_var_occ(_,N4))
           eq(N3,N4)
           Append_to_SAL_array(H, T -> sal_infix_occ(_,_,E), Others)
           where(sal_infix_occ(ArN, Op, sal_cc_array_set(P,E,Ty,In,Va)) -> NewExpr)
         ||
           Append_to_SAL_array(sal_infix_occ(Ar,Op,sal_cc_array_set(P,Ar,Ty,In,Va)), T -> NewExpr, T2)
           where(SAL_VALUE_EXPRS'list(H,T2) -> Others)
         |)

  'rule' Append_to_SAL_array(Expr, List -> Expr, List)

'action' Gen_SAL_Cmds(COMMANDS, SAL_VALUE_EXPRS, SAL_VALUE_EXPRS ->
	 					 SAL_VALUE_EXPRS,
						 SAL_VALUE_EXPRS)

  'rule' Gen_SAL_Cmds(list(Cmd, CmdsTail), SALExprs, SAL_CC_Exprs -> SALExprsout, SAL_CC_Exprsout):
  	 where(Cmd -> r_cmd(ass_occ(P, Id, Q, Expr)))
	 Id'Type -> TExpr
	 Gen_SAL_Expr(Expr, normal, TExpr -> SALExpr, SAL_CC_Expr0)
	 Id'Pos -> VarPos
	 look_up_variable_id(VarPos -> OptSALVarId)
	 (|
	   where(OptSALVarId -> var(SALVarId))
           (|
             where(Cmd -> r_cmd(ass_occ(_,_,_,array_expr(_,_,_))))
             where(SAL_CC_Expr0 -> SAL_CC_Expr)
           ||
	     Isin_subtype(Expr, TExpr -> Pred)
	     Simplify(Pred -> Pred1)
	     (|
	       ne(Pred1, no_val)
	       -- include subtype check in CC version
	       string_to_id("RSL_res_" -> ResId)
	       IncreaseCol(P -> ResPos)
	       New_value_id(ResPos, id_op(ResId) -> ResI)
	       Maxtype(TExpr -> MaxTExpr)
	       ResI'Type <- MaxTExpr
	       Isin_subtype(val_occ(P, ResI, nil), TExpr -> Pred2)
	       Simplify(Pred2 -> Pred3)
	       Gen_SAL_Expr(Pred3, normal, bool -> _, Cond)
	       Default_Bool_Tid -> BTid
	       BTid'Lifted_Tid -> tid(LBTid)
	       where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	       where(sal_esp_unary_prefix_occ(val_id(SAL_Op), Cond) -> IsTrueCond)
	       SALVarId'Ident -> Ident
	       id_to_string(Ident -> VarStr1)
	       PruneQuote(VarStr1 -> VarStr)
	       Concatenate("Update_to_variable_", VarStr -> Str1)
	       Concatenate(Str1, "_not_in_subtype" -> NavStr)
	       Extend_Nav_Type(P, NavStr -> NavId)
	       SAL_Gen_Type_Expr(P, TExpr -> _, CC_Type)
	       SAL_Generate_Result_for_Violation(CC_Type, sal_esp_value_occ(NavId) -> Else)
	       where(sal_named_val(id_op(id(ResId))) -> ResOcc)
	       where(sal_if_expr(IsTrueCond, ResOcc, nil, else(Else)) -> IF)
	       where(sal_let_expr(ResId, CC_Type, nil, nil, SAL_CC_Expr0, IF) -> SAL_CC_Expr)
	     ||
	       where(SAL_CC_Expr0 -> SAL_CC_Expr)
	     |)
           |)
	   where(sal_var_occ(P, SALVarId) -> SALVar)
	   where(SAL_VALUE_ID'val_id(sal_op_symb(sal_infix_op(eq))) -> Op)
	   where(SAL_VALUE_EXPR'sal_infix_occ(SALVar,Op,SALExpr) -> SALCmd)
	   -- cc
	   where(SAL_VALUE_EXPR'sal_infix_occ(SALVar,Op,SAL_CC_Expr) -> CC_Cmd)
	 ||
	   where(SAL_VALUE_EXPR'not_supported -> SALCmd)
	   where(SALCmd -> CC_Cmd)
	   Puterror(P)
	   Putmsg("Internal error: No SAL information found for the variable occurrence.\n")
	   Putnl()
	 |)
	 SAL_Insert_Expr(SALCmd, SALExprs -> SALExprs1)
	 SAL_Insert_Expr(CC_Cmd, SAL_CC_Exprs -> SAL_CC_Exprs1)
	 Gen_SAL_Cmds(CmdsTail, SALExprs1, SAL_CC_Exprs1 -> SALExprsout, SAL_CC_Exprsout)

  'rule' Gen_SAL_Cmds(list(Cmd, CmdsTail), SALExprs, SAL_CC_Exprs -> SALExprsout, SAL_CC_Exprsout):
  	 where(Cmd -> r_cmd(array_ass_occ(P, Id, Q, Index, Expr)))
         Id'Type -> Temp
         --Remove_Brackets(Temp -> array(T1, TExpr))
         Gen_SAL_Index_Exprs(Index, Temp -> SALExprIndex, SAL_CC_Expr0Index, TExpr)
	 Gen_SAL_Expr(Expr, normal, TExpr -> SALExpr, SAL_CC_Expr0)
	 --Gen_SAL_Expr(Index, normal, T1 -> SALExprIndex, SAL_CC_Expr0Index)
	 Id'Pos -> VarPos
	 look_up_variable_id(VarPos -> OptSALVarId)
	 (|
	   where(OptSALVarId -> var(SALVarId))

           Gen_SAL_CC_Cmds_For_Arrays(Expr, TExpr, P, SALVarId, SAL_CC_Expr0 -> SAL_CC_Expr, P1)
           Gen_SAL_CC_Cmds_For_Arrays_Val_Exprs(Index, Temp, P1, SALVarId, SAL_CC_Expr0Index -> SAL_CC_IndexExpr, P2)

	   where(sal_array_var_occ(P, SALVarId, SALExprIndex) -> SALVar)
           where(SAL_VALUE_ID'val_id(sal_op_symb(sal_infix_op(eq))) -> Op)
	   where(SAL_VALUE_EXPR'sal_infix_occ(SALVar,Op,SALExpr) -> SALCmd)
	   -- cc
	   --where(SAL_VALUE_EXPR'sal_infix_occ(SAL_CC_Var,Op,SAL_CC_Expr) -> CC_Cmd)
           SALVarId'Type -> Type
           where(sal_cc_array_set(P, sal_var_occ(P,SALVarId), Type, SAL_CC_IndexExpr, SAL_CC_Expr) -> CC_Cmd1)
           where(Op -> val_id(sal_op_symb(sal_infix_op(eq))))
           where(sal_infix_occ(sal_var_occ(P,SALVarId), Op, CC_Cmd1) -> CC_Cmd)
	   
	 ||
	   where(SAL_VALUE_EXPR'not_supported -> SALCmd)
	   where(SALCmd -> CC_Cmd)
	   Puterror(P)
	   Putmsg("Internal error: No SAL information found for the variable occurrence.\n")
	   Putnl()
	 |)
	 SAL_Insert_Expr(SALCmd, SALExprs -> SALExprs1)
	 SAL_Insert_Expr(CC_Cmd, SAL_CC_Exprs -> SAL_CC_Exprs1)
	 Gen_SAL_Cmds(CmdsTail, SALExprs1, SAL_CC_Exprs1 -> SALExprsout, SAL_CC_Exprsout)


  'rule' Gen_SAL_Cmds(nil, SALExprs, SAL_CC_Exprs -> SALExprs, SAL_CC_Exprs)

'action' Gen_SAL_Index_Exprs(VALUE_EXPRS, TYPE_EXPR -> SAL_VALUE_EXPRS, SAL_VALUE_EXPRS, TYPE_EXPR)
  'rule' Gen_SAL_Index_Exprs(list(H,nil), Type -> list(SALExpr,nil), list(SAL_CC_Expr,nil), VT)
         Remove_Brackets(Type -> array(IT, VT))
         Gen_SAL_Expr(H, normal, IT -> SALExpr, SAL_CC_Expr)

  'rule' Gen_SAL_Index_Exprs(list(H,T), Type -> list(SAL_Expr, SALExprs), list(SAL_CC_Expr, SAL_CC_Exprs), TypeRes)
         Remove_Brackets(Type -> Type2)
         where(Type2 -> array(IT,VT))
         Gen_SAL_Expr(H, normal, IT -> SAL_Expr, SAL_CC_Expr)
         Gen_SAL_Index_Exprs(T, VT -> SALExprs, SAL_CC_Exprs, TypeRes)


'action' Gen_SAL_CC_Cmds_For_Arrays_Val_Exprs(VALUE_EXPRS, TYPE_EXPR, POS, SAL_variable_id, SAL_VALUE_EXPRS -> SAL_VALUE_EXPRS, POS)
  'rule' Gen_SAL_CC_Cmds_For_Arrays_Val_Exprs(nil, _, P, _, nil -> nil, P)

  'rule' Gen_SAL_CC_Cmds_For_Arrays_Val_Exprs(list(Expr,TExpr), Type, P, SALVarId, list(SAL_CC_Expr0, Tail) -> list(HRes,TRes), ResPos)
         Remove_Brackets(Type -> array(IT,VT))
         Gen_SAL_CC_Cmds_For_Arrays(Expr, IT, P, SALVarId, SAL_CC_Expr0 -> HRes, _)
         Gen_SAL_CC_Cmds_For_Arrays_Val_Exprs(TExpr, VT, P, SALVarId, Tail -> TRes, ResPos)

'action' Gen_SAL_CC_Cmds_For_Arrays(VALUE_EXPR, TYPE_EXPR, POS, SAL_variable_id, SAL_VALUE_EXPR -> SAL_VALUE_EXPR, POS)

  'rule' Gen_SAL_CC_Cmds_For_Arrays(Expr, TExpr, P, SALVarId, SAL_CC_Expr0 -> SAL_CC_Expr, ResPos)
	   Isin_subtype(Expr, TExpr -> Pred)
	   Simplify(Pred -> Pred1)
	   (|
	     ne(Pred1, no_val)
	     -- include subtype check in CC version
	     string_to_id("RSL_res_" -> ResId)
	     IncreaseCol(P -> ResPos)
	     New_value_id(ResPos, id_op(ResId) -> ResI)
	     Maxtype(TExpr -> MaxTExpr)
	     ResI'Type <- MaxTExpr
	     Isin_subtype(val_occ(P, ResI, nil), TExpr -> Pred2)
	     Simplify(Pred2 -> Pred3)
	     Gen_SAL_Expr(Pred3, normal, bool -> _, Cond)
	     Default_Bool_Tid -> BTid
	     BTid'Lifted_Tid -> tid(LBTid)
	     where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	     where(sal_esp_unary_prefix_occ(val_id(SAL_Op), Cond) -> IsTrueCond)
	     SALVarId'Ident -> Ident
	     id_to_string(Ident -> VarStr1)
	     PruneQuote(VarStr1 -> VarStr)
	     Concatenate("Update_to_variable_", VarStr -> Str1)
	     Concatenate(Str1, "_not_in_subtype" -> NavStr)
	     Extend_Nav_Type(P, NavStr -> NavId)
	     SAL_Gen_Type_Expr(P, TExpr -> _, CC_Type)
	     SAL_Generate_Result_for_Violation(CC_Type, sal_esp_value_occ(NavId) -> Else)
	     where(sal_named_val(id_op(id(ResId))) -> ResOcc)
	     where(sal_if_expr(IsTrueCond, ResOcc, nil, else(Else)) -> IF)
	     where(sal_let_expr(ResId, CC_Type, nil, nil, SAL_CC_Expr0, IF) -> SAL_CC_Expr)
	   ||
	     where(SAL_CC_Expr0 -> SAL_CC_Expr)
             where(P -> ResPos)
	   |)

-------------------------------------------------------------------------------------
-- LTL property processing
-------------------------------------------------------------------------------------
'action' SAL_Process_Property(Property_id, SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS -> 
					   SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Process_Property(Pid, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElements):
	 -- Access the resolved field:
	 Pid'Resolved_Prop -> Prop
	 where(Prop -> r_prop(Pos, Ident, TsId, Property))
	 -- Lookup the SAL_trans_id referred in the property:
	 TsId'Pos -> TsPos
	 look_up_TranSys_id(TsPos -> OptTsId)
	 (|
	     where(OptTsId -> ts(SAL_TSid))
	     -- Translate the Property:
	     Gen_SAL_Expr(Property, normal, bool -> Prop_Expr,_)
	     -- Generate the new SAL element:
	     where(assertion_decl(Pos, Ident, SAL_TSid, Prop_Expr) -> ContextElement)
	     -- Generate the result:
	     Insert_Context_Element(ContextElement, ContextElements -> ContextElementsout)
	 ||
	     Puterror(Pos)
	     Putmsg("Internal error: Internal Transition System descriptor not foud\n")
	     where(ContextElements -> ContextElementsout)
	 |)
	 -- The CC part just ignores the assertions. This is so because the cc version is only meant to
	 -- check the satisfaction of confidence conditions (not the user-defined assertions). For user-defined assertions,
	 -- the normal version is generated without any cc-checking (that is warrantied by the previous running of the cc-version
	 -- of the translation)

-------------------------------------------------------------------------
-- SAL_Process_Sort_Kind
-------------------------------------------------------------------------

'action' SAL_Process_Sort_Kind(POS, SORT_KIND, Type_id, SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS -> 
					       SAL_CONTEXT_CONSTANTS,  -- non-cc version 
					       SAL_CONTEXT_CONSTANTS)  -- cc version
  'rule' SAL_Process_Sort_Kind(P,abstract, Typeid, ContextElements, CC_Context_Elements -> ContextElementsout, CC_ContextElementsout):
	 Puterror(P)
	 Putmsg("Abstract type not supported\n")
	 
	 -- The rest is to allow further analysis of the code... (error recovery)
	 Typeid'Ident -> Ident
	 -- Collecting the type decl. in the global TABLE:
	 New_SAL_type_id(P, Ident, defined(Typeid, nil)  -> Tid)
	 -- Creating the basic type elem:
	 where(user_defined(sal_sort(Tid)) -> TypeElem)
	 -- Generate the arguments for the tid:
	 id_to_string(Ident -> SortName)
	 Concatenate(SortName, "_Card" -> Str)
	 string_to_id(Str -> SortCardId)
	 string_to_id("4" -> SortCardValId)
	 Generate_Global_Constant(SortCardId, SortCardValId, Tid -> SizeMacroArg)
	 where(SAL_VALUE_IDS'list(SizeMacroArg,nil) -> Args)
	 Update_Macro_in_Tid(Tid, Args)
	 -- Updating the Tid:
	 Tid'TExpr <- TypeElem
	 -- Generating ContextElement:
	 where(sal_type_decl(Ident,Tid,TypeElem) -> ContextElement)
	 -- Confidence condition handling...
	 -- No confidence condition here...
	 Tid'ConfidenceExpr <- no_val
	 -- Updating AST:
	 Insert_Context_Element(ContextElement, ContextElements -> ContextElementsout)
	 -- cc
	 -- This version should add, not only the non-lifted type definition but also the
	 -- declaration of the lifted type. The problem here is that the nav fields for the type are NOT
	 -- KNOWN YET (they will be discovered on the way while translating). The approach to solve this is
	 -- to just add the non lifted declaration only (in the cc AST) for the moment and to collect the variant
	 -- as they are 'generated ' (the navs). The lifted declaration will be included on the second pass...
	 Insert_Context_Element(ContextElement, CC_Context_Elements  -> CC_ContextElementsout)
	 -- Just to avoid errors:
	 Tid'Lifted_Tid -> tid(LTid)
	 SAL_Gen_CC_Ops_Context(any, LTid)

  'rule' SAL_Process_Sort_Kind(P,record(Components), Typeid, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsout):
	 SAL_Process_Record_Kind(Typeid, Components, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsout)
--Putmsg("Record elements:\n")
--SAL_Print_Constants(ContextElementsout)
--Putmsg("Record cc elements:\n")
--SAL_Print_Constants(CC_ContextElementsout)

  'rule' SAL_Process_Sort_Kind(P,variant(Variants), Typeid, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsout):
	 AllConstants(Variants)
	 SAL_Process_Variant_Kind_as_Scalar(Typeid, Variants, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsout)

  'rule' SAL_Process_Sort_Kind(P,variant(Variants), Typeid, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsout):
	 Typeid'Ident -> Ident
	 SAL_Process_Variant_Kind(Typeid, Variants, ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsout)
	     
  'rule' SAL_Process_Sort_Kind(P,union(Choices), Typeid, ContextElements, CC_ContextElements-> ContextElements, CC_ContextElements):
	 Puterror(P)
	 Putmsg("Union types not supported")
	 Putnl()

'condition' AllConstants(VARIANTS)

  'rule' AllConstants(list(record(_,con_ref(_),nil), VS)):
	 AllConstants(VS)

  'rule' AllConstants(nil):

--------------------------------------------------------------------
-- Abbreviations...
--------------------------------------------------------------------
'action' SAL_Process_abbrev(Type_id, TYPE_DEFINITION, SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Process_abbrev(Typeid, no_def, ContextElements, CC_ContextElements -> ContextElements, CC_ContextElements):
	 Typeid'Pos -> Pos
	 Puterror(Pos)
	 Putmsg("Abstract type declarations are not allowed (try to redefine as variants)\n")

	 -- Another approach can be to use the macro processor (m4) to expand automatically the abstract
	 -- type into a variant or enumeration. This approach, however, is not very useful because all
	 -- functions using the type (in arguments or results) will also be abstract and those are not translatable either.
	 -- Moreover, the values of the type will only be known in the the translated code (so it's impossible to refer to them
	 -- in the RSL specification).

-- special treatment for abbreviation definitions of subtypes
-- since in the CC version we need the cc subtype def, while the
-- normal treatment of subtypes in the cc version is to use the
-- maximal type
--  'rule' SAL_Process_abbrev(Typeid, abbreviation(TypeExpr),  ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsout):


  'rule' SAL_Process_abbrev(Typeid, abbreviation(TypeExpr),  ContextElements, CC_ContextElements -> ContextElementsout, CC_ContextElementsout):
	 Typeid'Ident -> Ident
	 Typeid'Pos -> Pos

	 New_SAL_type_id(Pos, Ident, defined(Typeid, nil)  -> Tid)
	 -- Generate the type elem for the right hand side:
	 SAL_Gen_Type_Expr(Pos, TypeExpr -> SALTypeElem, CC_Type)
	 -- Updating the Tid:
	 Tid'TExpr <- SALTypeElem
	 -- Creating the basic type elem:
	 where(user_defined(sal_abbrev(SALTypeElem)) -> TypeElem)
	 -- Generate SAL Context Element:
	 where(sal_type_decl(Ident,Tid,TypeElem) -> ContextElement1)

	 -- CC-generation
	 CCGenerate_type(TypeExpr, nil)
	 GetCcVar(-> Cc)
	 Gen_SAL_Expr(Cc, normal, bool -> _, SAL_Cc)
	 Tid'ConfidenceExpr <- SAL_Cc

	 -- Build result:
	 Insert_Context_Element(ContextElement1, ContextElements  -> ContextElementsout)
	 -- Trying this in the cc:
	 -- As abbreviations are the only way the user has to introduce named types
	 -- and we want to use maximal types only in the cc version, type declarations are generated in the cc
	 -- version only if the type expression associated with it is
	 -- different from integer:  cwg why integer?

	 (|
	     -- If the lifted type expression is a a type reference (sal_defined) it means that
	     -- this type is maximally equivalent to some other type. In this case, the type declaration
	     -- SHOULD BE REMOVED and the lifted type field in the non-lifted TID pointed to the referred TID.
             where(CC_Type -> user_defined(sal_cc_type(type_refs(sal_defined(_, _, Tid1)), _)))
	     Tid'Lifted_Tid -> tid(LTid)
	     ne(LTid, Tid1)
	     -- The lifted version of this type is the lifted int type:
	     -- cwg There is no reason to think this is just int -
	     -- seems to be subtypes in general
	 
	     Tid'Lifted_Tid <- tid(Tid1)
	     where(CC_ContextElements -> CC_ContextElementsout)
	 ||
	     -- Generating the type declaration if it doesn't match the Int type:
	     where(sal_type_decl(Ident,Tid,CC_Type) -> CC_ContextElement1)
	     Insert_Context_Element(CC_ContextElement1, CC_ContextElements  -> CC_ContextElementsout)
	 |)
	 Tid'Lifted_Tid -> tid(LTid1)
	 -- Generating the CC_OPS context:
	   SAL_Gen_CC_Ops_Context(TypeExpr, LTid1)




	 -- Checking if it is necessary to create the RSL_is_<abbrev-name> function
	 [|
	     Typeid'Subtype -> funct(Valueid)
	     Valueid'Def -> Definition
--Putmsg("Generating RSL_is_")
--Print_id(Ident)
--Putmsg("() : ")
--where(Definition -> expl_fun(_,Body1, _, _,_,_))
--Print_expr(Body1)
--Putnl()
	     SAL_Process_Value_id(Valueid, Definition, is_in_function, nil, nil 
					   -> _, Is_in_Function)
	     -- Collecting the translated is_in_funtion:
	     Collect_Is_Type_Function(Is_in_Function)
--print(Is_in_Function)
--Putmsg("Done generating the RSL_is function\n")
	 |]
--Putmsg("Context constants: ")
--SAL_Print_Constants(CC_ContextElementsout)	 

----------------------------------------------------------
-- VARIANTS....
----------------------------------------------------------

'action' SAL_Process_Variant_Kind(Type_id, VARIANTS, SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Process_Variant_Kind(Typeid, Variants, ContextElements, CC_ContextElements -> 
					  ContextElementsout, CC_ContextElementsout):
	 Typeid'Ident -> Ident
	 Typeid'Pos ->Pos
	 -- Collecting the type decl. in the global TABLE:
	 -- (Creating the tid first, to allow look-up in the variants constructors)
	 -- This is necessary because the variant constructor has
	 -- this type as return-type.
	 New_SAL_type_id(Pos, Ident, defined(Typeid, nil)  -> Tid)
	 -- Process the variant fields:

	 SAL_Process_Variants(Typeid, Variants, nil, nil, ContextElements, CC_ContextElements -> 
				      DataTypeParts, CC_DataTypeParts, ContextElements1, CC_ContextElements1)

	 -- Creating the basic type elem:
	 where(user_defined(sal_variant_type(DataTypeParts)) -> TypeElem)
	 -- Generate SAL Context Element:
	 where(sal_type_decl(Ident,Tid,TypeElem)-> ContextElement)
	 -- Updating the Tid:
	 Tid'TExpr <- TypeElem 
	 
	 -- Add the type declaration on top:	 
	 Insert_Context_Element(ContextElement, ContextElements1 -> ContextElementsout)

	 -- cc
	 Tid'Lifted_Tid -> tid(LTid)
	 -- Generating the CC_OPS context:
	 SAL_Gen_CC_Ops_Context(defined(Typeid, nil), LTid)

	 where(user_defined(sal_variant_type(CC_DataTypeParts)) -> CC_TypeElem)
	 -- Generate SAL Context Element:
	 where(sal_type_decl(Ident,Tid,CC_TypeElem)-> CC_ContextElement)
	 -- Generate the context constants:

	 -- This version should add, not only the non-lifted type definition but also the
	 -- declaration of the lifted type. The problem here is that the nav fields for the type are NOT
	 -- KNOWN YET (they will be discovered on the way while translating). The approach to solve this is
	 -- to just add the non lifted declaration only (in the cc AST) for the moment and to collect the variant
	 -- as they are 'generated ' (the navs). The lifted declaration will be included on the second pass...
	 Insert_Context_Element(CC_ContextElement, CC_ContextElements1  -> CC_ContextElementsout)

'action' SAL_Process_Variant_Kind_as_Scalar(Type_id, VARIANTS, SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Process_Variant_Kind_as_Scalar(Typeid, Variants, ContextElements, CC_ContextElements
                         -> ContextElementsout, CC_ContextElementsout):
	 Typeid'Ident -> Ident
	 Typeid'Pos ->Pos
	 -- Make a tid which will be the type of the scalar constants
	 New_SAL_type_id(Pos, Ident, defined(Typeid, nil)  -> Tid)
	 where(type_refs(sal_defined(Pos, Ident, Tid)) -> TExpr)
	 SAL_Process_Variants_as_Scalars(TExpr, Variants -> Ids, LIds)
	 where(user_defined(sal_scalar_type(Ids)) -> TypeElem)
	 Tid'TExpr <- TypeElem
	 where(sal_type_decl(Ident,Tid,TypeElem)-> ContextElement)
	 Insert_Context_Element(ContextElement, ContextElements ->
						ContextElementsout)
	 -- cc
	 Tid'Lifted_Tid -> tid(LTid)
	 -- Generating the CC_OPS context:
	 SAL_Gen_CC_Ops_Context(defined(Typeid, nil), LTid)
	 where(user_defined(sal_scalar_type(LIds)) -> CC_TypeElem)
	 -- Generate SAL Context Element:
	 where(sal_type_decl(Ident,Tid,CC_TypeElem)-> CC_ContextElement)
	 Insert_Context_Element(CC_ContextElement, CC_ContextElements  -> CC_ContextElementsout)

/* cwg seems not to be used
--------------------------------------------------------------------------------------
-- SAL_Gen_Functions_from_Reconstructors
--------------------------------------------------------------------------------------
-- This function generates the functions declarations that correspond
-- to the reconstructors in RSL. As SAL does not provide reconstructor
-- functionalities, this feature is translated into external (respect
-- to the type declaration) functions declarations with the proper
-- name.
--------------------------------------------------------------------------------------
'action' SAL_Gen_Functions_from_Reconstructors(POS,IDENT, SAL_type_id, SAL_TYPE_EXPR,TYPE_EXPR -> SAL_CONSTANT_DECLS, SAL_CONSTANT_DECLS)

  'rule' SAL_Gen_Functions_from_Reconstructors(Pos, Ident, Tid, TExpr,
				      ReconstructedType -> Decls, CC_Decls)
	 where(TExpr -> user_defined(sal_variant_type(DataTypeParts)))
	 -- Generate the type expression that will be the result of
	 -- the reconstructor function:
	 SAL_Gen_Type_Expr(Pos, ReconstructedType -> TExpr1, CC_TE)
--	 where(type_refs(sal_defined(Pos, Ident, Tid)) -> TExpr1)

	 SAL_Gen_Functions_from_Reconstructors1(ReconstructedType,TExpr1, CC_TE, DataTypeParts -> Decls, CC_Decls)


'action' SAL_Gen_Functions_from_Reconstructors1(TYPE_EXPR, SAL_TYPE_EXPR, SAL_TYPE_EXPR,
		SAL_DATA_TYPE_PARTS -> SAL_CONSTANT_DECLS, SAL_CONSTANT_DECLS)

  'rule' SAL_Gen_Functions_from_Reconstructors1(ReconstructedType, TExpr, CC_TE, list(H, T) ->  Decls, CC_Decls)
	 SAL_Gen_Functions_from_Reconstructors1(ReconstructedType,TExpr, CC_TE, T -> Decls2, CC_Decls2)
	 where(H -> sal_part(Const, _))
	 where(Const -> sal_construc(_, Vid, _, Reconstructors))
	 SAL_Gen_Functions_from_Reconstructors2(ReconstructedType,
				TExpr, CC_TE, Const, Vid, Reconstructors -> Decls1, CC_Decls1)
	 SAL_Concatenate_Decls(Decls1, Decls2 -> Decls)
	 -- cc
	 SAL_Concatenate_Decls(CC_Decls1, CC_Decls2 -> CC_Decls)

  'rule' SAL_Gen_Functions_from_Reconstructors1(_,_, _, nil -> nil, nil)

'action' SAL_Gen_Functions_from_Reconstructors2(TYPE_EXPR, SAL_TYPE_EXPR, SAL_TYPE_EXPR, 
	   SAL_CONSTRUCTOR, SAL_value_id, SAL_RECONSTRUCTORS -> SAL_CONSTANT_DECLS, SAL_CONSTANT_DECLS)

  'rule' SAL_Gen_Functions_from_Reconstructors2(ReconstructedType,TExpr, CC_TE, Const, Vid, list(H,T) -> Decls, CC_Decls)
	 SAL_Gen_Function_from_Reconstructor(ReconstructedType,TExpr, CC_TE, Const, Vid, H -> Decl, CC_Decl)
	 SAL_Gen_Functions_from_Reconstructors2(ReconstructedType,TExpr, CC_TE, Const, Vid, T -> Decls1, CC_Decls1)
	 where(SAL_CONSTANT_DECLS'list(Decl, Decls1) -> Decls)
	 Vid'Declaration <- sal_const_decl(Decl)
	 --cc
	 where(SAL_CONSTANT_DECLS'list(CC_Decl, CC_Decls1) -> CC_Decls)
	 Vid'Lifted_Vid -> LVid
	 LVid'Declaration <- sal_const_decl(CC_Decl)

  'rule' SAL_Gen_Functions_from_Reconstructors2(_,_,_,_,_,nil -> nil, nil)

'action' SAL_Gen_Function_from_Reconstructor(TYPE_EXPR, SAL_TYPE_EXPR, SAL_TYPE_EXPR,
	   SAL_CONSTRUCTOR, SAL_value_id, SAL_RECONSTRUCTOR -> SAL_CONSTANT_DECL, SAL_CONSTANT_DECL)

  'rule' SAL_Gen_Function_from_Reconstructor(ReconstructedType, TExpr, LTExpr, Constructor, Vid, 
	   sal_reconstructor(IdOp, Vid1, ReconstrType,  ReconstructorType, AccesorPos) -> Decl, CC_Decl)
	 -- Generate the params:
	 -- Only two args:
	 -- 1) The proper field (the field whose value is going to change)
	 SAL_Gen_Param_Ident(-> IdentParam1)
	 where(formal_param(IdentParam1, ReconstrType, ReconstructorType) -> Param1)
	 -- 2) The comprised type
	 SAL_Gen_Param_Ident(-> IdentParam2)
	 
	 where(formal_param(IdentParam2, TExpr, ReconstructedType) -> Param2)
	 -- Generating the arg list:
	 where(SAL_FORMAL_FUN_PARAMETERS'list(Param1, list(Param2, nil)) -> Params)

	 -- Updating the arguments in the vid:
	 Vid1'Params <- Params

	 -- Generate the Namespace
	 -- The namespace must be nil in this case (no bindings introduced)
	 where(BINDING_NAMESPACE'nil -> Namespace)
	 -- Generate the Body
	 -- Generate the arguments:
	 where(Constructor -> sal_construc(_, _, Accesors,_))
	 SAL_Gen_Recons_Actual_Params(Accesors,AccesorPos,IdentParam1,IdentParam2 -> ArgExprs, CC_Args)

	 DefaultPos(->P)	 
	 where(sal_argument(ArgExprs) -> Args)
	 -- Generating the AST for the constructor ident:
	 where(sal_esp_value_occ(Vid) -> VariantConstructor)
	 -- function application (constructor of the variant)
	 where(sal_funct_applic(VariantConstructor, Args) -> Body)

	 where(sal_fun_const(IdOp, Vid1, nil, Params, TExpr, Namespace,
				   Body,nil) -> Decl)
	 -- cc
	 SAL_Gen_Type_Expr(P, ReconstructorType -> _, LReconstrType)
	 where(formal_param(IdentParam1, LReconstrType, ReconstructorType) -> LParam1)
	 where(formal_param(IdentParam2, LTExpr, ReconstructedType) -> LParam2)
	 -- Generating the arg list:
	 where(SAL_FORMAL_FUN_PARAMETERS'list(LParam1, list(LParam2, nil)) -> LParams)
	 -- Updating the arguments in the vid:
	 Vid1'Lifted_Vid -> LVid1
	 LVid1'Params <- LParams
	 
	 where(sal_argument(CC_Args) -> CC_Arguments)
	 -- Generating the AST for the constructor ident:
	 Vid'Lifted_Vid -> LVid
	 where(sal_esp_value_occ(LVid) -> LVariantConstructor)
	 -- function application (constructor of the variant)
	 where(sal_funct_applic(LVariantConstructor, CC_Arguments) -> CC_Body)


	 -- Lift the type:
	 Select_CC_Result_Type(LTExpr -> SelectedTid)
	 where(IdOp -> id(Ident1))
	 id_to_string(Ident1 -> IdStr)
	 SAL_Current_Cid -> Cid
	 Cid'Ident -> CidId
	 id_to_string(CidId -> CidIdStr)
	 Concatenate3(CidIdStr, "_", IdStr -> NameStr) 
	 -- Adding a new value for the type WFC checking
	 -- (the body of the function will be modified afterwards (on a separate pass)
	 --  when all the lifting is done)...
	 Concatenate("Argument_of_function_", NameStr -> WFCStr1)
	 Concatenate(WFCStr1, "_not_in_subtype" -> WFCStr)
	 -- Extending the lifted type with the proper constructor:
	 Vid1'Pos -> Pos
	 IncreaseCol(Pos -> IncPos)
	 Extend_Nav_Type(IncPos, WFCStr -> WFC_Vid)
	 where(sal_fun_const(IdOp, LVid1, nil, LParams, LTExpr, Namespace, CC_Body, vid(WFC_Vid)) -> CC_Decl)

'action' SAL_Gen_Recons_Actual_Params(SAL_DESTRUCTORS,POS, IDENT, IDENT  -> SAL_VALUE_EXPRS, SAL_VALUE_EXPRS)

  'rule' SAL_Gen_Recons_Actual_Params(
	  list(sal_destructor(IdOp, Vid, TElem,_),Rest), Pos, FieldIdent, TypeIdent -> Args, CC_Args)
	 Vid'Pos -> AccesorPos
	 (|
	    -- The accesor matches the field modified by the reconstructor:
	    eq(AccesorPos, Pos)
	    -- This is generated value_id, there is no real position
	    -- assoc. with it
	    DefaultPos(->P)
	    where(SAL_ID_OP'id(FieldIdent) -> FieldNewVal)
	    where(SAL_VALUE_ID'val_id(FieldNewVal) -> Value_occ)
	    where(sal_value_occ(Value_occ,nil) -> Arg)
	    -- this is the same in the cc version:
	    where(Arg -> CC_Arg)
	 ||
	    -- This is a field not modified by the reconstructor...
	    -- A proper destructor must be generated... (as a function app)
	    where(sal_esp_value_occ(Vid) -> VariantDestructor)
	    DefaultPos(->P)
	    where(SAL_ID_OP'id(TypeIdent) -> TypeName)
	    where(SAL_VALUE_ID'val_id(TypeName) -> TypeName_occ)
	    where(sal_value_occ(TypeName_occ,nil) -> Arg1)
	    where(sal_argument(SAL_VALUE_EXPRS'list(Arg1, nil)) -> Args)
	    where(sal_funct_applic(VariantDestructor, Args) -> Arg)
	    -- The destructor here is not the same (we want the lifted version of it)
	    Vid'Lifted_Vid -> LVid
	    where(sal_esp_value_occ(LVid) -> LVariantDestructor)
	    where(sal_funct_applic(LVariantDestructor, Args) -> CC_Arg)
	 |)
	 SAL_Gen_Recons_Actual_Params(Rest, Pos, FieldIdent, TypeIdent -> Args1, CC_Args1)
	 where(SAL_VALUE_EXPRS'list(Arg,Args1) -> Args)
	 --cc
	 where(SAL_VALUE_EXPRS'list(CC_Arg,CC_Args1) -> CC_Args)

  'rule' SAL_Gen_Recons_Actual_Params(nil,_,_,_ -> nil, nil)
cwg end of SAL_Gen_Reconstructors */
--------------------------------------------------------------------------------------
-- SAL_Gen_Context_Constants
--------------------------------------------------------------------------------------
-- This function converts a list of constant declarations (like a list
-- of functions) into a list of context constants (i.e. a list of
-- functions DECLARATIONS valid to be included in a context)
--------------------------------------------------------------------------------------

'action' SAL_Gen_Context_Constants(SAL_CONSTANT_DECLS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Gen_Context_Constants(list(Decl, Rest) -> Result):
	 SAL_Gen_Context_Constants(Rest -> Result1)
	 where(sal_const_decl(Decl) -> Constant)
	 where(SAL_CONTEXT_CONSTANTS'list(Constant, Result1) -> Result)

  'rule' SAL_Gen_Context_Constants(nil -> nil)

--------------------------------------------------------------------------------------
-- Variant fields processing:
--------------------------------------------------------------------------------------

'action' SAL_Process_Variants(Type_id, VARIANTS, SAL_DATA_TYPE_PARTS, SAL_DATA_TYPE_PARTS, SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS
				        -> SAL_DATA_TYPE_PARTS, SAL_DATA_TYPE_PARTS, SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Process_Variants(Typeid, list(record(Pos, con_ref(Valueid), nil),
               VariantsTail), DataTypeParts, CC_DataTypeParts, Elems, CC_Elems -> DataTypePartsout, CC_DataParts, ElemsOut, CC_ElemsOut):
-- treat like  scalar variant, but with a CC recogniser
   	 Valueid'Pos -> Pos2
	 Valueid'Ident -> IdorOp
	 SAL_TYPES_Cid -> Cid
	 Gen_SAL_Id_Op(Pos2, IdorOp, none, none -> IdOp, _)
	 Valueid'Type -> TypeExpr
	 SAL_Gen_Type_Expr(Pos, TypeExpr -> TElem, CC_Type)
	 New_SAL_value_id(Pos2, IdOp, Cid, TElem, constructor_value -> Vid)
	 Vid'Lifted_Vid -> LVid
	 LVid'Cid <- cid(Cid)
	 -- generate the CC recogniser
	 where(IdorOp -> id_op(Ident))  -- check for op ? TODO
	 id_to_string(Ident -> Str)
	 Concatenate(Str,"?" -> Str2)
	 string_to_id(Str2 -> Identq)
	 where(SAL_ID_OP'id(Identq) -> IdOpq)
	 SAL_Gen_Param_Ident(-> TestParamIdent)
	 where(TYPE_EXPR'defined(Typeid, nil) -> T)
	 Typeid'Pos -> TPos
	 SAL_Gen_Type_Expr(TPos, T -> _, T_CC_Type)
	 where(formal_param(TestParamIdent, T_CC_Type, T) -> TestParam) 
	 where(SAL_FORMAL_FUN_PARAMETERS'list(TestParam, nil)-> TestParams)
	 where(T_CC_Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 Tid'Constructor -> vid(Const)
	 Tid'Lifted_fields -> Fields
	 SAL_Find_Accesor_in_Fields(Fields, Const -> AccVid)
	 where(sal_funct_applic(sal_esp_value_occ(AccVid),
				sal_argument(list(sal_value_occ(val_id(id(TestParamIdent)),nil), nil)))
	       -> TestExpr0)
	 -- TestExpr0 is now T_val(x_)
	 DefaultPos(-> P)
	 SAL_Gen_Type_Expr(P, bool -> Bool, CCBool)
	 -- CWG 13/4/08
	 IncreaseCol(P -> P1)
	 SAL_TYPES_Cid -> STCid
	 New_SAL_value_id(P1, IdOpq, STCid, Bool, regular_value -> Vid1)
	 where(sal_funct_applic(sal_esp_value_occ(Vid1),
				sal_argument(list(TestExpr0, nil)))
	       -> TestExpr1)
	 -- TestExpr1 is now SAL_TYPES!Ident?(T_val(x_))
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LiftedBTid)
	 LiftedBTid'Constructor -> vid(ConstVid)
	 where(sal_funct_applic(sal_esp_value_occ(ConstVid),
				sal_argument(list(TestExpr1, nil)))
	       -> TestExpr)
	 -- TestExpr is now Bool__cc(Ident?(T_val(x_)))
	 SAL_Current_CC_Cid -> CC_Cid
	 New_SAL_value_id(P, IdOpq,CC_Cid,CCBool,regular_value -> TestVid)
	 TestVid'Params <- TestParams
	 TestVid'Lifted_Vid <- TestVid
	 where(sal_const_decl(sal_fun_const(IdOpq, TestVid, nil,
	  TestParams, CCBool,  nil, TestExpr, nil)) -> TestContextElement)
	 where(SAL_CONTEXT_CONSTANTS'list(TestContextElement, nil)
				      -> TestContextElements)
	 -- add to constructors, which are defined before
	 -- reconstructors, where it will be used
	 Collect_Lifted_Constructor(TestContextElements)

	 where(sal_construc(IdOp, Vid, nil, nil) -> SALConstructor)
	 where(sal_part(SALConstructor, nil) -> DataTypePart)
	 SAL_Insert_DataTypePart(DataTypePart, DataTypeParts -> DataTypeParts1)
	 SAL_Process_Variants(Typeid, VariantsTail, DataTypeParts1, CC_DataTypeParts, Elems, CC_Elems
	                  -> DataTypePartsout, CC_DataParts, ElemsOut, CC_ElemsOut)

  'rule' SAL_Process_Variants(Typeid, list(record(Pos, con_ref(Valueid), Components),
               VariantsTail), DataTypeParts, CC_DataTypeParts, Elems, CC_Elems -> DataTypePartsout, CC_DataParts, ElemsOut, CC_ElemsOut):
         Valueid'Pos -> Pos2
         Valueid'Ident -> IdorOp
	 -- Generating the type of the constructor:
	 Valueid'Type -> TypeExpr

	 SAL_Gen_Type_Expr(Pos, TypeExpr -> TElem, CC_Type)
	 -- Obtaining the Cid:
	 SAL_Current_Cid -> Cid
	 -- Generate the value-id
	 IncreaseCol(Pos2 -> NewPos2)
	 where(IdorOp -> id_op(Ident))  -- check for op ? TODO
	 id_to_string(Ident -> Str)
	 where(SAL_ID_OP'id(Ident) -> IdOp)

	 -- This is the value Id for the CONSTRUCTOR of the variant...
	 -- The lifted version of it will be replaced later with the proper
	 -- lifted version...
	 -- It is created with a fake position for the moment to do the trick below...
	 -- The proper position will be restored after the trick...
	 New_SAL_value_id(NewPos2, IdOp, Cid, TElem, constructor_value -> Vid)
	 Vid'Lifted_Vid -> LiftedBaseVid
	 LiftedBaseVid'IdOp <- IdOp
	 -- The increased position is used for the moment to produce a match 
	 -- with the fake constructor introduced below...


	 -- Generating the new constructor for the lifted version (this will have the checkings for the lifted type system)
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(Pos2, VE -> value_id(I1))
	[|
	   -- This is a fake constructor that is used in the cc version to refer to the non-lifted constructor
	   -- On an ocurrence of this vid (also fakely created below) it will match (temporarly) with the Vid created above
	   -- (by position)
	   New_value_id(NewPos2, id_op(Ident) -> Non_CC_RSL_Vid)
	   -- Faking the information (from the real one)
	   I1'Def -> Definition
	   Non_CC_RSL_Vid'Def <- Definition
	   I1'Qualifier -> Qualif
	   Non_CC_RSL_Vid'Qualifier <- Qualif
	   I1'Type -> TE1
	   Non_CC_RSL_Vid'Type <- TE1
	   where(Definition -> expl_fun(Parms, Body, Post, Pre, SA, SR))
	   -- Doing another trick here...
	   -- We are about to turn the formal parameters from the mk_ function
	   -- into actual parameter to... itself!
	   -- In this way, the function in the definition of the value_id will be:
	   -- Ident : T1 >< T2 ><.....>< Tn -> Tx
	   -- Ident(arg1, arg2,...., argn) is
	   --    Ident(arg1, arg2,...,argn)
	   SAL_Turn_Formals_to_Actuals(Parms -> ActualParams)
	   Gen_SALFormal_Parameters(Parms, TE1 -> SAL_Params,_, SAL_CC_Params)
	   Vid'Params <- SAL_Params
	   -- generating the application:
	   DefaultPos(-> P)
	   where(application(P, val_occ(P, Non_CC_RSL_Vid, nil), ActualParams) -> NewBody)
	   where(expl_fun(Parms, NewBody, Post, Pre, SA, SR) -> ModifiedDef)
	   I1'Def <- ModifiedDef
	   SAL_Process_Value_id(I1,ModifiedDef,cc_mk_function, nil, nil -> _, LiftedConstructor)
	   -- Un-doing the trick:
	   I1'Def <- Definition
           -- I1'Pos <- SavedPos
	   -- Setting up the proper lifted constructor
	   look_up_value_id(Pos2 -> vid(Mk_Fake_Vid))
	   Mk_Fake_Vid'Pos <- NewPos2
	   Mk_Fake_Vid'Lifted_Vid -> LiftedVid1
	   -- Now I want the system to use the lifted constructor every time the normal constructor is invoked,
	   -- so I link them, loosing the relationship with the fake one that is no needed anymore (the fake
	   -- constructor mk_<Id>_ is only used inside the body of the lifted constructor).
	   Vid'Lifted_Vid <- LiftedVid1
	   LiftedVid1'Params <- SAL_CC_Params
	   -- Removing the fake from the global collection (I don't want it anymore)
	   SAL_Remove_Vid_from_Globals(Mk_Fake_Vid)

	   -- Collecting the constructor:
	   Collect_Lifted_Constructor(LiftedConstructor)

	   -- we also need to define, where T is the variant type
	   -- Ident?(x_ : T): Bool__cc = Bool__cc(SAL_TYPES!Ident?(T_val(x_)))
	   Concatenate(Str,"?" -> Str2)
	   string_to_id(Str2 -> Identq)
	   where(SAL_ID_OP'id(Identq) -> IdOpq)
	   SAL_Gen_Param_Ident(-> TestParamIdent)
	   where(TYPE_EXPR'defined(Typeid, nil) -> T)
	   Typeid'Pos -> TPos
	   SAL_Gen_Type_Expr(TPos, T -> _, T_CC_Type)
	   where(formal_param(TestParamIdent, T_CC_Type, T) -> TestParam) 
	   where(SAL_FORMAL_FUN_PARAMETERS'list(TestParam, nil)-> TestParams)
	   where(T_CC_Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	   Tid'Constructor -> vid(Const)
	   Tid'Lifted_fields -> Fields
	   SAL_Find_Accesor_in_Fields(Fields, Const -> AccVid)
	   where(sal_funct_applic(sal_esp_value_occ(AccVid),
				  sal_argument(list(sal_value_occ(val_id(id(TestParamIdent)),nil), nil)))
	   	 -> TestExpr0)
	   -- TestExpr0 is now T_val(x_)
	   SAL_Gen_Type_Expr(P, bool -> Bool, CCBool)
	   -- CWG 13/4/08
	   IncreaseCol(P -> P1)
	   SAL_TYPES_Cid -> STCid
	   New_SAL_value_id(P1, IdOpq, STCid, Bool, regular_value -> Vid1)
	   where(sal_funct_applic(sal_esp_value_occ(Vid1),
				  sal_argument(list(TestExpr0, nil)))
	   	 -> TestExpr1)
	   -- TestExpr1 is now SAL_TYPES!Ident?(T_val(x_))
	   Default_Bool_Tid -> BTid
	   BTid'Lifted_Tid -> tid(LiftedBTid)
	   LiftedBTid'Constructor -> vid(ConstVid)
	   where(sal_funct_applic(sal_esp_value_occ(ConstVid),
				  sal_argument(list(TestExpr1, nil)))
		 -> TestExpr)
	   -- TestExpr is now Bool__cc(Ident?(T_val(x_)))
	   SAL_Current_CC_Cid -> CC_Cid
	   New_SAL_value_id(P, IdOpq,CC_Cid,CCBool,regular_value -> TestVid)
	   TestVid'Params <- TestParams
	   TestVid'Lifted_Vid <- TestVid
	   where(sal_const_decl(sal_fun_const(IdOpq, TestVid, nil,
	    TestParams, CCBool,  nil, TestExpr, nil)) -> TestContextElement)
	   where(SAL_CONTEXT_CONSTANTS'list(TestContextElement, nil)
	   				-> TestContextElements)
	   -- add to constructors, which are defined before
	   -- reconstructors, where it will be used
	   Collect_Lifted_Constructor(TestContextElements)
       |]

       -- Restoring the position in the vid for the non-lifted version:  
       Vid'Pos <- Pos2
 
       Vid'Lifted_Vid -> LVid

         SAL_Generate_Destructors(Components, nil,nil, nil,nil, Elems, CC_Elems -> Destructors, Reconstructors, CC_Destr, CC_Recons, Elems1, CC_Elems1)
--Putmsg("Variant reconstructors:\n")
--SAL_Print_Reconstructors(Reconstructors)

	 -- Add the reconstructors below ...
	 where(sal_construc(IdOp, Vid, Destructors,Reconstructors) -> SALConstructor)
	 where(sal_part(SALConstructor, nil) -> DataTypePart)

	 -- We are not adding the Reconstructors here... 
	 -- This is done in this way because this is the variant part of the non-lifted version of the variant 
	 -- in the cc version. For example:
	 -- Harbour :: 
	 --	 pool : T.Ship-set <-> update_pool 
	 --      berths : T.Index -m-> T.Ship <-> update_berths 
	 -- In the cc-version will be translated as:
	 -- Harbour : TYPE = DATATYPE
	 --	 mk_harbour(pool : Maximal(Ship)-set, berth: Maximal(Index)-m->Maximal(Ship))
	 -- And a cc declaration of the form:
	 -- Harbour_cc : TYPE = DATATYPE 
	 --      Harbour_cc(val : Harbour),
	 --	 Harbour_cc_nav(nav_val: Not_a_value_type)
	 -- Then, the reconstructor will refer to the <Harbour_cc> type, not to the <Harbour> one
	 -- That's why no reconstructor is added here.
	 -- If added, this breaks the type closure (fixed point) algorithm:
	 -- This happens because Harbour -> reconstructor - (by definition on the cc version) -> Harbour_cc ->
	 -- - (by lifting)    -> Harbour ===> CIRCULAR DEPENDENCY!
	 
	 where(sal_construc(IdOp, LiftedBaseVid, CC_Destr, CC_Recons) -> SAL_CC_Constructor)
	 -- cwg CC_Recons replaced to fix problem in calculating fixed points
	 -- The problem described above is dealt with by removing
	 -- reconstructors from the fixed point calculation
	 -- of non-lifted types
	 where(sal_part(SAL_CC_Constructor, nil) -> CC_DataTypePart)


	 SAL_Insert_DataTypePart(DataTypePart, DataTypeParts -> DataTypeParts1)
	 SAL_Insert_DataTypePart(CC_DataTypePart, CC_DataTypeParts -> CC_DataTypeParts1)
	 SAL_Process_Variants(Typeid, VariantsTail, DataTypeParts1, CC_DataTypeParts1, Elems1, CC_Elems1
	                  -> DataTypePartsout, CC_DataParts, ElemsOut, CC_ElemsOut)



  'rule' SAL_Process_Variants(Typeid, list(record(Pos, wildcard, _), VariantsTail),
					   DataTypeParts, CC_DataTypeParts, Elems, CC_Elems -> DataTypePartsout, CC_DataParts, Elems1, CC_Elems1)
         Puterror(Pos)
	 Putmsg("Wildcard variants not supported")
	 Putnl() -- cwg
	 SAL_Process_Variants(Typeid, VariantsTail, DataTypeParts, CC_DataTypeParts, Elems, CC_Elems -> 
				      DataTypePartsout, CC_DataParts, Elems1, CC_Elems1)

  'rule' SAL_Process_Variants(Typeid, nil, DataTypeParts, CC_DataTypeParts, Elems1, CC_Elems1 -> DataTypeParts, CC_DataTypeParts, Elems1, CC_Elems1):

'action' SAL_Process_Variants_as_Scalars(SAL_TYPE_EXPR, VARIANTS ->
						 SAL_VALUE_IDS, SAL_VALUE_IDS)
  'rule' SAL_Process_Variants_as_Scalars(TElem,
					 list(record(Pos,con_ref(Valueid),_), VS)
					 -> list(Vid, Ids), list(LVid, LIds)):
	 Valueid'Pos -> Pos2
	 Valueid'Ident -> IdorOp
	 -- Obtaining the Cid:
	 -- Enumerated types are defined in SAL_TYPES:
	 SAL_TYPES_Cid -> Cid
--Putmsg("Current context: ")
--Cid'Ident -> Idc
--Print_id(Idc)
--Putnl
	 Gen_SAL_Id_Op(Pos2, IdorOp, none, none -> IdOp, _)
	 New_SAL_value_id(Pos2, IdOp, Cid, TElem, constructor_value -> Vid)
	 Vid'Lifted_Vid -> LVid
	 -- lifted Vid is not actually defined - so make its Cid also SAL_TYPES
	 LVid'Cid <- cid(Cid)
--SAL_Print_Vid(Vid)
--Putnl()
--SAL_Print_Vid(LVid)
--Putnl()


	 SAL_Process_Variants_as_Scalars(TElem, VS -> Ids, LIds)

  'rule' SAL_Process_Variants_as_Scalars(_, nil -> nil, nil):

--------------------------------------------------------------------------------
-- SAL_Generate_Formals_from_Destructors
--------------------------------------------------------------------------------
-- Generating the formal parameters for the constructors...
-- It is necessary because they will be invoked as FUNCTIONS in SAL
-- and, due to the difference in the bindings, the actual list of arguments
-- is needed in order to allow the proper conversion of bindings when an application is found
---------------------------------------------------------------------------------
'action' SAL_Generate_Formals_from_Destructors(COMPONENTS ->
						SAL_FORMAL_FUN_PARAMETERS)

  'rule' SAL_Generate_Formals_from_Destructors(list(component(Pos,Destructor,OT,_), Rest) -> list(formal_param(Ident, TE,OT), Result))
         (|
	     where(Destructor -> destructor(_,IdOp))
	 ||
	     where(Destructor -> dest_ref(VId))
	     VId'Ident -> IdOp
	 |)
	 where(IdOp -> id_op(Ident))
	 SAL_Gen_Type_Expr(Pos, OT -> TE, _)
	 SAL_Generate_Formals_from_Destructors(Rest -> Result)

  'rule' SAL_Generate_Formals_from_Destructors(nil -> nil)

  'rule' SAL_Generate_Formals_from_Destructors(T -> nil)
	 Putmsg("Debugging predicate activated in 'SAL_Generate_Formals_from_Destructors'\n")

---------------------------------------------------------------------------------
-- SAL_Process_Record_Kind
----------------------------------------------------------------------------------
-- Records are converted to variants and processed in that way...
----------------------------------------------------------------------------------

'action' SAL_Process_Record_Kind(Type_id, COMPONENTS, SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS  
		      -> SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Process_Record_Kind(Typeid, Components, ContextElements, CC_ContextElements
                                              -> ContextElementsout, CC_ContextElementsOut):
	 -- Record's name:
	 Typeid'Ident -> Ident
	 Typeid'Pos-> Pos

--Putmsg("About to start record1\n")
--Global_Tid_Table -> Y
--print(Y)
	 IncreaseCol(Pos -> NewPos1)
	 -- Generating the tid...
	 -- Again, it is necessary to generate it before processing
	 -- the fields (the constructors has references to the record
	 -- type that contains them)
	 New_SAL_type_id(Pos, Ident, defined(Typeid,nil)  -> Tid)

--Putmsg("About to start record2\n")
--Global_Tid_Table -> X
--print(X)


	 -- Generating the type of the constructor (reference to this record type)
	 SAL_Gen_Type_Expr(Pos, defined(Typeid,nil) -> TElem, CC_Type)

	 -- Obtaining the Cid:
	 SAL_Current_Cid -> Cid

	 -- Creating the mk_<type_name> constructor (used to name the proper field in the variant)
	 id_to_string(Ident -> Str)
	 Concatenate("mk_",Str -> Str0)
	 Concatenate(Str0,"_" -> Str1)
	 string_to_id(Str0 -> Mk_ident)
	 where(SAL_ID_OP'id(Mk_ident) -> IdOp)

	 -- This is the value Id for the CONSTRUCTOR of the RECORD...
	 -- The lifted version of it will be replaced later with the proper
	 -- lifted version...
	 -- It is created with a fake position for the moment to do the trick below...
	 -- The proper position will be restored after the trick...
	 New_SAL_value_id(NewPos1, IdOp, Cid, TElem, constructor_value -> Vid)
	 Vid'Lifted_Vid -> LiftedBaseVid
	 LiftedBaseVid'IdOp <- IdOp
	 -- The increased position is used for the moment to produce a match 
	 -- with the fake constructor introduced below...


	 -- Generating the new mk_<...> for the lifted version (this will have the checkings for the lifted type system)
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(Pos, VE -> value_id(I1))
	[|
	   -- This is a fake constructor that is used in the cc version to refer to the non-lifted constructor
	   -- for the record (mk_<TypeName>_)
	   -- On an ocurrence of this vid (also fakely created below) it will match (temporarly) with the Vid created above
	   -- (by position)
	   New_value_id(NewPos1, id_op(Mk_ident) -> Non_CC_RSL_Vid)
	   -- Faking the information (from the real one)
	   I1'Def -> Definition
	   Non_CC_RSL_Vid'Def <- Definition
	   I1'Qualifier -> Qualif
	   Non_CC_RSL_Vid'Qualifier <- Qualif
	   I1'Type -> TE1
	   Non_CC_RSL_Vid'Type <- TE1
	   where(Definition -> expl_fun(Parms, Body, Post, Pre, SA, SR))
	   -- Doing another trick here...
	   -- We are about to turn the formal parameters from the mk_ function
	   -- into actual parameter to... itself!
	   -- In this way, the function in the definition of the value_id will be:
	   -- mk_<id> : T1 >< T2 ><.....>< Tn -> Tx
	   -- mk_<id>(arg1, arg2,...., argn) is
	   --    mk_<id>(arg1, arg2,...,argn)
	   SAL_Turn_Formals_to_Actuals(Parms -> ActualParams)
	   Gen_SALFormal_Parameters(Parms, TE1 -> SAL_Params,_, SAL_CC_Params)
	   Vid'Params <- SAL_Params
	   -- generating the application:
	   DefaultPos(-> P)
	   where(application(P, val_occ(P, Non_CC_RSL_Vid, nil), ActualParams) -> NewBody)

	   where(expl_fun(Parms, NewBody, Post, Pre, SA, SR) -> ModifiedDef)
	   I1'Def <- ModifiedDef

	   SAL_Process_Value_id(I1,ModifiedDef,cc_mk_function, nil, nil -> _, LiftedConstructor)
	   -- Un-doing the trick:
	   I1'Def <- Definition
           -- I1'Pos <- SavedPos
	   -- Setting up the proper lifted mk_function
	   look_up_value_id(Pos -> vid(Mk_Fake_Vid))
	   Mk_Fake_Vid'Pos <- NewPos1
	   Mk_Fake_Vid'Lifted_Vid -> LiftedVid1
	   -- Now I want the system to use the lifted constructor every tyme the normal constructor is invoked,
	   -- so I link them, loosing the relationship with the fake one that is no needed anymore (the fake
	   -- constructor mk_<id> is only used inside the body of the lifted constructor).
	   Vid'Lifted_Vid <- LiftedVid1
	   LiftedVid1'Params <- SAL_CC_Params
	   -- Removing the fake from the global collection (I don't want it anymore)
	   SAL_Remove_Vid_from_Globals(Mk_Fake_Vid)

	   -- Collecting the constructor:
	   Collect_Lifted_Constructor(LiftedConstructor)
       |]

       -- Restoring the position in the vid for the non-lifted version:  
       Vid'Pos <- Pos
 
       Vid'Lifted_Vid -> LVid
       SAL_Generate_Destructors(Components, nil,nil,nil,nil,ContextElements, CC_ContextElements
	          -> Destructors, Reconstructors, CC_Destructors, CC_Recons, ContextElements1, CC_ContextElements1)
--Putmsg("Record reconstructors:\n")
--SAL_Print_Reconstructors(Reconstructors)
       -- Add the reconstructors below ...
       where(sal_construc(IdOp, Vid, Destructors,Reconstructors) -> SALConstructor)
	 
       where(sal_part(SALConstructor, nil) -> DataTypePart)
	 

       -- Creating the basic type elem:
       where(user_defined(sal_variant_type(list(DataTypePart,nil))) -> TypeElem)
       -- Generate SAL Context Element:
       where(sal_type_decl(Ident,Tid,TypeElem)-> ContextElement)
       -- Updating the Tid:
  
	 
       -- Add the type declaration on top:
       Insert_Context_Element(ContextElement, ContextElements1 -> ContextElementsout)

	 -- cc
	 -- Generate SAL Context Element:
	 --  The Tid below MUST be the NON-LIFTED ONE! This is so because for records and variants,
	 -- the non-lifted definition (maybe modified for maximality) is also needed (in order to have
	 -- something to lift afterwards).

	 -- We are not adding the Reconstructors here... 
	 -- This is done in this way because this is the variant part of the non-lifted version of the variant 
	 -- in the cc version. For example:
	 -- Harbour :: 
	 --	 pool : T.Ship-set <-> update_pool 
	 --      berths : T.Index -m-> T.Ship <-> update_berths 
	 -- In the cc-version will be translated as:
	 -- Harbour : TYPE = DATATYPE
	 --	 mk_harbour_(pool : Maximal(Ship)-set, berth: Maximal(Index)-m->Maximal(Ship))
	 -- And a cc declaration of the form:
	 -- Harbour_cc : TYPE = DATATYPE 
	 --      Harbour_cc(val : Harbour),
	 --	 Harbour_cc_nav(nav_val: Not_a_value_type)
	 -- Then, the reconstructor will refer to the <Harbour_cc> type, not to the <Harbour> one
	 -- That's why no reconstructor is added here.
	 -- If added, this breaks the type closure (fixed point) algorithm:
	 -- This happens because Harbour -> reconstructor - (by definition on the cc version) -> Harbour_cc ->
	 -- - (by lifting)    -> Harbour ===> CIRCULAR DEPENDENCY!
--	 where(sal_construc(IdOp_, LiftedBaseVid, CC_Destructors, nil) -> SAL_CC_Constructor) -- jiperna (the nil was formerly: CC_Recons)
	 where(sal_construc(IdOp, LiftedBaseVid, CC_Destructors, CC_Recons) -> SAL_CC_Constructor)
	 -- cwg CC_Recons replaced to fix problem in calculating fixed points
	 -- The problem described above is dealt with by removing
	 -- reconstructors from the fixed point calculation
	 -- of non-lifted types
	 where(sal_part(SAL_CC_Constructor, nil) -> CC_DataTypePart)
	 where(user_defined(sal_variant_type(list(CC_DataTypePart,nil))) -> CC_TypeElem)

	 Tid'Lifted_Tid -> tid(LTid)
	 -- Generating the CC_OPS context:
	 SAL_Gen_CC_Ops_Context(defined(Typeid,nil), LTid)
	 LTid'TExpr <- user_defined(sal_cc_type(CC_TypeElem, defined(Typeid,nil)))
	 where(sal_type_decl(Ident,Tid,CC_TypeElem) -> CC_ContextElement)
	 LTid'Declaration <- CC_ContextElement
	 
	 -- This version should add, not only the non-lifted type definition but also the
	 -- declaration of the lifted type. The problem here is that the nav fields for the type are NOT
	 -- KNOWN YET (they will be discovered on the way while translating). The approach to solve this is
	 -- to just add the non lifted declaration only (in the cc AST) for the moment and to collect the variant
	 -- as they are 'generated ' (the navs). The lifted declaration will be included on the second pass...
	 Insert_Context_Element(CC_ContextElement, CC_ContextElements1  -> CC_ContextElementsOut)


'action' SAL_Turn_Formals_to_Actuals(FORMAL_FUNCTION_PARAMETERS -> ACTUAL_FUNCTION_PARAMETERS)

  'rule' SAL_Turn_Formals_to_Actuals(list(F1 : form_parm(P, B), nil) -> list(fun_arg(P, Exprs), nil))
	 SAL_Turn_Formal_to_Actual(F1 -> Exprs)

  'rule' SAL_Turn_Formals_to_Actuals(nil -> nil)

'action' SAL_Turn_Formal_to_Actual(FORMAL_FUNCTION_PARAMETER -> VALUE_EXPRS)

  'rule' SAL_Turn_Formal_to_Actual(form_parm(Pos, Bindings) -> Exprs)
	 SAL_Turn_Bindings_to_Actuals(Bindings -> Exprs)

'action' SAL_Turn_Bindings_to_Actuals(BINDINGS -> VALUE_EXPRS)

  'rule' SAL_Turn_Bindings_to_Actuals(list(Binding : single(Pos, IdOp), Rest) -> list(VE1, VRest))
	 New_value_id(Pos, IdOp -> I)
	 I'Type <- none -- generate an error if used
	 where(VALUE_EXPR'val_occ(Pos, I, nil) -> VE1)
	 SAL_Turn_Bindings_to_Actuals(Rest -> VRest)

  'rule' SAL_Turn_Bindings_to_Actuals(nil -> nil)

'action' SAL_Lower_Exprs(SAL_VALUE_EXPRS, SAL_FORMAL_FUN_PARAMETERS -> SAL_VALUE_EXPRS)

  'rule' SAL_Lower_Exprs(list(E, ES), list(FP, FPS) -> list(E1, ES1)):
	 where(FP -> formal_param(_, CC_Type, _))
	 SAL_Lower_Expr(E, CC_Type -> E1)
	 SAL_Lower_Exprs(ES, FPS -> ES1)

  'rule' SAL_Lower_Exprs(nil, _ -> nil):

'action' SAL_Lower_Expr(SAL_VALUE_EXPR, SAL_TYPE_EXPR -> SAL_VALUE_EXPR)

  'rule' SAL_Lower_Expr(E, CC_Type -> E1):
	 DefaultPos(->P)
	 where(CC_Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 Tid'Constructor -> vid(Const)
	 Tid'Lifted_fields -> Fields
	 SAL_Find_Accesor_in_Fields(Fields, Const -> AccVid)
	 where(sal_funct_applic(sal_esp_value_occ(AccVid),
				sal_argument(list(E, nil))) -> E1)

  'rule' SAL_Lower_Expr(E, CC_Type -> E1):
  	 where(CC_Type -> user_defined(sal_cc_type(user_defined(sal_bracket_type(T)),_)))
	 SAL_Lower_Expr(E, T -> E1)

/*
-- CWG 12/4/08
-- now added in values.g for SAL, and resolved in cc.g
-------------------------------------------------------------------
-- SAL_Add_destructors
-------------------------------------------------------------------
-- Adds the constructors (compulsory in SAL) when missing....
-------------------------------------------------------------------
'action' SAL_Add_destructors(Type_id)

-- insert any missing destructors
  'rule' SAL_Add_destructors(I):
	 [|
	   I'Type -> sort(K)
	   (|
	     where(K -> variant(VS))
	     SAL_Add_destructors_to_variants(I, partial, VS, 0 -> VS1)
	     I'Type <- sort(variant(VS1))
	   ||
	     where(K -> record(CS))
	     SAL_Add_destructors_to_components(I, total, CS, 0 -> CS1, _)
	     I'Type <- sort(record(CS1))
	   |)
	 |]

'action' SAL_Add_destructors_to_variants(Type_id, FUNCTION_ARROW, VARIANTS, INT -> VARIANTS)

  'rule' SAL_Add_destructors_to_variants(I, Arr, list(V, VS), N -> list(V1, VS1)):
	 SAL_Add_destructors_to_variant(I, Arr, V, N -> V1, N1)
	 SAL_Add_destructors_to_variants(I, Arr, VS, N1 -> VS1)

  'rule' SAL_Add_destructors_to_variants(_, _, nil, _ -> nil):

'action' SAL_Add_destructors_to_variant(Type_id, FUNCTION_ARROW, VARIANT, INT -> VARIANT, INT)

  'rule' SAL_Add_destructors_to_variant(I, Arr, record(P, C, CS), N ->
					      record(P, C, CS1), N1):
	 SAL_Add_destructors_to_components(I, Arr, CS, N -> CS1, N1)

'action' SAL_Add_destructors_to_components(Type_id, FUNCTION_ARROW, COMPONENTS, INT -> COMPONENTS, INT)

  'rule' SAL_Add_destructors_to_components(I, Arr, list(C, CS), N -> list(C1, CS1), N1):
	 SAL_Add_destructor_to_component(I, Arr, C, N -> C1, N2)
	 SAL_Add_destructors_to_components(I, Arr, CS, N2 -> CS1, N1)

  'rule' SAL_Add_destructors_to_components(_, _, nil, N -> nil, N):

'action' SAL_Add_destructor_to_component(Type_id, FUNCTION_ARROW, COMPONENT, INT -> COMPONENT, INT)

  'rule' SAL_Add_destructor_to_component(I, Arr, component(P, nil, T, R), N ->
						  component(P, D, T, R), N+1)
	 Int_to_string(N -> S)
	 Concatenate3("acc_", S, "_" -> AccS)
	 string_to_id(AccS -> AccId)
	 New_value_id(P, id_op(AccId) -> AccI)
	 AccI'Type <- fun(defined(I, nil), Arr, result(T,nil,nil,nil,nil))
	 where(dest_ref(AccI) -> D)
--	 Putwarning(P)
--	 Putmsg("Generating missing accessor\n")

  'rule' SAL_Add_destructor_to_component(_, _, C, N -> C, N):

*/

---------------------------------------------------------------
-- SAL_Generate_Destructors
---------------------------------------------------------------
-- This function processes the destructors (RSL destructors) and
-- translates them into SAL destructors...
---------------------------------------------------------------
'action' SAL_Generate_Destructors(COMPONENTS, 
				  SAL_DESTRUCTORS, SAL_RECONSTRUCTORS, 
				  SAL_DESTRUCTORS, SAL_RECONSTRUCTORS, 
				  SAL_CONTEXT_CONSTANTS, 
				  SAL_CONTEXT_CONSTANTS -> 
				  SAL_DESTRUCTORS, SAL_RECONSTRUCTORS, SAL_DESTRUCTORS, SAL_RECONSTRUCTORS, SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

-- any missing destructors added earlier
         
	 -- Destructor and Reconstructor
  'rule' SAL_Generate_Destructors(list(component(Pos,
			                   dest_ref(ValueidDestruct),
					   TypeExpr,
			                   recon_ref(ValueidRecons)),
                            ComponentsTail),
                            Destructors, Reconstructors, CC_Destructors, CC_Reconstructors, CElems, CC_CElems -> 
			    Destructorsout, Reconstructorsout, CC_DestructorsOut, CC_ReconstructorsOut, CElemsOut, CC_CElemsOut):

	 -- Destructor to Destructor
	 ValueidDestruct'Pos -> Pos2
	 ValueidDestruct'Ident -> IdDestruct


	 Gen_SAL_Id_Op(Pos2, IdDestruct,none,none -> IdOp, _) -- the accesors are, again, names (only the id part is used)
	 SAL_Gen_Type_Expr(Pos, TypeExpr -> TElem, CC_Type)

	 where(IdDestruct -> id_op(Ident))
	 IncreaseCol(Pos2 -> NewPos1)

	 SAL_Current_Cid -> Cid

	 -- This is the value Id for the CONSTRUCTOR of the RECORD...
	 -- The lifted version of it will be replaced later with the proper
	 -- lifted version...
	 -- It is created with a fake position for the moment to do the trick below...
	 -- The proper position will be restored after the trick...
	 New_SAL_value_id(NewPos1, IdOp, Cid, TElem, record_field  -> Vid)
	 Vid'Lifted_Vid -> LiftedBaseVid
	 LiftedBaseVid'IdOp <- IdOp
	 -- The increased position is used for the moment to produce a match 
	 -- with the fake destructor introduced below...

	[|
	   -- This is a fake constructor that is used in the cc version to refer to the non-lifted destructor
	   -- for the record
	   -- On an ocurrence of this vid (also fakely created below) it will match (temporarly) with the Vid created above
	   -- (by position)
	   New_value_id(NewPos1, id_op(Ident) -> Non_CC_RSL_Vid)
	   -- Faking the information (from the real one)
	   ValueidDestruct'Def -> Definition
	   Non_CC_RSL_Vid'Def <- Definition
	   ValueidDestruct'Qualifier -> Qualif
	   Non_CC_RSL_Vid'Qualifier <- Qualif
	   ValueidDestruct'Type -> TE1
	   Non_CC_RSL_Vid'Type <- TE1
	   where(Definition -> expl_fun(Parms, Body, Post, Pre, SA, SR))
	   -- Doing another trick here...
	   -- We are about to turn the formal parameters from the destructor function
	   -- into actual parameter to... itself!
	   -- In this way, the function in the definition of the value_id will be:
	   -- <destr_id> : T1 >< T2 ><.....>< Tn -> Tx
	   -- <destr_id>(arg1, arg2,...., argn) is
	   --    <destr_id>(arg1, arg2,...,argn)
	   SAL_Turn_Formals_to_Actuals(Parms -> ActualParams)
	   Gen_SALFormal_Parameters(Parms, TE1 -> SAL_Params,_, SAL_CC_Params)
	   Vid'Params <- SAL_Params
	   -- generating the application:
	   DefaultPos(-> P)
	   where(application(P, val_occ(P, Non_CC_RSL_Vid, nil), ActualParams) -> NewBody)
	   where(expl_fun(Parms, NewBody, Post, Pre, SA, SR) -> ModifiedDef)
	   ValueidDestruct'Def <- ModifiedDef

	   SAL_Process_Value_id(ValueidDestruct,ModifiedDef, destructor_function, nil, nil -> _, LiftedDestructor)
	   -- Un-doing the trick:
	   ValueidDestruct'Def <- Definition
	   -- Setting up the proper lifted destr_function
	   look_up_value_id(Pos2 -> vid(Mk_Fake_Vid))
	   Mk_Fake_Vid'Pos <- NewPos1
	   Mk_Fake_Vid'Lifted_Vid -> LiftedVid1
	   -- Now I want the system to use the lifted destructor every time the normal constructor is invoked,
	   -- so I link them, loosing the relationship with the fake one that is no needed anymore (the fake
	   -- constructor <destr_Id>_ is only used inside the body of the lifted constructor).
	   Vid'Lifted_Vid <- LiftedVid1
	   LiftedVid1'Params <- SAL_CC_Params
	   -- Removing the fake from the global collection (I don't want it anymore)
	   SAL_Remove_Vid_from_Globals(Mk_Fake_Vid)

	   -- Collecting the destructor:
	   Collect_Lifted_Destructor(LiftedDestructor)
       |]
         Vid'Pos <- Pos2

         where(sal_destructor(IdOp, Vid, TElem, TypeExpr) -> Destructor) --OriginalVariant
	 SAL_Insert_Destructor(Destructor, Destructors -> Destructors1)
	 -- cc 
	 where(sal_destructor(IdOp, LiftedBaseVid, TElem, TypeExpr) -> CC_Destructor) --OriginalVariant
	 SAL_Insert_Destructor(CC_Destructor, CC_Destructors -> CC_Destructors1)

	 SAL_Generate_Destructors(ComponentsTail, Destructors1, Reconstructors, CC_Destructors1, CC_Reconstructors, CElems, CC_CElems
					 -> Destructorsout,
					 Recons1,
					 CC_DestructorsOut,
					 CC_Recons1,
					 CElems1, CC_CElems1)

	 -- make reconstructors last to ensure all destructors are
	 -- created first, else later destructor occurrences in
	 -- reconstructor definitions will not be qualified


	 -- Processing the reconstructor:
	 ValueidRecons'Pos -> PosRC
	 ValueidRecons'Ident -> IdRC
	 ValueidRecons'Def -> ReconsDef
	 -- Signaling that we are processing a reconstructor:
	 SAL_Current_Reconstructor <- value_id(ValueidRecons)
	 -- cwg last parameter to following function was nil
	 SAL_Process_Value_id(ValueidRecons,ReconsDef, reconstructor_function, CElems1, CC_CElems1 -> CElemsOut, CC_CElemsOut)
	 SAL_Current_Reconstructor <- nil
	 look_up_value_id(PosRC -> vid(Vid1))
	 Collect_Reconstructor_Decls(CC_CElemsOut)

	 -- Reconstructor arguments will be generated separately (they need more information)
	 Vid1'IdOp -> IdOpRC1
	 where(sal_reconstructor(IdOpRC1, Vid1, TElem, TypeExpr, Pos2) -> Reconstructor)--OriginalVariant
	 SAL_Insert_Reconstructor(Reconstructor, Recons1 -> Reconstructorsout)

	 -- cc
	 Vid1'Lifted_Vid -> LVid1
	 where(sal_reconstructor(IdOpRC1, LVid1, CC_Type, TypeExpr, Pos2) -> CC_Reconstructor)--OriginalVariant
	 SAL_Insert_Reconstructor(CC_Reconstructor, CC_Recons1 -> CC_ReconstructorsOut)

	 -- Destructor and No Reconstructor
  'rule' SAL_Generate_Destructors(list(component(Pos,
			                   dest_ref(ValueidDestruct),
					   TypeExpr,
			                   nil),
                            ComponentsTail),
                            Destructors, RC, CC_Destructors, CC_RC, CElems, CC_CElems -> 
			           Destructorsout, RCout, CC_DestructorsOut, CC_ReconstructorsOut, CElemsOut, CC_CElemsOut):

	 -- Destructor to Destructor
	 ValueidDestruct'Pos -> Pos2
	 ValueidDestruct'Ident -> IdDestruct

	 Gen_SAL_Id_Op(Pos2, IdDestruct,none,none -> IdOp, _) -- the accesors are, again, names (only the id part is used)
	 SAL_Gen_Type_Expr(Pos, TypeExpr -> TElem, CC_Type)

	 where(IdDestruct -> id_op(Ident))
	 IncreaseCol(Pos2 -> NewPos1)

	 SAL_Current_Cid -> Cid

	 -- This is the value Id for the CONSTRUCTOR of the RECORD...
	 -- The lifted version of it will be replaced later with the proper
	 -- lifted version...
	 -- It is created with a fake position for the moment to do the trick below...
	 -- The proper position will be restored after the trick...
	 New_SAL_value_id(NewPos1, IdOp, Cid, TElem, record_field  -> Vid)
	 Vid'Lifted_Vid -> LiftedBaseVid
	 LiftedBaseVid'IdOp <- IdOp
	 -- The increased position is used for the moment to produce a match 
	 -- with the fake constructor introduced below...
	[|
	   -- This is a fake constructor that is used in the cc version to refer to the non-lifted constructor
	   -- for the record (mk_<TypeName>_)
	   -- On an ocurrence of this vid (also fakely created below) it will match (temporarly) with the Vid created above
	   -- (by position)
	   New_value_id(NewPos1, id_op(Ident) -> Non_CC_RSL_Vid)
	   -- Faking the information (from the real one)
	   ValueidDestruct'Def -> Definition
	   Non_CC_RSL_Vid'Def <- Definition
	   ValueidDestruct'Qualifier -> Qualif
	   Non_CC_RSL_Vid'Qualifier <- Qualif
	   ValueidDestruct'Type -> TE1
	   Non_CC_RSL_Vid'Type <- TE1
	   where(Definition -> expl_fun(Parms, Body, Post, Pre, SA, SR))
	   -- Doing another trick here...
	   -- We are about to turn the formal parameters from the destructor function
	   -- into actual parameter to... itself!
	   -- In this way, the function in the definition of the value_id will be:
	   -- <destr_id> : T1 >< T2 ><.....>< Tn -> Tx
	   -- <destr_id>(arg1, arg2,...., argn)
	   --    <destr_id>_(arg1, arg2,...,argn)
	   SAL_Turn_Formals_to_Actuals(Parms -> ActualParams)
	   Gen_SALFormal_Parameters(Parms, TE1 -> SAL_Params,_, SAL_CC_Params)

	   Vid'Params <- SAL_Params
	   -- generating the application:
	   DefaultPos(-> P)
	   where(application(P, val_occ(P, Non_CC_RSL_Vid, nil), ActualParams) -> NewBody)
	   where(expl_fun(Parms, NewBody, Post, Pre, SA, SR) -> ModifiedDef)
	   ValueidDestruct'Def <- ModifiedDef

	   SAL_Process_Value_id(ValueidDestruct,ModifiedDef,destructor_function, nil, nil -> _, Destrs)
	   -- Un-doing the trick:
	   ValueidDestruct'Def <- Definition
           -- I1'Pos <- SavedPos
	   -- Setting up the proper lifted destr_function
	   look_up_value_id(Pos2 -> vid(Mk_Fake_Vid))
	   Mk_Fake_Vid'Pos <- NewPos1
	   Mk_Fake_Vid'Lifted_Vid -> LiftedVid1
	   -- Now I want the system to use the lifted destructor every time the normal constructor is invoked,
	   -- so I link them, loosing the relationship with the fake one that is no needed anymore (the fake
	   -- constructor <destr_Id>_ is only used inside the body of the lifted constructor).
	   Vid'Lifted_Vid <- LiftedVid1
	   LiftedVid1'Params <- SAL_CC_Params
	   -- Removing the fake from the global collection (I don't want it anymore)
	   SAL_Remove_Vid_from_Globals(Mk_Fake_Vid)

	   -- Collecting the destructor:
	   Collect_Lifted_Destructor(Destrs)
       |]
       Vid'Pos <- Pos2


         where(sal_destructor(IdOp, Vid, TElem, TypeExpr) -> Destructor) --OriginalVariant
	 SAL_Insert_Destructor(Destructor, Destructors -> Destructors1)
         
	 -- cc
	 where(sal_destructor(IdOp, LiftedBaseVid, TElem, TypeExpr) -> CC_Destructor) --OriginalVariant
	 SAL_Insert_Destructor(CC_Destructor, CC_Destructors -> CC_Destructors1)

         SAL_Generate_Destructors(ComponentsTail, Destructors1,RC, CC_Destructors1, CC_RC, CElems, CC_CElems  -> 
                                      Destructorsout,RCout,CC_DestructorsOut, CC_ReconstructorsOut, CElemsOut, CC_CElemsOut)


	 

  -- NEITHER Destructor NOR Reconstructor
  'rule' SAL_Generate_Destructors(list(component(Pos,
			                   nil,
					   TypeExpr,
			                   nil),
                            ComponentsTail),
                            Destructors, RC, CC_Destructors, CC_RC, CElems, CC_CElems -> 
			    Destructorsout,RCout,CC_DestructorsOut, CC_ReconstructorsOut, CElemsOut, CC_CElemsOut):

	 -- This case should never arise... skipping (error recovery)
	 SAL_Generate_Destructors(ComponentsTail, Destructors,RC, CC_Destructors, CC_RC,CElems, CC_CElems   -> 
						  Destructorsout,RCout,CC_DestructorsOut, CC_ReconstructorsOut, CElemsOut, CC_CElemsOut)


  'rule' SAL_Generate_Destructors(nil, Destructors, RC, CC_D, CC_RC,CElems, CC_CElems  -> Destructors,  RC, CC_D, CC_RC, CElems, CC_CElems)

  'rule' SAL_Generate_Destructors(T, Tail, RC,CC_D, CC_RC, CElems, CC_CElems -> Tail, RC, CC_D, CC_RC, CElems, CC_CElems)
	 Putmsg("Debugging predicate activated in SAL_Generate_Destructors\n")
	 print(T)

---------------------------------------------------------------
-- SAL_Gen_Deref_Ident
---------------------------------------------------------------
-- Needed in SAL for DATATYPES... i.e.: T: TYPE = DATATYPE
--					            const(val_: ...)
-- Encapsulated in function for re-use....
--------------------------------------------------------------

'action' SAL_Gen_Deref_Ident(POS -> SAL_ID_OP)

  'rule' SAL_Gen_Deref_Ident(P -> Ident)
	 string_to_id("val_" -> Id)
	 where(SAL_ID_OP'id(Id) -> Ident)

-----------------------------------------------------------------------
-- SAL_Gen_Type_List
-----------------------------------------------------------------------
-- This function is used to process the types associated with bindings...
-- In particular, it is needed to make a pairwise matching (when possible) with
-- the bindings to allow the NAMESPACE generation for functions and to process the bindings
-- in function declarations (like in the case f : T >< T1 >< ... -> Tn f(a,b,c,...)) is... 
-----------------------------------------------------------------------
'action' SAL_Gen_Type_List(BINDINGS, TYPE_EXPR -> SAL_TYPE_LIST)

         -- Special case... there is only one argumen in the
	 -- binding... That name should be assigned to the whole product...

  'rule' SAL_Gen_Type_List(list(single(P, Id), nil),
					  TExpr -> Result)
	 where(SAL_TYPE_LIST'list(TExpr,nil) -> Result)

  'rule' SAL_Gen_Type_List(_, product(list(TE, Rest)) -> Result)
	 Process_Rest(Rest -> Result1)
	 where(SAL_TYPE_LIST'list(TE, Result1) -> Result)

  'rule' SAL_Gen_Type_List(_, Type -> Result)
	 where(SAL_TYPE_LIST'list(Type, nil) -> Result)

'action' Process_Rest(PRODUCT_TYPE -> SAL_TYPE_LIST)

  'rule' Process_Rest(list(TE, Rest) -> Result)
	 Process_Rest(Rest -> Result1)
	 where(SAL_TYPE_LIST'list(TE, Result1) -> Result)

  'rule' Process_Rest(nil -> nil)

---------------------------------------------------------------------------
-- SAL_Prepare_Bindings
---------------------------------------------------------------------------
-- This function prepares the bindings for namespace extraction.
-- In particular, it contains rules for:
-- * Handling the initial (special) case: This happens on bindings on the form:
--   f : T1 ...           // where T1 = T2 >< T3
--   f(a,b)...
--   This case, in particular, will not carry a product-binding (as
--   spected and generated in the general case). Instead, a list of
--   single-binded names will be generated.
--   This function will replace a binding list of the form:
--      list(single(), single()...) asociated with only one type
--   with a binding list of the form:
--      list(product(single(), single(),...), nil)
---------------------------------------------------------------------------
'action' SAL_Prepare_Bindings(BINDINGS, SAL_TYPE_LIST -> BINDINGS)

  'rule' SAL_Prepare_Bindings(list(H,T), list(_, nil) -> Result)
	 -- There are more bindings in the list:
	 ne(T, nil)
	 -- convert it into a product:
	 where(H -> single(P,_))
	 where(BINDING'product(P, list(H,T)) -> ListElem)
	 where(BINDINGS'list(ListElem, nil) -> Result)

  'rule' SAL_Prepare_Bindings(BS, _ -> BS)

--------------------------------------------------------------------
-- Gen_SAL_Result_Type
--------------------------------------------------------------------
-- Processes the functions type expression and generates the result 
-- type from it... (trivial)
--------------------------------------------------------------------

'action' Gen_SAL_Result_Type(POS, TYPE_EXPR -> TYPE_EXPR, SAL_TYPE_EXPR, SAL_TYPE_EXPR)

  'rule' Gen_SAL_Result_Type(Pos, TypeExpr -> RSL_ResultType, SAL_ResultType, CC_Type)
	 Split_fun_type(TypeExpr -> _, RSL_ResultType)
	 SAL_Gen_Type_Expr(Pos, RSL_ResultType -> SAL_ResultType, CC_Type)

--------------------------------------------------------------------
-- Gen_SALFormal_Parameters
---------------------------------------------------------------------
-- This function converts the FORMAL funtion parameters from RSL into the SAL ones
-- The most complex part is to convert the BINDINGS in the declaration into
-- namespace elements when needed, i.e. in the case:
-- type
--   Prod = Int >< Int
-- value
--   test : Prod -> Bool
--   test(p) is let (a,b) = p 
--      in  a > 1
--      end
-- WILL TRANSLATE TO:
-- test(p : Prod) : Bool_ =
--    LET LetId1_ : Prod = p 
--    IN LetId1.1 > 1
---------------------------------------------------------------------

'action' Gen_SALFormal_Parameters(FORMAL_FUNCTION_PARAMETERS, TYPE_EXPR
               -> SAL_FORMAL_FUN_PARAMETERS, BINDING_NAMESPACE, SAL_FORMAL_FUN_PARAMETERS)

  'rule' Gen_SALFormal_Parameters(list(form_parm(Pos, Bindings), ParamsTail),
	          TypeExpr -> ParamsOut, Namespace, CC_ParamsOut):

	 Split_fun_type(TypeExpr -> ArgsType, ResultType)
	 SAL_Gen_Type_List(Bindings, ArgsType -> T11)
	 SAL_Prepare_Bindings(Bindings, T11 -> PreparedBS)
	 Gen_SALFormal_Parameter(PreparedBS, T11 -> ParamsOut, Namespace, CC_ParamsOut)

  'rule' Gen_SALFormal_Parameters(nil, T -> nil,nil, nil):

'action' Gen_SALFormal_Parameter(BINDINGS, SAL_TYPE_LIST
	    -> SAL_FORMAL_FUN_PARAMETERS, BINDING_NAMESPACE, SAL_FORMAL_FUN_PARAMETERS)

  'rule' Gen_SALFormal_Parameter(list(single(P, Id), nil), list(TExpr, nil)
	    -> list(ParamOut, nil), Namespace, list(CC_ParamOut, nil)):

	 where(Id -> id_op(Ident))
	 -- It is not necessary to generate a new identifier...
	 -- In this case, the identifier name is introduced in the let 
	 -- (it does not include a sub-binding), for example:
	 -- let e : f(...)
	 -- in this case, ' e ' should be used as identifier for the
	 -- let expression
	 -- Generating the type element:	 
	 SAL_Gen_Type_Expr(P, TExpr -> TElem, LiftedTE)
	 -- Generate the parameter:
 	 where(formal_param(Ident,TElem,TExpr) -> ParamOut)
	 -- There is no need for namespace  here
	 -- (the namespace for lets is used to translate the names
	 -- introduced by the binding into field accesors... in this
	 -- case, there are no fields to acces.
	 where(BINDING_NAMESPACE'nil -> Namespace)
	 -- cc result:
	 where(formal_param(Ident, LiftedTE, TExpr) -> CC_ParamOut)
--Putmsg("Formal of type ")
--Print_type(TExpr)
--Putmsg(" gives lifted type ")
--(|
--where(LiftedTE -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
--SAL_Print_Tid(Tid)
--||
--print(LiftedTE)
--|)
--Putnl



  'rule' Gen_SALFormal_Parameter(list(single(P, Id), BS),
    	    list(T, TS) -> ParamsOut, Namespace, CC_ParamsOut):

	 Gen_SALFormal_Parameter(list(single(P,Id),nil), list(T,nil) 
	         -> Params1, Namespace1, CC_Params1)
	 Gen_SALFormal_Parameter(BS,TS -> Params2, Namespace2, CC_Params2)
	 SAL_Concatenate_Params(Params1,Params2 -> ParamsOut)
	 SAL_Catenate_Namespaces(Namespace1, Namespace2 -> Namespace)
	 -- cc
	 SAL_Concatenate_Params(CC_Params1,CC_Params2 -> CC_ParamsOut)

	 
  -- This case corresponds to signatures of the form:
  -- f(T1 >< T2 >< (T3 >< T4)) (when processing the (T3 >< T4) product
  'rule' Gen_SALFormal_Parameter(list(product(P, BS1), BS2),
				 list(product(list(T, TS)), TS2) -> ParamsOut,Namespace, CC_ParamsOut):

	 -- Process the current product:
	 SAL_Gen_Type_List(BS1, product(list(T, TS)) -> TypeList)
	 Gen_SALFormal_Parameter(BS1, TypeList -> Params1, Namespace1, CC_Params1)
	 -- Process the rest of the params:	
	 Gen_SALFormal_Parameter(BS2,TS2 -> Params2, Namespace2, CC_Params2)
	 -- Concatenate the stacks:
	 SAL_Catenate_Namespaces(Namespace1,Namespace2 -> Namespace)
	 SAL_Concatenate_Params(Params1, Params2 -> ParamsOut)
	 -- cc
	 SAL_Concatenate_Params(CC_Params1, CC_Params2 -> CC_ParamsOut) 

  -- Here is the most interesting case...
  -- On the binding side we have something that looks like a product
  -- On the other hand, the type list has a non-product type in the
  -- head... Another binding was introduced!
  'rule' Gen_SALFormal_Parameter(list(product(P, BS1), BS2),
				 list(T, TS) -> ParamsOut,Namespace, CC_ParamsOut):

	 -- Generate the identifier:
	 SAL_Gen_Param_Ident(-> Ident)
	 -- Generating the type element:	 
	 SAL_Gen_Type_Expr(P, T -> TElem, LiftedTE)
	 -- Generate the param:
	 where(formal_param(Ident,TElem,T) -> Param1)
	 -- Generate the namespace for this product-binding:
	 SAL_Gen_Namespace_from_Bindings(Ident, BS1 -> Namespace1)
	 -- Process the rest of the params:
	 Gen_SALFormal_Parameter(BS2,TS -> Params2, Namespace2, CC_Params2)
	 -- Concatenate the stacks:
	 SAL_Catenate_Namespaces(Namespace1,Namespace2 -> Namespace)
	 where(SAL_FORMAL_FUN_PARAMETERS'list(Param1, Params2) -> ParamsOut)
	 -- cc
	 where(formal_param(Ident,LiftedTE,T) -> CC_Param1)
	 where(SAL_FORMAL_FUN_PARAMETERS'list(CC_Param1, CC_Params2) -> CC_ParamsOut)

  'rule' Gen_SALFormal_Parameter(nil, _ -> nil,nil,nil): 

  'rule' Gen_SALFormal_Parameter(BS, TS -> nil,nil,nil)
	 Putmsg("Debugging predicate ACTIVATED for FORMAL PARAMS!\n")
	 print(BS)
	 print(TS)

-------------------------------------------------------------------
'action' SAL_Concatenate_Params(SAL_FORMAL_FUN_PARAMETERS,
	   SAL_FORMAL_FUN_PARAMETERS -> SAL_FORMAL_FUN_PARAMETERS)

  'rule' SAL_Concatenate_Params(list(H,T), Other -> Result)
	 SAL_Concatenate_Params(T, Other -> Result1)
	 where(SAL_FORMAL_FUN_PARAMETERS'list(H, Result1) -> Result)

  'rule' SAL_Concatenate_Params(nil, Other -> Other)

-------------------------------------------------------------------
-- SAL_Gen_Namespace
-------------------------------------------------------------------
-- This routine generates the namespace (introduced either with let
-- expressions or with function parameters)
-------------------------------------------------------------------

'action' SAL_Gen_Namespace_from_Bindings(IDENT, BINDINGS -> BINDING_NAMESPACE)

  'rule' SAL_Gen_Namespace_from_Bindings(Ident, BS ->  Namespace)
	 SAL_Internal_Gen_Namespace_from_Bindings(1, Ident, BS -> Namespace)

'action' SAL_Gen_Namespace_from_Binding(IDENT, BINDING -> BINDING_NAMESPACE)

  'rule' SAL_Gen_Namespace_from_Binding(Ident, B -> Namespace)
	 SAL_Internal_Gen_Namespace_from_Binding(1, Ident, B -> Namespace)

'action' SAL_Internal_Gen_Namespace_from_Bindings(INT, IDENT, BINDINGS -> BINDING_NAMESPACE)

  'rule' SAL_Internal_Gen_Namespace_from_Bindings(Index, Ident, 
				list(B, BS) -> Namespace)
	 SAL_Internal_Gen_Namespace_from_Binding(Index, Ident, B -> Namespace1)
	 SAL_Internal_Gen_Namespace_from_Bindings(Index+1, Ident, BS -> Namespace2)
	 SAL_Catenate_Namespaces(Namespace1,Namespace2 -> Namespace)

  'rule' SAL_Internal_Gen_Namespace_from_Bindings(_,_,nil -> nil)

'action' SAL_Internal_Gen_Namespace_from_Binding(INT, IDENT, BINDING -> BINDING_NAMESPACE)

  'rule' SAL_Internal_Gen_Namespace_from_Binding(Index, Ident, 
				single(P,Id) -> Namespace)
	 -- Process the current elem:
	 where(SAL_ID_OP'id(Ident) -> RecordName)
	 where(Id -> id_op(Ident1))
	 where(SAL_ID_OP'id(Ident1) -> Id1)
	 where(SAL_NAME'id_op(Id1) -> BoundName)
	 where(binding_elem(Index, RecordName, BoundName) -> BElem)
	 where(BINDING_NAMESPACE'list(BElem, nil) -> Namespace)

  'rule' SAL_Internal_Gen_Namespace_from_Binding(Index, Ident, 
				product(_,ProdBindings) -> Namespace)
	 where(SAL_ID_OP'id(Ident) -> RecordName)
	 -- Generate an entry for the current (fake)
	 -- There is no name asociated with the current field (it was
	 -- unfolded and names were asociated with its components)
	 where(SAL_NAME'nil -> BoundName)
	 where(binding_elem(Index, RecordName, BoundName) -> BElem)
	 SAL_Process_ProdBindings(1, BElem,ProdBindings -> Namespace1)
	 where(BINDING_NAMESPACE'list(BElem, Namespace1) -> Namespace)


--------------------------------------------------------------------------------
-- SAL_Process_ProdBindings
--------------------------------------------------------------------------------
-- This predicate processes a product inside a binding. This case
-- occurs, for example, when:
--
-- f(T1,T2, T3)
-- f(x, y, (a,(b,c))) is ... given that T3 = T4 >< (T5 >< T6)
--
-- Here, (b,c) is a new binding asociated with the second element in
-- the tuple asoc. with T3. This kind of binding is not possible in SAL, so
-- it has to be transformed to indexes (b = 1, c = 2) within the
-- proper field in the arguments (in this case, the one asociated with
-- T3.2).
-- The translation will be like:
-- f(x : T1, y: T2, Arg1_: T3) and every reference to a will be
-- translated to 'Arg1_.1', meanwhile, references to b will be 'Arg1_.3.1'
-- This routine generates the proper namespace (with nested references
-- to 'Arg1_.3' in the example) for 'b' and 'c'
--------------------------------------------------------------------------------

'action' SAL_Process_ProdBindings(INT, BINDING_ELEM, BINDINGS -> BINDING_NAMESPACE)

  'rule' SAL_Process_ProdBindings(Index, BElem, 
				list(single(P,Id),BS) -> Namespace)
	 -- Process the current elem:
	 where(Id -> id_op(Ident1))
	 where(SAL_ID_OP'id(Ident1) -> Id1)
	 where(SAL_NAME'id_op(Id1) -> BoundName)
	 where(nested_elem(Index, BoundName, BElem) -> BElem1)
	 -- Process the rest of the bindings:
	 SAL_Process_ProdBindings(Index+1, BElem, BS -> Namespace2)
	 where(BINDING_NAMESPACE'list(BElem1, Namespace2) -> Namespace)

  'rule' SAL_Process_ProdBindings(Index, BElem,  
				list(product(_,ProdBindings),BS) -> Namespace)
	 -- Generate an entry for the current (fake)
	 -- There is no name asociated with the current field (it was
	 -- unfolded and names were asociated with its components)
	 where(SAL_NAME'nil -> BoundName)
	 where(nested_elem(Index, BoundName,BElem) -> BElem1)
	 SAL_Process_ProdBindings(1, BElem1,ProdBindings -> Namespace2)
	 SAL_Process_ProdBindings(Index+1, BElem, BS -> Namespace1)
	 SAL_Catenate_Namespaces(Namespace1,Namespace2 -> Namespace)

  'rule' SAL_Process_ProdBindings(_,_, nil -> nil)

  'rule' SAL_Process_ProdBindings(_,_, BS -> nil)
	 Putmsg("Debugging predicate activated in SAL_Process_ProdBindings\n")
	 print(BS)
----------------------------------------------------------------------------------
'action' SAL_Process_Typing(TYPING -> SAL_ID_OP, SAL_TYPE_EXPR, BINDING_NAMESPACE, SAL_TYPE_EXPR)

  'rule' SAL_Process_Typing(single(_,Binding,T) -> Ident, TExpr,  Namespace, LTExpr)
	 (|
	    where(T -> product(_))
	    -- The type is not a product in the top level of the typing...
	    (|
		where(Binding -> single(P, IdOp))
		-- There is no actual binding introduced... 
		-- (i.e. has the form: a : T1)
		-- No namespace needed:
		where(BINDING_NAMESPACE'nil -> Namespace)
		-- Use the name in the specification:
		Gen_SAL_Id_Op(P, IdOp,none,none -> Ident, _) -- only a name, no need to distinguish with non-cc version
		-- Generate the type expression:
		SAL_Gen_Type_Expr(P, T -> TExpr, LTExpr)
	    ||
	        where(Binding -> product(P,_))
	        -- A binding is introduced
		-- (like: (Id1, Id2) : T1)
		-- Generate the identifier:
		SAL_Gen_Type_Ident(-> Ident1)
		where(SAL_ID_OP'id(Ident1) -> Ident)
		-- Generate the namespace:
		SAL_Remove_First_Brackets_from_Binding(Binding -> BS)
		SAL_Gen_Namespace_from_Bindings(Ident1, BS -> Namespace)
		-- Generate the type expr:
		SAL_Gen_Type_Expr(P, T -> TExpr, LTExpr)
             |)
	 ||
	     -- The type in the top level is a product:
	     (|
		where(Binding -> single(P, IdOp))
		-- There is no actual name introduced... 
		-- (i.e. has the form: a : (T1 >< T2))
		-- No namespace needed:
		where(BINDING_NAMESPACE'nil -> Namespace)
		-- Use the name in the specification:
		Gen_SAL_Id_Op(P, IdOp,none,none -> Ident, _) -- a name again... no distinction between cc and non-cc versions here...
		-- Generate the type expression:
		SAL_Gen_Type_Expr(P, T -> TExpr, LTExpr)
	    ||
	        where(Binding -> product(P,_))
	        -- A binding is introduced
		-- (like: (Id1, Id2) : (T1 >< T2))
		-- Generate the identifier:
		SAL_Gen_Type_Ident(-> Ident1)
		where(SAL_ID_OP'id(Ident1) -> Ident)
		-- Generate the namespace:
		SAL_Remove_First_Brackets_from_Binding(Binding -> BS)
		SAL_Gen_Namespace_from_Bindings(Ident1, BS -> Namespace)
		-- Generate the type expr:
		SAL_Gen_Type_Expr(P, T -> TExpr, LTExpr)
             |)
	  |)


----------------------------------------------------------------------------------
'action' Gen_SALBindings(BINDINGS -> SAL_BINDINGS)

  'rule' Gen_SALBindings(list(B, BS) -> list(B1, BS1)):
	 Gen_SALBinding(B -> B1)
	 Gen_SALBindings(BS -> BS1)

  'rule' Gen_SALBindings(nil -> nil):

'action' Gen_SALBinding(BINDING -> SAL_BINDING)

  'rule' Gen_SALBinding(single(P, Id) -> sal_typed_id(P, Idop, nil)):
	 Gen_SAL_Id_Op(P, Id,none,none -> Idop, _) -- just translating a name, no need to distinguish with non-cc version

  'rule' Gen_SALBinding(product(Pos, BS) -> sal_prod_binding(Pos, BS1)):
	 Gen_SALBindings(BS -> BS1)

'action' Gen_SALBindings_from_Typings(TYPINGS -> SAL_BINDINGS, SAL_BINDINGS, PRODUCT_TYPE)

  'rule' Gen_SALBindings_from_Typings(list(TP, TPS) -> BS, /*CC_BS*/ BS, TypeList):
	 Gen_SALBindings_from_Typing(TP -> BS1, CC_BS1, TLS1)
	 Gen_SALBindings_from_Typings(TPS -> BS2, CC_BS2, TLS2)
	 Concat_SALBindings(BS1, BS2 -> BS)
	 Concat_SALBindings(CC_BS1, CC_BS2 -> CC_BS)
	 SAL_Concatenate_Types(TLS1, TLS2 -> TypeList)

  'rule' Gen_SALBindings_from_Typings(nil -> nil, nil,nil)

'action' Gen_SALBindings_from_Typing(TYPING -> SAL_BINDINGS, SAL_BINDINGS, PRODUCT_TYPE)

  'rule' Gen_SALBindings_from_Typing(single(P, single(_, Id), T) ->
					list(sal_typed_id(P, IdOp, SALType), nil),
                                        list(sal_typed_id(P, IdOp, SALType), nil), TypeList):
					--list(sal_typed_id(P, IdOp, CC_Type), nil), TypeList):
	 Gen_SAL_Id_Op(P, Id,none,none -> IdOp, _) -- just translating a name, no need to distinguish with non-cc version
	 SAL_Gen_Type_Expr(P, T -> SALType, SAL_CC_Type1)
	 where(SAL_CC_Type1 -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 Tid'Constructor -> vid(Const)
	 Tid'Lifted_fields -> Fields
	 SAL_Find_Accesor_in_Fields(Fields, Const -> AccVid)
	 AccVid'Type -> CC_Type
	 where(PRODUCT_TYPE'list(T,nil) -> TypeList)


  'rule' Gen_SALBindings_from_Typing(single(P, product(P1, list(B, BS)), T0) 
								   -> BS3, BS3 /*CC_BS3*/, TypeList):
	 Debracket_abbrev(T0 -> product(list(T, TS))) -- in pvs_gen_ast.g
	 Gen_SALBindings_from_Typing1(single(P, B, T) -> BS1, CC_BS1, TLS1)
	 Gen_SALBindings_from_Typing(single(P, product(P1, BS), product(TS))
								 -> BS2, CC_BS2, TLS2)
	 Concat_SALBindings(BS1, BS2 -> BS3)
	 Concat_SALBindings(CC_BS1, CC_BS2 -> CC_BS3)
	 SAL_Concatenate_Types(TLS1, TLS2 -> TypeList)

  'rule' Gen_SALBindings_from_Typing(single(P, product(P1, nil), _) -> nil, nil, nil):

  'rule' Gen_SALBindings_from_Typing(single(P, product(_, BS), T) ->
							  list(PB, nil), list(PB,nil) /*list(CC_PB, nil)*/, list(T,nil)):
	 Gen_SALBindings(BS -> PBS)
	 SAL_Gen_Type_Expr(P, T -> SALT, SAL_CC_Type1)
	 where(SAL_CC_Type1 -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 Tid'Constructor -> vid(Const)
	 Tid'Lifted_fields -> Fields
	 SAL_Find_Accesor_in_Fields(Fields, Const -> AccVid)
	 AccVid'Type -> CC_Type
	 where(sal_typed_prod(P, PBS, SALT) -> PB)
	 where(sal_typed_prod(P, PBS, CC_Type) -> CC_PB)
	 
  'rule' Gen_SALBindings_from_Typing(multiple(P, list(B, BS), T) -> BS3, BS3 /*CC_BS3*/, TypeList):
	 Gen_SALBindings_from_Typing(single(P, B, T) -> BS1, CC_BS1, TLS1)
	 Gen_SALBindings_from_Typing(multiple(P, BS, T) -> BS2, CC_BS2, TLS2)
	 Concat_SALBindings(BS1, BS2 -> BS3)
	 Concat_SALBindings(CC_BS1, CC_BS2 -> CC_BS3)
	 SAL_Concatenate_Types(TLS1, TLS2 -> TypeList)

  'rule' Gen_SALBindings_from_Typing(multiple(P, nil, _) -> nil, nil, nil):

-- no further nesting allowed now
'action' Gen_SALBindings_from_Typing1(TYPING -> SAL_BINDINGS, SAL_BINDINGS, PRODUCT_TYPE)

  'rule' Gen_SALBindings_from_Typing1(single(P, single(_, Id), T) ->
					list(sal_typed_id(P, IdOp, SALT), nil),
					list(sal_typed_id(P, IdOp, CC_Type), nil), list(T,nil)):
	 Gen_SAL_Id_Op(P, Id,none,none -> IdOp, _) -- just translating a name, no need to distinguish with non-cc version
 	 SAL_Gen_Type_Expr(P, T -> SALT, SAL_CC_Type1)
	 where(SAL_CC_Type1 -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 Tid'Constructor -> vid(Const)
	 Tid'Lifted_fields -> Fields
	 SAL_Find_Accesor_in_Fields(Fields, Const -> AccVid)
	 AccVid'Type -> CC_Type

  'rule' Gen_SALBindings_from_Typing1(single(P, product(_, BS), T) ->
							  list(PB, nil), list(CC_PB, nil), list(T,nil)):
	 Gen_SALBindings(BS -> PBS)
	 SAL_Gen_Type_Expr(P, T -> SALT, SAL_CC_Type1)
	 where(SAL_CC_Type1 -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 Tid'Constructor -> vid(Const)
	 Tid'Lifted_fields -> Fields
	 SAL_Find_Accesor_in_Fields(Fields, Const -> AccVid)
	 AccVid'Type -> CC_Type
	 where(sal_typed_prod(P, PBS, SALT) -> PB)
	 where(sal_typed_prod(P, PBS, CC_Type) -> CC_PB)
	 
/*'action' Gen_SALBindings_from_Typing_Not_Top(TYPING -> SAL_BINDINGS, SAL_BINDINGS, PRODUCT_TYPE)

  'rule' Gen_SALBindings_from_Typing_Not_Top(single(P, single(_, Id), T) ->
					list(sal_typed_id(P, IdOp, SALType), nil),
					list(sal_typed_id(P, IdOp, CC_Type), nil), TypeList):
	 Gen_SAL_Id_Op(P, Id,none,none -> IdOp, _) -- just translating a name, no need to distinguish with non-cc version
	 SAL_Gen_Type_Expr(P, T -> SALType, CC_Type)
	 where(PRODUCT_TYPE'list(T,nil) -> TypeList)


  'rule' Gen_SALBindings_from_Typing_Not_Top(single(P, product(P1, list(B, BS)), T0) 
								   -> BS3, CC_BS3, TypeList):
	 Debracket_abbrev(T0 -> product(list(T, TS))) -- in pvs_gen_ast.g
	 Gen_SALBindings_from_Typing1_Not_Top(single(P, B, T) -> BS1, CC_BS1, TLS1)
	 Gen_SALBindings_from_Typing_Not_Top(single(P, product(P1, BS), product(TS))
								 -> BS2, CC_BS2, TLS2)
	 Concat_SALBindings(BS1, BS2 -> BS3)
	 Concat_SALBindings(CC_BS1, CC_BS2 -> CC_BS3)
	 SAL_Concatenate_Types(TLS1, TLS2 -> TypeList)

  'rule' Gen_SALBindings_from_Typing_Not_Top(single(P, product(P1, nil), _) -> nil, nil, nil):

  'rule' Gen_SALBindings_from_Typing_Not_Top(single(P, product(_, BS), T) ->
							  list(PB, nil), list(CC_PB, nil), list(T,nil)):
	 Gen_SALBindings(BS -> PBS)
	 SAL_Gen_Type_Expr(P, T -> SALT, CC_Type)
	 where(sal_typed_prod(P, PBS, SALT) -> PB)
	 where(sal_typed_prod(P, PBS, CC_Type) -> CC_PB)
	 
  'rule' Gen_SALBindings_from_Typing_Not_Top(multiple(P, list(B, BS), T) -> BS3, CC_BS3, TypeList):
	 Gen_SALBindings_from_Typing_Not_Top(single(P, B, T) -> BS1, CC_BS1, TLS1)
	 Gen_SALBindings_from_Typing_Not_Top(multiple(P, BS, T) -> BS2, CC_BS2, TLS2)
	 Concat_SALBindings(BS1, BS2 -> BS3)
	 Concat_SALBindings(CC_BS1, CC_BS2 -> CC_BS3)
	 SAL_Concatenate_Types(TLS1, TLS2 -> TypeList)

  'rule' Gen_SALBindings_from_Typing_Not_Top(multiple(P, nil, _) -> nil, nil, nil):

-- no further nesting allowed now
'action' Gen_SALBindings_from_Typing1_Not_Top(TYPING -> SAL_BINDINGS, SAL_BINDINGS, PRODUCT_TYPE)

  'rule' Gen_SALBindings_from_Typing1_Not_Top(single(P, single(_, Id), T) ->
					list(sal_typed_id(P, IdOp, SALT), nil),
					list(sal_typed_id(P, IdOp, CC_Type), nil), list(T,nil)):
	 Gen_SAL_Id_Op(P, Id,none,none -> IdOp, _) -- just translating a name, no need to distinguish with non-cc version
 	 SAL_Gen_Type_Expr(P, T -> SALT, CC_Type)

  'rule' Gen_SALBindings_from_Typing1_Not_Top(single(P, product(_, BS), T) ->
							  list(PB, nil), list(CC_PB, nil), list(T,nil)):
	 Gen_SALBindings(BS -> PBS)
	 SAL_Gen_Type_Expr(P, T -> SALT, CC_Type)
	 where(sal_typed_prod(P, PBS, SALT) -> PB)
	 where(sal_typed_prod(P, PBS, CC_Type) -> CC_PB)
	 
*/

'action' Concat_SALBindings(SAL_BINDINGS, SAL_BINDINGS -> SAL_BINDINGS)

  'rule' Concat_SALBindings(list(B, BS), BS1 -> list(B, BS2)):
	 Concat_SALBindings(BS, BS1 -> BS2)

  'rule' Concat_SALBindings(nil, BS -> BS)


--------------------------------------------------
--  RSL Type Expression  ==>  SAL Type Expression
--------------------------------------------------

'action' SAL_Gen_Type_Expr(POS, TYPE_EXPR -> SAL_TYPE_EXPR, SAL_TYPE_EXPR)

---------------------------------------------------------------------
-- Non translatable type expressions:
---------------------------------------------------------------------

  'rule' SAL_Gen_Type_Expr(Pos, real -> SALTypeExprout, SALTypeExprout):
	 where(SAL_TYPE_EXPR'nil -> SALTypeExprout)
	 Puterror(Pos)
	 Putmsg("Real type not supported")
	 Putnl()

  'rule' SAL_Gen_Type_Expr(Pos, text -> SALTypeExprout, SALTypeExprout):
	 where(SAL_TYPE_EXPR'nil-> SALTypeExprout)
	 Puterror(Pos)
	 Putmsg("Text type not supported")
	 Putnl()

  'rule' SAL_Gen_Type_Expr(Pos, char -> SALTypeExprout, SALTypeExprout):
	 where(SAL_TYPE_EXPR'nil -> SALTypeExprout)
	 Puterror(Pos)
	 Putmsg("Char type not supported")
	 Putnl()

  'rule' SAL_Gen_Type_Expr(Pos, time -> SALTypeExprout, SALTypeExprout):
	 where(SAL_TYPE_EXPR'nil -> SALTypeExprout)
	 Puterror(Pos)
	 Putmsg("Time type not supported")
	 Putnl()

 -- Inifinite collections not supported due to type finiteness requirement
 -- in SAL:

 'rule' SAL_Gen_Type_Expr(Pos, infin_set(TypeExprFS) -> SALTypeExprout, SALTypeExprout):
	 where(SAL_TYPE_EXPR'nil -> SALTypeExprout)
	 Puterror(Pos)
	 Putmsg("Infinite set type not supported")
	 Putnl()

  'rule' SAL_Gen_Type_Expr(Pos, infin_list(TypeExprFL) -> SALTypeExprout, SALTypeExprout):
	 where(SAL_TYPE_EXPR'nil -> SALTypeExprout)
	 Puterror(Pos)
	 Putmsg("Infinite list type not supported")
	 Putnl()

  'rule' SAL_Gen_Type_Expr(Pos, infin_map(Dom, Rng) -> SALTypeExprout, SALTypeExprout):
	 where(SAL_TYPE_EXPR'nil -> SALTypeExprout)
	 Puterror(Pos)
	 Putmsg("Infinite map type not supported")
	 Putnl()

--------------------------------------------------------------------------
-- BASIC RSL TYPES 
--------------------------------------------------------------------------

  'rule' SAL_Gen_Type_Expr(Pos, unit -> SALTypeExprout, SALTypeExprout):
	 -- CWG shouldn't this be an error?
	 Puterror(Pos)
	 Putmsg("Unit type not supported")
	 Putnl()
	 where(rsl_built_in(unit) -> SALTypeExprout)

  'rule' SAL_Gen_Type_Expr(Pos, bool -> SALTypeExprout, LiftedType):
	 Default_Bool_Tid -> BTid
	 where(rsl_built_in(boolean(BTid)) -> SALTypeExprout)
	 -- cc
	 BTid'Lifted_Tid -> tid(LTid)
	 LTid'Pos -> LPos
	 LTid'Ident -> LId
	 where(user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, LTid)), bool)) -> LiftedType)

  'rule' SAL_Gen_Type_Expr(Pos, int -> SALTypeExprout, LiftedType):
	 Default_Int_Tid -> Tid
	 where(rsl_built_in(integer(Tid)) -> SALTypeExprout)
	 -- cc
	 Tid'Lifted_Tid -> tid(LTid)
	 LTid'Pos -> LPos
	 LTid'Ident -> LId
	 where(user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, LTid)), int)) -> LiftedType)

  'rule' SAL_Gen_Type_Expr(Pos, nat -> SALTypeExprout, LiftedType):
	 Default_Nat_Tid -> NTid
	 where(rsl_built_in(natural(NTid)) -> SALTypeExprout)
	 -- cc
	 Default_Int_Tid -> Tid
	 Tid'Lifted_Tid -> tid(LTid)
	 LTid'Pos -> LPos
	 LTid'Ident -> LId
	 where(user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, LTid)), nat)) -> LiftedType)


  'rule' SAL_Gen_Type_Expr(Pos, fin_set(TypeExprFS) -> SALNonQualExpr, LiftedType):
	 SAL_Gen_Type_Expr(Pos, TypeExprFS -> SALQualTypeExpr, SAL_MTE)
	 -- Check if there is already a set of this type:
	 SAL_Check_Defined_Set(Pos,TypeExprFS -> OptTid)
	 (|
	    -- There is a set of this type:
	    where(OptTid -> tid(SetTid))
--Putmsg("Existing lifted set type for ")
--Print_type(TypeExprFS)
--Putmsg(" is ")
--SetTid'Lifted_Tid -> tid(LTid)
--SAL_Print_Tid(LTid)
--Putnl
	 ||
	    -- There is no set of this type, generate a new one:
	    -- Increasing the pos for uniqueness:
	    IncreaseCol(Pos -> NewPos)
	    Gen_Set_Type(NewPos, TypeExprFS -> SetTid)
	 |)
	 where(rsl_built_in(sal_finite_set(SetTid,SALQualTypeExpr)) -> SALNonQualExpr)
	 -- cc version:
	 SetTid'Lifted_Tid -> tid(LSetTid)
	 LSetTid'Ident -> LId
	 LSetTid'Pos -> LPos
	 where(user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, LSetTid)), fin_set(TypeExprFS))) -> LiftedType)

  'rule' SAL_Gen_Type_Expr(Pos, fin_list(TypeExprFL) -> SALNonQualExpr, SALNonQualExpr):
	 where(SAL_TYPE_EXPR'nil -> SALNonQualExpr)
	 Puterror(Pos)
	 Putmsg("List type not supported")
	 Putnl()

/*	 -- In case we want to process it...
	 SAL_Gen_Type_Expr(Pos, TypeExprFL -> SALQualTypeExpr)
	 -- Check if there is already a list of this type:
	 SAL_Check_Defined_List(Pos, TypeExprFL -> OptTid)
	 (|
	    -- There is a list of this type:
	    where(OptTid -> tid(ListTid))
	 ||
	    -- There is no list of this type, generate a new one:
	    (|
	       where(TypeExprFL -> defined(Typeid,_))
	       Typeid'Ident -> Ident
	    ||
	       where(SALQualTypeExpr -> rsl_built_in(integer(Tid)))
	       Tid'Ident -> Ident
	    ||
	       where(SALQualTypeExpr -> rsl_built_in(boolean(Tid)))
	       Tid'Ident -> Ident
	    ||
               Puterror(Pos)
	       Putmsg("Trying to define a list of a non supported type in the SAL translator.\n")
	       SAL_Gen_Type_Ident(-> Ident)
	    |)
	    SAL_Gen_New_List_Type(Ident, TypeExprFL -> ListTid)
	 |)
	 where(rsl_built_in(sal_list_type(ListTid,SALQualTypeExpr)) -> SALNonQualExpr) 
*/


  'rule' SAL_Gen_Type_Expr(Pos, fin_map(Dom, Rng) -> SALNonQualExpr, LiftedType):
	 SAL_Gen_Type_Expr(Pos, Dom  -> DomSAL, SAL_MDom)
	 SAL_Gen_Type_Expr(Pos, Rng -> RngSAL, SAL_MRng)
	 -- Check if there is already a map of this type:
	 SAL_Check_Defined_Map(Pos, Dom, Rng -> OptTid)
	 (|
	    -- There is a map of this type:
	    where(OptTid -> tid(MapTid))
	 ||
	    -- There is no map of this type, generate a new one:
	    -- Increasing the pos for uniqueness:
	    IncreaseCol(Pos -> NewPos)
	    Gen_Map_Type(NewPos, Dom, Pos, Rng -> MapTid)
	 |)
	 where(rsl_built_in(sal_finite_map(MapTid,DomSAL, RngSAL)) -> SALNonQualExpr)
	 -- cc version:
	 MapTid'Lifted_Tid -> tid(LMapTid)
	 LMapTid'Ident -> LId
	 LMapTid'Pos -> LPos
	 where(user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, LMapTid)), fin_map(Dom, Rng))) -> LiftedType)

--------------------------------------------------------------------------
-- User-defined types:
--------------------------------------------------------------------------

  'rule' SAL_Gen_Type_Expr(Pos, Type: product(ProdType) -> SALNonQualExpr, LiftedType):
	 Gen_SAL_Tuple_List(Pos, ProdType, nil, nil -> TupleList, LTupleList)
	 where(user_defined(sal_tuple_type(TupleList)) -> SALNonQualExpr)
	 -- cc
	 SAL_Check_Defined_Maximal_Type(Type -> OptTid)
	 (|
	     -- There exists a product type that maximally matches this one
	     where(OptTid -> tid(ProdTid))
	     ProdTid'Pos -> P
	     ProdTid'Ident -> Id
	     where(user_defined(sal_cc_type(type_refs(sal_defined(P, Id, ProdTid)), Type)) -> LiftedType)
	 ||
	     -- Generating a new Product type declaration
	     SAL_Gen_Ident_From_Type(user_defined(sal_tuple_type(LTupleList)) -> Id)
	     SAL_Current_CC_Cid -> CCid
	     New_SAL_type_id_with_Cid(Pos, Id, CCid, Type -> ProdTid)
	     ProdTid'Lifted_Tid -> tid(LProdTid)
	     LProdTid'Declaration <- sal_type_decl(Id, ProdTid, user_defined(sal_tuple_type(LTupleList)))
	     LProdTid'TExpr <- user_defined(sal_tuple_type(LTupleList))
	     Maxtype(Type -> MaximalType)
	     Add_Lifted_to_Global(MaximalType, LProdTid)
	     LProdTid'Ident -> Ident
	     where(user_defined(sal_cc_type(type_refs(sal_defined(Pos,Ident, LProdTid)), Type)) -> LiftedType)
	 |)
	 

  'rule' SAL_Gen_Type_Expr(Pos, Type : fun(ParamType, A1, Result) -> SALNonQualExpr, LiftedType):
	 SAL_Gen_Type_Expr(Pos, ParamType -> DomType, LDom)
	 where(Result -> result(TypeExpr, _, _, _, _))
	 SAL_Gen_Type_Expr(Pos, TypeExpr -> QResult, LRng)
	 where(user_defined(sal_fun_type(DomType, QResult)) -> SALNonQualExpr)
	 -- cc
	 SAL_Check_Defined_Maximal_Type(Type -> OptTid)
	 (|
	     -- There exists a product type that maximally matches this one
	     where(OptTid -> tid(ProdTid))
	     ProdTid'Pos -> P
	     ProdTid'Ident -> Id
	     where(user_defined(sal_cc_type(type_refs(sal_defined(P, Id, ProdTid)), Type)) -> LiftedType)
	 ||
	     -- Generating a new Product type declaration
	     SAL_Gen_Ident_From_Type(user_defined(sal_fun_type(LDom, LRng)) -> Id)
	     SAL_Current_CC_Cid -> CCid
	     New_SAL_type_id_with_Cid(Pos, Id, CCid, Type -> ProdTid)
	     ProdTid'Lifted_Tid -> tid(LProdTid)
	     LProdTid'Declaration <- sal_type_decl(Id, ProdTid, user_defined(sal_fun_type(LDom, LRng)))
	     LProdTid'TExpr <- user_defined(sal_fun_type(LDom, LRng))
	     Maxtype(Type -> MaximalType)
	     Add_Lifted_to_Global(MaximalType, LProdTid)
	     LProdTid'Ident -> Ident
	     where(user_defined(sal_cc_type(type_refs(sal_defined(Pos,Ident, LProdTid)), Type)) -> LiftedType)
	 |)

-- subtype is {| x : T :- x isin {a .. b} |}, T is Int or Nat
-- SAL type is [a .. b]
  'rule' SAL_Gen_Type_Expr(Pos, Type : subtype(Typing, Restriction) -> SALNonQualExpr, LiftedType):
	 where(Typing -> single(_, B, T))
	 (| eq(T, int) || eq(T, nat) |)
	 where(Restriction -> restriction(_,infix_occ(_, E, I, nil, ranged_set(_, L, R))))
	 Matches_binding(E, B)
	 Id_of_isin_set -> I1
	 eq(I, I1)
	 Gen_SAL_Expr(L, normal, int -> SL,_)
	 Gen_SAL_Expr(R, normal, int -> SR,_)
	 where(user_defined(sal_ranged_type(SL, SR)) -> SALNonQualExpr)
	 -- cc
	 SAL_Process_Typing(Typing -> Ident, TExpr, Namespace, BaseType)
	 Gen_SAL_Restriction(Restriction, bool -> _, CC_Restriction)
	 SAL_Check_Defined_Maximal_Type(Type -> OptTid)
	 (|
	     -- There exists a product type that maximally matches this one
	     where(OptTid -> tid(ProdTid))
	     ProdTid'Pos -> P
	     ProdTid'Ident -> Id
	     where(user_defined(sal_cc_type(type_refs(sal_defined(P, Id, ProdTid)), Type)) -> LiftedType)
	 ||
	     -- Generating a new Product type declaration
	     SAL_Gen_Ident_From_Type(BaseType -> Id)
	     SAL_Current_CC_Cid -> CCid
	     New_SAL_type_id_with_Cid(Pos, Id, CCid, Type -> ProdTid)
	     ProdTid'Lifted_Tid -> tid(LProdTid)
	     where(BaseType -> user_defined(sal_cc_type(type_refs(sal_defined(LPos,LId,Tid11)), _)))
	     where(user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, Tid11)), Type)) -> LiftedType1)
	     LProdTid'Declaration <- sal_type_decl(Id, ProdTid, LiftedType1)
	     LProdTid'TExpr <- LiftedType1
	     Maxtype(Type -> MaximalType)
	     Add_Lifted_to_Global(MaximalType, LProdTid)
	     LProdTid'Ident -> Ident1
	     where(user_defined(sal_cc_type(type_refs(sal_defined(Pos,Ident1, LProdTid)), Type)) -> LiftedType)
	 |)

-- subtype is {| x : Nat :- x <= a} |}
-- SAL type is [0 .. a]
-- subtype is {| x : Nat :- x < a} |}
-- SAL type is [0 .. a-1]
  'rule' SAL_Gen_Type_Expr(Pos, Type : subtype(Typing, Restriction) -> SALNonQualExpr, LiftedType):
	 where(Typing -> single(_, B, nat))
	 where(Restriction -> restriction(_,infix_occ(_, E, I, nil, A)))
	 Matches_binding(E, B)
	 (|
	   Id_of_le_int -> I1
	   eq(I, I1)
	   string_to_id("0" -> Zid)
	   where(sal_literal(integ(Zid)) -> SL)
	   Gen_SAL_Expr(A, normal, int -> SR,_)
	 ||
	   Id_of_lt_int -> I1
	   eq(I, I1)
	   string_to_id("0" -> Zid)
	   where(sal_literal(integ(Zid)) -> SL)
	   Id_of_minus_inf_int -> I2
	   string_to_id("1" -> Oneid)
	   where(VALUE_EXPR'literal_expr(Pos, int(Oneid)) -> One)
	   where(VALUE_EXPR'infix_occ(Pos, A, I2, nil, One) -> R)
	   Gen_SAL_Expr(R, normal, int -> SR,_)
	 |)
	 where(user_defined(sal_ranged_type(SL, SR)) -> SALNonQualExpr)
	 -- cc
	 SAL_Process_Typing(Typing -> Ident, TExpr, Namespace, BaseType)
	 Gen_SAL_Restriction(Restriction, bool -> _, CC_Restriction)
	 SAL_Check_Defined_Maximal_Type(Type -> OptTid)
	 (|
	     -- There exists a product type that maximally matches this one
	     where(OptTid -> tid(ProdTid))
	     ProdTid'Pos -> P
	     ProdTid'Ident -> Id
	     where(user_defined(sal_cc_type(type_refs(sal_defined(P, Id, ProdTid)), Type)) -> LiftedType)
	 ||
	     -- Generating a new Product type declaration
	     SAL_Gen_Ident_From_Type(BaseType -> Id)
	     SAL_Current_CC_Cid -> CCid
	     New_SAL_type_id_with_Cid(Pos, Id, CCid, Type -> ProdTid)
	     ProdTid'Lifted_Tid -> tid(LProdTid)
	     where(BaseType -> user_defined(sal_cc_type(type_refs(sal_defined(LPos,LId,Tid11)), _)))
	     where(user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, Tid11)), Type)) -> LiftedType1)
	     LProdTid'Declaration <- sal_type_decl(Id, ProdTid, LiftedType1)
	     LProdTid'TExpr <- LiftedType1
	     Maxtype(Type -> MaximalType)
	     Add_Lifted_to_Global(MaximalType, LProdTid)
	     LProdTid'Ident -> Ident1
	     where(user_defined(sal_cc_type(type_refs(sal_defined(Pos,Ident1, LProdTid)), Type)) -> LiftedType)
	 |)

  'rule' SAL_Gen_Type_Expr(Pos, Type : subtype(Typing, Restriction) -> SALNonQualExpr, LiftedType):
	 SAL_Process_Typing(Typing -> Ident, TExpr, Namespace, BaseType)
	 Gen_SAL_Restriction(Restriction, bool -> SALRestriction, CC_Restriction)
	 where(user_defined(sal_subtype(Ident,TExpr,Namespace,SALRestriction)) -> SALNonQualExpr)
	 -- cc
	 SAL_Check_Defined_Maximal_Type(Type -> OptTid)
	 (|
	     -- There exists a type that maximally matches this one
	     where(OptTid -> tid(ProdTid))
	     ProdTid'Pos -> P
	     ProdTid'Ident -> Id
	     where(user_defined(sal_cc_type(type_refs(sal_defined(P, Id, ProdTid)), Type)) -> LiftedType)
	 ||
	     Maxtype(Type -> MaximalType)
	     SAL_Gen_Type_Expr(Pos, MaximalType -> _, LiftedType)
where(LiftedType -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,LProdTid)), _)))



	     -- Generating a new type declaration
--	     SAL_Gen_Ident_From_Type(BaseType -> Id)
--	     SAL_Current_CC_Cid -> CCid
--	     New_SAL_type_id_with_Cid(Pos, Id, CCid, Type -> ProdTid)
--	     ProdTid'Lifted_Tid -> tid(LProdTid)
--	     where(BaseType -> user_defined(sal_cc_type(type_refs(sal_defined(LPos,LId,Tid11)), _)))
--	     where(user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, Tid11)), Type)) -> LiftedType1)
--	     LProdTid'Declaration <- sal_type_decl(Id, ProdTid, LiftedType1)
--	     LProdTid'TExpr <- LiftedType1
--	     Maxtype(Type -> MaximalType)
--	     Add_Lifted_to_Global(MaximalType, LProdTid)
--	     LProdTid'Ident -> Ident1
--	     where(user_defined(sal_cc_type(type_refs(sal_defined(Pos,Ident1, LProdTid)), Type)) -> LiftedType)
	 |)


  'rule' SAL_Gen_Type_Expr(Pos, bracket(TypeExpr) -> SALNonQualExpr, LiftedType):
	 SAL_Gen_Type_Expr(Pos, TypeExpr -> SALTypeElem, LiftedType1)
	 where(user_defined(sal_bracket_type(SALTypeElem)) -> SALNonQualExpr)
	 where(user_defined(sal_cc_type(user_defined(sal_bracket_type(LiftedType1)), bracket(TypeExpr))) -> LiftedType)

----------------------------------------------------------------------------------
-- TYPE REFERENCES:
----------------------------------------------------------------------------------

  'rule' SAL_Gen_Type_Expr(Pos, Type1 : defined(Typeid, OptQual) -> SALNonQualExpr, LiftedType):


	 -- This rule processes the type references...
	 Typeid'Type -> Type
	 Typeid'Pos -> Pos2
	 Typeid'Ident -> Ident
--Print_id(Ident)
--Putnl()
--[|
--where(Type -> sort(record(_)))
--Putmsg("Starting record\n")
--Global_Tid_Table -> X
--print(X)
--|]

	 look_up_type_id(Pos2 -> OptTid)
	 (|
             where(OptTid -> tid(ReferredTid))
	 ||
	     Putmsg("Internal Error! Type identifier not found\n")
	     New_SAL_type_id(Pos,Ident, any -> ReferredTid)
	 |)
	 -- TYPE REFERENCES WITHIN RECORDS and VARIANTS
	 (| -- undef_type
	   where(Type -> undef_type)
	   where(SAL_TYPE_EXPR'nil -> SALNonQualExpr)
	   Putmsg("Internal error, Undefined type found")
	   Putnl()
	 || -- Abstract
	   where(Type -> sort(abstract))
	   where(type_refs(sal_defined(Pos2,Ident,ReferredTid)) -> SALNonQualExpr)
	 || -- Record
	   where(Type -> sort(record(_))) 
	   where(type_refs(sal_defined(Pos2,Ident,ReferredTid)) -> SALNonQualExpr)
	 || -- Variant
	   where(Type -> sort(variant(_)))
	   where(type_refs(sal_defined(Pos2,Ident,ReferredTid)) -> SALNonQualExpr)
	 || -- 
	   where(Type -> sort(union(_)))
	   where(SAL_TYPE_EXPR'nil -> SALNonQualExpr)
	   Puterror(Pos)
	   Putmsg("Union types not supported")
	   Putnl()
	 || -- abbrev
	   where(Type -> abbrev(_))
	   -- abbreviation
	   Typeid'Def -> abbreviation(TypeExpr)
	   where(type_refs(sal_defined(Pos2,Ident,ReferredTid)) -> SALNonQualExpr)
	 |)
	 -- cc
	 SAL_Check_Defined_Maximal_Type(Type1 -> OptTid1)
	 (|
	    where(OptTid1 -> tid(ProdTid))
	    ProdTid'Pos -> P
	    ProdTid'Ident -> Id
	    where(user_defined(sal_cc_type(type_refs(sal_defined(P, Id, ProdTid)), Type1)) -> LiftedType)
	 ||
	    -- I want to use the abbreviation otherwise:
	    ReferredTid'Lifted_Tid -> tid(LTid)
	    LTid'Pos -> Pos3
	    LTid'Ident -> LIdent
	    where(user_defined(sal_cc_type(type_refs(sal_defined(Pos3, LIdent, LTid)), Type1)) -> LiftedType)
	    Add_Lifted_to_Global(Type1, LTid)
	 |)

   'rule' SAL_Gen_Type_Expr(Pos, named_type(Name) -> SALNonQualExpr, SALNonQualExpr):
          --Resolve_type(named_type(Name) -> Resolved)
          --SAL_Gen_Type_Expr(Pos, Resolved -> SALNonQualExpr, SALNonQualExpr2)
          --print("Error - Debug")
	  Puterror(Pos)
          Putmsg("Internal error: Unresolved type found\n")
	  --print(named_type(Name))
          Print_name(Name)
--Resolve_type(named_type(Name) -> T2)
--Print_type(T2)
	  where(SAL_TYPE_EXPR'nil -> SALNonQualExpr)


------------------------------------------------------------------------------
-- SPECIAL INDICATORS:
------------------------------------------------------------------------------

  'rule' SAL_Gen_Type_Expr(Pos, any -> SALTypeExprout, SALTypeExprout):
	 where(SAL_TYPE_EXPR'nil -> SALTypeExprout)
	 Puterror(Pos)
	 Putmsg("Internal error: ANY type found when generating type expression\n")

  'rule' SAL_Gen_Type_Expr(Pos, none -> SALTypeExprout, SALTypeExprout):
	 where(SAL_TYPE_EXPR'nil -> SALTypeExprout)
	 Puterror(Pos)
	 Putmsg("Internal error: NONE type found when generating type expression\n")

  'rule' SAL_Gen_Type_Expr(Pos, poly(Num) -> SALTypeExprout, SALTypeExprout):
	 -- This is just for operations (like '=') and the type is not
	 -- needed so far (but I'm not sure about it yet)
	 -- CONSIDER the case of equality among integers?
	 where(SAL_TYPE_EXPR'poly -> SALTypeExprout)

  'rule' SAL_Gen_Type_Expr(Pos, array(T1, T2) -> SALNonQualExpr, LiftedType) --rsl_built_in(sal_array(T1A,T2A)), rsl_built_in(sal_array(T1B,T2B))):
         SAL_Gen_Type_Expr(Pos, T1 -> T1A, T1B)
         SAL_Gen_Type_Expr(Pos, T2 -> T2A, T2B)
--         Maxtype(T1 -> TMax)
--         (|
--           eq(TMax, int)
           SAL_Check_Defined_Array(Pos, T1, T2 -> OptTid)
           (|
             where(OptTid -> tid(ArrayTid))
           ||
             IncreaseCol(Pos -> NewPos)
             Gen_Array_Type(NewPos, T1, Pos, T2 -> ArrayTid)
           |)
  	   where(rsl_built_in(sal_array(ArrayTid, T1A, T2A)) -> SALNonQualExpr)
	   -- cc version:
	   ArrayTid'Lifted_Tid -> tid(LArrayTid)
	   LArrayTid'Ident -> LId
	   LArrayTid'Pos -> LPos
	   where(user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, LArrayTid)), array(T1, T2))) -> LiftedType)
--         ||
           
--         ||
--           Puterror(Pos)
--print(T1)
--print(TMax)
--           Putmsg("Only ints or subtype of int are accepted in index of arrays, but found ")
--           Print_type(T1)
--           Putmsg(".\n")
--           where(unsupported_type -> SALNonQualExpr)
--           where(unsupported_type -> LiftedType)
--         |)

  'rule' SAL_Gen_Type_Expr(Pos, fin_map(Dom, Rng) -> SALNonQualExpr, LiftedType):
	 SAL_Gen_Type_Expr(Pos, Dom  -> DomSAL, SAL_MDom)
	 SAL_Gen_Type_Expr(Pos, Rng -> RngSAL, SAL_MRng)
	 -- Check if there is already a map of this type:
	 SAL_Check_Defined_Map(Pos, Dom, Rng -> OptTid)
	 (|
	    -- There is a map of this type:
	    where(OptTid -> tid(MapTid))
	 ||
	    -- There is no map of this type, generate a new one:
	    -- Increasing the pos for uniqueness:
	    IncreaseCol(Pos -> NewPos)
	    Gen_Map_Type(NewPos, Dom, Pos, Rng -> MapTid)
	 |)
	 where(rsl_built_in(sal_finite_map(MapTid,DomSAL, RngSAL)) -> SALNonQualExpr)
	 -- cc version:
	 MapTid'Lifted_Tid -> tid(LMapTid)
	 LMapTid'Ident -> LId
	 LMapTid'Pos -> LPos
	 where(user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, LMapTid)), fin_map(Dom, Rng))) -> LiftedType)


-- debug
  'rule' SAL_Gen_Type_Expr(P, T -> nil, nil)
	 PrintPos(P)
	 print("Debugging pred. activated with type ")
	 Print_type(T)
	 Putnl()
	 print(T)

--------------------------------------------------
'action' Gen_SAL_Tuple_List(POS, PRODUCT_TYPE, SAL_TUPLE_ELEMS, SAL_TUPLE_ELEMS -> SAL_TUPLE_ELEMS, SAL_TUPLE_ELEMS)

  'rule' Gen_SAL_Tuple_List(Pos, list(Type1, ProdTypeTail), TupleList, LTList -> TupleListout, L_TupleListOut):
	 SAL_Gen_Type_Expr(Pos, Type1 -> SALTypeExpr1, SAL_LTE)
	 SAL_Insert_Tuple(sal_tuple(SALTypeExpr1), TupleList -> TupleList1)
	 SAL_Insert_Tuple(sal_tuple(SAL_LTE), LTList -> LTList1)
	 Gen_SAL_Tuple_List(Pos, ProdTypeTail, TupleList1, LTList1 -> TupleListout, L_TupleListOut)

  'rule' Gen_SAL_Tuple_List(Pos, nil, TupleList, LTList -> TupleList, LTList):


--------------------------------------------------
'action' Gen_SAL_Restriction(RESTRICTION, TYPE_EXPR -> SAL_VALUE_EXPR, SAL_VALUE_EXPR)

  'rule' Gen_SAL_Restriction(restriction(Pos, ValueExpr), TypeExpr ->  SALRestriction, SAL_CC_Restriction):
	 Gen_SAL_Expr(ValueExpr, normal, TypeExpr -> SALRestriction, SAL_CC_Restriction1)
	 -- cc
	 -- Adding the is_true part before the actual restriction (that has type Bool_cc)
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	 where(sal_esp_unary_prefix_occ(val_id(SAL_Op), SAL_CC_Restriction1) -> SAL_CC_Restriction)

  'rule' Gen_SAL_Restriction(nil, _ -> SALRestriction, SAL_CC_Restriction):
	 DefaultPos(-> P)
	 Gen_SAL_Restriction(restriction(P, literal_expr(P, bool_true)), bool -> SALRestriction, SAL_CC_Restriction)


--------------------------------------------------
--  RSL Value Expression  ==> SAL Expression
--------------------------------------------------

--------------------------------------------------
'action' Gen_SAL_ExprPairs(VALUE_EXPR_PAIRS, SAL_VALUE_EXPR_PAIRS, SAL_VALUE_EXPR_PAIRS,
			TYPE_EXPR, TYPE_EXPR -> SAL_VALUE_EXPR_PAIRS, SAL_VALUE_EXPR_PAIRS)

  'rule' Gen_SAL_ExprPairs(list(ValueExprPair, ValueExprPairsTail),
			    SALExprPairs, SAL_CC_ExprPairs, DomType, RngType -> SALExprPairsout, CC_SALExprPairsout):
	 
	 Gen_SAL_ExprPair(ValueExprPair, DomType, RngType -> SALExprPair, SAL_CC_ExprPair)
	 SAL_Insert_ExprPair(SALExprPair, SALExprPairs -> SALExprPairs1)
	 -- cc
	 SAL_Insert_ExprPair(SAL_CC_ExprPair, SAL_CC_ExprPairs -> SAL_CC_ExprPairs1)
	 Gen_SAL_ExprPairs(ValueExprPairsTail, SALExprPairs1, SAL_CC_ExprPairs1, DomType, RngType -> 
					       SALExprPairsout, CC_SALExprPairsout)

  'rule' Gen_SAL_ExprPairs(nil, SALExprPairs, SAL_CC_Expr_Pairs,_,_ -> SALExprPairs, SAL_CC_Expr_Pairs):


--------------------------------------------------
'action' Gen_SAL_ExprPair(VALUE_EXPR_PAIR,
			TYPE_EXPR, TYPE_EXPR -> SAL_VALUE_EXPR_PAIR, SAL_VALUE_EXPR_PAIR)

  'rule' Gen_SAL_ExprPair(pair(LeftValueExpr, RightValueExpr), DomType, RngType -> SALExprPairout, SAL_CC_ExprPairout):
	 Gen_SAL_Expr(LeftValueExpr, normal, DomType -> LeftSALExpr, L_CC_Expr)
	 Gen_SAL_Expr(RightValueExpr, normal, RngType -> RightSALExpr, R_CC_Expr)
	 where(SAL_VALUE_EXPR_PAIR'pair(LeftSALExpr, RightSALExpr) -> SALExprPairout)
	 -- cc outcome:
	 where(SAL_VALUE_EXPR_PAIR'pair(L_CC_Expr, R_CC_Expr) -> SAL_CC_ExprPairout)


---------------------------------------------------------------------------------------
-- Gen_SAL_Exprs
---------------------------------------------------------------------------------------
-- Generates a list of expressions (from its RSL counterpart)
-- NOTE: The SAME TYPE is used for all of them!
---------------------------------------------------------------------------------------
'action' Gen_SAL_Exprs(VALUE_EXPRS, SAL_VALUE_EXPRS, SAL_VALUE_EXPRS, TYPE_EXPR, -> SAL_VALUE_EXPRS, SAL_VALUE_EXPRS)

  'rule' Gen_SAL_Exprs(list(ValueExpr, ValueExprsTail), SALExprs, SAL_CC_Exprs, TExpr -> SALExprsout, SAL_CC_Exprsout):
	 Gen_SAL_Expr(ValueExpr, normal, TExpr -> SALExpr, SAL_CC_Expr)
	 SAL_Insert_Expr(SALExpr, SALExprs -> SALExprs1)
	 SAL_Insert_Expr(SAL_CC_Expr, SAL_CC_Exprs -> SAL_CC_Exprs1)
	 Gen_SAL_Exprs(ValueExprsTail, SALExprs1, SAL_CC_Exprs1, TExpr -> SALExprsout, SAL_CC_Exprsout)

  'rule' Gen_SAL_Exprs(nil, SALExprs, SAL_CC_Exprs, _ -> SALExprs, SAL_CC_Exprs):

--------------------------------------------------------------------------------------------------
-- This function differs from the one above in that it unfolds the type it receives (it is supposed
-- to be the content of a product) and uses the unfolded type to generate the individual expressions...
-- It is used only to process product expressions
---------------------------------------------------------------------------------------------------
'action' Gen_SAL_Exprs_for_product(VALUE_EXPRS, SAL_VALUE_EXPRS, SAL_VALUE_EXPRS, PRODUCT_TYPE, -> SAL_VALUE_EXPRS, SAL_VALUE_EXPRS)

  'rule' Gen_SAL_Exprs_for_product(list(ValueExpr, ValueExprsTail), SALExprs, SAL_CC_Exprs, list(H, Tail) -> SALExprsout, SAL_CC_Exprsout):
	 Gen_SAL_Expr(ValueExpr, normal, H -> SALExpr, SAL_CC_Expr)
	 SAL_Insert_Expr(SALExpr, SALExprs -> SALExprs1)
	 SAL_Insert_Expr(SAL_CC_Expr, SAL_CC_Exprs -> SAL_CC_Exprs1)
	 Gen_SAL_Exprs_for_product(ValueExprsTail, SALExprs1, SAL_CC_Exprs1, Tail -> SALExprsout, SAL_CC_Exprsout)

  'rule' Gen_SAL_Exprs_for_product(nil, SALExprs, SAL_CC_Exprs, nil -> SALExprs, SAL_CC_Exprs):

-------------------------------------------------------------------------------------------------
-- Gen_SAL_Expr
-------------------------------------------------------------------------------------------------
-- This function is the interface to the expression translator...
-- Its function is to use the EXTENDED TYPE CHECKING RULES before invoking the proper expression
-- translation function.
-- The advantage of this approach is the centralization of the acces to the type check functionlity
-- (instead of replicating it on every function...)
-- The function also generates a second translation for the same expression. This second translation
-- is meant to be used by the cc-generation routines. In particular, it replaces all value occurrences
-- with the proper constructor/destructor in the context of the lifted type system:
-- For example:
-- x + 1 (where x is of Int type and the result of the expression is also Int)
-- will be translated (in the second expression) as:
-- Int_(val(x) + 1);
--------------------------------------------------------------------------------------------------

'action' Gen_SAL_Expr(VALUE_EXPR, EXPR_CONTEXT, TYPE_EXPR -> SAL_VALUE_EXPR, -- non-cc version
							     SAL_VALUE_EXPR) -- cc version

  'rule' Gen_SAL_Expr(Expr, Expr_Context, Type -> SAL_Expr, SAL_CC_Expr)
	 (| -- evoids analyzing no-val exprs (it is not manageable by the the resolver and the
	    -- SAL type checker invokes it)
	    where(Expr -> no_val)
	    where(SAL_VALUE_EXPR'nil -> SAL_Expr)
	    where(SAL_Expr -> SAL_CC_Expr)
	 ||
	    SAL_Get_Expr_Pos(Expr -> Pos)
	    Type_Check(Pos, Expr, Expr_Context, Type)
	    Gen_SAL_Expr_(Expr, Type -> SAL_Expr, SAL_CC_Expr)
	 |)

---------------------------------------------------------------------------------------------
-- This is the actual value translator routine...
---------------------------------------------------------------------------------------------

'action' Gen_SAL_Expr_(VALUE_EXPR, TYPE_EXPR -> SAL_VALUE_EXPR, SAL_VALUE_EXPR)

  'rule' Gen_SAL_Expr_(literal_expr(Pos, ValueLit), TExpr -> SALExprout, CC_Expr):
	 Gen_SAL_literal_expr(Pos, ValueLit, TExpr -> SALExprout, CC_Expr)
/*
  'rule' Gen_SAL_Expr_(named_val(_, name(Pos, IdorOp)), TExpr -> SALExprout):
Putmsg("Gen_Sal_Expr_2\n")
	 Gen_SAL_Id_Op(Pos, IdorOp, TExpr, none -> IdOp, _) -- it is just a name... no need for the distinction here
	 where(SAL_VALUE_EXPR'sal_named_val(id_op(IdOp)) -> SALExprout)
*/ -- this shouldn't be here... named_vals are UNRESOLVED!

  'rule' Gen_SAL_Expr_(pre_name(Pos, Name), _ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("pre name not supported")
	 Putnl()

  'rule' Gen_SAL_Expr_(chaos(Pos),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("chaos not supported")
	 Putnl()

  'rule' Gen_SAL_Expr_(skip(Pos),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("skip not supported")
	 Putnl()

  'rule' Gen_SAL_Expr_(stop(Pos),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("stop not supported")
	 Putnl()
--	 where(SAL_VALUE_EXPR'stop -> SALExprout)

  'rule' Gen_SAL_Expr_(swap(Pos),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("swap not supported")
	 Putnl()

  'rule' Gen_SAL_Expr_(product(Pos, ValueExprs), TExpr -> SALExprout, CC_Expr):
	 (|
	    Type_is_product(TExpr -> PT)
	    Gen_SAL_Exprs_for_product(ValueExprs, nil, nil, PT -> SALExprs, SAL_CC_Exprs)
	    where(SAL_VALUE_EXPR'sal_product(SALExprs) -> SALExprout)
	    where(SAL_VALUE_EXPR'sal_product(SAL_CC_Exprs) -> CC_Expr)
	 ||
	    Puterror(Pos)
	    Putmsg("Internal error: Unexpected type found in product expression\n")
	    where(SAL_VALUE_EXPR'no_val -> SALExprout)
	    where(SALExprout -> CC_Expr)
	 |)

  'rule' Gen_SAL_Expr_(ranged_set(Pos, LeftValueExpr, RightValueExpr), TExpr -> SALExprout, CC_Expr):
	 Type_is_set(TExpr -> DomType)
         SAL_Gen_Type_Expr(Pos, DomType -> SALDomType, SALDomType_CC)
	 Gen_SAL_Expr(LeftValueExpr, normal, DomType -> LeftSALExpr, L_CC_Expr)
	 Gen_SAL_Expr(RightValueExpr, normal, DomType -> RightSALExpr, R_CC_Expr)
	 where(SAL_VALUE_EXPR'sal_ranged_set(LeftSALExpr, RightSALExpr, SALDomType) -> SALExprout)
	 -- Generating something like:
	 -- IF ALL (x: {| x: SAL_maximal(T) :- x => LeftValueExpr /\ x <= RightValueExpr |}) : insubtype(x) THEN S ELSE nav ENDIF
	 -- where:
	 -- S = LAMBDA (x:T) x >= a AND x <= b
	 -- Creating the ALL expression:
	 DefaultPos(-> P)
	 string_to_id("x_" -> Ident)
	 SAL_Gen_Type_Expr(Pos, DomType -> _, SALType)
	 SAL_Gen_Type_Expr(Pos, TExpr -> _, SetType)
	 Openenv()
	 -- trick to update the environment and add 'x_' to the scope so Isin_subtype doesn't have problems...
	 Define_value_binding(single(Pos,id_op(Ident)), any)
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(Pos, VE -> value_id(I))
	 where(VALUE_EXPR'val_occ(Pos, I, nil) -> Occ)
	 Isin_subtype(Occ, DomType -> SubtypeCond)

	 Id_of_le_int -> LeVid
	 Id_of_ge_int -> GeVid
	 where(VALUE_EXPR'infix_occ(Pos, Occ,GeVid,nil,LeftValueExpr) -> LE_Expr)
	 where(VALUE_EXPR'infix_occ(Pos, Occ,LeVid,nil,RightValueExpr) -> GE_Expr)
	 where(VALUE_EXPR'ax_infix(Pos, LE_Expr, and, GE_Expr, Pos) -> AndExpr)
	 -- generating the proper subtype:
	 where(TYPING'single(Pos, single(Pos, id_op(Ident)), DomType) -> Typing)
	 where(TYPE_EXPR'subtype(Typing, restriction(Pos, AndExpr)) -> GenSubType) -- TODO: Wrong type.
	 
	 where(VALUE_EXPR'quantified(Pos, all, list(single(Pos, single(Pos, id_op(Ident)), GenSubType), nil), restriction(Pos,SubtypeCond)) -> RSL_All)
	 -- Restoring the environment (removing the trick's effects)
	 Closeenv()
	 (|
	      ne(SubtypeCond, no_val)
	      Gen_SAL_Expr(SubtypeCond, normal, bool -> _, CC_Condition)
	      -- Instead of the following:
	      -- Gen_SAL_Expr(RSL_All, normal, bool -> _, Restriction1)
	      -- We want an speciall treatment here (to generate the subtype {| x: SAL_maximal(T) :- x => LeftValueExpr /\ x <= RightValueExpr |})
	      -- so we COPY here the same procedures from the expression translator for quantified expressions:
	      -----------------------------------------------------------------------------------------------------------
	      Gen_SAL_Quantifier(all -> BindinOp)
	      Gen_SALBindings_from_Typings(list(single(Pos, single(Pos, id_op(Ident)), GenSubType), nil) -> SALBindings, SAL_CC_Bindings, TypeList)
	      Gen_SAL_Restriction(restriction(Pos,SubtypeCond), bool -> _, SAL_CC_Restriction)
	      -- cc
	      -- Introducing a let to overwrite the bindings in the quantifier with a lifted value:
	      SAL_Turn_Bindings_into_Lets(SAL_CC_Bindings, SAL_CC_Restriction, TypeList -> CC_Expr1, UpdatedBindings) -- Need to change something in this
	      -- Using the UpdatedBindings (this introduces the subtyping of the maximal SAL type):
	      --where(SAL_VALUE_EXPR'sal_ranged_set_quantified(BindinOp, bindings(UpdatedBindings), CC_Expr1) -> CC_Expr2)
              where(SAL_VALUE_EXPR'sal_quantified(BindinOp, bindings(UpdatedBindings), CC_Expr1) -> CC_Expr2)
              --where(SAL_VALUE_EXPR'sal_quantified(BindinOp, bindings(SAL_CC_Bindings), CC_Expr1) -> CC_Expr2) -- TODO: Something here, fine now
	      -- wrapping this expression (of type BOOLEAN) to make it of type Bool_cc
	      Default_Bool_Tid -> BTid
	      BTid'Lifted_Tid -> tid(LBTid)
	      LBTid'Constructor -> vid(CVid)
	      where(sal_argument(list(CC_Expr2, nil)) -> Arg)
	      where(sal_funct_applic(sal_esp_value_occ(CVid), Arg) -> Restriction1)
	      --------------------------------------------------------------------------------------------------------
	      -- Creating the restriction (x >= a AND x <= b IMPLIES insubtype(x))
	      LBTid'Pos -> LBPos
	      -- adding 'is_true'
	      where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	      where(sal_esp_unary_prefix_occ(val_id(SAL_Op), Restriction1) -> Condition)
	      Gen_SAL_Expr(AndExpr, normal, bool -> _, LSetRestriction)
	      where(sal_esp_unary_prefix_occ(val_id(SAL_Op), LSetRestriction) -> SetRestriction)
	      where(SAL_VALUE_EXPR'sal_ranged_cc_set(Ident, SetType, SALType, SetRestriction, lifted_int) -> EnumSetExpr)
	      -- Generating the IF expr:
	      Get_Invalid_Insertion_Nav(-> NavValId)
	      SAL_Generate_Result_for_Violation(SetType, sal_esp_value_occ(NavValId) -> WrongApplExpr)
              --where(EnumSetExpr -> CC_Expr)
	      where(sal_if_expr(Condition, EnumSetExpr, nil, else(WrongApplExpr)) -> CC_Expr)
	 ||
	   -- get elem (ie Int) accessor
	   where(SALType -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,ElemTid)),_)))
           ElemTid'Constructor -> vid(ElemConsVid)
	   ElemTid'Lifted_fields -> Fields
           SAL_Find_Accesor_in_Fields(Fields, ElemConsVid -> AccessorVid)
	   where(sal_esp_value_occ(AccessorVid) -> Acc)
	   where(sal_funct_applic(Acc, sal_argument(list(L_CC_Expr, nil))) -> L_CC)
	   where(sal_funct_applic(Acc, sal_argument(list(R_CC_Expr, nil))) -> R_CC)
	   where(SAL_VALUE_EXPR'sal_ranged_set(L_CC, R_CC, lifted_int) -> Set_CC)
	   where(SetType -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,SetTid)),_)))
	   SetTid'Constructor -> vid(SetConsVid)
	   where(sal_funct_applic(sal_esp_value_occ(SetConsVid),
		sal_argument(list(Set_CC, nil))) -> CC_Expr)
	 |)
	 

  'rule' Gen_SAL_Expr_(enum_set(Pos, ValueExprs), TExpr1 -> SALExprout, CC_Expr):
	 Get_Type_of_Value_Expr(enum_set(Pos, ValueExprs) -> T)
	 Type_is_set(TExpr1 -> TExpr)
	 -- getting the tid:
	 -- cwg enough to know there is a set matching this maximally
	 SAL_Check_Defined_Set(Pos,TExpr -> OptTid) -- SetTid
	 (| -- it's a set...
	     where(OptTid -> tid(SetTid))
	     (| -- There is a disambiguation:
	        Get_Current_Disamb(-> disamb(_, ValueExpr, TypeExpr))
		-- And it disambiguates the current value:
		eq(ValueExpr, enum_set(Pos, ValueExprs))
		-- use the type:
		Type_is_set(TypeExpr -> ElemType)
		SAL_Gen_Type_Expr(Pos, ElemType -> SALTExpr, LTExpr)
	     ||
		-- it's not ANY (a type can be determined for the expr)
	        ne(TExpr, any)
		-- Generating the type:
		SAL_Gen_Type_Expr(Pos, TExpr -> SALTExpr, LTExpr)
	     ||
		Puterror(Pos)
		Putmsg("No way to disambiguate the type of the value\n")
		where(SAL_TYPE_EXPR'nil -> SALTExpr)
		where(SAL_TYPE_EXPR'nil -> LTExpr)
	     |)
	     Gen_SAL_Exprs(ValueExprs, nil, nil, TExpr -> SALExprs, SAL_CC_Exprs)
	     where(SAL_VALUE_EXPR'sal_enum_set(SetTid,SALTExpr,SALExprs) -> SALExprout)
	     -- cc
	     SetTid'Lifted_Tid -> tid(LiftedSet)
	     where(SAL_VALUE_EXPR'sal_enum_set(LiftedSet,LTExpr,SAL_CC_Exprs) -> CC_Expr1)
	 ||
	     -- There is no set of this type... creating a new one...
	     Gen_Set_Type(Pos, TExpr -> SetTid)
	     SAL_Gen_Type_Expr(Pos, TExpr -> SALTExpr, CC_Type)
	     Gen_SAL_Exprs(ValueExprs, nil, nil, TExpr -> SALExprs, SAL_CC_Exprs)
	     where(SAL_VALUE_EXPR'sal_enum_set(SetTid,SALTExpr,SALExprs) -> SALExprout)
	     -- cc
	     SetTid'Lifted_Tid -> tid(LiftedSet)
	     LiftedSet'Constructor -> vid(ConstVid)
	     where(SAL_VALUE_EXPR'sal_enum_set(LiftedSet,CC_Type,SAL_CC_Exprs) -> CC_Expr1)
	 |)
	 -- Adding verifications for the elements being added to the set...
	 -- This type correctness verification on insertion ensures (by construction) that the
	 -- set contains valid elements (and avoids quantified verifications...)
	 SAL_Gen_Is_In_Condition(ValueExprs, TExpr -> Condition)
	 (|
	         eq(Condition, no_val)
		 where(CC_Expr1 -> CC_Expr)
	 ||
		 Gen_SAL_Expr(Condition, normal, bool -> _, CC_Condition1)
		 -- make is_true operator
		 Default_Bool_Tid -> BTid
		 BTid'Lifted_Tid -> tid(LBTid)
		 where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
		 where(sal_esp_unary_prefix_occ(val_id(SAL_Op), CC_Condition1) -> CC_Condition)
		 -- cwg generating type tends to generate
		 -- a new non-cc maximal set
--		 SAL_Gen_Type_Expr(Pos, TExpr1 -> _, SetType) 
		 LiftedSet'Ident -> Id
		 where(user_defined(sal_cc_type(type_refs(sal_defined(Pos, Id, LiftedSet)), TExpr1)) -> SetType)
		 Get_Invalid_Insertion_Nav(-> NavValId)
		 SAL_Generate_Result_for_Violation(SetType, sal_esp_value_occ(NavValId) -> WrongApplExpr)
		 where(sal_if_expr(CC_Condition, CC_Expr1, nil, else(WrongApplExpr)) -> CC_Expr)
	 |)

	    
  'rule' Gen_SAL_Expr_(comp_set(Pos, ValueExpr,
		      set_limit(Pos2, Typings, Restriction)), TExpr1 -> SALExprout, CC_Expr):
	 -- try for version where expr matches binding
	 -- ie has form { x | x : T :- p(x) ]
	 where(Typings -> list(Typing, nil))

	 where(Typing -> single(TPos, Binding, TT))
	 Matches_binding(ValueExpr, Binding) --sml.g
	 --
	 Type_is_set(TExpr1 -> DomType)
	 SAL_Gen_Type_Expr(Pos, DomType -> SALType_NonLifted, SALType)
	 Gen_SALBindings_from_Typing(Typing -> SALBindings, SAL_CC_B, ProdType)
	 Gen_SAL_Restriction(Restriction, bool -> SALRestriction, SAL_CC_Restriction)
	 where(SAL_VALUE_EXPR'sal_comp_simp_set(bindings(SALBindings), SALRestriction) -> SALExprout)
	 -- cc
	 -- Generating something like:
	 -- IF ALL (x: SAL_maximal(T) : p(x)): insubtype(x) THEN S ELSE nav ENDIF
	 -- where:
	 -- S = LAMBDA (x:T): p(x)
	 -- Creating the ALL expression:

	 Openenv()
	 -- trick to update the environment and add 'x_' to the scope so Isin_subtype doesn't have problems...
	 Define_value_binding(Binding, TT)
	 (|
	    where(Binding -> single(BPos, id_op(Ident)))
	 ||
	    where(Binding -> product(BPos, list(single(_,id_op(Ident)),_)))
	 |)
	 Get_current_top_values(-> VE)
	 Select_id_by_pos(BPos, VE -> value_id(I))
	 where(VALUE_EXPR'val_occ(Pos, I, nil) -> Occ)
	 Isin_subtype(Occ, DomType -> SubtypeCond)

	 -- In this case we are not interested in using a subtype here. The reason is that
	 -- SAL can not resolve (for the general case) the predicate involved in the subtype (p(x)) we are trying to
	 -- use. Given the approach SAL uses to resolve the subtypes of the form {x: SAL_maximal(T) : p(x)}, p(x) must be resolvable
	 -- at compile time. Even more, if p(x) isn't of the form p(x) = x > v1 /\ x < v2; it might be possible for the model checker
	 -- to never end (and to run out of memory trying to expand the subtype).
--	 where(TYPE_EXPR'subtype(Typing, Restriction) -> GenSubType)
	 -- Using just the maximal type here (the translator ensures that it will be translated to its restricted version)
	 -- (the translator is only using unbounded types + restriction when a subtype is found). This behaviour is kept in this
	 -- way to detect subtype errors in RANGED sets, where the approach mentioned above works.
	 --Maxtype(DomType -> GenSubType)
         where(DomType -> GenSubType)
 
	 --where(VALUE_EXPR'quantified(Pos, all, list(single(TPos, Binding, GenSubType), nil), restriction(Pos,SubtypeCond)) -> RSL_All)
         where(VALUE_EXPR'quantified(Pos, all, list(single(TPos, Binding, DomType), nil), restriction(Pos,SubtypeCond)) -> RSL_All)
	 -- Restoring the environment (removing the trick's effects)

	 Closeenv()
	 (|
	      ne(SubtypeCond, no_val)
	      Gen_SAL_Expr(SubtypeCond, normal, bool -> _, CC_Condition)
	      Gen_SAL_Expr(RSL_All, normal, bool -> _, Restriction1)
	      Default_Bool_Tid -> BTid
	      BTid'Lifted_Tid -> tid(LBTid)
	      LBTid'Ident -> LBId
	      LBTid'Pos -> LBPos
	      -- adding 'is_true'
	      where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	      where(sal_esp_unary_prefix_occ(val_id(SAL_Op), Restriction1) -> Condition)
	      
	      SAL_Gen_Type_Expr(Pos, TExpr1 -> _, SetType)
              
	      where(Restriction -> restriction(_, LambdaRestriction))

	      Gen_SAL_Expr(LambdaRestriction, normal, bool -> _, SetRestriction)
	      where(sal_esp_unary_prefix_occ(val_id(SAL_Op), SetRestriction) -> SetRestriction1)
              SAL_Gen_Type_Expr(Pos, DomType -> SALDomType, SALDomType_CC)
	      where(SAL_VALUE_EXPR'sal_ranged_cc_set(Ident, SetType, SALType, SetRestriction1, SALType_NonLifted) -> EnumSetExpr)
	      -- Generating the IF expr:
	      Get_Invalid_Insertion_Nav(-> NavValId)
	      SAL_Generate_Result_for_Violation(SetType, sal_esp_value_occ(NavValId) -> WrongApplExpr)
	      where(sal_if_expr(Condition, EnumSetExpr, nil, else(WrongApplExpr)) -> CC_Expr)
	 ||
	     -- cwg
	     -- the SAL_CC_Restriction assumes the ids in SAL_CC_B
	     -- are of lifted types, but they are not.
	     -- we solve this by inserting a LET of the form 
             -- (where x is the binding)
	     -- LET (x : T_cc) = T_cc(x) IN
	     SAL_Lift_Bindings(SAL_CC_B, ProdType, SAL_CC_Restriction -> SAL_CC_Let_Restriction)
	     where(SAL_VALUE_EXPR'sal_comp_simp_set(bindings(SAL_CC_B), SAL_CC_Let_Restriction) -> SAL_CC_Exprout)
	     Type_is_set(TExpr1 -> TExpr)
	     -- cwg enough to know there is a set matching this maximally
             SAL_Check_Defined_Set(Pos, TExpr -> OptTid)
	     --SAL_Check_Defined_Maximal_Set(Pos,TExpr -> OptTid)
	     (| -- it's a set...
	         where(OptTid -> tid(SetTid))
	         (| -- it's not ANY (a type can be determined for the expr)
	             ne(TExpr, any)
		     -- Generating the type:
		     SAL_Gen_Type_Expr(Pos, TExpr -> SALTExpr, CC_Type)
                 ||
	             -- This is the case of: {} (type = any)
		     -- Get the disambiguation...
		     Get_Current_Disamb(-> Disamb)
		     (|
	                 -- There is a disambiguation:
			 where(Disamb -> disamb(_, ValueExpr1, TypeExpr))
			 -- And it disambiguates the current value:
			 eq(ValueExpr1, comp_set(Pos, ValueExpr,
			 set_limit(Pos2, Typings, Restriction)))
			 -- use the type:
			 Type_is_set(TypeExpr -> ElemType)
			 SAL_Gen_Type_Expr(Pos, ElemType -> SALTExpr, CC_Type)
		     ||
		         Puterror(Pos)
			 Putmsg("No way to disambiguate the type of the value\n")
			 where(SAL_TYPE_EXPR'nil -> SALTExpr)
			 where(SALTExpr -> CC_Type)
	             |)  
	         |)
	         SetTid'Lifted_Tid -> tid(LiftedSet)
		 LiftedSet'Constructor -> vid(ConstVid)
		 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(SAL_CC_Exprout, nil))) -> CC_Expr)
             ||
	         -- There is no set of this type... creating a new one...
		 Gen_Set_Type(Pos, TExpr -> SetTid)
		 SetTid'Lifted_Tid -> tid(LiftedSet)
		 LiftedSet'Constructor -> vid(ConstVid)
		 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(SAL_CC_Exprout, nil))) -> CC_Expr)
	     |)
	 |)



  'rule' Gen_SAL_Expr_(comp_set(Pos, ValueExpr,
		      set_limit(Pos2, Typings, Restriction)), TExpr1 -> SALExprout, CC_Expr):
         Type_is_set(TExpr1 -> TExpr)
	 Gen_SAL_Expr(ValueExpr, normal, TExpr -> SALExpr, SAL_CC_Expr)
	 SAL_Gen_Type_Expr(Pos, TExpr -> SALTypeExpr, CC_Type)
	 Gen_SALBindings_from_Typings(Typings -> SALBindings, SAL_CC_B, ProdType)
	 Gen_SAL_Restriction(Restriction, bool -> SALRestriction, SAL_CC_Restriction)
	 where(sal_comp_set(SALExpr, SALTypeExpr,bindings(SALBindings), SALRestriction) -> SALExprout)
	 -- cc
	 where(CC_Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 Tid'Constructor -> vid(Const)
	 -- construct expression
	 -- SAL_CC_Restriction AND T_cc(y_) = SAL_CC_Expr
	 string_to_id("y_" -> Yid)
	 where(sal_named_val(id_op(id(Yid))) -> Yname)
	 where(sal_funct_applic(sal_esp_value_occ(Const),
		sal_argument(SAL_VALUE_EXPRS'list(Yname, nil))) -> LY)
	 where(sal_infix_occ(LY,
		val_id(sal_op_symb(sal_infix_op(eq))), SAL_CC_Expr) -> R)
	 where(sal_ax_infix(SAL_CC_Restriction, and, R) -> SAL_CC_Restriction1)
	 SAL_Lift_Bindings(SAL_CC_B, ProdType,  SAL_CC_Restriction1 -> SAL_CC_Let_Restriction)
	 --(|
	   --Maximal(TExpr)
	   where(SALTypeExpr -> SALMaxTypeExpr)
	 --||
	   --Maxtype(TExpr -> MaxTExpr)
	   --SAL_Gen_Type_Expr(Pos, MaxTExpr -> SALMaxTypeExpr, _)
	 --|)
	 where(sal_comp_cc_set(Yid, SALMaxTypeExpr, bindings(SAL_CC_B), SAL_CC_Let_Restriction) -> CC_Exprout)
	 (|
	   -- cwg enough to know there is a set matching this maximally
	   --SAL_Check_Defined_Maximal_Set(Pos,TExpr -> tid(SetTid))
           SAL_Check_Defined_Set(Pos,TExpr -> tid(SetTid))
         ||
	   -- this set type not yet defined
	   Gen_Set_Type(Pos, TExpr -> SetTid)
	 |)
	 SetTid'Lifted_Tid -> tid(LiftedSet)
	 LiftedSet'Constructor -> vid(ConstVid)
	 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(CC_Exprout, nil))) -> CC_Expr)


  'rule' Gen_SAL_Expr_(ranged_list(Pos, LeftValueExpr, RightValueExpr), TExpr -> SALExprout, SALExprout):
	 Puterror(Pos)
	 Putmsg("List expressions are not accepted\n")
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 /*Gen_SAL_Expr(LeftValueExpr,normal, TExpr -> LeftSALExpr)
	 Gen_SAL_Expr(RightValueExpr, normal, TExpr -> RightSALExpr,_)
	 where(SAL_VALUE_EXPR'sal_ranged_list(LeftSALExpr, RightSALExpr) -> SALExprout)*/

  'rule' Gen_SAL_Expr_(enum_list(Pos, ValueExprs), TExpr -> SALExprout, SALExprout):
	 Puterror(Pos)
	 Putmsg("List expressions are not accepted\n")
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 /*Gen_SAL_Exprs(ValueExprs, nil, TExpr -> SALExprs)
	 where(SAL_VALUE_EXPR'sal_enum_list(SALExprs) -> SALExprout)*/

  'rule' Gen_SAL_Expr_(comp_list(Pos, ValueExpr, Limit), TExpr -> SALExprout, SALExprout):
         Puterror(Pos)
	 Putmsg("List expressions are not accepted\n")
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 /*Type_is_list(TExpr -> ElemsType)
	 Gen_SAL_Expr(ValueExpr, normal, ElemsType -> SALExpr,_)
	 SAL_Gen_ListLimit(Limit, TExpr -> SALLimit)
	 where(SAL_VALUE_EXPR'sal_comp_list(SALExpr, SALLimit) -> SALExprout)*/

  'rule' Gen_SAL_Expr_(enum_map(Pos, ValueExprPairs), TExpr1 -> SALExprout, CC_Expr):
	 Get_Type_of_Value_Expr(enum_map(Pos, ValueExprPairs) -> T)
	 Type_is_map(TExpr1 -> Dom, Rng)
	 -- getting the tid:
	 SAL_Check_Defined_Map(Pos,Dom,Rng -> OptTid)
	 (|
	         where(OptTid -> tid(MapTid))
	 ||
                 -- There is no map of this type, generate a new one:
                 Gen_Map_Type(Pos, Dom, Pos, Rng -> MapTid)
	 |)
	 (|
	        (| eq(Dom, any) || eq(Rng,any) |)
		    -- This is the case of: [] (type = any)
		    Get_Current_Disamb(-> Disamb)
	            (|
		       -- There is a disambiguation:
		       where(Disamb -> disamb(_, ValueExpr, TypeExpr))
		       -- And it disambiguates the current value:
		       eq(ValueExpr, enum_map(Pos, ValueExprPairs))
		       -- use the type:
		       Type_is_map(TypeExpr -> Dom1, Rng1)
	            ||
		       Puterror(Pos)
		       Putmsg("No way to disambiguate the type of the value\n")
		       where(TYPE_EXPR'none -> Dom1)
		       where(TYPE_EXPR'none -> Rng1)
	            |)  
	         SAL_Gen_Type_Expr(Pos, Dom1 -> DomST, LDomST)
		 SAL_Gen_Type_Expr(Pos, Rng1 -> RngST, LRngST)
	 ||
	         -- Generating the type:
		 SAL_Gen_Type_Expr(Pos, Dom -> DomST,LDomST)
		 SAL_Gen_Type_Expr(Pos, Rng -> RngST, LRngST)
	 |)
	 Gen_SAL_ExprPairs(ValueExprPairs, nil, nil, Dom, Rng -> SALExprPairs, SAL_CC_Expr_Pairs)
	 where(SAL_VALUE_EXPR'sal_enum_map(MapTid, DomST, RngST, SALExprPairs) -> SALExprout)
	 -- cc
	 MapTid'Lifted_Tid -> tid(LiftedMap)
	 where(SAL_VALUE_EXPR'sal_enum_map(LiftedMap, LDomST, LRngST, SAL_CC_Expr_Pairs) -> CC_Expr1)
	 -- Adding verifications for the elements being added to the set...
	 -- This type correctness verification on insertion ensures (by construction) that the
	 -- set contains valid elements (and avoids quantified verifications...)
	 SAL_Gen_Is_In_Condition_for_Pairs(ValueExprPairs, Dom,Rng -> Condition)
	 (|
	      eq(Condition, no_val)
	      where(CC_Expr1 -> CC_Expr)
	 ||
	      Get_Invalid_Insertion_Nav(-> NavValId)
	      Gen_SAL_Expr(Condition, normal, bool -> _, CC_Condition1)
	      -- make is_true operator
	      Default_Bool_Tid -> BTid
	      BTid'Lifted_Tid -> tid(LBTid)
	      where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	      where(sal_esp_unary_prefix_occ(val_id(SAL_Op), CC_Condition1) -> CC_Condition)
	      SAL_Gen_Type_Expr(Pos, fin_map(Dom,Rng) -> _, MapType) 
	      SAL_Generate_Result_for_Violation(MapType, sal_esp_value_occ(NavValId) -> WrongApplExpr)
	      where(sal_if_expr(CC_Condition, CC_Expr1, nil, else(WrongApplExpr)) -> CC_Expr)
	 |)



  'rule' Gen_SAL_Expr_(comp_map(Pos, pair(LeftValueExpr, RightValueExpr),
                      set_limit(Pos2, Typings, Restriction)), TExpr -> SALExprout, CC_Expr):
	 -- try for version where left matches binding
	 -- ie has form [ x +> e(x) | x : T :- p(x) ]
	 where(Typings -> list(Typing, nil))
	 where(Typing -> single(_, Binding, TypeExprDom))
	 Matches_binding(LeftValueExpr, Binding) --sml.g
	 -- Is the simple case...
	 -- As the type system is different in SAL is not possible to rely on the RSL types inside 'pair(_,_)'
	 -- Using the inherited type instead:
	 -- Checking if the map is correctly formed (that means, if the types of the expressions match (according to SAL criteria))

	 Type_is_map(TExpr -> Dom,Rng)
	 -- Looking up the SAL map:
	 SAL_Check_Defined_Map(Pos,Dom,Rng -> OptTid)
	 (|
	     where(OptTid -> tid(Tid))
	 ||
	     -- There is no map of this type, generate a new one:
             Gen_Map_Type(Pos, Dom, Pos, Rng -> Tid)
	 |)
	 Gen_SALBindings_from_Typing(Typing -> SALBindings, _, ProdType)
	 Gen_SAL_Restriction(Restriction, bool -> SALRestriction, SAL_CC_Restriction)
	 Gen_SAL_Expr(RightValueExpr, normal, Rng -> SALRightExpr, _)
         -- It is necessary to refer to the constructor and destructor
	 -- of the 'map_range' type
         Tid'TExpr -> rsl_built_in(sal_finite_map(_,_,type_refs(sal_defined(_,_,RngTid))))
--SAL_Print_Tid(RngTid)
--Putnl()
        RngTid'TExpr -> TExpr1
--print(TExpr)
         -- Disassembling the type to get the information:
         where(TExpr1 -> user_defined(sal_variant_type(Dparts)))
         where(Dparts -> list(NilPart,list(ValPart,nil)))
         where(NilPart -> sal_part(NilConst,_))
         where(NilConst -> sal_construc(_,NilVid,_,_))
         where(ValPart -> sal_part(ValConst,_))
         where(ValConst -> sal_construc(_,ValVid,_,_))
	 where(SAL_VALUE_EXPR'sal_comp_rng_map(SALRightExpr,
	 ValVid, NilVid, bindings(SALBindings), SALRestriction) -> SALExprout)
	 -- cc
	 -- SAL_CC_Restriction assumes the ids in SALBindings
	 -- are of lifted types, but they are not.
	 -- we solve this by inserting a LET of the form 
	 -- (where x is the binding)
	 -- LET (x : Dom_cc) = Dom_cc(x) IN
	 (|
	   eq(SAL_CC_Restriction, nil)
	   where(SAL_VALUE_EXPR'nil -> Let_Restriction)
	 ||
	   SAL_Lift_Bindings(SALBindings, ProdType, SAL_CC_Restriction -> Let_Restriction)
	 |)
	 where(SAL_VALUE_EXPR'sal_comp_rng_map(SALRightExpr, ValVid,
	 NilVid, bindings(SALBindings), Let_Restriction) -> CC_Exprout)
	 Tid'Lifted_Tid -> tid(LiftedMap)
	 LiftedMap'Constructor -> vid(ConstVid)
	 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(CC_Exprout, nil))) -> CC_Expr)

  'rule' Gen_SAL_Expr_(comp_map(Pos, pair(LeftValueExpr, RightValueExpr),
                      set_limit(Pos2, Typings, Restriction)), TExpr -> SALExprout, SALExprout):
         Puterror(Pos)
	 Putmsg("Complex comprehended map expressions are not accepted\n")
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 

  'rule' Gen_SAL_Expr_(function(Pos, LambdaParam, ValueExpr), TExpr -> SALExprout, CC_Expr):
	 Gen_SAL_Expr(ValueExpr, normal, TExpr -> SALExpr, SAL_CC_Expr)
	 SAL_Gen_Lambda_Binding(LambdaParam -> LambdaBinding, CC_LBS)
	 where(SAL_VALUE_EXPR'sal_function(LambdaBinding, SALExpr) -> SALExprout)
	 -- cc
	 where(SAL_VALUE_EXPR'sal_function(CC_LBS, SAL_CC_Expr) -> CC_Expr)

  'rule' Gen_SAL_Expr_(application(Pos, ValueExpr, Args:list(_, list(_, _))), TExpr
				       -> SALExprout, CC_Expr):
	 -- deal with one application at a time by nesting
	 Rearrange_application(Pos, ValueExpr, Args -> ValueExpr1) --cpp.g
	 Gen_SAL_Expr(ValueExpr1, argument, TExpr -> SALExprout, CC_Expr) 

  'rule' Gen_SAL_Expr_(application(Pos, ValueExpr, list(Arg, nil)), ExprType -> SALExprout, CC_Expr):
	 Get_Type_of_Value_Expr(ValueExpr -> ValueExprType)
	 Gen_SAL_applic_Expr(Pos,ValueExprType, ValueExpr, Arg -> SALExprout, CC_Expr)

  'rule' Gen_SAL_Expr_(quantified(Pos, Quantifier, Typings, Restriction), TExpr -> SALExprout, CC_Expr):
	 Gen_SAL_Quantifier(Quantifier -> BindinOp)
	 Gen_SALBindings_from_Typings(Typings -> SALBindings, SAL_CC_Bindings, TypeList)
	 Gen_SAL_Restriction(Restriction, bool -> RestrictionExpr, SAL_CC_Restriction)
	 where(SAL_VALUE_EXPR'sal_quantified(BindinOp, bindings(SALBindings),
                                   RestrictionExpr) -> SALExprout)
	 -- cc
	 -- Introducing a let to overwrite the bindings in the quantifier with a lifted value:
	 -- We don't want this any more (the only particular case that wants it is the value-expression translator
	 -- for ranged sets and this rule is no longer invoked from there...)
	 SAL_Turn_Bindings_into_Lets(SAL_CC_Bindings, SAL_CC_Restriction, TypeList -> CC_Expr1, _)
	 --where(SAL_VALUE_EXPR'sal_quantified(BindinOp, bindings(SAL_CC_Bindings), CC_Expr1) -> CC_Expr2)
         where(SAL_VALUE_EXPR'sal_quantified(BindinOp, bindings(SALBindings), CC_Expr1) -> CC_Expr2)
	 -- wrapping this expression (of type BOOLEAN) to make it of type Bool_cc
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 LBTid'Constructor -> vid(CVid)
	 where(sal_argument(list(CC_Expr2, nil)) -> Arg)
	 where(sal_funct_applic(sal_esp_value_occ(CVid), Arg) -> CC_Expr)

  'rule' Gen_SAL_Expr_(equivalence(Pos, ValueExprL, ValueExprR,
                                  PreCond), TExpr -> SALExprout, CC_Expr):
	 Gen_SAL_Expr(ValueExprL, normal, TExpr -> SALExprL, SAL_CC_ExprL)
	 Gen_SAL_Expr(ValueExprR, normal, TExpr -> SALExprR, SAL_CC_ExprR)
	 (|
	   where(PreCond -> pre_cond(Pos2, Pre))
 	   Gen_SAL_Expr(Pre, normal, TExpr -> SALExprPre, CC_Pre)
	 ||
	   where(PreCond -> nil)
	   where(SAL_VALUE_EXPR'nil -> SALExprPre)
	   where(SALExprPre -> CC_Pre)
	 |)
	 where(SAL_VALUE_EXPR'sal_equivalence(SALExprL, SALExprR, SALExprPre) -> SALExprout)
	 -- cc
	 where(SAL_VALUE_EXPR'sal_equivalence(SAL_CC_ExprL, SAL_CC_ExprR, CC_Pre) -> CC_Expr)

  'rule' Gen_SAL_Expr_(post(Pos, ValueExpr, Post, PreCond),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("post expressions not supported")
	 Putnl()

  'rule' Gen_SAL_Expr_(disamb(Pos, ValueExpr, TypeExpr), TExpr -> SALExprout, CC_Expr):
	 Push_Disamb(disamb(Pos, ValueExpr, TypeExpr))
	 Gen_SAL_Expr(ValueExpr, normal, TExpr -> SALExprout, CC_Expr)
	 Pop_Disamb()

  'rule' Gen_SAL_Expr_(bracket(Pos, ValueExpr), TExpr -> SALExprout, CC_Expr):
	 Gen_SAL_Expr(ValueExpr, normal, TExpr -> SALExpr, SAL_CC_Expr)
	 where(SAL_VALUE_EXPR'sal_bracket(SALExpr) -> SALExprout)
	 -- cc
	 where(SAL_VALUE_EXPR'sal_bracket(SAL_CC_Expr) -> CC_Expr)

  'rule' Gen_SAL_Expr_(ax_infix(Pos, LeftValueExpr, Conn, RightValueExpr, Pos1), TExpr -> SALExprout, CC_Expr):
/* -- should not be necessary to use if expressions since cc version
   -- effectively deals with undefined expressions in logical expressions
-- translate boolean connectives as if expressions to preserve
-- conditional logic
	 where(region(Pos, Pos) -> Region)
	 (|
	   eq(Conn, implies)
	   Gen_SAL_Expr_(
		if_expr(Pos, LeftValueExpr, RightValueExpr,
			Region, nil,
			else(Pos1, literal_expr(Pos1, bool_true))),
		TExpr -> SALExprout, CC_Expr)   
	 ||
	   eq(Conn, or)
	   Gen_SAL_Expr_(
		if_expr(Pos, LeftValueExpr, literal_expr(Pos, bool_true),
			Region, nil,
			else(Pos, RightValueExpr)),
		TExpr -> SALExprout, CC_Expr)
	 ||
	   -- eq(Conn, and)
	   Gen_SAL_Expr_(
		if_expr(Pos, LeftValueExpr, RightValueExpr,
			Region, nil,
			else(Pos1, literal_expr(Pos1, bool_false))),
		TExpr -> SALExprout, CC_Expr)
	 |)
*/

	 Gen_SAL_Expr(LeftValueExpr, normal, TExpr -> LeftSALExpr, Left_CC_Expr)
	 Gen_SAL_Logic_Conn(Conn -> SALConn, CC_Conn)
	 Gen_SAL_Expr(RightValueExpr, normal, TExpr -> RightSALExpr, Right_CC_Expr)
	 where(SAL_VALUE_EXPR'sal_ax_infix(LeftSALExpr, SALConn, RightSALExpr) -> SALExprout)
	 -- cc
	 (|
            where(CC_Conn -> sal_cc_op(sal_prefix_op(not), _))
	    Puterror(Pos)
	    Putmsg("Internal error: axiom prefix unary operation found when binary infix operation was expected\n")
	    where(SAL_VALUE_EXPR'sal_esp_unary_prefix_occ(val_id(CC_Conn), Left_CC_Expr)  -> CC_Expr)
	 ||
	    where(SAL_VALUE_EXPR'sal_esp_prefix_occ(val_id(CC_Conn), Left_CC_Expr, Right_CC_Expr)  -> CC_Expr)
	 |)

 
  'rule' Gen_SAL_Expr_(stmt_infix(Pos, _, _, _),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("stmt_infix expressions not supported")
	 Putnl()
	 -- EXTENSION HERE WHEN MODEL CHECKING IMP. CONCURRENT SPECS...

  'rule' Gen_SAL_Expr_(always(Pos, ValueExpr), TExpr -> SALExprout, SALExprout):
	 Gen_SAL_Expr(ValueExpr, normal, TExpr -> SALExprout,_)
	 Putwarning(Pos)
	 Putmsg("always expressions ignored")
	 Putnl()
 
  'rule' Gen_SAL_Expr_(ax_prefix(Pos, Conn, ValueExpr), TExpr -> SALExprout, CC_Expr):
	 Gen_SAL_Logic_Conn(Conn -> SALConn, CC_Conn)
	 Gen_SAL_Expr(ValueExpr, normal, TExpr -> SALExpr, SAL_CC_Expr)
	 where(SAL_VALUE_EXPR'sal_ax_prefix(SALConn, SALExpr)  -> SALExprout)
	 -- cc
	 (|
            where(CC_Conn -> sal_cc_op(sal_prefix_op(not),_))
	    where(SAL_VALUE_EXPR'sal_esp_unary_prefix_occ(val_id(CC_Conn), SAL_CC_Expr)  -> CC_Expr)
	 ||
	    Puterror(Pos)
	    Putmsg("Internal error: axiom infix binary operation found when unary prefix operation was expected\n")
	    where(SAL_VALUE_EXPR'sal_esp_prefix_occ(val_id(CC_Conn), SAL_CC_Expr, nil)  -> CC_Expr)
	 |)
 
  'rule' Gen_SAL_Expr_(comprehended(Pos, _, _, _),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("comprehended expressions not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_SAL_Expr_(initialise(Pos, _),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("initialise expressions not supported")
	 Putnl()
	 -- EXTENSION WHEN accepting IMPERATIVE SPECS

	 
  'rule' Gen_SAL_Expr_(assignment(Pos, Vname, ValueExprR), TExpr -> SALExprout, CC_Expr):
	 Gen_SAL_Expr(ValueExprR, normal, TExpr -> SALExprR, SAL_CC_ExprR)
	 (|
		where(Vname -> name(_,id_op(Ident)))
	 ||
		where(Vname -> qual_name(_,Qualif,id_op(Ident)))
	 |)
	 where(SAL_VALUE_EXPR'sal_assignment(Ident,SALExprR)-> SALExprout)
	 -- cc
	 where(SAL_VALUE_EXPR'sal_assignment(Ident,SAL_CC_ExprR)-> CC_Expr)

	 -- not supported
  'rule' Gen_SAL_Expr_(input(Pos, _), TExpr -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("input expressions not supported")

	 -- not supported
  'rule' Gen_SAL_Expr_(output(Pos, _, _),_ -> SALExprout,SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("output expressions not supported")
	 Putnl()

  'rule' Gen_SAL_Expr_(local_expr(Pos, Decls, ValueExpr), TExpr -> SALExprout, CC_Expr):
	 Gen_SAL_Expr_(ValueExpr, TExpr -> SALExprout, CC_Expr)
	 Putwarning(Pos)
	 Putmsg("local expressions ignored")
	 Putnl()

  'rule' Gen_SAL_Expr_(let_expr(Pos, LetDefs, ValueExpr), TExpr ->  SALExprout, CC_Expr):
	 -- The ValueExpr contains the expression in the LET scope
	 -- The LetDefs contains the let definition, and the type
	 -- SAL_Process_Let_Defs(LetDefs -> Identif, AsocType, Namespace)
	 -- Generate the identifier introduced in the LET... (Ident)
	SAL_Process_Let_Defs(LetDefs, ValueExpr, TExpr -> SALExprout, CC_Expr)


  'rule' Gen_SAL_Expr_(if_expr(Pos, ValueExpr, Then, _, Elsifs, Else), TExpr
					      -> SALExprout, CC_Expr):
	 [|
	   eq(Else, nil)
	   Puterror(Pos)
	   Putmsg("if expressions without else branch not supported")
	   Putnl()
	 |]
	 Gen_SAL_Expr(ValueExpr, normal, bool -> SALExpr1, SAL_CC_Expr1)
	 Gen_SAL_Expr(Then, normal, TExpr -> SALThen, SAL_CC_Then)
	 SAL_Gen_Elsifs(Elsifs, nil, nil, TExpr -> SALElsifs, SAL_CC_Elsif)
	 SAL_Gen_Else(Else, TExpr -> SALElse, SAL_CC_Else)
	 where(SAL_VALUE_EXPR'sal_if_expr(SALExpr1, SALThen, SALElsifs, SALElse) -> SALExprout)
	 --cc
	 -- translated as
	 -- LET x = ValueExpr IN
	 -- IF Bool__nav?(x) THEN T_nav(Bool__nav_val(x))
	 -- ELSE IF is_true(x) THEN SAL_CC_Then SAL_CC_Elsif ELSE SAL_CC_Else ENDIF
	 -- ENDIF
	 -- Adding the 'is_true' part in front of the condition...
	 SAL_Gen_Let_Ident(-> X)
	 SAL_Gen_Type_Expr(Pos, bool -> Bool, CCBool)
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 -- construct inner if
	 where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	 where(sal_value_occ(val_id(id(X)), nil) -> XOcc)
	 where(sal_esp_unary_prefix_occ(val_id(SAL_Op), XOcc) -> Is_true_Expr)
	 where(SAL_VALUE_EXPR'sal_if_expr(Is_true_Expr, SAL_CC_Then,
	 SAL_CC_Elsif, SAL_CC_Else) -> CC_If1)
	 -- construct outer if
	 Get_lifted_constructor(Bool -> BoolNavConst)
	 where(BoolNavConst -> sal_construc(_, BoolNavConstVid, BoolNavAccessor, _))
	 where(BoolNavAccessor -> list(sal_destructor(_, BoolNavAccVid, _, _), _))
	 where(sal_argument(list(XOcc, nil)) -> XArg)
	 where(sal_recogniser(BoolNavConstVid, XArg) -> Cond)
	 where(sal_funct_applic(sal_esp_value_occ(BoolNavAccVid), XArg) -> Expr)
	 where(sal_argument(list(Expr, nil)) -> Arg1)
	 Maxtype(TExpr -> MaxT)
	 SAL_Gen_Type_Expr(Pos, MaxT -> IfType, _)
	 Get_lifted_constructor(IfType -> NavConst)
	 where(NavConst -> sal_construc(_, NavConstVid, _, _))
	 where(sal_funct_applic(sal_esp_value_occ(NavConstVid), Arg1) -> Nav)
--where(SAL_VALUE_EXPR'nil -> Nav)
	 where(sal_if_expr(Cond, Nav, nil, else(CC_If1)) -> CC_If2)
	 where(sal_let_expr(X, CCBool, nil, nil, SAL_CC_Expr1, CC_If2) -> CC_Expr)


  'rule' Gen_SAL_Expr_(case_expr(Pos1, ValueExpr, Pos2, CaseBranches), TExpr -> SALExprout, CC_Expr):
	 -- ignore disambiguation, but use type
	 (|
	   where(ValueExpr -> disamb(_, ValueExpr1, XT))
	 ||
	   where(ValueExpr -> ValueExpr1)
	   Make_results(ValueExpr -> list(result(XT,_,_,_,_),_))
	 |)
	 -- translate as let x = ValueExpr1 in case x of ... end
	 SAL_Gen_Let_Ident(-> X)
	 New_value_id(Pos1, id_op(X) -> XVid)
	 XVid'Type <- XT
	 where(VALUE_EXPR'val_occ(Pos1, XVid, nil) -> XOcc)
	 Gen_SAL_Cases(XOcc, CaseBranches, TExpr -> SALExprout1, CC_Expr1)
	 Gen_SAL_Expr(XOcc, normal, XT -> SAL_X, SAL_CC_X)
	 Maxtype(XT -> MaxT)
	 SAL_Gen_Type_Expr(Pos1, MaxT -> SAL_XT, SAL_CC_XT)
	 Gen_SAL_Expr(ValueExpr1, normal, XT -> SAL_Expr1, SAL_CC_Expr1)
	 where(sal_let_expr(X, SAL_XT, nil, nil, SAL_Expr1, SALExprout1) -> SALExprout)
	 -- cc version needs to check ValueExpr1 as a possible nav:
	 -- LET x = SAL_CC_Expr1 IN
	 -- IF XT_nav?(x) THEN T_nav(XT_nav_val(x)) ELSE CC_Expr1 ENDIF
	 Get_lifted_constructor(SAL_XT -> XTNavConst)
	 where(XTNavConst -> sal_construc(_, XTNavConstVid, XTNavAccessor, _))
	 where(XTNavAccessor -> list(sal_destructor(_, XTNavAccVid, _, _), _))
	 where(sal_argument(list(SAL_X, nil)) -> XArg)
	 where(sal_recogniser(XTNavConstVid, XArg) -> Cond)
	 where(sal_funct_applic(sal_esp_value_occ(XTNavAccVid), XArg) -> Expr)
	 where(sal_argument(list(Expr, nil)) -> Arg1)
	 Maxtype(TExpr -> MaxTExpr)
	 SAL_Gen_Type_Expr(Pos1, MaxTExpr -> CaseType, _)
	 Get_lifted_constructor(CaseType -> NavConst)
	 where(NavConst -> sal_construc(_, NavConstVid, _, _))
	 where(sal_funct_applic(sal_esp_value_occ(NavConstVid), Arg1) -> Nav)
	 where(sal_if_expr(Cond, Nav, nil, else(CC_Expr1)) -> CC_Expr2)
	 where(sal_let_expr(X, SAL_CC_XT, nil, nil, SAL_CC_Expr1, CC_Expr2) -> CC_Expr)
	 

	 -- not supported
  'rule' Gen_SAL_Expr_(while_expr(Pos, _, _), TExpr -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("while expressions not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_SAL_Expr_(until_expr(Pos, _, _), TExpr -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("until expressions not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_SAL_Expr_(for_expr(Pos, _, _),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("for expressions not supported")
	 Putnl()


  'rule' Gen_SAL_Expr_(env_class_scope(Pos, instantiation(
                                              name(Pos2,
                                                   id_op(Id)),
                                              nil), _,
                                       ValueExpr), TExpr
                      -> SALExprout, SALExprout):
	 -- SEE THIS!!! Instantiate the proper context?
	 --Gen_SAL_Expr(ValueExpr, normal, TExpr -> SALExprout)
	 Puterror(Pos)
	 Putmsg("Environment class scope not translatable into SAL\n")
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)

  'rule' Gen_SAL_Expr_(env_class_scope(Pos, Class, CE, ValueExpr), TExpr
                      -> SALExprout, SALExprout):
	 Current -> C
	 Current <- current_env(CE, C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil, Paths)
--	 Open_TotalDeclareds
	 -- Uncomment this when translating classes!
--	 SAL_Trans_Class(Class)
	 Gen_SAL_Expr(ValueExpr, normal, TExpr -> SALExprout, _)
	 Close_TotalDeclareds
	 Current <- C
	 Extend_paths <- Paths

  'rule' Gen_SAL_Expr_(implementation_relation(Pos, NewClass, OldClass),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("implementation relation not supported")
	 Putnl()
 
	 -- resolved to class scope expr
  'rule' Gen_SAL_Expr_(implementation_expr(Pos, NewObjExpr, OldObjExpr),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("implementation expressions not supported")
	 Putnl()

  'rule' Gen_SAL_Expr_(local_val_occ(Pos, Valueid, OptQual), TExpr -> SALExprout, CC_Expr):
	 Valueid'Ident -> IdorOp
	 Valueid'Pos -> Pos1
	 Valueid'Qualifier -> Ids
--Putmsg("Processing val_occ ")
--Print_id_or_op(IdorOp)
--Putmsg(" at pos ")
--PrintPos(Pos1)
--Putnl()
	 Gen_SAL_Id_Op(Pos, IdorOp, TExpr,none -> IdOp, _) -- here the id_op is used to encode the name of the value (an Ident)
							   -- no different treatment with the non-cc version...
	 -- Looking up the position of the value in the global table
	 -- A successful look-up indicates the presence of an especial value

--Putmsg("Assuming local variable\n")
	    -- Generating a typical value expression occurences
	    -- One of the following:
	    --    Local variables
	    --	  Let bindings
	    -- Processing the qualification:
	    SAL_Proc_Qualification(OptQual -> Qualif)
	    where(SAL_VALUE_EXPR'sal_value_occ(val_id(IdOp), Qualif) -> SALExprout)
	    -- the same for the cc version:
	    where(SALExprout -> CC_Expr)


  'rule' Gen_SAL_Expr_(val_occ(Pos, Valueid, OptQual), TExpr -> SALExprout, CC_Expr):
	 Valueid'Ident -> IdorOp
	 Valueid'Pos -> Pos1
	 Valueid'Qualifier -> Ids
--Putmsg("Processing val_occ ")
--Print_id_or_op(IdorOp)
--Putmsg(" at pos ")
--PrintPos(Pos1)
--Putnl()
	 Gen_SAL_Id_Op(Pos, IdorOp, TExpr,none -> IdOp, _) -- here the id_op is used to encode the name of the value (an Ident)
							   -- no different treatment with the non-cc version...
	 -- Looking up the position of the value in the global table
	 -- A successful look-up indicates the presence of an especial value
	 
	 (|
	    -- detecting if it is RSL_is_Int OR RSL_is_Nat
	    (|
		Id_of_rsl_is_int -> RSL_is_Int
	        eq(RSL_is_Int, Valueid)
	        SAL_RSL_is_Int_Vid -> SAL_is_Int
	        where(SAL_VALUE_EXPR'sal_esp_value_occ(SAL_is_Int) -> SALExprout)
	        where(SALExprout -> CC_Expr)
	    ||
		Id_of_rsl_is_nat -> RSL_is_Nat
		eq(RSL_is_Nat, Valueid)
	        SAL_RSL_is_Nat_Vid -> SAL_is_Nat
	        where(SAL_VALUE_EXPR'sal_esp_value_occ(SAL_is_Nat) -> SALExprout)
	        where(SALExprout -> CC_Expr)
	    |)
	 ||
	    DefaultPos(-> DefPos)
	    eq(DefPos, Pos1)
--Putmsg("Matched with the default pos\n")
	    -- If the position in the Valueid is de DefaultPos, then we are handling on of the
	    -- fake ValueIds created for the RSL operations...
	    SAL_Proc_Qualification(OptQual -> Qualif)
	    where(SAL_VALUE_EXPR'sal_value_occ(val_id(IdOp), Qualif) -> SALExprout)
	    -- the same for the cc version:
	    where(SALExprout -> CC_Expr)
	 ||
	    -- Otherwise... It is a ValueId created from some value in the code...
	    -- Then, an equivalent Vid should exist
	    look_up_value_id(Pos1 -> OptVid)
--Putmsg("Looking up value: ")
--where(IdorOp -> id_op(ID))
--Print_id(ID)
--Putnl()
--Putmsg("In position: ")
--PrintPos(Pos1)
--Putnl()
	    where(OptVid -> vid(Vid))
--Putmsg("Reference to  ")
--where(IdorOp -> id_op(ID1))
--Print_id(ID1)
--Putmsg(" solved with lookup! (")
--SAL_Print_Vid(Vid)
--Putmsg(")\n")
	    -- The value was found in the global table,
	    -- This means that the value is:
	    --	  Either a function name (globally available in SAL)
	    --	  Or a constant declaration (also global)
	    --	  Or a variant constructor...
	    -- In this case, an special variant of value_occ is
	    -- generated:
	    where(SAL_VALUE_EXPR'sal_esp_value_occ(Vid) -> SALExprout)
	    -- the cc version differs in that the lifted Vid is used instead:
	    Vid'Lifted_Vid -> LVid
	    where(SAL_VALUE_EXPR'sal_esp_value_occ(LVid) -> CC_Expr1)
	    (|
		-- If the value is a variant field (empty constructor) like
		-- m1 in:
		-- Money == m1 | m2
		-- Then we want to generate: lifted_constructor(m1) because
		-- m1 was not re-written as a function...
		Vid'VType -> constructor_value
		Vid'Params -> nil
		-- generating the constructor:
		SAL_Gen_Type_Expr(Pos, TExpr -> _,CC_Type)
		where(CC_Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
		Tid'Lifted_Tid -> tid(LTid)
		LTid'Pos -> LPos
		LTid'Ident -> LId
		LTid'Constructor -> vid(ConstVid)
		where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(CC_Expr1, nil))) -> CC_Expr)
	    ||
		where(CC_Expr1 -> CC_Expr)
	    |)
	 ||
--Putmsg("Assuming local variable\n")
	    -- Generating a typical value expression occurences
	    -- One of the following:
	    --    Local variables
	    --	  Let bindings
	    -- Processing the qualification:
	    SAL_Proc_Qualification(OptQual -> Qualif)
	    where(SAL_VALUE_EXPR'sal_value_occ(val_id(IdOp), Qualif) -> SALExprout)
	    -- the same for the cc version:
	    where(SALExprout -> CC_Expr)
	 |)
	 

  'rule' Gen_SAL_Expr_(var_occ(Pos, VarId, _),_ -> SALExprout, SALExprout):
	 VarId'Pos -> Pos1
	 look_up_variable_id(Pos1 -> OptVarId)
	 (|
		where(OptVarId -> var(SAL_Var_id))
		where(sal_var_occ(Pos, SAL_Var_id) -> SALExprout)
	 ||
		Puterror(Pos)
		Putmsg("Internal error: SAL variable identifier not found\n")
		where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 |)

	 -- not supported
  'rule' Gen_SAL_Expr_(pre_occ(Pos, _, _),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("prename occurrences not supported")
	 Putnl()

-- special code to deal with x isin {a..b}
-- as if a <= x then x <= b else false end [x just an identifier]
-- or let y_ = x in if a <= y_ then y_ <= b else false end end

  'rule' Gen_SAL_Expr_(infix_occ(Pos, LeftValueExpr, Valueid, OptQual,
				RightValueExpr), TExpr -> SALExprout, CC_Expr):
	 Id_of_isin_set -> Isin
	 eq(Valueid, Isin)
	 where(RightValueExpr -> ranged_set(_, Left, Right))
	 Id_of_le_int -> Leq
	 (|
	   -- x is often just an identifier,
	   -- so avoid a let in this case
	   where(LeftValueExpr -> VALUE_EXPR'val_occ(_,_,_))
	   where(LeftValueExpr -> V)
	   where(LET_DEFS'nil -> LDs)
	 ||
	   string_to_id("y_" -> Id)
	   New_value_id(Pos, id_op(Id) -> Vid)
	   Vid'Type <- int
	   where(VALUE_EXPR'val_occ(Pos, Vid, nil) -> V)
	   where(binding(Pos, single(Pos, id_op(Id))) -> LB)
	   where(LET_DEFS'list(explicit(Pos, LB, LeftValueExpr), nil) -> LDs)
	 |)
	 where(VALUE_EXPR'infix_occ(Pos, Left, Leq, nil, V) -> E1)
	 where(VALUE_EXPR'infix_occ(Pos, V, Leq, nil, Right) -> E2)
	 where(region(Pos,Pos) -> Region)
	 where(VALUE_EXPR'if_expr(Pos, E1, E2, Region, nil,
			    else(Pos, literal_expr(Pos, bool_false))) -> If)
	 (|
	   eq(LDs, nil)
	   Gen_SAL_Expr_(If, TExpr -> SALExprout, CC_Expr)
	 ||
	   Gen_SAL_Expr_(let_expr(Pos, LDs, If), TExpr -> SALExprout, CC_Expr)
	 |)

  'rule' Gen_SAL_Expr_(infix_occ(Pos, LeftValueExpr, Valueid, OptQual,
				RightValueExpr), TExpr -> SALExprout, CC_Expr):
	 Valueid'Ident -> IdorOp
	 Valueid'Pos -> Pos1

	 Make_results(LeftValueExpr -> list(result(LeftType, _,_,_,_),_))
	 Make_results(RightValueExpr -> list(result(RightType, _,_,_,_),_))

	 Gen_SAL_Expr(LeftValueExpr, normal, LeftType -> LeftSALExpr, Left_CC_Expr)
	 Gen_SAL_Expr(RightValueExpr, normal, RightType -> RightSALExpr, Right_CC_Expr)

	 Valueid'Qualifier -> Ids

	 SAL_Reduce_to_finite_collections(LeftType -> LeftType1)
	 SAL_Reduce_to_finite_collections(RightType -> RightType1)

--Putmsg("------------------------------------------------------------------------------\n")
--Print_expr(infix_occ(Pos, LeftValueExpr, Valueid, OptQual,RightValueExpr))
--Putmsg("\n------------------------------------------------------------------------------\n")
--Print_expr(LeftValueExpr)
--Putmsg(": ")
--Print_type(LeftType1)
--Putnl()
--Print_expr(RightValueExpr)
--Putmsg(": ")
--Print_type(RightType1)
--Putnl()
--print(Right_CC_Expr)
--[|
--where(Right_CC_Expr -> sal_esp_value_occ(Vid11))
--SAL_Print_Vid(Vid11)
--|]
	 Gen_SAL_Id_Op(Pos, IdorOp, LeftType1, RightType1 -> IdOp, CC_IdOp) -- here, the distinction is necessary!
	 (| -- operator symbol
	   where(IdOp -> sal_op_symb(Op))
	   Valueid'Type -> T
	   Split_fun_type(T -> D, R) --cc.g
	   SAL_Disambiguate_op(Op, D, R -> Op1)
	   (| -- qualified
	     look_up_value_id(Pos -> OptCid)
	     ne(OptCid,nil)
	     SAL_Proc_Qualification(OptQual -> Qualif)
	     where(sal_funct_expr(val_id(sal_op_symb(Op1)),Qualif,
			 LeftSALExpr, RightSALExpr) -> SALExprout)
	   ||
	     -- infix_op
	     where(Op1 -> sal_infix_op(_))
	     -- Get the current context:
	     SAL_Current_Cid -> Cid
	     -- Generating the type element:
	     Valueid'Type -> TypeExpr
--	     SAL_Gen_Type_Expr(Pos, TypeExpr -> TElem)
--	     New_SAL_value_id(Pos, IdOp, Cid, TElem,regular_value -> Vid)
	     where(SAL_VALUE_EXPR'sal_infix_occ(LeftSALExpr, 
	       val_id(sal_op_symb(Op1)), RightSALExpr) -> SALExprout)
	   || -- prefix_op
	     where(Op -> sal_prefix_op(_))
	     Puterror(Pos)
	     Putmsg("internal - prefix_op in an infix_occ")
	     Putnl()
	     where(SAL_VALUE_EXPR'nil -> SALExprout)
	   ||
	     where(Op -> sal_function_op(hash))
             -- For functions the whole application is turned into a LAMBDA function:
	     -- Get the type of the domain of the second function:
	     Split_fun_type(RightType -> SecondFunctionDom, _)
	     IncreaseCol(Pos -> IncPos)
	     SAL_Gen_Type_Expr(IncPos, SecondFunctionDom -> SALSecondFunctionDom, _)
	     -- Generate the ' x' identifier:
	     string_to_id("x" -> XId)
	     where(SAL_ID_OP'id(XId) -> IdOp11)
	     -- Building the SAL_Binding:
	     where(sal_typed_id(Pos, IdOp11, SALSecondFunctionDom) -> Binding)
	     where(SAL_LAMBDA_BINDING'bindings(SAL_BINDINGS'list(Binding,nil))-> LambdaBinding)
	     where(SAL_LAMBDA_BINDINGS'list(LambdaBinding,nil) -> LambdaBindings)
	     -- Generating the application:
	     -- Translate the right hand part of the hash (it should be a function)
	     IncreaseCol(IncPos -> IncPosI)
	     Gen_SAL_Expr(RightValueExpr, normal, RightType -> InnerFunction, _)
	     where(sal_funct_applic(InnerFunction, sal_argument(list(sal_value_occ(val_id(id(XId)),nil),nil))) -> InnerApplication)
	     -- Going to process the function in the left side of the hash operator:
	     Gen_SAL_Expr(LeftValueExpr, normal, LeftType -> OuterFunction, _)
	     where(sal_funct_applic(OuterFunction, sal_argument(list(InnerApplication,nil))) -> ApplicationExpr)
	     -- Building up the LAMBDA expression:
	     where(sal_function(LambdaBindings, ApplicationExpr) -> SALExprout)
	   || -- function_op (handled as built in operations in SAL)
	     where(Op1 -> sal_function_op(_))
	     SAL_Proc_Qualification(OptQual -> Qualif)
	     where(sal_funct_expr(val_id(sal_op_symb(Op1)),Qualif, LeftSALExpr,
                              RightSALExpr) -> SALExprout)
	   |)
	 ||
	   (| -- Set function detected...
             where(IdOp -> sal_set_op(Op1,T1,Tid))
	     Valueid'Type -> T
	     Split_fun_type(T -> D, R) --cc.g
	     SAL_Disambiguate_op(Op1, D, R -> Op2)
	     (|
	       -- replace s union {e} and {e} union s by add(e,s)
	       where(Op2 -> sal_function_op(union))
	       (| -- first check for singleton on right
	         where(RightSALExpr -> sal_enum_set(_, _, list(E, nil)))
		 where(LeftSALExpr -> S)
	       || -- else check for singleton on left
	         where(LeftSALExpr -> sal_enum_set(_, _, list(E, nil)))
		 where(RightSALExpr -> S) 
	       |)
	       where(SAL_VALUE_EXPR'sal_esp_prefix_occ(
	         val_id(sal_set_op(sal_function_op(add_set),T1,Tid)), E, S) -> SALExprout)
	     ||
	       where(SAL_VALUE_EXPR'sal_esp_prefix_occ(
	         val_id(sal_set_op(Op2,T1,Tid)), LeftSALExpr, RightSALExpr) -> SALExprout)
	     |)		
	   || -- map function detected
	     where(IdOp -> sal_map_op(Op1,D1,R1,Tid))
	     (|
/* this makes no sense - removed CWG 12/4/07
	       (| where(Op1 -> sal_function_op(isin)) || where(Op1 -> sal_function_op(notisin)) |)
	       Tid'TExpr -> rsl_built_in(sal_finite_map(_,_,Range))
	       where(Range -> type_refs(sal_defined(_,_,MapRangeTid)))
	       MapRangeTid'TExpr -> user_defined(sal_variant_type(list(NIL_Part,list(Val_Part,_))))
	       (|
	         where(Op1 -> sal_function_op(notisin))
                 where(NIL_Part -> sal_part(Construct,_))
	       ||
	         where(Op1 -> sal_function_op(isin))
                 where(Val_Part -> sal_part(Construct,_))
	       |)
	       where(Construct -> sal_construc(_, ConsVid, _, _))
	       where(sal_argument(list(LeftSALExpr, nil)) -> Args)
	       where(sal_funct_applic(RightSALExpr, Args) -> MapApp)
	       where(sal_recogniser(ConsVid, sal_argument(list(MapApp, nil))) -> SALExprout)
	     ||
*/
		where(Op1 -> sal_function_op(hash))
		Puterror(Pos)
		Putmsg("'Hash' operator for maps not supported for model checking\n")
		where(SAL_VALUE_EXPR'nil -> SALExprout)
	     ||
		Valueid'Type -> T
		Split_fun_type(T -> D, R) --cc.g
		SAL_Disambiguate_op(Op1, D, R -> Op2)
		(|
		  -- replace m !! [d +> r] by add(d,r,s)
		  where(Op2 -> sal_function_op(override))
		  -- check for singleton maplet
		  where(RightSALExpr -> sal_enum_map(_, _, _, list(Pair, nil)))
		  where(Pair -> pair(DE, RE))
		  where(sal_esp_ternary_occ(val_id(sal_map_op(sal_function_op(add_map),D1,R1,Tid)), DE, RE, LeftSALExpr) -> SALExprout)
		||  
		  where(SAL_VALUE_EXPR'sal_esp_prefix_occ(
		    val_id(sal_map_op(Op2,D1,R1,Tid)), LeftSALExpr, RightSALExpr) -> SALExprout)
		|)
             |)
	   || -- list function detected (not supported, but...)
	     where(IdOp -> sal_list_op(Op1,T1))
	     Valueid'Type -> T
	     Split_fun_type(T -> D, R) --cc.g
	     SAL_Disambiguate_op(Op1, D, R -> Op2)
	     where(SAL_VALUE_EXPR'sal_esp_prefix_occ(
	        val_id(sal_list_op(Op2,T1)), LeftSALExpr, RightSALExpr) -> SALExprout)
           || -- Speciall INT operations:
	     where(IdOp -> sal_int_op(Op1, IntCid))
	     where(SAL_VALUE_EXPR'sal_esp_prefix_occ(
	        val_id(sal_int_op(Op1, IntCid)), LeftSALExpr, RightSALExpr) -> SALExprout)
	      
	   |)
	 || -- not an operator symbol
	   where(SAL_VALUE_EXPR'nil -> SALExprout)
	 |)

	 -- cc part...
	 -- handling the operations...
	 (|
	     where(CC_IdOp -> sal_op_symb(Op))
	     (|
	        where(Op -> sal_function_op(hash))
		-- For functions the whole application is turned into a LAMBDA function:
		-- Get the type of the domain of the second function:
		Split_fun_type(RightType -> SecondFunctionDom, _)
		IncreaseCol(Pos -> IncPos)
		SAL_Gen_Type_Expr(IncPos, SecondFunctionDom -> _, SALSecondFunctionDom)
		-- Generate the ' x' identifier:
		string_to_id("x" -> XId)
		where(SAL_ID_OP'id(XId) -> IdOp11)
		-- Building the SAL_Binding:
		where(sal_typed_id(Pos, IdOp11, SALSecondFunctionDom) -> Binding)
		where(SAL_LAMBDA_BINDING'bindings(SAL_BINDINGS'list(Binding,nil))-> LambdaBinding)
		where(SAL_LAMBDA_BINDINGS'list(LambdaBinding,nil) -> LambdaBindings)
		-- Generating the application:
		-- Translate the right hand part of the hash (it should be a function)
		IncreaseCol(IncPos -> IncPosI)
		Gen_SAL_Expr(RightValueExpr, normal, RightType -> InnerFunction, _)
		where(sal_funct_applic(InnerFunction, sal_argument(list(sal_value_occ(val_id(id(XId)),nil),nil))) -> InnerApplication)
		-- Going to process the function in the left side of the hash operator:
		Gen_SAL_Expr(LeftValueExpr, normal, LeftType -> OuterFunction, _)
		where(sal_funct_applic(OuterFunction, sal_argument(list(InnerApplication,nil))) -> ApplicationExpr)
		-- Building up the LAMBDA expression:
		where(sal_function(LambdaBindings, ApplicationExpr) -> CC_Expr)
	     ||
	        -- the other option is a '=' or '~='  is found...  CHECK?
		where(sal_funct_expr(val_id(sal_op_symb(Op)),nil, Left_CC_Expr, Right_CC_Expr) -> CC_Expr)
	     |)
	 ||
	   (| -- replace s union {e} and {e} union s with add(e,s)
	     where(CC_IdOp -> sal_cc_op(sal_function_op(union), Tid))
	     (|
	       (|
		 -- singleton on right
		 where(Right_CC_Expr -> sal_enum_set(_, _, list(CC_E, nil)))
		 where(Left_CC_Expr -> CC_S)
	       ||
		 -- singleton on left
		 where(Left_CC_Expr -> sal_enum_set(_, _, list(CC_E, nil)))
		 where(Right_CC_Expr -> CC_S)
	       |)
	       where(SAL_VALUE_EXPR'sal_esp_prefix_occ(val_id(sal_cc_op(sal_function_op(add_set), Tid)), CC_E, CC_S) -> CC_Expr)
	     ||
	     -- another common pattern is 
	     -- union(s, IF Guard THEN {e} ELSE set_nav ENDIF)
	     -- and we can generate instead (since union is strict)
	     -- IF Guard THEN add(e,s) ELSE set_nav ENDIF
	       (|
		 -- singleton on right
		 where(Right_CC_Expr -> sal_if_expr(Guard, Then, nil, else(Else)))
		 where(Left_CC_Expr -> CC_S)
	       ||
	         -- singleton on left
		 where(Left_CC_Expr -> sal_if_expr(Guard, Then, nil, else(Else)))
		 where(Right_CC_Expr -> CC_S)
	       |)
	       -- check Then is a singleton
	       where(Then -> sal_enum_set(_, _, list(CC_E, nil)))
	       -- check Else is set_nav
	       where(Else -> sal_funct_applic(sal_esp_value_occ(Fid),_))
	       Tid'DefaultNav -> vid(NavConst)
	       eq(Fid, NavConst)
	       where(SAL_VALUE_ID'val_id(sal_cc_op(sal_function_op(add_set), Tid)) -> Op)
	       where(sal_if_expr(Guard, sal_esp_prefix_occ(Op, CC_E, CC_S), nil, else(Else)) -> CC_Expr)
	     |)
	   || -- replace m !! [d +> r] with add(d,r,s)
	     where(CC_IdOp -> sal_cc_op(sal_function_op(override), Tid))
	     -- check for singleton maplet
	     where(Right_CC_Expr -> sal_enum_map(_, _, _, list(CC_Pair, nil)))
	     where(CC_Pair -> pair(CC_DE, CC_RE))
	     where(SAL_VALUE_ID'val_id(sal_cc_op(sal_function_op(add_map),Tid)) -> Op)
	     where(sal_esp_ternary_occ(Op, CC_DE, CC_RE, Left_CC_Expr) -> CC_Expr)
	   ||
	     where(SAL_VALUE_EXPR'sal_esp_prefix_occ(val_id(CC_IdOp), Left_CC_Expr, Right_CC_Expr) -> CC_Expr)
	   |)
	 |)


  'rule' Gen_SAL_Expr_(prefix_occ(Pos, Valueid, OptQual, ValueExpr), TExpr
                      -> SALExprout, CC_Expr):
	 Valueid'Ident -> IdorOp
	 Valueid'Pos -> Pos1
	 Valueid'Qualifier -> Ids
	 -- There is no information here to get the type...
	 -- for example consider:
	 --     s isin rng berths(h),
	 -- prefix occ gets: rng berths(h) 
	 -- and the type is: s-type set
	 -- there is no way to determine, which type should be assigned to the 
	 -- right part of rng... so: ANY!x
-- CWG The above is rubbish
-- If it were not possible to reasonably get a type for 
-- the argument the type checker would have failed earlier
--	 Gen_SAL_Expr(ValueExpr, normal, any -> SALExpr, Left_CC_Expr)
	 Make_results(ValueExpr -> list(result(ArgType,_,_,_,_),_))
	 Gen_SAL_Expr(ValueExpr, normal, ArgType -> SALExpr, Left_CC_Expr)
	 

	 -- Obtain the types of both sides (needed for generating the
	 -- proper operation:
	 Get_Type_of_Value_Expr(ValueExpr -> LeftType)
	 Gen_SAL_Id_Op(Pos, IdorOp, LeftType,none -> IdOp, CC_IdOp)  -- here the distinction is also necessary
	 (| -- operator symbol
	   where(IdOp -> sal_op_symb(Op))
	   Valueid'Type -> T
	   Split_fun_type(T -> D, R)
	   SAL_Disambiguate_op(Op, D, R -> Op1)
	   (| -- infix_op
	     where(Op1 -> sal_infix_op(InfixOp))
	     ne(InfixOp, minus)
	     Puterror(Pos)
	     Putmsg("internal - infix_op in an prefix_occ")
	     Putnl()
	     where(SAL_VALUE_EXPR'nil -> SALExprout)
	   || -- prefix_op
	     where(Op1 -> sal_prefix_op(_))
	     eq(OptQual, nil)
	     where(SAL_VALUE_EXPR'sal_prefix_occ(
		val_id(sal_op_symb(Op1)), nil,SALExpr)
                   -> SALExprout)
	   || -- function_op
	     (| where(Op1 -> sal_function_op(_)) || ne(OptQual, nil) |)
	     SAL_Proc_Qualification(OptQual -> Qualif)
	     where(sal_funct_expr(val_id(sal_op_symb(Op1)), Qualif,
                              SALExpr, nil) -> SALExprout)
	   ||
	     eq(Op1, sal_identity)  -- int and real
	     where(SALExpr -> SALExprout)
	   |)
	 || -- not an operator symbol
	    -- It is a function invocation...
	    SAL_Proc_Qualification(OptQual -> Qualif)
	    where(sal_prefix_occ(val_id(IdOp), 
			Qualif,SALExpr) -> SALExprout)
	 |)
	 -- cc
	 -- handling the operations...
	 (|
	     where(CC_IdOp -> sal_op_symb(_))
	     -- there has been an error...
	     where(SAL_VALUE_EXPR'nil -> CC_Expr)
	 ||
	     (|
	        where(CC_IdOp -> sal_cc_op(sal_infix_op(minus), Type))
		where(SAL_VALUE_EXPR'sal_esp_unary_prefix_occ(val_id(sal_cc_op(sal_prefix_op(minus), Type)), Left_CC_Expr) -> CC_Expr)
	     ||
	        where(SAL_VALUE_EXPR'sal_esp_unary_prefix_occ(val_id(CC_IdOp), Left_CC_Expr) -> CC_Expr)
	     |)
	 |)


  'rule' Gen_SAL_Expr_(ass_occ(Pos, VarId, Qual, Expr),Type -> SALExprout, CC_Expr):
	 VarId'Pos -> VarPos
	 look_up_variable_id(VarPos -> OptSALVarId)
	 (|
	     where(OptSALVarId -> var(SALVarId))
	     where(sal_var_occ(Pos, SALVarId) -> SALLeftExpr)
	     where(SAL_VALUE_ID'val_id(sal_op_symb(sal_infix_op(eq))) -> Op)
	     VarId'Type -> VarType
	     Gen_SAL_Expr(Expr, normal, VarType -> SALRightExpr, SAL_CC_Right)
	     where(SAL_VALUE_EXPR'sal_infix_occ(SALLeftExpr,Op,SALRightExpr) -> SALExprout)
	     -- cc
	     where(SAL_VALUE_EXPR'sal_infix_occ(SALLeftExpr,Op,SAL_CC_Right) -> CC_Expr)
	 ||
	     where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	     where(SALExprout -> CC_Expr)
	     Puterror(Pos)
	     Putmsg("Internal error: No SAL information found for the variable occurrence.\n")
	     Putnl()
	 |)

	 -- not supported
  'rule' Gen_SAL_Expr_(input_occ(Pos, _, _),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("input_occ not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_SAL_Expr_(output_occ(Pos, _, _, _),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("output_occ not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_SAL_Expr_(env_local(Pos, Decls, ClassEnv, ValueExpr),_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'not_supported -> SALExprout)
	 Puterror(Pos)
	 Putmsg("env_local not supported")
	 Putnl()

  'rule' Gen_SAL_Expr_(no_val,_ -> SALExprout, SALExprout):
	 where(SAL_VALUE_EXPR'no_val -> SALExprout)

  'rule' Gen_SAL_Expr_(cc_expr(OptPos, String, _, ValueExpr), TExpr -> SALExprout, SALExprout):
	 Gen_SAL_Expr(ValueExpr, normal, TExpr -> SALExprout, _)

  'rule' Gen_SAL_Expr_(array_expr(P,S,V), TExpr -> SALExprout, CC_Expr)
         where(S -> single(_,B,T))
         --Define_value_binding(B,T) -- TODO: Skal nok ikke være her
         Gen_SALBindings_from_Typing(S -> TR1, TR2, PB)

         Get_Type_of_Value_Expr(array_expr(P, S, V) -> Type)
	 Type_is_array(TExpr -> Dom, Rng)
	 Gen_SAL_Expr_(V, Rng -> VR1, VR2)
         -- getting the tid:s
	 SAL_Check_Defined_Array(P,Dom,Rng -> OptTid)
	 (|
	         where(OptTid -> tid(ArrayTid))
	 ||
                 -- There is no array of this type, generate a new one:
                 Gen_Array_Type(P, Dom, P, Rng -> ArrayTid)
	 |)
	 (|
	        (| eq(Dom, any) || eq(Rng,any) |)
		    -- This is the case of: [] (type = any)
		    Get_Current_Disamb(-> Disamb)
	            (|
		       -- There is a disambiguation:
		       where(Disamb -> disamb(_, ValueExpr, TypeExpr))
		       -- And it disambiguates the current value:
		       eq(ValueExpr, array_expr(P, S, V))
		       -- use the type:
		       Type_is_array(TypeExpr -> Dom1, Rng1)
	            ||
		       Puterror(P)
		       Putmsg("No way to disambiguate the type of the value\n")
		       where(TYPE_EXPR'none -> Dom1)
		       where(TYPE_EXPR'none -> Rng1)
	            |)  
	         SAL_Gen_Type_Expr(P, Dom1 -> DomST, LDomST)
		 SAL_Gen_Type_Expr(P, Rng1 -> RngST, LRngST)
	 ||
	         -- Generating the type:
		 SAL_Gen_Type_Expr(P, Dom -> DomST, LDomST)
		 SAL_Gen_Type_Expr(P, Rng -> RngST, LRngST)
	 |)
         --Gen_SAL_Expr(Index, normal, Dom -> SALExpr, SAL_CC_Expr)
	 --Gen_SAL_ExprPairs(ValueExprPairs, nil, nil, Dom, Rng -> SALExprPairs, SAL_CC_Expr_Pairs)
	 where(SAL_VALUE_EXPR'sal_array_expr(TR1, DomST, VR1) -> SALExprout)
         ArrayTid'Lifted_Tid -> tid(LiftedArray)
	 LiftedArray'Constructor -> vid(ConstVid)
  Select_CC_Result_Type(LRngST -> RngTid)
  RngTid'Constructor -> vid(ConstVidRng)
  Get_Ident_From_Binding(TR2 -> IdentRng)
  Select_CC_Result_Type(LDomST -> DomTid)
  DomTid'Constructor -> vid(ConstVidDom)
  Get_Ident_From_Binding(TR2 -> IdentDom)
  where(sal_funct_applic(sal_esp_value_occ(ConstVidDom), sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(IdentRng)),nil), nil))) -> InitExpr)
  RngTid'Lifted_fields -> Fields
  SAL_Find_Accesor_in_Fields(Fields, ConstVidRng -> AccessorVid)
  where(sal_esp_value_occ(AccessorVid) -> Acc)
  where(sal_funct_applic(Acc, sal_argument(list(VR2, nil))) -> VR2B)

  where(sal_let_expr(IdentRng, LDomST, nil, nil, InitExpr, VR2B) -> CC_Let_Expr)
         where(SAL_VALUE_EXPR'sal_array_expr(TR1, LDomST, CC_Let_Expr) -> CC_Expr11)
	 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(CC_Expr11,nil))) -> CC_Expr1)
	 -- cc
	 --ArrayTid'Lifted_Tid -> tid(LiftedArray)
	 --where(SAL_VALUE_EXPR'sal_array_access(LiftedArray, SAL_CC_Expr) -> CC_Expr1)
	 -- Adding verifications for the elements being added to the set...
	 -- This type correctness verification on insertion ensures (by construction) that the
	 -- set contains valid elements (and avoids quantified verifications...)
	 --SAL_Gen_Is_In_Condition_for_Pairs(Index, Dom,Rng -> Condition)
         Isin_subtype(V, Rng -> Condition)
	 (|
	      eq(Condition, no_val)
	      where(CC_Expr1 -> CC_Expr)
	 ||
              Simplify(Condition -> Condition1)
	      Get_Invalid_Insertion_Nav(-> NavValId)
	      Gen_SAL_Expr(Condition1, normal, bool -> _, CC_Condition1)
              -- make is_true operator
	      Default_Bool_Tid -> BTid
	      BTid'Lifted_Tid -> tid(LBTid)
	      where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	      where(sal_esp_unary_prefix_occ(val_id(SAL_Op), CC_Condition1) -> CC_Condition2)
              SAL_Turn_Bindings_into_Lets(TR2, CC_Condition2, PB -> CC_Condition3, _) -- TODO Should one use the the SAL_BINDINGS returned.
	      where(sal_quantified(forall, bindings(TR1), CC_Condition3) -> CC_Condition)
	      SAL_Gen_Type_Expr(P, array(Dom,Rng) -> _, ArrayType)
	      SAL_Generate_Result_for_Violation(ArrayType, sal_esp_value_occ(NavValId) -> WrongApplExpr)
	      where(sal_if_expr(CC_Condition, CC_Expr1, nil, else(WrongApplExpr)) -> CC_Expr)
	 |)


	 -- not supported

  'rule' Gen_SAL_Expr_(array_access(P,N,I), T -> SALExprOut, SAL_CC_ExprOut)
         Get_Type_of_Value_Expr(N -> Temp)
         Remove_Brackets(Temp -> array(TI,TV))
         Gen_SAL_Expr(N, normal, array(TI,TV) -> SALExprOut1, SAL_CC_ExprOut1)
         Gen_SAL_Expr(I, normal, TI -> SALExprOut2, SAL_CC_ExprOut2A)
         where(sal_array_access(SALExprOut1, SALExprOut2) -> SALExprOut)

         SAL_Check_Defined_Array(P, TI, TV -> tid(Tid))

         Isin_subtype(I, TI -> Condition)
	 (|
	   eq(Condition, no_val)
           where(SAL_CC_ExprOut2A -> SAL_CC_ExprOut2)
	 ||
           Get_Invalid_Insertion_Nav(-> NavValId)
	   Gen_SAL_Expr(Condition, normal, bool -> _, CC_Condition1)
	   -- make is_true operator
	   Default_Bool_Tid -> BTid
	   BTid'Lifted_Tid -> tid(LBTid)
	   where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	   where(sal_esp_unary_prefix_occ(val_id(SAL_Op), CC_Condition1) -> CC_Condition)
           DefaultPos(-> P1)
	   SAL_Gen_Type_Expr(P1, TI -> _, CC_Type)
	   SAL_Generate_Result_for_Violation(CC_Type, sal_esp_value_occ(NavValId) -> WrongApplExpr)
	   where(sal_if_expr(CC_Condition, SAL_CC_ExprOut2A, nil, else(WrongApplExpr)) -> CC_Expr)
           where(CC_Expr -> SAL_CC_ExprOut2)
	  |)


         where(sal_cc_array_access(SAL_CC_ExprOut1, SAL_CC_ExprOut2, Tid) -> SAL_CC_ExprOut)


  'rule' Gen_SAL_Expr_(V,T -> nil, nil):
	 Putmsg("Debugging in SAL EXPR\n")
	 Print_type(T)
	 Putnl()
	 Print_expr(V)
print(V)
	 Putnl()
--	 print(V)

-------------------------------------------------

'action' SAL_Gen_Array_Index_Conditions(VALUE_EXPRS, TYPE_EXPR, SAL_VALUE_EXPRS -> SAL_VALUE_EXPRS)
  'rule' SAL_Gen_Array_Index_Conditions(nil, _, nil -> nil)

  'rule' SAL_Gen_Array_Index_Conditions(list(H,T), Type, list(SAL_H, SAL_T) -> list(HRes, TRes))
         Remove_Brackets(Type -> array(IT, VT))
         SAL_Gen_Array_Index_Condition(H, IT, SAL_H -> HRes)
         SAL_Gen_Array_Index_Conditions(T, VT, SAL_T -> TRes)

'action' SAL_Gen_Array_Index_Condition(VALUE_EXPR, TYPE_EXPR, SAL_VALUE_EXPR -> SAL_VALUE_EXPR)
  'rule' SAL_Gen_Array_Index_Condition(Index, Dom, Index2 -> SALExprout2)
                --Remove_Brackets(Temp -> array(Dom,Rng))
                Isin_subtype(Index, Dom -> Condition)
	        (|
	          eq(Condition, no_val)
                  where(Index2 -> SALExprout2)
	        ||
                  Get_Invalid_Insertion_Nav(-> NavValId)
	          Gen_SAL_Expr(Condition, normal, bool -> _, CC_Condition1)
	          -- make is_true operator
	          Default_Bool_Tid -> BTid
	          BTid'Lifted_Tid -> tid(LBTid)
	          where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	          where(sal_esp_unary_prefix_occ(val_id(SAL_Op), CC_Condition1) -> CC_Condition)
                  DefaultPos(-> P)
	          SAL_Gen_Type_Expr(P, Dom -> _, CC_Type)
	          SAL_Generate_Result_for_Violation(CC_Type, sal_esp_value_occ(NavValId) -> WrongApplExpr)
	          where(sal_if_expr(CC_Condition, Index2, nil, else(WrongApplExpr)) -> CC_Expr)
                  where(CC_Expr -> SALExprout2)
	          |)

-------------------------------------------------
'action' SAL_Gen_Is_In_Condition(VALUE_EXPRS, TYPE_EXPR -> VALUE_EXPR)

  'rule' SAL_Gen_Is_In_Condition(list(VE, Rest), Type -> Condition)
	 SAL_Gen_Is_In_Condition(Rest, Type -> CondRest)
	 Isin_subtype(VE, Type -> CurrentCond)
	 (|
	     eq(CurrentCond, no_val)
	     where(CondRest -> Condition)
	 ||
	     (|
	         eq(CondRest, no_val)
		 where(CurrentCond -> Condition)
	     ||
	         DefaultPos(-> P)
		 where(VALUE_EXPR'ax_infix(P, CurrentCond, and, CondRest, P) -> Condition)
	     |)
	 |)


  'rule' SAL_Gen_Is_In_Condition(nil, _ -> no_val)

'action' SAL_Gen_Is_In_Condition_for_Pairs(VALUE_EXPR_PAIRS, TYPE_EXPR, TYPE_EXPR -> VALUE_EXPR)

  'rule' SAL_Gen_Is_In_Condition_for_Pairs(list(pair(VE1, VE2), Rest), Type1, Type2 -> Condition)
	 SAL_Gen_Is_In_Condition_for_Pairs(Rest, Type1, Type2 -> CondRest)
	 Isin_subtype(VE1, Type1 -> CurrentCond1)
	 Isin_subtype(VE2, Type2 -> CurrentCond2)
	 DefaultPos(-> P)
	 (|
	     eq(CurrentCond1, no_val)
	     (|
	         eq(CurrentCond2, no_val)
		 where(CondRest -> Condition)
	     ||
	         (|
	             eq(CondRest, no_val)
		     where(CurrentCond2 -> Condition)
	         ||     
		     where(VALUE_EXPR'ax_infix(P, CurrentCond2, and, CondRest, P) -> Condition)
	         |)
	     |)  
	 ||
	     (|
	         eq(CurrentCond2, no_val)
		 (|
	             eq(CondRest, no_val)
		     where(CurrentCond1 -> Condition)
	         ||
		     where(VALUE_EXPR'ax_infix(P, CurrentCond1, and, CondRest, P) -> Condition)
	         |)
	     ||
		 where(VALUE_EXPR'ax_infix(P, CurrentCond1, and, CurrentCond2, P) -> Condition1)
		 (|
	             eq(CondRest, no_val)
		     where(Condition1 -> Condition)
	         ||
		     where(VALUE_EXPR'ax_infix(P, Condition1, and, CondRest, P) -> Condition)
	         |)
	     |)
	 |)

  'rule' SAL_Gen_Is_In_Condition_for_Pairs(nil, _, _ -> no_val)
-------------------------------------------------
-------------------------------------------------
'action' Gen_SAL_Cases(VALUE_EXPR, CASE_BRANCHES, TYPE_EXPR -> SAL_VALUE_EXPR, SAL_VALUE_EXPR)

  'rule' Gen_SAL_Cases(V, list(case(Pos, Patt, V1, _), BRS), TExpr -> SALExpr, CC_Expr)
	 Pattern_match(V, Patt -> Cond, LetDefs)
	 SAL_Process_Let_Defs(LetDefs, V1, TExpr -> SALExpr2, SAL_CC_Let_Expr)
	 Simplify(Cond -> Cond1)
	 (|   -- is it a record pattern?
	      where(Patt -> record_occ_pattern(_,_,_,_))
	      -- This case is handled diferently because an esp expression must be generated...
	      -- In record occ patterns, the occurrence of the constructor is used for matching the structure
	      -- In sal, a RECOGNIZED is needed (the name of the field + '?') so an special expr must be generated...
	      -- The problem is that yhe Cond generated in 'Pattern_match' has a normal val-occ and the translation of 
	      -- that will not generate anything but a sal-val-occ (which is not correct here!)....

	      -- We know that it is an application (it's a constructor) with only one arg(the argument of the case)
	      where(Cond1 -> application(_,val_occ(Pos1,ConstOcc,Q),  list(fun_arg(ArgPos, list(ArgOcc,nil)),nil)))
	      -- looking up for the value:
	      ConstOcc'Pos -> ConstPos
	      look_up_value_id(ConstPos -> OptConstVid)
	      (|
		  where(OptConstVid -> vid(ConstVid))
		  ConstVid'Lifted_Vid -> CC_ConstVid
		  ConstOcc'Type -> Type
		  Type_is_fun(Type -> Dom,_,_)
		  Gen_SAL_Expr(ArgOcc, argument, Dom -> SAL_Arg, SAL_CC_Arg)
		  -- Generating the condition: (special case)
		  where(sal_recogniser(ConstVid, sal_argument(list(SAL_Arg,nil))) -> SALCond)
		  -- cc
		  where(sal_recogniser(CC_ConstVid, sal_argument(list(SAL_CC_Arg,nil))) -> SAL_CC_Cond)
	      ||
		  Puterror(Pos)
		  Putmsg("Internal error: No value reference when processing pattern\n")
		  Gen_SAL_Expr(Cond1, normal, bool -> SALCond, SAL_CC_Cond)
	      |)
	 ||
	     -- list patterns --> Not allowed!
	     (|
		where(Patt -> enum_list(Pos1,_))
	     ||
		where(Patt -> conc_list(Pos1, _,_))
	     |)
	     Puterror(Pos1)
	     Putmsg("List patterns not accepted")
	     Gen_SAL_Expr(Cond1, normal, bool -> SALCond, SAL_CC_Cond) 
	 ||
	     Gen_SAL_Expr(Cond1, normal, bool -> SALCond, SAL_CC_Cond)
	 |)
	 -- adding the is_true for the cc if...
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 where(sal_cc_op(sal_function_op(is_true), LBTid) ->SAL_Op)
	 -- add is_true
	 where(sal_esp_unary_prefix_occ(val_id(SAL_Op),SAL_CC_Cond) -> Is_true_Expr)	   
	 (|
	   eq(Cond1, no_val)
	   -- comes from wildcard pattern
	   -- no need to translate more case branches
	   where(SALExpr2 -> SALExpr)
	   where(SAL_CC_Let_Expr -> CC_Expr)
	 ||
	   eq(BRS, nil)
	   -- last case
	   -- ignore Cond for non-cc version
	   where(SALExpr2 -> SALExpr)
	   -- add nav as else in cc version
	   Get_Swap_Nav(-> NavId)
	   SAL_Gen_Type_Expr(Pos, TExpr -> _, CC_Type)
	   SAL_Generate_Result_for_Violation(CC_Type,
				sal_esp_value_occ(NavId) -> SwapNavExpr)
	   where(SAL_VALUE_EXPR'sal_if_expr(Is_true_Expr, SAL_CC_Let_Expr, nil, else(SwapNavExpr)) -> CC_Expr)
	 ||
	   Gen_SAL_Cases(V, BRS, TExpr -> SALExpr3, SAL_CC_Expr3)
	   where(SAL_VALUE_EXPR'sal_if_expr(SALCond, SALExpr2, nil, else(SALExpr3)) -> SALExpr)
	   -- cc
	   where(SAL_VALUE_EXPR'sal_if_expr(Is_true_Expr, SAL_CC_Let_Expr, nil, else(SAL_CC_Expr3)) -> CC_Expr)
	 |)

'action' SAL_Proc_Qualification(OPT_QUALIFICATION -> SAL_OBJ_QUALIF)

  'rule' SAL_Proc_Qualification(qualification(OExpr) -> Qualif):
	 (|
	    where(OExpr -> obj_name(Name))
	    (|
	       where(Name -> name(Pos, IdOp))
	       (|
	          where(IdOp -> id_op(Ident))
		  ident_oid_look_up(Ident -> OptOid)
		  (|
		     where(OptOid -> oid(Oid))
		     where(SAL_OBJ_QUALIF'qualif(Oid) -> Qualif)
		  ||
		     Putmsg("Internal error! The object used for qualification does not exist internally.\n")
		     where(SAL_OBJ_QUALIF'nil -> Qualif)
		  |)
	       ||
	          Putmsg("Internal error? Instance qualification is an operation name\n")
		  where(SAL_OBJ_QUALIF'nil -> Qualif)
	       |)
	    ||
	       Putmsg("Internal error? Instance qualification is a qualified name\n")
	       where(SAL_OBJ_QUALIF'nil -> Qualif)
	    |)
	 ||
	    where(OExpr -> obj_occ(POS, RSL_Oid))
	    RSL_Oid'Pos -> Pos
	    look_up_object_id(Pos -> OptOid)
	    (|
		where(OptOid -> oid(Oid))
		where(SAL_OBJ_QUALIF'qualif(Oid) -> Qualif)
	    ||
		Putmsg("Internal error! The qualification does not exist internally.\n")
		where(SAL_OBJ_QUALIF'nil -> Qualif)
	    |)
	 ||
	    Putmsg("Internal error? Instance qualification is something...\n")   
	    where(SAL_OBJ_QUALIF'nil -> Qualif)
	 |)

  'rule' SAL_Proc_Qualification(nil -> nil)

----------------------------------------------------------------------------------
-- SAL_Turn_Bindings_into_Lets
----------------------------------------------------------------------------------

'action' GetTid(SAL_TYPE_EXPR -> SAL_type_id)
  'rule' GetTid(type_refs(sal_defined(_,_,Tid)) -> Tid)

  'rule' GetTid(rsl_built_in(boolean(Tid)) -> Tid)

  'rule' GetTid(rsl_built_in(integer(Tid)) -> Tid)

  'rule' GetTid(rsl_built_in(natural(Tid)) -> Tid)


'action' SAL_Turn_Bindings_into_Lets(SAL_BINDINGS, SAL_VALUE_EXPR, PRODUCT_TYPE -> SAL_VALUE_EXPR, SAL_BINDINGS)

  'rule' SAL_Turn_Bindings_into_Lets(list(sal_typed_id(P,IdOp,CC_Type), Rest), Body, list(T, RestT) -> Expr, BS)
	 SAL_Turn_Bindings_into_Lets(Rest, Body, RestT -> NewBody, RestBS)
	 where(IdOp -> id(Ident))
	 --where(CC_Type -> type_refs(sal_defined(_,_,Tid)))
         GetTid(CC_Type -> Tid)
	 Tid'Lifted_Tid -> tid(LTid)
	 LTid'Pos -> LPos
	 LTid'Ident -> LId
	 LTid'Constructor -> vid(ConstVid)
	 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(sal_value_occ(val_id(id(Ident)),nil), nil))) -> InitExpr)
	 where(sal_let_expr(Ident, type_refs(sal_defined(LPos,LId,LTid)), nil, nil, InitExpr, NewBody) -> Expr)
	 --
	 SAL_Turn_Type_into_Maximal_plus_restriction(T -> CC_Type1)
	 where(SAL_BINDINGS'list(sal_typed_id(P,IdOp,CC_Type1), RestBS) -> BS)

  'rule' SAL_Turn_Bindings_into_Lets(nil, Body, _ -> Body, nil)



--------------------------------------------------


'action' Gen_SAL_applic_Expr(POS, TYPE_EXPR, VALUE_EXPR, ACTUAL_FUNCTION_PARAMETER
						    -> SAL_VALUE_EXPR, SAL_VALUE_EXPR)

  'rule' Gen_SAL_applic_Expr(Pos, TypeExpr, ValueExpr, Arg ->
  SALExprout, SAL_CC_Application):
	 Gen_SAL_Expr(ValueExpr, argument, TypeExpr -> SALExpr,
	 SAL_CC_Expr)
	 (|
	   Make_function_type(TypeExpr -> TypeExpr1)
	   ne(TypeExpr1, none)
	   (|
	        where(SALExpr -> sal_esp_value_occ(Vid))
		--Vid'Params -> Params
                --print(Vid)
                --print(Params)
                --print(Arg)
		Gen_RSLFormal_Parameters(TypeExpr1 -> RSLParams)
		Gen_SALFormal_Parameters(RSLParams,TypeExpr1 ->	Params, _, CC_Params)
                --print(Params)
		SAL_Bind_Actual_to_Formal(Arg, Params -> SALArgs, SAL_CC_Args)
		where(SAL_VALUE_EXPR'sal_funct_applic(SALExpr, SALArgs) -> SALExprout)
		where(SAL_VALUE_EXPR'sal_funct_applic(SAL_CC_Expr, SAL_CC_Args)
					      -> SAL_CC_Application)
	   ||
	        -- This case is not so common:
		-- occurs, for example, when:
		-- f : T1 >< (T2 -> T3) -> T4
		-- f(a,f1) is ... f1(...)
		-- In this case, the ocurrence of f1 in the body
		-- doesn't have a Vid (because is a local function)
		where(ValueExpr -> val_occ(_, Valueid,_))
		Gen_RSLFormal_Parameters(TypeExpr1 -> RSLParams)
		Gen_SALFormal_Parameters(RSLParams,TypeExpr1 ->	Params, _, CC_Params)
		SAL_Bind_Actual_to_Formal(Arg, Params -> SALArgs, SAL_CC_Args)

		where(SAL_VALUE_EXPR'sal_funct_applic(SALExpr, SALArgs)
					      -> SALExprout)
		where(SAL_VALUE_EXPR'sal_funct_applic(SAL_CC_Expr, SAL_CC_Args)
					      -> SAL_CC_Application)
	   ||
	        -- Handles curried function application
		-- (i.e. when invoking a function defined as:
		--     f : T1 -> (T2 -> T3))
		--  you get something like:
		--     f(v1)(v2)
		--  where 'f(v1)' is the function that is applied to
		--  v2 (and there is no Vid for that either).
		where(ValueExpr -> application(_, ValueExpr2,_))
		Gen_RSLFormal_Parameters(TypeExpr1 -> RSLParams)
		Gen_SALFormal_Parameters(RSLParams,TypeExpr1 ->	Params, _, CC_Params)
		SAL_Bind_Actual_to_Formal(Arg, Params -> SALArgs, SAL_CC_Args)
		where(SAL_VALUE_EXPR'sal_funct_applic(SALExpr, SALArgs)
					      -> SALExprout)
		where(SAL_VALUE_EXPR'sal_funct_applic(SAL_CC_Expr, SAL_CC_Args)
					      -> SAL_CC_Application)
	   /*||
                where(SALExpr -> sal_var_occ(P,Vid))
		Gen_RSLFormal_Parameters(TypeExpr1 -> RSLParams)
		Gen_SALFormal_Parameters(RSLParams,TypeExpr1 ->	Params, _, CC_Params)
                SAL_Bind_Actual_to_Formal(Arg, Params -> SALArgs, SAL_CC_Args)

		where(SAL_VALUE_EXPR'sal_funct_applic(SALExpr, SALArgs)
					      -> SALExprout)
		where(SAL_VALUE_EXPR'sal_funct_applic(SAL_CC_Expr, SAL_CC_Args)
					      -> SAL_CC_Application)*/
           ||
	        Putmsg("Internal Error: Function without value identification\n")
		Print_expr(ValueExpr)
		Putnl()
		print(ValueExpr)
		where(SAL_VALUE_EXPR'nil -> SALExprout)
		where(SAL_VALUE_EXPR'nil -> SAL_CC_Application) 
	   |)
	   
         || -- It's a map:
	   Make_map_type(TypeExpr -> TypeExpr1)
	   ne(TypeExpr1, none)
	   Type_is_map(TypeExpr1 -> Dom, Rng)
	   Gen_SAL_Arguments(Arg, Dom -> SALArg, SAL_CC_Arg)
	   SAL_Check_Defined_Map(Pos,Dom,Rng -> OptTid)
	   (|
	      where(OptTid -> tid(MapTid))
	      where(SAL_VALUE_EXPR'sal_map_applic(MapTid, SALExpr, SALArg)
					      -> SALExprout)
	      -- for CC map applications we use the "apply"
	      -- function defined in the map_cc_OPS context
	      MapTid'Lifted_Tid -> tid(LMTid)

/*              Get_Subtype_Condition_From_Actual_Function_Parameter(Dom, Arg -> Condition)
                Get_Invalid_Insertion_Nav(-> NavValId)
	        Gen_SAL_Expr(Condition, normal, bool -> _, CC_Condition1)
	        -- make is_true operator
	        Default_Bool_Tid -> BTid
	        BTid'Lifted_Tid -> tid(LBTid)
	        where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	        where(sal_esp_unary_prefix_occ(val_id(SAL_Op), CC_Condition1) -> CC_Condition)
SAL_Gen_Type_Expr(Pos, fin_map(Dom,Rng) -> _, MapType)
	        SAL_Generate_Result_for_Violation(MapType, sal_esp_value_occ(NavValId) -> WrongApplExpr)
	      where(sal_if_expr(CC_Condition, SAL_CC_Expr, nil, else(WrongApplExpr)) -> SAL_CC_Expr1)*/


	      where(sal_cc_map_applic(LMTid, SAL_CC_Expr, SAL_CC_Arg)
					      -> SAL_CC_Application)

	   ||
	      Putmsg("Internal error: No map declaration found for the map aplication: ")
	      Print_expr(ValueExpr)
	      Putnl()
	      where(SAL_VALUE_EXPR'nil -> SALExprout)
	      where(SAL_VALUE_EXPR'nil -> SAL_CC_Application) 
	   |)
         || -- must be a list
/*
	   Make_list_type(TypeExpr -> TypeExpr1)
	   Gen_SAL_Arguments(Arg,TypeExpr1 -> SALArg)
	   where(SAL_VALUE_EXPR'sal_list_applic(SALExpr, SALArg)
					      -> SALExprout)
*/
	     -- lists are not accepted... just recovering...
	     where(SAL_VALUE_EXPR'nil -> SALExprout)
	     where(SAL_VALUE_EXPR'nil -> SAL_CC_Application)   
	 |)


'action' Get_Subtype_Condition_From_Actual_Function_Parameter(TYPE_EXPR, ACTUAL_FUNCTION_PARAMETER -> VALUE_EXPR)
  'rule' Get_Subtype_Condition_From_Actual_Function_Parameter(T, fun_arg(P,VE) -> Res)
         Get_Subtype_Condition_From_Value_Exprs(T, VE, P -> Res)

'action' Get_Subtype_Condition_From_Value_Exprs(TYPE_EXPR, VALUE_EXPRS, POS -> VALUE_EXPR)

  'rule' Get_Subtype_Condition_From_Value_Exprs(T, list(H,nil), _ -> Cond)
         Isin_subtype(H, T -> Cond)

  'rule' Get_Subtype_Condition_From_Value_Exprs(T, list(H,Tail), P -> Cond)
         Isin_subtype(H, T -> Cond1)
         Get_Subtype_Condition_From_Value_Exprs(T, Tail, P -> Cond2)
         where(VALUE_EXPR'ax_infix(P,Cond1,and,Cond2,P) -> Cond)

-------------------------------------------------------------------------------
-- SAL_Bind_Actual_to_Formal
-------------------------------------------------------------------------------
-- This procedure produces the binding between actual and formal
-- parameters.
-- This functionality is necessary due to the less powerful binding
-- mechanism in SAL. Expressions like:
-- f : T1 >< T2
-- f(...) is ...
--
-- a : (T1 >< T2)
-- f(a)
--
-- Need to be transformed to something like:
-- f(name1 : T1, name2 : T2) ...
-- a : [T1, T2]
-- f(a.1, a.2) <-- This is the resolution provided by this function
-------------------------------------------------------------------------------
'action' SAL_Bind_Actual_to_Formal(ACTUAL_FUNCTION_PARAMETER, 
				SAL_FORMAL_FUN_PARAMETERS -> SAL_ARGS, SAL_ARGS)

  'rule' SAL_Bind_Actual_to_Formal(fun_arg(Pos, ValueExprs), Parameters -> sal_argument(Arguments), sal_argument(CC_Arguments))
	 SAL_Internal_Bind_Actual_to_Formal(ValueExprs, Parameters -> Arguments, CC_Arguments)

--------------------------------------------------------------------------------
'action' SAL_Internal_Bind_Actual_to_Formal(VALUE_EXPRS,
				SAL_FORMAL_FUN_PARAMETERS -> SAL_VALUE_EXPRS, SAL_VALUE_EXPRS)

  'rule' SAL_Internal_Bind_Actual_to_Formal(Acts:list(V1, RestActual),
				list(Param, RestParam) -> Arguments, CC_Arguments)

	 where(Param -> formal_param(_,_, RSL_Type))	 

	 (|
	    -- Simplest case, only one argument:
	    eq(RestActual, nil)
	    eq(RestParam, nil)
	    Gen_SAL_Expr(V1, argument, RSL_Type -> Actual, CC_Actual)
	    where(SAL_VALUE_EXPRS'list(Actual,nil) -> Arguments)
	    where(SAL_VALUE_EXPRS'list(CC_Actual,nil) -> CC_Arguments)

	 ||
	    -- The actual is a singleton but the formal is a list:
	    -- For example:
	    -- f : T1 >< T2 ...
	    -- f(a,b) is ...
	    -- value1 : (T1 >< T2)
	    -- f(value1)
	    eq(RestActual, nil)
	    ne(RestParam, nil)
	    -- The code should be generated like:
	    -- f(value1.1, value1.2)

	    Gen_SAL_Expr(V1, argument, RSL_Type -> Actual, CC_Actual)
	    where(Actual -> sal_value_occ(val_id(IdOp), _))
	    SAL_Gen_Arg_Names_for_Tuple(IdOp, list(Param, RestParam) -> Arguments)
	    -- 
	    -- CORRECT THIS... THIS IS JUST AN STUB IN ORDER TO COMPILE
	    -- SHOULD BE REMOVED AND CHANGED FOR SOMETHING APPROPRIATE
	    -- But will only be possible to be defined when the functor
	    -- for the modified value expressions get known....
	    -- For example:
	    -- T : T1 >< T2
	    -- f : T1 >< T2
	    -- f(a,b) ...
	    -- val1 : T;
	    -- f(val1) --> f(val1.1, val1.2) in the normal translation

	    -- for the CC version, it should be something:
	    -- f(val1) --> f(value(val1).1, value(val1).2)  --- The accesor should be used first (in order to remove the lifting)
	    -- so the proper accesor should be obtained first and the name generation 
	    -- routine be modified appropriately...
	    where(Arguments -> CC_Arguments) -- CHANGE THIS!
	 ||
	    -- added by cwg
	    -- The actual is a list and the formal a singleton
	    ne(RestActual, nil)
	    eq(RestParam, nil)
	    Type_is_product(RSL_Type -> TS)
	    Gen_SAL_Exprs_for_product(Acts, nil, nil, TS -> Arguments, CC_Arguments)
	 ||
	    ne(RestActual, nil)
	    ne(RestParam, nil)
	    -- Both list have more than one element.
	    -- As the RSL spec did type checked, this means that there
	    -- exists a one-to-one mapping between the actual and the
	    -- formal parameters...

	    Gen_SAL_Expr(V1, argument, RSL_Type -> Actual, CC_Actual)
	    SAL_Internal_Bind_Actual_to_Formal(RestActual, RestParam -> RestArgs, CC_RestArgs)
	    where(SAL_VALUE_EXPRS'list(Actual, RestArgs) -> Arguments)
	    where(SAL_VALUE_EXPRS'list(CC_Actual, CC_RestArgs) -> CC_Arguments)
	 |)   


  'rule' SAL_Internal_Bind_Actual_to_Formal(nil,nil -> nil, nil)

  'rule' SAL_Internal_Bind_Actual_to_Formal(Actual, Formal -> nil,nil)
	 Putmsg("Debugging predicate activated in: SAL_Internal_Bind_Actual_to_Formal\n")
	 Putmsg("Actual:\n")
	 print(Actual)
	 Putmsg("Formal:\n")
	 print(Formal)
	 Putmsg("Actual:\n")
	 Print_exprs(Actual)
	 Putnl()
	 Putmsg("---------------------------------------\n")
--------------------------------------------------
--------------------------------------------------
'action' Gen_SAL_literal_expr(POS, VALUE_LITERAL, TYPE_EXPR -> SAL_VALUE_EXPR, SAL_VALUE_EXPR)

  'rule' Gen_SAL_literal_expr(Pos, unit,_ -> SALExpr, SALExpr):
	 where(SAL_VALUE_EXPR'unit -> SALExpr)
         
  'rule' Gen_SAL_literal_expr(Pos, bool_true,_ -> SALExpr, CC_Expr):
	 where(SAL_VALUE_EXPR'sal_literal(bool_true) -> SALExpr)
	 -- cc
	 -- Getting the proper constructor:
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LiftedBTid)
	 LiftedBTid'Constructor -> vid(ConstVid)
	 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(SALExpr, nil))) -> CC_Expr)
        
  'rule' Gen_SAL_literal_expr(Pos, bool_false,_ -> SALExpr, CC_Expr):
	 where(SAL_VALUE_EXPR'sal_literal(bool_false) -> SALExpr)
 	 -- cc
	 -- Getting the proper constructor:
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LiftedBTid)
	 LiftedBTid'Constructor -> vid(ConstVid)
	 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(SALExpr, nil))) -> CC_Expr)
	
  'rule' Gen_SAL_literal_expr(Pos, int(Val), TExpr -> SALExpr, CC_Expr):
	 SAL_Match_Type(Pos, TExpr, nat, no)
	 where(SAL_VALUE_EXPR'sal_literal(integ(Val)) -> SALExpr)
	 -- cc
	 -- Getting the proper constructor:
	 Default_Int_Tid -> ITid
	 ITid'Lifted_Tid -> tid(LiftedITid)
	 LiftedITid'Constructor -> vid(ConstVid)
	 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(SALExpr, nil))) -> CC_Expr)

  'rule' Gen_SAL_literal_expr(Pos, int(Val), TExpr -> SALExpr, CC_Expr):
	 where(SAL_VALUE_EXPR'sal_literal(integ(Val)) -> SALExpr)
	 -- cc
	 -- Getting the proper constructor:
	 Default_Int_Tid -> ITid
	 ITid'Lifted_Tid -> tid(LiftedITid)
	 LiftedITid'Constructor -> vid(ConstVid)
	 where(sal_funct_applic(sal_esp_value_occ(ConstVid), sal_argument(SAL_VALUE_EXPRS'list(SALExpr, nil))) -> CC_Expr)

  'rule' Gen_SAL_literal_expr(Pos, real(Val),_ -> SALExpr, SALExpr):
	 where(SAL_VALUE_EXPR'not_supported -> SALExpr)
	 Puterror(Pos)
	 Putmsg("real not supported")
	 Putnl()
	 
  'rule' Gen_SAL_literal_expr(Pos, text(Val),_ -> SALExpr, SALExpr):
	 where(SAL_VALUE_EXPR'not_supported -> SALExpr)
	 Puterror(Pos)
	 Putmsg("text not supported")
	 Putnl()
	 
  'rule' Gen_SAL_literal_expr(Pos, char(Val),_ -> SALExpr, SALExpr):
	 where(SAL_VALUE_EXPR'not_supported -> SALExpr)
	 Puterror(Pos)
	 Putmsg("char not supported")
	 Putnl()


--------------------------------------------------
'action' Gen_SAL_Arguments(ACTUAL_FUNCTION_PARAMETER, TYPE_EXPR -> SAL_ARGS, SAL_ARGS)

  'rule' Gen_SAL_Arguments(fun_arg(Pos, ValueExprs), TExpr -> Argumentsout, CC_Argumentsout):
	 Gen_SAL_Exprs_Arguments(ValueExprs, nil, nil, TExpr -> SALExprs, SAL_CC_Exprs)
	 where(sal_argument(SALExprs) -> Argumentsout)
	 where(sal_argument(SAL_CC_Exprs) -> CC_Argumentsout)

'action' Gen_SAL_Exprs_Arguments(VALUE_EXPRS, SAL_VALUE_EXPRS, SAL_VALUE_EXPRS, TYPE_EXPR, -> SAL_VALUE_EXPRS, SAL_VALUE_EXPRS)

  'rule' Gen_SAL_Exprs_Arguments(list(ValueExpr, ValueExprsTail), SALExprs, SAL_CC_Exprs, TExpr -> SALExprsout, SAL_CC_Exprsout):
	 Gen_SAL_Expr(ValueExpr, normal, TExpr -> SALExpr, SAL_CC_ExprTemp)

         Isin_subtype(ValueExpr, TExpr -> Condition)
         (|
           where(Condition -> no_val)
           where(SAL_CC_ExprTemp -> SAL_CC_Expr)
         ||         
           Get_Invalid_Insertion_Nav(-> NavValId)
	   Gen_SAL_Expr(Condition, normal, bool -> _, CC_Condition1)
	   Default_Bool_Tid -> BTid
	   BTid'Lifted_Tid -> tid(LBTid)
	   where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	   where(sal_esp_unary_prefix_occ(val_id(SAL_Op), CC_Condition1) -> CC_Condition)
DefaultPos(-> Pos)
           SAL_Gen_Type_Expr(Pos, TExpr -> _, Type)
	   SAL_Generate_Result_for_Violation(Type, sal_esp_value_occ(NavValId) -> WrongApplExpr)
	   where(sal_if_expr(CC_Condition, SAL_CC_ExprTemp, nil, else(WrongApplExpr)) -> SAL_CC_Expr)
         |)

	 SAL_Insert_Expr(SALExpr, SALExprs -> SALExprs1)
	 SAL_Insert_Expr(SAL_CC_Expr, SAL_CC_Exprs -> SAL_CC_Exprs1)
	 Gen_SAL_Exprs_Arguments(ValueExprsTail, SALExprs1, SAL_CC_Exprs1, TExpr -> SALExprsout, SAL_CC_Exprsout)

  'rule' Gen_SAL_Exprs_Arguments(nil, SALExprs, SAL_CC_Exprs, _ -> SALExprs, SAL_CC_Exprs):

--------------------------------------------------
'action' SAL_Gen_Elsifs(ELSIF_BRANCHES, SAL_ELSIF_BRANCHES, SAL_ELSIF_BRANCHES, TYPE_EXPR -> SAL_ELSIF_BRANCHES, SAL_ELSIF_BRANCHES)

  'rule' SAL_Gen_Elsifs(list(Elsif, ElsifTail), SALElsifs, SAL_CC_Elsifs,TExpr -> SALElsifsout, SAL_CC_Elsifsout):
	 SAL_Gen_Elsif(Elsif, TExpr -> SALElsif, SAL_CC_Elsif)
	 SAL_Insert_Elsif(SALElsif, SALElsifs -> SALElsifs1)
	 -- cc
	 SAL_Insert_Elsif(SAL_CC_Elsif, SAL_CC_Elsifs -> SAL_CC_Elsifs1)

	 SAL_Gen_Elsifs(ElsifTail, SALElsifs1, SAL_CC_Elsifs1, TExpr -> SALElsifsout, SAL_CC_Elsifsout)


  'rule' SAL_Gen_Elsifs(nil, SALElsifs, SAL_CC_Elsifs, _ -> SALElsifs, SAL_CC_Elsifs):


'action' SAL_Gen_Elsif(ELSIF_BRANCH, TYPE_EXPR -> SAL_ELSIF_BRANCH, SAL_ELSIF_BRANCH)

  'rule' SAL_Gen_Elsif(elsif(Pos, If, Then, _), TExpr -> SALElsif, SAL_CC_Elsif):
	 Gen_SAL_Expr(If, normal, bool -> SALIf, SAL_CC_If)
	 Gen_SAL_Expr(Then, normal, TExpr -> SALThen, SAL_CC_Then)
	 where(SAL_ELSIF_BRANCH'elsif(SALIf, SALThen) -> SALElsif)
	 --cc
	 -- Adding the 'is_true' part in front of the condition...
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	 -- add is_true
	 where(sal_esp_unary_prefix_occ(val_id(SAL_Op), SAL_CC_If) -> Is_true_Expr)
	 where(SAL_ELSIF_BRANCH'elsif(Is_true_Expr, SAL_CC_Then) -> SAL_CC_Elsif)
	   

'action' SAL_Gen_Else(ELSE_BRANCH, TYPE_EXPR -> SAL_ELSE_BRANCH, SAL_ELSE_BRANCH)

  'rule' SAL_Gen_Else(else(Pos, ValueExpr), TExpr -> SALElse, SAL_CC_Else):
	 Gen_SAL_Expr(ValueExpr, normal, TExpr -> SALExpr, SAL_CC_Expr)
	 where(SAL_ELSE_BRANCH'else(SALExpr) -> SALElse)
	 -- cc
	 where(SAL_ELSE_BRANCH'else(SAL_CC_Expr) -> SAL_CC_Else)

  'rule' SAL_Gen_Else(nil,_ -> SALElse, SALElse):
	 where(SAL_ELSE_BRANCH'nil -> SALElse)


------------------------------------------------------
-- Generate LetBindings
--------------------------------------------------

'action' SAL_Process_Let_Defs(LET_DEFS, VALUE_EXPR, TYPE_EXPR -> SAL_VALUE_EXPR, SAL_VALUE_EXPR)

  'rule' SAL_Process_Let_Defs(list(LetDef, LetDefsTail), ValueExpr, TExpr ->  SAL_Expr, SAL_CC_Expr):
	 -- Only the last element in the let_defs list will generate
	 -- the value expression in the IN section (let body)
	 SAL_Process_Let_Def(LetDef, no_val, TExpr -> Id, TElem, CC_TElem, Namespace, Init, CC_Init, ValueExpr1, CC_ValueExpr1, Condition)
	 SAL_Process_Let_Defs(LetDefsTail,ValueExpr, TExpr -> ValueExpr2, CC_ValueExpr2)
	 SAL_Join_SAL_Let_Defs(ValueExpr1,ValueExpr2 -> SalExpr1)
	 -- For compatibility with other tools:
	 SAL_Gen_Let_Bindings(list(LetDef, LetDefsTail) -> Let_Bindings, CC_Let_Bindings)
	 where(sal_let_expr(Id, TElem, Namespace, Let_Bindings, Init, SalExpr1) -> SAL_Expr)
	 -- cc version:
	 SAL_Join_SAL_Let_Defs(CC_ValueExpr1,CC_ValueExpr2 -> Sal_CC_Expr1)
	 where(sal_let_expr(Id, CC_TElem, Namespace, CC_Let_Bindings, CC_Init, Sal_CC_Expr1) -> SAL_CC_Let_Expr)
	 -- all the rest is irrelevant since it duplicates
	 -- the precondition check on the reconstructor
	 -- so we just ...
	 where(SAL_CC_Let_Expr -> SAL_CC_Expr)
/*	 (|
	    eq(Condition, no_val)
	    where(SAL_CC_Let_Expr -> SAL_CC_Expr)
	 ||
	    Gen_SAL_Expr(Condition, normal, bool -> _, CC_Cond)
	    SAL_Current_Reconstructor -> value_id(RSLReconsVid)
	    RSLReconsVid'Pos -> P
	    IncreaseCol(P -> P1)
	    RSLReconsVid'Ident -> IdOp
	    where(IdOp -> id_op(Ident))
	    SAL_Gen_Type_Expr(P1, TExpr -> _, CC_Type)
	    id_to_string(Ident -> IdStr)
	    SAL_Current_Cid -> Cid
	    Cid'Ident -> CidId
	    id_to_string(CidId -> CidIdStr)
	    Concatenate3(CidIdStr, "_", IdStr -> NameStr) 
	    Concatenate3("Reconstructor_", NameStr, "_applied_to_wrong_variant" -> NavStr)
	    Extend_Nav_Type(P1, NavStr -> NavVid)
	    where(sal_esp_value_occ(NavVid) -> Expr4)
	    SAL_Generate_Result_for_Violation(CC_Type, Expr4 -> WrongApplExpr)
	    where(sal_if_expr(CC_Cond, SAL_CC_Let_Expr, nil, else(WrongApplExpr)) -> SAL_CC_Expr)
	 |)
*/

  'rule' SAL_Process_Let_Defs(nil,ValueExpr, TExpr -> SAL_Expr, SAL_CC_Expr):
	 Gen_SAL_Expr(ValueExpr, normal, TExpr -> SAL_Expr, SAL_CC_Expr)

-------------------------------------------------------
'action' SAL_Gen_Let_Bindings(LET_DEFS -> SAL_LET_BINDINGS, SAL_LET_BINDINGS)

  'rule' SAL_Gen_Let_Bindings(list(Def,Defs) -> LBS, CC_LBS)
	 SAL_Gen_Let_Binding(Def -> LBS1, CC_LBS1)
	 SAL_Gen_Let_Bindings(Defs -> LBS2, CC_LBS2)
	 SAL_Concat_LetBindings(LBS1, LBS2 -> LBS)
	 -- cc
	 SAL_Concat_LetBindings(CC_LBS1, CC_LBS2 -> CC_LBS)

  'rule' SAL_Gen_Let_Bindings(nil -> nil, nil)

'action' SAL_Gen_Let_Binding(LET_DEF -> SAL_LET_BINDINGS, SAL_LET_BINDINGS)

  'rule' SAL_Gen_Let_Binding(explicit(Pos, binding(_, single(P, Id)), ValueExpr)
				        -> list(LetBindingout, nil), list(CC_LetBindingout, nil)):
	 -- Extracting the type from the expression:
	 Get_Type_of_Value_Expr(ValueExpr -> TExpr)
	 Gen_SAL_Expr(ValueExpr, normal, TExpr -> SALExpr, CC_Expr)
	 Gen_SAL_Id_Op(P, Id,none,none -> IdOp, CC_IdOp)
	 -- Added... careful:
	 SAL_Gen_Type_Expr(Pos,TExpr -> STExpr, CC_Type)
	 where(SAL_BINDINGS'list(sal_typed_id(Pos, IdOp, STExpr),nil) -> BS)
	 where(sal_let_bind(sal_let_idop(IdOp, BS, nil), SALExpr) -> LetBindingout)
	 -- cc
	 -- generating the binding for the cc version:
	 where(SAL_BINDINGS'list(sal_typed_id(Pos, CC_IdOp, CC_Type),nil) -> CC_BS)
	 where(sal_let_bind(sal_let_idop(CC_IdOp, CC_BS, nil), CC_Expr) -> CC_LetBindingout)
	 

  'rule' SAL_Gen_Let_Binding(explicit(_, binding(_, product(_, BS)),  ValueExpr)
				        -> LBS, CC_LBS):
	 -- ignore disambiguation introduced by resolving
	 (|
	   where(ValueExpr -> disamb(_, ValueExpr1, _))
	 ||
	   where(ValueExpr -> ValueExpr1)
	 |)
	 -- Extracting the type from the expression:
	 Get_Type_of_Value_Expr(ValueExpr1 -> TExpr)
	 Gen_SAL_Expr(ValueExpr1, normal, TExpr -> SALExpr, CC_Expr)
	 SAL_Process_Let_Bindings(BS, nil -> LetBinds, LBS1, CC_LetBinds, CC_LBS1)
	 where(SAL_LET_BINDINGS'list(sal_let_binds(LetBinds, SALExpr), LBS1) -> LBS)
	 -- cc
	 where(SAL_LET_BINDINGS'list(sal_let_binds(CC_LetBinds, CC_Expr), CC_LBS1) -> CC_LBS)

  'rule' SAL_Gen_Let_Binding(explicit(Pos, pattern(Pos2, Pattern),
                         ValueExpr) -> LBS, CC_LBS):
	 -- ignore disambiguation introduced by resolving
	 (|
	   where(ValueExpr -> disamb(_, ValueExpr1, _))
	 ||
	   where(ValueExpr -> ValueExpr1)
	 |)
	 Pattern_match(ValueExpr1, Pattern -> ValueExpr2, LetDefs)
	 -- condition ValueExpr2 ignored as generates a CC in RSL
	 SAL_Gen_Let_Bindings(LetDefs -> LBS, CC_LBS)

  'rule' SAL_Gen_Let_Binding(implicit(Pos, Typing, Restriction) -> LBS, CC_LBS):
	 Typing_to_expr(Pos, Typing -> Expr)
	 Id_of_hd_set -> Ihd
	 where(VALUE_EXPR'comp_set(Pos, Expr, 
			     set_limit(Pos, list(Typing, nil), Restriction))
							 -> Set)
	 where(VALUE_EXPR'prefix_occ(Pos, Ihd, nil, Set) -> Expr2)
	 where(Typing -> single(_, Binding, _))
	 SAL_Gen_Let_Binding(explicit(Pos, binding(Pos, Binding), Expr2)
						     -> LBS, CC_LBS)

'action' SAL_Process_Let_Bindings(BINDINGS, SAL_LET_BINDINGS -> SAL_LETBINDS, SAL_LET_BINDINGS, SAL_LETBINDS, SAL_LET_BINDINGS)

  'rule' SAL_Process_Let_Bindings(list(single(P, Id), BS), LBGS ->
					     list(LB, LBS), LBGS1, list(CC_LB,CC_LBS),CC_LBGS1):
	 Gen_SAL_Id_Op(P, Id,none,none -> IdOp, CC_IdOp)
	 where(sal_let_idop(IdOp, nil, nil) -> LB)
	 SAL_Process_Let_Bindings(BS, LBGS -> LBS, LBGS1, CC_LBS, CC_LBGS1)
	 -- cc
	 where(sal_let_idop(CC_IdOp, nil, nil) -> CC_LB)


  'rule' SAL_Process_Let_Bindings(list(product(_, BS), BS1), LBGS ->
					     list(LB, LBS), LBGSOut,  -- non-cc results
					     list(LB, CC_LBS), CC_LBGSOut): -- cc results
	 SAL_Gen_Prod_Ident("" -> IdProd)
	 where(sal_let_idop(id(IdProd), nil, nil) -> LB)
	 SAL_Process_Let_Bindings(BS, LBGS -> LBS1, LBGS1, CC_LBS1, CC_LBGS1)
	 SAL_Process_Let_Bindings(BS1, LBGS1 -> LBS, LBGS2, CC_LBS, CC_LBGS2)
	 where(SAL_LET_BINDINGS'list(sal_let_binds(LBS1,
				sal_named_val(id_op(id(IdProd)))), LBGS2) -> LBGSOut)
	 -- cc
	 where(SAL_LET_BINDINGS'list(sal_let_binds(CC_LBS1,
				sal_named_val(id_op(id(IdProd)))), CC_LBGS2) -> CC_LBGSOut)

  'rule' SAL_Process_Let_Bindings(nil, LBGS -> nil, LBGS, nil, LBGS):


----------------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------------
'action' SAL_Concat_LetBindings(SAL_LET_BINDINGS, SAL_LET_BINDINGS -> SAL_LET_BINDINGS)

  'rule' SAL_Concat_LetBindings(list(B, BS), BS1 -> list(B, BS2)):
	 SAL_Concat_LetBindings(BS, BS1 -> BS2)

  'rule' SAL_Concat_LetBindings(nil, BS -> BS):

--------------------------------------------------
'action' SAL_Process_Let_Def(LET_DEF, VALUE_EXPR, TYPE_EXPR -> IDENT, 
				     SAL_TYPE_EXPR,   -- type for the normal version
				     SAL_TYPE_EXPR,   -- type for the cc-lifted type system
				     BINDING_NAMESPACE, -- Namespace for the non-cc version
				     SAL_VALUE_EXPR,  -- init for the normal version
				     SAL_VALUE_EXPR,  -- init for the cc version
				     SAL_VALUE_EXPR,  -- body expression in the non-cc
				     SAL_VALUE_EXPR,  -- body expr for the cc version
				     VALUE_EXPR)      -- If a condition was generated (a record pattern was found)

  'rule' SAL_Process_Let_Def(explicit(Pos, binding(P0, single(P, Id)), InitExpr),
			   VExpr, TExpr -> Ident, 
			   TElem, CC_TElem,
			   Namespace,
			   Init, CC_Init,
			   Body_Expr, CC_Body_Expr, no_val):

	 -- Get the type for the let:
	 Get_Type_of_Value_Expr(InitExpr -> InitTExpr)
	 where(Id -> id_op(Ident))
	 -- It is not necessary to generate a new identifier...
	 -- In this case, the identifier name is introduced in the let 
	 -- (it does not include a sub-binding), for example:
	 -- let e : f(...)
	 -- in this case, ' e ' should be used as identifier for the
	 -- let expression
	 -- Generating the type element:	 
	 SAL_Gen_Type_Expr(P, InitTExpr -> TElem, CC_TElem)
	 -- There is no need for namespace  here
	 -- (the namespace for lets is used to translate the names
	 -- introduced by the binding into field accesors... in this
	 -- case, there are no fields to acces.
	 where(BINDING_NAMESPACE'nil -> Namespace)
	 -- Generating the initialization expression: 
	 Gen_SAL_Expr(InitExpr, normal, InitTExpr -> Init, CC_Init)
	 -- Generate the body expression:
	 (|
	    eq(VExpr, no_val)
	    where(SAL_VALUE_EXPR'no_val -> Body_Expr)
	    where(Body_Expr -> CC_Body_Expr)
	 ||
	    Gen_SAL_Expr(VExpr, normal, TExpr -> Body_Expr, CC_Body_Expr)
	 |)


  'rule' SAL_Process_Let_Def(explicit(Pos, binding(_, product(Pos1, BS)),  InitExpr),
			   VExpr, TExpr -> Ident, 
			   TElem, CC_TElem,
			   Namespace,
			   Init, CC_Init,
			   Body_Expr, CC_Body_Expr, no_val):


	 -- Get the type for the let:
	 Get_Type_of_Value_Expr(InitExpr -> InitTExpr)
	 -- Generate the identifier:
	 SAL_Gen_Let_Ident(-> Ident)
	 -- Generating the type element:	 
	 SAL_Gen_Type_Expr(Pos, InitTExpr -> TElem, CC_TElem)
	 -- Process the bindings...
	 where(SAL_ID_OP'id(Ident) -> IdOp)
	 SAL_Gen_Namespace_from_Bindings(Ident, BS -> Namespace)
	 -- Generate the init expr
	 Gen_SAL_Expr(InitExpr, normal, InitTExpr -> Init, CC_Init)
	 -- Generate the body expression:
	 (|
	    eq(VExpr, no_val)
	    where(SAL_VALUE_EXPR'no_val -> OriginalBody)
	    where(OriginalBody -> CC_Body_Expr)
	 ||
	    Gen_SAL_Expr(VExpr, normal, TExpr -> OriginalBody, CC_Body_Expr)
	 |)
	 where(OriginalBody -> Body_Expr)

  'rule' SAL_Process_Let_Def(explicit(Pos, pattern(Pos2, Pattern),Value), InitExpr, TExpr -> Ident, 
			   TElem, CC_TElem,
			   Namespace,
			   Init, CC_Init,
			   Body_Expr, CC_Body_Expr, SCond):

	 Pattern_match(Value, Pattern -> Condition, LetDefs)
	 Simplify(Condition -> SCond)
	 SAL_Process_Let_Defs(LetDefs, InitExpr, TExpr -> Expr, CC_Expr)
	 where(Expr -> sal_let_expr(Ident, TElem, _, _, Init, Body_Expr))
	 where(CC_Expr -> sal_let_expr(_, CC_TElem, Namespace, CC_Let_Bindings, CC_Init, CC_Body_Expr))

  'rule' SAL_Process_Let_Def(implicit(Pos, Typing, Restriction), InitExpr, TExpr -> Ident,
	 		   TElem, CC_TElem,
			   Namespace,
			   Init, CC_Init,
			   Body_Expr, CC_Body_Expr, no_val):

	 Puterror(Pos)
	 Putmsg("Implicit let expressions are not allowed\n")
	 Gen_SAL_Expr(InitExpr, normal, TExpr -> Init, CC_Init)
	 where(Init -> Body_Expr)
	 SAL_Gen_Let_Ident(-> Ident)
	 -- Generating the type element:	 
	 SAL_Gen_Type_Expr(Pos, TExpr -> TElem, CC_TElem)
	 where(BINDING_NAMESPACE'nil -> Namespace)
	 -- cc
	 -- stub for error recovery...
	 where(Init -> CC_Body_Expr)

---------------------------------------------------------
-- Generate SAL Bindings from RSL Typings and Bindings  -
---------------------------------------------------------

--------------------------------------------------
'action' SAL_Gen_Lambda_Bindings(TYPINGS -> SAL_LAMBDA_BINDINGS, SAL_LAMBDA_BINDINGS)

  'rule' SAL_Gen_Lambda_Bindings(list(Typing, TypingsTail) -> list(LambdaBinding, LambdaBindings),
							      list(CC_LambdaBinding, CC_LambdaBindings)):
	 Gen_SALBindings_from_Typing(Typing -> SALBindings, SAL_CC_B, _)
	 where(SAL_LAMBDA_BINDING'bindings(SALBindings) -> LambdaBinding)
	 SAL_Gen_Lambda_Bindings(TypingsTail -> LambdaBindings, CC_LambdaBindings)
	 -- cc
	 where(SAL_LAMBDA_BINDING'bindings(SAL_CC_B) -> CC_LambdaBinding)

  'rule' SAL_Gen_Lambda_Bindings(nil -> nil, nil):


--------------------------------------------------
'action' SAL_Gen_Lambda_Binding(LAMBDA_PARAMETER -> SAL_LAMBDA_BINDINGS, SAL_LAMBDA_BINDINGS)

  'rule' SAL_Gen_Lambda_Binding(l_typing(Pos, nil) -> nil, nil):
	 Puterror(Pos)
	 Putmsg("Unit type not supported")
	 Putnl()

  'rule' SAL_Gen_Lambda_Binding(l_typing(Pos, Typings) -> LambdaBindingsout, CC_LBS):
	 SAL_Gen_Lambda_Bindings(Typings -> LambdaBindingsout, CC_LBS)

  'rule' SAL_Gen_Lambda_Binding(s_typing(Pos, Typing) -> list(LambdaBinding, nil),
							 list(CC_LBS, nil)):
	 Gen_SALBindings_from_Typing(Typing -> SALBindings, CC_BS,_)
	 where(SAL_LAMBDA_BINDING'bindings(SALBindings) -> LambdaBinding)
	 --cc
	 where(SAL_LAMBDA_BINDING'bindings(CC_BS) -> CC_LBS)

	   

--------------------------------------------------
'action' Gen_SAL_Id_Op(POS, ID_OR_OP, TYPE_EXPR, TYPE_EXPR -> 
				      SAL_ID_OP, -- non-cc version
				      SAL_ID_OP) -- cc-version

  'rule' Gen_SAL_Id_Op(Pos, id_op(Ident),_,_ -> SAL_Id_or_op, SAL_Id_or_op):
	 where(SAL_ID_OP'id(Ident) -> SAL_Id_or_op)

  -- Does not matter wich type is it, '=' and '~=' are not handled specially in the non-cc version...
  'rule' Gen_SAL_Id_Op(Pos, op_op(eq),LT,_ -> sal_op_symb(sal_infix_op(eq)), CC_OP)
	 -- the cc version do changes it:
	 SAL_Gen_Type_Expr(Pos, LT -> _, LiftedT)
	 where(LiftedT -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 where(sal_cc_op(sal_infix_op(eq), Tid) -> CC_OP)	 

  'rule' Gen_SAL_Id_Op(Pos, op_op(neq),LT,_ -> sal_op_symb(sal_infix_op(neq)), CC_OP)
	 -- the cc version do changes it:
	 SAL_Gen_Type_Expr(Pos, LT -> _, LiftedT)
	 where(LiftedT -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 where(sal_cc_op(sal_infix_op(neq), Tid) -> CC_OP)

  'rule' Gen_SAL_Id_Op(Pos, op_op(rem), LT,RT -> SAL_Id_Op, SAL_CC_Id_Op)
	 -- This is the INTEGER DIVISION
	 -- In this case, the rem (modulo) operation 
	 -- does not match the semantic of the MOD operator in SAL
	 -- MUST BE TRANSLATED SEPARATELY in the case of integers...
	 -- ON THE OTHER HAND:   
	 -- The case of NAT or other subtypes of INT will not be treated in a different way.
	 -- This policy ensures semantic preservation (paying the cost of the invocation of
	 -- this special MODULO operator instead of the built in one). 
	 -- This is done in this way because it would be (in the general case) impossible to
	 -- determine when a subtype of Int ensures that there are no negative values inside the type.
	 -- In the worst case, we'll be paying the cost of extra checkings (for negative values) in cases
	 -- where they are not needed (they are ensured by the type's definition) but the SEMANTICS of MOD will
	 -- be preserved in ALL cases...
	 -- THUS, NO DISTINCTION AMONG INT SUBTYPES IS CARRIED OUT HERE!
	 -- Generating a new operator kind:
	 Match(LT, nil, int)
	 Match(RT, nil, int)
	 Gen_SAL_Op(Pos, rem -> SALOp)
	 Default_Int_Tid -> IntTid
	 where(sal_int_op(SALOp, IntTid) -> SAL_Id_Op)
	 -- cc part...
	 IntTid'Lifted_Tid -> tid(LTid)
	 where(sal_cc_op(SALOp, LTid) -> SAL_CC_Id_Op)

  'rule' Gen_SAL_Id_Op(Pos, op_op(Op), TL, TR -> SAL_Id_or_op, CC_IdOp):
	 Gen_SAL_Op(Pos, Op -> SALOp1)
	 SAL_Disambiguate_op(SALOp1, TL, TR -> SALOp)
	 (|
	    where(TYPE_EXPR'bool -> TE)
	    SAL_Match_Type(Pos, TL,  TE,yes)
	    SAL_Match_Type(Pos,TR, TE ,yes)
	    where(sal_op_symb(SALOp) -> SAL_Id_or_op)
	    -- cc
	    Default_Bool_Tid -> BoolTid
	    BoolTid'Lifted_Tid -> tid(Tid)
	    where(sal_cc_op(SALOp, Tid) -> CC_IdOp)
	 ||
	    where(TYPE_EXPR'nat -> TE)
	    SAL_Match_Type(Pos, TL, TE, no)
	    SAL_Match_Type(Pos, TR, TE, no)
	    where(sal_op_symb(SALOp) -> SAL_Id_or_op)
	    -- cc (uses Int + subtype check)
	    Default_Int_Tid -> IntTid
	    IntTid'Lifted_Tid -> tid(Tid)
	    where(sal_cc_op(SALOp, Tid) -> CC_IdOp)
         ||
            where(TYPE_EXPR'int -> TE)
	    SAL_Match_Type(Pos, TL, TE, yes)
	    SAL_Match_Type(Pos, TR, TE, yes)
	    where(sal_op_symb(SALOp) -> SAL_Id_or_op)
	    -- cc
	    Default_Int_Tid -> IntTid
	    IntTid'Lifted_Tid -> tid(Tid)
	    where(sal_cc_op(SALOp, Tid) -> CC_IdOp)
	 ||
	    where(SALOp -> sal_function_op(hash))
	    Type_is_fun(TL -> _,_,_)
	    Type_is_fun(TR -> _,_,_)
	    -- cc: keeping the same handling...
	    where(sal_op_symb(SALOp) -> SAL_Id_or_op)
	    where(SAL_Id_or_op -> CC_IdOp)
	 ||
	    -- Verifying if it is a set:
	    (|-- (both sides has set type)
	       Type_is_set(TL -> TExpr)
	       Type_is_set(TR -> _)
	    || -- the right has set type
	       Type_is_set(TR -> TExpr)
	       -- the only choices are:
	       (| -- belongs to (isin)
	          where(SALOp -> sal_function_op(isin))
	       || -- doesn't belong to (not-isin)
	          where(SALOp -> sal_function_op(notisin))
	       |)
	    || -- special case: (used in unary operators like rng)
	       eq(TR, none)
	       Type_is_set(TL -> TExpr)
	    |)
	    SAL_Check_Defined_Set(Pos, TExpr -> OptTid)
	    SAL_Gen_Type_Expr(Pos, TExpr -> SALTExpr, _)
	    (|
	        where(OptTid -> tid(SetTid))
		ne(TExpr, any)
		-- Generating the proper operation:
		where(sal_set_op(SALOp, SALTExpr, SetTid) -> SAL_Id_or_op)
	    ||
		-- Generating the new type:
		Gen_Set_Type(Pos, TExpr -> SetTid)
		-- Generating the proper operation:
		where(sal_set_op(SALOp, SALTExpr, SetTid) -> SAL_Id_or_op)
	    |)
	    -- cc
	    SetTid'Lifted_Tid -> tid(Tid)
	    where(sal_cc_op(SALOp, Tid) -> CC_IdOp)
	 ||
	    (| -- both are maps (most common case)
	       Type_is_map(TL -> Dom, Rng)
	       Type_is_map(TR -> _, _)
	    ||
	       -- The first is a map:
	       Type_is_map(TL -> Dom, Rng)
	       -- The second one is a set (cases for restrict-by and to)
	       Type_is_set(TR -> _)
	    ||
	       -- The right is a map
	       Type_is_map(TR -> Dom, Rng)
	       -- the only choices are:
	       (| -- belongs to (isin)
	          where(SALOp -> sal_function_op(isin))
	       || -- doesn't belong to (not-isin)
	          where(SALOp -> sal_function_op(notisin))
	       |)
	    ||-- special case: (used in unary operators like rng)
	       eq(TR, none)
	       Type_is_map(TL -> Dom,Rng)
	    |)
	    SAL_Check_Defined_Map(Pos, Dom,Rng -> OptTid)
	    -- Generating the type:
	    SAL_Gen_Type_Expr(Pos, Dom -> SALDom, _)
	    SAL_Gen_Type_Expr(Pos, Rng -> SALRng, _)
	    (|
	        where(OptTid -> tid(MapTid))
		-- Generating the proper operation:
		where(sal_map_op(SALOp, SALDom, SALRng, MapTid) -> SAL_Id_or_op)
	    ||
	       -- There is no map of this type, generate a new one:
	       Gen_Map_Type(Pos, Dom, Pos, Rng -> MapTid)
	       where(sal_map_op(SALOp, SALDom, SALRng, MapTid) -> SAL_Id_or_op)
	    |)
	    -- cc
	    MapTid'Lifted_Tid -> tid(Tid)
            where(sal_cc_op(SALOp, Tid) ->  CC_IdOp)
	 || -- The type is a list!
	    Type_is_list(TL -> ElemType)
	    Puterror(Pos)
	    Putmsg("List operations not supported\n")
	    -- Generating the proper operation anyway (error recovery)
	    where(sal_op_symb(SALOp) -> SAL_Id_or_op)
	    where(SAL_Id_or_op -> CC_IdOp) 
	 ||
	    -- Normal case (it is not an operation over collections...)
	    -- This means that we are handling operations over some of the built-in types
	    -- but the system is using type references (that didn't make the SAL_MATCH_TYPE routine above to match)
	    where(sal_op_symb(SALOp) -> SAL_Id_or_op)
	    -- cc
	    SAL_Gen_Type_Expr(Pos, TL -> _,LTLE)
	    where(LTLE -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,LTid)), _)))
	    where(sal_cc_op(SALOp, LTid) -> CC_IdOp) 
	 |)

  'rule' Gen_SAL_Id_Op(P, Id, array(_, T1B), T2 -> SAL_OP1, SAL_OP2)
         Gen_SAL_Id_Op(P, Id, T1B, T2 -> SAL_OP1, SAL_OP2)

  'rule' Gen_SAL_Id_Op(P, Id, T1, array(_, T2B) -> SAL_OP1, SAL_OP2)
         Gen_SAL_Id_Op(P, Id, T1, T2B -> SAL_OP1, SAL_OP2)




--------------------------------------------------

'action' Gen_SAL_Op(POS, OP -> SAL_OP)

  'rule' Gen_SAL_Op(Pos, eq -> SALOp):
	 where(sal_infix_op(eq) -> SALOp)

  'rule' Gen_SAL_Op(Pos, neq -> SALOp):
	 where(sal_infix_op(neq) -> SALOp)

  'rule' Gen_SAL_Op(Pos, gt -> SALOp):
	 where(sal_infix_op(gt) -> SALOp)
  'rule' Gen_SAL_Op(Pos, lt -> SALOp):
	 where(sal_infix_op(lt) -> SALOp)
  'rule' Gen_SAL_Op(Pos, ge -> SALOp):
	 where(sal_infix_op(ge) -> SALOp)
  'rule' Gen_SAL_Op(Pos, le -> SALOp):
	 where(sal_infix_op(le) -> SALOp)

  'rule' Gen_SAL_Op(Pos, supset -> SALOp):
	 where(sal_function_op(supset) -> SALOp)

  'rule' Gen_SAL_Op(Pos, subset -> SALOp):
	 where(sal_function_op(subset) -> SALOp)

  'rule' Gen_SAL_Op(Pos, supseteq -> SALOp):
	 where(sal_function_op(supseteq) -> SALOp)

  'rule' Gen_SAL_Op(Pos, subseteq -> SALOp):
	 where(sal_function_op(subseteq) -> SALOp)

  'rule' Gen_SAL_Op(Pos, isin -> SALOp):
	 where(sal_function_op(isin) -> SALOp)

  'rule' Gen_SAL_Op(Pos, notisin -> SALOp):
	 where(sal_function_op(notisin) -> SALOp)

  'rule' Gen_SAL_Op(Pos, rem -> SALOp):
	 where(sal_function_op(rem) -> SALOp)
				 
  'rule' Gen_SAL_Op(Pos, caret -> SALOp):
	 where(SAL_OP'not_supported -> SALOp)
	 Puterror(Pos)
	 Putmsg("^ operator not supported for model checking\n")

  'rule' Gen_SAL_Op(Pos, union -> SALOp):
	 where(sal_function_op(union) -> SALOp)

  'rule' Gen_SAL_Op(Pos, override -> SALOp):
	 where(sal_function_op(override) -> SALOp)

  'rule' Gen_SAL_Op(Pos, mult -> SALOp):
	 where(sal_infix_op(mult) -> SALOp)

  'rule' Gen_SAL_Op(Pos, div -> SALOp):
	 where(sal_infix_op(div) -> SALOp)

  'rule' Gen_SAL_Op(Pos, hash -> SALOp):
	 where(sal_function_op(hash) -> SALOp)

  'rule' Gen_SAL_Op(Pos, inter -> SALOp):
	 where(sal_function_op(inter) -> SALOp)

  'rule' Gen_SAL_Op(Pos, exp -> SALOp):
	 where(sal_function_op(exp) -> SALOp)

  'rule' Gen_SAL_Op(Pos, abs -> SALOp):
	 where(sal_function_op(abs) -> SALOp)

  'rule' Gen_SAL_Op(Pos, int -> SALOp):
	 where(sal_identity -> SALOp)

  'rule' Gen_SAL_Op(Pos, real -> SALOp):
	 where(sal_identity -> SALOp)

  'rule' Gen_SAL_Op(Pos, card -> SALOp):
	 where(SAL_OP'not_supported -> SALOp)
	 Puterror(Pos)
	 Putmsg("card operator not supported for model checking\n")

  'rule' Gen_SAL_Op(Pos, len -> SALOp):
	 where(SAL_OP'not_supported -> SALOp)
	 Puterror(Pos)
	 Putmsg("len operator not supported for model checking\n")

  'rule' Gen_SAL_Op(Pos, inds -> SALOp):
	 where(SAL_OP'not_supported -> SALOp)
	 Puterror(Pos)
	 Putmsg("inds operator not supported for model checking\n")

  'rule' Gen_SAL_Op(Pos, elems -> SALOp):
	 where(SAL_OP'not_supported -> SALOp)
	 Puterror(Pos)
	 Putmsg("elems operator not supported for model checking\n")

  'rule' Gen_SAL_Op(Pos, hd -> SALOp):
	 where(SAL_OP'not_supported -> SALOp)
	 Puterror(Pos)
	 Putmsg("hd operator not supported for model checking\n")

  'rule' Gen_SAL_Op(Pos, tl -> SALOp):
	 where(SAL_OP'not_supported -> SALOp)
	 Puterror(Pos)
	 Putmsg("tl operator not supported for model checking\n")

  'rule' Gen_SAL_Op(Pos, dom -> SALOp):
	 where(sal_function_op(dom) -> SALOp)
  'rule' Gen_SAL_Op(Pos, rng -> SALOp):
	 where(sal_function_op(rng) -> SALOp)

  -- LTL operators:
--  'rule' Gen_SAL_Op(Pos, g -> sal_prefix_op(g))
--  'rule' Gen_SAL_Op(Pos, f -> sal_prefix_op(f))
--  'rule' Gen_SAL_Op(Pos, x -> sal_prefix_op(x))

  
-- not supported
  'rule' Gen_SAL_Op(Pos, wait -> SALOp):	-- only used in TRSL
	 where(SAL_OP'not_supported -> SALOp)
	 Puterror(Pos)
	 Putmsg("'wait' operator not supported for model checking\n")

  'rule' Gen_SAL_Op(Pos, plus -> SALOp):
	 where(sal_infix_op(plus) -> SALOp)

  'rule' Gen_SAL_Op(Pos, minus -> SALOp):
	 where(sal_infix_op(minus) -> SALOp)

'action' SAL_Disambiguate_op(SAL_OP, TYPE_EXPR, TYPE_EXPR -> SAL_OP)

  'rule' SAL_Disambiguate_op(sal_function_op(rem), L, R -> sal_function_op(difference)):
	 Type_is_set(L -> _)
	 Type_is_set(R -> _)
	   
  'rule' SAL_Disambiguate_op(sal_function_op(rem), L, R -> sal_function_op(restriction_by)):
	 Type_is_map(L -> _, _)
	 Type_is_set(R -> _)

  'rule' SAL_Disambiguate_op(sal_infix_op(div), _, R -> sal_infix_op(int_div)):
	 Match(R, up, int)

  'rule' SAL_Disambiguate_op(sal_infix_op(div), L, R -> sal_function_op(restriction_to)):
	 Type_is_map(L -> _, _)
	 Type_is_set(R -> _)

  'rule' SAL_Disambiguate_op(Op, _, _ -> Op):


--------------------------------------------------
'action' Gen_SAL_Logic_Conn(CONNECTIVE -> SAL_LOGIC_CONNECTIVE, SAL_ID_OP)

  'rule' Gen_SAL_Logic_Conn(implies -> SALConn, CC_Conn):
	 where(SAL_LOGIC_CONNECTIVE'implies -> SALConn)
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 where(sal_cc_op(sal_infix_op(implies), LBTid) -> CC_Conn)

  'rule' Gen_SAL_Logic_Conn(or -> SALConn, CC_Conn):
	 where(SAL_LOGIC_CONNECTIVE'or -> SALConn)
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 where(sal_cc_op(sal_infix_op(or), LBTid) -> CC_Conn)

  'rule' Gen_SAL_Logic_Conn(and -> SALConn, CC_Conn):
	 where(SAL_LOGIC_CONNECTIVE'and -> SALConn)
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 where(sal_cc_op(sal_infix_op(and), LBTid) -> CC_Conn)

  'rule' Gen_SAL_Logic_Conn(not -> SALConn, CC_Conn):
	 where(SAL_LOGIC_CONNECTIVE'not -> SALConn)
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 where(sal_cc_op(sal_prefix_op(not), LBTid) -> CC_Conn)

--------------------------------------------------
'action' Gen_SAL_Quantifier(QUANTIFIER -> SAL_BINDING_OP)

  'rule' Gen_SAL_Quantifier(all -> SALQuantifier):
	 where(SAL_BINDING_OP'forall -> SALQuantifier)

  'rule' Gen_SAL_Quantifier(exists -> SALQuantifier):
	 where(SAL_BINDING_OP'exists -> SALQuantifier)

  'rule' Gen_SAL_Quantifier(exists1 -> SALQuantifier):
	 where(SAL_BINDING_OP'exists1 -> SALQuantifier)


-------------------------------------------------------------------------------
-- SECOND PASS
-------------------------------------------------------------------------------
'action' SAL_Refine_CC_ast(SAL_CONTEXTS, SAL_CONTEXTS ->
					SAL_CONTEXTS)

         -- If there are errors, do not proceed any further modifying the AST!
  'rule' SAL_Refine_CC_ast(Unproccesed, Processed -> Unproccesed):
	 HasErrors()
	 
	 -- No errors, keep on translating (AST refinement)
  'rule' SAL_Refine_CC_ast(Unproccesed, Processed -> Result):
	 -- Move type declarations and collect new contexts:
	 SAL_Sort_Type_Decls(Unproccesed, Processed -> Contexts, CollectedTypes)
--Putmsg("CC Contexts:\n")
--SAL_Print_Contexts(Contexts)
--Putmsg("CC Before SAL_Process_Type_Decls:\n")
--SAL_Print_Constants(CollectedTypes)
	 -- Generating the lifted type declarations:
	 SAL_Gen_Lifted_Decls(-> LiftedDecls)
--Putmsg("Lifted declarations:\n")
--SAL_Print_Constants(LiftedDecls)
	 -- Adding the Is_<type> functions...
	 -- They are required to collect the values that were formerly (in the non-cc version) included
	 -- in the subtyping information
	 Collected_Is_Type_Functions -> Is_Type_Funs
	 SAL_Concatenate_Context_Constants(Is_Type_Funs, CollectedTypes -> CollectedTypes1)
	 SAL_Concatenate_Context_Constants(CollectedTypes1, LiftedDecls -> TypeDecls)
	 -- All the information for the fixed point is (might be) already calculated
	 -- for the non-cc version and some types are shared between them. To ensure proper
	 -- context qualification and type closure, all information about the FP is reseted:
	 SAL_Reset_Fixed_Point_Info
--Putmsg("Before SAL_Process_Type_Decls:\n")
--SAL_Print_Constants(TypeDecls)
--Putmsg("Contexts:\n")
--SAL_Print_Contexts(Contexts)
	 SAL_Process_Type_Decls(TypeDecls, TypeDecls, Contexts -> Result1, ExtendedTypes)
--Putmsg("After SAL_Process_Type_Decls:\n")
--SAL_Print_Constants(ExtendedTypes)
--Putmsg("Result1:\n")
--SAL_Print_Contexts(Result1)
	 -- Access the collected list (default types):
	 Generated_CC_Contexts -> Collected
	 -- Incorporate the collected contexts:
	 SAL_Insert_Contexts(Result1, Collected -> Result2)
	 -- not used cwg	 
	 -- SAL_Types_Extra_CC_Defs -> Collections
	 -- SAL_Concatenate_Context_Constants(ExtendedTypes,Collections -> Types)

	 -- Prefix with RSL_is_Int and RSL_is_Nat
	 SAL_Add_is_Type_functions(ExtendedTypes -> Types)

	 -- Adding the Constructors and Reconstructors:
	 Collected_Lifted_Constructors -> Constructors
	 Collected_Lifted_Destructors -> Destructors

	 Collected_Reconstructors -> Recons
--Putmsg("Reconstructors:\n")
--SAL_Print_Constants(Recons)
	 -- Concatenating (the order is important... constructors check arguments (so Is_type_functions first),
         -- then, the constructors should appear second because they are used in the reconstructors)
	 -- cwg this analysis is too weak.  Is_type functions may use
	 -- destructors from other types.  The arrangement should be
	 -- on a type-by-type basis
	 SAL_Concatenate_Context_Constants(Constructors, Destructors
	 -> C1)
	 SAL_Concatenate_Context_Constants(C1, Recons  -> C2)
	 SAL_Concatenate_Context_Constants(Types, C2 -> Declarations)
	 -- Removing duplicates:
--Putmsg("Declarations:\n")
--SAL_Print_Constants(Declarations)
	 SAL_Remove_Duplicates_from_Fixed_Point(Declarations -> FilteredTypes)
--Putmsg("Filtered Types:\n")
--SAL_Print_Constants(FilteredTypes)
	 -- remove the types that are defined in SAL_TYPES
	 SAL_Remove_SAL_TYPES(FilteredTypes -> FilteredTypes1)
--Putmsg("After removing SAL_TYPES:\n")
--SAL_Print_Constants(FilteredTypes1)
	 -- Generating the SAL_TYPES_cc context:
	 SAL_CC_TYPES_Cid -> TYPES_Cid
	 SAL_Generate_Context(TYPES_Cid, FilteredTypes1 -> TypesContext)
	 SAL_Insert_Context(TypesContext, Result2 -> Contexts1)
	 -- remove reconsructors from current context
	 SAL_Current_CC_Cid -> CC_Cid
	 SAL_Remove_Decls_From_Contexts(Recons, CC_Cid, Contexts1 -> Contexts2)
--Putmsg("Contexts2:\n")
--SAL_Print_Contexts(Contexts2)
	 -- The SAL_GLOBAL context will be shared by both versions... no generation here...

	 -- Adding the operation contexts:
	 Get_CC_Operation_Contexts(-> OperationCs)

	 SAL_Insert_Contexts(OperationCs, Contexts2 -> SortedContexts)

	 -- Generating a separate context with Int_cc, Bool_cc and Not_a_value_type
	 -- These three must be separated because they are needed by the operations
	 -- RSL_is_Int and RSL_is_Nat that are defined in SAL_TYPES_cc (they may introduce
	 -- circular dependencies otherwise).
	 SAL_Generate_CC_BuiltIn_Context(-> CC_BuiltInContext)
	 SAL_Insert_Context(CC_BuiltInContext, SortedContexts -> Result)
--Putmsg("CC Final Result:\n")
--SAL_Print_Contexts(Result)

'action' SAL_Refine_Simple_CC_ast(SAL_CONTEXTS, SAL_CONTEXTS ->
					SAL_CONTEXTS)
 
  'rule' SAL_Refine_Simple_CC_ast(Unproccesed, Processed -> Result):
	 -- Renaming the contexts and uptating Cids:
	 SAL_Rename_Contexts(Unproccesed -> Unproccesed1)
	 -- Move type declarations and collect new contexts:
	 SAL_Sort_Type_Decls(Unproccesed1, Processed -> Contexts, CollectedTypes)
	 -- Generating the lifted type declarations:
	 SAL_Gen_Lifted_Decls(-> LiftedDecls)
	 -- Adding the Is_<type> functions...
	 -- They are required to collect the values that were formerly (in the non-cc version) included
	 -- in the subtyping information
	 Collected_Is_Type_Functions -> Is_Type_Funs
	 SAL_Concatenate_Context_Constants(Is_Type_Funs, CollectedTypes -> CollectedTypes1)
	 SAL_Concatenate_Context_Constants(CollectedTypes1, LiftedDecls -> TypeDecls)
	 -- All the information for the fixed point is (might be) already calculated
	 -- for the non-cc version and some types are shared between them. To ensure proper
	 -- context qualification and type closure, all information about the FP is reseted:
	 SAL_Reset_Fixed_Point_Info
	 SAL_Process_Type_Decls(TypeDecls, TypeDecls, Contexts -> Result1, ExtendedTypes)
	 -- Access the collected list (default types):
	 Generated_CC_Contexts -> Collected
	 -- Incorporate the collected contexts:
	 SAL_Insert_Contexts(Result1, Collected -> Result2)	 
	 -- not used cwg	 
	 -- SAL_Types_Extra_CC_Defs -> Collections
	 -- SAL_Concatenate_Context_Constants(ExtendedTypes,Collections -> Types)

	 -- Prefix with RSL_is_Int and RSL_is_Nat
	 SAL_Add_is_Type_functions(ExtendedTypes -> Types)

	 -- Adding the Constructors and Reconstructors:
	 Collected_Lifted_Constructors -> Constructors
	 Collected_Lifted_Destructors -> Destructors
	 Collected_Reconstructors -> Recons
	 -- Concatenating (the order is important... constructors check arguments (so Is_type_functions first),
         -- then, the constructors should appear second because they are used in the reconstructors)
	 
	 SAL_Concatenate_Context_Constants(Constructors, Destructors -> C1)
	 SAL_Concatenate_Context_Constants(C1, Recons  -> C2)
	 SAL_Concatenate_Context_Constants(Types, C2 -> Declarations)
	 -- Removing duplicates:
	 SAL_Remove_Duplicates_from_Fixed_Point(Declarations -> FilteredTypes)
	 -- remove the types that are defined in SAL_TYPES
	 SAL_Remove_SAL_TYPES(FilteredTypes -> FilteredTypes1)
	 -- Generating the SAL_TYPES_cc context:
	 SAL_CC_TYPES_Cid -> TYPES_Cid
	 TYPES_Cid'Ident -> TypesId
	 SAL_Update_Names(TypesId, TYPES_Cid -> _)
	 SAL_Generate_Context(TYPES_Cid, FilteredTypes1 -> TypesContext)
	 SAL_Insert_Context(TypesContext, Result2 -> Contexts1)
	 -- remove reconstructors from current context
	 SAL_Current_CC_Cid -> CC_Cid
	 SAL_Remove_Decls_From_Contexts(Recons, CC_Cid, Contexts1 -> Contexts2)
	 -- The SAL_GLOBAL context will be shared by both versions... no generation here...

	 -- Adding the operation contexts:
	 Get_CC_Operation_Contexts(-> OperationCs)
	 SAL_Rename_Contexts(OperationCs -> OperationCs1)
	 SAL_Insert_Contexts(OperationCs1, Contexts2 -> SortedContexts)

	 -- Generating a separate context with Int_cc, Bool_cc and Not_a_value_type
	 -- These three must be separated because they are needed by the operations
	 -- RSL_is_Int and RSL_is_Nat that are defined in SAL_TYPES_cc (they may introduce
	 -- circular dependencies otherwise).
	 SAL_Generate_Simple_CC_BuiltIn_Context(-> CC_BuiltInContext)
	 SAL_Insert_Context(CC_BuiltInContext, SortedContexts -> Result)

'action' SAL_Rename_Contexts(SAL_CONTEXTS -> SAL_CONTEXTS)

  'rule' SAL_Rename_Contexts(list(Context, Rest) -> list(NewContext, NewRest))
	 (|
	     where(Context -> context(Id, cid(Cid), Elems))
	     SAL_Update_Names(Id, Cid -> NewId)
	     where(context(NewId, cid(Cid), Elems) -> NewContext)
	 ||
	     where(Context -> macro_context(Id, cid(Cid), MacroElems))
	     SAL_Update_Names(Id, Cid -> NewId)
	     where(macro_context(NewId, cid(Cid), MacroElems) -> NewContext)
	 |)
	 SAL_Rename_Contexts(Rest -> NewRest)

  'rule' SAL_Rename_Contexts(nil -> nil)


'action' SAL_Refine_ast(SAL_CONTEXTS, SAL_CONTEXTS -> SAL_CONTEXTS)

         -- If there are errors, do not proceed any further modifying the AST!
  'rule' SAL_Refine_ast(Unproccesed, Processed -> Unproccesed):
	 HasErrors()
	 
	 -- No errors, keep on translating (AST refinement)
  'rule' SAL_Refine_ast(Unproccesed, Processed -> Result):
	 -- Putmsg("Incorporating the SAL_TYPES context...\n")
	 -- Move type declarations and collect new contexts:
	 SAL_Sort_Type_Decls(Unproccesed, Processed -> Contexts, CollectedTypes)

--SAL_Print_Constants(CollectedTypes)
--Putmsg("Contexts:\n")
--SAL_Print_Contexts(Contexts)
	 -- Process the collected type decls:
	 SAL_Process_Type_Decls(CollectedTypes, CollectedTypes, Contexts -> Result1, ExtendedTypes)
--Putmsg("After SAL_Process_Type_Decls:\n")
--SAL_Print_Constants(ExtendedTypes)
--Putmsg("Result1:\n")
--SAL_Print_Contexts(Result1)
	 -- Access the collected list (default types):
	 Generated_Contexts -> Collected
	 -- Incorporate the collected contexts:
	 SAL_Insert_Contexts(Result1, Collected -> Result2)
	 SAL_Types_Extra_Defs -> Collections
	 SAL_Concatenate_Context_Constants(ExtendedTypes,Collections -> Types)

	 SAL_Remove_Duplicates_from_Fixed_Point(Types -> FilteredTypes)
	 SAL_TYPES_Cid -> TYPES_Cid
	 SAL_Generate_Context(TYPES_Cid, FilteredTypes -> TypesContext)
--Putmsg("TypesContext:\n")
--SAL_Print_Context(TypesContext)
	 -- CWG 13/4/08
	 -- save types and values defined in SAL_TYPES
	 -- so we do not redefine them in SAL_TYPES_cc
	 where(TypesContext -> context(_, _, Context_Constants))
	 SAL_TYPES_Constants <- Context_Constants
--Putmsg("Saved SAL_TYPES definitions:\n")
--SAL_Print_Constants(Context_Constants)

	 SAL_Insert_Context(TypesContext, Result2 -> Result0)
--Putmsg("Result0:\n")
--SAL_Print_Contexts(Result0)
	 -- Generate the 'SAL_GLOBAL' context (contains the boundaries
	 -- for all types):
	 -- Putmsg("Incorporating the SAL_GLOBAL context...\n")
	 SAL_Gen_GLOBAL_Context(-> GlobalContext)
	 -- Incorporate it to the AST:
	 SAL_Insert_Context(GlobalContext, Result0 -> Contexts1)

	 -- Adding the operation contexts:
	 Get_Operation_Contexts(-> OperationCs)
	 SAL_Insert_Contexts(OperationCs, Contexts1 -> Result)
--Putmsg("Final result:\n")
--SAL_Print_Contexts(Result)
	
 
'action' SAL_Sort_Type_Decls(SAL_CONTEXTS, SAL_CONTEXTS ->
				SAL_CONTEXTS,SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Sort_Type_Decls(list(Context, Tail), Contexts ->
					  ContextsOut, CollectedConstants):
	 where(Context -> context(Ident, OptCid, Elems))
	 where(OptCid -> cid(Cid))
	 -- Extracts and collects the type declarations in the contexts:
	 SAL_Process_Context_Elements(Cid, Elems -> Collected1, RemainingElements1)
	 -- Rebuilds the original context without type declarations
	 where(context(Ident,OptCid,RemainingElements1) -> ModifiedContext)
	 where(SAL_CONTEXTS'list(ModifiedContext, Contexts) -> Processed)
	 SAL_Sort_Type_Decls(Tail, Processed -> ContextsOut, Constants)
	 SAL_Concatenate_Context_Constants(Collected1,Constants -> CollectedConstants)
	 

  'rule' SAL_Sort_Type_Decls(nil, Contexts -> Contexts, nil):

'action' SAL_Process_Context_Elements(SAL_context_id,SAL_CONTEXT_CONSTANTS ->
						SAL_CONTEXT_CONSTANTS,
						SAL_CONTEXT_CONSTANTS)


 'rule' SAL_Process_Context_Elements(Cid,list(Head, Tail) ->
						     Collected, Remainings):
	 where(Head -> sal_type_decl(Ident, Tid,TypeExpr))
	 -- Process the rest
	 SAL_Process_Context_Elements(Cid,Tail  -> Collected1, Remainings1)
	 (|	    
	    where(TypeExpr -> user_defined(_))
	    -- Remove the type from the actual context
	    Remove_Decl_from_Static(Cid,Head)
	    where(SAL_CONTEXT_CONSTANTS'list(Head, Collected1) -> Collected)
	    -- As the declaration is being removed (temporarily) from
	    -- the AST, collect it inside the Tid:
	    Tid'Declaration <- Head
	    where(Remainings1 -> Remainings)
	 ||
	   (|
	      where(TypeExpr -> rsl_built_in(_))
	      print("Internal error! There can't be a type definition overloading the built-in types!")
	   ||
              where(TypeExpr -> type_refs(_))
	      print("Internal error! There can't be a type definition marked as a type reference")
	   ||
	      where(TypeExpr -> unsupported_type)
	      -- just ignore it! (error-recovery value!)
	   ||
	      where(TypeExpr -> nil)
	      -- just ignore it! (error-recovery value!)
	   |)
	   where(Collected1 -> Collected)
	   where(Remainings1 -> Remainings)
	 |)


  
  -- The current context element IS NOT a type declaration:
  -- (The element MUST be PRESERVED in the current context)
  'rule' SAL_Process_Context_Elements(Cid,list(Head, Tail) -> Collected, RemainingsOut):
	 -- Process the rest:
	 SAL_Process_Context_Elements(Cid,Tail -> Collected, Rems1)
	 where(SAL_CONTEXT_CONSTANTS'list(Head, Rems1) -> RemainingsOut)
	 
  'rule' SAL_Process_Context_Elements(Cid,nil -> nil, nil):	

------------------------------------------------------------------------
-- Collect_Type_Decl
------------------------------------------------------------------------
-- Collects temporary the type declarations in a global variable
------------------------------------------------------------------------

'action' Collect_Type_Decl(SAL_CONTEXT_CONSTANT,
	   SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' Collect_Type_Decl(Decl, list(H,T) -> list(H, Result))
	 Collect_Type_Decl(Decl, T -> Result)

  'rule' Collect_Type_Decl(Decl, nil -> list(Decl, nil))


------------------------------------------------------------------------
-- SAL_Process_Type_Decls
------------------------------------------------------------------------
-- This predicate will:
-- 1) procces the list of type declarations (collected throughout the 
--    diferent contexts), 
-- 2) calculate the type closure (fixed point) of each of the elements 
--    in the list,
------------------------------------------------------------------------

'action' SAL_Process_Type_Decls(
		SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS, SAL_CONTEXTS
				-> SAL_CONTEXTS, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Process_Type_Decls(list(H,T), AllDecls, CurrentContexts ->
					  UpdatedContexts, TypeCollection):
	 -- Calculate the fixed point for the type:
--Putmsg("Fixed points:\n")
--Print_Fixed_Point(list(H,T))
--Putmsg("Context constant:\n")
--SAL_Print_Constant(H)
--Putmsg("Current contexts:\n")
--SAL_Print_Contexts(CurrentContexts)
	 SAL_compute_fixed_point(H, CurrentContexts,nil -> FixedPoint, CS0)

         -- Fixed point items already in AllDecls should be removed
	 -- (this also removes H: we replace later)
	 SAL_Remove_Duplicate_Context_Constants(FixedPoint, AllDecls -> FixedPoint1)
--Putmsg("Added fixed points:\n")
--Print_Fixed_Point(FixedPoint)
--Putmsg("New contexts:\n")
--SAL_Print_Contexts(CS0)

	 -- we need to append H to its fixed point, for dependency
         -- ordering
	 SAL_Append_Decl(H, FixedPoint1 -> FixedPoint2)   

	 -- Generate the new context with the information and
	 -- update the Cids and Vids included there:
	 SAL_Process_Type_Decls(T, AllDecls, CS0 -> UpdatedContexts, Collected1)
	 SAL_Concatenate_Context_Constants(FixedPoint, Collected1 -> TypeCollection)


  'rule' SAL_Process_Type_Decls(nil, _, Contexts -> Contexts, nil)


------------------------------------------------------------------------
-- SAL_Generate_Context
------------------------------------------------------------------------
-- This function will generate the AST context declaration provided
-- with the type declaration that initiated the context generation and
-- its type-closure (types and value definitions involved in the type
-- declaration).
-- The procedure will also update the proper Cid field in all value-
-- and type-ids involved in the closure.
------------------------------------------------------------------------

'action' SAL_Generate_Context(SAL_context_id, 
			 SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT)

  'rule' SAL_Generate_Context(Cid, CElem -> New_Context)

	 Cid'Ident -> Ident
	 where(cid(Cid) -> OptCid)
	 -- Update the Cid's arg list:
	 Collect_Tids_in_Cid(CElem, Cid)
	 SAL_Split_Constants(CElem -> Static, NonStatic)
	 Extend_Static_in_Cid_Decls(Cid,Static)
	 Extend_State_in_Cid_Decls(Cid,NonStatic)
	 Update_Reference_Information(Cid, CElem)
	 where(context(Ident, OptCid, CElem) -> New_Context)

------------------------------------------------------------------------
-- check_Cid_in_Context_list
------------------------------------------------------------------------
-- This condition tries to find the Cid given as a param in the list 
-- of context.
------------------------------------------------------------------------

'condition' check_Cid_in_Context_list(SAL_CONTEXTS, SAL_context_id)

  'rule' check_Cid_in_Context_list(list(context(_,cid(Cid),_),Rest), Cid1):
	 (|
	     eq(Cid, Cid1)
	 ||
	     check_Cid_in_Context_list(Rest, Cid1)
	 |)



------------------------------------------------------------------------
-- SAL_insert_type_decls
------------------------------------------------------------------------
-- Auxiliary procedure that produces an in-order insertion in the list
------------------------------------------------------------------------
'action' SAL_insert_type_decls(SAL_CONTEXT_CONSTANTS, SAL_CONTEXT -> SAL_CONTEXT)

  'rule' SAL_insert_type_decls(Constants, context(Ident, Cid, Elements) -> Result):
	 SAL_insert_type_decls1(Constants, Elements ->  Result1)
	 where(context(Ident, Cid, Result1) -> Result)

'action' SAL_insert_type_decls1(SAL_CONTEXT_CONSTANTS,
			SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_insert_type_decls1(List, list(Head, Tail) -> list(Head,  Result1))
	 SAL_insert_type_decls1(List, Tail -> Result1)

  'rule' SAL_insert_type_decls1(List, nil -> List)
------------------------------------------------------------------------
-- SAL_insert_type_decl
------------------------------------------------------------------------
-- Auxiliary procedure that produces an in-order insertion in the list
-- (that is not the typical, simple, insertion!)
------------------------------------------------------------------------
'action' SAL_insert_type_decl(SAL_CONTEXT_CONSTANT, SAL_CONTEXT -> SAL_CONTEXT)

  'rule' SAL_insert_type_decl(Elem, context(Ident, Cid, Elements) -> Result):
	 SAL_insert_elem(Elem, Elements -> Result1)
	 where(context(Ident, Cid, Result1) -> Result)

'action' SAL_insert_elem(SAL_CONTEXT_CONSTANT, SAL_CONTEXT_CONSTANTS
					       -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_insert_elem(Elem, list(Head, Tail) -> Result):
         SAL_insert_elem(Elem, Tail -> Result1)
	 where(SAL_CONTEXT_CONSTANTS'list(Head, Result1) -> Result)

  'rule' SAL_insert_elem(Elem, nil -> SAL_CONTEXT_CONSTANTS'list(Elem,nil))

-------------------------------------------------------------------------
-- SAL_Insert_Contexts
-------------------------------------------------------------------------
-- Auxiliary procedure... concatenates two Context lists...
-------------------------------------------------------------------------

'action' SAL_Insert_Contexts(SAL_CONTEXTS, SAL_CONTEXTS -> SAL_CONTEXTS)

  'rule' SAL_Insert_Contexts(List1, list(H,T) -> Result):
	 SAL_Insert_Contexts(List1, T -> Result1)
	 where(SAL_CONTEXTS'list(H, Result1) -> Result)

  'rule' SAL_Insert_Contexts(List1, nil -> List1)


'action' SAL_Insert_Context(SAL_CONTEXT, SAL_CONTEXTS -> SAL_CONTEXTS)

  'rule' SAL_Insert_Context(Elem, List -> SAL_CONTEXTS'list(Elem, List)):


-------------------------------------------------------------------------
-- SAL_Gen_GLOBAL_Context
-------------------------------------------------------------------------
-- This procedure explores the global array-like structure that
-- contains the SAL_type_ids generated during translation and collects
-- the arguments required by them.
-- Then, an AST CONTEXT element is generated with this information for
-- it to be outputed as other context generated with the translation
-- mechanism. 
-------------------------------------------------------------------------

'action' SAL_Gen_GLOBAL_Context(-> SAL_CONTEXT)

  'rule' SAL_Gen_GLOBAL_Context(-> NewContext):
	 SAL_GLOBAL_Cid -> CidData
	 CidData'Ident -> Ident
	 where(cid(CidData) -> Cid)
	 Generated_Constants -> ConstDecls
	 SAL_Filter_Repeated_Decls(ConstDecls -> FilteredDecls)
	 SAL_Generate_Constant_Decl_List(FilteredDecls -> ContextConstants)
	 where(context(Ident, Cid, ContextConstants) -> NewContext)

'action' SAL_Filter_Repeated_Decls(SAL_CONSTANT_DECLS ->
						SAL_CONSTANT_DECLS)

  'rule' SAL_Filter_Repeated_Decls(list(Decl, T) -> Result)
	 SAL_Filter_Repeated_Decls(T -> Res1)
	 where(Decl -> sal_param_decl(Decls,Tid))
	 SAL_Filter_One_Decl(Decls, T -> Res2)
	 (| 
	     where(Res2 -> nil)
	     where(Res1 -> Result)
	 ||
	     where(SAL_CONSTANT_DECLS'list(sal_param_decl(Res2,Tid), Res1) -> Result)
	 |)

  'rule' SAL_Filter_Repeated_Decls(nil -> nil)

'action' SAL_Filter_One_Decl(SAL_CONSTANT_DECLS, SAL_CONSTANT_DECLS -> SAL_CONSTANT_DECLS)

  'rule' SAL_Filter_One_Decl(list(H,T),List ->  Result):
	 SAL_Filter_One_Decl(T, List -> Res1)
	 (|
	    Verify_repetition(H,List)
	    where(Res1 -> Result)
	 ||
	    where(SAL_CONSTANT_DECLS'list(H, Res1) -> Result)
	 |)

  'rule' SAL_Filter_One_Decl(nil,_ -> nil)

'condition' Verify_repetition(SAL_CONSTANT_DECL, SAL_CONSTANT_DECLS)

  'rule' Verify_repetition(Elem, list(sal_param_decl(Decls,Tid),Rest)):
	 (|
	    Verify_repetition(Elem, Decls)
	 ||
	    Verify_repetition(Elem,Rest)
	 |)

  'rule' Verify_repetition(Elem, list(sal_expl_const(_,Vid1,_,_), T))
	 where(Elem -> sal_expl_const(_,Vid,_,_))
	 Vid'IdOp -> IdOp
	 (|
	    eq(Vid,Vid1)
	 ||
	    Verify_repetition(Elem, T)
	 |)


'action' SAL_Generate_Constant_Decl_List(SAL_CONSTANT_DECLS ->
					SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Generate_Constant_Decl_List(list(Decl, T) -> Result):
	 SAL_Generate_Constant_Decl_List(T -> Rest)
	 where(Decl -> sal_param_decl(T1, Tid))
	 Tid'Ident -> Id
	 where(SAL_CONTEXT_CONSTANTS'list(sal_const_decl(Decl), Rest) -> Result)

  'rule' SAL_Generate_Constant_Decl_List(nil -> nil)
/*
	 -- Get the global data 'array ':
	 Global_Tid_Table -> Array
	 -- Proces it for getting the Args:
	 SAL_Remove_Duplicated_Tids(Array -> FilteredTidList)
	 -- Generate the constant declarations:
	 SAL_Generate_Constant_Decl_List(FilteredTidList -> ContextConstants)
	 where(context(Ident, Cid, ContextConstants) -> NewContext)
	 
'action' SAL_Generate_Constant_Decl_List(SAL_TYPE_IDS
					   -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Generate_Constant_Decl_List(list(H,T) -> Result):
	 SAL_Get_Constants_from_Tid(H -> Res)
	 SAL_Generate_Constant_Decl_List(T -> Result1)
	 SAL_Concatenate_Constants(Res, Result1 -> Res1)
	 SAL_Filter_Repeated_Constants(Res1 -> Result)

  'rule' SAL_Generate_Constant_Decl_List(nil -> nil)

'action' SAL_Get_Constants_from_Tid(SAL_type_id -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Get_Constants_from_Tid(Tid -> Result):
	 Tid'Ident -> Id
	 -- Collecting from Qualif Args:
	 Tid'Args -> Args
	 SAL_Collect_Constants_from_Args(Args -> R1)
	 -- Collecting from Macro Args:
	 Tid'MacroArgs -> MacroArgs
	 SAL_Collect_Constants_from_Args(MacroArgs -> R2)
	 -- Collecting from comprised:
	 Tid'Comprised -> ComprisedArgs
	 SAL_Collect_Constants_from_Args(ComprisedArgs -> R3)
	 -- Concatenate the lists:
	 SAL_Concatenate_Constants(R1,R2 -> R4)
	 SAL_Concatenate_Constants(R3, R4 -> Result)

'action' SAL_Collect_Constants_from_Args(SAL_CONTEXT_ARGS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Collect_Constants_from_Args(list(H,T) -> Result):
	 SAL_Collect_Constants_from_Args(T -> Result1)
	 SAL_GLOBAL_Cid -> Cid
	 (|
	    where(H -> num_arg(_, Decl))
	    -- Updating the context (as this constant declaration is
	    -- being moved to the SAL_GLOBAL context):
	    where(Decl -> sal_param_decl(Constants,_))
	    SAL_Update_Cid_in_Vids(Constants, Cid)
	    -- Generating the result:
	    where(SAL_CONTEXT_CONSTANTS'list(sal_const_decl(Decl), Result1) -> Result)
	 ||
	    where(H -> type_arg(_))
	    where(Result1 -> Result)
	 ||
	    where(H -> macro_arg(_, Decl))
	    -- Updating the context (as this constant declaration is
	    -- being moved to the SAL_GLOBAL context):
	    where(Decl -> sal_param_decl(Constants,_))
	    SAL_Update_Cid_in_Vids(Constants, Cid)
	    -- Generating the result:
	    where(SAL_CONTEXT_CONSTANTS'list(sal_const_decl(Decl), Result1) -> Result)
	 |)

  'rule' SAL_Collect_Constants_from_Args(nil -> nil)
*/
  
'action' SAL_Update_Cid_in_Vids(SAL_CONSTANT_DECLS, SAL_context_id)

  'rule' SAL_Update_Cid_in_Vids(list(H, T), Cid):
	 SAL_Update_Cid_in_Vids(T,Cid)
	 (|
	     where(H -> sal_expl_const(_, Vid,_,_))
	 ||
	     where(H -> sal_fun_const(_, Vid,_,_,_,_,_,_))
	 |)
	 Vid'Cid <- cid(Cid)

  'rule' SAL_Update_Cid_in_Vids(list(H, T), Cid):
	 SAL_Update_Cid_in_Vids(T,Cid)

  'rule' SAL_Update_Cid_in_Vids(nil, Cid):

'action' SAL_Concatenate_Constants(SAL_CONTEXT_CONSTANTS,
		                      SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Concatenate_Constants(list(H,T), List -> Result):
	 SAL_Concatenate_Constants(T, List -> Result1)
	 where(SAL_CONTEXT_CONSTANTS'list(H, Result1) -> Result)

  'rule' SAL_Concatenate_Constants(nil, List -> List)

'action' SAL_Convert_Id_Op(ID_OR_OP -> SAL_ID_OP)

  'rule' SAL_Convert_Id_Op(id_op(Id) -> Result):
	 where(SAL_ID_OP'id(Id) -> Result)

  'rule' SAL_Convert_Id_Op(op_op(Op) -> Result):
	 
	 (|
	     eq(Op,eq)
	     where(sal_infix_op(eq) -> Res)
	 ||
	     eq(Op,neq)
	     where(sal_infix_op(neq) -> Res)
	 ||
             eq(Op,gt)
	     where(sal_infix_op(gt) -> Res)
	 ||
	     eq(Op,lt)
	     where(sal_infix_op(lt) -> Res)
	 ||
	     eq(Op,ge)
	     where(sal_infix_op(ge) -> Res)
	 ||
	     eq(Op,le)
	     where(sal_infix_op(le) -> Res)
	 ||
	     eq(Op,mult)
	     where(sal_infix_op(mult) -> Res)
	 ||
	     eq(Op,div)
	     where(sal_infix_op(div) -> Res)
	 ||
	     eq(Op,plus)
	     where(sal_infix_op(plus) -> Res)
	 ||
	     eq(Op,minus)
	     where(sal_infix_op(minus) -> Res)
	 ||
	     eq(Op,supset)
	     where(sal_function_op(supset)-> Res)
	 ||
	     eq(Op,subset)
	     where(sal_function_op(subset)-> Res)
	 ||
	     eq(Op,supseteq)
	     where(sal_function_op(supseteq)-> Res)
	 ||
	     eq(Op,subseteq)
	     where(sal_function_op(subseteq)-> Res)
	 ||
	     eq(Op,isin)
	     where(sal_function_op(isin)-> Res)
	 ||
	     eq(Op,notisin)
	     where(sal_function_op(notisin)-> Res)
	 ||
	     eq(Op,rem)
	     where(sal_function_op(rem)-> Res)
	 ||
	     eq(Op,caret)
	     where(sal_function_op(caret)-> Res)
	 ||
	     eq(Op,union)
	     where(sal_function_op(union)-> Res)
	 ||
	     eq(Op,override)
	     where(sal_function_op(override)-> Res)
	 ||
	     eq(Op,hash)
	     where(sal_function_op(hash)-> Res)
	 ||
	     eq(Op,inter)
	     where(sal_function_op(inter)-> Res)
	 ||
	     eq(Op,exp)
	     where(sal_function_op(exp)-> Res)
	 ||
	     eq(Op,abs)
	     where(sal_function_op(abs)-> Res)
	 ||
	     eq(Op,card)
	     where(sal_function_op(card)-> Res)
	 ||
	     eq(Op,len)
	     where(sal_function_op(len)-> Res)
	 ||
	     eq(Op,inds)
	     where(sal_function_op(inds)-> Res)
	 ||
	     eq(Op,elems)
	     where(sal_function_op(elems)-> Res)
	 ||
	     eq(Op,hd)
	     where(sal_function_op(hd)-> Res)
	 ||
	     eq(Op,tl)
	     where(sal_function_op(tl)-> Res)
	 ||
	     eq(Op,dom)
	     where(sal_function_op(dom)-> Res)
	 ||
	     eq(Op,rng)
 	     where(sal_function_op(rng)-> Res)
	 |)
	 where(sal_op_symb(Res) -> Result)


  'rule' SAL_Convert_Id_Op(_ -> Result):
	 where(sal_op_symb(not_supported) -> Result)


--------------------------------------------------------------------

'action' SAL_Filter_Repeated_Constants(SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Filter_Repeated_Constants(list(H,T) -> Result):
	 SAL_Filter_Repeated_Constants(T -> Res1)
	 (|
	    where(H -> sal_const_decl(sal_expl_const(_,Vid,_,_)))
	 ||
	    where(H -> sal_const_decl(sal_fun_const(_,Vid,_,_,_,_,_,_)))
	 |)
	 (|
	    SAL_Check_Repeated_Vid(Vid, T)
	    where(Res1 -> Result)
	 ||
	    where(SAL_CONTEXT_CONSTANTS'list(H, Res1) -> Result)
	 |)


  'rule' SAL_Filter_Repeated_Constants(list(H,T) -> Result):
	 where(H -> sal_const_decl(sal_param_decl(List,Tid)))
	 SAL_Filter_Repeated_Constants2(List,T -> FilteredList)
	 (|
	    eq(FilteredList, nil)
	    SAL_Filter_Repeated_Constants(T -> Result)
	 ||
	    where(sal_const_decl(sal_param_decl(FilteredList,Tid)) -> H1)
	    SAL_Filter_Repeated_Constants(T -> Res1)
	    where(SAL_CONTEXT_CONSTANTS'list(H1, Res1) -> Result)
	 |)
	 
	 
  'rule' SAL_Filter_Repeated_Constants(list(H,T) -> Result):
	 -- This is not a constant declaration...
	 -- just ignore it and process the rest:
	 SAL_Filter_Repeated_Constants(T -> Result)

  'rule' SAL_Filter_Repeated_Constants(nil -> nil)

'condition' SAL_Check_Repeated_Vid(SAL_value_id, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Check_Repeated_Vid(CVid, list(H,T))
	 (|
	    (|
		where(H -> sal_const_decl(sal_expl_const(_,Vid,_,_)))
	    ||
		where(H -> sal_const_decl(sal_fun_const(_,Vid,_,_,_,_,_,_)))
	    |)
	    eq(CVid, Vid)
	 ||
	    SAL_Check_Repeated_Vid(CVid, T)
	 |) 

  'rule' SAL_Check_Repeated_Vid(CVid, list(H,T))
         where(H -> sal_const_decl(sal_param_decl(List,_)))
	 (|
	    SAL_Check_Repeated_Vid2(CVid, List)
	 ||
	    SAL_Check_Repeated_Vid(CVid, T)
	 |)


'condition' SAL_Check_Repeated_Vid2(SAL_value_id, SAL_CONSTANT_DECLS)

  'rule' SAL_Check_Repeated_Vid2(CVid, list(H,T)):
	 (|
	    (|
		where(H -> sal_expl_const(_,Vid,_,_))
	    ||
		where(H -> sal_fun_const(_,Vid,_,_,_,_,_,_))
	    |)
	    eq(CVid, Vid)
	 ||
	    SAL_Check_Repeated_Vid2(CVid, T)
	 |) 

----------------------------
'action' SAL_Filter_Repeated_Constants2(SAL_CONSTANT_DECLS,
	 		SAL_CONTEXT_CONSTANTS -> SAL_CONSTANT_DECLS)

  'rule' SAL_Filter_Repeated_Constants2(list(Decl,Rest), List -> Result):
	 SAL_Filter_Repeated_Constants2(Rest, List -> Res1)
	 (|
		where(Decl -> sal_expl_const(_,Vid,_,_))
	 ||
		where(Decl -> sal_fun_const(_,Vid,_,_,_,_,_,_))
	 |)
	 (|
	 	SAL_Check_Repeated_Vid(Vid, List)
		where(Res1 -> Result)
	 ||
		where(SAL_CONSTANT_DECLS'list(Decl, Res1) -> Result)
	 |)

  'rule' SAL_Filter_Repeated_Constants2(nil, _ -> nil)


-------------------------
'action' SAL_Gen_Init_Expr(SAL_TYPE_EXPR -> SAL_VALUE_EXPR)

  'rule' SAL_Gen_Init_Expr(rsl_built_in(boolean) -> sal_literal(bool_false))
  'rule' SAL_Gen_Init_Expr(rsl_built_in(integer(Tid)) -> Low)
	 Tid'Declaration -> Decl
	 where(Decl ->  sal_type_decl(IntId2, _, TExpr))
	 where(TExpr -> sal_basic(sal_rectricted_integer(Low, High)))


  'rule' SAL_Gen_Init_Expr(T -> nil)
	 Putmsg("Debugging predicate activated in SAL_Gen_Init_Expr\n")
	 print(T)
---- Must be extended here!

-----------------------------------------------------------------------
-- SAL_Split_type
-----------------------------------------------------------------------
-- This function splits the inherited type in an infix-occ and returns
-- the proper type for the left and right expressions.
-- For example:
-- If the type is Int -m-> Bool and the operation is restrict-by
-- then:
-- The left expression's type must be: Int -m-> Bool
-- and the right's one must be: Int-set
-----------------------------------------------------------------------
'action' SAL_Split_type(ID_OR_OP, TYPE_EXPR -> TYPE_EXPR, TYPE_EXPR)

  'rule' SAL_Split_type(IdOp, TExpr -> Left, Right)
	 (|
	    Type_is_set(TExpr -> SetType)
	    (|
	        (| eq(IdOp, op_op(isin)) || eq(IdOp, op_op(notisin)) |)
	        where(SetType -> Left)
		where(TExpr -> Right)
	    ||
		where(TExpr -> Left)
		where(TExpr -> Right)
	    |)
	 ||
	    Type_is_map(TExpr -> Dom,Rng)
	    (|
	        (| eq(IdOp, op_op(rem)) -- restriction-by
		|| eq(IdOp, op_op(div)) |) -- restriction-to
	        where(TExpr -> Left)
		where(fin_set(Dom) -> Right) -- the second arg is of set type
	    || 
	        -- in the rest of the operations, the types on the
		-- left and right hand side parts are of the same map type:
	        where(TExpr -> Left)
		where(TExpr -> Right)
	    |)
	 ||
	    where(TExpr -> Left)
	    where(TExpr -> Right)
	 |)

-------------------------------------------------------------------------
'action' Gen_RSLFormal_Parameters(TYPE_EXPR -> FORMAL_FUNCTION_PARAMETERS)

  'rule' Gen_RSLFormal_Parameters(product(ProdType) -> list(form_parm(P,BS),nil))
	 DefaultPos(->P)
	 Internal_Gen_RSLFormal_Parameters(ProdType -> BS)

  'rule' Gen_RSLFormal_Parameters(fun(T,_,_) -> Params)
	 Gen_RSLFormal_Parameters(T -> Params)

  'rule' Gen_RSLFormal_Parameters(T -> list(form_parm(P,list(BS,nil)),nil))
	 DefaultPos(->P)
	 Gen_RSLFormal_Parameter(T -> BS)

'action' Internal_Gen_RSLFormal_Parameters(PRODUCT_TYPE -> BINDINGS)
	 
  'rule' Internal_Gen_RSLFormal_Parameters(list(T, Rest) -> list(B,BS))
	 Gen_RSLFormal_Parameter(T -> B)
	 Internal_Gen_RSLFormal_Parameters(Rest -> BS)

  'rule' Internal_Gen_RSLFormal_Parameters(nil -> nil)

'action' Gen_RSLFormal_Parameter(TYPE_EXPR -> BINDING)

  'rule' Gen_RSLFormal_Parameter(T -> Binding)
	 DefaultPos(-> P)
	 SAL_Gen_Param_Ident(-> Ident)
	 where(BINDING'single(P, id_op(Ident)) -> Binding)

-------------------------------------------------------------------------
-- SAL_Gen_Lambda_Param_from_Parameters
-------------------------------------------------------------------------
-- This function will generate the lambda parameters from the
-- additional parameters in curried functions
-------------------------------------------------------------------------
'action' SAL_Gen_Lambda_Param_from_Parameters(
	    FORMAL_FUNCTION_PARAMETERS, TYPE_EXPR, VALUE_EXPR -> VALUE_EXPR)

  'rule' SAL_Gen_Lambda_Param_from_Parameters(list(H, Tail),
	   TExpr, VE -> function(Pos1, LambdaParam, ExprOut))

	 Split_fun_type(TExpr -> ArgsType, ResultType)
	 where(H -> form_parm(Pos1, BS))
	 (|
	    where(BS -> list(B, nil))
	 ||
	    where(BINDING'product(Pos1, BS) -> B)
	 |)
	 where(TYPING'single(Pos1, B, ArgsType) -> Typing)
	 where(s_typing(Pos1, Typing) -> LambdaParam)
	 SAL_Gen_Lambda_Param_from_Parameters(Tail, ResultType, VE -> ExprOut)

  'rule' SAL_Gen_Lambda_Param_from_Parameters(nil, _, VE -> VE)


--------------------------------------------------------------------------------
-- Type_Check
--------------------------------------------------------------------------------
-- This function type checks an expression against the expected type for it.
-- The type checking is carried out following the SAL type system and equivalence 
-- rules.
-- (that is different from the MAXIMAL type equivalence used in RAISE).
--------------------------------------------------------------------------------

'action' Type_Check(POS, VALUE_EXPR, EXPR_CONTEXT, TYPE_EXPR)

	 -- Skipping the type checking...
	 -- Remove this and invoke the proper routine: the one below is not powerfull
	 -- enough (it fails because of
	 -- Get_Type_of_Value_Expr can not be invoked sometimes (like in the expression
	 -- inside a restriction), because it does not has a way to update the context
	 -- properly according with the typings before)
  'rule' Type_Check(_, _, _, _)

  'rule' Type_Check(Pos, Expr, normal, ExpectedType)
	 Get_Type_of_Value_Expr(Expr -> ActualType)
             [|
	         Is_Collection(Expr)
		 (|
		    -- It IS a collection... no unfolding of actuals...
		    SAL_Match_Type(Pos, ActualType, ExpectedType,no)
		 ||
		    -- Error reporting:
	            (|
	                -- Map errors:
			Type_is_map(ExpectedType -> Dom,Rng)
			-- Checking the domain:
			Type_is_map(ActualType -> ExprDom, ExprRng)
			(|
	                    SAL_Match_Type(Pos, Dom,ExprDom,no)
		        ||
		            Puterror(Pos)
			    Putmsg("Incopatible types in map domain:\nExpected: ")
			    Print_type(Dom)
			    Putmsg("\nFound: ")
			    Print_type(ExprDom)
			    Putnl()
		        |)
			-- Checking the range:
		        (|
		            SAL_Match_Type(Pos, Rng,ExprRng,no)
		        ||
	                    Puterror(Pos)
		            Putmsg("Incopatible types in map range:\nExpected: ")
			    Print_type(Rng)
			    Putmsg("\nFound: ")
			    Print_type(ExprRng)
			    Putnl()
	                |)
	           ||
	                Puterror(Pos)
		        Putmsg("Expected type: ")
		        Print_type(ExpectedType)
		        Putmsg(" type found: ")
		        Print_type(ActualType)
		        Putnl()
                   |)
		|)
	     |]
	     -- Verifying infix ops for collections ....
	     [|
	       (|
	         Infix_occ_is_Collection_op(Expr)
	         where(Expr -> infix_occ(Pos1, LE,Op,_,RE))
		 Get_Type_of_Value_Expr(Expr -> FullType)
		 Get_Type_of_Value_Expr(LE -> TLE)
		 Get_Type_of_Value_Expr(RE -> TRE)
		 Op'Ident -> IdOp
		 SAL_Split_Type_of_infix_occ(Expr -> LeftType, RightType)
		 (|
		     -- Do not unfold subtypes (not for collections)
	             SAL_Match_Type(Pos, TLE, LeftType,no)
		 ||
		     Puterror(Pos1)
		     Putmsg("Incompatible types in the domain of application of ")
		     Print_id_or_op(IdOp)
		     Putmsg(".\n Found: ")
		     Print_type(TLE)
		     Putmsg(" expected: ")
		     Print_type(LeftType)
		     Putnl()
		 |)
		 (|
		     SAL_Match_Type(Pos, TRE, RightType,no)
		 ||
		     Puterror(Pos1)
		     Putmsg("Incompatible types in range of the application of ")
		     Print_id_or_op(IdOp)
		     Putmsg(".\n Found: ")
		     Print_type(TRE)
		     Putmsg(" expected: ")
		     Print_type(RightType)
		     Putnl()
		 |)
	       ||
	         where(Expr -> ass_occ(Pos1, VarId, _, RE))
		 VarId'Type -> TLE
		 Get_Type_of_Value_Expr(RE -> TRE)
		 (|
		     -- Do not unfold subtypes (not for collections)
		     Is_Collection(RE)
	             SAL_Match_Type(Pos, TLE, TRE,no)
		 ||
		     -- It is not a collection... unfold if neccesary
	             SAL_Match_Type(Pos, TLE, TRE, yes)
		 ||
		     Puterror(Pos1)
		     Putmsg("Incompatible types in assignament")
		     Putmsg(".\n Left hand side: ")
		     Print_type(TLE)
		     Putmsg(" right hand side: ")
		     Print_type(TRE)
		     Putnl()
		 |)
               |)
	     |]


  'rule' Type_Check(Pos, Expr, argument, ExpectedType)
	 -- In this expression context, the rules are the same than the ones in RSL and,
	 -- as the code has already been type checked, we know that it TYPE CHECKS!

--------------------------------------------------------
'action' Gen_Map_Type(POS, TYPE_EXPR, POS, TYPE_EXPR -> SAL_type_id)

  'rule' Gen_Map_Type(DomPos, DomType, RngPos, RngType -> MapTid)
--Putmsg("Entering to generate a new map...\n")
--Print_type(DomType)
--Putmsg("-m->")
--Print_type(RngType)
--Putnl()
	 -- CWG 14/4/08
	 -- CC map uses unlifted map: no nav values in range
         (|  -- Domain:
	     where(DomType -> defined(DomTypeid,_))
	     DomTypeid'Ident -> DomIdent
	     (|
	        -- Range:
	        where(RngType -> defined(RngTypeid,_))
	        RngTypeid'Ident -> RngIdent
		SAL_Gen_New_Map_Type(DomPos, DomIdent, RngIdent, DomType, RngType -> MapTid)
	     ||
	        Is_basic_type(RngType)
	        (|
	            where(RngType -> int)
		    Default_Int_Tid -> Tid
                ||
	            where(RngType -> nat)
		    Default_Nat_Tid -> Tid
                ||
	            where(RngType -> bool)
		    Default_Bool_Tid -> Tid
	        |)
		Tid'Ident -> RngIdent

		-- Generating the map:
		SAL_Gen_New_Map_Type(DomPos,DomIdent, RngIdent, DomType, RngType -> MapTid)
	     ||
	        -- this is an anonymous type... (like Int -m-> (Int >< Nat))
	        -- NOT ACCEPTED!
	        Puterror(RngPos)
	        Putmsg("Type not accepted for the range of map\n")
		SAL_Gen_Type_Ident(-> Ident)
		New_SAL_type_id(RngPos, Ident, any -> MapTid)	
	     |)
	 ||
	       Is_basic_type(DomType)
	       (|
	         where(DomType -> int)
		 Default_Int_Tid -> Tid
               ||
	         where(DomType -> nat)
		 Default_Nat_Tid -> Tid
               ||
	         where(DomType -> bool)
		 Default_Bool_Tid -> Tid
	       |)
	       Tid'Ident -> DomIdent
             (|
	        -- Range:
	        where(RngType -> defined(RngTypeid,_))
	        RngTypeid'Ident -> RngIdent
		SAL_Gen_New_Map_Type(DomPos,DomIdent, RngIdent, DomType, RngType -> MapTid)
	     ||
	        Is_basic_type(RngType)
	        (|
	           where(RngType -> int)
		   Default_Int_Tid -> Tid1
                ||
		   where(RngType -> nat)
		   Default_Nat_Tid -> Tid1
                ||
		   where(RngType -> bool)
		   Default_Bool_Tid -> Tid1
	        |)
		Tid1'Ident -> RngIdent
		SAL_Gen_New_Map_Type(DomPos,DomIdent, RngIdent, DomType, RngType -> MapTid)
	     ||
	        -- this is an anonymous type... (like Int -m-> (Int >< Nat))
	        -- NOT ACCEPTED!
	        Puterror(RngPos)
	        Putmsg("Type not accepted for the range of map\n")
		SAL_Gen_Type_Ident(-> Ident)
		New_SAL_type_id(RngPos, Ident, any -> MapTid)	
	     |)
	 ||
	      -- this is an anonymous type... (like (Int >< Nat)-m-> Int)
	      -- NOT ACCEPTED!
	      Puterror(DomPos)
	      Putmsg("Type not accepted for the domain of map\n")
	      SAL_Gen_Type_Ident(-> Ident)
	      New_SAL_type_id(DomPos, Ident, any -> MapTid)	
	 |)


'action' Gen_Array_Type(POS, TYPE_EXPR, POS, TYPE_EXPR -> SAL_type_id)

  'rule' Gen_Array_Type(DomPos, DomType, RngPos, RngType -> ArrayTid)
--Putmsg("Entering to generate a new map...\n")
--Print_type(DomType)
--Putmsg("-m->")
--Print_type(RngType)
--Putnl()
--Print_type(RngType)
	 -- CWG 14/4/08
	 -- CC map uses unlifted map: no nav values in range
         (|  -- Domain:
	     where(DomType -> defined(DomTypeid,_))
	     DomTypeid'Ident -> DomIdent
	     (|
	        -- Range:
	        where(RngType -> defined(RngTypeid,_))
	        RngTypeid'Ident -> RngIdent
		SAL_Gen_New_Array_Type(DomPos, DomIdent, RngIdent, DomType, RngType -> ArrayTid)
	     ||
	        Is_basic_type(RngType)
	        (|
	            where(RngType -> int)
		    Default_Int_Tid -> Tid
                ||
	            where(RngType -> nat)
		    Default_Nat_Tid -> Tid
                ||
	            where(RngType -> bool)
		    Default_Bool_Tid -> Tid
	        |)
		Tid'Ident -> RngIdent

		-- Generating the array:
		SAL_Gen_New_Array_Type(DomPos,DomIdent, RngIdent, DomType, RngType -> ArrayTid)
	     ||
	        -- this is an anonymous type... (like Int -m-> (Int >< Nat))
	        -- NOT ACCEPTED!
	        Puterror(RngPos)
	        Putmsg("Type not accepted for the range of array\n")
		SAL_Gen_Type_Ident(-> Ident)
                --SAL_Gen_Type_Expr(RngPos, RngType ->
		New_SAL_type_id(RngPos, Ident, any -> ArrayTid)	
	     |)
	 ||
	       Is_basic_type(DomType)
	       (|
	         where(DomType -> int)
		 Default_Int_Tid -> Tid
               ||
	         where(DomType -> nat)
		 Default_Nat_Tid -> Tid
               ||
	         where(DomType -> bool)
		 Default_Bool_Tid -> Tid
	       |)
	       Tid'Ident -> DomIdent
             (|
	        -- Range:
	        where(RngType -> defined(RngTypeid,_))
	        RngTypeid'Ident -> RngIdent
		SAL_Gen_New_Array_Type(DomPos,DomIdent, RngIdent, DomType, RngType -> ArrayTid)
	     ||
	        Is_basic_type(RngType)
	        (|
	           where(RngType -> int)
		   Default_Int_Tid -> Tid1
                ||
		   where(RngType -> nat)
		   Default_Nat_Tid -> Tid1
                ||
		   where(RngType -> bool)
		   Default_Bool_Tid -> Tid1
	        |)
		Tid1'Ident -> RngIdent
		SAL_Gen_New_Array_Type(DomPos,DomIdent, RngIdent, DomType, RngType -> ArrayTid)
	     ||
	        -- this is an anonymous type... (like Int -m-> (Int >< Nat))
	        -- NOT ACCEPTED!
	        Puterror(RngPos)
	        Putmsg("Type not accepted for the range of array\n")
		SAL_Gen_Type_Ident(-> Ident)
		New_SAL_type_id(RngPos, Ident, any -> ArrayTid)	
	     |)
	 ||
	      -- this is an anonymous type... (like (Int >< Nat)-m-> Int)
	      -- NOT ACCEPTED!
	      Puterror(DomPos)
	      Putmsg("Type not accepted for the domain of array\n")
	      SAL_Gen_Type_Ident(-> Ident)
	      New_SAL_type_id(DomPos, Ident, any -> ArrayTid)	
	 |)




'action' Gen_Set_Type(POS, TYPE_EXPR -> SAL_type_id)

  'rule' Gen_Set_Type(Pos, Type -> SetTid)
	 (|
	     where(Type -> defined(Typeid,_))
	     Typeid'Ident -> Ident
	     SAL_Gen_New_Set_Type(Pos, Ident, Type -> SetTid)
	 ||
	     Is_basic_type(Type)
	     (|
	         where(Type -> int)
		 Default_Int_Tid -> Tid
	         Tid'Ident -> Ident
             ||
	         where(Type -> bool)
		 Default_Bool_Tid -> Tid
	         Tid'Ident -> Ident
             ||
	         where(Type -> nat)
		 Default_Nat_Tid -> Tid
	         Tid'Ident -> Ident
	     |)
	     SAL_Gen_New_Set_Type(Pos, Ident, Type -> SetTid)
	 /*||
             SAL_Gen_Type_Expr(Pos, Type -> SAL_Type, SAL_CC_Type)
             SAL_Check_Defined_Maximal_Type(Type -> tid(Tid))
             --SAL_Check_Defined_Type(Type -> tid(Tid))
             Tid'Ident -> Ident
             SAL_Gen_New_Set_Type(Pos, Ident, Type -> SetTid)*/
         ||
	     Puterror(Pos)
	     Putmsg("Type not supported for sets (")
	     Print_type(Type)
	     Putmsg(")\n")
	     -- print(Type)
	     SAL_Gen_Type_Ident(-> Ident)
	     New_SAL_type_id(Pos, Ident, any -> SetTid)
	 |)

	 

---------------------------------------------------------------------
'condition' Is_basic_type(TYPE_EXPR)

  'rule' Is_basic_type(int)
  'rule' Is_basic_type(nat)
  'rule' Is_basic_type(bool)
-- non supported:
  'rule' Is_basic_type(unit)
  'rule' Is_basic_type(real)
  'rule' Is_basic_type(text)
  'rule' Is_basic_type(char)
  'rule' Is_basic_type(time)

'condition' Is_Collection_type(TYPE_EXPR)

  'rule' Is_Collection_type(Type)
	 Type_is_set(Type -> _)

  'rule' Is_Collection_type(Type)
	 Type_is_map(Type -> _, _)

  'rule' Is_Collection_type(Type)
	 Type_is_list(Type -> _)

-----------------------------------
'condition' Infix_occ_is_Collection_op(VALUE_EXPR)

  'rule' Infix_occ_is_Collection_op(infix_occ(Pos1, LE,Op1,_,RE))
	 Op1'Ident -> Op
	 (|
	    Get_Type_of_Value_Expr(LE -> TL)
	    Is_Collection_type(TL)
	 ||
	    Get_Type_of_Value_Expr(RE -> TR)
	    Is_Collection_type(TR)
	 |)

-------------------------------------
'action' SAL_Turn_Type_into_Maximal_plus_restriction(TYPE_EXPR -> SAL_TYPE_EXPR)

  'rule' SAL_Turn_Type_into_Maximal_plus_restriction(defined(TypeId,_) -> Type)
	 TypeId'Def -> abbreviation(TE)
	 SAL_Turn_Type_into_Maximal_plus_restriction(TE -> Type)

/*  'rule' SAL_Turn_Type_into_Maximal_plus_restriction(int, inside_subtype -> Type)
	 DefaultPos(-> P)
	 Default_Int_Tid -> ITid
	 ITid'Args -> list(LI_Vid,list(HI_Vid,nil))
	 string_to_id("x_" -> Id)
	 -- x_ >= LowInt
	 where(sal_infix_occ(sal_value_occ(val_id(id(Id)),nil), val_id(sal_op_symb(sal_infix_op(ge))), sal_esp_value_occ(LI_Vid)) -> LE)
	 -- x_ <= MaxInt
	 where(sal_infix_occ(sal_value_occ(val_id(id(Id)),nil), val_id(sal_op_symb(sal_infix_op(le))), sal_esp_value_occ(HI_Vid)) -> RE)
	 -- LE /\ RE
	 where(sal_ax_infix(LE, and, RE) -> Restriction)
	 where(user_defined(sal_subtype(id(Id),sal_basic(sal_integer),nil, Restriction)) -> Type)
*/

  'rule' SAL_Turn_Type_into_Maximal_plus_restriction(int -> Type)
	 DefaultPos(-> P)
	 SAL_Gen_Type_Expr(P, int -> Type, _)

/*  'rule' SAL_Turn_Type_into_Maximal_plus_restriction(nat, inside_subtype -> Type)
	 DefaultPos(-> P)
	 Default_Nat_Tid -> ITid
	 ITid'Args -> list(HI_Vid,nil)
	 string_to_id("x_" -> Id)
	 string_to_id("0" -> ZeroId)
	 -- x_ >= LowInt
	 where(sal_infix_occ(sal_value_occ(val_id(id(Id)),nil), val_id(sal_op_symb(sal_infix_op(ge))), sal_value_occ(val_id(id(ZeroId)),nil)) -> LE)
	 -- x_ <= MaxInt
	 where(sal_infix_occ(sal_value_occ(val_id(id(Id)),nil), val_id(sal_op_symb(sal_infix_op(le))), sal_esp_value_occ(HI_Vid)) -> RE)
	 -- LE /\ RE
	 where(sal_ax_infix(LE, and, RE) -> Restriction)
	 where(user_defined(sal_subtype(id(Id),sal_basic(sal_integer),nil, Restriction)) -> Type)
*/
  'rule' SAL_Turn_Type_into_Maximal_plus_restriction(nat -> Type)
	 DefaultPos(-> P)
	 SAL_Gen_Type_Expr(P, nat -> Type, _)

  'rule' SAL_Turn_Type_into_Maximal_plus_restriction(T : subtype(Typing, Restriction) -> Type)
	 DefaultPos(-> P)
	 SAL_Gen_Type_Expr(P, T -> user_defined(sal_subtype(Ident,_,Namespace,SALRestriction)), CC_Type)
--SAL_Print_Expr(SALRestriction)
--Putnl()
--
--Gen_SAL_Expr(R, normal, bool -> _, R1)
--SAL_Print_Expr(R1)
--Putnl()
	 -- jiperna: Trying this now (using a lifted restriction expression rather the one generated in
	 -- the type expression).
	 -- This is an attempt to avoid the problem that arises when a ranged set is defined using
	 -- defined values. For example, {T.min .. 3} would produce in the lifted version:
	 -- {| SAL_TYPES!min .. 3 |} where it should produce
	 -- {| SAL_cc_TYPES!min .. Lifted_int(3) |}
	 where(Restriction -> restriction(_,R))
	 Gen_SAL_Expr(R, normal, bool -> _, LiftedRestriction)
	 where(Ident -> id(X_Ident))
	 -- Generating a lifted occurrence of x_
	 where(CC_Type -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,Tid)),_)))
	 Tid'Constructor -> vid(Const)
	 where(sal_argument(list(sal_value_occ(val_id(Ident),nil),nil)) -> Args)
	 -- Generating the AST for the constructor ident:
	 where(sal_esp_value_occ(Const) -> Constructor)
	 -- function application (constructor of the variant)
	 where(sal_funct_applic(Constructor, Args) -> NewXOcc)
	 SAL_Replace_Ident(X_Ident, NewXOcc, LiftedRestriction -> NewRestriction1)
	 -- Adding the 'is_true' to make it BOOL:
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 where(sal_cc_op(sal_function_op(is_true), LBTid) -> SAL_Op)
	 -- add is_true
	 where(sal_esp_unary_prefix_occ(val_id(SAL_Op), NewRestriction1) -> NewRestriction)
--juan
	 SAL_Get_Maximal_Type_from_Typing(Typing -> TExpr)
	 where(user_defined(sal_subtype(Ident,TExpr,Namespace,NewRestriction)) -> Type) -- formerlu: SALRestriction instead of NewRestriction

  'rule' SAL_Turn_Type_into_Maximal_plus_restriction(T -> Type)
	 DefaultPos(-> P)
	 SAL_Gen_Type_Expr(P, T -> Type,_)

'action' SAL_Get_Maximal_Type_from_Typing(TYPING -> SAL_TYPE_EXPR)

  'rule' SAL_Get_Maximal_Type_from_Typing(single(Pos, BS, T) -> sal_basic(sal_integer))
	 Maxtype(T -> int)


	 -- just in case... doesn't seem to be useful, but still possible
  'rule' SAL_Get_Maximal_Type_from_Typing(single(Pos, BS, T) -> sal_basic(sal_boolean))
	 Maxtype(T -> bool)

	 -- is this correct?
  'rule' SAL_Get_Maximal_Type_from_Typing(Typing -> SAL_Type)
	 (|
	    where(Typing -> single(P,_,T))
	 ||
	    where(Typing -> multiple(P,_,T))
	 |)
	 SAL_Gen_Type_Expr(P, T -> SAL_Type,_)

-----------------------------------------------------------------
'action' SAL_Reduce_to_finite_collections(TYPE_EXPR -> TYPE_EXPR)

  'rule' SAL_Reduce_to_finite_collections(infin_set(T) -> fin_set(T1))
	 SAL_Reduce_to_finite_collections(T -> T1)
  
  'rule' SAL_Reduce_to_finite_collections(infin_map(D,R) -> fin_map(D1,R1))
	 SAL_Reduce_to_finite_collections(D -> D1)
	 SAL_Reduce_to_finite_collections(R -> R1)

  'rule' SAL_Reduce_to_finite_collections(infin_list(T) -> fin_list(T1))
	 SAL_Reduce_to_finite_collections(T -> T1)

--CWG 24/6/06
-- jiperna: 25/06/06: if a defined type is opened, then we are missing the Tid information
-- and this will generate problems when trying to generate sets of this type. For example, in the case
-- of an T1-set (where T1 is a defined type). When we are translating something of the form a isin T1_var, we miss
-- the information that says what T1_var is a type reference and we get the type expression that is abbreviated by T1.
-- This produces errors, for example, when trying to find (or declare) a set of type T1.
-- Moreover, this rule is not necessary because the whole predicate is meant to transform type expressions
-- of the form infin-set or things like that... In the case of abbreviations, the error (an infin set or map) would
-- be detected when the type is declared and here, the error skipped.

--  'rule' SAL_Reduce_to_finite_collections(T:defined(I, _) -> T1):
--	 I'Def -> Defn
--	 (|
--	   where(Defn -> abbreviation(TA))
--	   SAL_Reduce_to_finite_collections(TA -> T1)
--	 ||
--	   where(T -> T1)
--	 |)

  'rule' SAL_Reduce_to_finite_collections(product(TS) -> product(TS1)):
	 SAL_Reduce_to_finite_product(TS -> TS1)

  'rule' SAL_Reduce_to_finite_collections(fin_set(T) -> fin_set(T1))
	 SAL_Reduce_to_finite_collections(T -> T1)
  
  'rule' SAL_Reduce_to_finite_collections(fin_map(D,R) -> fin_map(D1,R1))
	 SAL_Reduce_to_finite_collections(D -> D1)
	 SAL_Reduce_to_finite_collections(R -> R1)

  'rule' SAL_Reduce_to_finite_collections(fin_list(T) -> fin_list(T1))
	 SAL_Reduce_to_finite_collections(T -> T1)

  'rule' SAL_Reduce_to_finite_collections(
	      fun(D, A, result(R,Rd,Wr,In,Out)) ->
	           fun(D1, A, result(R1,Rd,Wr,In,Out))):
	 SAL_Reduce_to_finite_collections(D -> D1)
	 SAL_Reduce_to_finite_collections(R -> R1)

  'rule' SAL_Reduce_to_finite_collections(subtype(TP, R) -> subtype(TP1, R)):
	 SAL_Reduce_to_finite_typing(TP -> TP1)

  'rule' SAL_Reduce_to_finite_collections(bracket(T) -> T1):
	 SAL_Reduce_to_finite_collections(T -> T1)

  'rule' SAL_Reduce_to_finite_collections(T -> T)

'action' SAL_Reduce_to_finite_product(PRODUCT_TYPE -> PRODUCT_TYPE)

  'rule' SAL_Reduce_to_finite_product(list(T, TS) -> list(T1, TS1)):
	 SAL_Reduce_to_finite_collections(T -> T1)
	 SAL_Reduce_to_finite_product(TS -> TS1)

  'rule' SAL_Reduce_to_finite_product(nil -> nil):

'action' SAL_Reduce_to_finite_typing(TYPING -> TYPING)

  'rule' SAL_Reduce_to_finite_typing(single(P,B,T) -> single(P,B,T1)):
	 SAL_Reduce_to_finite_collections(T -> T1)

  'rule' SAL_Reduce_to_finite_typing(multiple(P,BS,T) -> multiple(P,BS,T1)):
	 SAL_Reduce_to_finite_collections(T -> T1)

'condition' Print_Sal_Bind_Ident(SAL_BINDINGS)
  'rule' Print_Sal_Bind_Ident(list(sal_typed_id(_,_,type_refs(sal_defined(_,Ident,_))),_)):
         C_id_to_string(Ident -> IdentString)
--	 print(IdentString)

  'rule' Print_Sal_Bind_Ident(_):
         print("No match")

'action' Get_Ident_From_Binding(SAL_BINDINGS -> IDENT)
  'rule' Get_Ident_From_Binding(list(sal_typed_id(_,id(Ident),_),nil) -> Ident)

'action' Set_Valoccs_As_Locals_Parameters(ACTUAL_FUNCTION_PARAMETERS -> ACTUAL_FUNCTION_PARAMETERS)

  'rule' Set_Valoccs_As_Locals_Parameters(nil -> nil)

  'rule' Set_Valoccs_As_Locals_Parameters(list(fun_arg(P,Exprs),Rest) -> list(fun_arg(P,ExprsRes),RestRes))
         Set_Valoccs_As_Locals_Parameters(Rest -> RestRes)
         Set_Valoccs_As_Locals_Exprs(Exprs -> ExprsRes)

'action' Set_Valoccs_As_Locals_Exprs(VALUE_EXPRS -> VALUE_EXPRS)
  'rule' Set_Valoccs_As_Locals_Exprs(nil -> nil)

  'rule' Set_Valoccs_As_Locals_Exprs(list(H,T) -> list(HRes,TRes))
         Set_Valoccs_As_Locals_Exprs(T -> TRes)
         Set_Valoccs_As_Locals(H -> HRes)

'action' Set_Valoccs_As_Locals(VALUE_EXPR -> VALUE_EXPR)
  'rule' Set_Valoccs_As_Locals(val_occ(P,V,Q) -> local_val_occ(P,V,Q))

  'rule' Set_Valoccs_As_Locals(application(P, E, A) -> application(P, E, ARes))
         Set_Valoccs_As_Locals_Parameters(A -> ARes)

  'rule' Set_Valoccs_As_Locals(ax_infix(Pos1, Left, Con, Right, Pos2) -> ax_infix(Pos1, LeftRes, Con, RightRes, Pos2))
         Set_Valoccs_As_Locals(Left -> LeftRes)
         Set_Valoccs_As_Locals(Right -> RightRes)

  'rule' Set_Valoccs_As_Locals(V -> V)



