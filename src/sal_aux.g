-- RSL Type Checker
-- Copyright (C) 2005 UNU/IIST

-- raise@iist.unu.edu

-- This module has auxiliary actions for
-- the RSL to SAL translator

'module' sal_aux


'use' ast print ext env objects values types pp cc sml
      sal_ast sal_gen_ast
      sal_print
      sal_global_vars
      sal_gen_ast	-- SAL_Gen_Type_Expr
      pvs_gen_ast       -- Get_Type_of_Value_Expr	
      sal_cc_aux

'export'
	 --   Variables

	 -- Actions
	 SAL_Init_Aux


	 -- To manage ContextIdMap
--	 InitContextIdMap
--	 AddContext
--	 GetContextId

	 -- To manage context's info
	 Insert_Context_Element
	 Insert_Context_Elements
	 SAL_Insert_Destructor
	 SAL_Insert_Reconstructor
	 SAL_Insert_DataTypePart
	 SAL_Insert_Tuple
	 SAL_Insert_Expr
	 SAL_Insert_ExprPair
	 SAL_Insert_Elsif	 
	 
	 -- To manage precedences:
	 SAL_lower_precedence
	 SAL_connective_precedence
	 SAL_infix_precedence

	 -- Translation utilities
	 SALBindings_to_expr
	 
	 -- For Let identifier generation
	 SAL_Gen_Let_Ident

	 -- For Let expression concatenation
	 SAL_Join_SAL_Let_Defs

	 -- For Params identifier generation
	 SAL_Gen_Param_Ident

	 -- For types (subtypes) ident. generation
	 SAL_Gen_Type_Ident

	 -- For Sort expansion (macro proc)
	 SAL_Gen_Sort_Value_Ident

	 -- For binding remainings processing:
	 SAL_Append_Remainings


	 SAL_Concatenate_Decls
	 SAL_Concatenate_Value_Ids
	 SAL_Concatenate_Type_Ids
	 SAL_Concatenate_Context_Constants
	 SAL_Remove_Duplicate_Context_Constants
	 SAL_Append_Decl
	 SAL_Concatenate_Variable_Decls
	 SAL_Concatenate_Initializations
	 SAL_Concatenate_Bindings
	 SAL_Concatenate_Transitions
	 SAL_Concatenate_Types

	 Remove_duplicates_from_Vids
	 Remove_duplicates_from_Tids
	 Remove_reconstructors

	 SAL_Concatenate_Context_Args
	 SAL_Extract_Args_from_Tids
	 SAL_Remove_Duplicated_Args

	 Collect_Tids_in_Cid
	 SAL_Split_Constants
	 Update_Reference_Information

	 SAL_Check_Cid_in_Cids
	 SAL_Remove_Duplicates_from_Fixed_Point
	 SAL_Remove_Duplicates_from_Decls

	 SAL_Remove_SAL_TYPES

	 Is_Tid_Included_in_Decls
	 Is_Vid_Included_in_Decls

	 Push_Namespace
	 Pop_Namespace

	 SAL_Remove_First_Brackets_from_Binding

	 SAL_Gen_Arg_Names_for_Tuple
	 SAL_Concatenate_Value_Exprs

	 -- Routines for default context generation/initialization
	 SAL_Gen_Int_Context_and_Tid
	 SAL_Gen_Bool_Context_and_Tid
	 SAL_Gen_Nat_Context_and_Tid

	 Generate_Constant_for_Type
	 Generate_Global_Constant
	 Generate_Global_Pair_of_Constants
	 Update_Global_Constant

	 -- For list type handling:
	 SAL_Check_Defined_List
	 SAL_Gen_New_List_Type

	 -- For set type handling:
	 SAL_Check_Defined_Set
	 SAL_Check_Defined_Maximal_Set
	 SAL_Gen_New_Set_Type

	 -- For map type handling:
	 SAL_Check_Defined_Map
	 SAL_Gen_New_Map_Type

	 -- For array type handling:
	 SAL_Check_Defined_Array
	 SAL_Gen_New_Array_Type

	 -- For disambiguation handling:
	 Push_Disamb
	 Pop_Disamb
	 Get_Current_Disamb


	 SAL_Match_Type

	 SAL_Get_Expr_Pos
	 Is_Collection
	 
	 SAL_Split_Type_of_infix_occ

	 SAL_Find_Accesor_in_Fields
	 SAL_Reset_Fixed_Point_Info
	 SAL_Gen_Ident_From_Type

	 SAL_Check_Defined_Maximal_Type
	 Add_Lifted_to_Global
	 Init_SAL_CC_Collection

	 SAL_Gen_CC_Ops_Context
	 SAL_Get_MapNav

'type' CONTEXT_ID_MAP

       list		(Head	:	CONTEXT_ID_MAP_NODE,
			 Tail	:	CONTEXT_ID_MAP)

       nil

'type'  CONTEXT_ID_MAP_NODE     

	map_node	(orig	:	Object_id,
			 mapped	:	SAL_context_id)


-- used to map Scheme identifiers to Cids

'var' ContextIdMap	: CONTEXT_ID_MAP

'action' SAL_Init_Aux

  'rule' SAL_Init_Aux
	 LetIndex <- 0
	 ParamIndex <- 0
	 TypeIndex <- 0
	 SortIndex <- 0
	 Current_List_Types <- nil	 
	 Current_Set_Types <- nil
	 Current_Map_Types <- nil 
         Current_Array_Types <- nil
	 Current_CC_Lifted_Types <- nil
	 Disamb_Stack <- nil

'action' SAL_Gen_Let_Ident(-> IDENT)
	 
  'rule' SAL_Gen_Let_Ident(-> IdLet):
	 where("LetId" -> IdStrng1)
	 LetIndex -> LetIndex1
	 LetIndex <- LetIndex1 + 1
	 LetIndex -> LetIndex2
	 Int_to_string(LetIndex2 -> LetIndxStrng)
	 Concatenate3(IdStrng1, LetIndxStrng, "_" -> LetIdStrng)
	 string_to_id(LetIdStrng -> IdLet)

'action' SAL_Join_SAL_Let_Defs(SAL_VALUE_EXPR, SAL_VALUE_EXPR -> SAL_VALUE_EXPR)

  'rule' SAL_Join_SAL_Let_Defs(sal_let_expr(Id, TElem, NS, LBS, Init, Expr) ,  SExpr -> Result):
	 SAL_Join_SAL_Let_Defs(Expr, SExpr -> Result1)
	 where(sal_let_expr(Id, TElem, NS, LBS, Init, Result1) -> Result)

  'rule' SAL_Join_SAL_Let_Defs(nil, SExpr -> SExpr)

  'rule' SAL_Join_SAL_Let_Defs(no_val, SExpr -> SExpr)

  'rule' SAL_Join_SAL_Let_Defs(S, SExpr -> SExpr)
	 Putmsg("Debugging predicate activated in SAL_Join_SAL_Let_Defs\n")
	 print(S)

'action' SAL_Gen_Param_Ident(-> IDENT)
	 
  'rule' SAL_Gen_Param_Ident(-> IdParam):
	 where("ParamId" -> IdStrng1)
	 ParamIndex -> ParamIndex1
	 ParamIndex <- ParamIndex1 + 1
	 ParamIndex -> ParamIndex2
	 Int_to_string(ParamIndex2 -> ParamIndxStrng)
	 Concatenate3(IdStrng1, ParamIndxStrng, "_" -> ParamIdStrng)
	 string_to_id(ParamIdStrng -> IdParam)

'action' SAL_Gen_Type_Ident(-> IDENT)
	 
  'rule' SAL_Gen_Type_Ident(-> IdType):
	 where("TypeId" -> IdStrng1)
	 TypeIndex -> TypeIndex1
	 TypeIndex <- TypeIndex1 + 1
	 TypeIndex -> TypeIndex2
	 Int_to_string(TypeIndex2 -> TypeIndxStrng)
	 Concatenate3(IdStrng1, TypeIndxStrng, "_" -> TypeIdStrng)
	 string_to_id(TypeIdStrng -> IdType)

'action' SAL_Gen_Sort_Value_Ident(-> IDENT)

  'rule' SAL_Gen_Sort_Value_Ident(-> IdSort):
	 where("SortVal" -> IdStrng1)
	 SortIndex -> SortIndex1
	 SortIndex <- SortIndex1 + 1
	 SortIndex -> SortIndex2
	 Int_to_string(SortIndex2 -> SortIndxStrng)
	 Concatenate3(IdStrng1, SortIndxStrng, "_" -> SortIdStrng)
	 string_to_id(SortIdStrng -> IdSort)

/*--------------------------------------------------
--  to manage ContextIdMap
--------------------------------------------------
'action' InitContextIdMap

  'rule' InitContextIdMap:
	 ContextIdMap <- nil

'action' AddContext(Object_id -> IDENT)

  'rule' AddContext(I -> Id1):
	 ContextIdMap -> Map
	 I'Ident -> Id
	 AddContext1(I, Id, Map, 1 -> Id1)

'action' AddContext1(Object_id, IDENT, CONTEXT_ID_MAP, INT -> IDENT)

  'rule' AddContext1(I, New, theory_map(I1, New1, Map), N -> Id):
	 (|
	   eq(I, I1) -- nothing to do
	   where(New1 -> Id)
	 ||
	   eq(New, New1)
	   I'Ident -> Orig
	   id_to_string(Orig -> S)
	   Make_concatenation(S, N -> S1)
	   string_to_id(S1 -> New2)
	   ContextIdMap -> AllMap
	   AddContext1(I, New2, AllMap, N+1 -> Id)
	 ||
	   AddContext1(I, New, Map, N -> Id)
	 |)

  'rule' AddContext1(I, New, nil, _ -> New):
	 ContextIdMap -> AllMap
	 ContextIdMap <- theory_map(I, New, AllMap)

'action' GetContextId(Object_id -> IDENT)

  'rule' GetContextId(I -> Id):
	 ContextIdMap -> Map
	 GetContextId1(I, Map -> Id)

'action' GetContextId1(Object_id, CONTEXT_ID_MAP -> IDENT)

  'rule' GetContextId1(I, theory_map(I1, New1, Map) -> Id):
	 (|
	   eq(I, I1)
	   where(New1 -> Id)
	 ||
	   GetContextId1(I, Map -> Id)
	 |)

-- in case used before defined
  'rule' GetContextId1(I, nil -> Id):
	 AddContext(I -> Id)

-- for debugging
'action' PrintContextIdMap

  'rule' PrintContextIdMap:
	 ContextIdMap -> Map
	 PrintContextIdMap1(Map)

'action' PrintContextIdMap1(CONTEXT_ID_MAP)

  'rule' PrintContextIdMap1(theory_map(I, New, Map)):
	 I'Ident -> Id
	 Print_id(Id)
	 Putmsg(" maps to ")
	 Print_id(New)
	 Putnl
	 PrintContextIdMap1(Map)

  'rule' PrintContextIdMap1(nil):
*/
------------------------------------------------------------------
	 
'action' Insert_Context_Element(SAL_CONTEXT_CONSTANT, SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' Insert_Context_Element(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_Context_Element(Elem, ElemsTail -> Elems1)

  'rule' Insert_Context_Element(Elem, nil -> list(Elem, nil)):

-----------------------------------------------------------------------------------
'action' Insert_Context_Elements(SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' Insert_Context_Elements(List, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_Context_Elements(List, ElemsTail -> Elems1)

  'rule' Insert_Context_Elements(List, nil -> List):
--------------------------------------------------------------------

'action' SAL_Insert_Destructor(SAL_DESTRUCTOR, SAL_DESTRUCTORS -> SAL_DESTRUCTORS)

  'rule' SAL_Insert_Destructor(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 SAL_Insert_Destructor(Elem, ElemsTail -> Elems1)

  'rule' SAL_Insert_Destructor(Elem, nil -> list(Elem, nil)):
	 
--------------------------------------------------------------------
'action' SAL_Insert_Reconstructor(SAL_RECONSTRUCTOR, SAL_RECONSTRUCTORS -> SAL_RECONSTRUCTORS)

  'rule' SAL_Insert_Reconstructor(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 SAL_Insert_Reconstructor(Elem, ElemsTail -> Elems1)

  'rule' SAL_Insert_Reconstructor(Elem, nil -> list(Elem, nil)):
--------------------------------------------------------------------

'action' SAL_Insert_DataTypePart(SAL_DATA_TYPE_PART, SAL_DATA_TYPE_PARTS -> SAL_DATA_TYPE_PARTS)

  'rule' SAL_Insert_DataTypePart(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 SAL_Insert_DataTypePart(Elem, ElemsTail -> Elems1)

  'rule' SAL_Insert_DataTypePart(Elem, nil -> list(Elem, nil)):

--------------------------------------------------------------------

'action' SAL_Insert_Tuple(SAL_TUPLE_ELEM, SAL_TUPLE_ELEMS -> SAL_TUPLE_ELEMS)

  'rule' SAL_Insert_Tuple(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 SAL_Insert_Tuple(Elem, ElemsTail -> Elems1)

  'rule' SAL_Insert_Tuple(Elem, nil -> list(Elem, nil)):
----------------------------------------------------------------------
'action' SAL_Insert_Expr(SAL_VALUE_EXPR, SAL_VALUE_EXPRS -> SAL_VALUE_EXPRS)

  'rule' SAL_Insert_Expr(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 SAL_Insert_Expr(Elem, ElemsTail -> Elems1)

  'rule' SAL_Insert_Expr(Elem, nil -> list(Elem, nil)):

---------------------------------

'action' SAL_Insert_ExprPair(SAL_VALUE_EXPR_PAIR, SAL_VALUE_EXPR_PAIRS 
						  -> SAL_VALUE_EXPR_PAIRS)

  'rule' SAL_Insert_ExprPair(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 SAL_Insert_ExprPair(Elem, ElemsTail -> Elems1)

  'rule' SAL_Insert_ExprPair(Elem, nil -> list(Elem, nil)):

-------------------------------------------------------

'action' SAL_Insert_Elsif(SAL_ELSIF_BRANCH, SAL_ELSIF_BRANCHES -> SAL_ELSIF_BRANCHES)

  'rule' SAL_Insert_Elsif(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 SAL_Insert_Elsif(Elem, ElemsTail -> Elems1)

  'rule' SAL_Insert_Elsif(Elem, nil -> list(Elem, nil)):

------------------------------------------------------------
-- Precedence handling....
------------------------------------------------------------

'condition' SAL_lower_precedence(SAL_VALUE_EXPR, INT)

  'rule' SAL_lower_precedence(V, I)
	 SAL_expr_precedence(V -> P)
	 lt(P,I)

'action' SAL_expr_precedence(SAL_VALUE_EXPR -> INT)

  'rule' SAL_expr_precedence(sal_literal(_) -> 0):

  'rule' SAL_expr_precedence(sal_named_val(_) -> 0):

  'rule' SAL_expr_precedence(sal_product(_) -> 0):

  'rule' SAL_expr_precedence(sal_ranged_set(_,_,_) -> 1):

  'rule' SAL_expr_precedence(sal_enum_set(_,_,_) -> 1):

  'rule' SAL_expr_precedence(sal_comp_simp_set(_,_) -> 0):

  'rule' SAL_expr_precedence(sal_comp_set(_,_,_,_) -> 0):

  'rule' SAL_expr_precedence(sal_ranged_list(_,_) -> 1):

  'rule' SAL_expr_precedence(sal_enum_list(_) -> 0):

  'rule' SAL_expr_precedence(sal_comp_list(_,_) -> 1):

  'rule' SAL_expr_precedence(sal_enum_map(_,_,_,_) -> 1):

  'rule' SAL_expr_precedence(sal_comp_rng_map(_,_,_,_,_) -> 22):

  'rule' SAL_expr_precedence(sal_comp_map(_,_,_,_) -> 22):

  'rule' SAL_expr_precedence(sal_function(_,_) -> 22):

  'rule' SAL_expr_precedence(sal_list_applic(_,_) -> 1):

  'rule' SAL_expr_precedence(sal_map_applic(_,_,_) -> 1):

  'rule' SAL_expr_precedence(sal_funct_applic(_,_) -> 1):

  'rule' SAL_expr_precedence(sal_quantified(_,_,_) -> 22):

  'rule' SAL_expr_precedence(sal_equivalence(_,_,nil) -> 14):

  'rule' SAL_expr_precedence(sal_equivalence(_,_,_) -> 18):

  'rule' SAL_expr_precedence(sal_bracket(_) -> 0):

  'rule' SAL_expr_precedence(sal_ax_infix(_,C,_) -> P):
	 SAL_connective_precedence(C -> P)

  'rule' SAL_expr_precedence(sal_funct_expr(_,_,_,_) -> 1):

  'rule' SAL_expr_precedence(sal_ax_prefix(_,_) -> 15):

  'rule' SAL_expr_precedence(sal_let_expr(_,_,_,nil,_,V) -> P):
	 SAL_expr_precedence(V -> P)

  'rule' SAL_expr_precedence(sal_let_expr(_,_,_,_,_,_) -> 22):

  'rule' SAL_expr_precedence(sal_if_expr(_,_,_,_) -> 0):

  'rule' SAL_expr_precedence(sal_value_occ(_,_) -> 0):

  'rule' SAL_expr_precedence(sal_infix_occ(_,val_id(IdOp),_) -> P):
         SAL_id_operator_precedence(IdOp -> P)

  'rule' SAL_expr_precedence(sal_prefix_occ(val_id(IdOp),_,_) -> 1):
         SAL_id_operator_precedence(IdOp -> P)

  'rule' SAL_expr_precedence(_ -> 0):


'action' SAL_connective_precedence(SAL_LOGIC_CONNECTIVE -> INT)

  'rule' SAL_connective_precedence(implies -> 18):

  'rule' SAL_connective_precedence(or -> 17):

  'rule' SAL_connective_precedence(and -> 16):

  'rule' SAL_connective_precedence(not -> 15):

'action' SAL_id_operator_precedence(SAL_ID_OP -> INT)

  'rule' SAL_id_operator_precedence(id(_) -> 1):

  'rule' SAL_id_operator_precedence(sal_op_symb(Op) -> P):
	 SAL_operator_precedence(Op -> P)

  'rule' SAL_id_operator_precedence(sal_set_op(Op,_,_) -> P):
	 SAL_operator_precedence(Op -> P)

  'rule' SAL_id_operator_precedence(sal_map_op(Op,_,_,_) -> P):
	 SAL_operator_precedence(Op -> P)

'action' SAL_operator_precedence(SAL_OP -> INT)

  'rule' SAL_operator_precedence(sal_infix_op(Op) -> P):
	 SAL_infix_precedence(Op -> P)

  'rule' SAL_operator_precedence(sal_prefix_op(_) -> 9):

  'rule' SAL_operator_precedence(sal_function_op(_) -> 1):

'action' SAL_infix_precedence(SAL_INFIX_OP -> INT)

  'rule' SAL_infix_precedence(eq -> 14):

  'rule' SAL_infix_precedence(neq -> 14):

  'rule' SAL_infix_precedence(gt -> 14):

  'rule' SAL_infix_precedence(lt -> 14):

  'rule' SAL_infix_precedence(ge -> 14):

  'rule' SAL_infix_precedence(le -> 14):

  'rule' SAL_infix_precedence(mult -> 8):

  'rule' SAL_infix_precedence(div -> 8):

  'rule' SAL_infix_precedence(int_div -> 8)

  'rule' SAL_infix_precedence(plus -> 9):

  'rule' SAL_infix_precedence(minus -> 9):

---------------------------------------------------
'action' SALBindings_to_expr(SAL_BINDINGS -> SAL_VALUE_EXPR)

  'rule' SALBindings_to_expr(list(B, nil) -> E):
	 SALBinding_to_expr(B -> E)

  'rule' SALBindings_to_expr(BS -> sal_product(ES)):
	 SALBindings_to_exprs(BS -> ES)

'action' SALBindings_to_exprs(SAL_BINDINGS -> SAL_VALUE_EXPRS)

  'rule' SALBindings_to_exprs(list(B, BS) -> list(E, ES)):
	 SALBinding_to_expr(B -> E)
	 SALBindings_to_exprs(BS -> ES)

  'rule' SALBindings_to_exprs(nil -> nil):

'action' SALBinding_to_expr(SAL_BINDING -> SAL_VALUE_EXPR)

  'rule' SALBinding_to_expr(sal_prod_binding(Pos, BS) -> sal_product(ES)):
	 SALBindings_to_exprs(BS -> ES)

  'rule' SALBinding_to_expr(sal_typed_prod(Pos, BS, _) -> sal_product(ES)):
	 SALBindings_to_exprs(BS -> ES)

  'rule' SALBinding_to_expr(sal_typed_id(Pos, IdOp, _) -> sal_named_val(id_op(IdOp))):

----------------------------------------------------------

'action' SAL_Append_Remainings(REMAINING_BINDINGS,REMAINING_BINDINGS
			-> REMAINING_BINDINGS)

  'rule' SAL_Append_Remainings(list(H,T), ToAppend -> Result)
	 SAL_Append_Remainings(T, ToAppend -> Result1)
	 where(REMAINING_BINDINGS'list(H, Result1) -> Result)

  'rule' SAL_Append_Remainings(nil, ToAppend -> ToAppend)

-----------------------------------------------------------
'action' SAL_Concatenate_Decls(SAL_CONSTANT_DECLS, SAL_CONSTANT_DECLS
						   -> SAL_CONSTANT_DECLS)

  'rule' SAL_Concatenate_Decls(list(E,Rest), List -> list(E, Result1))
	 SAL_Concatenate_Decls(Rest, List -> Result1)

  'rule' SAL_Concatenate_Decls(nil, List -> List)

-------------------------------------------------------------

'action' SAL_Concatenate_Value_Ids(SAL_VALUE_IDS, SAL_VALUE_IDS 
						  -> SAL_VALUE_IDS)

  'rule' SAL_Concatenate_Value_Ids(list(Vid,Rest), List -> list(Vid, Result1))
	 SAL_Concatenate_Value_Ids(Rest, List -> Result1)

  'rule' SAL_Concatenate_Value_Ids(nil, List -> List)

-----------------------------------------------------------
'action' SAL_Concatenate_Type_Ids(SAL_TYPE_IDS, SAL_TYPE_IDS 
						  -> SAL_TYPE_IDS)

  'rule' SAL_Concatenate_Type_Ids(list(Tid,Rest), List -> list(Tid, Result1))
	 -- This function is used in the sal_type_fixed_point to join Tid lists
	 -- WE DON'T WANT TO COLLECT THE BASIC TYPES' DEFINITIONS so, the concatenating
	 -- function is ensuring that!
	 Default_Int_Tid -> ITid
	 Default_Nat_Tid -> NTid
	 Default_Bool_Tid -> BTid
	 ITid'Lifted_Tid -> tid(LITid)
	 NTid'Lifted_Tid -> tid(LNTid)
	 BTid'Lifted_Tid -> tid(LBTid)
	 SAL_Nav_Tid -> NavTid
	 ne(Tid, ITid)
	 ne(Tid, NTid)
	 ne(Tid, BTid)
	 ne(Tid, LITid)
	 ne(Tid, LBTid)
	 ne(Tid, LNTid)
	 ne(Tid, NavTid)
	 SAL_Concatenate_Type_Ids(Rest, List -> Result1)

  'rule' SAL_Concatenate_Type_Ids(list(Tid,Rest), List -> Result1)
	 SAL_Concatenate_Type_Ids(Rest, List -> Result1)

  'rule' SAL_Concatenate_Type_Ids(nil, List -> List)
-----------------------------------------------------------
'action' SAL_Concatenate_Context_Constants(SAL_CONTEXT_CONSTANTS,
	   SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

	 -- removing nils if they appear...
  'rule' SAL_Concatenate_Context_Constants(list(nil,T), List -> Result1)
	 SAL_Concatenate_Context_Constants(T, List -> Result1)

  'rule' SAL_Concatenate_Context_Constants(list(H,T), List -> list(H, Result1))
	 SAL_Concatenate_Context_Constants(T, List -> Result1)

  'rule' SAL_Concatenate_Context_Constants(nil, List -> NewList)
	 Remove_nils(List -> NewList)
------------------------------------------------------------
'action' Remove_nils(SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' Remove_nils(list(nil, Rest) -> NewRest)
	 Remove_nils(Rest -> NewRest)

  'rule' Remove_nils(list(T, Rest) -> list(T, NewRest))
	 Remove_nils(Rest -> NewRest)

  'rule' Remove_nils(nil -> nil)
------------------------------------------------------------
-- remove from first list items with same type, value or object ids
-- as items in second list
'action' SAL_Remove_Duplicate_Context_Constants(SAL_CONTEXT_CONSTANTS,
	      SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Remove_Duplicate_Context_Constants(list(H, T), List -> Result):
  	 SAL_Context_Constant_in_list(H, List)
	 SAL_Remove_Duplicate_Context_Constants(T, List -> Result)

  'rule' SAL_Remove_Duplicate_Context_Constants(list(H, T), List -> list(H, Result)):
  	 SAL_Remove_Duplicate_Context_Constants(T, List -> Result)

  'rule' SAL_Remove_Duplicate_Context_Constants(nil, _ -> nil):
------------------------------------------------------------
'condition' SAL_Context_Constant_in_list(SAL_CONTEXT_CONSTANT,
	      SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Context_Constant_in_list(Const, list(H, T)):
  	 (|
	   SAL_Context_Constants_same_id(Const, H)
	 ||
	   SAL_Context_Constant_in_list(Const, T)
	 |)

'condition' SAL_Context_Constants_same_id(SAL_CONTEXT_CONSTANT,
	      SAL_CONTEXT_CONSTANT)

  'rule' SAL_Context_Constants_same_id(sal_type_decl(_, Id1, _),
  	 			       sal_type_decl(_, Id2, _)):
  	 eq(Id1, Id2)

  'rule' SAL_Context_Constants_same_id(sal_object_decl(_, _, Id1, _, _),
  	 			       sal_object_decl(_, _, Id2, _, _)):
  	 eq(Id1, Id2)

  'rule' SAL_Context_Constants_same_id(
  	    sal_const_decl(sal_expl_const(_, Id1, _, _)),
	    sal_const_decl(sal_expl_const(_, Id2, _, _))):
	 eq(Id1, Id2)

  'rule' SAL_Context_Constants_same_id(
  	    sal_const_decl(sal_fun_const(_, Id1, _, _, _, _, _, _)),
	    sal_const_decl(sal_fun_const(_, Id2, _, _, _, _, _, _))):
	 eq(Id1, Id2)



------------------------------------------------------------

'action' SAL_Append_Decl(SAL_CONTEXT_CONSTANT, SAL_CONTEXT_CONSTANTS
	   -> SAL_CONTEXT_CONSTANTS)
   
  'rule' SAL_Append_Decl(Decl, list(H,T) -> list(H, Result))
	 SAL_Append_Decl(Decl, T -> Result)

  'rule' SAL_Append_Decl(Decl, nil -> list(Decl, nil))

------------------------------------------------------------
'action' SAL_Concatenate_Variable_Decls(SAL_VAR_DECLS, SAL_VAR_DECLS -> SAL_VAR_DECLS)

  'rule' SAL_Concatenate_Variable_Decls(list(V1, Rest), List -> list(V1, NewList))
	 SAL_Concatenate_Variable_Decls(Rest, List -> NewList)

  'rule' SAL_Concatenate_Variable_Decls(nil, List -> List)
------------------------------------------------------------
'action' SAL_Concatenate_Initializations(SAL_INITIALIZATIONS,
			SAL_INITIALIZATIONS -> SAL_INITIALIZATIONS)

  'rule' SAL_Concatenate_Initializations(list(H, Rest), List -> list(H, NRest))
	 SAL_Concatenate_Initializations(Rest, List -> NRest)

  'rule' SAL_Concatenate_Initializations(nil, List -> List)

------------------------------------------------------------
'action' SAL_Concatenate_Bindings(SAL_BINDINGS,
			SAL_BINDINGS -> SAL_BINDINGS)

  'rule' SAL_Concatenate_Bindings(list(H, Rest), List -> list(H, NRest))
	 SAL_Concatenate_Bindings(Rest, List -> NRest)

  'rule' SAL_Concatenate_Bindings(nil, List -> List)
------------------------------------------------------------
'action' SAL_Concatenate_Transitions(SAL_TRANSITIONS, SAL_TRANSITIONS -> SAL_TRANSITIONS)

  'rule' SAL_Concatenate_Transitions(list(T1, Rest), List -> list(T1, NRest))
	 SAL_Concatenate_Transitions(Rest, List -> NRest)

  'rule' SAL_Concatenate_Transitions(nil, List -> List)
------------------------------------------------------------
'action' Remove_duplicates_from_Vids(SAL_VALUE_IDS -> SAL_VALUE_IDS)

  'rule' Remove_duplicates_from_Vids(list(Vid, Vids) -> Result)
	 Remove_duplicates_from_Vids(Vids -> Result1)
	 (|
	    Vid_included_in_Vids(Vid, Vids)
	    where(Result1 -> Result)
	 ||
	    where(SAL_VALUE_IDS'list(Vid,Vids) -> Result)
	 |)

  'rule' Remove_duplicates_from_Vids(nil -> nil)

'condition' Vid_included_in_Vids(SAL_value_id, SAL_VALUE_IDS)

  'rule' Vid_included_in_Vids(Vid, list(Vid1, Vids))
	 (|
	     eq(Vid,Vid1)
	 ||
	     Vid_included_in_Vids(Vid, Vids)
	 |)

------------------------------------------------------------

'action' Remove_duplicates_from_Tids(SAL_TYPE_IDS -> SAL_TYPE_IDS)

  'rule' Remove_duplicates_from_Tids(list(Tid, Tids) -> Result)
	 Remove_duplicates_from_Tids(Tids -> Result1)
	 (|
	    Tid_included_in_Tids(Tid, Tids)
	    where(Result1 -> Result)
	 ||
	    where(SAL_TYPE_IDS'list(Tid,Tids) -> Result)
	 |)

  'rule' Remove_duplicates_from_Tids(nil -> nil)

'condition' Tid_included_in_Tids(SAL_type_id, SAL_TYPE_IDS)

  'rule' Tid_included_in_Tids(Tid, list(Tid1, Tids))
	 (|
	     eq(Tid,Tid1)
	 ||
	     Tid_included_in_Tids(Tid, Tids)
	 |)
------------------------------------------------------------

'action' Remove_reconstructors(SAL_VALUE_IDS -> SAL_VALUE_IDS)

  'rule' Remove_reconstructors(list(Vid, Vids) -> Res):
	 Remove_reconstructors(Vids -> Res1)
	 (|
	   Vid'VType -> reconstructor_value
	   where(Res1 -> Res)	   
	 ||
	   where(SAL_VALUE_IDS'list(Vid, Res1) -> Res)
	 |)

  'rule' Remove_reconstructors(nil -> nil):

---------------------------------------------------

'action' SAL_Concatenate_Context_Args(SAL_VALUE_IDS, SAL_VALUE_IDS -> SAL_VALUE_IDS)

  'rule' SAL_Concatenate_Context_Args(List1, list(H,T) -> Result):
	 SAL_Concatenate_Context_Args(List1, T -> Result1)
	 where(SAL_VALUE_IDS'list(H, Result1) -> Result)

  'rule' SAL_Concatenate_Context_Args(List1, nil -> List1)
--------------------------------------------------
'action' SAL_Extract_Args_from_Tids(SAL_TYPE_IDS -> SAL_VALUE_IDS)

  'rule' SAL_Extract_Args_from_Tids(list(Tid, Rest) -> Result):
	 SAL_Extract_Args_from_Tids(Rest -> Result1)
	 Tid'Args -> Args
	 SAL_Concatenate_Context_Args(Args, Result1 -> Result)

  'rule' SAL_Extract_Args_from_Tids(nil -> nil)
---------------------------------------------------

'action' SAL_Remove_Duplicated_Args(SAL_CONTEXT_ARGS -> SAL_CONTEXT_ARGS)

  'rule' SAL_Remove_Duplicated_Args(list(Current, Rest) -> Result)
	 SAL_Remove_Duplicated_Args(Rest -> Result1)
	 (|
	    SAL_Search_Arg(Current, Rest)
	    where(Result1 -> Result)
	 ||
	    where(SAL_CONTEXT_ARGS'list(Current, Result1) -> Result)
	 |)

  'rule' SAL_Remove_Duplicated_Args(nil -> nil)

'condition' SAL_Search_Arg(SAL_CONTEXT_ARG, SAL_CONTEXT_ARGS)

  'rule' SAL_Search_Arg(Arg, list(Arg1, Tail))
	 eq(Arg, Arg1)

  'rule' SAL_Search_Arg(Arg, list(Arg1, Tail)):
	 ne(Arg, Arg1)
	 SAL_Search_Arg(Arg, Tail)

------------------------------------------------------------------
'action' Collect_Tids_in_Cid(SAL_CONTEXT_CONSTANTS, SAL_context_id)

  'rule' Collect_Tids_in_Cid(list(H,T), Cid)
	 where(H -> sal_type_decl(_,Tid,_))
	 Extend_Static_in_Cid_Decl(Cid, H)
	 Collect_Tids_in_Cid(T, Cid)

  'rule' Collect_Tids_in_Cid(list(_,T), Cid)
	 Collect_Tids_in_Cid(T, Cid)


  'rule' Collect_Tids_in_Cid(nil,_)

------------------------------------------------------------------
'action' SAL_Split_Constants(SAL_CONTEXT_CONSTANTS ->
	   SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Split_Constants(list(H,T) -> list(H,Static), State)
	 (|
	    where(H -> sal_type_decl(_,_,_))
	 ||
	    where(H -> sal_object_decl(_,_,_,_,_))
	 ||
	    where(H -> assertion_decl(_,_,_,_))
	 ||
	    where(H -> module_decl(_,_,_,_,_,_))
	 ||
	    where(H -> sal_const_decl(Decl))
	    (|
	       where(Decl -> sal_nodef(_,_,_))
	    ||
	       where(Decl -> sal_expl_const(_,_,_,_))
	    ||
	       where(Decl -> sal_param_decl(_,_))
	    |)
	 |)
	 SAL_Split_Constants(T -> Static, State)

   'rule' SAL_Split_Constants(list(H,T) -> Static, list(H,State))
	  SAL_Split_Constants(T -> Static, State)
	  
   'rule' SAL_Split_Constants(nil -> nil, nil)

------------------------------------------------------------------

'action' Update_Reference_Information(SAL_context_id, SAL_CONTEXT_CONSTANTS)

  'rule' Update_Reference_Information(Cid, list(H, T))
	 Update_Reference_Information(Cid, T)
	 Update_References_in_Decl(H, Cid)

  'rule' Update_Reference_Information(_, nil)

'action' Update_References_in_Decl(SAL_CONTEXT_CONSTANT, SAL_context_id)

  'rule' Update_References_in_Decl(sal_type_decl(_,Tid,Expr),Cid):
	 Update_Cid_in_Tid(Tid,Cid)
--	 Extend_Decl_Cid_in_Tid(Tid,Cid)
	 Update_Possible_Vids_in_type(Expr, Cid)

  'rule' Update_References_in_Decl(sal_const_decl(Decl),Cid):

            (|
                where(Decl -> sal_expl_const(_,Vid,_,_))
            ||
	        where(Decl -> sal_fun_const(_,Vid,_,_,_,_,_,_))
            |)	  
	    Update_Cid_in_Vid(Vid,Cid)
--	    Extend_Decl_Cid_in_Vid(Vid,Cid)
	    -- There is no need to analyze internal expressions because,
	    -- if they involve another Vid or Cid, its declaration should be
	    -- included in the fixed point.


  'rule' Update_References_in_Decl(D, Cid)
	 -- Ignoring the rest...


------------------------------------------------------------------------
-- Update_Possible_Vids_in_type(TElem, Cid1)
------------------------------------------------------------------------
-- This function updates the Cid field in the values that can appear
-- within a type declaration.
-- Cases contamplated so far:
-- * RECORDS: the fields may be used as functions (destructors for being
--            more precise) that must have the proper
--	      qualification. As the type is being moved, the
--	      information for this values must also be updated.
-- * VARIANTS:
--	* Constructors (including the destructors and reconstructors inside)
--        (except that reconstructors in the non-cc version are not updated)
-- added by CWG 11/7/06
-- * SCALAR TYPES:
--      just variants with all variants constants
------------------------------------------------------------------------

'action' Update_Possible_Vids_in_type(SAL_TYPE_EXPR, SAL_context_id)

  'rule' Update_Possible_Vids_in_type(
            user_defined(sal_record_type(Fields)),  Cid):
--	 Update_Fields_Cid_info(Fields, Cid)
	 Update_Data_Parts_Cid_info(Fields, Cid)

  'rule' Update_Possible_Vids_in_type(
            user_defined(sal_variant_type(FieldsParts)), Cid)
	 Update_Data_Parts_Cid_info(FieldsParts, Cid)

  'rule' Update_Possible_Vids_in_type(
	    user_defined(sal_scalar_type(Vids)), Cid):
	 Update_Vids_Cid_info(Vids, Cid)

  'rule' Update_Possible_Vids_in_type(_,_)

'action' Update_Fields_Cid_info(SAL_FIELD_DECLS, SAL_context_id)

  'rule' Update_Fields_Cid_info(list(field(_,Vid,_), Rest), Cid)
	 where(cid(Cid) -> OptCid)
	 Vid'Cid <- OptCid
	 Update_Fields_Cid_info(Rest, Cid)

  'rule' Update_Fields_Cid_info(nil, _)


'action' Update_Data_Parts_Cid_info(SAL_DATA_TYPE_PARTS, SAL_context_id)

  'rule' Update_Data_Parts_Cid_info(list(sal_part(Constructor,_), Rest), Cid)
	 where(Constructor -> sal_construc(_,Vid, Destructors, Reconstructors))
	 where(cid(Cid) -> OptCid)
	 Update_Cid_in_Vid(Vid, Cid)
	 Update_Destructors_Cid_info(Destructors, Cid)
	 -- reconstructors in non-cc versions are not updated
	 [|
	   SAL_TYPES_Cid -> TYPES_Cid
	   ne(TYPES_Cid, Cid)
	   Update_Reconstructors_Cid_info(Reconstructors, Cid)
	 |]
	 Update_Data_Parts_Cid_info(Rest, Cid)

  'rule' Update_Data_Parts_Cid_info(nil, _)


'action' Update_Destructors_Cid_info(SAL_DESTRUCTORS, SAL_context_id)

  'rule' Update_Destructors_Cid_info(
	   list(sal_destructor(_,Vid,_,_), Rest), Cid)
	 where(cid(Cid) -> OptCid)
	 Update_Cid_in_Vid(Vid, Cid)
	 Update_Destructors_Cid_info(Rest, Cid)

  'rule' Update_Destructors_Cid_info(nil,_)


'action' Update_Reconstructors_Cid_info(SAL_RECONSTRUCTORS, SAL_context_id)

  'rule' Update_Reconstructors_Cid_info(
	   list(sal_reconstructor(_,Vid,_,_,_), Rest), Cid)
	 where(cid(Cid) -> OptCid)
	 Update_Cid_in_Vid(Vid, Cid)
	 Update_Reconstructors_Cid_info(Rest, Cid)

  'rule' Update_Reconstructors_Cid_info(nil,_)

'action' Update_Vids_Cid_info(SAL_VALUE_IDS, SAL_context_id)

  'rule' Update_Vids_Cid_info(list(Vid, Vids), Cid):
	 where(cid(Cid) -> OptCid)
--Putmsg("Vid: ")
--print(Vid)
--SAL_Print_Vid(Vid)
--Putmsg(" moved to ")
--SAL_Print_Cid(Cid)
--Putnl()
	 Vid'Cid <- OptCid
	 Update_Vids_Cid_info(Vids, Cid)

  'rule' Update_Vids_Cid_info(nil, _):

---------------------------------------------------------------
'condition' SAL_Check_Cid_in_Cids(SAL_context_id, SAL_CONTEXT_IDS)
						  
  'rule' SAL_Check_Cid_in_Cids(Cid, list(Cid1, Rest))
	 (|
	    eq(Cid,Cid1)
	 ||
	    SAL_Check_Cid_in_Cids(Cid, Rest)
	 |)
----------------------------------------------------------------
'action' SAL_Remove_Duplicates_from_Fixed_Point(
	   SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Remove_Duplicates_from_Fixed_Point(list(H,T) -> list(H,Result))
	 SAL_Remove_Copies_of_Decl(H, T -> NewTail)
	 SAL_Remove_Duplicates_from_Fixed_Point(NewTail -> Result)

  'rule' SAL_Remove_Duplicates_from_Fixed_Point(nil -> nil)

'action' SAL_Remove_Copies_of_Decl(SAL_CONTEXT_CONSTANT,
	   SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Remove_Copies_of_Decl(sal_type_decl(P,Tid,Type),
		list(sal_type_decl(Pos,Tid1,Type1), Rest) -> Result)
	 SAL_Remove_Copies_of_Decl(sal_type_decl(P,Tid,Type),Rest -> Result1)
         (|
	    eq(Tid,Tid1)
	    where(Result1 -> Result)
	 ||
	    where(SAL_CONTEXT_CONSTANTS'
	      list(sal_type_decl(Pos,Tid1,Type1), Result1) -> Result)
	 |)

  'rule' SAL_Remove_Copies_of_Decl(sal_const_decl(Decl1),
		list(sal_const_decl(Decl2), Rest) -> Result)
	 SAL_Remove_Copies_of_Decl(sal_const_decl(Decl1) ,Rest -> Result1)
	 (|
	    (|
	       where(Decl1 -> sal_expl_const(_,Vid1,_,_))
	       where(Decl2 -> sal_expl_const(_,Vid2,_,_))
	    ||
	       where(Decl1 -> sal_fun_const(_,Vid1, _,_,_,_,_,_))
	       where(Decl2 -> sal_fun_const(_,Vid2, _,_,_,_,_,_))
	    |)
	    eq(Vid1,Vid2)
	    where(Result1 -> Result)
	 ||
	    where(SAL_CONTEXT_CONSTANTS'
	      list(sal_const_decl(Decl2), Result1) -> Result)
	 |)
  
  'rule' SAL_Remove_Copies_of_Decl(D, list(H,T) -> Result)
	 SAL_Remove_Copies_of_Decl(D , T -> Result1)
	 where(SAL_CONTEXT_CONSTANTS'list(H, Result1) -> Result)

  'rule' SAL_Remove_Copies_of_Decl(_, nil -> nil)
----------------------------------------------------------------------------
'action' SAL_Remove_SAL_TYPES(SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Remove_SAL_TYPES(CCS -> CCS1):
  	 SAL_TYPES_Constants -> Removes
	 SAL_Remove_SAL_TYPES1(Removes, CCS -> CCS1)

'action' SAL_Remove_SAL_TYPES1(SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)
	 
  'rule' SAL_Remove_SAL_TYPES1(list(H, T), CCS -> CCS1):
  	 SAL_Remove_Copies_of_Decl(H, CCS -> CCS2)
	 SAL_Remove_SAL_TYPES1(T, CCS2 -> CCS1)

  'rule' SAL_Remove_SAL_TYPES1(nil, CCS -> CCS):
----------------------------------------------------------------------------
'condition' Is_Tid_Included_in_Decls(SAL_type_id, SAL_CONTEXT_CONSTANTS)

  'rule' Is_Tid_Included_in_Decls(Tid, 
	   list(sal_type_decl(_,Tid1,Type1), Rest))
	 (|
	    eq(Tid,Tid1)
	 ||
	    Is_Tid_Included_in_Decls(Tid, Rest)
	 |)
 
   -- If it is not a type declaration, ignore it
  'rule' Is_Tid_Included_in_Decls(Tid, list(_,Rest))
	 Is_Tid_Included_in_Decls(Tid, Rest)
----------------------------------------------------------------------------
'condition' Is_Vid_Included_in_Decls(SAL_value_id, SAL_CONTEXT_CONSTANTS)

  'rule' Is_Vid_Included_in_Decls(Vid, 
	   list(sal_const_decl(Decl2), Rest))
	 (|
	    (|
	       where(Decl2 -> sal_expl_const(_,Vid2,_,_))
	    ||
	       where(Decl2 -> sal_fun_const(_,Vid2, _,_,_,_,_,_))
	    |)
	    eq(Vid,Vid2)
	 ||
	    Is_Vid_Included_in_Decls(Vid, Rest)
	 |)
 
   -- If it is not a value declaration, ignore it
  'rule' Is_Vid_Included_in_Decls(Vid, list(_,Rest))
	 Is_Vid_Included_in_Decls(Vid, Rest)
----------------------------------------------------------------------------
'action' Push_Namespace(BINDING_NAMESPACE)
	 
  'rule' Push_Namespace(NewNS)
	 Current_LBS_Env -> Current
	 where(BINDING_NAMESPACE_STACK'list(NewNS,Current) -> NewCurrent)
	 Current_LBS_Env <- NewCurrent

'action' Pop_Namespace()

  'rule' Pop_Namespace():
	 Current_LBS_Env -> Current
	 where(Current -> list(H, Tail))
	 Current_LBS_Env <- Tail
----------------------------------------------------------------------------
'action' SAL_Remove_First_Brackets_from_Binding(BINDING -> BINDINGS)

  'rule' SAL_Remove_First_Brackets_from_Binding(product(_,BS) -> BS)

  'rule' SAL_Remove_First_Brackets_from_Binding(B -> BINDINGS'list(B,nil))
----------------------------------------------------------------------------

'action' SAL_Gen_Arg_Names_for_Tuple(SAL_ID_OP, 
	   SAL_FORMAL_FUN_PARAMETERS -> SAL_VALUE_EXPRS)

  'rule' SAL_Gen_Arg_Names_for_Tuple(IdOp, Formals -> Exprs)
	 Internal_Gen_Names_for_tuple(1, IdOp, Formals -> Exprs)


'action' Internal_Gen_Names_for_tuple(INT, SAL_ID_OP, 
	  SAL_FORMAL_FUN_PARAMETERS -> SAL_VALUE_EXPRS)

  'rule' Internal_Gen_Names_for_tuple(Index, IdOp,  
	   list(formal_param(_,TE1,_), Rest1) -> list(Current, Result1))
	 DefaultPos(->P)
	 where(record_val_id(P,IdOp,Index) -> ValueId)
	 where(sal_value_occ(ValueId,nil) -> Current)
	 Internal_Gen_Names_for_tuple(Index+1, IdOp, Rest1 ->  Result1)

  'rule' Internal_Gen_Names_for_tuple(_,_,Formals -> nil)

----------------------------------------------------------------------------

'action' SAL_Concatenate_Value_Exprs(SAL_VALUE_EXPRS, SAL_VALUE_EXPRS
						    -> SAL_VALUE_EXPRS)

  'rule' SAL_Concatenate_Value_Exprs(list(H,T), List -> list(H,  Result))
	 SAL_Concatenate_Value_Exprs(T, List -> Result)

  'rule' SAL_Concatenate_Value_Exprs(nil, List -> List)
----------------------------------------------------------------------------
'action' SAL_Gen_Int_Context_and_Tid

  'rule' SAL_Gen_Int_Context_and_Tid
	 string_to_id("IT_AN" -> IntId1)
	 New_SAL_single_context_id(IntId1, 2 -> Cid)

	 -- updating the Cid info with the SAL_TYPES_cc cid:
	 SAL_TYPES_Cid -> TCid
	 TCid'Lifted_Cid -> LTCid
	 Cid'Lifted_Cid <- LTCid

	 DefaultPos(-> BasicPos)
	 IncreaseCol(BasicPos -> P)
	 string_to_id("Int_" -> IntId2)
	 New_SAL_type_id_with_Cid(P, IntId2,Cid, int -> Tid) 
	 string_to_id("DefaultIntLow" -> DLI)
	 string_to_id("DefaultIntHigh" -> DHI)
	 IntLowVal -> DLId
	 IntHighVal -> DHId
	 Generate_Global_Pair_of_Constants(DLI,DLId,DHI,DHId,Tid -> LI_Vid, HI_Vid)

  	 -- Update the arg list:
	 LI_Vid'IdOp -> IdOp1
	 HI_Vid'IdOp -> IdOp2
	 where(IdOp1 -> id(Ide1))
	 where(IdOp2 -> id(Ide2))
	 -- Collecting the arguments in the type:
	 where(SAL_VALUE_IDS'list(LI_Vid,list(HI_Vid,nil)) -> Args)
         Update_Args_in_Tid(Tid, Args)

	 -- Generate the proper information for the operations context:
	 SAL_Gen_Int_Ops_Context(Tid-> OpCid)
	 Tid'OperationsCid <- cid(OpCid)

	 -- Collecting the Tid and Cid:
	 Default_Int_Cid <- Cid
	 Default_Int_Tid <- Tid

	 -- Generate the type declaration in the context:
	 where(sal_esp_value_occ(LI_Vid) -> Low)
	 where(sal_esp_value_occ(HI_Vid) -> High)
	 where(sal_basic(sal_rectricted_integer(Low, High)) -> TExpr)
	 where(sal_type_decl(IntId2, Tid, TExpr) -> Decl)
	 -- Incorporate it in the Cid:
	 Extend_Static_in_Cid_Decl(Cid, Decl)
	 -- Collect the declaration in the Tid:
	 Tid'Declaration <- Decl
	 -- Generate the context declaration:
	 where(context(IntId1, cid(Cid), list(Decl,nil)) -> IntContext)
	 -- Add it to the global collection:
	 Generated_Contexts -> List
	 where(SAL_CONTEXTS'list(IntContext, List) -> NewList)
	 Generated_Contexts <- NewList
	 -- Adding the type expression:
	 Tid'TExpr <- rsl_built_in(integer(Tid))
	 -- cc
	 Tid'Lifted_Tid -> tid(LTid)
	 -- Operation context for the cc version
	 Extend_Nav_Type(P, "Division_by_zero" -> SubtypeNavId)
	 SAL_Gen_Int_CC_Ops_Context(LTid, SubtypeNavId -> OpLCid)
	 LTid'OperationsCid <- cid(OpLCid)

	 -- adding this context in the cc collection too:
	 Generated_CC_Contexts -> List1
	 where(SAL_CONTEXTS'list(IntContext, List1) -> NewList1)
	 Generated_CC_Contexts <- NewList1 

	 -- Generating the RSL_is_Int function:
	 -- EXTRACTING INFO FROM THE RSL version:
	 Id_of_rsl_is_int -> Valueid
	 Valueid'Ident -> FunctionIdOp
	 Valueid'Pos -> FunctionPos
	 -- translating the name:
	 Gen_SAL_Id_Op(FunctionPos, FunctionIdOp, none, none -> SAL_Fun_Id, _)
	 TCid'Lifted_Cid -> cid(CCid)
	 LTid'Ident -> LId
	 LTid'Pos -> LPos
	 New_SAL_value_id(FunctionPos, SAL_Fun_Id, CCid,  user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, LTid)), 
					                                           int)), regular_value -> FVid)
	 
	 -- CREATING THE PARAMETER:
	 string_to_id("Arg_" -> ArgId)
	 where(formal_param(ArgId, user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, LTid)), int)), int) -> FormalParam)
	 FVid'Params <- list(FormalParam, nil)
	 -- CREATING THE BODY:
	 -- Building expr: 'x_ >= Default_Low_Int'
	 LTid'Constructor -> vid(ConstructorVid)
	 where(sal_cc_op(sal_infix_op(ge), LTid) -> GE_Op)
	 where(sal_funct_applic(sal_esp_value_occ(ConstructorVid),sal_argument(SAL_VALUE_EXPRS'list(sal_esp_value_occ(LI_Vid), nil))) -> Lifted_Low_Int)
	 where(sal_esp_prefix_occ(val_id(GE_Op), sal_value_occ(val_id(id(ArgId)), nil), Lifted_Low_Int) -> GE_Expr)
	 -- Building expr: 'x_ <= Default_High_Int'
	 where(sal_cc_op(sal_infix_op(le), LTid) -> LE_Op)
	 where(sal_funct_applic(sal_esp_value_occ(ConstructorVid),sal_argument(SAL_VALUE_EXPRS'list(sal_esp_value_occ(HI_Vid), nil))) -> Lifted_High_Int)
	 where(sal_esp_prefix_occ(val_id(LE_Op), sal_value_occ(val_id(id(ArgId)), nil), Lifted_High_Int) -> LE_Expr)
	 -- Putting all together: 'x_ >= Default_Low_Int' AND 'x_ <= Default_High_Int'
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 LBTid'Ident -> LBId
	 LBTid'Pos -> LBPos
	 -- generate IF A THEN B ELSE FALSE ENDIF instead of A AND B
	 -- add is_true for if condition
	 where(sal_cc_op(sal_function_op(is_true), LBTid) -> Is_true_Op)
	 where(sal_esp_unary_prefix_occ(val_id(Is_true_Op), GE_Expr) -> GE_is_true)
	 Gen_SAL_literal_expr(BasicPos, bool_false, bool -> _, CC_False)
	 where(sal_if_expr(GE_is_true, LE_Expr, nil, else(CC_False)) -> RSL_is_Int_Body)

--	 where(sal_cc_op(sal_infix_op(and), LBTid) -> AND_Op)
--	 where(sal_esp_prefix_occ(val_id(AND_Op), GE_Expr, LE_Expr) -> RSL_is_Int_Body) --AND_Expr
	 
	 -- Generating the declaration:
	 where(sal_const_decl(sal_fun_const(SAL_Fun_Id, FVid, nil, list(FormalParam, nil), 
					    user_defined(sal_cc_type(type_refs(sal_defined(LBPos, LBId, LBTid)), bool)),
					    nil, RSL_is_Int_Body, nil)) -> RSL_is_Int_Decl)

	 FVid'Declaration <- RSL_is_Int_Decl
	 SAL_RSL_is_Int_Vid <- FVid
	 FVid'Lifted_Vid <- FVid
---------------------------------------------------------------------------------
'action' SAL_Gen_Bool_Context_and_Tid

  'rule' SAL_Gen_Bool_Context_and_Tid
	 string_to_id("BT_AN" -> BoolId1)
	 New_SAL_single_context_id(BoolId1, 2 -> Cid)
	 -- updating the Cid info with the SAL_TYPES_cc cid:
	 SAL_TYPES_Cid -> TCid
	 TCid'Lifted_Cid -> LTCid
	 Cid'Lifted_Cid <- LTCid

	 DefaultPos(-> BasicPos)
	 IncreaseCol(BasicPos -> IntPos) -- Reserved for ints...
	 IncreaseCol(IntPos -> P)
	 string_to_id("Bool_" -> BoolId2)
	 New_SAL_type_id_with_Cid(P, BoolId2,Cid, bool -> Tid)

	 -- Generate the proper information for the operations context:
	 SAL_Gen_Bool_Ops_Context(-> OpCid)
	 Tid'OperationsCid <- cid(OpCid)

 	 -- Collecting the Tid and Cid:
	 Default_Bool_Cid <- Cid
	 Default_Bool_Tid <- Tid

	 -- Generate the type declaration in the context:
	 where(sal_basic(sal_boolean) -> TExpr)
	 where(sal_type_decl(BoolId2, Tid, TExpr) -> Decl)
	 -- Incorporate it in the Cid:
	 Extend_Static_in_Cid_Decl(Cid, Decl)
	 -- Collect the declaration in the Tid:
	 Tid'Declaration <- Decl
	 -- Generate the context declaration:
	 where(context(BoolId1, cid(Cid), list(Decl,nil)) -> BoolContext)
	 -- Add it to the global collection:
	 Generated_Contexts -> List
	 where(SAL_CONTEXTS'list(BoolContext, List) -> NewList)
	 Generated_Contexts <- NewList
	 Tid'TExpr <- rsl_built_in(boolean(Tid))

	 -- cc
	 -- adding this context in the cc collection too:
	 Generated_CC_Contexts -> List1
	 where(SAL_CONTEXTS'list(BoolContext, List1) -> NewList1)
	 Generated_CC_Contexts <- NewList1 
	 -- Operation context for the cc version
	 Tid'Lifted_Tid -> tid(LTid)
	 SAL_Gen_Bool_CC_Ops_Context(LTid-> OpLCid)
	 LTid'OperationsCid <- cid(OpLCid)
	 
	 -- adding this context in the cc collection too:
	 Generated_CC_Contexts -> List2
	 where(SAL_CONTEXTS'list(BoolContext, List2) -> NewList2)
	 Generated_CC_Contexts <- NewList2
-----------------------------------------------------------------------
'action' SAL_Gen_Nat_Context_and_Tid

  'rule' SAL_Gen_Nat_Context_and_Tid
	 string_to_id("NT_AN" -> NatId1)
	 New_SAL_single_context_id(NatId1, 2 -> Cid)
	 -- updating the Cid info with the SAL_TYPES_cc cid:
	 SAL_TYPES_Cid -> TCid
	 TCid'Lifted_Cid -> LTCid
	 Cid'Lifted_Cid <- LTCid

	 DefaultPos(-> BasicPos)
	 IncreaseCol(BasicPos -> IntPos)
	 IncreaseCol(IntPos -> BoolPos)
	 IncreaseCol(BoolPos -> P)
	 string_to_id("Nat_" -> NatId2)
	 New_SAL_type_id_with_Cid(P, NatId2,Cid, nat -> Tid)
	 
	 string_to_id("DefaultNatHigh" -> DHN)
	 NatHighVal -> ValId
	 Generate_Global_Constant(DHN, ValId, Tid -> HN_Vid)

  	 -- Update the arg list:
	 HN_Vid'IdOp -> IdOp1
	 where(IdOp1 -> id(Ide1))
	 -- Collecting the arguments in the type:
	 where(SAL_VALUE_IDS'list(HN_Vid,nil) -> Args)
         Update_Args_in_Tid(Tid, Args)

	 -- Collecting the Tid and Cid:
	 Default_Nat_Cid <- Cid
	 Default_Nat_Tid <- Tid

	 -- Generate the type declaration in the context:
	 string_to_id("0" -> Zero)
	 where(sal_literal(integ(Zero)) -> Low)
	 where(sal_esp_value_occ(HN_Vid) -> High)
	 where(sal_basic(sal_rectricted_integer(Low, High)) -> TExpr)
	 where(sal_type_decl(NatId2, Tid, TExpr) -> Decl)
	 -- Incorporate it in the Cid:
	 Extend_Static_in_Cid_Decl(Cid, Decl)
	 -- Collect the declaration in the Tid:
	 Tid'Declaration <- Decl
	 -- Generate the context declaration:
	 where(context(NatId1, cid(Cid), list(Decl,nil)) -> NatContext)
	 -- Add it to the global collection:
	 Generated_Contexts -> List
	 where(SAL_CONTEXTS'list(NatContext, List) -> NewList)
	 Generated_Contexts <- NewList
	 Tid'TExpr <- rsl_built_in(natural(Tid))
	 -- cc
	 Tid'Lifted_Tid -> tid(LTid)
	 LTid'OperationsCid <- nil

	 -- adding this context in the cc collection too:
	 Generated_CC_Contexts -> List1
	 where(SAL_CONTEXTS'list(NatContext, List1) -> NewList1)
	 Generated_CC_Contexts <- NewList1 

	 -- Generating the RSL_is_Nat function:
	 -- EXTRACTING INFO FROM THE RSL version:
	 Id_of_rsl_is_nat -> Valueid
	 Valueid'Ident -> FunctionIdOp
	 Valueid'Pos -> FunctionPos
	 -- translating the name:
	 Gen_SAL_Id_Op(FunctionPos, FunctionIdOp, none, none -> SAL_Fun_Id, _)
	 TCid'Lifted_Cid -> cid(CCid)
	 Default_Int_Tid -> IntTid
	 IntTid'Lifted_Tid -> tid(LITid)
	 LITid'Ident -> LId
	 LITid'Pos -> LPos
	 New_SAL_value_id(FunctionPos, SAL_Fun_Id, CCid,  user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, LITid)), 
					                                           int)), regular_value -> FVid)
	 
	 -- CREATING THE PARAMETER:
	 string_to_id("Arg_" -> ArgId)
	 where(formal_param(ArgId, user_defined(sal_cc_type(type_refs(sal_defined(LPos, LId, LITid)), int)), int) -> FormalParam)
	 FVid'Params <- list(FormalParam, nil)
	 -- CREATING THE BODY:
	 -- Building expr: 'x_ >= Default_Low_Nat'
	 LITid'Constructor -> vid(ConstructorVid)
	 where(sal_cc_op(sal_infix_op(ge), LITid) -> GE_Op)
	 where(sal_funct_applic(sal_esp_value_occ(ConstructorVid),sal_argument(SAL_VALUE_EXPRS'list(Low, nil))) -> Lifted_Low_Nat)
	 where(sal_esp_prefix_occ(val_id(GE_Op), sal_value_occ(val_id(id(ArgId)), nil), Lifted_Low_Nat) -> GE_Expr)
	 -- Building expr: 'x_ <= Default_High_Nat'
	 where(sal_cc_op(sal_infix_op(le), LITid) -> LE_Op)
	 where(sal_funct_applic(sal_esp_value_occ(ConstructorVid),sal_argument(SAL_VALUE_EXPRS'list(High, nil))) -> Lifted_High_Nat)
	 where(sal_esp_prefix_occ(val_id(LE_Op), sal_value_occ(val_id(id(ArgId)), nil), Lifted_High_Nat) -> LE_Expr)
	 -- Putting all together: 'x_ >= Default_Low_Nat' AND 'x_ <= Default_High_Nat'
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 LBTid'Ident -> LBId
	 LBTid'Pos -> LBPos
	 -- generate IF A THEN B ELSE FALSE ENDIF instead of A AND B
	 -- add is_true for if condition
	 where(sal_cc_op(sal_function_op(is_true), LBTid) -> Is_true_Op)
	 where(sal_esp_unary_prefix_occ(val_id(Is_true_Op), GE_Expr) -> GE_is_true)
	 Gen_SAL_literal_expr(BasicPos, bool_false, bool -> _, CC_False)
	 where(sal_if_expr(GE_is_true, LE_Expr, nil, else(CC_False)) -> RSL_is_Nat_Body)

--	 where(sal_cc_op(sal_infix_op(and), LBTid) -> AND_Op)
--	 where(sal_esp_prefix_occ(val_id(AND_Op), GE_Expr, LE_Expr) -> RSL_is_Nat_Body) --AND_Expr
	 
	 -- Generating the declaration:
	 where(sal_const_decl(sal_fun_const(SAL_Fun_Id, FVid, nil, list(FormalParam, nil), 
					    user_defined(sal_cc_type(type_refs(sal_defined(LBPos, LBId, LBTid)), bool)),
					    nil, RSL_is_Nat_Body, nil)) -> RSL_is_Nat_Decl)

	 FVid'Declaration <- RSL_is_Nat_Decl
	 SAL_RSL_is_Nat_Vid <- FVid
	 FVid'Lifted_Vid <- FVid

--------------------------------------------------------------------
'action' SAL_Check_Defined_List(POS, TYPE_EXPR -> OPT_SAL_TYPE_ID)

  'rule' SAL_Check_Defined_List(Pos, TExpr -> OptCid)
	 Current_List_Types -> ListTypes
	 SAL_Internal_Check_Defined_List(Pos, TExpr, ListTypes -> OptCid)

'action' SAL_Internal_Check_Defined_List(POS, TYPE_EXPR, SAL_LIST_TYPES -> OPT_SAL_TYPE_ID)

  'rule' SAL_Internal_Check_Defined_List(Pos, TExpr, list(list_type(TExpr1, Tid), Rest) -> OptTid)
	 (|
	     SAL_Match_Type(Pos, TExpr,TExpr1,no)
--	     Match(TExpr,nil,TExpr1)
	     where(tid(Tid) -> OptTid)
	 ||
	     SAL_Internal_Check_Defined_List(Pos, TExpr, Rest -> OptTid)
	 |)

  'rule' SAL_Internal_Check_Defined_List(_, _, nil -> nil)

'action' SAL_Gen_New_List_Type(IDENT, TYPE_EXPR -> SAL_type_id)

  'rule' SAL_Gen_New_List_Type(ListTypeId, TExpr -> Tid)
	 -- Generate a new Cid:
	 id_to_string(ListTypeId -> IdStr)
	 Concatenate(IdStr, "list" -> ListIdStr)
	 string_to_id(ListIdStr -> ListId)
	 where(OPT_CONTEXT_ID'nil -> Cid)
	 
	 DefaultPos(->P)
	 New_SAL_type_id(P, ListId, fin_list(TExpr) -> Tid)

	 -- Generate the proper information for the operations context:
-- Put something more complex here...
--	 SAL_Gen_List_Ops_Context(-> OpCid)
--	 Tid'OperationsCid <- cid(OpCid)

	 -- Collecting the Tid:
	 where(list_type(TExpr, Tid) -> ListInfo)
	 Current_List_Types -> ListTypes
	 where(SAL_LIST_TYPES'list(ListInfo, ListTypes) -> NewListTypes)
	 Current_List_Types <- NewListTypes

	 -- Generate the global constant for the length of the new list:
	 Concatenate(IdStr, "_list_length" -> LLStr)
	 string_to_id(LLStr -> LLIdent)
	 string_to_id("4" -> LenId)
	 Generate_Global_Constant(LLIdent,LenId,Tid -> Vid)

     -- Generate the DOMAIN of the list declaration (numeric)
	 string_to_id("1" -> ValOneId)
	 where(sal_literal(integ(ValOneId)) -> LowVal)
	 where(sal_esp_value_occ(Vid) -> HighVal)
	 string_to_id("Default_List_Dom" -> ListDomId)
		 
	 New_SAL_type_id(P, ListDomId, int -> DomTid)
	 where(sal_basic(sal_rectricted_integer(LowVal, HighVal)) -> DomTE)
	 DomTid'TExpr <- DomTE
	 -- Generate the declaration:
	 where(sal_type_decl(ListDomId, DomTid, DomTE) -> DomDecl)
	 -- Update the declaration in the tid:
	 DomTid'Declaration <- DomDecl

     -- Range type and declaration generation:
	 New_SAL_type_id(P, ListTypeId, any -> RangeTid)
	 SAL_Gen_Type_Expr(P, TExpr -> SALRangeType, _)
	 RangeTid'TExpr <- SALRangeType
	 -- Generate de declaration:
	 where(sal_type_decl(ListTypeId, RangeTid, SALRangeType) -> RangeDecl)
	 -- Update the declaration infomation in the tid:
	 RangeTid'Declaration <- RangeDecl

     -- List declaration:
	 where(type_refs(sal_defined(P,ListTypeId,RangeTid)) -> Range)
	 -- Generate the type reference for the domain (DOM)
	 where(type_refs(sal_defined(P,ListDomId,DomTid)) -> Domain)
	 -- Generate the mapping that implements the list:
	 -- List_ : TYPE = [Dom -> Range];
	 where(sal_basic(sal_total_function(Domain, Range)) -> TE2)
	 where(sal_type_decl(ListId, Tid, TE2) -> Decl)
	 -- Collect the declaration in the Tid:
	 Tid'Declaration <- Decl
	 Tid'TExpr <- rsl_built_in(sal_list_type(Tid, Range))

	 -- Generate the Cid for the operations of this list:
	 Concatenate(ListIdStr, "OPS" -> OperationsIdentStr)
	 SAL_Gen_Collections_Ops_Context(OperationsIdentStr,TE2,Tid -> OpCid)
	 -- Update the reference in the Tid:
	 Tid'OperationsCid <- cid(OpCid)
-----------------------------------------------------------------------------------------------
'action' SAL_Check_Defined_Set(POS, TYPE_EXPR -> OPT_SAL_TYPE_ID)

  'rule' SAL_Check_Defined_Set(Pos, TExpr -> OptTid)
	 Current_Set_Types -> SetTypes
	 SAL_Internal_Check_Defined_Set(Pos, TExpr, SetTypes -> OptTid)

'action' SAL_Internal_Check_Defined_Set(POS,  TYPE_EXPR, SAL_LIST_TYPES -> OPT_SAL_TYPE_ID)

  'rule' SAL_Internal_Check_Defined_Set(Pos, TExpr, list(list_type(TExpr1, Tid), Rest) -> OptTid)
	 (|
	     SAL_Match_Type(Pos, TExpr, TExpr1,no)
	     where(tid(Tid) -> OptTid)
	 ||
	     SAL_Internal_Check_Defined_Set(Pos, TExpr, Rest -> OptTid)
	 |)

 'rule' SAL_Internal_Check_Defined_Set(_,_, nil -> nil)

'action' SAL_Check_Defined_Maximal_Set(POS, TYPE_EXPR -> OPT_SAL_TYPE_ID)

  'rule' SAL_Check_Defined_Maximal_Set(Pos, TExpr -> OptTid)
	 Current_Set_Types -> SetTypes
	 SAL_Internal_Check_Defined_Maximal_Set(Pos, TExpr, SetTypes -> OptTid)

'action' SAL_Internal_Check_Defined_Maximal_Set(POS,  TYPE_EXPR, SAL_LIST_TYPES -> OPT_SAL_TYPE_ID)

  'rule' SAL_Internal_Check_Defined_Maximal_Set(Pos, TExpr, list(list_type(TExpr1, Tid), Rest) -> OptTid)
	 (|
	     Match(TExpr,nil,TExpr1)
	     where(tid(Tid) -> OptTid)
	 ||
	     SAL_Internal_Check_Defined_Maximal_Set(Pos, TExpr, Rest -> OptTid)
	 |)

  'rule' SAL_Internal_Check_Defined_Maximal_Set(_,_, nil -> nil)

----------------------

'action' SAL_Gen_New_Set_Type(POS, IDENT, TYPE_EXPR -> SAL_type_id)

  'rule' SAL_Gen_New_Set_Type(Pos, SetTypeId, TExpr -> Tid)
	 -- Generate a new Cid:
	 id_to_string(SetTypeId -> IdStr)
	 Concatenate(IdStr, "_set" -> SetIdStr)
	 string_to_id(SetIdStr -> SetId)
	 SAL_TYPES_Cid -> Cid
	 
	 New_SAL_type_id_with_Cid(Pos, SetId,Cid, fin_set(TExpr) -> Tid)
	 SAL_Find_Tid(TExpr -> DomTid)

     -- Set declaration:
	 SAL_Gen_Type_Expr(Pos, TExpr -> Domain, LiftedDomain)
	 SAL_Gen_Type_Expr(Pos, bool -> Range, LiftedRange)
/*
	 Default_Bool_Tid -> BoolTid
	 BoolTid'Ident -> BoolId
	 where(type_refs(sal_defined(Pos,BoolId,BoolTid)) -> Range)
	 -- Generate the type reference for the domain (DOM)
	 where(type_refs(sal_defined(Pos,SetTypeId,DomTid)) -> Domain)
*/
	 -- Generate the mapping that implements the set:
	 -- Set : TYPE = [Dom -> Boolean];
	 where(sal_basic(sal_total_function(Domain, Range)) -> TE2)
	 where(sal_type_decl(SetId, Tid, TE2) -> Decl)
	 -- Collect the declaration in the Tid:
	 Tid'Declaration <- Decl
	 Tid'TExpr <- rsl_built_in(sal_finite_set(Tid, Domain))

	 SAL_Types_Extra_Defs -> Defs
	 where(SAL_CONTEXT_CONSTANTS'list(Decl, nil) -> New)
	 SAL_Concatenate_Context_Constants(Defs, New -> NewDefs)
	 SAL_Types_Extra_Defs <- NewDefs

	 -- Generate the Cid for the operations of this set:
	 SAL_Gen_Set_Ops_Context(SetIdStr,TE2,Tid -> OpCid)
	 -- Update the reference in the Tid:
	 Tid'OperationsCid <- cid(OpCid)
	 -- unless the set element type is maximal we need to create a
	 -- set type with maximal element type, as the lifted version
	 -- of this maximal set is the appropriate type for the lifting of
	 -- the current set
	 (|
	   --Maximal(TExpr) -- We do not want to use the maximal set
	   -- eq(1,0)
	   -- the set type is already maximal; no need to generate a
	   -- new one

	   -- Collecting the new set in the CC collection:
	   add_tid_to_lifted_global(Tid)
	   Tid'Lifted_Tid -> tid(LTid)

	   -- Updating the operations cid:
	   Concatenate(SetIdStr, "_cc" -> NewSetIdStr)
	   SAL_Gen_Set_CC_Ops_Context(NewSetIdStr,Domain,LiftedDomain,LTid -> CC_Cid)
	   CC_Cid'Lifted_Cid -> OpLCid
	   LTid'OperationsCid <- OpLCid
	 ||
	   SAL_Gen_New_Set_Maximal_Type(Pos, TExpr -> LTid)
	   Tid'Lifted_Tid <- tid(LTid)
           
	   LTid'OperationsCid -> OpLCid
	 |)
	 OpCid'Lifted_Cid <- OpLCid
	 -- Collecting the Tid: (doing this at the end, otherwise, the detection for the lifted set will always find itself)
	 where(list_type(TExpr, Tid) -> SetInfo)
	 Current_Set_Types -> SetTypes
	 where(SAL_LIST_TYPES'list(SetInfo, SetTypes) -> NewSetTypes)
	 Current_Set_Types <- NewSetTypes
--print(NewTid)


'action' SAL_Gen_New_Set_Maximal_Type(POS, TYPE_EXPR -> SAL_type_id)

  'rule' SAL_Gen_New_Set_Maximal_Type(Pos, TExpr -> LTid)
	 -- cc
	 SAL_Check_Defined_Maximal_Set(Pos, TExpr -> OptMaxTid)
	 (|
	     -- there exists another set that maximally matches this one...
	     where(OptMaxTid -> tid(MaxTid))
	     MaxTid'Lifted_Tid -> tid(LTid)
	     -- The lifted version of the current set is the lifted set of the
	     -- one that matches this set:

	 ||
	     -- This is the first set of this type
	     -- changed cwg to use non-lifted maximal type for set
	     -- predicate domain and range
	     Maxtype(TExpr -> MaxTExpr)
 	     SAL_Gen_Type_Expr(Pos, MaxTExpr -> Domain, LiftedDomain)
	     SAL_Gen_Ident_From_Type(Domain -> SetDomId)
	     id_to_string(SetDomId -> Str)
	     Concatenate(Str, "_set" -> Str1)
	     string_to_id(Str1 -> DomId)

	     -- a whole new Tid is created here...
	     -- This is done in this way because due to the maximal type usage,
	     -- this type DOES NOT MATCH the type used in the non-cc version...
	     -- For an example, consider the TE:
	     --   Ship = {| Int |},
	     --   ShipSet = Ship-set
	     -- In the non-cc version, the Tid associated with ShipSet referrs to Ship and
	     -- this is not correct in the cc-version (by maximality, it should refer to Int_)
	     -- In particular, the cc-version should work on a Tid called 'Int__set' ([Int -> Bool]) 
	     -- as base type for the lifted set 'Int__set_cc' defined as:
	     -- Int__set_cc : DATATYPE =
	     --     Int__set_cc(Int__set_val: Int__set)
	     --	    Int__set_nav(Int__set_nav_val : Not_a_value_type)
	     -- END;
	     SAL_Current_CC_Cid -> CCid
	     New_SAL_type_id_with_Cid(Pos, DomId, CCid, fin_set(MaxTExpr) -> BaseSetTid)
--	     BaseSetTid'Lifted_Tid -> tid(LBaseSetTid)
	     -- Building the cc version of the base set (maximal, NON-LIFTED set for the original set)
	     -- Generate the mapping that implements the set:
	     -- Set : TYPE = [Dom -> Bool];
	     SAL_Gen_Type_Expr(Pos, bool -> Range, LiftedRange)
	     where(sal_basic(sal_total_function(Domain, Range)) -> CC_BaseSet)
	     where(sal_type_decl(DomId, BaseSetTid, CC_BaseSet) -> CC_BaseDecl)
	     -- Collect the declaration in the Tid:
	     BaseSetTid'Declaration <- CC_BaseDecl
	     BaseSetTid'Lifted_Tid -> tid(LTid)
	     LTid'Ident -> LId
	     BaseSetTid'TExpr <- user_defined(sal_cc_type(type_refs(sal_defined(Pos, LId, LTid)), 
			                                   fin_set(TExpr)))
	     -- The original set type has a lifted type that is the lifted Tid recently created 
	     -- Collecting the new set in the CC collection:
	     add_tid_to_lifted_global(BaseSetTid)
	     Add_Lifted_to_Global(fin_set(MaxTExpr), LTid)
	     -- Updating the operations cid:
	     id_to_string(DomId -> DomIdStr)
	     Concatenate(DomIdStr, "_cc" -> NewSetIdStr)
	     SAL_Gen_Set_CC_Ops_Context(NewSetIdStr,Domain,LiftedDomain,LTid -> OpLCid)
	     BaseSetTid'OperationsCid <- cid(OpLCid)
	     OpLCid'Lifted_Cid -> LOpCid
	     LTid'OperationsCid <- LOpCid
	 |)



-----------------------------------------------------------------------------------------------
'action' SAL_Check_Defined_Map(POS, TYPE_EXPR, TYPE_EXPR -> OPT_SAL_TYPE_ID)

  'rule' SAL_Check_Defined_Map(Pos, D,R -> OptCid)
	 Current_Map_Types -> MapTypes
	 SAL_Internal_Check_Defined_Map(Pos, D,R, MapTypes -> OptCid)

'action' SAL_Internal_Check_Defined_Map(POS,TYPE_EXPR, TYPE_EXPR, SAL_LIST_TYPES -> OPT_SAL_TYPE_ID)

  'rule' SAL_Internal_Check_Defined_Map(Pos, D,R, list(map_type(TExpr1, TExpr2, Tid), Rest) -> OptTid)
	 (|
-- cwg.  Revert to using maximal types
	     SAL_Match_Type(Pos, D,TExpr1,no)
	     SAL_Match_Type(Pos, R,TExpr2,no)
--	     Match(D,nil,TExpr1)
--	     Match(R,nil,TExpr2)
	     where(tid(Tid) -> OptTid)
	 ||
	     SAL_Internal_Check_Defined_Map(Pos, D,R, Rest -> OptTid)
	 |)

  'rule' SAL_Internal_Check_Defined_Map(_,_,_, nil -> nil)


'action' SAL_Check_Defined_Array(POS, TYPE_EXPR, TYPE_EXPR -> OPT_SAL_TYPE_ID)

  'rule' SAL_Check_Defined_Array(Pos, D,R -> OptCid)
	 Current_Array_Types -> ArrayTypes
	 SAL_Internal_Check_Defined_Array(Pos, D,R, ArrayTypes -> OptCid)

'action' SAL_Internal_Check_Defined_Array(POS,TYPE_EXPR, TYPE_EXPR, SAL_LIST_TYPES -> OPT_SAL_TYPE_ID)

  'rule' SAL_Internal_Check_Defined_Array(Pos, D,R, list(array_type(TExpr1, TExpr2, Tid), Rest) -> OptTid)
	 (|
-- cwg.  Revert to using maximal types
	     SAL_Match_Type(Pos, D,TExpr1,no)
	     SAL_Match_Type(Pos, R,TExpr2,no)
--	     Match(D,nil,TExpr1)
--	     Match(R,nil,TExpr2)
	     where(tid(Tid) -> OptTid)
	 ||
	     SAL_Internal_Check_Defined_Array(Pos, D,R, Rest -> OptTid)
	 |)

  'rule' SAL_Internal_Check_Defined_Array(_,_,_, nil -> nil)



------------------------------

'action' SAL_Gen_New_Map_Type(POS, IDENT, IDENT, TYPE_EXPR, TYPE_EXPR -> SAL_type_id)

  'rule' SAL_Gen_New_Map_Type(Pos, DomTypeId,RngTypeId,D, R -> Tid)
	 -- Generate a new Cid:
	 id_to_string(DomTypeId -> IdStr1)
	 id_to_string(RngTypeId -> IdStr3)
	 Concatenate(IdStr1, "_" -> IdStr2)
	 Concatenate(IdStr2, IdStr3 -> IdStr)
	 Concatenate(IdStr, "_map" -> MapIdStr)
	 string_to_id(MapIdStr -> MapId)	 
	 SAL_TYPES_Cid -> Cid
	 
	 New_SAL_type_id_with_Cid(Pos, MapId,Cid, fin_map(D,R) -> Tid)

	 SAL_Find_Tid(D -> DomTid)
	 SAL_Find_Tid(R -> RngTid)

	 -- Generate the range of the list (datatype)
	 Concatenate(MapIdStr, "_range" -> MapRangeStr)
	 string_to_id(MapRangeStr -> MapRangeId)
	 IncreaseCol(Pos -> Pos1)
	 New_SAL_type_id_with_Cid(Pos1, MapRangeId,Cid, any -> MapRangeTid)
	 -- Generating the type reference to the MapRangeType:
	 where(type_refs(sal_defined(Pos1, MapRangeId, MapRangeTid)) -> MapRangeRef)
	 -- generate the nil part:
	 Concatenate(MapIdStr, "_nil" -> Nil_Str)
	 string_to_id(Nil_Str -> Nil_Cons_id)
	 where(SAL_ID_OP'id(Nil_Cons_id) -> NilIdOp)
	 New_SAL_value_id(Pos, NilIdOp, Cid, MapRangeRef,constructor_value -> NilVid)
	 where(sal_construc(NilIdOp, NilVid, nil,nil) -> Nil_Construct)
	 where(sal_part(Nil_Construct,MapRangeRef) -> NIL_Part)
	 -- generate the Range part:
	 Concatenate(MapIdStr, "_range" -> RangeStr)
	 string_to_id(RangeStr -> Val_Cons_id)
	 where(SAL_ID_OP'id(Val_Cons_id) -> ValIdOp)
	 -- Increasing the pos of this new value...
	 -- Used for lookup...
	 IncreaseCol(Pos1 -> IncPos)
	 New_SAL_value_id(IncPos, ValIdOp, Cid, MapRangeRef,constructor_value -> ValVid)
	 -- generating the destructor:
	 Concatenate(MapIdStr, "_val" -> VAL_str)
	 string_to_id(VAL_str -> Rng_Cons_id)
	 where(SAL_ID_OP'id(Rng_Cons_id) -> RngIdOp)
	 RngTid'Pos -> RPos
	 RngTid'Ident -> RngId
	 where(type_refs(sal_defined(RPos, RngId, RngTid)) -> SALRngType)
         -- Don't use RPos here - causes confusion if RPos is a subtype CWG
         IncreaseCol(IncPos -> IncPos1)
	 New_SAL_value_id(IncPos1, RngIdOp, Cid, SALRngType, regular_value -> RngVid)
	 where(SAL_DESTRUCTORS'list(sal_destructor(RngIdOp,RngVid,SALRngType,none), nil) -> Destrs)
	 --
	 where(sal_construc(ValIdOp, ValVid, Destrs, nil) -> Val_Construct)
	 where(sal_part(Val_Construct,MapRangeRef) -> Val_Part)
	 --
	 where(SAL_DATA_TYPE_PARTS'list(NIL_Part, list(Val_Part, nil)) -> DTParts)
	 where(user_defined(sal_variant_type(DTParts)) -> MapRangeTypeExpr)
	 -- Updating the type info in the Tid:
	 MapRangeTid'TExpr <- MapRangeTypeExpr
	 -- Generate the declaration:
	 where(sal_type_decl(MapRangeId, MapRangeTid, MapRangeTypeExpr) -> RangeDecl)
	 MapRangeTid'Declaration  <- RangeDecl
	 Extend_Static_in_Cid_Decl(Cid, RangeDecl)


     -- Map declaration:
	 where(type_refs(sal_defined(IncPos,MapRangeId,MapRangeTid)) -> Range)
	 -- Generate the type reference for the domain (DOM)
	 where(type_refs(sal_defined(Pos,DomTypeId,DomTid)) -> Domain)
	 -- Generate the mapping that implements the map:
	 -- Map : TYPE = [Domain -> Range];
	 where(sal_basic(sal_total_function(Domain, Range)) -> TE2)
	 where(sal_type_decl(MapId, Tid, TE2) -> Decl)
	 -- Incorporate it in the Cid:
	 Extend_Static_in_Cid_Decl(Cid, Decl)
	 -- Collect the declaration in the Tid:
	 Tid'Declaration <- Decl
	 Tid'TExpr <- rsl_built_in(sal_finite_map(Tid,Domain,Range))

	 SAL_Types_Extra_Defs -> Defs
	 where(SAL_CONTEXT_CONSTANTS'list(RangeDecl, list(Decl, nil)) -> New)
	 SAL_Concatenate_Context_Constants(Defs, New -> NewDefs)
	 SAL_Types_Extra_Defs <- NewDefs

	 -- It is necessary to generate the sets for the dom and rng operations:
	 -- Dom set:

	 SAL_Check_Defined_Set(Pos, D -> DOptTid)
	 (|
	    --There is no set of this type, generate a new one:
	    eq(DOptTid, nil)
	    -- It is necessary to update the pos because the current TID already 
	    -- has this position (the TID of the map). If the positions match, no new
	    -- type_id will be created (the map_tid will be returned instead)
	    IncreaseCol(IncPos -> IncPosII)
--Putmsg("1\n")
--Putmsg(MapIdStr)
--Putnl()
	    SAL_Gen_New_Set_Type(IncPosII,DomTypeId, D -> DomSetTid)
--Putmsg("2\n")
--Putmsg(MapIdStr)
--Putnl()
	    DomSetTid'Cid <- cid(Cid)
	 ||
	    where(IncPos -> IncPosII)
	    where(DOptTid -> tid(DomSetTid))
	 |)

	 
	 -- Rng set:
	 SAL_Check_Defined_Set(Pos, R -> ROptTid)
	 (|
	    --There is no set of this type, generate a new one:
	    eq(ROptTid, nil)
	    IncreaseCol(IncPosII -> IncPosIII)
	    SAL_Gen_New_Set_Type(IncPosIII, RngTypeId, R -> RngSetTid)
	    RngSetTid'Cid <- cid(Cid)
	 ||
	    where(ROptTid -> tid(RngSetTid))
	 |)
	 
	 
	 DomSetTid'OperationsCid -> cid(OpsDomTypeCid)
	 RngSetTid'OperationsCid -> cid(OpsRngTypeCid)

	 -- seems MapIdStr can be corrupted by SAL_Gen_New_Set_Type
	 -- so make it again CWG 12/4/08
	 id_to_string(MapId -> MapIdStr2)
	 -- Generate the Cid for the operations of this map:
	 SAL_Gen_Map_Ops_Context(MapIdStr2,MapRangeTypeExpr,Tid,OpsDomTypeCid, OpsRngTypeCid,DomSetTid ,RngSetTid-> OpCid)
	 -- Update the reference in the Tid:
	 Tid'OperationsCid <- cid(OpCid)

	 -- cc
--Putmsg("Generating a new cc map\n")
	     -- Generating lifted domain and range for the map:
	     SAL_Gen_Type_Expr(Pos, D -> Dom, LDom)
	     SAL_Gen_Type_Expr(Pos, R -> Rng, LRng)


	     Maxtype(D -> MaxD)
	     SAL_Gen_Type_Expr(Pos, MaxD -> MaxDom, _)
	     Maxtype(R -> MaxR)
             SAL_Gen_Type_Expr(Pos, R -> MaxRng, _)

	     Tid'Lifted_Tid -> tid(LMapTid)
	     add_tid_to_lifted_global(Tid)
	     DomSetTid'Lifted_Tid -> tid(LDomSetTid)
	     RngSetTid'Lifted_Tid -> tid(LRngSetTid)
	     where(LDom -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,LDomTid)),_)))
	     where(LRng -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,LRngTid)),_))) 
	     LMapTid'Ident -> LMapId
	     id_to_string(LMapId -> Str5)
	     SAL_Gen_Map_CC_Ops_Context(Str5,LMapTid,LDomTid,LRngTid,LDomSetTid, LRngSetTid, Dom, Rng, MaxDom, MaxRng, MapRangeTid -> LOpCid)
	     LMapTid'OperationsCid <- cid(LOpCid)
	     OpCid'Lifted_Cid <- cid(LOpCid)
--SAL_Print_Tid(LMapTid)
--Putnl()



	 -- Collecting the map AT THE END to avoid its own detection when checking for maximal types
	 -- for the cc-version:
	 where(map_type(D,R , Tid) -> MapInfo)
	 Current_Map_Types -> MapTypes
	 where(SAL_LIST_TYPES'list(MapInfo, MapTypes) -> NewMapTypes)
	 Current_Map_Types <- NewMapTypes


'action' SAL_Gen_New_Array_Type(POS, IDENT, IDENT, TYPE_EXPR, TYPE_EXPR -> SAL_type_id)

  'rule' SAL_Gen_New_Array_Type(Pos, DomTypeId,RngTypeId,D, R -> Tid)
	 -- Generate a new Cid:
	 id_to_string(DomTypeId -> IdStr1)
	 id_to_string(RngTypeId -> IdStr3)
	 Concatenate(IdStr1, "_" -> IdStr2)
	 Concatenate(IdStr2, IdStr3 -> IdStr)
	 Concatenate(IdStr, "_array" -> ArrayIdStr)
	 string_to_id(ArrayIdStr -> ArrayId)	 
	 SAL_TYPES_Cid -> Cid
	 
	 New_SAL_type_id_with_Cid(Pos, ArrayId,Cid, array(D,R) -> Tid)

	 SAL_Find_Tid(D -> DomTid)
	 SAL_Find_Tid(R -> RngTid)

	 -- Generate the range of the list (datatype)
	 Concatenate(ArrayIdStr, "_range" -> ArrayRangeStr)
	 string_to_id(ArrayRangeStr -> ArrayRangeId)
	 IncreaseCol(Pos -> Pos1)
	 New_SAL_type_id_with_Cid(Pos1, ArrayRangeId,Cid, any -> ArrayRangeTid)
	 -- Generating the type reference to the MapRangeType:
	 where(type_refs(sal_defined(Pos1, ArrayRangeId, ArrayRangeTid)) -> ArrayRangeRef)
	 -- generate the nil part:
	 Concatenate(ArrayIdStr, "_nil" -> Nil_Str)
	 string_to_id(Nil_Str -> Nil_Cons_id)
	 where(SAL_ID_OP'id(Nil_Cons_id) -> NilIdOp)
	 New_SAL_value_id(Pos, NilIdOp, Cid, ArrayRangeRef,constructor_value -> NilVid)
	 where(sal_construc(NilIdOp, NilVid, nil,nil) -> Nil_Construct)
	 where(sal_part(Nil_Construct,ArrayRangeRef) -> NIL_Part)
	 -- generate the Range part:
	 Concatenate(ArrayIdStr, "_range" -> RangeStr)
	 string_to_id(RangeStr -> Val_Cons_id)
	 where(SAL_ID_OP'id(Val_Cons_id) -> ValIdOp)
	 -- Increasing the pos of this new value...
	 -- Used for lookup...
	 IncreaseCol(Pos1 -> IncPos)
	 New_SAL_value_id(IncPos, ValIdOp, Cid, ArrayRangeRef,constructor_value -> ValVid)
	 -- generating the destructor:
	 Concatenate(ArrayIdStr, "_val" -> VAL_str)
	 string_to_id(VAL_str -> Rng_Cons_id)
	 where(SAL_ID_OP'id(Rng_Cons_id) -> RngIdOp)
	 RngTid'Pos -> RPos
	 RngTid'Ident -> RngId
	 where(type_refs(sal_defined(RPos, RngId, RngTid)) -> SALRngType)
         -- Don't use RPos here - causes confusion if RPos is a subtype CWG
         IncreaseCol(IncPos -> IncPos1)
	 New_SAL_value_id(IncPos1, RngIdOp, Cid, SALRngType, regular_value -> RngVid)
	 where(SAL_DESTRUCTORS'list(sal_destructor(RngIdOp,RngVid,SALRngType,none), nil) -> Destrs)
	 --
	 where(sal_construc(ValIdOp, ValVid, Destrs, nil) -> Val_Construct)
	 where(sal_part(Val_Construct,ArrayRangeRef) -> Val_Part)
	 --
	 where(SAL_DATA_TYPE_PARTS'list(NIL_Part, list(Val_Part, nil)) -> DTParts)
	 where(user_defined(sal_variant_type(DTParts)) -> ArrayRangeTypeExpr)
	 -- Updating the type info in the Tid:
	 ArrayRangeTid'TExpr <- ArrayRangeTypeExpr
	 -- Generate the declaration:
	 where(sal_type_decl(ArrayRangeId, ArrayRangeTid, ArrayRangeTypeExpr) -> RangeDecl)
	 ArrayRangeTid'Declaration  <- RangeDecl
	 Extend_Static_in_Cid_Decl(Cid, RangeDecl)


     -- Array declaration:
	 --where(type_refs(sal_defined(IncPos,ArrayRangeId,ArrayRangeTid)) -> Range)
	 where(type_refs(sal_defined(Pos,RngTypeId,RngTid)) -> Range)
	 -- Generate the type reference for the domain (DOM)
	 where(type_refs(sal_defined(Pos,DomTypeId,DomTid)) -> Domain)
	 -- Generate the mapping that implements the map:
	 -- Map : TYPE = [Domain -> Range];
	 where(sal_basic(sal_array(Domain, Range)) -> TE2)
	 where(sal_type_decl(ArrayId, Tid, TE2) -> Decl)
	 -- Incorporate it in the Cid:
	 Extend_Static_in_Cid_Decl(Cid, Decl)
	 -- Collect the declaration in the Tid:
	 Tid'Declaration <- Decl
	 Tid'TExpr <- rsl_built_in(sal_array(Tid,Domain,Range))

	 SAL_Types_Extra_Defs -> Defs
	 --where(SAL_CONTEXT_CONSTANTS'list(RangeDecl, list(Decl, nil)) -> New)
	 where(SAL_CONTEXT_CONSTANTS'list(Decl, nil) -> New)
	 SAL_Concatenate_Context_Constants(Defs, New -> NewDefs)
	 SAL_Types_Extra_Defs <- NewDefs

	 -- It is necessary to generate the sets for the dom and rng operations:
	 -- Dom set:

	 SAL_Check_Defined_Set(Pos, D -> DOptTid)
	 (|
	    --There is no set of this type, generate a new one:
	    eq(DOptTid, nil)
	    -- It is necessary to update the pos because the current TID already 
	    -- has this position (the TID of the map). If the positions match, no new
	    -- type_id will be created (the map_tid will be returned instead)
	    --IncreaseCol(IncPos -> IncPosII)
            IncreaseCol(Pos -> IncPosII)
--Putmsg("1\n")
--Putmsg(MapIdStr)
--Putnl()
	    SAL_Gen_New_Set_Type(IncPosII,DomTypeId, D -> DomSetTid)
--Putmsg("2\n")
--Putmsg(MapIdStr)
--Putnl()
	    DomSetTid'Cid <- cid(Cid)
	 ||
	    where(Pos -> IncPosII)
	    where(DOptTid -> tid(DomSetTid))
	 |)

	 
	 -- Rng set:
	 SAL_Check_Defined_Set(Pos, R -> ROptTid)
	 (|
	    --There is no set of this type, generate a new one:
	    eq(ROptTid, nil)
	    IncreaseCol(IncPosII -> IncPosIII)
	    SAL_Gen_New_Set_Type(IncPosIII, RngTypeId, R -> RngSetTid)
	    RngSetTid'Cid <- cid(Cid)
	 ||
	    where(ROptTid -> tid(RngSetTid))
	 |)
	 
	 
	 DomSetTid'OperationsCid -> cid(OpsDomTypeCid)
	 RngSetTid'OperationsCid -> cid(OpsRngTypeCid)

	 -- seems MapIdStr can be corrupted by SAL_Gen_New_Set_Type
	 -- so make it again CWG 12/4/08
	 id_to_string(ArrayId -> ArrayIdStr2)
	 -- Generate the Cid for the operations of this map:
	 SAL_Gen_Array_Ops_Context(ArrayIdStr2,ArrayRangeTypeExpr,Tid,OpsDomTypeCid, OpsRngTypeCid,DomSetTid ,RngSetTid-> OpCid)
	 -- Update the reference in the Tid:
	 Tid'OperationsCid <- cid(OpCid)

	 -- cc
--Putmsg("Generating a new cc map\n")
	     -- Generating lifted domain and range for the map:
	     SAL_Gen_Type_Expr(Pos, D -> Dom, LDom)
	     SAL_Gen_Type_Expr(Pos, R -> Rng, LRng)


	     Maxtype(D -> MaxD)
	     SAL_Gen_Type_Expr(Pos, MaxD -> MaxDom, _)
	     Maxtype(R -> MaxR)
	     SAL_Gen_Type_Expr(Pos, MaxR -> MaxRng, _)
	     Tid'Lifted_Tid -> tid(LArrayTid)
	     add_tid_to_lifted_global(Tid)
	     DomSetTid'Lifted_Tid -> tid(LDomSetTid)
	     RngSetTid'Lifted_Tid -> tid(LRngSetTid)
	     where(LDom -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,LDomTid)),_)))
	     where(LRng -> user_defined(sal_cc_type(type_refs(sal_defined(_,_,LRngTid)),_))) 
	     LArrayTid'Ident -> LArrayId
	     id_to_string(LArrayId -> Str5)
	     SAL_Gen_Array_CC_Ops_Context(Str5,LArrayTid,LDomTid,LRngTid,LDomSetTid, LRngSetTid, Dom, Rng, MaxDom, MaxRng -> LOpCid)
	     LArrayTid'OperationsCid <- cid(LOpCid)
	     OpCid'Lifted_Cid <- cid(LOpCid)
--SAL_Print_Tid(LMapTid)
--Putnl()



	 -- Collecting the map AT THE END to avoid its own detection when checking for maximal types
	 -- for the cc-version:
	 where(array_type(D,R , Tid) -> ArrayInfo)
	 Current_Array_Types -> ArrayTypes
	 where(SAL_LIST_TYPES'list(ArrayInfo, ArrayTypes) -> NewArrayTypes)
	 Current_Array_Types <- NewArrayTypes

-----------------------------------------------------------------------------------------------


'action' Generate_Constant_for_Type(IDENT, IDENT  -> SAL_value_id, SAL_CONSTANT_DECL)

  'rule' Generate_Constant_for_Type(Ident, InitValId -> Vid, Decl):
	 where(sal_literal(integ(InitValId)) -> Expr1)
	 -- Generate the global Vid for this value:
	 where(SAL_ID_OP'id(Ident) -> IdOp1)
	 New_SAL_special_value_id(IdOp1, sal_basic(sal_integer) -> Vid)
	 -- Generate the declaration
	 where(sal_expl_const(IdOp1, Vid, sal_basic(sal_integer), Expr1) -> Decl)

'action' Update_Constants_for_Type(SAL_CONSTANT_DECLS, IDENT, IDENT -> SAL_CONSTANT_DECLS)

  'rule' Update_Constants_for_Type(list(Const, Consts), Ident, ValIdent
  	 				      -> list(Const1, Consts1)):
  	 (|
	   where(Const -> sal_expl_const(IdOp, Vid, sal_basic(sal_integer), Expr))
	   where(Expr -> sal_literal(integ(_)))
	   where(IdOp -> id(Ident1))
	   eq(Ident, Ident1)
	   where(sal_literal(integ(ValIdent)) -> Expr1)
	   where(sal_expl_const(IdOp, Vid, sal_basic(sal_integer), Expr1) -> Const1)
	   where(Consts -> Consts1)
	 ||
	   Update_Constants_for_Type(Consts, Ident, ValIdent -> Consts1)
  	   where(Const -> Const1)
	 |)

  'rule' Update_Constants_for_Type(nil, _, _ -> nil):

'action' Generate_Global_Constant(IDENT, IDENT, SAL_type_id -> SAL_value_id)
	 
  'rule' Generate_Global_Constant(Id,InitValId, Tid -> Vid)
	 Generate_Constant_for_Type(Id,InitValId -> Vid, Decl)
	 where(sal_param_decl(SAL_CONSTANT_DECLS'list(Decl,nil),Tid) -> CD)
	 -- Collect the new constant decl globally (used later in when
	 -- generating the global context:
	 Generated_Constants -> CurrConst1
	 where(SAL_CONSTANT_DECLS'list(CD, CurrConst1) -> NewConts1)
	 Generated_Constants <- NewConts1

'action' Update_Global_Constant(IDENT, IDENT)

  'rule' Update_Global_Constant(Ident, ValIdent):
  	 Generated_Constants -> Consts
	 Update_Global_Constants(Consts, Ident, ValIdent -> Consts1)
	 Generated_Constants <- Consts1

'action' Update_Global_Constants(SAL_CONSTANT_DECLS, IDENT, IDENT -> SAL_CONSTANT_DECLS) 

  'rule' Update_Global_Constants(list(D, DS), Id, ValId -> list(D1,
  DS1)):
	 (|
	   where(D -> sal_param_decl(Consts, Tid))
	   Update_Constants_for_Type(Consts, Id, ValId -> Consts1)
	   where(sal_param_decl(Consts1, Tid) -> D1)
	 ||
	   where(D -> D1)
	 |)
	 Update_Global_Constants(DS, Id, ValId -> DS1)

  'rule' Update_Global_Constants(nil, _, _ -> nil):



'action' Generate_Global_Pair_of_Constants(IDENT, IDENT, IDENT, IDENT, SAL_type_id 
	   -> SAL_value_id, SAL_value_id)

  'rule' Generate_Global_Pair_of_Constants(Id1,InitValId1,Id2,InitValId2,Tid ->
								   Vid1,Vid2)

	 Generate_Constant_for_Type(Id1, InitValId1 -> Vid1, Constant)
	 Generate_Constant_for_Type(Id2, InitValId2 -> Vid2, Constant1)

	 -- Update the declaration in the Vid (used for fixed point calculation)	   
	 -- (Even though it is not really used in the calculation)
	 Vid1'Declaration <- sal_const_decl(sal_param_decl(
			       SAL_CONSTANT_DECLS'list(Constant,nil),Tid))
	 Vid2'Declaration <- sal_const_decl(sal_param_decl(
			       SAL_CONSTANT_DECLS'list(Constant1,nil),Tid))

	 -- Collect both declarations:   
	 where(sal_param_decl(SAL_CONSTANT_DECLS'list(Constant,list(Constant1,nil)),Tid) -> CD)
	 -- Collect the new constant decl globally (used later in when
	 -- generating the global context:
	 Generated_Constants -> CurrConst1
	 where(SAL_CONSTANT_DECLS'list(CD, CurrConst1) -> NewConts1)
	 Generated_Constants <- NewConts1

-----------------------------------------------------
'action' SAL_Gen_Bool_Ops_Context(-> SAL_context_id)

  'rule' SAL_Gen_Bool_Ops_Context(-> Cid)
	 string_to_id("BO_AN" -> Ident)
	 New_SAL_context_id(Ident, 0 -> Cid)
------------------------------------------------------
'action' SAL_Gen_Collections_Ops_Context(STRING, SAL_TYPE_EXPR, SAL_type_id -> SAL_context_id)

  'rule' SAL_Gen_Collections_Ops_Context(Str, TExpr,Tid -> Cid)
	 -- Generating the name for the new context:
	 Concatenate(Str, "_OPS" -> Str2)
	 string_to_id(Str2 -> Ident)
	 New_SAL_context_id(Ident, 0 -> Cid)

'action' SAL_Gen_Set_Ops_Context(STRING, SAL_TYPE_EXPR, SAL_type_id -> SAL_context_id)

  'rule' SAL_Gen_Set_Ops_Context(Str, TExpr,Tid -> Cid)
	 -- Generating the name for the new context:
	 Concatenate(Str, "_OPS" -> Str2)
	 string_to_id(Str2 -> Ident)
	 New_SAL_context_id(Ident, 0 -> Cid)
	 -- Generating the AST element for the context:
	 where(macro_set_cmd(Tid, TExpr) -> Elem)
	 where(MACRO_CONSTANTS'list(Elem,nil) -> Elems)
	 where(macro_context(Ident, cid(Cid), Elems) -> NewContext)
	 -- Adding the context to the global list of operation contexts:
	 SAL_Add_Operation_Context(NewContext)

'action' SAL_Gen_Set_CC_Ops_Context(STRING, SAL_TYPE_EXPR, SAL_TYPE_EXPR, SAL_type_id -> SAL_context_id)

  'rule' SAL_Gen_Set_CC_Ops_Context(Str, TExpr, LTExpr, Tid -> LCid)
	 Concatenate(Str, "_OPS" -> Str2)
	 string_to_id(Str2 -> Ident)
	 New_SAL_context_id(Ident, 0 -> LCid)
	 LCid'Lifted_Cid <- cid(LCid)
	 -- cc
	 where(macro_cc_set_cmd(Tid, TExpr, LTExpr) -> CC_Elem)
	 where(MACRO_CONSTANTS'list(CC_Elem,nil) -> CC_Elems)
	 where(macro_context(Ident, cid(LCid), CC_Elems) -> CC_Context)
	 SAL_Add_CC_Operation_Context(CC_Context)

'action' SAL_Gen_Map_Ops_Context(STRING,SAL_TYPE_EXPR, SAL_type_id, 
                                 SAL_context_id, SAL_context_id, SAL_type_id, SAL_type_id -> SAL_context_id)

  'rule' SAL_Gen_Map_Ops_Context(Str, TExpr,Tid,OpsDomSetCid,OpsRngSetCid,DomSetTid,RngSetTid -> Cid)
	 -- Generating the name for the new context:
	 Concatenate(Str, "_OPS" -> Str2)
	 string_to_id(Str2 -> Ident)
	 New_SAL_context_id(Ident, 0 -> Cid)
	 -- Generating the AST element for the context:
	 where(macro_map_cmd(Tid, TExpr,OpsDomSetCid,OpsRngSetCid,DomSetTid,RngSetTid) -> Elem)
	 where(MACRO_CONSTANTS'list(Elem,nil) -> Elems)
	 where(macro_context(Ident, cid(Cid), Elems) -> NewContext)
	 -- Adding the context to the global list of operation contexts:
	 SAL_Add_Operation_Context(NewContext)

'action' SAL_Gen_Array_Ops_Context(STRING,SAL_TYPE_EXPR, SAL_type_id, 
                                 SAL_context_id, SAL_context_id, SAL_type_id, SAL_type_id -> SAL_context_id)

  'rule' SAL_Gen_Array_Ops_Context(Str, TExpr,Tid,OpsDomSetCid,OpsRngSetCid,DomSetTid,RngSetTid -> Cid)
	 -- Generating the name for the new context:
	 Concatenate(Str, "_OPS" -> Str2)
	 string_to_id(Str2 -> Ident)
	 New_SAL_context_id(Ident, 0 -> Cid)
	 -- Generating the AST element for the context:
	 where(macro_array_cmd(Tid, TExpr,OpsDomSetCid,OpsRngSetCid,DomSetTid,RngSetTid) -> Elem)
	 where(MACRO_CONSTANTS'list(Elem,nil) -> Elems)
	 where(macro_context(Ident, cid(Cid), Elems) -> NewContext)
	 -- Adding the context to the global list of operation contexts:
	 SAL_Add_Operation_Context(NewContext)


'action' SAL_Gen_Map_CC_Ops_Context(STRING, SAL_type_id, SAL_type_id, 
   SAL_type_id, SAL_type_id, SAL_type_id,
   SAL_TYPE_EXPR, SAL_TYPE_EXPR, SAL_TYPE_EXPR, SAL_TYPE_EXPR, SAL_type_id  
                                                          -> SAL_context_id)

  'rule' SAL_Gen_Map_CC_Ops_Context(Str, MapTid, DomTid, RngTid, DomSetTid, RngSetTid, D, R, MD, MR, MapRangeTid -> Cid)
	 SAL_Get_MapNav(-> MapNavVid)
	 -- Generating the name for the new context:
	 Concatenate(Str, "_OPS" -> Str2)
	 string_to_id(Str2 -> Ident)
	 New_SAL_context_id(Ident, 0 -> Cid)
	 Cid'Lifted_Cid <- cid(Cid)
	 where(macro_cc_map_cmd(MapTid, DomTid, RngTid, DomSetTid,
	 RngSetTid, MapNavVid, D, R, MD, MR, MapRangeTid) -> CC_Elem)
	 where(MACRO_CONSTANTS'list(CC_Elem,nil) -> CC_Elems)
	 where(macro_context(Ident, cid(Cid), CC_Elems) -> CC_Context)
	 SAL_Add_CC_Operation_Context(CC_Context)

'action' SAL_Gen_Array_CC_Ops_Context(STRING, SAL_type_id, SAL_type_id, 
   SAL_type_id, SAL_type_id, SAL_type_id,
   SAL_TYPE_EXPR, SAL_TYPE_EXPR, SAL_TYPE_EXPR, SAL_TYPE_EXPR  
                                                          -> SAL_context_id)

  'rule' SAL_Gen_Array_CC_Ops_Context(Str, ArrayTid, DomTid, RngTid, DomSetTid, RngSetTid, D, R, MD, MR -> Cid)
	 SAL_Get_ArrayNav(-> ArrayNavVid)
	 -- Generating the name for the new context:
	 Concatenate(Str, "_OPS" -> Str2)
	 string_to_id(Str2 -> Ident)
	 New_SAL_context_id(Ident, 0 -> Cid)
	 Cid'Lifted_Cid <- cid(Cid)
	 where(macro_cc_array_cmd(ArrayTid, DomTid, RngTid, DomSetTid,
	 RngSetTid, ArrayNavVid, D, R, MD, MR) -> CC_Elem)
	 where(MACRO_CONSTANTS'list(CC_Elem,nil) -> CC_Elems)
	 where(macro_context(Ident, cid(Cid), CC_Elems) -> CC_Context)
	 SAL_Add_CC_Operation_Context(CC_Context)


'action' SAL_Get_MapNav(-> SAL_value_id)

  'rule' SAL_Get_MapNav(-> MapNavVid):
	 (|
	   MapApplicationNav -> vid(MapNavVid)
         ||
	   DefaultPos(->P)
	   Extend_Nav_Type(P, "Argument_of_map_application_not_in_domain" -> MapNavVid)
	   MapApplicationNav <- vid(MapNavVid)
	 |)

'action' SAL_Get_ArrayNav(-> SAL_value_id)

  'rule' SAL_Get_ArrayNav(-> ArrayNavVid):
	 (|
	   ArrayApplicationNav -> vid(ArrayNavVid)
         ||
	   DefaultPos(->P)
	   Extend_Nav_Type(P, "Argument_of_array_application_not_in_domain" -> ArrayNavVid)
	   ArrayApplicationNav <- vid(ArrayNavVid)
	 |)

'action' SAL_Gen_Int_Ops_Context(SAL_type_id -> SAL_context_id)

  'rule' SAL_Gen_Int_Ops_Context(IntTid -> Cid)
	 IntTid'Ident -> Id
	 id_to_string(Id -> Str)
	 -- Generating the name for the new context:
	 Concatenate(Str, "_OPS" -> Str2)
	 string_to_id(Str2 -> Ident)
	 New_SAL_context_id(Ident, 0 -> Cid)
	 -- Generating the AST element for the context:
	 where(macro_int_cmd(IntTid) -> Elem)
	 where(MACRO_CONSTANTS'list(Elem,nil) -> Elems)
	 where(macro_context(Ident, cid(Cid), Elems) -> NewContext)
	 -- Adding the context to the global list of operation contexts:
	 SAL_Add_Operation_Context(NewContext)

'action' SAL_Gen_Int_CC_Ops_Context(SAL_type_id, SAL_value_id  -> SAL_context_id)

  'rule' SAL_Gen_Int_CC_Ops_Context(IntTid, Div_by_Cero_Vid -> Cid)
	 IntTid'Ident -> Id
	 id_to_string(Id -> Str)
	 -- Generating the name for the new context:
	 Concatenate(Str, "_OPS" -> Str2)
	 string_to_id(Str2 -> Ident)
	 Default_Bool_Tid -> BoolTid
	 New_SAL_context_id(Ident, 0 -> Cid)
	 -- Generating the AST element for the context:
	 where(macro_int_cc_cmd(IntTid, BoolTid, Div_by_Cero_Vid) -> Elem)
	 where(MACRO_CONSTANTS'list(Elem,nil) -> Elems)
	 where(macro_context(Ident, cid(Cid), Elems) -> NewContext)
	 -- Adding the context to the global list of CC operation contexts:
	 SAL_Add_CC_Operation_Context(NewContext)


'action' SAL_Gen_Bool_CC_Ops_Context(SAL_type_id -> SAL_context_id)

  'rule' SAL_Gen_Bool_CC_Ops_Context(BoolTid -> Cid)
	 BoolTid'Ident -> Id
	 id_to_string(Id -> Str)
	 -- Generating the name for the new context:
	 Concatenate(Str, "_OPS" -> Str2)
	 string_to_id(Str2 -> Ident)
	 New_SAL_context_id(Ident, 0 -> Cid)
	 -- Generating the AST element for the context:
	 where(macro_bool_cc_cmd(BoolTid) -> Elem)
	 where(MACRO_CONSTANTS'list(Elem,nil) -> Elems)
	 where(macro_context(Ident, cid(Cid), Elems) -> NewContext)
	 -- Adding the context to the global list of CC operation contexts:
	 SAL_Add_CC_Operation_Context(NewContext)

-------------------------------------------------------------------
-- SAL_Gen_CC_Ops_Context
-------------------------------------------------------------------
-- Used to generate contexts for all the cc types where 'eq' and 'neq'
-- functions need to be defined (the built-in '=' and '/=' can't be used
-- beceuse of nav values need to be preserved).
-------------------------------------------------------------------
'action' SAL_Gen_CC_Ops_Context(TYPE_EXPR, SAL_type_id)

	 -- If the type associated with this Tid is a collection (set, map or list)
	 -- then no context should be generated by this routine (collections have OPS contexts
	 -- generated specially for them)
  'rule' SAL_Gen_CC_Ops_Context(T,_)
	 Type_is_Collection(T)

  'rule' SAL_Gen_CC_Ops_Context(_, Tid)
	 Tid'Ident -> Id
	 id_to_string(Id -> Str)
	 -- Generating the name for the new context:
	 Concatenate(Str, "_OPS" -> Str2)
	 string_to_id(Str2 -> Ident)
	 New_SAL_context_id(Ident, 0 -> Cid)
	 -- Generating the AST element for the context:
	 where(macro_type_cc_cmd(Tid) -> Elem)
	 where(MACRO_CONSTANTS'list(Elem,nil) -> Elems)
	 where(macro_context(Ident, cid(Cid), Elems) -> NewContext)
	 -- Adding the context to the global list of CC operation contexts:
	 SAL_Add_CC_Operation_Context(NewContext)
	 Tid'OperationsCid <- cid(Cid)
-----------------------------------------------------
'action' Push_Disamb(VALUE_EXPR)

  'rule' Push_Disamb(Disamb)
	 Disamb_Stack -> CurrStack
	 where(VALUE_EXPRS'list(Disamb, CurrStack) -> NewS)
	 Disamb_Stack <- NewS
	 
'action' Pop_Disamb

  'rule' Pop_Disamb
	 Disamb_Stack -> CurrStack
	 (|
	    where(CurrStack -> list(_, Rest))
	 ||
	    Putmsg("Internal error: Disambiguation stack undeflow\n")
	    where(VALUE_EXPRS'nil -> Rest)
	 |)
	 Disamb_Stack <- Rest

'action' Get_Current_Disamb(-> VALUE_EXPR)

  'rule' Get_Current_Disamb(-> Disamb)
	 Disamb_Stack -> CurrStack
	 (|
	    where(CurrStack -> list(Disamb,_))
	 ||
	    where(VALUE_EXPR'no_val -> Disamb)
	 |)

---------------------------------------------------------------------
-- SAL_Match_Type
---------------------------------------------------------------------
-- Function that will match types. Will not use Match_type because
-- this funtion works over MAXIMAL types and SAL requires a finer
-- grade in the comparison.
---------------------------------------------------------------------
'condition' SAL_Match_Type(POS, TYPE_EXPR, TYPE_EXPR, UNFOLD_SUBTYPES)


  'rule' SAL_Match_Type(_, defined(Pos1, _), defined(Pos2, _),_)
	 eq(Pos1, Pos2)

  'rule' SAL_Match_Type(_, int, int,_)

  'rule' SAL_Match_Type(_, nat, nat,_)
 
-- Nat and Int are indistinguishable so far... (Not any more)
--  'rule' SAL_Match_Type(_, nat, int,_)
--  'rule' SAL_Match_Type(_, int, nat,_)

  -- Basic types:
  'rule' SAL_Match_Type(_, bool, bool,_)
  'rule' SAL_Match_Type(_, unit, unit,_)

  -- For compatibility:
  'rule' SAL_Match_Type(_, real, real,_)
  'rule' SAL_Match_Type(_, char, char,_)
  'rule' SAL_Match_Type(_, text, text,_)

  -- any matches by default:
  'rule' SAL_Match_Type(_, any, _,_)  
  'rule' SAL_Match_Type(_, _, any,_)

  'rule' SAL_Match_Type(Pos, subtype(Typing,_), T, yes)
	 (|
	     where(Typing -> single(_,_,Type))
	 ||
	     where(Typing -> multiple(_,_,Type))
	 |)
	 SAL_Match_Type(Pos, Type, T, yes)

  'rule' SAL_Match_Type(Pos, T1,T2, US)
	 (|
	    Type_is_set(T1 -> TExpr1)
	    Type_is_set(T2 -> TExpr2)
	    SAL_Match_Type(Pos,TExpr1, TExpr2, US)
	 ||
	    Type_is_map(T1 -> D1,R1)
	    Type_is_map(T2 -> D2,R2)
	    SAL_Match_Type(Pos,D1, D2, US)
	    SAL_Match_Type(Pos,R1, R2, US)
	 ||
	    Type_is_list(T1 -> R1)
	    Type_is_list(T2 -> R2)
	    SAL_Match_Type(Pos, R1, R2, US)
          ||
            Type_is_array(T1 -> D1, R1)
            Type_is_array(T2 -> D2, R2)
            SAL_Match_Type(Pos, D1, D2, US)
            SAL_Match_Type(Pos, R1, R2, US)
	 |)

  'rule' SAL_Match_Type(_, defined(Tid1,_), defined(Tid2,_), _):
	 eq(Tid1, Tid2)

  'rule' SAL_Match_Type(Pos, T1, T2, US)
	 (|
	    where(T2 -> defined(Tid,_))
	    Tid'Def -> T11
	    where(T11 -> abbreviation(T))
	    SAL_Match_Type(Pos, T1, T, US)
	 ||
            where(T1 -> defined(Tid,_))
	    Tid'Def -> T11
	    where(T11 -> abbreviation(T))
	    SAL_Match_Type(Pos, T, T2, US)
	 |)
 
  'rule' SAL_Match_Type(Pos, product(PT1), product(PT2),US)
	 SAL_Match_Products(Pos, PT1, PT2, US)

  'rule' SAL_Match_Type(Pos, function(ParType1, _, result(_,RType1)), function(ParType2, _, result(_,RType2)), US)
	 SAL_Match_Type(Pos,ParType1, ParType2, US)
	 SAL_Match_Type(Pos, RType1, RType2, US)

  'rule' SAL_Match_Type(Pos, fun(ParType1, _, result(RType1,_,_,_,_)), fun(ParType2, _, result(RType2,_,_,_,_)), US)
	 SAL_Match_Type(Pos,ParType1, ParType2, US)
	 SAL_Match_Type(Pos, RType1, RType2, US)

  'rule' SAL_Match_Type(Pos, bracket(T1), T2, US)
	 SAL_Match_Type(Pos, T1, T2, US)

  'rule' SAL_Match_Type(Pos, T1, bracket(T2), US)
	 SAL_Match_Type(Pos, T1, T2, US)

---------------------------------------------------------------------
'condition' SAL_Match_Products(POS, PRODUCT_TYPE, PRODUCT_TYPE, UNFOLD_SUBTYPES)

  'rule' SAL_Match_Products(Pos, list(T1, Rest1), list(T2, Rest2), US)
	 SAL_Match_Type(Pos, T1, T2, US)
	 SAL_Match_Products(Pos, Rest1, Rest2, US)

  'rule' SAL_Match_Products(_, nil,nil,_)
---------------------------------------------------------------------
'action' SAL_Find_Tid(TYPE_EXPR -> SAL_type_id)

  'rule' SAL_Find_Tid(defined(Typeid,_) -> Tid)
	 Typeid'Pos -> Pos
	 look_up_type_id(Pos -> OptTid)
	 where(OptTid -> tid(Tid))
	 
  'rule' SAL_Find_Tid(int -> Tid)
	 Default_Int_Tid -> Tid	 	 

  'rule' SAL_Find_Tid(bool -> Tid)
	 Default_Bool_Tid -> Tid

  'rule' SAL_Find_Tid(nat -> Tid)
	 Default_Nat_Tid -> Tid	 

----------------------------------------------------------------------
'action' SAL_Remove_Duplicates_from_Decls(
	   SAL_CONTEXT_CONSTANTS -> SAL_CONTEXT_CONSTANTS)

  'rule' SAL_Remove_Duplicates_from_Decls(list(H,T) -> Result)
	 (|
	    is_present_ahead(H, T)
	    SAL_Remove_Duplicates_from_Decls(T -> Result)
	 ||
	    SAL_Remove_Duplicates_from_Decls(T -> Result1)
	    where(SAL_CONTEXT_CONSTANTS'list(H, Result1) -> Result)
	 |)

  'rule' SAL_Remove_Duplicates_from_Decls(nil -> nil)

'condition' is_present_ahead(SAL_CONTEXT_CONSTANT, SAL_CONTEXT_CONSTANTS)

  'rule' is_present_ahead(Decl, list(Decl1, Rest))
	 (|
	     match_decl(Decl,Decl1)
	 ||
	     is_present_ahead(Decl, Rest)
	 |)

'condition' match_decl(SAL_CONTEXT_CONSTANT, SAL_CONTEXT_CONSTANT)

  'rule' match_decl(sal_type_decl(P,Tid,Type), sal_type_decl(Pos,Tid1,Type1))
	 eq(Tid,Tid1)

  'rule' match_decl(sal_const_decl(Decl1), sal_const_decl(Decl2))
	 (|
	    where(Decl1 -> sal_expl_const(_,Vid1,_,_))
	    where(Decl2 -> sal_expl_const(_,Vid2,_,_))
	 ||
	    where(Decl1 -> sal_fun_const(_,Vid1, _,_,_,_,_,_))
	    where(Decl2 -> sal_fun_const(_,Vid2, _,_,_,_,_,_))
	 |)
	 eq(Vid1,Vid2)


-------------------------------------------------------------------------------
'action' SAL_Get_Expr_Pos(VALUE_EXPR -> POS)

  'rule' SAL_Get_Expr_Pos(literal_expr(Pos, ValueLit) -> Pos)

  'rule' SAL_Get_Expr_Pos(named_val(Pos, name(_, IdorOp)) -> Pos)

  'rule' SAL_Get_Expr_Pos(pre_name(Pos, Name) -> Pos)

  'rule' SAL_Get_Expr_Pos(chaos(Pos) -> Pos)

  'rule' SAL_Get_Expr_Pos(skip(Pos) -> Pos)


  'rule' SAL_Get_Expr_Pos(stop(Pos) -> Pos)


  'rule' SAL_Get_Expr_Pos(swap(Pos) -> Pos)


  'rule' SAL_Get_Expr_Pos(product(Pos, ValueExprs) -> Pos)


  'rule' SAL_Get_Expr_Pos(ranged_set(Pos, LeftValueExpr, RightValueExpr) -> Pos)


  'rule' SAL_Get_Expr_Pos(enum_set(Pos, ValueExprs) -> Pos)


  'rule' SAL_Get_Expr_Pos(comp_set(Pos, ValueExpr,
		      set_limit(Pos2, Typings, Restriction)) -> Pos)


  'rule' SAL_Get_Expr_Pos(comp_set(Pos, ValueExpr,
		      set_limit(Pos2, Typings, Restriction)) -> Pos)


  'rule' SAL_Get_Expr_Pos(ranged_list(Pos, LeftValueExpr, RightValueExpr) -> Pos)


  'rule' SAL_Get_Expr_Pos(enum_list(Pos, ValueExprs) -> Pos)


  'rule' SAL_Get_Expr_Pos(comp_list(Pos, ValueExpr, Limit) -> Pos)
    
   
  'rule' SAL_Get_Expr_Pos(enum_map(Pos, ValueExprPairs) -> Pos):
  
  'rule' SAL_Get_Expr_Pos(comp_map(Pos, pair(LeftValueExpr, RightValueExpr),
                      set_limit(Pos2, Typings, Restriction)) -> Pos)



  'rule' SAL_Get_Expr_Pos(comp_map(Pos, pair(LeftValueExpr, RightValueExpr),
                      set_limit(Pos2, Typings, Restriction)) -> Pos)

  'rule' SAL_Get_Expr_Pos(function(Pos, LambdaParam, ValueExpr) -> Pos)


  'rule' SAL_Get_Expr_Pos(application(Pos, ValueExpr, Args:list(_, list(_, _)))
				       -> Pos)


  'rule' SAL_Get_Expr_Pos(application(Pos, ValueExpr, list(Arg, nil)) -> Pos)


  'rule' SAL_Get_Expr_Pos(quantified(Pos, Quantifier,  Typings, Restriction) -> Pos)


  'rule' SAL_Get_Expr_Pos(equivalence(Pos, ValueExprL, ValueExprR,
                                  PreCond) -> Pos)


  'rule' SAL_Get_Expr_Pos(post(Pos, ValueExpr, Post, PreCond) -> Pos)


  'rule' SAL_Get_Expr_Pos(disamb(Pos, ValueExpr, TypeExpr) -> Pos)


  'rule' SAL_Get_Expr_Pos(bracket(Pos, ValueExpr) -> Pos)


  'rule' SAL_Get_Expr_Pos(ax_infix(Pos, LeftValueExpr, Conn, RightValueExpr, _) -> Pos)

 
  'rule' SAL_Get_Expr_Pos(stmt_infix(Pos, _, _, _) -> Pos)

  'rule' SAL_Get_Expr_Pos(val_infix(Pos, _,_,_) -> Pos)

	 -- always ignored
  'rule' SAL_Get_Expr_Pos(always(Pos, ValueExpr) -> Pos)

 
  'rule' SAL_Get_Expr_Pos(ax_prefix(Pos, Conn, ValueExpr) -> Pos)

 
  'rule' SAL_Get_Expr_Pos(comprehended(Pos, _, _, _) -> Pos)


	 -- not supported
  'rule' SAL_Get_Expr_Pos(initialise(Pos, _) -> Pos)


	 
  'rule' SAL_Get_Expr_Pos(assignment(Pos, Vname, ValueExprR) -> Pos)


	 -- not supported
  'rule' SAL_Get_Expr_Pos(input(Pos, _) -> Pos)


	 -- not supported
  'rule' SAL_Get_Expr_Pos(output(Pos, _, _) -> Pos)


	 -- not supported
  'rule' SAL_Get_Expr_Pos(local_expr(Pos, Decls, ValueExpr) -> Pos)

  'rule' SAL_Get_Expr_Pos(let_expr(Pos, LetDefs, ValueExpr) -> Pos)

  'rule' SAL_Get_Expr_Pos(if_expr(Pos, ValueExpr, Then, _, Elsifs, Else)
					      -> Pos)

  'rule' SAL_Get_Expr_Pos(case_expr(Pos, ValueExpr, Pos2, CaseBranches) -> Pos)

	 -- not supported
  'rule' SAL_Get_Expr_Pos(while_expr(Pos, _, _) -> Pos)

	 -- not supported
  'rule' SAL_Get_Expr_Pos(until_expr(Pos, _, _) -> Pos)

	 -- not supported
  'rule' SAL_Get_Expr_Pos(for_expr(Pos, _, _) -> Pos)

  'rule' SAL_Get_Expr_Pos(env_class_scope(Pos, _, _, _) -> Pos)

  'rule' SAL_Get_Expr_Pos(env_class_scope(Pos, Class, CE, ValueExpr) -> Pos)

  'rule' SAL_Get_Expr_Pos(implementation_relation(Pos, NewClass, OldClass) -> Pos)
 
	 -- resolved to class scope expr
  'rule' SAL_Get_Expr_Pos(implementation_expr(Pos, NewObjExpr, OldObjExpr) -> Pos)

  'rule' SAL_Get_Expr_Pos(val_occ(Pos, Valueid, OptQual) -> Pos)

	 -- not supported
  'rule' SAL_Get_Expr_Pos(var_occ(Pos, VarId, _) -> Pos)

	 -- not supported
  'rule' SAL_Get_Expr_Pos(pre_occ(Pos, _, _) -> Pos)

  'rule' SAL_Get_Expr_Pos(infix_occ(Pos, LeftValueExpr, Valueid, OptQual,
				RightValueExpr) -> Pos)

  'rule' SAL_Get_Expr_Pos(prefix_occ(Pos, Valueid, OptQual, ValueExpr) -> Pos)

	 -- not supported
  'rule' SAL_Get_Expr_Pos(ass_occ(Pos, VarId, Qual, Expr) -> Pos)

	 -- not supported
  'rule' SAL_Get_Expr_Pos(input_occ(Pos, _, _) -> Pos)

	 -- not supported
  'rule' SAL_Get_Expr_Pos(output_occ(Pos, _, _, _) -> Pos)

	 -- not supported
  'rule' SAL_Get_Expr_Pos(env_local(Pos, Decls, ClassEnv, ValueExpr) -> Pos)

  'rule' SAL_Get_Expr_Pos(no_val -> Pos)
	 DefaultPos(-> Pos)

  'rule' SAL_Get_Expr_Pos(array_access(P,_,_) -> P)

  'rule' SAL_Get_Expr_Pos(array_assignment(P,_,_,_) -> P)

  'rule' SAL_Get_Expr_Pos(array_expr(P,_,_) -> P)

  'rule' SAL_Get_Expr_Pos(local_val_occ(P,_,_) -> P)

  'rule' SAL_Get_Expr_Pos(E -> P)
	 DefaultPos(-> P)
	 Putmsg("Debugging predicate activated in SAL_Get_Expr_Pos\n")
	 print(E)
-------------------------
'condition' Is_Collection(VALUE_EXPR)

  'rule' Is_Collection(Expr)
	 Get_Type_of_Value_Expr(Expr -> T)
	 Type_is_Collection(T)

'condition' Type_is_Collection(TYPE_EXPR)

  'rule' Type_is_Collection(T)
	 (|
	    Type_is_map(T -> _,_)
	 ||
	    Type_is_set(T -> _)
	 ||
	    Type_is_list(T -> _)
	 |)	    
----------------------------------
'action' SAL_Split_Type_of_infix_occ(VALUE_EXPR -> TYPE_EXPR, TYPE_EXPR)

  'rule' SAL_Split_Type_of_infix_occ(infix_occ(Pos1, LE,Op1,_,RE) -> LeftType, RightType)
	 Op1'Ident -> Op
	 (|
	    -- set operations... (where the left part is not a set)
	    (| eq(Op, op_op(isin)) || eq(Op, op_op(notisin)) |)
	    Get_Type_of_Value_Expr(RE -> RightType)
	    (|
	      Type_is_set(RightType -> LeftType)
	    ||
	      Type_is_map(RightType -> LeftType, _)
	    |)
	 ||
	    --  difference/restrict_by and restrict_to (can be a map or a set op)
	    (| eq(Op, op_op(rem)) || eq(Op, op_op(div)) |)
	    Get_Type_of_Value_Expr(LE -> LeftType)
	    (|
	        Type_is_map(LeftType -> DomType,_)
		where(infin_set(DomType) -> RightType)
	    ||
	        Get_Type_of_Value_Expr(RE -> RightType)
	    |)
	 ||
	    -- The rest of the cases (map and set operations) has the same type on both sides...
	    -- Taking the right hand side one...
	    Get_Type_of_Value_Expr(RE -> RightType)
	    where(RightType -> LeftType)
         |)

-----------------------------------
'action' SAL_Find_Accesor_in_Fields(SAL_DATA_TYPE_PARTS, SAL_value_id -> SAL_value_id)

  'rule' SAL_Find_Accesor_in_Fields(list(sal_part(sal_construc(_,Vid,Acc,_), _), Rest), Vid1 -> FoundVid)
         (|
            eq(Vid, Vid1)       
            where(Acc -> list(sal_destructor(_, FoundVid,_,_), _))
         ||
            SAL_Find_Accesor_in_Fields(Rest, Vid1 -> FoundVid)
         |)

---------------------------------
'action' SAL_Reset_Fixed_Point_Info

  'rule' SAL_Reset_Fixed_Point_Info
	 Global_Tid_Table -> Tids
	 Global_Vid_Table -> Vids
	 SAL_Reset_Fixed_Point_Info_in_Tids(Tids)
	 SAL_Reset_Fixed_Point_Info_in_Vids(Vids)


'action' SAL_Reset_Fixed_Point_Info_in_Tids(SAL_TYPE_IDS)

  'rule' SAL_Reset_Fixed_Point_Info_in_Tids(list(Tid, Rest))
	 Tid'FixedPoint <- nil
	 Tid'FPStatus <- not_calculated
	 SAL_Reset_Fixed_Point_Info_in_Tids(Rest)

  'rule' SAL_Reset_Fixed_Point_Info_in_Tids(nil)

'action' SAL_Reset_Fixed_Point_Info_in_Vids(SAL_VALUE_IDS)

  'rule' SAL_Reset_Fixed_Point_Info_in_Vids(list(Vid, Rest))
	 Vid'FixedPoint <- nil
	 Vid'FPStatus <- not_calculated
	 SAL_Reset_Fixed_Point_Info_in_Vids(Rest)

  'rule' SAL_Reset_Fixed_Point_Info_in_Vids(nil)
----------------------------------

'action' SAL_Gen_Ident_From_Type(SAL_TYPE_EXPR -> IDENT)

  'rule' SAL_Gen_Ident_From_Type(user_defined(sal_cc_type(TE, _)) -> Ident)
	 SAL_Gen_Ident_From_Type(TE -> Ident)

  'rule' SAL_Gen_Ident_From_Type(rsl_built_in(integer(Tid)) -> Ident)
	 Tid'Ident -> Ident
--	 string_to_id("Int" -> Ident)

  'rule' SAL_Gen_Ident_From_Type(rsl_built_in(natural(Tid)) -> Ident)
	 Tid'Ident -> Ident

  'rule' SAL_Gen_Ident_From_Type(rsl_built_in(boolean(Tid)) -> Ident)
	 Tid'Ident -> Ident

  'rule' SAL_Gen_Ident_From_Type(type_refs(sal_defined(_, Ident, _)) -> Ident)

  'rule' SAL_Gen_Ident_From_Type(user_defined(sal_sort(Tid)) -> Ident)
	 Tid'Ident -> Ident

  'rule' SAL_Gen_Ident_From_Type(user_defined(sal_bracket_type(TE)) -> Ident)
	 SAL_Gen_Ident_From_Type(TE -> Ident)

  'rule' SAL_Gen_Ident_From_Type(user_defined(sal_tuple_type(TElems)) -> Ident)
	 SAL_Gen_Ident_From_Tuple(TElems -> Ident)

  'rule' SAL_Gen_Ident_From_Type(user_defined(sal_abbrev(TE)) -> Ident)
	 SAL_Gen_Ident_From_Type(TE -> Ident)

  'rule' SAL_Gen_Ident_From_Type(user_defined(sal_fun_type(D,R)) -> Ident)
	 SAL_Gen_Ident_From_Type(D -> DId)
	 SAL_Gen_Ident_From_Type(R -> RId)
	 id_to_string(DId -> DStr)
	 id_to_string(RId -> RStr)
	 Concatenate(DStr, "_f_" -> Str1)
	 Concatenate(Str1, RStr -> Str2)
	 string_to_id(Str2 -> Ident)

  'rule' SAL_Gen_Ident_From_Type(user_defined(sal_subtype(id(Ident), _, _, _)) -> Ident)

  'rule' SAL_Gen_Ident_From_Type(user_defined(sal_record_type(Fields)) -> Ident)
	 SAL_Gen_Ident_From_Fields(Fields -> Ident)

  'rule' SAL_Gen_Ident_From_Type(user_defined(sal_variant_type(Fields)) -> Ident)
	 SAL_Gen_Ident_From_Fields(Fields -> Ident)

  'rule' SAL_Gen_Ident_From_Type(nil -> Ident):
  	 -- consequence of other errors - ignore
	 SAL_Gen_Type_Ident(-> Ident)

-----------------------------------------

'action' SAL_Gen_Ident_From_Tuple(SAL_TUPLE_ELEMS -> IDENT)

  'rule' SAL_Gen_Ident_From_Tuple(list(sal_tuple(TE), nil) -> Ident)
	 SAL_Gen_Ident_From_Type(TE -> Ident)

  'rule' SAL_Gen_Ident_From_Tuple(list(sal_tuple(TE), Rest) -> Ident)
	 SAL_Gen_Ident_From_Type(TE -> Id1)
	 SAL_Gen_Ident_From_Tuple(Rest -> Id2)
	 id_to_string(Id1 -> Str1)
	 id_to_string(Id2 -> Str2)
	 Concatenate(Str1, "_x_" -> Str3)
	 Concatenate(Str3, Str2 -> Str4)
	 string_to_id(Str4 -> Ident)

----------------------------------------
'action' SAL_Gen_Ident_From_Fields(SAL_DATA_TYPE_PARTS -> IDENT)

  'rule' SAL_Gen_Ident_From_Fields(list(sal_part(_, TE), nil) -> Ident)
	 SAL_Gen_Ident_From_Type(TE -> Ident)

  'rule' SAL_Gen_Ident_From_Fields(list(sal_part(_, TE), Rest) -> Ident)
	 SAL_Gen_Ident_From_Type(TE -> Id1)
	 SAL_Gen_Ident_From_Fields(Rest -> Id2)
	 id_to_string(Id1 -> Str1)
	 id_to_string(Id2 -> Str2)
	 Concatenate(Str1, "_v_" -> Str3)
	 Concatenate(Str3, Str2 -> Str4)
	 string_to_id(Str4 -> Ident)

----------------------------------------------------------------------
-- SAL_Check_Defined_Product
----------------------------------------------------------------------
-- This function checks if there exists another product definition that
-- maximally matches the current one.
---------------------------------------------------------------------

'action' SAL_Check_Defined_Maximal_Type(TYPE_EXPR -> OPT_SAL_TYPE_ID)

  'rule' SAL_Check_Defined_Maximal_Type(TExpr -> OptTid)
  	 Maxtype(TExpr -> Max)
	 Current_CC_Lifted_Types -> CC_Types
	 SAL_Internal_Check_Defined_Maximal_Type(Max, CC_Types -> OptTid)

'action' SAL_Internal_Check_Defined_Maximal_Type(TYPE_EXPR, SAL_LIST_TYPES -> OPT_SAL_TYPE_ID)

  'rule' SAL_Internal_Check_Defined_Maximal_Type(TExpr, list(lifted_type(TExpr1, Tid), Rest) -> OptTid)
	 (|
	     Maximal(TExpr1)
	     Match(TExpr,nil,TExpr1)
	     where(tid(Tid) -> OptTid)
	 ||
	     SAL_Internal_Check_Defined_Maximal_Type(TExpr, Rest -> OptTid)
	 |)

  'rule' SAL_Internal_Check_Defined_Maximal_Type(_, nil -> nil)

'action' Add_Lifted_to_Global(TYPE_EXPR, SAL_type_id)

  'rule' Add_Lifted_to_Global(TE, Tid)
	 Current_CC_Lifted_Types -> Current_CC_Types
	 where(SAL_LIST_TYPES'list(lifted_type(TE, Tid), Current_CC_Types) -> CC_Types)
	 Current_CC_Lifted_Types <- CC_Types

'action' Init_SAL_CC_Collection

  'rule' Init_SAL_CC_Collection
	 Default_Int_Tid -> ITid
	 ITid'Lifted_Tid -> tid(LITid)
	 Default_Bool_Tid -> BTid
	 BTid'Lifted_Tid -> tid(LBTid)
	 Current_CC_Lifted_Types <- SAL_LIST_TYPES'list(lifted_type(int, LITid), list(lifted_type(bool, LBTid), nil))

----------------------------------------
'action' SAL_Concatenate_Types(PRODUCT_TYPE, PRODUCT_TYPE -> PRODUCT_TYPE)

  'rule' SAL_Concatenate_Types(list(H,Rest), List -> list(H, Result1))
	 SAL_Concatenate_Types(Rest, List -> Result1)

  'rule' SAL_Concatenate_Types(nil, List -> List)
