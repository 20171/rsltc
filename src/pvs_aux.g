-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module has auxiliary actions for
-- the RSL to PVS translator

'module' pvs_aux


'use' ast print ext env objects values types pp cc sml
      pvs_ast


'export'
	 --   Variables

	 -- switch to distinguish if a module is a theory
	 IsTheoryOrDevtReln
	 -- switch to distinguish if top module is a theory
	 TopIsTheoryOrDevtReln
	 -- List of Idents for IMPORTINGS
	 -- to avoid duplicates
	 Importings
	 -- To keep all the Declareds already done
	 -- for sorting declareds
	 TotalDeclareds
	 -- Used to generate different THEORY Identifiers
         -- to translate every top class scope expression
	 -- a RSL theory as a PVS THEORY, when there is
	 -- no axiom name
	 TheoryIndex

	 -- Actions

	 -- To manage variable TheoryIndex
	 Init_TheoryIndex

	 -- To manage variable Importings
	 Init_Importings
	 Add_Importings

	 -- To manage variable TotalDeclareds
	 Init_TotalDeclareds
	 Add_Declareds
	 Add_Declared
	 Open_TotalDeclareds
	 Close_TotalDeclareds
	 Get_TotalDeclareds
	 Find_Declared
	 Find_Declared_s

	 -- To manage TheoryIdMap
	 InitTheoryIdMap
	 AddTheory
	 GetTheoryId

	 -- Miscelaneus
	 Gen_Theory_Name
	 Get_Pos_in_Declareds
	 Get_Pos_in_Declared
	 PVS_Literal_to_Ident
	 WriteFile_Name
	 SetTopIsTheory
	 SetTopNotTheory
	 TopIsTheory
	 SetIsTheory
	 SetNotTheory
	 IsTheory

	 -- Concatenates
	 -- Conc_*(Elems1, Elems2 -> Elems1 ^ Elems2)
	 Conc_Bindings
	 Conc_IdentList
	 Conc_PVSBindings
	 Conc_Declareds
	 Conc_PVS_Opt_Pos
	 Conc_Pos

	 -- Inserts
	 -- Insert_*(Elem, Elems -> Elems ^ <Elem>)
	 Insert_TypeExpr
	 Insert_DataTypePart
	 Insert_Accesor
	 Insert_SetBinding
	 Insert_LambdaBinding
	 Insert_LetBinding
	 Insert_LetBind
	 Insert_PVSBinding
	 Insert_Arguments
	 Insert_PVSFormal_Parameters
	 Insert_Theory_Element
	 Insert_Tuple
	 Insert_PVS_Expr
	 Insert_PVS_ExprPair
	 Insert_Elsif
	 Insert_Projection
	 Insert_Binding
	 Insert_Declared
	 Insert_IdOp
	 Insert_Ident

	 -- Pushs
	 -- Push_*(Elem, Elems -> <Elem> ^ Elems)
	 Push_Declared
	 
	 -- Insert_union_*(Elem, Elems ->
	 --                  if Elem is not in Elems
	 --                    then Elems ^ <Elem>)
	 Insert_u_Binding
	 Insert_u_Declared

	 -- Subtracts
	 -- Subtract(A, B -> C = A\B)
	 Subtract_Theory_Elems
	 Substract_Declareds
	 Substract_Declareds_by_Pos
	 -- Subtract(Declareds, Declareds_s -> Declareds\Declareds_s)
	 Substract_Declareds_s
	 -- Subtract(D, v1 -> {v in D | v <> v1})
	 Substract_Valueid
	 -- Subtract(D, B -> {x in D | x'id not in B})
	 Substract_Declareds_in_Bindings
	 -- Subtract(A, B -> B+(A\all built in operators in A))
	 Substract_Built_in_Ops

	 --  Reverse lists
	 Rev_Declareds

	 --  Conditions
	 Not_in_Theory_Elems
	 Not_in_Bindings
	 Not_in_Declareds
	 Not_in_Declareds_by_Pos
	 Is_in_Declareds_by_Pos
	 Not_eq_AxiomDefs_by_Pos
	 Are_Standard_Ops
	 Are_Functions
	 Are_not_Functions
	 Is_Recursive_Function
	 Not_Recursive_Function
	 Eq_Declareds_by_Pos
	 Eq_Declared_by_Pos
	 Eq_Pos
	 Eq_Line_Pos
	 Eq_Ident

	 --  Sweeps
	 Collect_Type_ids
	 Collect_Value_ids
	 Collect_Value_id_Variant
	 Collect_Pos
	 Collect_IdsInPattern
	 Collect_Ops_infix_occ
	 Collect_Ops_prefix_occ
	 Collect_Redef_Opers

	 -- Precedences
	 PVS_lower_precedence
	 PVS_connective_precedence
	 PVS_id_operator_precedence
	 PVS_infix_precedence

	 PVSBindings_to_expr

	 -- Prints
	 -- auxiliary for debugging
	 Print_if_Id_in_Declareds_s
	 Print_if_Id_in_Declareds
	 Print_if_Id_in_Declared
	 PrintTheoryElements
	 PrintTheoryElement
	 PrintTheoryDecl
	 PrintConstDecl
	 PrintTotalDeclaredsCard
	 PrintTotalDeclareds  -- print var TotalDeclareds
	 PrintDeclareds_s
	 PrintDeclareds
	 PrintDeclared
	 PrintImporting
	 Print_Valueid_Id
	 Print_Value_id
	 Print_Type_id
	 PrintIdOp
	 PrintId
	 Print_Axiom_id
	 Print_Object_ids
	 Print_Object_id
	 Print_Scheme_id
	 Print_Theory_id
	 PrintLetDefs
	 PrintLetDef
	 PrintLetBinding


--------------------------------------------------
--   Variables
--------------------------------------------------

--------------------------------------------------
'var' IsTheoryOrDevtReln	 : ISTHEORY

'var' TopIsTheoryOrDevtReln	 : ISTHEORY

--------------------------------------------------
'var' Importings	 : IDENTS

--------------------------------------------------
'var' TotalDeclareds	 : DECLAREDS_S

--------------------------------------------------
-- Used to generate different THEORY Identifiers
'var' TheoryIndex		 : INT

--------------------------------------------------
-- used to map original to new theory ids
'var' TheoryIdMap	: THEORY_ID_MAP

--------------------------------------------------
--  Actions
--------------------------------------------------



--------------------------------------------------
--  Miscelaneus
--------------------------------------------------


--------------------------------------------------
'action' Gen_Theory_Name(STRING -> STRING)
	 
  'rule' Gen_Theory_Name(IdStrng -> TheoryStrng):
	 (|
	   eq(IdStrng, "")
	   where("Ax_" -> TheoryStrng1)
	 ||
	   where(IdStrng -> TheoryStrng1)
	 |)
	 TheoryIndex -> TheoryIndex1
	 TheoryIndex <- TheoryIndex1 + 1
	 TheoryIndex -> TheoryIndex2
	 TheoryIndex <- TheoryIndex2

	 Int_to_string(TheoryIndex2 -> TheoryIndxStrng)
	 Concatenate3(TheoryStrng1, TheoryIndxStrng, "_"
                      -> TheoryStrng)


--------------------------------------------------
'condition' Get_Pos_in_Declareds(DECLAREDS, POS_LIST -> POS_LIST)

  'rule' Get_Pos_in_Declareds(list(Declrd, DeclrdsTail), OptPos -> PosOut):
	 Get_Pos_in_Declared(Declrd -> PosOut1)
	 Conc_Pos(OptPos, PosOut1 -> PosOut2)
	 Get_Pos_in_Declareds(DeclrdsTail, PosOut2 -> PosOut)

  'rule' Get_Pos_in_Declareds(nil, OptPos -> OptPos):

--------------------------------------------------
'condition' Get_Pos_in_Declared(DECLARED -> POS_LIST)

  'rule' Get_Pos_in_Declared(type_item(Typeid) -> PosOut):
	 Typeid'Pos -> Pos
	 where(POS_LIST'list(Pos, nil) -> PosOut)

  'rule' Get_Pos_in_Declared(value_item(Valueid) -> PosOut):
	 Valueid'Pos -> Pos
	 where(POS_LIST'list(Pos, nil) -> PosOut)

  'rule' Get_Pos_in_Declared(axiom_item(Axiomid) -> PosOut):
	 Axiomid'Pos -> Pos
	 where(POS_LIST'list(Pos, nil) -> PosOut)

  'rule' Get_Pos_in_Declared(lemma_item(Axiomid) -> PosOut):
	 Axiomid'Pos -> Pos
	 where(POS_LIST'list(Pos, nil) -> PosOut)

  'rule' Get_Pos_in_Declared(rec_fun_item(Valueid) -> PosOut):
	 Valueid'Pos -> Pos
	 where(POS_LIST'list(Pos, nil) -> PosOut)

  'rule' Get_Pos_in_Declared(mut_rec_fun_item(Valueid) -> PosOut):
	 Valueid'Pos -> Pos
	 where(POS_LIST'list(Pos, nil) -> PosOut)

  'rule' Get_Pos_in_Declared(rec_item(Declareds) -> PosOut):
	 Get_Pos_in_Declareds(Declareds, nil -> PosOut)

  'rule' Get_Pos_in_Declared(mark_item(String) -> PosOut):
	 where(POS_LIST'nil -> PosOut)

  'rule' Get_Pos_in_Declared(nil -> PosOut):
	 where(POS_LIST'nil -> PosOut)

--------------------------------------------------
'action' PVS_Literal_to_Ident(PVS_EXPR -> IDENT)
         
  'rule' PVS_Literal_to_Ident(literal_expr(bool_true) -> Ident):
	 string_to_id("true" -> Ident)
        
  'rule' PVS_Literal_to_Ident(literal_expr(bool_false) -> Ident):
	 string_to_id("false" -> Ident)
	
  'rule' PVS_Literal_to_Ident(literal_expr(int(Ident)) -> Ident):
	
  'rule' PVS_Literal_to_Ident(literal_expr(real(Ident)) -> Ident):
	 
  'rule' PVS_Literal_to_Ident(literal_expr(text(Val)) -> Ident):
	 string_to_id(Val -> Ident)
	 
  'rule' PVS_Literal_to_Ident(literal_expr(char(Val)) -> Ident):
	 Char_to_string(Val -> String)
	 string_to_id(String -> Ident)
	 
  'rule' PVS_Literal_to_Ident(Expr -> Ident):
	 print("ERR - internal, PVS to lit, not lit")
	 string_to_id("ERR" -> Ident)


--------------------------------------------------
'action' WriteFile_Name(NAME)
	 
  'rule' WriteFile_Name(name(Pos, id_op(Id))):
	 C_id_to_string(Id -> IdString)
	 WriteFile(IdString)
	 
  'rule' WriteFile_Name(name(Pos, op_op(Op))):
	 WriteFile("Operator")
	 
  'rule' WriteFile_Name(qual_name(Pos, ObjExpr, id_op(Id))):
	 C_id_to_string(Id -> IdString)
	 WriteFile(IdString)
	 
  'rule' WriteFile_Name(qual_name(Pos, ObjExpr, op_op(Op))):
	 WriteFile("Operator")



--------------------------------------------------
'action' SetIsTheory

  'rule' SetIsTheory:
	 IsTheoryOrDevtReln <- theory


--------------------------------------------------
'action' SetNotTheory

  'rule' SetNotTheory:
	 IsTheoryOrDevtReln <- nil


--------------------------------------------------
'condition' IsTheory

  'rule' IsTheory:
	 IsTheoryOrDevtReln -> X
	 eq(X, theory)



--------------------------------------------------
--------------------------------------------------
'action' SetTopIsTheory

  'rule' SetTopIsTheory:
	 TopIsTheoryOrDevtReln <- theory


--------------------------------------------------
'action' SetTopNotTheory

  'rule' SetTopNotTheory:
	 TopIsTheoryOrDevtReln <- nil


--------------------------------------------------
'condition' TopIsTheory

  'rule' TopIsTheory:
	 TopIsTheoryOrDevtReln -> X
	 eq(X, theory)



--------------------------------------------------
--  To manage variable TheoryIndex
--------------------------------------------------

--------------------------------------------------
'action' Init_TheoryIndex

  'rule' Init_TheoryIndex
	 TheoryIndex <- 0



--------------------------------------------------
--  To manage variable Importings
--------------------------------------------------

--------------------------------------------------
'action' Init_Importings

  'rule' Init_Importings
	 Importings <- nil


--------------------------------------------------
'action' Add_Importings(IDENTS -> IDENTS)

-- adds idents not already imported: returns those new ones
-- ie the ones that need to be imported
  'rule' Add_Importings(Ids -> Ids1):
	 Importings -> Imps
	 Add_idents(Ids, Imps -> Ids1, Imps1)
	 Importings <- Imps1

'action' Add_idents(IDENTS, IDENTS -> IDENTS, IDENTS)

  'rule' Add_idents(list(Id, Ids), Ids1 -> New, Added):
	 (|
	   Isin_ids(Id, Ids1)
	   Add_idents(Ids, Ids1 -> New, Added)
	 ||
	   Add_idents(Ids, Ids1 -> New1, Added1)
	   where(IDENTS'list(Id, New1) -> New)
	   where(IDENTS'list(Id, Added1) -> Added)
	 |)

  'rule' Add_idents(nil, Ids -> nil, Ids):

'condition' Isin_ids(IDENT, IDENTS)

  'rule' Isin_ids(Id0, list(Id, Ids)):
	 (| eq(Id0, Id) || Isin_ids(Id0, Ids) |)


--------------------------------------------------
--  To manage variable TotalDeclareds
--------------------------------------------------

--------------------------------------------------
'action' Init_TotalDeclareds

  'rule' Init_TotalDeclareds
	 TotalDeclareds <- nil


--------------------------------------------------
'action' Add_Declareds(DECLAREDS)

  'rule' Add_Declareds(Declrds):
	 (|
	   TotalDeclareds -> list(Declrds1, Declrds_s)
	   Conc_Declareds(Declrds1, Declrds -> Declrds2)
	   TotalDeclareds <- list(Declrds2, Declrds_s)
         ||
	   TotalDeclareds -> nil
	   TotalDeclareds <- list(Declrds, nil)
         |)


--------------------------------------------------
'action' Add_Declared(DECLARED)

  'rule' Add_Declared(Declrd):
	 (|
	   TotalDeclareds -> list(Declrds, Declrds_s)
	   TotalDeclareds <- list(list(Declrd, Declrds), Declrds_s)
         ||
	   TotalDeclareds -> nil
	   TotalDeclareds <- list(list(Declrd, nil), nil)
         |)

--------------------------------------------------
'action' Open_TotalDeclareds

  'rule' Open_TotalDeclareds
	 TotalDeclareds -> X
	 TotalDeclareds <- list(nil, X)

--------------------------------------------------
'action' Close_TotalDeclareds

  'rule' Close_TotalDeclareds
	 TotalDeclareds -> list(_, X)
	 TotalDeclareds <- X

--------------------------------------------------
'action' Get_TotalDeclareds(-> DECLAREDS_S)

  'rule' Get_TotalDeclareds(-> TotalDeclds):
	 TotalDeclareds -> TotalDeclds

--------------------------------------------------
'condition' Find_Declared(DECLARED)

  'rule' Find_Declared(Declrd):
	 TotalDeclareds -> Declrds_s
	 Find_Declared_s(Declrd, Declrds_s)


--------------------------------------------------
'condition' Find_Declared_s(DECLARED, DECLAREDS_S)

  'rule' Find_Declared_s(Declrd, list(Declrds, Declrds_s)):
	 (|
	   Find_Declared_s(Declrd, list(Declrds, nil))
	 ||
	   Find_Declared_s(Declrd, Declrds_s)
	 |)

--------------------------------------------------
--  to manage TheoryIdMap
--------------------------------------------------
'action' InitTheoryIdMap

  'rule' InitTheoryIdMap:
	 TheoryIdMap <- nil

'action' AddTheory(Object_id -> IDENT)

  'rule' AddTheory(I -> Id1):
	 TheoryIdMap -> Map
	 I'Ident -> Id
	 AddTheory1(I, Id, Map, 1 -> Id1)

'action' AddTheory1(Object_id, IDENT, THEORY_ID_MAP, INT -> IDENT)

  'rule' AddTheory1(I, New, theory_map(I1, New1, Map), N -> Id):
	 (|
	   eq(I, I1) -- nothing to do
	   where(New1 -> Id)
	 ||
	   I'Pos -> P
	   I1'Pos -> P1
	   eq(P, P1) -- nothing to do
	   where(New1 -> Id)
	 ||
	   eq(New, New1)
	   I'Ident -> Orig
	   id_to_string(Orig -> S)
	   Make_concatenation(S, N -> S1)
	   string_to_id(S1 -> New2)
	   TheoryIdMap -> AllMap
	   AddTheory1(I, New2, AllMap, N+1 -> Id)
	 ||
	   AddTheory1(I, New, Map, N -> Id)
	 |)

  'rule' AddTheory1(I, New, nil, _ -> New):
	 TheoryIdMap -> AllMap
	 TheoryIdMap <- theory_map(I, New, AllMap)
-- I'Pos -> P
-- PrintPos(P)
-- I'Ident -> Id
-- Print_id(Id)
-- Putmsg(" mapped to ")
-- Print_id(New)
-- Putnl
-- PrintTheoryIdMap

'action' GetTheoryId(Object_id -> IDENT)

  'rule' GetTheoryId(I -> Id):
	 TheoryIdMap -> Map
	 GetTheoryId1(I, Map -> Id)

'action' GetTheoryId1(Object_id, THEORY_ID_MAP -> IDENT)

  'rule' GetTheoryId1(I, theory_map(I1, New1, Map) -> Id):
	 (|
	   eq(I, I1)
	   where(New1 -> Id)
	 ||
	   GetTheoryId1(I, Map -> Id)
	 |)

-- in case used before defined
  'rule' GetTheoryId1(I, nil -> Id):
	 AddTheory(I -> Id)
-- I'Pos -> P
-- PrintPos(P)
-- I'Ident -> Orig
-- Print_id(Orig)
-- Putmsg(" mapped (before defined) to ")
-- Print_id(Id)
-- Putnl
-- PrintTheoryIdMap

-- for debugging
'action' PrintTheoryIdMap

  'rule' PrintTheoryIdMap:
	 TheoryIdMap -> Map
	 PrintTheoryIdMap1(Map)

'action' PrintTheoryIdMap1(THEORY_ID_MAP)

  'rule' PrintTheoryIdMap1(theory_map(I, New, Map)):
	 I'Ident -> Id
	 Print_id(Id)
	 Putmsg(" maps to ")
	 Print_id(New)
	 Putnl
	 PrintTheoryIdMap1(Map)

  'rule' PrintTheoryIdMap1(nil):
	 	 
	 


	 



--------------------------------------------------
--  Concatenates
--------------------------------------------------


--------------------------------------------------
-- Conc_Declareds(Ds, Ds1 -> Ds ^ Ds1)
'action' Conc_Declareds(DECLAREDS, DECLAREDS -> DECLAREDS)

  'rule' Conc_Declareds(list(Declared, Declareds), Declareds1 -> list(Declared, Declareds2)):
         Conc_Declareds(Declareds, Declareds1 -> Declareds2)

  'rule' Conc_Declareds(nil, Declareds -> Declareds):



--------------------------------------------------
'action' Conc_Bindings(BINDINGS, BINDINGS -> BINDINGS)

  'rule' Conc_Bindings(list(Elem, Elems), Elems1 -> list(Elem, Elems2)):
	 Conc_Bindings(Elems, Elems1 -> Elems2)

  'rule' Conc_Bindings(nil, Elems -> Elems):




--------------------------------------------------
'action' Conc_IdentList(IDENTS, IDENTS -> IDENTS)

  'rule' Conc_IdentList(list(Elem, Elems), Elems1 -> list(Elem, Elems2)):
	 Conc_IdentList(Elems, Elems1 -> Elems2)

  'rule' Conc_IdentList(nil, Elems -> Elems):



--------------------------------------------------
'action' Conc_PVSBindings(PVS_BINDINGS, PVS_BINDINGS -> PVS_BINDINGS)

  'rule' Conc_PVSBindings(list(Elem, Elems), Elems1 -> list(Elem, Elems2)):
	 Conc_PVSBindings(Elems, Elems1 -> Elems2)

  'rule' Conc_PVSBindings(nil, Elems -> Elems):


--------------------------------------------------
'action' Conc_PVS_Opt_Pos(PVS_OPT_POS_S, PVS_OPT_POS_S -> PVS_OPT_POS_S)

  'rule' Conc_PVS_Opt_Pos(list(Elem, Elems), Elems1 -> list(Elem, Elems2)):
	 Conc_PVS_Opt_Pos(Elems, Elems1 -> Elems2)

  'rule' Conc_PVS_Opt_Pos(nil, Elems -> Elems):


--------------------------------------------------
'action' Conc_Pos(POS_LIST, POS_LIST -> POS_LIST)

  'rule' Conc_Pos(list(Elem, Elems), Elems1 -> list(Elem, Elems2)):
	 Conc_Pos(Elems, Elems1 -> Elems2)

  'rule' Conc_Pos(nil, Elems -> Elems):
			 


--------------------------------------------------
--  Inserts
--------------------------------------------------

--------------------------------------------------
-- Insert_Binding(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_Binding(BINDING, BINDINGS -> BINDINGS)

  'rule' Insert_Binding(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_Binding(Elem, ElemsTail -> Elems1)

  'rule' Insert_Binding(Elem, nil -> list(Elem, nil)):

--------------------------------------------------
-- Insert_Declared(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_Declared(DECLARED, DECLAREDS -> DECLAREDS)

  'rule' Insert_Declared(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_Declared(Elem, ElemsTail -> Elems1)

  'rule' Insert_Declared(Elem, nil -> list(Elem, nil)):

--------------------------------------------------
-- Push_Declared(Elem, Elems -> <Elem> ^ Elems)
'action' Push_Declared(DECLARED, DECLAREDS -> DECLAREDS)

  'rule' Push_Declared(Elem, Elems -> list(Elem, Elems)):


--not used
--------------------------------------------------
-- Insert_union_Binding(A, A_List -> if A is not in A_List then A_List ^ <A>)
'action' Insert_u_Binding(BINDING, BINDINGS -> BINDINGS)

  'rule' Insert_u_Binding(A, list(A1, A_ListTail) -> list(A1, A_List1)):
         (|
           eq(A, A1)
           where(A_ListTail -> A_List1)
         ||
           Insert_u_Binding(A, A_ListTail -> A_List1)
         |) 

  'rule' Insert_u_Binding(A, nil -> list(A, nil)):


--------------------------------------------------
-- Insert_u_Declared(Decled, Decleds -> if Decled is not in then Decls ^ <Decled>)
'action' Insert_u_Declared(DECLARED, DECLAREDS -> DECLAREDS)

  'rule' Insert_u_Declared(Decled, list(Decled1, DecledsTail) -> list(Decled1, Decleds1)):
         (|
           eq(Decled, Decled1)
           where(DecledsTail -> Decleds1)
         ||
           Insert_u_Declared(Decled, DecledsTail -> Decleds1)
         |) 

  'rule' Insert_u_Declared(Decled, nil -> list(Decled, nil)):


--------------------------------------------------
-- Insert_(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_TypeExpr(PVS_TYPE_EXPR, PVS_TYPE_EXPRS -> PVS_TYPE_EXPRS)

  'rule' Insert_TypeExpr(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_TypeExpr(Elem, ElemsTail -> Elems1)

  'rule' Insert_TypeExpr(Elem, nil -> list(Elem, nil)):
			 

--------------------------------------------------
-- Insert_(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_DataTypePart(DATA_TYPE_PART, DATA_TYPE_PARTS -> DATA_TYPE_PARTS)

  'rule' Insert_DataTypePart(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_DataTypePart(Elem, ElemsTail -> Elems1)

  'rule' Insert_DataTypePart(Elem, nil -> list(Elem, nil)):
			 

--------------------------------------------------
-- Insert_(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_Accesor(ACCESOR, ACCESORS -> ACCESORS)

  'rule' Insert_Accesor(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_Accesor(Elem, ElemsTail -> Elems1)

  'rule' Insert_Accesor(Elem, nil -> list(Elem, nil)):
	 

--------------------------------------------------
-- Insert_(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_SetBinding(SETBINDING, SETBINDINGS -> SETBINDINGS)

  'rule' Insert_SetBinding(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_SetBinding(Elem, ElemsTail -> Elems1)

  'rule' Insert_SetBinding(Elem, nil -> list(Elem, nil)):
		 

--------------------------------------------------
-- Insert_(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_LambdaBinding(LAMBDABINDING, LAMBDABINDINGS -> LAMBDABINDINGS)

  'rule' Insert_LambdaBinding(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_LambdaBinding(Elem, ElemsTail -> Elems1)

  'rule' Insert_LambdaBinding(Elem, nil -> list(Elem, nil)):
			 

--------------------------------------------------
-- Insert_(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_LetBinding(LETBINDING, LETBINDINGS -> LETBINDINGS)

  'rule' Insert_LetBinding(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_LetBinding(Elem, ElemsTail -> Elems1)

  'rule' Insert_LetBinding(Elem, nil -> list(Elem, nil)):
			 

--------------------------------------------------
-- Insert_(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_LetBind(LETBIND, LETBINDS -> LETBINDS)

  'rule' Insert_LetBind(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_LetBind(Elem, ElemsTail -> Elems1)

  'rule' Insert_LetBind(Elem, nil -> list(Elem, nil)):
		 

--------------------------------------------------
-- Insert_PVSBinding(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_PVSBinding(PVS_BINDING, PVS_BINDINGS -> PVS_BINDINGS)

  'rule' Insert_PVSBinding(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_PVSBinding(Elem, ElemsTail -> Elems1)

  'rule' Insert_PVSBinding(Elem, nil -> list(Elem, nil)):

--------------------------------------------------
-- Insert_Arguments(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_Arguments(ARGUMENTS, ARGUMENTS_LIST -> ARGUMENTS_LIST)

  'rule' Insert_Arguments(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_Arguments(Elem, ElemsTail -> Elems1)

  'rule' Insert_Arguments(Elem, nil -> list(Elem, nil)):

--------------------------------------------------
-- Insert_(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_PVSFormal_Parameters(PVS_BINDINGS, PVS_FORMAL_FUN_PARAMETERS
                                     -> PVS_FORMAL_FUN_PARAMETERS)

  'rule' Insert_PVSFormal_Parameters(Elem, list(Elem1, ElemsTail)
                                     -> list(Elem1, Elems1)):
	 Insert_PVSFormal_Parameters(Elem, ElemsTail -> Elems1)

  'rule' Insert_PVSFormal_Parameters(Elem, nil -> list(Elem, nil)):



--------------------------------------------------
-- Insert_Theory_Element(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_Theory_Element(THEORY_ELEMENT, THEORY_ELEMENTS -> THEORY_ELEMENTS)

  'rule' Insert_Theory_Element(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_Theory_Element(Elem, ElemsTail -> Elems1)

  'rule' Insert_Theory_Element(Elem, nil -> list(Elem, nil)):




--------------------------------------------------
-- Insert_Tuple(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_Tuple(TUPLE, TUPLE_LIST -> TUPLE_LIST)

  'rule' Insert_Tuple(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_Tuple(Elem, ElemsTail -> Elems1)

  'rule' Insert_Tuple(Elem, nil -> list(Elem, nil)):



--------------------------------------------------
-- Insert_PVS_Expr(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_PVS_Expr(PVS_EXPR, PVS_EXPRS -> PVS_EXPRS)

  'rule' Insert_PVS_Expr(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_PVS_Expr(Elem, ElemsTail -> Elems1)

  'rule' Insert_PVS_Expr(Elem, nil -> list(Elem, nil)):



--------------------------------------------------
-- Insert_PVS_ExprPair(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_PVS_ExprPair(PVS_EXPR_PAIR, PVS_EXPR_PAIRS -> PVS_EXPR_PAIRS)

  'rule' Insert_PVS_ExprPair(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_PVS_ExprPair(Elem, ElemsTail -> Elems1)

  'rule' Insert_PVS_ExprPair(Elem, nil -> list(Elem, nil)):



--------------------------------------------------
-- Insert_(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_Elsif(PVS_ELSIF_BRANCH, PVS_ELSIF_BRANCHES -> PVS_ELSIF_BRANCHES)

  'rule' Insert_Elsif(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_Elsif(Elem, ElemsTail -> Elems1)

  'rule' Insert_Elsif(Elem, nil -> list(Elem, nil)):



--------------------------------------------------
-- Insert_(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_Projection(INT, PROJECTION_LIST -> PROJECTION_LIST)

  'rule' Insert_Projection(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_Projection(Elem, ElemsTail -> Elems1)

  'rule' Insert_Projection(Elem, nil -> list(Elem, nil)):
		 

--------------------------------------------------
-- Insert_(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_IdOp(ID_OP, ID_OP_S -> ID_OP_S)

  'rule' Insert_IdOp(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 Insert_IdOp(Elem, ElemsTail -> Elems1)

  'rule' Insert_IdOp(Elem, nil -> list(Elem, nil)):
		 

--------------------------------------------------
-- Insert_(Elem, Elems -> Elems ^ <Elem>)
'action' Insert_Ident(IDENT, IDENTS -> IDENTS)

  'rule' Insert_Ident(Elem, list(Elem1, ElemsTail) -> list(Elem1, Elems1)):
	 (|
	   eq(Elem, Elem1)
	   where(ElemsTail -> Elems1)
	 ||
	   Insert_Ident(Elem, ElemsTail -> Elems1)
	 |)

  'rule' Insert_Ident(Elem, nil -> list(Elem, nil)):
		 

--------------------------------------------------
--  Subtracts
--------------------------------------------------


--------------------------------------------------
-- Subtract(A, B -> C = A\B)
'action' Subtract_Theory_Elems(THEORY_ELEMENTS, THEORY_ELEMENTS -> THEORY_ELEMENTS)

  'rule' Subtract_Theory_Elems(list(A_Elem, A_Tail), B -> C):
	 Subtract_Theory_Elems(A_Tail, B -> C1)
	 (|
	   Not_in_Theory_Elems(A_Elem, B)
	   where(THEORY_ELEMENTS'list(A_Elem, C1) -> C)
	 ||
	   where(C1 -> C)
	 |)

  'rule' Subtract_Theory_Elems(nil, _ -> nil):


--------------------------------------------------
-- Subtract(D, v1 -> {v in D | v <> v1})
'action' Substract_Valueid(DECLAREDS, Value_id -> DECLAREDS)

  'rule' Substract_Valueid(list(value_item(Valueid1), DeclrdsTail),
                                        Valueid
                                         -> Declaredsout):
         Substract_Valueid(DeclrdsTail, Valueid -> Declareds1)
         (|
           ne(Valueid, Valueid1)
           where(DECLAREDS'list(value_item(Valueid1), Declareds1)
	         -> Declaredsout)
         ||
           where(Declareds1 -> Declaredsout)
         |)
 
  'rule' Substract_Valueid(list(type_item(Typeid), Tail), Valueid
                                         -> Declaredsout):
         Substract_Valueid(Tail, Valueid -> Declaredsout)
 
  'rule' Substract_Valueid(list(axiom_item(A), Tail), Valueid
                                         -> Declaredsout):
         Substract_Valueid(Tail, Valueid -> Declaredsout)
         
  'rule' Substract_Valueid(nil, Valueid -> nil):


--------------------------------------------------
-- Subtract(D, B -> {x in D | x'id not in B})
'action' Substract_Declareds_in_Bindings(DECLAREDS, BINDINGS -> DECLAREDS)

  'rule' Substract_Declareds_in_Bindings(list(value_item(Valueid), DeclrdsTail),
                                         Bindings
                                         -> Declaredsout):
         Substract_Declareds_in_Bindings(DeclrdsTail, Bindings -> Declareds1)
         (|
           Valueid'Pos -> PosValueid
           Not_in_Bindings(PosValueid, Bindings)
           where(DECLAREDS'list(value_item(Valueid), Declareds1) -> Declaredsout)
         ||
           where(Declareds1 -> Declaredsout)
         |)
 
  'rule' Substract_Declareds_in_Bindings(list(type_item(Typeid), Tail), Bindings
                                         -> Declaredsout):
         Substract_Declareds_in_Bindings(Tail, Bindings -> Declareds1)
         (|
           Typeid'Pos -> PosTypeid
           Not_in_Bindings(PosTypeid, Bindings)
           where(DECLAREDS'list(type_item(Typeid), Declareds1) -> Declaredsout)
         ||
           where(Declareds1 -> Declaredsout)
         |)
 
  'rule' Substract_Declareds_in_Bindings(list(axiom_item(A), Tail), Bindings
                                         -> Declaredsout):
         Substract_Declareds_in_Bindings(Tail, Bindings -> Declaredsout)
         
  'rule' Substract_Declareds_in_Bindings(nil, Bindings -> nil):


--------------------------------------------------
-- Subtract(A, B -> A\B)
'action' Substract_Declareds_s(DECLAREDS, DECLAREDS_S -> DECLAREDS)

  'rule' Substract_Declareds_s(DecledsIn,
                               list(Decleds, Decleds_sTail)
                               -> DecledsOut):

         Substract_Declareds_by_Pos(DecledsIn, Decleds
                                    -> DecledsOut1)
         (|
           eq(DecledsOut1, nil)
           where(DecledsOut1 -> DecledsOut)
         ||
           Substract_Declareds_s(DecledsOut1, Decleds_sTail
                                 -> DecledsOut)
         |)

  'rule' Substract_Declareds_s(nil, _ -> nil):

  'rule' Substract_Declareds_s(DecledsIn, nil
                               -> DecledsIn):


--------------------------------------------------
-- Subtract(A, B -> A\B)
'action' Substract_Declareds(DECLAREDS, DECLAREDS -> DECLAREDS)

  'rule' Substract_Declareds(list(A_Decled, A_Tail), B -> C):

         Substract_Declareds(A_Tail, B -> C1)
         (|
           Not_in_Declareds(A_Decled, B)
           where(DECLAREDS'list(A_Decled, C1) -> C)
         ||
           where(C1 -> C)
         |)

  'rule' Substract_Declareds(nil, _ -> nil):


--------------------------------------------------
-- Subtract(A, B -> A\B)
'action' Substract_Declareds_by_Pos(DECLAREDS, DECLAREDS -> DECLAREDS)

  'rule' Substract_Declareds_by_Pos(list(A_Decled, A_Tail), B -> C):

         Substract_Declareds_by_Pos(A_Tail, B -> C1)
         (|
           Is_in_Declareds_by_Pos(A_Decled, B)
           where(C1 -> C)
         ||
           where(DECLAREDS'list(A_Decled, C1) -> C)
         |)

  'rule' Substract_Declareds_by_Pos(nil, _ -> nil):


--------------------------------------------------
-- Subtract(A, B -> B+(A\all built in operators in A))
'action' Substract_Built_in_Ops(DECLAREDS, DECLAREDS -> DECLAREDS)

  'rule' Substract_Built_in_Ops(list(value_item(Valueid), DeclsTail),
                                DeclsIn -> DeclsOut):
         Valueid'Ident -> IdorOp
         Valueid'Pos -> Pos
	 (|
	   where(IdorOp -> op_op(Op))
	   (|
	     Built_in(Op, Valueid)
	     where(DeclsIn -> Decls1)
	   ||
             Insert_Declared(value_item(Valueid), DeclsIn
                             -> Decls1)
           |)
	 ||
	   where(DeclsIn -> Decls1)
         |)
	 Substract_Built_in_Ops(DeclsTail, Decls1 -> DeclsOut)

  'rule' Substract_Built_in_Ops(nil, Decls -> Decls):


--------------------------------------------------
--  Reverse lists
--------------------------------------------------

--------------------------------------------------
-- Reverses a list of Declareds
'action' Rev_Declareds(DECLAREDS, DECLAREDS -> DECLAREDS)

  'rule' Rev_Declareds(ListIn, ListAux -> ListOut):
         (|
           where(ListIn -> list(Elem, ListTail))
           Rev_Declareds(ListTail, list(Elem, ListAux) -> ListOut)
         ||
           where(ListIn -> nil)
           where(ListAux -> ListOut)
         |)

--------------------------------------------------
--  Conditions
--------------------------------------------------


--------------------------------------------------
'condition' Not_in_Theory_Elems(THEORY_ELEMENT, THEORY_ELEMENTS)

  'rule' Not_in_Theory_Elems(TheoryElem, list(TheoryElem2, TheoryElemsTail)):
	 ne(TheoryElem, TheoryElem2)
	 Not_in_Theory_Elems(TheoryElem, TheoryElemsTail)

  'rule' Not_in_Theory_Elems(TheoryElem, nil):

--------------------------------------------------
'condition' Not_in_Bindings(POS, BINDINGS)

  'rule' Not_in_Bindings(PosValueid, list(single(Pos, IdOp), BindingsTail)):
         ne(PosValueid, Pos)
         Not_in_Bindings(PosValueid, BindingsTail)

  'rule' Not_in_Bindings(PosValueid, nil):


--------------------------------------------------
'condition' Not_Eq_PosList(POS_LIST, POS_LIST)

  'rule' Not_Eq_PosList(list(Pos1, PosList1Tail),
                        list(Pos2, PosList2Tail)):
         ne(Pos1, Pos2)
         Not_Eq_PosList(PosList1Tail, PosList2Tail)

  'rule' Not_Eq_PosList(nil, nil):


--------------------------------------------------
'condition' Not_in_Declareds(DECLARED, DECLAREDS)

  'rule' Not_in_Declareds(Decled, list(Decled2, DecledsTail)):
         ne(Decled, Decled2)
         Not_in_Declareds(Decled, DecledsTail)

  'rule' Not_in_Declareds(Decled, nil):


--------------------------------------------------
'condition' Not_in_Declareds_by_Pos(DECLARED, DECLAREDS)

  'rule' Not_in_Declareds_by_Pos(Declrd1, list(Declrd2, DeclrdsTail)):
--	 Not_eq_Declared_by_Pos(Declrd1, Declrd2)
	 Not_in_Declareds_by_Pos(Declrd1, DeclrdsTail)

  'rule' Not_in_Declareds_by_Pos(Declrd1, nil):


--------------------------------------------------
'condition' Is_in_Declareds_by_Pos(DECLARED, DECLAREDS)

  'rule' Is_in_Declareds_by_Pos(Declrd1, list(Declrd2, DeclrdsTail)):
         (|
	   Eq_Declared_by_Pos(Declrd1, Declrd2)
         ||
	   Is_in_Declareds_by_Pos(Declrd1, DeclrdsTail)
         |)

/*
--------------------------------------------------
'condition' Not_in_Declareds_by_Pos(DECLARED, DECLAREDS)

  'rule' Not_in_Declareds_by_Pos(type_item(Typeid),
                                 list(type_item(Typeid2), DecledsTail)):
	 Typeid'Pos -> Pos
	 Typeid2'Pos -> Pos2
	 ne(Pos, Pos2)
         Not_in_Declareds_by_Pos(type_item(Typeid), DecledsTail)

  'rule' Not_in_Declareds_by_Pos(value_item(Valueid),
                                 list(value_item(Valueid2), DecledsTail)):
	 Valueid'Pos -> Pos
	 Valueid2'Pos -> Pos2
	 ne(Pos, Pos2)
         Not_in_Declareds_by_Pos(value_item(Valueid), DecledsTail)

  'rule' Not_in_Declareds_by_Pos(axiom_item(Axiomid),
                                 list(axiom_item(Axiomid2), DecledsTail)):
	 Axiomid'Pos -> Pos
	 Axiomid2'Pos -> Pos2
	 ne(Pos, Pos2)
         Not_in_Declareds_by_Pos(axiom_item(Axiomid), DecledsTail)

  'rule' Not_in_Declareds_by_Pos(lemma_item(Axiomid),
                                 list(lemma_item(Axiomid2), DecledsTail)):
	 Axiomid'Pos -> Pos
	 Axiomid2'Pos -> Pos2
	 ne(Pos, Pos2)
         Not_in_Declareds_by_Pos(lemma_item(Axiomid), DecledsTail)

  'rule' Not_in_Declareds_by_Pos(rec_fun_item(Valueid),
                                 list(rec_fun_item(Valueid2), DecledsTail)):
	 Valueid'Pos -> Pos
	 Valueid2'Pos -> Pos2
	 ne(Pos, Pos2)
         Not_in_Declareds_by_Pos(rec_fun_item(Valueid), DecledsTail)

  'rule' Not_in_Declareds_by_Pos(mut_rec_fun_item(Valueid),
                                 list(mut_rec_fun_item(Valueid2), DecledsTail)):
	 Valueid'Pos -> Pos
	 Valueid2'Pos -> Pos2
	 ne(Pos, Pos2)
         Not_in_Declareds_by_Pos(mut_rec_fun_item(Valueid), DecledsTail)

  'rule' Not_in_Declareds_by_Pos(rec_item(Declareds),
                                 list(rec_item(Declareds2), DecledsTail)):
         Not_eq_Declareds_by_Pos(Declareds, Declareds2)
         Not_in_Declareds_by_Pos(rec_item(Declareds), DecledsTail)

  'rule' Not_in_Declareds_by_Pos(mark_item(String),
                                 list(mark_item(String2), DecledsTail)):
	 ne(String, String2)
         Not_in_Declareds_by_Pos(mark_item(String), DecledsTail)

  'rule' Not_in_Declareds_by_Pos(Decled, nil):
*/
--------------------------------------------------
'condition' Not_eq_AxiomDefs_by_Pos(AXIOM_DEFS, AXIOM_DEFS)

  'rule' Not_eq_AxiomDefs_by_Pos(list(axiom_def(Pos, _, _), AxiomDefsTail),
                                 list(axiom_def(Pos2, _, _), AxiomDefsTail2)):
	 ne(Pos, Pos2)
	 Not_eq_AxiomDefs_by_Pos(AxiomDefsTail, AxiomDefsTail2)

  'rule' Not_eq_AxiomDefs_by_Pos(AxiomDef, nil):

--------------------------------------------------
'condition' Eq_Declareds_by_Pos(DECLAREDS, DECLAREDS)

  'rule' Eq_Declareds_by_Pos(list(Declrd, DeclrdsTail), list(Declrd2, DeclrdsTail2)):
	 Eq_Declared_by_Pos(Declrd, Declrd2)
	 Eq_Declareds_by_Pos(DeclrdsTail, DeclrdsTail2)

  'rule' Eq_Declareds_by_Pos(nil, nil):

--------------------------------------------------
'condition' Eq_Declared_by_Pos(DECLARED, DECLARED)

  'rule' Eq_Declared_by_Pos(type_item(Typeid), type_item(Typeid2)):
	 Typeid'Pos -> Pos
	 Typeid2'Pos -> Pos2
	 eq(Pos, Pos2)

  'rule' Eq_Declared_by_Pos(value_item(Valueid), value_item(Valueid2)):
	 Valueid'Pos -> Pos
	 Valueid2'Pos -> Pos2
	 eq(Pos, Pos2)

  'rule' Eq_Declared_by_Pos(axiom_item(Axiomid), axiom_item(Axiomid2)):
	 Axiomid'Pos -> Pos
	 Axiomid2'Pos -> Pos2
	 eq(Pos, Pos2)

  'rule' Eq_Declared_by_Pos(lemma_item(Axiomid), lemma_item(Axiomid2)):
	 Axiomid'Pos -> Pos
	 Axiomid2'Pos -> Pos2
	 eq(Pos, Pos2)

  'rule' Eq_Declared_by_Pos(rec_fun_item(Valueid), rec_fun_item(Valueid2)):
	 Valueid'Pos -> Pos
	 Valueid2'Pos -> Pos2
	 eq(Pos, Pos2)

  'rule' Eq_Declared_by_Pos(mut_rec_fun_item(Valueid), mut_rec_fun_item(Valueid2)):
	 Valueid'Pos -> Pos
	 Valueid2'Pos -> Pos2
	 eq(Pos, Pos2)

  'rule' Eq_Declared_by_Pos(rec_item(Declareds), rec_item(Declareds2)):
         Eq_Declareds_by_Pos(Declareds, Declareds2)

  'rule' Eq_Declared_by_Pos(mark_item(String), mark_item(String2)):
	 eq(String, String2)

  'rule' Eq_Declared_by_Pos(nil, nil):


--------------------------------------------------
'condition' Are_Standard_Ops(DECLAREDS, DECLAREDS -> DECLAREDS)

  'rule' Are_Standard_Ops(list(Decl, DeclsTail),
                          Decls -> StdOpDeclsout):
         where(Decl -> value_item(Valueid))
         Valueid'Ident -> IdorOp
         (| -- IdOp is standard?
	   where(IdorOp -> op_op(_))
           Insert_Declared(Decl, Decls -> Decls1)
         ||
           where(Decls -> Decls1)
         |)
         Are_Standard_Ops(DeclsTail, Decls1 -> StdOpDeclsout)

  'rule' Are_Standard_Ops(nil, StdOpDecls -> StdOpDecls):

--------------------------------------------------
'condition' Are_Functions(DECLAREDS, DECLAREDS -> DECLAREDS)

  'rule' Are_Functions(Declsin, Decls -> FunDeclsout):
         Get_Decls_Funct(Declsin, Decls -> FunDeclsout)
	 ne(FunDeclsout, nil)

--  'rule' Are_Functions(nil, Decls -> Decls):


-- auxiliary for action Are_Functions
--------------------------------------------------
'action' Get_Decls_Funct(DECLAREDS, DECLAREDS -> DECLAREDS)

  'rule' Get_Decls_Funct(list(Decl, DeclsTail),
                       Decls -> FunDeclsout):
         where(Decl -> value_item(Valueid))
         Valueid'Def -> ValueDef
         (|
           where(ValueDef -> expl_fun(_, _, _, _, _, _))
           Insert_Declared(Decl, Decls -> Decls1)
           Get_Decls_Funct(DeclsTail, Decls1 -> FunDeclsout)
         ||
           where(ValueDef -> impl_fun(_, _, _, _))
           Insert_Declared(Decl, Decls -> Decls1)
           Get_Decls_Funct(DeclsTail, Decls1 -> FunDeclsout)
         ||
           Get_Decls_Funct(DeclsTail, Decls -> FunDeclsout)
         |)

  'rule' Get_Decls_Funct(list(Decl, DeclsTail),
                       Decls -> NoFunDeclsout):
         Get_Decls_Funct(DeclsTail, Decls -> NoFunDeclsout)

  'rule' Get_Decls_Funct(nil, FunDecls -> FunDecls):

--------------------------------------------------
'condition' Are_not_Functions(DECLAREDS, DECLAREDS -> DECLAREDS)

  'rule' Are_not_Functions(Declsin, Decls -> NoFunDeclsout):
         Get_Decls_not_Funct(Declsin, Decls -> NoFunDeclsout)
	 ne(NoFunDeclsout, nil)

--  'rule' Are_not_Functions(nil, Decls -> Decls):


-- auxiliary for action Are_not_Functions
--------------------------------------------------
'action' Get_Decls_not_Funct(DECLAREDS, DECLAREDS -> DECLAREDS)

  'rule' Get_Decls_not_Funct(list(Decl, DeclsTail),
                       Decls -> NoFunDeclsout):
         where(Decl -> value_item(Valueid))
         Valueid'Def -> ValueDef
         (|
           where(ValueDef -> expl_fun(_, _, _, _, _, _))
           Get_Decls_not_Funct(DeclsTail, Decls -> NoFunDeclsout)
         ||
           where(ValueDef -> impl_fun(_, _, _, _))
           Get_Decls_not_Funct(DeclsTail, Decls -> NoFunDeclsout)
         ||
           Insert_Declared(Decl, Decls -> Decls1)
           Get_Decls_not_Funct(DeclsTail, Decls1 -> NoFunDeclsout)
         |)

  'rule' Get_Decls_not_Funct(list(Decl, DeclsTail),
                       Decls -> NoFunDeclsout):
         Insert_Declared(Decl, Decls -> Decls1)
         Get_Decls_not_Funct(DeclsTail, Decls1 -> NoFunDeclsout)

  'rule' Get_Decls_not_Funct(nil, NoFunDecls -> NoFunDecls):


--------------------------------------------------
-- Fails if Value_id isin DECLAREDS
'condition' Is_Recursive_Function(Value_id, DECLAREDS)

  'rule' Is_Recursive_Function(Valueid1, list(value_item(Valueid2),
                                              DeclsTail)):
         (|
	   eq(Valueid1, Valueid2)
	 ||
	   Is_Recursive_Function(Valueid1, DeclsTail)
	 |)


--------------------------------------------------
-- Fails if Value_id NOT isin DECLAREDS
'condition' Not_Recursive_Function(Value_id, DECLAREDS)

  'rule' Not_Recursive_Function(Valueid1, list(value_item(Valueid2),
                                              DeclsTail)):
	 ne(Valueid1, Valueid2)
	 Not_Recursive_Function(Valueid1, DeclsTail)

  'rule' Not_Recursive_Function(Valueid1, list(_,
                                              DeclsTail)):
	 Not_Recursive_Function(Valueid1, DeclsTail)

  'rule' Not_Recursive_Function(Valueid1, nil):


--------------------------------------------------
'condition' Eq_Pos(POS, STRING)

  'rule' Eq_Pos(Pos, String):
	 PosAsString(Pos -> PosString)
	 eq(PosString, String)

--------------------------------------------------
'condition' Eq_Line_Pos(POS, STRING)

  'rule' Eq_Line_Pos(Pos, String):
	 LinePosAsString(Pos -> PosString)
	 eq(PosString, String)

--------------------------------------------------
'condition' Eq_Ident(IDENT, STRING)

  'rule' Eq_Ident(Id, String):
	 id_to_string(Id -> IdString)
	 eq(IdString, String)


--------------------------------------------------
--  Sweeps
--------------------------------------------------


--------------------------------------------------
'sweep' Collect_Type_ids(ANY, DECLAREDS -> DECLAREDS)

-- ignore disambiguations (can be inserted during resolving)
  'rule' Collect_Type_ids(VALUE_EXPR'disamb(_, V, _), Declareds -> Declareds1):
	 Collect_Type_ids(V, Declareds -> Declareds1)
  
  'rule' Collect_Type_ids(TYPE_EXPR'defined(Typeid, nil), Declareds -> Declareds1):
	 (| -- may be affected by WITH
	   Check_type_defined(defined(Typeid, nil) -> defined(Typeid1, nil))
           Insert_Declared(type_item(Typeid1), Declareds -> Declareds1)
	 ||
	   where(Declareds -> Declareds1)
	 |)

--------------------------------------------------
'sweep' Collect_Value_ids(ANY, DECLAREDS -> DECLAREDS)

  'rule' Collect_Value_ids(VALUE_EXPR'val_occ(_, Valueid, nil), Declareds -> Declareds1):
         Insert_Declared(value_item(Valueid), Declareds -> Declareds1)

  'rule' Collect_Value_ids(VALUE_EXPR'infix_occ(_, L, I, Q, R), Declareds -> Declareds3):
	 Collect_Value_ids(L, Declareds -> Declareds1)
	 (|
	   I'Ident -> op_op(Op)
	   (| Built_in(Op, I) || ne(Q, nil) |)
	   where(Declareds1 -> Declareds2)
	 ||
	   Insert_Declared(value_item(I), Declareds1 -> Declareds2)
	 |)
	 Collect_Value_ids(R, Declareds2 -> Declareds3)

  'rule' Collect_Value_ids(VALUE_EXPR'prefix_occ(_, I, Q, V), Declareds -> Declareds2):
	 (|
	   I'Ident -> op_op(Op)
	   (| Built_in(Op, I) || ne(Q, nil) |)
	   where(Declareds -> Declareds1)
	 ||
	   Insert_Declared(value_item(I), Declareds -> Declareds1)
	 |)
	 Collect_Value_ids(V, Declareds1 -> Declareds2)
  
--------------------------------------------------
'sweep' Collect_Value_id_Variant(ANY, DECLAREDS -> DECLAREDS)

  'rule' Collect_Value_id_Variant(VARIANT'record(Pos, con_ref(Valueid),
                                                 Components),
                                  DeclaredsIn -> DeclaredsOut):
         Insert_Declared(value_item(Valueid), DeclaredsIn -> Declareds1)
	 Collect_Value_id_Variant(Components, Declareds1 -> DeclaredsOut)

  'rule' Collect_Value_id_Variant(COMPONENT'component(Pos,
                                                      dest_ref(Valueid),
                                                      TypeExpr,
                                                      Reconstructor),
                                  DeclaredsIn -> DeclaredsOut):
         Insert_Declared(value_item(Valueid), DeclaredsIn -> Declareds1)
	 (|
	   where(Reconstructor -> recon_ref(Rid))
	   Insert_Declared(value_item(Rid), Declareds1 -> DeclaredsOut)
	 ||
	   where(Declareds1 -> DeclaredsOut)
	 |)  

--------------------------------------------------
'sweep' Collect_Pos(ANY, BINDINGS -> BINDINGS)

  'rule' Collect_Pos(BINDING'single(Pos, IdOp), Bindings -> Bindingsout):
         Insert_Binding(single(Pos, IdOp), Bindings -> Bindingsout)

  'rule' Collect_Pos(id_pattern(Pos, IdOp), Bindings -> Bindingsout):
         Insert_Binding(single(Pos, IdOp), Bindings -> Bindingsout)

--------------------------------------------------
'sweep' Collect_IdsInPattern(ANY, BINDINGS -> BINDINGS)

  'rule' Collect_IdsInPattern(PATTERN'id_pattern(Pos, IdOp),
                              Bindings -> Bindingsout):
         Insert_Binding(BINDING'single(Pos, IdOp), Bindings
                        -> Bindingsout)

  'rule' Collect_IdsInPattern(PATTERN'name_pattern(Pos1, name(Pos2, IdOp)),
                              Bindings -> Bindingsout):
         Insert_Binding(BINDING'single(Pos1, IdOp), Bindings
                        -> Bindingsout)

  'rule' Collect_IdsInPattern(PATTERN'name_pattern(Pos1,
                                                   qual_name(Pos2,
                                                             Qual,
                                                             IdOp)),
                              Bindings -> Bindingsout):
         Insert_Binding(BINDING'single(Pos1, IdOp), Bindings
                        -> Bindingsout)


--------------------------------------------------
'sweep' Collect_Ops_infix_occ(ANY, DECLAREDS -> DECLAREDS)

  'rule' Collect_Ops_infix_occ(VALUE_EXPR'infix_occ(P, LVE, Valueid, OQ, RVE),
                           DeclaredsIn -> DeclaredsOut):
	 Collect_Ops_infix_occ(LVE, DeclaredsIn -> DeclaredsIn1)    
         Insert_Declared(value_item(Valueid), DeclaredsIn1
                             -> DeclaredsOut1)
	 Collect_Ops_infix_occ(RVE, DeclaredsOut1 -> DeclaredsOut)    


--------------------------------------------------
'sweep' Collect_Ops_prefix_occ(ANY, DECLAREDS -> DECLAREDS)

  'rule' Collect_Ops_prefix_occ(VALUE_EXPR'prefix_occ(_, Valueid, nil, VE),
                           DeclaredsIn -> DeclaredsOut):
         Insert_Declared(value_item(Valueid), DeclaredsIn
                             -> DeclaredsOut1)
	 Collect_Ops_prefix_occ(VE, DeclaredsOut1 -> DeclaredsOut)    


--------------------------------------------------
'sweep' Collect_Redef_Opers(ANY, DECLAREDS -> DECLAREDS)

  'rule' Collect_Redef_Opers(VALUE_EXPR'infix_occ(Pos1, LVE, Valueid, Q, RVE),
                           DeclaredsIn -> DeclaredsOut):
         Valueid'Pos -> Pos
         Valueid'Ident -> IdorOp

	 Collect_Redef_Opers(LVE, DeclaredsIn -> Declareds1)    
	 Collect_Redef_Opers(RVE, Declareds1 -> Declareds2)    
	 (|
	   where(IdorOp -> op_op(Op))
	   (|
	     (| Built_in(Op, Valueid) || ne(Q, nil) |)
	     where(Declareds2 -> DeclaredsOut)
	   ||
	     Insert_Declared(value_item(Valueid), Declareds2 -> DeclaredsOut)
           |)
	 ||
	   where(DeclaredsIn -> DeclaredsOut)
         |)


  'rule' Collect_Redef_Opers(VALUE_EXPR'prefix_occ(_, Valueid, Q, VE),
                           DeclaredsIn -> DeclaredsOut):
         Valueid'Pos -> Pos
         Valueid'Ident -> IdorOp
	 Collect_Redef_Opers(VE, DeclaredsIn -> Declareds1)    
	 (|
	   where(IdorOp -> op_op(Op))
	   (|
	     (| Built_in(Op, Valueid) || ne(Q, nil) |)
	     where(Declareds1 -> DeclaredsOut)
	   ||
	     Insert_Declared(value_item(Valueid), Declareds1 -> DeclaredsOut)
           |)
	 ||
	   where(DeclaredsIn -> DeclaredsOut)
         |)


--------------------------------------------------
-- Precedences
--------------------------------------------------

'condition' PVS_lower_precedence(PVS_EXPR, INT)

  'rule' PVS_lower_precedence(V, I)
	 PVS_expr_precedence(V -> P)
	 lt(P,I)

'action' PVS_expr_precedence(PVS_EXPR -> INT)

  'rule' PVS_expr_precedence(literal_expr(_) -> 0):

  'rule' PVS_expr_precedence(named_val(_) -> 0):

  'rule' PVS_expr_precedence(product(_) -> 0):

  'rule' PVS_expr_precedence(ranged_set(_,_) -> 1):

  'rule' PVS_expr_precedence(enum_set(_) -> 1):

  'rule' PVS_expr_precedence(comp_simp_set(_,_) -> 0):

  'rule' PVS_expr_precedence(comp_set(_,_,_,_) -> 0):

  'rule' PVS_expr_precedence(ranged_list(_,_) -> 1):

  'rule' PVS_expr_precedence(enum_list(_) -> 0):

  'rule' PVS_expr_precedence(comp_list(_,_) -> 1):

  'rule' PVS_expr_precedence(enum_map(_) -> 1):

  'rule' PVS_expr_precedence(comp_rng_map(_,_,_,_,_) -> 22):

  'rule' PVS_expr_precedence(comp_map(_,_,_,_,_) -> 22):

  'rule' PVS_expr_precedence(function(_,_) -> 22):

  'rule' PVS_expr_precedence(list_applic(_,_) -> 1):

  'rule' PVS_expr_precedence(map_applic(_,_) -> 1):

  'rule' PVS_expr_precedence(funct_applic(_,_) -> 1):

  'rule' PVS_expr_precedence(quantified(_,_,_) -> 22):

  'rule' PVS_expr_precedence(equivalence(_,_,nil) -> 14):

  'rule' PVS_expr_precedence(equivalence(_,_,_) -> 18):

  'rule' PVS_expr_precedence(post(_,_,_,nil) -> 22):

  'rule' PVS_expr_precedence(post(_,_,_,_) -> 18):

  'rule' PVS_expr_precedence(disamb(_,_) -> 5):

  'rule' PVS_expr_precedence(bracket(_) -> 0):

  'rule' PVS_expr_precedence(ax_infix(_,C,_) -> P):
	 PVS_connective_precedence(C -> P)

  'rule' PVS_expr_precedence(funct_expr(_,_,_,_) -> 1):

  'rule' PVS_expr_precedence(ax_prefix(_,_) -> 15):

  'rule' PVS_expr_precedence(let_expr(nil,V) -> P):
	 PVS_expr_precedence(V -> P)

  'rule' PVS_expr_precedence(let_expr(_,_) -> 22):

  'rule' PVS_expr_precedence(if_expr(_,_,_,_) -> 0):

  'rule' PVS_expr_precedence(val_occ(_,_) -> 0):

  'rule' PVS_expr_precedence(infix_occ(_,val_id(_, IdOp),_) -> P):
         PVS_id_operator_precedence(IdOp -> P)

  'rule' PVS_expr_precedence(prefix_occ(val_id(_, IdOp),_) -> 1):
         PVS_id_operator_precedence(IdOp -> P)

  'rule' PVS_expr_precedence(_ -> 0):


'action' PVS_connective_precedence(PVS_CONNECTIVE -> INT)

  'rule' PVS_connective_precedence(implies -> 18):

  'rule' PVS_connective_precedence(or -> 17):

  'rule' PVS_connective_precedence(and -> 16):

  'rule' PVS_connective_precedence(not -> 15):

'action' PVS_id_operator_precedence(ID_OP -> INT)

  'rule' PVS_id_operator_precedence(id(_) -> 1):

  'rule' PVS_id_operator_precedence(op_symb(Op) -> P):
	 PVS_operator_precedence(Op -> P)

'action' PVS_operator_precedence(PVS_OP -> INT)

  'rule' PVS_operator_precedence(infix_op(Op) -> P):
	 PVS_infix_precedence(Op -> P)

  'rule' PVS_operator_precedence(prefix_op(_) -> 9):

  'rule' PVS_operator_precedence(function_op(_) -> 1):

'action' PVS_infix_precedence(INFIX_OP -> INT)

  'rule' PVS_infix_precedence(eq -> 14):

  'rule' PVS_infix_precedence(neq -> 14):

  'rule' PVS_infix_precedence(gt -> 14):

  'rule' PVS_infix_precedence(lt -> 14):

  'rule' PVS_infix_precedence(ge -> 14):

  'rule' PVS_infix_precedence(le -> 14):

  'rule' PVS_infix_precedence(mult -> 8):

  'rule' PVS_infix_precedence(div -> 8):

  'rule' PVS_infix_precedence(plus -> 9):

  'rule' PVS_infix_precedence(minus -> 9):


--------------------------------------------------
'action' PVSBindings_to_expr(PVS_BINDINGS -> PVS_EXPR)

  'rule' PVSBindings_to_expr(list(B, nil) -> E):
	 PVSBinding_to_expr(B -> E)

  'rule' PVSBindings_to_expr(BS -> product(ES)):
	 PVSBindings_to_exprs(BS -> ES)

'action' PVSBindings_to_exprs(PVS_BINDINGS -> PVS_EXPRS)

  'rule' PVSBindings_to_exprs(list(B, BS) -> list(E, ES)):
	 PVSBinding_to_expr(B -> E)
	 PVSBindings_to_exprs(BS -> ES)

  'rule' PVSBindings_to_exprs(nil -> nil):

'action' PVSBinding_to_expr(PVS_BINDING -> PVS_EXPR)

  'rule' PVSBinding_to_expr(prod_binding(BS) -> product(ES)):
	 PVSBindings_to_exprs(BS -> ES)

  'rule' PVSBinding_to_expr(typed_prod(BS, _) -> product(ES)):
	 PVSBindings_to_exprs(BS -> ES)

  'rule' PVSBinding_to_expr(typed_id(IdOp, _) -> named_val(id_op(IdOp))):




--------------------------------------------------
--   Prints
--------------------------------------------------


--------------------------------------------------
'action' Print_if_in_Declareds_s(DECLAREDS_S, DECLARED)

  'rule' Print_if_in_Declareds_s(list(Decls, Decls_sTail), DeclIn):
	 Print_if_in_Declareds(Decls, DeclIn)
	 Print_if_in_Declareds_s(Decls_sTail, DeclIn)

	 -- no more Declareds
  'rule' Print_if_in_Declareds_s(nil, Decl2):
	 Putmsg("----- END Declareds -----")
	 Putmsg("                         ")
	 Putnl()


--------------------------------------------------
'action' Print_if_in_Declareds(DECLAREDS, DECLARED)

  'rule' Print_if_in_Declareds(list(Decl1, DeclsTail), Decl2):
	 Print_if_in_Declared(Decl1, Decl2)
	 Print_if_in_Declareds(DeclsTail, Decl2)

	 -- no more Declareds
  'rule' Print_if_in_Declareds(nil, Decl2):
	 Putmsg("----- END Declareds -----")
	 Putmsg("                         ")
	 Putnl()



--------------------------------------------------
'action' Print_if_in_Declared(DECLARED, DECLARED)

  'rule' Print_if_in_Declared(type_item(Typeid1), type_item(Typeid2)):
	 [|
	   eq(Typeid1, Typeid2)
	   Print_Type_id(Typeid1, "type_item in DECLARED FOUND")
	 |]

  'rule' Print_if_in_Declared(value_item(Valueid1), value_item(Valueid2)):
	 [|
	   eq(Valueid1, Valueid2)
	   Print_Value_id(Valueid1, "value_item in DECLARED FOUND")
	 |]

  'rule' Print_if_in_Declared(axiom_item(AxiomDefs1), axiom_item(AxiomDefs2)):
	 [|
	   eq(AxiomDefs1, AxiomDefs2)
	   Putmsg("---- SAME AxiomDefs in DECLARED")
	   Putnl()
	   print(AxiomDefs1)
	 |]

  'rule' Print_if_in_Declared(rec_fun_item(Valueid1), rec_fun_item(Valueid2)):
	 [|
	   eq(Valueid1, Valueid2)
	   Print_Value_id(Valueid1, "rec_fun_item in DECLARED FOUND")
	 |]

  'rule' Print_if_in_Declared(mut_rec_fun_item(Valueid1), mut_rec_fun_item(Valueid2)):
	 [|
	   eq(Valueid1, Valueid2)
	   Print_Value_id(Valueid1, "mut_rec_fun_item in DECLARED FOUND")
	 |]

  'rule' Print_if_in_Declared(rec_item(Declareds1), rec_item(Declareds2)):
	 [|
	   eq(Declareds1, Declareds2)
	   Putmsg("Declareds in rec_item in DECLARED FOUND")
	   Putnl()
	 |]

  'rule' Print_if_in_Declared(mark_item(String1), mark_item(String2)):
	 [|
	   eq(String1, String2)
	   print("mark_item in DECLARED FOUND")
	   print(String1)
	 |]

	 -- do nothing if another combination
  'rule' Print_if_in_Declared(_, _):


--------------------------------------------------
'action' Print_if_Id_in_Declareds_s(DECLAREDS_S, STRING, OP)

  'rule' Print_if_Id_in_Declareds_s(list(Decls, Decls_sTail), IdString, Op):
	 Print_if_Id_in_Declareds(Decls, IdString, Op)
	 Print_if_Id_in_Declareds_s(Decls_sTail, IdString, Op)

	 -- no more Declareds
  'rule' Print_if_Id_in_Declareds_s(nil, IdString, Op):
	 Putmsg("----- END Declareds_s -----")
	 Putnl()
	 Putnl()


--------------------------------------------------
'action' Print_if_Id_in_Declareds(DECLAREDS, STRING, OP)

  'rule' Print_if_Id_in_Declareds(list(Decl1, DeclsTail), IdString, Op):
	 Print_if_Id_in_Declared(Decl1, IdString, Op)
	 Print_if_Id_in_Declareds(DeclsTail, IdString, Op)

	 -- no more Declareds
  'rule' Print_if_Id_in_Declareds(nil, IdString, Op):
	 Putmsg("----- END Declareds -----")
	 Putmsg("                         ")
	 Putnl()



--------------------------------------------------
'action' Print_if_Id_in_Declared(DECLARED, STRING, OP)

  'rule' Print_if_Id_in_Declared(type_item(Typeid), IdString, Op):
	 [|
	   Typeid'Ident -> Ident
	   id_to_string(Ident -> IdString1)
	   eq(IdString, IdString1)
	   Print_Type_id(Typeid, "type_item in DECLARED FOUND")
	 |]

  'rule' Print_if_Id_in_Declared(value_item(Valueid), IdString, Op):
	   Valueid'Ident -> IdorOp
	   (|
	     where(IdorOp -> id_op(Ident))
	     id_to_string(Ident -> IdString1)
	     eq(IdString, IdString1)
	     Print_Value_id(Valueid, "value_item in DECLARED FOUND")
	   ||
	     where(IdorOp -> op_op(Op1))
	     eq(Op, Op1)
	     Print_Value_id(Valueid, "value_item in DECLARED FOUND")
	   |)

  'rule' Print_if_Id_in_Declared(axiom_item(AxiomDefs), IdString, Op):
--	 Putmsg("axiom_item")
--	 Putnl()

  'rule' Print_if_Id_in_Declared(rec_fun_item(Valueid), IdString, Op):
	   Valueid'Ident -> IdorOp
	   (|
	     where(IdorOp -> id_op(Ident))
	     id_to_string(Ident -> IdString1)
	     eq(IdString, IdString1)
	     Print_Value_id(Valueid, "value_item in DECLARED FOUND")
	   ||
	     where(IdorOp -> op_op(Op1))
	     eq(Op, Op1)
	     Print_Value_id(Valueid, "value_item in DECLARED FOUND")
	   |)

  'rule' Print_if_Id_in_Declared(mut_rec_fun_item(Valueid), IdString, Op):
	   Valueid'Ident -> IdorOp
	   (|
	     where(IdorOp -> id_op(Ident))
	     id_to_string(Ident -> IdString1)
	     eq(IdString, IdString1)
	     Print_Value_id(Valueid, "value_item in DECLARED FOUND")
	   ||
	     where(IdorOp -> op_op(Op1))
	     eq(Op, Op1)
	     Print_Value_id(Valueid, "value_item in DECLARED FOUND")
	   |)

  'rule' Print_if_Id_in_Declared(rec_item(Declareds), IdString, Op):
	 Print_if_Id_in_Declareds(Declareds, IdString, Op)

  'rule' Print_if_Id_in_Declared(mark_item(String), IdString, Op):
	 [|
	   eq(IdString, String)
	   print("mark_item in DECLARED FOUND")
	   print(String)
	 |]

	 -- do nothing if another combination
  'rule' Print_if_Id_in_Declared(_, _, Op):


--------------------------------------------------
'action' PrintTotalDeclaredsCard(STRING)

  'rule' PrintTotalDeclaredsCard(Msg):
	 Get_TotalDeclareds(-> TotalDeclrds)
	 CountDeclareds_s(TotalDeclrds, 0 -> Count)
	 Putmsg(Msg)
	 Putnl()
	 Putmsg("Items in TotalDeclareds: ")
	 print(Count)

--------------------------------------------------
'action' CountDeclareds_s(DECLAREDS_S, INT -> INT)

  'rule' CountDeclareds_s(list(Declareds, Declareds_sTail),
                          CountIn -> CountOut):
	 CountDeclareds(Declareds, CountIn -> CountOut1)
	 CountDeclareds_s(Declareds_sTail, CountOut1
			   -> CountOut)

  'rule' CountDeclareds_s(nil, Count -> Count):

--------------------------------------------------
'action' CountDeclareds(DECLAREDS, INT -> INT)

  'rule' CountDeclareds(list(Declared, DeclaredsTail),
                          CountIn -> CountOut):
	 where(CountIn + 1 -> CountOut1)
	 CountDeclareds(DeclaredsTail, CountOut1
			 -> CountOut)

  'rule' CountDeclareds(nil, Count -> Count):


--------------------------------------------------
'action' PrintTotalDeclareds(STRING)

  'rule' PrintTotalDeclareds(Msg):
	 Putmsg("---------------------")
	 Putnl()
	 Putmsg(Msg)
	 Putnl()
	 Get_TotalDeclareds(-> TotalDeclrds)
	 PrintDeclareds_s(TotalDeclrds)

--------------------------------------------------
'action' PrintDeclareds_s(DECLAREDS_S)

  'rule' PrintDeclareds_s(list(Declareds, Declareds_sTail)):
	 PrintDeclareds(Declareds)
	 PrintDeclareds_s(Declareds_sTail)

  'rule' PrintDeclareds_s(nil):

--------------------------------------------------
'action' PrintDeclareds(DECLAREDS)

  'rule' PrintDeclareds(list(Declared, DeclaredsTail)):
	 PrintDeclared(Declared)
	 [|
	   ne(DeclaredsTail, nil)
	   Putmsg(", ")
	   PrintDeclareds(DeclaredsTail)
         |]

	 -- no more Declareds
  'rule' PrintDeclareds(nil):
--	 Putmsg("----- END Declareds -----")
--	 Putmsg("                         ")
	 Putnl()



--------------------------------------------------
'action' PrintDeclared(DECLARED)

  'rule' PrintDeclared(type_item(Typeid)):
	 Putmsg("type ")
	 Typeid'Ident -> Id
	 Print_id(Id)
--	 Print_Type_id(Typeid, "type_item in DECLARED")

  'rule' PrintDeclared(value_item(Valueid)):
	 Putmsg("value ")
	 Valueid'Ident -> Id
	 Print_id_or_op(Id)
--	 Print_Value_id(Valueid, "value_item in DECLARED")

  'rule' PrintDeclared(axiom_item(Axiomid)):
	 Putmsg("axiom")
--	 Putmsg(" axiom_item in DECLARED")
--	 Putnl()
--[|
--  Axiomid'Ident -> ident(Id)
--  Putmsg("[")
--  Print_id(Id)
--  Putmsg("]\n")
--|]
--Axiomid'Axiom -> A
--Print_expr(A)
--Putnl()

  'rule' PrintDeclared(lemma_item(AxiomDefs)):
	 Print_Axiom_id(AxiomDefs, " lemma_item in DECLARED")

  'rule' PrintDeclared(rec_fun_item(Valueid)):
	 Print_Value_id(Valueid, "rec_fun_item in DECLARED")

  'rule' PrintDeclared(mut_rec_fun_item(Valueid)):
	 Print_Value_id(Valueid, "mut_rec_fun_item in DECLARED")

  'rule' PrintDeclared(rec_item(Declareds)):
	 Putmsg("---- BEGIN rec_item in DECLARED ----")
	 Putnl()
	 PrintDeclareds(Declareds)
	 Putmsg("----  END rec_item in DECLARED  ----")
	 Putnl()

  'rule' PrintDeclared(mark_item(String)):
	 Putmsg("mark_item in DECLARED")
	 Putnl()
	 Putmsg(String)
	 Putnl()

  'rule' PrintDeclared(nil):
	 Putmsg("nil in DECLARED")
	 Putnl()


--------------------------------------------------
'action' PrintTheoryElements(THEORY_ELEMENTS)

  'rule' PrintTheoryElements(list(TheoryElem, TheoryElemsTail)):
	 PrintTheoryElement(TheoryElem)
	 PrintTheoryElements(TheoryElemsTail)

	 -- no more TheoryElements
  'rule' PrintTheoryElements(nil):
	 Putmsg("---- END THEORY_ELEMENTS ----")
	 Putnl()
	 Putnl()


--------------------------------------------------
'action' PrintTheoryElement(THEORY_ELEMENT)

  'rule' PrintTheoryElement(importing(Importing)):
	 PrintImporting(Importing)

  'rule' PrintTheoryElement(theory_decl(TheoryDecl)):
--	 print("TheoryDecl")
	 PrintTheoryDecl(TheoryDecl)

  'rule' PrintTheoryElement(rec_decl(TheoryElems)):
	 Putmsg("---------- BEGIN rec_decl ----------")
	 Putnl()
	 PrintTheoryElements(TheoryElems)
	 Putmsg("---------- END rec_decl ------------")
	 Putnl()

  'rule' PrintTheoryElement(mark_decl(String)):
	 Putmsg("mark_decl: ")
	 print(String)


--------------------------------------------------
'action' PrintTheoryDecl(THEORY_DECL)

  'rule' PrintTheoryDecl(type_decl(Ids, _, _, _, _)):
	 print("TheoryDecl: type_decl")

  'rule' PrintTheoryDecl(var_decl(IdOps, _)):
	 print("TheoryDecl: var_decl")

  'rule' PrintTheoryDecl(const_decl(ConstDecl)):
--	 print("TheoryDecl: ConstDecl")
	 PrintConstDecl(ConstDecl)

  'rule' PrintTheoryDecl(formula_decl(_, _, _)):
	 print("TheoryDecl: formula_decl")

  'rule' PrintTheoryDecl(inline_datatype(Id, _)):
	 print("TheoryDecl: inline_datatype")

  'rule' PrintTheoryDecl(nil):
	 print("TheoryDecl: nil")


--------------------------------------------------
'action' PrintConstDecl(CONSTANT_DECL)

  'rule' PrintConstDecl(nodef(IdOps, _, _)):
	 print("ConstDecl: nodef")
	 where(IdOps -> list(IdOp, T))
	 PrintIdOp(IdOp)

  'rule' PrintConstDecl(expl_const(IdOps, _, _)):
	 print("ConstDecl: expl_const")
	 where(IdOps -> list(IdOp, T))
	 PrintIdOp(IdOp)

  'rule' PrintConstDecl(impl_const(IdOps, _, _)):
	 print("ConstDecl: impl_const")
	 where(IdOps -> list(IdOp, T))
	 PrintIdOp(IdOp)

  'rule' PrintConstDecl(expl_fun_const(IdOp, _, _, _, _, _)):
	 print("ConstDecl: expl_fun_const")
	 PrintIdOp(IdOp)

  'rule' PrintConstDecl(impl_fun_const(IdOp, _, _, _, _)):
	 print("ConstDecl: impl_fun_const")
	 PrintIdOp(IdOp)

  'rule' PrintConstDecl(nil):
	 print("ConstDecl: nil")


--------------------------------------------------
'action' PrintImporting(IMPORTING)

  'rule' PrintImporting(theory_name(TheoryNames)):
	 Putmsg("Importing: theory_name")
	 Putnl()

  'rule' PrintImporting(theory_map(Dom, Rng)):
	 Putmsg("Importing: theory_map")
	 Putnl()

  'rule' PrintImporting(theory_ranged_set(TypeExpr)):
	 Putmsg("Importing: theory_ranged_set")
	 Putnl()

  'rule' PrintImporting(theory_ranged_list(TypeExpr)):
	 Putmsg("Importing: theory_ranged_list")
	 Putnl()

  'rule' PrintImporting(theory_comp_list(TypeExpr)):
	 Putmsg("Importing: theory_comp_list")
	 Putnl()

  'rule' PrintImporting(nil):
	 Putmsg("Importing: nil")
	 Putnl()


--------------------------------------------------
'action' PrintIdOp(ID_OP)

  'rule' PrintIdOp(id(Id)):
	 Putmsg("IdOp is ")
	 PrintId(Id)

  'rule' PrintIdOp(op_symb(Op)):
	 print("IdOp: op_symb")

  'rule' PrintIdOp(nil):
	 print("IdOp: nil")


--------------------------------------------------
'action' PrintId(IDENT)

  'rule' PrintId(Id):
	 id_to_string(Id -> IdStr)
	 Putmsg("Ident: ")
	 Putmsg(IdStr)
	 Putmsg(" ")
	 print(Id)


--------------------------------------------------
'action' Print_Valueid_Id(Value_id, STRING, STRING)

  'rule' Print_Valueid_Id(Valueid, IdString1, Msg):
	 Valueid'Ident -> Ident
	 [|
	   where(Ident -> id_op(Id))
	   id_to_string(Id -> IdString2)
	   eq(IdString1, IdString2)
	   Print_Value_id(Valueid, Msg)
	 |]


--------------------------------------------------
'action' Print_Value_id(Value_id, STRING)

  'rule' Print_Value_id(Valueid, Msg):
         Valueid'Pos -> Pos
         Valueid'Ident -> IdOp
         Valueid'Type -> Type
         Valueid'Def -> ValueDef
         Valueid'Qualifier -> Objectids
	 Putmsg("---------------------------")
	 Putnl()
	 [|
	   ne(Msg, "")
	   Putmsg(Msg)
	   Putnl()
	 |]
	 Putmsg("Valueid: ")
	 print(Valueid)
	 Putmsg("Pos: ")
	 print(Pos)
	 Putmsg("IdOp: ")
	 print(IdOp)
	 [|
	   where(IdOp -> id_op(Id))
	   id_to_string(Id -> IdSt)
	   Putmsg("Ident: ")
	   print(IdSt)
	 |]
	 (|
	   where(ValueDef -> no_def)
	   Putmsg("ValueDef: no_def")
	   Putnl()
	 ||
	   where(ValueDef -> expl_val(ValueExpr, _))
	   Putmsg("ValueDef: expl_val")
	   Putnl()
	 ||
	   where(ValueDef -> impl_val(ValueExpr))
	   Putmsg("ValueDef: impl_val")
	   Putnl()
	 ||
	   where(ValueDef -> expl_fun(Params, ValueExpr, _, Pre, OptCond, _))
	   Putmsg("ValueDef: expl_fun")
	   Putnl()
/*
	   Putmsg("ValueExpr of expl_fun")
	   Putnl()
	   print(ValueExpr)
	   Putmsg("------end ValueExpr of expl_fun")
	   Putnl()
*/
	 ||
	   where(ValueDef -> impl_fun(Params, Post, Pre, OptCond))
	   Putmsg("ValueDef: impl_fun")
	   Putnl()
	 |)
	 Putmsg("- Qualifier (Object_ids) -")
	 Putnl()
	 Print_Object_ids(Objectids, Msg)
	 Putmsg("--- end Value_id ---")
	 Putnl()


--------------------------------------------------
'action' Print_Type_id(Type_id, STRING)

  'rule' Print_Type_id(Typeid, Msg):
         Typeid'Pos -> Pos
         Typeid'Ident -> Ident
         Typeid'Type -> Type
         Typeid'Def -> TypeDef
	 Typeid'Qualifier -> Objectids
	 Putmsg("---------------------------")
	 Putnl()
	 print(Msg)
	 Putmsg("Typeid: ")
	 print(Typeid)
	 Putmsg("Pos: ")
	 print(Pos)
	 Putmsg("Ident: ")
	 id_to_string(Ident -> IdSt)
	 Putmsg(IdSt)
	 Putmsg(" : ")
	 print(Ident)
	 (|
	   where(TypeDef -> no_def)
	   Putmsg("TypeDef: no_def")
	   Putnl()
	 ||
	   where(TypeDef -> abbreviation(TypeExpr))
	   Putmsg("TypeDef: abbreviation")
	   Putnl()
/*
	   Putmsg("TypeExpr of abbreviation")
	   Putnl()
	   print(TypeExpr)
	   Putmsg("--- end TypeExpr of abbreviation")
	   Putnl()
*/
	 |)
	 (|
	   where(Type -> undef_type)
	   Putmsg("Type: undef_type")
	   Putnl()
	 ||
	   where(Type -> sort(SortKind))
	   Putmsg  ("Type: SortKind")
	   (|
	     where(SortKind -> abstract)
	     Putmsg(" (abstract)")
	     Putnl()
	   ||
	     where(SortKind -> record(_))
	     Putmsg(" (record)")
	     Putnl()
	   ||
	     where(SortKind -> variant(_))
	     Putmsg(" (variant)")
	     Putnl()
	   ||
	     where(SortKind -> union(_))
	     Putmsg(" (union)")
	     Putnl()
	   |)
	 ||
	   where(Type -> abbrev(TypeExpr))
	   Putmsg("Type: abbrev")
	   Putnl()
/*
	   Putmsg("TypeExpr of abbrev")
	   print(TypeExpr)
	   Putmsg("--- end TypeExpr of abbrev")
*/
	 |)
	 Putmsg("- Qualifier (Object_ids) -")
	 Putnl()
	 Print_Object_ids(Objectids, Msg)
	 Putmsg("--- end Type_id ---")
	 Putnl()


--------------------------------------------------
'action' Print_Axiom_Defs(AXIOM_DEFS)

  'rule' Print_Axiom_Defs(list(AxiomDef, AxiomDefsTail)):
	 Print_Axiom_Def(AxiomDef)
	 Print_Axiom_Defs(AxiomDefsTail)

  'rule' Print_Axiom_Defs(nil):


--------------------------------------------------
'action' Print_Axiom_Def(AXIOM_DEF)

  'rule' Print_Axiom_Def(axiom_def(Pos, OptIdent, ValueExpr)):
	 Putmsg("Pos: ")
	 Pos_to_string(Pos -> PosSt)
	 Putmsg(PosSt)
	 Putmsg("; ")
	 Putmsg("Opt_Ident: ")
	 (|
	   eq(OptIdent, nil)
	   where("nil" -> IdSt)
	 ||
	   where(OptIdent -> ident(Ident))
	   id_to_string(Ident -> IdSt)
	 |)
	 Putmsg(IdSt)
	 Putmsg(" : ")
	 print(OptIdent)
	 


--------------------------------------------------
'action' Print_Axiom_id(Axiom_id, STRING)

  'rule' Print_Axiom_id(Axiomid, Msg):
         Axiomid'Pos -> Pos
         Axiomid'Ident -> OptIdent
         Axiomid'Axiom -> AxiomExpr
	 Putmsg("---------------------------")
	 Putnl()
	 Putmsg(Msg)
	 Putnl()
	 Putmsg("Axiomid: ")
	 print(Axiomid)
	 Putmsg("Pos: ")
	 print(Pos)
--	 Pos_to_string(Pos -> PosSt)
--	 Putmsg(PosSt)
	 Putmsg("Opt_Ident: ")
	 (|
	   eq(OptIdent, nil)
	   where("nil" -> IdSt)
	 ||
	   where(OptIdent -> ident(Ident))
	   id_to_string(Ident -> IdSt)
	 |)
	 Putmsg(IdSt)
	 Putnl()
--	 Putmsg(" : ")
	 print(OptIdent)
/*
	   Putmsg("--------AxiomExpr--------")
	   Putnl()
	   print(AxiomExpr)
	   Putmsg("------end AxiomExpr------")
	   Putnl()
*/
	 Putmsg("------- end Axiomid -------")
	 Putnl()
	 Putnl()


--------------------------------------------------
'action' Print_Object_ids(Object_ids, STRING)

  'rule' Print_Object_ids(list(Objectid, ObjectidsTail), Msg):
	 Print_Object_id(Objectid, Msg)
	 Print_Object_ids(ObjectidsTail, Msg)

  'rule' Print_Object_ids(nil, Msg):
	 Putmsg("------------ END Object_ids")
	 Putnl()


--------------------------------------------------
'action' Print_Object_id(Object_id, STRING)

  'rule' Print_Object_id(Objectid, Msg):
	 Objectid'Pos -> Pos
	 Objectid'Ident -> Ident
	 Objectid'Qualifier -> Objectids
	 Objectid'Params -> Params
	 Putmsg("---------------------------")
	 Putnl()
	 Putmsg(Msg)
	 Putnl()
	 Putmsg("Objectid: ")
	 print(Objectid)
	 Putmsg("Pos: ")
	 print(Pos)
	 Putmsg("Ident: ")
	 id_to_string(Ident -> IdSt)
	 Putmsg(IdSt)
	 Putmsg(" : ")
	 print(Ident)
	 Putmsg("- Qualifier (Object_ids) -")
	 Putnl()
	 Print_Object_ids(Objectids, Msg)
	 (|
	   eq(Params, nil)
	   Putmsg("Params: nil")
	   Putnl()
	 ||
	   Putmsg("Params: Type_Expr")
	   Putnl()
	 |)
	 Putmsg("--- end Objectid ---")
	 Putnl()


--------------------------------------------------
'action' Print_Scheme_id(Scheme_id, STRING)

  'rule' Print_Scheme_id(Schemeid, Msg):
	 Schemeid'Pos -> Pos
	 Schemeid'Ident -> Ident
	 Schemeid'Qualifier -> Objectids
	 Schemeid'Params -> ModuleEnv
	 Schemeid'Class -> Class
	 -- Schemeid'With -> ObjectExprs
	 Putmsg("---------------------------")
	 Putnl()
	 Putmsg(Msg)
	 Putnl()
	 Putmsg("Schemeid: ")
	 print(Schemeid)
	 Putmsg("Pos: ")
	 print(Pos)
	 Putmsg("Ident: ")
	 id_to_string(Ident -> IdSt)
	 Putmsg(IdSt)
	 Putmsg(" : ")
	 print(Ident)
	 Putmsg("--- end Schemeid ---")
	 Putnl()


--------------------------------------------------
'action' Print_Theory_id(Theory_id, STRING)

  'rule' Print_Theory_id(Theoryid, Msg):
	 Theoryid'Pos -> Pos
	 Theoryid'Ident -> Ident
	 Theoryid'Env -> ClassEnv
	 Putmsg("---------------------------")
	 Putnl()
	 Putmsg(Msg)
	 Putnl()
	 Putmsg("Theoryid: ")
	 print(Theoryid)
	 Putmsg("Pos: ")
	 print(Pos)
	 Putmsg("Ident: ")
	 id_to_string(Ident -> IdSt)
	 Putmsg(IdSt)
	 Putmsg(" : ")
	 print(Ident)
	 Putmsg("--- end Theoryid ---")
	 Putnl()

--------------------------------------------------
'action' PrintLetDefs(LET_DEFS)

  'rule' PrintLetDefs(list(LetDef, LetDefsTail)):
	 PrintLetDef(LetDef)
	 PrintLetDefs(LetDefsTail)

	 -- no more Declareds
  'rule' PrintLetDefs(nil):
	 Putmsg("----- END LetDefs -----")
	 Putnl()

--------------------------------------------------
'action' PrintLetDef(LET_DEF)

  'rule' PrintLetDef(explicit(Pos, LetBinding, ValueExpr)):
	 Putmsg("Explicit Let")
	 Putnl()
	 PrintLetBinding(LetBinding)
	 Putmsg("-- ValueExpr")
	 Putnl()
	 print(ValueExpr)

  'rule' PrintLetDef(implicit(Pos, Typing, Restriction)):
	 Putmsg("Implicit Let")
	 Putnl()

--------------------------------------------------
'action' PrintLetBinding(LET_BINDING)

  'rule' PrintLetBinding(binding(Pos, Binding)):
	 Putmsg("-- Let Binding: Binding")
	 Putnl()
	 print(Binding)

  'rule' PrintLetBinding(pattern(Pos, Pattern)):
	 Putmsg("-- Let Binding: Pattern")
	 Print_pattern(Pattern)
	 Putnl()

