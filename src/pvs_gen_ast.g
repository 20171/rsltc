-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module generates PVS abstract syntax tree
-- from the sorted declareds


'module' pvs_gen_ast

'use' ast print ext env objects values types pp cc cpp sml
      pvs pvs_ast pvs_aux pvs_gen_code

      sal_gen_ast

'export' 
	 Gen_PVS_ast

	 -- exported to be used in sal_gen_ast:
	 Debracket_abbrev
	 Debracket_bindings
	 Get_Type_of_Value_Expr
	 Is_dom_or_elems
--------------------------------------------------
'action' Gen_PVS_ast(DECLAREDS, THEORY_ELEMENTS -> THEORY_ELEMENTS)

  'rule' Gen_PVS_ast(list(Declared, DeclaredsTail), TheoryElements  -> TheoryElementsout):
--print("BEGIN Gen_PVS_ast")
	 ProcessDeclared(Declared, TheoryElements -> TheoryElements1)
--print("END Gen_PVS_ast")
	 Gen_PVS_ast(DeclaredsTail, TheoryElements1  -> TheoryElementsout)

	 -- no more Declareds
  'rule' Gen_PVS_ast(nil, TheoryElements -> TheoryElements):


--------------------------------------------------
'action' ProcessDeclared(DECLARED, THEORY_ELEMENTS -> THEORY_ELEMENTS)

  'rule' ProcessDeclared(type_item(Typeid), TheoryElements -> TheoryElementsout):
	 Add_destructors(Typeid)
	 Typeid'Type -> Type
--print("ProcessDeclared - type_item - 1")
	 Process_Type_id(Type, Typeid, TheoryElements -> TheoryElementsout)
--print("ProcessDeclared - type_item - 2")

  'rule' ProcessDeclared(value_item(Valueid), TheoryElements -> TheoryElementsout):
	 Valueid'Def -> Def
--print("ProcessDeclared - value_item - 1")
	 Process_Value_id(Valueid, Def, TheoryElements -> TheoryElementsout)
--print("ProcessDeclared - value_item - 2")

  'rule' ProcessDeclared(rec_fun_item(Valueid), TheoryElements -> TheoryElementsout):
	 Valueid'Def -> Def
--print("ProcessDeclared - rec_fun_item - 1")
	 Process_Value_id(Valueid, Def, TheoryElements -> TheoryElementsout)
--print("ProcessDeclared - rec_fun_item - 2")

  'rule' ProcessDeclared(mut_rec_fun_item(Valueid), TheoryElements -> TheoryElementsout):
	 Valueid'Def -> Def
--print("ProcessDeclared - mut_rec_fun_item")
	 Process_Value_id(Valueid, Def, TheoryElements -> TheoryElementsout)

  'rule' ProcessDeclared(rec_item(Declareds), TheoryElements -> TheoryElementsout):
--print("-------------------------------------")
--print("ProcessDeclared, rec_item")
--PrintDeclareds(Declareds)
	 Gen_PVS_ast(Declareds, nil -> TheoryElements1)
	 where(rec_decl(TheoryElements1) -> TheoryElement)
	 Insert_Theory_Element(TheoryElement, TheoryElements -> TheoryElementsout)
--print("-------------------------------------")
--print("in gen_ast, ProcessDeclared, rec_decl")
--PrintTheoryElement(TheoryElement)

  'rule' ProcessDeclared(axiom_item(Axiomid), TheoryElements  -> TheoryElementsout):
--print("ProcessDeclared - axiom_item - 1")
	 Process_Axiom_id(Axiomid, TheoryElements -> TheoryElementsout)
--print("ProcessDeclared - axiom_item - 2")

  'rule' ProcessDeclared(lemma_item(Axiomid), TheoryElements  -> TheoryElementsout):
--print("ProcessDeclared - lemma_item - 1")
	 Process_Lemma_item(Axiomid, TheoryElements -> TheoryElementsout)
--print("ProcessDeclared - lemma_item - 2")

  'rule' ProcessDeclared(mark_item(Msg), TheoryElements  -> TheoryElementsout):
--print("ProcessDeclared - mark_item")
	 Insert_Theory_Element(mark_decl(Msg), TheoryElements -> TheoryElementsout)

	   

--------------------------------------------------
'action' Process_Type_id(TYPE, Type_id, THEORY_ELEMENTS -> THEORY_ELEMENTS)

  'rule' Process_Type_id(undef_type, Typeid, TheoryElements  -> TheoryElementsout):
	 Typeid'Ident -> Ident
	 where(theory_decl(type_decl(list(Ident, nil), nil, nil, undefined_type, nil))
	         -> TheoryElement)
	 Insert_Theory_Element(TheoryElement, TheoryElements -> TheoryElementsout)

  'rule' Process_Type_id(sort(SortKind), Typeid, TheoryElements  -> TheoryElementsout):
	 Process_Sort_Kind(SortKind, Typeid, TheoryElements  -> TheoryElementsout)

  'rule' Process_Type_id(abbrev(TypeExpr), Typeid, TheoryElements  -> TheoryElementsout):
	 Typeid'Ident -> Ident
	 Typeid'Def -> Def
	 
	 Process_abbrev(Typeid, Def, TheoryElements -> TheoryElementsout)

	   

--------------------------------------------------
'action' Process_Value_id(Value_id, VALUE_DEFINITION, THEORY_ELEMENTS -> THEORY_ELEMENTS)

	 -- No Value Definition
  'rule' Process_Value_id(Valueid, no_def, TheoryElements -> TheoryElementsout):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> Ident
	 Gen_PVS_Id_Op(Pos, Ident -> IdOp)
	 Valueid'Type -> TypeExpr

	 where(TheoryElements -> TheoryElements2)

	 Gen_PVS_Type_Expr(Pos, TypeExpr -> PVSTypeExpr)
	 where(theory_decl(const_decl(
			     nodef(list(IdOp, nil),
                                   PVSTypeExpr, no_def)))
               -> TheoryElement
              )
	 Insert_Theory_Element(TheoryElement, TheoryElements2 -> TheoryElementsout)

	 -- Explicit Value Definition
  'rule' Process_Value_id(Valueid, expl_val(ValExpr, _), TheoryElements -> TheoryElementsout):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> Ident
	 (| -- explicit values stored as disambiguations (from cpp)
	   where(ValExpr -> disamb(Pos2, ValExprDis, _))
	 ||
	   where(ValExpr -> ValExprDis)
	 |)
	 Gen_PVS_Id_Op(Pos, Ident -> IdOp)
	 Valueid'Type -> TypeExpr
	 Valueid'Def -> ValDef
	 
	 -- CC lemma
	 CCGenerate(ValExprDis, nil)
	 GetCcVar(-> Cc)
	 (|
	   eq(Cc, no_val)
	   where(TheoryElements -> TheoryElements3)
	 ||
	   Gen_PVS_Expr(Cc -> PVSCc)
	   CcLemmaName(Ident -> Strng)
	   where(theory_decl(formula_decl(Strng, lemma, PVSCc))
								  -> CcEl)
	   Insert_Theory_Element(CcEl, TheoryElements -> TheoryElements3)
	 |)

	 Gen_PVS_Type_Expr(Pos, TypeExpr -> PVSTypeExpr)
	 Gen_PVS_Expr(ValExprDis -> PVSExpr)
	 where(theory_decl(const_decl(
		             expl_const(list(IdOp, nil),
			                PVSTypeExpr, PVSExpr)))
               -> TheoryElement
              )
	 Insert_Theory_Element(TheoryElement, TheoryElements3 -> TheoryElementsout)

	 -- Implicit Value Definition
  'rule' Process_Value_id(Valueid, impl_val(ValExpr), TheoryElements -> TheoryElementsout):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> Ident
	 Gen_PVS_Id_Op(Pos, Ident -> IdOp)
	 Valueid'Type -> TypeExpr
	 
	 -- CC lemma
	 CCGenerate(ValExpr, nil)
	 GetCcVar(-> Cc)
	 (|
	   eq(Cc, no_val)
	   where(TheoryElements -> TheoryElements3)
	 ||
	   Gen_PVS_Expr(Cc -> PVSCc)
	   CcLemmaName(Ident -> Strng)
	   where(theory_decl(formula_decl(Strng, lemma, PVSCc)) -> CcEl)
	   Insert_Theory_Element(CcEl, TheoryElements -> TheoryElements3)
	 |)

	 Gen_PVS_Type_Expr(Pos, TypeExpr -> PVSTypeExpr)
	 Gen_PVS_Expr(ValExpr -> PVSExpr)
	 where(theory_decl(const_decl(
			     impl_const(list(IdOp, nil),
                                        PVSTypeExpr, PVSExpr)))
               -> TheoryElement
              )
	 Insert_Theory_Element(TheoryElement, TheoryElements3
                               -> TheoryElementsout)

	 -- Explicit Function Signature (from mutual recursion)
	 -- (also used for explicit function)
  'rule' Process_Value_id(Valueid, expl_fun(Params, no_val,
				            PostCond, PreCond,
				            _, _),
                          TheoryElements -> TheoryElementsout):
	 Valueid'Pos -> PosVid
	 Valueid'Ident -> Ident
	 Gen_PVS_Id_Op(PosVid, Ident -> IdOp)
	 Valueid'Type -> TypeExpr
	 Gen_PVSFormal_Parameters(Params, TypeExpr -> PVSParams)
	 Gen_PVS_Type_Expr(PosVid, TypeExpr -> PVSTypeExpr)
	 (|
	   where(PreCond -> pre_cond(Pos, Pre))
	   Gen_PVS_Expr(Pre -> PVSPreCond)
	 ||
	   where(PVS_EXPR'nil -> PVSPreCond)
	 |)
  	 where(theory_decl(const_decl(
			     expl_fun_const(IdOp, nil, PVSParams, 
                                            PVSTypeExpr, nil, PVSPreCond)))
	         -> TheoryElement
                )
	 Insert_Theory_Element(TheoryElement, TheoryElements ->
						TheoryElementsout)

	 -- Explicit Function Definition
  'rule' Process_Value_id(Valueid, expl_fun(Params, ValExpr,
				            PostCond, PreCond,
				            OptCond, _),
                          TheoryElements -> TheoryElementsout):
	 Valueid'Pos -> PosVid

	 Collect_Value_ids(ValExpr, nil -> DeclaredsValVE)
	 (|
	   Is_Recursive_Function(Valueid, DeclaredsValVE)
	   where(recursive -> Recursive)
	 ||
	   where(RECURSIVE'nil -> Recursive)
	 |)

	 Valueid'Type -> T
	 Make_function_type(T -> fun(D, ARR, result(R,RD,WR,IN,OUT)))
	 (|
	   (| Maximal(R) || eq(Recursive, nil) |)
	   where(RECURSIVE_SUBTYPE'nil -> RecSub)
	 ||
	   Maxtype(R -> RM)
	   Valueid'Type <- fun(D, ARR, result(RM,RD, WR,IN,OUT))
	   where(recursive_subtype -> RecSub) 
	 |)

	 Valueid'Ident -> Ident
	 Gen_PVS_Id_Op(PosVid, Ident -> IdOp)

         -- Valueid'Type may have changed:
	 Valueid'Type -> TypeExpr

	 Gen_PVSFormal_Parameters(Params, TypeExpr -> PVSParams)

	 Gen_PVS_Type_Expr(PosVid, TypeExpr -> PVSTypeExpr)
	 Gen_PVS_Expr(ValExpr -> PVSExpr)
	 (|
	   where(PreCond -> pre_cond(Pos, Pre))
	   Gen_PVS_Expr(Pre -> PVSPreCond)
	 ||
	   where(PVS_EXPR'nil -> PVSPreCond)
	 |)

	 where(theory_decl(const_decl(
			     expl_fun_const(IdOp, Recursive, PVSParams, 
                                            PVSTypeExpr, PVSExpr, PVSPreCond)))
	         -> TheoryElement
                )
	 -- CC lemma
	 -- replace original type
	 Valueid'Type <- T
	 Parms_to_typings(Params, T -> TPS)
	 Gen_PVS_Type_Expr(PosVid, T -> PVST)
	 (|
	   where(PreCond -> pre_cond(P2, C))
	   CCGenerate(C, list(typings(TPS), nil))
	 ||
	   where(VALUE_EXPR'literal_expr(PosVid, bool_true) -> C)
	 |)
	 CCGenerate(ValExpr, list(assumption(C), list(typings(TPS), nil)))
--	 [|
--	   -- include subtype correctness of result
--	   -- for recursive functions, since not generated as a TCC
--	   -- by PVS
--	   eq(Recursive, recursive)
--	   Generate(ccvaluedef(exp_fun(PosVid, single(PosVid,single(PosVid,Ident),TypeExpr), form_appl(PosVid,Ident,Params), ValExpr, PostCond, PreCond)),PosVid,no_def,nil)
--	 |]
	 GetCcVar(-> Cc)
	 (|
	   eq(Cc, no_val)
	   Insert_Theory_Element(TheoryElement, TheoryElements ->
						TheoryElements2)
	 ||
	   Gen_PVS_Expr(Cc -> PVSCc)
	   CcLemmaName(Ident -> Strng)
	   where(theory_decl(formula_decl(Strng, lemma, PVSCc)) -> CcEl)
	   (|
	     eq(Recursive, nil)
	     Insert_Theory_Element(CcEl, TheoryElements -> TheoryElements1)
	     Insert_Theory_Element(TheoryElement, TheoryElements1 ->
						TheoryElements2)
	   ||
	     -- must put definition first as CC lemma may use function name
	     Insert_Theory_Element(TheoryElement, TheoryElements ->
						TheoryElements1)
	     Insert_Theory_Element(CcEl, TheoryElements1 -> TheoryElements2)
	   |)
	 |)
	 (|
	   eq(RecSub, recursive_subtype)
	   JudgementName(Ident -> Str)
	   where(theory_decl(judgement_decl(Str, IdOp, PVSParams,
						 PVST, PVSPreCond))
								  -> JEl)
	   Insert_Theory_Element(JEl, TheoryElements2 -> TheoryElements3)
	 ||
	   where(TheoryElements2 -> TheoryElements3)
	 |)
	 -- optional postcondition
	 (|
	   where(PostCond -> post(Post))
	   CcLemmaName(Ident -> PStr)
	   Get_fun_result_type(Params, TypeExpr -> Result)
	   Gen_PostCond(Post, Result -> PVSPost)
	   where(theory_decl(post_decl(PStr, IdOp, PVSParams,
					     PVST, PVSPost, PVSPreCond))
			 					  -> PEl)
	   Insert_Theory_Element(PEl, TheoryElements3 -> TheoryElementsout)
	 ||
	   where(TheoryElements3 -> TheoryElementsout)
	 |)



	 -- Implicit Function Definition
  'rule' Process_Value_id(Valueid, impl_fun(Params, Post,
				            PreCond,
					    OptCond),
			    TheoryElements -> TheoryElementsout):
	 Valueid'Pos -> Pos
	 Valueid'Ident -> Ident
	 Gen_PVS_Id_Op(Pos, Ident -> IdOp)
	 Valueid'Type -> TypeExpr

	 Gen_PVSFormal_Parameters(Params, TypeExpr -> PVSParams)

	 Gen_PVS_Type_Expr(Pos, TypeExpr -> PVSTypeExpr)
	 Get_fun_result_type(Params, TypeExpr -> Result)
	 Gen_PostCond(Post, Result -> PVSPost)
	 (|
	   where(PreCond -> pre_cond(Pos2, Pre))
	   Gen_PVS_Expr(Pre -> PVSPreCond)
	 ||
	   where(PVS_EXPR'nil -> PVSPreCond)
	 |)

	 -- CC lemma
	 Parms_to_typings(Params, TypeExpr -> TPS)
	 (|
	   where(PreCond -> pre_cond(P2, C))
	   CCGenerate(C, list(typings(TPS), nil))
	 ||
	   where(VALUE_EXPR'literal_expr(Pos, bool_true) -> C)
	 |)
	 where(Post -> post_cond(P1,R,E))
	 (|
	   where(R -> result(P3, B))
	   where(TypeExpr -> fun(_, _, result(T1,_,_,_,_)))
	   where(TYPINGS'list(single(P3, B, T1), nil) -> TPSR)
	 ||
	   where(TYPINGS'nil -> TPSR)
	 |)
	 CCGenerate(E, list(typings(TPSR), list(assumption(C), list(typings(TPS), nil))))
	 GetCcVar(-> Cc)
	 (|
	   eq(Cc, no_val)
	   where(TheoryElements -> TheoryElements3)
	 ||
	   Gen_PVS_Expr(Cc -> PVSCc)
	   CcLemmaName(Ident -> Strng)
	   where(theory_decl(formula_decl(Strng, lemma, PVSCc)) -> CcEl)
	   Insert_Theory_Element(CcEl, TheoryElements -> TheoryElements3)
	 |)

	 where(theory_decl(const_decl(
                             impl_fun_const(IdOp,
                                            PVSParams,
					    PVSTypeExpr,
					    PVSPost,
					    PVSPreCond)))
               -> TheoryElement
              )
	 Insert_Theory_Element(TheoryElement, TheoryElements3 -> TheoryElementsout)

'action' Get_fun_result_type(FORMAL_FUNCTION_PARAMETERS, TYPE_EXPR -> TYPE_EXPR)

  'rule' Get_fun_result_type(list(_, Parms), T -> T2):
	 Split_fun_type(T -> _, T1)
	 Get_fun_result_type(Parms, T1 -> T2)

  'rule' Get_fun_result_type(nil, T -> T):

--------------------------------------------------
'action' Process_Axiom_id(Axiom_id, THEORY_ELEMENTS -> THEORY_ELEMENTS)

  'rule' Process_Axiom_id(Axiomid, TheoryElements -> TheoryElementsout):
	 Axiomid'Ident -> OptIdent
	 Axiomid'Axiom -> ValueExpr
	 (|
	   where(OptIdent -> ident(Ident))
	   id_to_string(Ident -> Strng)
	 ||
	   where(OptIdent -> nil)
	   where("" -> Strng)
	   string_to_id("axiom" -> Ident)
	 |)

	 -- CC lemma
	 CCGenerate(ValueExpr, nil)
	 GetCcVar(-> Cc)
	 (|
	   eq(Cc, no_val)
	   where(TheoryElements -> TheoryElements1)
	 ||
	   Gen_PVS_Expr(Cc -> PVSCc)
	   CcLemmaName(id_op(Ident) -> Strngcc)
	   where(theory_decl(formula_decl(Strngcc, lemma, PVSCc))
								  -> CcEl)
	   Insert_Theory_Element(CcEl, TheoryElements -> TheoryElements1)
	 |)

	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
/*
print("-------------------------------")
Putmsg("Axiom - ValueExpr: ")
print(IdentAx)
print(ValueExpr)
*/
	 where(theory_decl(formula_decl(Strng, axiom,
                           PVSExpr)) -> TheoryElement)
	 Insert_Theory_Element(TheoryElement, TheoryElements1 ->
                               TheoryElementsout)


--------------------------------------------------
'action' Process_Lemma_item(Axiom_id, THEORY_ELEMENTS -> THEORY_ELEMENTS)

  'rule' Process_Lemma_item(Axiomid, TheoryElements -> TheoryElementsout):
	 Axiomid'Ident -> OptIdent
	 Axiomid'Axiom -> ValueExpr
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
--Print_Axiom_id(Axiomid, " lemma_item")
	 (|
	   where(OptIdent -> ident(Ident))
	   id_to_string(Ident -> Strng)
	 ||
	   where("" -> Strng)
	 |)
	 where(theory_decl(formula_decl(Strng, lemma,
                           PVSExpr)) -> TheoryElement)
	 Insert_Theory_Element(TheoryElement, TheoryElements ->
                               TheoryElementsout)


--------------------------------------------------
'action' Process_Sort_Kind(SORT_KIND, Type_id, THEORY_ELEMENTS -> THEORY_ELEMENTS)

  'rule' Process_Sort_Kind(abstract, Typeid, TheoryElements -> TheoryElementsout):
	 Typeid'Ident -> Ident
	 where(theory_decl(type_decl(list(Ident, nil), nil, nil, uninterpreted_type, nil))
	     -> TheoryElement1)
	 Insert_Theory_Element(TheoryElement1, TheoryElements  -> TheoryElementsout)

  'rule' Process_Sort_Kind(record(Components), Typeid, TheoryElements -> TheoryElementsout):
	 Process_Record_Kind(Typeid, Components, TheoryElements -> TheoryElementsout)

  'rule' Process_Sort_Kind(variant(Variants), Typeid, TheoryElements -> TheoryElementsout):
	 Process_Variant_Kind(Typeid, Variants, TheoryElements -> TheoryElementsout)
	     
	 -- @@ incomplete, not supported?
  'rule' Process_Sort_Kind(union(Choices), Typeid, TheoryElements -> TheoryElementsout):
	 Typeid'Ident -> Ident
	 where(theory_decl(type_decl(list(Ident, nil), nil, nil, union_type,
	                                 nil)) -> TheoryElement1)
	 Insert_Theory_Element(TheoryElement1, TheoryElements  -> TheoryElementsout)


--------------------------------------------------
'action' Process_abbrev(Type_id, TYPE_DEFINITION, THEORY_ELEMENTS -> THEORY_ELEMENTS)

  'rule' Process_abbrev(Typeid, no_def, TheoryElements -> TheoryElementsout):
	 Typeid'Ident -> Ident
	 where(theory_decl(type_decl(list(Ident, nil), nil, nil, undefined_type,
	                                 nil)) -> TheoryElement1)
	 Insert_Theory_Element(TheoryElement1, TheoryElements  -> TheoryElementsout)

  'rule' Process_abbrev(Typeid, abbreviation(TypeExpr), TheoryElements -> TheoryElementsout):
	 Typeid'Ident -> Ident
	 Typeid'Pos -> Pos

	 -- CC lemma
	 CCGenerate_type(TypeExpr, nil)
	 GetCcVar(-> Cc)
	 (|
	   eq(Cc, no_val)
	   where(TheoryElements -> TheoryElements1)
	 ||
	   Gen_PVS_Expr(Cc -> PVSCc)
	   CcLemmaName(id_op(Ident) -> Strng)
	   where(theory_decl(formula_decl(Strng, lemma, PVSCc))
								  -> CcEl)
	   Insert_Theory_Element(CcEl, TheoryElements -> TheoryElements1)
	 |)

	 Gen_PVS_Type_Expr(Pos, TypeExpr -> PVSTypeExpr)
	 where(theory_decl(type_decl(list(Ident, nil), nil, equal,
	                         PVSTypeExpr, nil)) -> TheoryElement1)
	 Insert_Theory_Element(TheoryElement1, TheoryElements1  -> TheoryElementsout)



--------------------------------------------------
'action' Process_Variant_Kind(Type_id, VARIANTS, THEORY_ELEMENTS -> THEORY_ELEMENTS)

  'rule' Process_Variant_Kind(Typeid, Variants, TheoryElements
                         -> TheoryElementsout):
	 Typeid'Ident -> Ident
	 Process_Variants(Variants, nil -> DataTypeParts)
	 where(theory_decl(inline_datatype(Ident, DataTypeParts))
	         -> TheoryElement)
/*
print("------------------")
print("DataTypeParts")
print(DataTypeParts)
*/
	 Insert_Theory_Element(TheoryElement, TheoryElements
                               -> TheoryElements1)
	 Variant_Reconstructors_to_Theory_Elements(Variants, TheoryElements1
						       -> TheoryElementsout)


--------------------------------------------------
'action' Process_Variants(VARIANTS, DATA_TYPE_PARTS -> DATA_TYPE_PARTS)

	 --                    <-------------- Variant --------------->
  'rule' Process_Variants(list(record(Pos, 
	 --                           <-- Constructor --->
                                      con_ref(Valueid), Components),
                          VariantsTail), DataTypeParts
                          -> DataTypePartsout):
         Valueid'Pos -> Pos2
         Valueid'Ident -> IdorOp
	 Gen_PVS_Id_Op(Pos2, IdorOp -> IdOp)
         Process_Components(Components, nil -> Accesors)
	 --    <---- PVS_Constructor ------->
	 where(construct(IdOp, Accesors) -> PVSConstructor)
	 --    <------ DataTypePart -------->
	 where(part(PVSConstructor, nil, nil) -> DataTypePart)
	 Insert_DataTypePart(DataTypePart, DataTypeParts -> DataTypeParts1)
	 Process_Variants(VariantsTail, DataTypeParts1
	                  -> DataTypePartsout)

  'rule' Process_Variants(list(record(Pos, wildcard, _), VariantsTail),
					   DataTypeParts -> DataTypePartsout)
         Puterror(Pos)
	 Putmsg("Wildcard variants not supported")
	 Process_Variants(VariantsTail, DataTypeParts -> DataTypePartsout)

  'rule' Process_Variants(nil, DataTypeParts -> DataTypeParts):


--------------------------------------------------
'action' Process_Record_Kind(Type_id, COMPONENTS, THEORY_ELEMENTS -> THEORY_ELEMENTS)

  'rule' Process_Record_Kind(Typeid, Components, TheoryElements
                                              -> TheoryElementsout):
	 Typeid'Ident -> Ident
	 id_to_string(Ident -> StringId)
	 Concatenate("mk_" , StringId -> StringConst)
	 string_to_id(StringConst -> IdConst)
	 where(ID_OP'id(IdConst) -> IdOp)
         Process_Components(Components, nil -> Accesors)
	 --    <---- PVS_Constructor ------->
	 where(construct(IdOp, Accesors) -> PVSConstructor)
	 --    <------ DataTypePart -------->
	 where(part(PVSConstructor, nil, nil) -> DataTypePart)
	 Insert_DataTypePart(DataTypePart, nil -> DataTypeParts)
	 where(theory_decl(inline_datatype(Ident, DataTypeParts))
	         -> TheoryElement)
	 Insert_Theory_Element(TheoryElement, TheoryElements
                                      -> TheoryElements1)
	 Record_Reconstructors_to_Theory_Elements(Components, TheoryElements1
						       -> TheoryElementsout)

--------------------------------------------------
'action' Add_destructors(Type_id)

-- insert any missing destructors
  'rule' Add_destructors(I):
	 [|
	   I'Type -> sort(K)
	   (|
	     where(K -> variant(VS))
	     Add_destructors_to_variants(I, partial, VS, 0 -> VS1)
	     I'Type <- sort(variant(VS1))
	   ||
	     where(K -> record(CS))
	     Add_destructors_to_components(I, total, CS, 0 -> CS1, _)
	     I'Type <- sort(record(CS1))
	   |)
	 |]

'action' Add_destructors_to_variants(Type_id, FUNCTION_ARROW, VARIANTS, INT -> VARIANTS)

  'rule' Add_destructors_to_variants(I, Arr, list(V, VS), N -> list(V1, VS1)):
	 Add_destructors_to_variant(I, Arr, V, N -> V1, N1)
	 Add_destructors_to_variants(I, Arr, VS, N1 -> VS1)

  'rule' Add_destructors_to_variants(_, _, nil, _ -> nil):

'action' Add_destructors_to_variant(Type_id, FUNCTION_ARROW, VARIANT, INT -> VARIANT, INT)

  'rule' Add_destructors_to_variant(I, Arr, record(P, C, CS), N ->
					      record(P, C, CS1), N1):
	 Add_destructors_to_components(I, Arr, CS, N -> CS1, N1)

'action' Add_destructors_to_components(Type_id, FUNCTION_ARROW, COMPONENTS, INT -> COMPONENTS, INT)

  'rule' Add_destructors_to_components(I, Arr, list(C, CS), N -> list(C1, CS1), N1):
	 Add_destructor_to_component(I, Arr, C, N -> C1, N2)
	 Add_destructors_to_components(I, Arr, CS, N2 -> CS1, N1)

  'rule' Add_destructors_to_components(_, _, nil, N -> nil, N):

'action' Add_destructor_to_component(Type_id, FUNCTION_ARROW, COMPONENT, INT -> COMPONENT, INT)

  'rule' Add_destructor_to_component(I, Arr, component(P, nil, T, R), N ->
						  component(P, D, T, R), N+1)
	 Int_to_string(N -> S)
	 Concatenate3("acc_", S, "_" -> AccS)
	 string_to_id(AccS -> AccId)
	 New_value_id(P, id_op(AccId) -> AccI)
	 AccI'Type <- fun(defined(I, nil), Arr, result(T,nil,nil,nil,nil))
	 where(dest_ref(AccI) -> D)
	 Putwarning(P)
	 Putmsg("accessor ")
	 Putmsg(AccS)
	 Putmsg(" generated")
	 Putnl()

  'rule' Add_destructor_to_component(_, _, C, N -> C, N):



--------------------------------------------------
'action' Process_Components(COMPONENTS, ACCESORS -> ACCESORS)

-- any missing destructors added earlier
         
	 -- Destructor and Reconstructor
  'rule' Process_Components(list(component(Pos,
			                   dest_ref(ValueidDestruct),
					   TypeExpr,
			                   recon_ref(ValueidRecons)),
                            ComponentsTail),
                            Accesors -> Accesorsout):
	 -- Destructor to Accesor
	 ValueidDestruct'Pos -> Pos2
	 ValueidDestruct'Ident -> IdDestruct
	 Gen_PVS_Id_Op(Pos2, IdDestruct -> IdOpAcc1)
	 Gen_PVS_Type_Expr(Pos, TypeExpr -> PVSTypeExpr)
         where(accesor(list(IdOpAcc1, nil), PVSTypeExpr) -> Accesor)
	 Insert_Accesor(Accesor, Accesors -> Accesors1)
         Process_Components(ComponentsTail, Accesors1 -> Accesorsout)
         
	 -- Destructor and No Reconstructor
  'rule' Process_Components(list(component(Pos,
			                   dest_ref(ValueidDestruct),
					   TypeExpr,
			                   nil),
                            ComponentsTail),
                            Accesors -> Accesorsout):
	 -- Destructor to Accesor
	 ValueidDestruct'Pos -> Pos2
	 ValueidDestruct'Ident -> IdDestruct
	 Gen_PVS_Id_Op(Pos2, IdDestruct -> IdOpAcc1)
	 Gen_PVS_Type_Expr(Pos, TypeExpr -> PVSTypeExpr)
         where(accesor(list(IdOpAcc1, nil), PVSTypeExpr) -> Accesor)
	 Insert_Accesor(Accesor, Accesors -> Accesors1)
         Process_Components(ComponentsTail, Accesors1 -> Accesorsout)
         
  'rule' Process_Components(nil, Accesors -> Accesors)
--------------------------------------------------
'action' Record_Reconstructors_to_Theory_Elements(COMPONENTS, THEORY_ELEMENTS
						       -> THEORY_ELEMENTS)

  'rule' Record_Reconstructors_to_Theory_Elements(list(C, CS), TES -> TESOut):
	 (|
	   where(C -> component(_, _, _, recon_ref(I)))
	   I'Def -> Def
	   Process_Value_id(I, Def, TES -> TES1)
	 ||
	   where(TES -> TES1)
	 |)
	 Record_Reconstructors_to_Theory_Elements(CS, TES1 -> TESOut)

  'rule' Record_Reconstructors_to_Theory_Elements(nil, TES -> TES):

'action' Variant_Reconstructors_to_Theory_Elements(VARIANTS, THEORY_ELEMENTS
						       -> THEORY_ELEMENTS)

  'rule' Variant_Reconstructors_to_Theory_Elements(list(V, VS), TES -> TESOut)
	 where(V -> record(_, _, Comps))
	 Record_Reconstructors_to_Theory_Elements(Comps, TES -> TES1)
	 Variant_Reconstructors_to_Theory_Elements(VS, TES1 -> TESOut)

  'rule' Variant_Reconstructors_to_Theory_Elements(nil, TES -> TES):



--------------------------------------------------
'action' Gen_PVSFormal_Parameters(FORMAL_FUNCTION_PARAMETERS, TYPE_EXPR
                                  -> PVS_FORMAL_FUN_PARAMETERS)

  'rule' Gen_PVSFormal_Parameters(list(form_parm(Pos, Bindings), ParamsTail),
			          TypeExpr
         			  -> list(ParamOut, ParamsOut)):
	 Split_fun_type(TypeExpr -> T1, T2)
	 Debracket_abbrev(T1 -> T11)
	 Debracket_bindings(Bindings -> BS)
	 Gen_PVSFormal_Parameter(BS, T11 -> ParamOut)
	 Gen_PVSFormal_Parameters(ParamsTail, T2 -> ParamsOut)

  'rule' Gen_PVSFormal_Parameters(nil, T -> nil):


'action' Gen_PVSFormal_Parameter(BINDINGS, TYPE_EXPR -> PVS_BINDINGS)

  'rule' Gen_PVSFormal_Parameter(list(single(P, Id), nil), T -> list(Parm, nil)):
	 Gen_PVS_Id_Op(P, Id -> Idop)
	 Gen_PVS_Type_Expr(P, T -> PVST)
	 where(typed_id(Idop, PVST) -> Parm)

  'rule' Gen_PVSFormal_Parameter(list(single(P, Id), BS),
				 product(list(T, TS)) -> list(Parm, Parms)):
	 Gen_PVS_Id_Op(P, Id -> Idop)
	 Gen_PVS_Type_Expr(P, T -> PVST)
	 where(typed_id(Idop, PVST) -> Parm)
	 Gen_PVSFormal_Parameter(BS, product(TS) -> Parms)

  'rule' Gen_PVSFormal_Parameter(list(product(P, BS1), BS2),
				 product(list(T, TS)) -> list(Parm, Parms)):
	 Gen_PVSBindings(BS1 -> PVSBindings)
	 Gen_PVS_Type_Expr(P, T -> PVST)
	 where(typed_prod(PVSBindings, PVST) -> Parm)
	 Gen_PVSFormal_Parameter(BS2, product(TS) -> Parms)

  'rule' Gen_PVSFormal_Parameter(nil, _ -> nil): 

  'rule' Gen_PVSFormal_Parameter(BS, T -> list(Parm, nil)):
	 Gen_PVSBindings(BS -> PVSBindings)
	 DefaultPos(->P)
	 Gen_PVS_Type_Expr(P, T -> PVST)
	 where(typed_prod(PVSBindings, PVST) -> Parm)


'action' Gen_PVSBindings(BINDINGS -> PVS_BINDINGS)

  'rule' Gen_PVSBindings(list(B, BS) -> list(B1, BS1)):
	 Gen_PVSBinding(B -> B1)
	 Gen_PVSBindings(BS -> BS1)

  'rule' Gen_PVSBindings(nil -> nil):

'action' Gen_PVSBinding(BINDING -> PVS_BINDING)

  'rule' Gen_PVSBinding(single(P, Id) -> typed_id(Idop, nil)):
	 Gen_PVS_Id_Op(P, Id -> Idop)

  'rule' Gen_PVSBinding(product(_, BS) -> prod_binding(BS1)):
	 Gen_PVSBindings(BS -> BS1)

'action' Gen_PVSBindings_from_Typings(TYPINGS -> PVS_BINDINGS)

  'rule' Gen_PVSBindings_from_Typings(list(TP, TPS) -> BS):
	 Gen_PVSBindings_from_Typing(TP -> BS1)
	 Gen_PVSBindings_from_Typings(TPS -> BS2)
	 Concat_PVSBindings(BS1, BS2 -> BS)

  'rule' Gen_PVSBindings_from_Typings(nil -> nil)

'action' Gen_PVSBindings_from_Typing(TYPING -> PVS_BINDINGS)

  'rule' Gen_PVSBindings_from_Typing(single(P, single(_, Id), T) ->
					list(typed_id(IdOp, PVST), nil)):
	 Gen_PVS_Id_Op(P, Id -> IdOp)
	 Gen_PVS_Type_Expr(P, T -> PVST)

  'rule' Gen_PVSBindings_from_Typing(single(P, product(P1, list(B, BS)), T0) 
								   -> BS3):
	 Debracket_abbrev(T0 -> product(list(T, TS)))
	 Gen_PVSBindings_from_Typing1(single(P, B, T) -> BS1)
	 Gen_PVSBindings_from_Typing(single(P, product(P1, BS), product(TS))
								 -> BS2)
	 Concat_PVSBindings(BS1, BS2 -> BS3)

  'rule' Gen_PVSBindings_from_Typing(single(P, product(P1, nil), _) -> nil):

  'rule' Gen_PVSBindings_from_Typing(single(P, product(_, BS), T) ->
							  list(PB, nil)):
	 Gen_PVSBindings(BS -> PBS)
	 Gen_PVS_Type_Expr(P, T -> PVST)
	 where(typed_prod(PBS, PVST) -> PB)

  'rule' Gen_PVSBindings_from_Typing(multiple(P, list(B, BS), T) -> BS3):
	 Gen_PVSBindings_from_Typing(single(P, B, T) -> BS1)
	 Gen_PVSBindings_from_Typing(multiple(P, BS, T) -> BS2)
	 Concat_PVSBindings(BS1, BS2 -> BS3)

  'rule' Gen_PVSBindings_from_Typing(multiple(P, nil, _) -> nil):

-- no further nesting allowed now
'action' Gen_PVSBindings_from_Typing1(TYPING -> PVS_BINDINGS)

  'rule' Gen_PVSBindings_from_Typing1(single(P, single(_, Id), T) ->
					list(typed_id(IdOp, PVST), nil)):
	 Gen_PVS_Id_Op(P, Id -> IdOp)
	 Gen_PVS_Type_Expr(P, T -> PVST)

  'rule' Gen_PVSBindings_from_Typing1(single(P, product(_, BS), T) ->
							  list(PB, nil)):
	 Gen_PVSBindings(BS -> PBS)
	 Gen_PVS_Type_Expr(P, T -> PVST)
	 where(typed_prod(PBS, PVST) -> PB)

	 

'action' Concat_PVSBindings(PVS_BINDINGS, PVS_BINDINGS -> PVS_BINDINGS)

  'rule' Concat_PVSBindings(list(B, BS), BS1 -> list(B, BS2)):
	 Concat_PVSBindings(BS, BS1 -> BS2)

  'rule' Concat_PVSBindings(nil, BS -> BS)



--------------------------------------------------

'action' Debracket_abbrev(TYPE_EXPR -> TYPE_EXPR)

-- removes brackets and expands definitions (in the hope of finding
-- products) but does not remove subtypes

  'rule' Debracket_abbrev(bracket(T) -> T1):
	 Debracket_abbrev(T -> T1)

  'rule' Debracket_abbrev(defined(I, _) -> T1):
	 I'Def -> abbreviation(T2)
	 Debracket_abbrev(T2 -> T1)

  'rule' Debracket_abbrev(T -> T):

'action' Debracket_bindings(BINDINGS -> BINDINGS)

-- removes unnecessary brackets as in ((x,y)) (making (x,y))

  'rule' Debracket_bindings(list(product(_, BS), nil) -> BS1):
	 Debracket_bindings(BS -> BS1)

  'rule' Debracket_bindings(BS -> BS):

--------------------------------------------------
'action' Gen_PostCond(POST_CONDITION, TYPE_EXPR -> PVS_POST_COND)

  'rule' Gen_PostCond(post_cond(Pos, result(Pos2, Binding), Expr), TypeExpr
				      -> PVSPost):
	 Gen_PVSBindings_from_Typing(single(Pos2, Binding, TypeExpr) -> PVSBindings)
	 Gen_PVS_Expr(Expr -> PVSExpr)
	 where(postcond(PVSBindings, PVSExpr) -> PVSPost)

  'rule' Gen_PostCond(post_cond(Pos, nil, Expr), _ -> PVSPost):
	 Gen_PVS_Expr(Expr -> PVSExpr)
	 where(postcond(nil, PVSExpr) -> PVSPost)


--------------------------------------------------
--  RSL Type Expression  ==>  PVS Type Expression
--------------------------------------------------


--------------------------------------------------
'action' Gen_PVS_Type_Expr(POS, TYPE_EXPR -> PVS_TYPE_EXPR)

  'rule' Gen_PVS_Type_Expr(Pos, unit -> PVSTypeExprout):
	 where(PVS_TYPE_EXPR'not_supported -> PVSTypeExprout)
	 Puterror(Pos)
	 Putmsg("Unit type not supported")
	 Putnl()

  'rule' Gen_PVS_Type_Expr(Pos, bool -> PVSTypeExprout):
	 where(PVS_TYPE_EXPR'bool -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, int -> PVSTypeExprout):
	 where(PVS_TYPE_EXPR'int -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, nat -> PVSTypeExprout):
	 where(PVS_TYPE_EXPR'nat -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, real -> PVSTypeExprout):
	 where(PVS_TYPE_EXPR'real -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, text -> PVSTypeExprout):
	 where(PVS_TYPE_EXPR'text -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, char -> PVSTypeExprout):
	 where(PVS_TYPE_EXPR'char -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, time -> PVSTypeExprout):
	 where(PVS_TYPE_EXPR'nil -> PVSTypeExprout)
	 Puterror(Pos)
	 Putmsg("Time type not supported")
	 Putnl()

  'rule' Gen_PVS_Type_Expr(Pos, defined(Typeid, OptQual) -> PVSTypeExprout):
	 Typeid'Type -> Type
	 Typeid'Pos -> Pos2
	 Typeid'Ident -> Ident
	 Typeid'Qualifier -> Ids
	 Gen_PVS_Qualification(OptQual, Ids -> NameQual)
	 (| -- undef_type
	   where(Type -> undef_type)
	   where(PVS_TYPE_EXPR'named_type(id(Ident), NameQual) -> PVSTypeExprout)
	   print("undefined type")
	 || -- Abstract
	   where(Type -> sort(abstract))
	   where(PVS_TYPE_EXPR'named_type(id(Ident), NameQual) -> PVSTypeExprout)
	 || -- Record
	   where(Type -> sort(record(_)))
	   where(PVS_TYPE_EXPR'named_type(id(Ident), NameQual) -> PVSTypeExprout)
	 || -- Variant
	   where(Type -> sort(variant(_)))
	   where(PVS_TYPE_EXPR'named_type(id(Ident), NameQual) -> PVSTypeExprout)
	 || -- 
	   where(Type -> sort(union(_)))
	   where(PVS_TYPE_EXPR'named_type(id(Ident), NameQual) -> PVSTypeExprout)
	   Puterror(Pos2)
	   Putmsg("union type not supported")
	   Putnl()
	 || -- abbrev
	   where(Type -> abbrev(_))
	   (| -- no_def
	     Typeid'Def -> no_def
	     where(PVS_TYPE_EXPR'named_type(id(Ident), NameQual) -> PVSTypeExprout)
	   || -- abbreviation
	     Typeid'Def -> abbreviation(TypeExpr)
--	     Gen_PVS_Type_Expr(Pos, TypeExpr -> PVSTypeExprout)
	     where(PVS_TYPE_EXPR'named_type(id(Ident), NameQual) -> PVSTypeExprout)
	   |)
	 |)

  'rule' Gen_PVS_Type_Expr(Pos, named_type(Name) -> PVSTypeExprout):
	 (|
	   where(Name -> name(_, id_op(Ident)))
	   where(PVS_TYPE_EXPR'named_type(id(Ident), nil) -> PVSTypeExprout)
	 ||
	   where(Name -> qual_name(_, ObjExpr, IdorOp))
	   Process_Object_Expr(ObjExpr -> NameQual)
	   Gen_PVS_Id_Op(Pos, IdorOp -> IdOp)
	   where(PVS_TYPE_EXPR'named_type(IdOp, NameQual) -> PVSTypeExprout)
	 |)

  'rule' Gen_PVS_Type_Expr(Pos, product(ProdType) -> PVSTypeExprout):
	 Gen_PVS_Tuple_List(Pos, ProdType, nil -> TupleList)
	 where(tuple_type(TupleList) -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, fin_set(TypeExprFS) -> PVSTypeExprout):
	 Gen_PVS_Type_Expr(Pos, TypeExprFS -> PVSTypeExpr1)
	 where(finite_set(PVSTypeExpr1) -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, infin_set(TypeExprFS) -> PVSTypeExprout):
	 Gen_PVS_Type_Expr(Pos, TypeExprFS -> PVSTypeExpr1)
	 where(infinite_set(PVSTypeExpr1) -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, fin_list(TypeExprFL) -> PVSTypeExprout):
	 Gen_PVS_Type_Expr(Pos, TypeExprFL -> PVSTypeExpr1)
	 Gen_PVS_List(PVSTypeExpr1 -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, infin_list(TypeExprFL) -> PVSTypeExprout):
	 where(PVS_TYPE_EXPR'not_supported -> PVSTypeExprout)
	 Puterror(Pos)
	 Putmsg("infinite list type not supported")
	 Putnl()

  'rule' Gen_PVS_Type_Expr(Pos, fin_map(Dom, Rng) -> PVSTypeExprout):
	 Gen_PVS_Type_Expr(Pos, Dom -> DomPVS)
	 Gen_PVS_Type_Expr(Pos, Rng -> RngPVS)
	 -- Previous map declaration already taken care of
	 where(finite_map(DomPVS, RngPVS) -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, infin_map(Dom, Rng) -> PVSTypeExprout):
	 Gen_PVS_Type_Expr(Pos, Dom -> DomPVS)
	 Gen_PVS_Type_Expr(Pos, Rng -> RngPVS)
	 -- Previous map declaration already taken care of
	 where(infinite_map(DomPVS, RngPVS) -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, fun(ParamType, _, Result) -> PVSTypeExprout):
	 Gen_PVS_Type_Expr(Pos, ParamType -> DomType)
	 where(Result -> result(TypeExpr, _, _, _, _))
	 Gen_PVS_Type_Expr(Pos, TypeExpr -> PVSResult)
	 where(fun_type(nil, DomType, PVSResult) -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, subtype(Typing, Restriction) -> PVSTypeExprout):
	 Gen_PVSBindings_from_Typing(Typing -> PVSBindings)
	 where(SETBINDING'bindings(PVSBindings) -> SetBinding)
	 Gen_PVS_Restriction(Restriction -> PVSRestriction)
	 where(PVS_TYPE_EXPR'subtype(SetBinding, PVSRestriction) -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, bracket(TypeExpr) -> PVSTypeExprout):
	 Gen_PVS_Type_Expr(Pos, TypeExpr -> PVSTypeExpr)
	 where(bracket_type(PVSTypeExpr) -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, any -> PVSTypeExprout):
	 where(PVS_TYPE_EXPR'any -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, none -> PVSTypeExprout):
	 where(PVS_TYPE_EXPR'none -> PVSTypeExprout)

  'rule' Gen_PVS_Type_Expr(Pos, poly(Num) -> PVSTypeExprout):
	 where(PVS_TYPE_EXPR'poly -> PVSTypeExprout)

-- debug
--   'rule' Gen_PVS_Type_Expr(P, T -> none)
-- Print_type(T)
-- Putnl()
-- print(T)

--------------------------------------------------
'action' Gen_PVS_Tuple_List(POS, PRODUCT_TYPE, TUPLE_LIST -> TUPLE_LIST)

  'rule' Gen_PVS_Tuple_List(Pos, list(Type1, ProdTypeTail), TupleList -> TupleListout):
	 Gen_PVS_Type_Expr(Pos, Type1 -> PVSTypeExpr1)
	 Insert_Tuple(tuple(nil, PVSTypeExpr1), TupleList -> TupleList1)
	 Gen_PVS_Tuple_List(Pos, ProdTypeTail, TupleList1 -> TupleListout)

  'rule' Gen_PVS_Tuple_List(Pos, nil, TupleList -> TupleList):


--------------------------------------------------
'action' Gen_PVS_List(PVS_TYPE_EXPR -> PVS_TYPE_EXPR)

  'rule' Gen_PVS_List(PVSTypeExpr -> PVSTypeExprout):
	 where(list_type(PVSTypeExpr) -> PVSTypeExprout)


--------------------------------------------------
'action' Gen_PVS_Restriction(RESTRICTION -> PVS_EXPR)

  'rule' Gen_PVS_Restriction(restriction(Pos, ValueExpr) -> PVSRestriction):
	 Gen_PVS_Expr(ValueExpr -> PVSRestriction)

  'rule' Gen_PVS_Restriction(nil -> PVSRestriction):
	 where(PVS_EXPR'nil -> PVSRestriction)
	 



--------------------------------------------------
--  RSL Value Expression  ==> PVS Expression
--------------------------------------------------


--------------------------------------------------
'action' Gen_PVS_ExprPairs(VALUE_EXPR_PAIRS, PVS_EXPR_PAIRS -> PVS_EXPR_PAIRS)

  'rule' Gen_PVS_ExprPairs(list(ValueExprPair, ValueExprPairsTail), PVSExprPairs -> PVSExprPairsout):
	 Gen_PVS_ExprPair(ValueExprPair -> PVSExprPair)
	 Insert_PVS_ExprPair(PVSExprPair, PVSExprPairs -> PVSExprPairs1)
	 Gen_PVS_ExprPairs(ValueExprPairsTail, PVSExprPairs1 -> PVSExprPairsout)

  'rule' Gen_PVS_ExprPairs(nil, PVSExprPairs -> PVSExprPairs):


--------------------------------------------------
'action' Gen_PVS_ExprPair(VALUE_EXPR_PAIR -> PVS_EXPR_PAIR)

  'rule' Gen_PVS_ExprPair(pair(LeftValueExpr, RightValueExpr) -> PVSExprPairout):
	 Gen_PVS_Expr(LeftValueExpr -> LeftPVSExpr)
	 Gen_PVS_Expr(RightValueExpr -> RightPVSExpr)
	 where(PVS_EXPR_PAIR'pair(LeftPVSExpr, RightPVSExpr) -> PVSExprPairout)


--------------------------------------------------
'action' Gen_PVS_Exprs(VALUE_EXPRS, PVS_EXPRS -> PVS_EXPRS)

  'rule' Gen_PVS_Exprs(list(ValueExpr, ValueExprsTail), PVSExprs -> PVSExprsout):
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 Insert_PVS_Expr(PVSExpr, PVSExprs -> PVSExprs1)
	 Gen_PVS_Exprs(ValueExprsTail, PVSExprs1 -> PVSExprsout)

  'rule' Gen_PVS_Exprs(nil, PVSExprs -> PVSExprs):




--------------------------------------------------
'action' Gen_PVS_Expr(VALUE_EXPR -> PVS_EXPR)

  'rule' Gen_PVS_Expr(literal_expr(Pos, ValueLit) -> PVSExprout):
	 Gen_PVS_literal_expr(Pos, ValueLit -> PVSExprout)

  'rule' Gen_PVS_Expr(named_val(_, name(Pos, IdorOp)) -> PVSExprout):
	 Gen_PVS_Id_Op(Pos, IdorOp -> IdOp)
	 where(PVS_EXPR'named_val(id_op(IdOp)) -> PVSExprout)

  'rule' Gen_PVS_Expr(pre_name(Pos, Name) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("pre name not supported")
	 Putnl()

  'rule' Gen_PVS_Expr(chaos(Pos) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("chaos not supported")
	 Putnl()

  'rule' Gen_PVS_Expr(skip(Pos) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("skip not supported")
	 Putnl()

  'rule' Gen_PVS_Expr(stop(Pos) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("stop not supported")
	 Putnl()

  'rule' Gen_PVS_Expr(swap(Pos) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("swap not supported")
	 Putnl()

  'rule' Gen_PVS_Expr(product(Pos, ValueExprs) -> PVSExprout):
	 Gen_PVS_Exprs(ValueExprs, nil -> PVSExprs)
	 where(PVS_EXPR'product(PVSExprs) -> PVSExprout)

  'rule' Gen_PVS_Expr(ranged_set(Pos, LeftValueExpr, RightValueExpr) -> PVSExprout):
	 Gen_PVS_Expr(LeftValueExpr -> LeftPVSExpr)
	 Gen_PVS_Expr(RightValueExpr -> RightPVSExpr)
	 where(PVS_EXPR'ranged_set(LeftPVSExpr, RightPVSExpr) -> PVSExprout)

  'rule' Gen_PVS_Expr(enum_set(Pos, ValueExprs) -> PVSExprout):
	 Gen_PVS_Exprs(ValueExprs, nil -> PVSExprs)
	 where(PVS_EXPR'enum_set(PVSExprs) -> PVSExprout)

  'rule' Gen_PVS_Expr(comp_set(Pos, ValueExpr,
		      set_limit(Pos2, Typings, Restriction)) -> PVSExprout):
	 -- try for version where expr matches binding
	 -- ie has form { x | x : T :- p(x) ]
	 where(Typings -> list(Typing, nil))
	 where(Typing -> single(_, Binding, _))
	 Matches_binding(ValueExpr, Binding)
	 Gen_PVSBindings_from_Typing(Typing -> PVSBindings)
	 Gen_PVS_Restriction(Restriction -> PVSRestriction)
	 where(comp_simp_set(bindings(PVSBindings), PVSRestriction) -> PVSExprout)

  'rule' Gen_PVS_Expr(comp_set(Pos, ValueExpr,
		      set_limit(Pos2, Typings, Restriction)) -> PVSExprout):
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 Get_Type_of_Value_Expr(ValueExpr -> TypeExpr)
	 Gen_PVS_Type_Expr(Pos, TypeExpr -> PVSTypeExpr)
	 Gen_PVSBindings_from_Typings(Typings -> PVSBindings)
	 Gen_PVS_Restriction(Restriction -> PVSRestriction)
	 where(PVS_EXPR'comp_set(PVSExpr, PVSTypeExpr,
			bindings(PVSBindings), PVSRestriction) -> PVSExprout)

  'rule' Gen_PVS_Expr(ranged_list(Pos, LeftValueExpr, RightValueExpr) -> PVSExprout):
	 Gen_PVS_Expr(LeftValueExpr -> LeftPVSExpr)
	 Gen_PVS_Expr(RightValueExpr -> RightPVSExpr)
	 where(PVS_EXPR'ranged_list(LeftPVSExpr, RightPVSExpr) -> PVSExprout)

  'rule' Gen_PVS_Expr(enum_list(Pos, ValueExprs) -> PVSExprout):
	 Gen_PVS_Exprs(ValueExprs, nil -> PVSExprs)
	 where(PVS_EXPR'enum_list(PVSExprs) -> PVSExprout)

  'rule' Gen_PVS_Expr(comp_list(Pos, ValueExpr, Limit) -> PVSExprout):
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 Gen_ListLimit(Limit -> PVSLimit)
	 where(PVS_EXPR'comp_list(PVSExpr, PVSLimit) -> PVSExprout)

  'rule' Gen_PVS_Expr(enum_map(Pos, ValueExprPairs) -> PVSExprout):
	 Gen_PVS_ExprPairs(ValueExprPairs, nil -> PVSExprPairs)
	 where(PVS_EXPR'enum_map(PVSExprPairs) -> PVSExprout)

  'rule' Gen_PVS_Expr(comp_map(Pos, pair(LeftValueExpr, RightValueExpr),
                      set_limit(Pos2, Typings, Restriction)) -> PVSExprout):
	 -- try for version where left matches binding
	 -- ie has form [ x +> e(x) | x : T :- p(x) ]
	 where(Typings -> list(Typing, nil))
	 where(Typing -> single(_, Binding, TypeExprDom))
	 Matches_binding(LeftValueExpr, Binding)
	 Gen_PVS_Expr(RightValueExpr -> PVSRightExpr)
	 Gen_PVS_Type_Expr(Pos, TypeExprDom -> PVSTypeExprDom)
	 Get_Type_of_Value_Expr(RightValueExpr -> TypeExprRng)
	 Gen_PVS_Type_Expr(Pos, TypeExprRng -> PVSTypeExprRng)
	 Gen_PVSBindings_from_Typing(Typing -> PVSBindings)
	 Gen_PVS_Restriction(Restriction -> PVSRestriction)
	 where(PVS_EXPR'comp_rng_map(PVSRightExpr, PVSTypeExprDom,
						   PVSTypeExprRng,
               bindings(PVSBindings), PVSRestriction) -> PVSExprout)

  'rule' Gen_PVS_Expr(comp_map(Pos, pair(LeftValueExpr, RightValueExpr),
                      set_limit(Pos2, Typings, Restriction)) -> PVSExprout):
	 Gen_PVS_Expr(LeftValueExpr -> PVSLeftExpr)
	 Gen_PVS_Expr(RightValueExpr -> PVSRightExpr)
	 where(PVS_EXPR_PAIR'pair(PVSLeftExpr, PVSRightExpr) -> PVSExprPair)
	 Get_Type_of_Value_Expr(LeftValueExpr -> TypeExprDom)
	 Get_Type_of_Value_Expr(RightValueExpr -> TypeExprRng)
	 Gen_PVS_Type_Expr(Pos, TypeExprDom -> PVSTypeExprDom)
	 Gen_PVS_Type_Expr(Pos, TypeExprRng -> PVSTypeExprRng)
	 Gen_PVSBindings_from_Typings(Typings -> PVSBindings)
	 Gen_PVS_Restriction(Restriction -> PVSRestriction)
	 where(PVS_EXPR'comp_map(PVSExprPair, PVSTypeExprDom, PVSTypeExprRng,
               bindings(PVSBindings), PVSRestriction) -> PVSExprout)

  'rule' Gen_PVS_Expr(function(Pos, LambdaParam, ValueExpr) -> PVSExprout):
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 Gen_LambdaBinding(LambdaParam -> LambdaBinding)
	 where(PVS_EXPR'function(LambdaBinding, PVSExpr) -> PVSExprout)

  'rule' Gen_PVS_Expr(application(Pos, ValueExpr, Args:list(_, list(_, _)))
				       -> PVSExprout):
	 -- deal with one application at a time by nesting
	 Rearrange_application(Pos, ValueExpr, Args -> ValueExpr1)
	 Gen_PVS_Expr(ValueExpr1 -> PVSExprout) 

  'rule' Gen_PVS_Expr(application(Pos, ValueExpr, list(Arg, nil)) -> PVSExprout):
	 Get_Type_of_Value_Expr(ValueExpr -> ValueExprType)
	 Gen_PVS_applic_Expr(ValueExprType, ValueExpr, Arg -> PVSExprout)


  'rule' Gen_PVS_Expr(quantified(Pos, Quantifier, Typings,
                                 Restriction)
                      -> PVSExprout):
	 Gen_PVS_Quantifier(Quantifier -> BindinOp)
	 Gen_PVSBindings_from_Typings(Typings -> PVSBindings)
	 Gen_PVS_Restriction(Restriction -> RestrictionExpr)
	 where(PVS_EXPR'quantified(BindinOp, bindings(PVSBindings),
                                   RestrictionExpr) -> PVSExprout)

  'rule' Gen_PVS_Expr(equivalence(Pos, ValueExprL, ValueExprR,
                                  PreCond) -> PVSExprout):
	 Gen_PVS_Expr(ValueExprL -> PVSExprL)
	 Gen_PVS_Expr(ValueExprR -> PVSExprR)
	 (|
	   where(PreCond -> pre_cond(Pos2, Pre))
 	   Gen_PVS_Expr(Pre -> PVSExprPre)
	 ||
	   where(PreCond -> nil)
	   where(PVS_EXPR'nil -> PVSExprPre)
	 |)
	 where(PVS_EXPR'equivalence(PVSExprL, PVSExprR, PVSExprPre)
	       -> PVSExprout)

  'rule' Gen_PVS_Expr(post(Pos, ValueExpr, Post, PreCond) -> PVSExprout):

	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 Get_Type_of_Value_Expr(ValueExpr -> TypeExpr)
	 Gen_PVS_Type_Expr(Pos, TypeExpr -> PVSTypeExpr)
	 Gen_PostCond(Post, TypeExpr -> PVSPost)
	 (|
	   where(PreCond -> pre_cond(Pos2, PreExpr))
	   Gen_PVS_Expr(PreExpr -> PVSPreCond)
	 ||
	   where(PVS_EXPR'nil -> PVSPreCond)
	 |)
	 where(PVS_EXPR'post(PVSExpr, PVSTypeExpr, PVSPost,
	                     PVSPreCond) -> PVSExprout)

  'rule' Gen_PVS_Expr(disamb(Pos, ValueExpr, TypeExpr) -> PVSExprout):
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 Gen_PVS_Type_Expr(Pos, TypeExpr -> PVSTypeExpr)
	 where(PVS_EXPR'disamb(PVSExpr, PVSTypeExpr) -> PVSExprout)

  'rule' Gen_PVS_Expr(bracket(Pos, ValueExpr) -> PVSExprout):
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 where(PVS_EXPR'bracket(PVSExpr) -> PVSExprout)

  'rule' Gen_PVS_Expr(ax_infix(Pos, LeftValueExpr, Conn, RightValueExpr, _) -> PVSExprout):
	 Gen_PVS_Expr(LeftValueExpr -> LeftPVSExpr)
	 Gen_PVS_Connective(Conn -> PVSConn)
	 Gen_PVS_Expr(RightValueExpr -> RightPVSExpr)
	 where(PVS_EXPR'ax_infix(LeftPVSExpr, PVSConn, RightPVSExpr) -> PVSExprout)
 
  'rule' Gen_PVS_Expr(stmt_infix(Pos, _, _, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("stmt_infix expressions not supported")
	 Putnl()

	 -- always ignored
  'rule' Gen_PVS_Expr(always(_, ValueExpr) -> PVSExprout):
	 Gen_PVS_Expr(ValueExpr -> PVSExprout)
 
  'rule' Gen_PVS_Expr(ax_prefix(Pos, Conn, ValueExpr) -> PVSExprout):
	 Gen_PVS_Connective(Conn -> PVSConn)
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 where(PVS_EXPR'ax_prefix(PVSConn, PVSExpr)  -> PVSExprout)
 
  'rule' Gen_PVS_Expr(comprehended(Pos, _, _, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("comprehended expressions not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_PVS_Expr(initialise(Pos, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("initialise expressions not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_PVS_Expr(assignment(Pos, _, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("assignment expressions not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_PVS_Expr(input(Pos, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("input expressions not supported")

	 -- not supported
  'rule' Gen_PVS_Expr(output(Pos, _, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("output expressions not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_PVS_Expr(local_expr(Pos, Decls, ValueExpr) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
 	 Puterror(Pos)
	 Putmsg("local expressions not supported")
	 Putnl()

  'rule' Gen_PVS_Expr(let_expr(Pos, LetDefs, ValueExpr) -> PVSExprout):
	 Process_Let_Defs(LetDefs -> LetBindings)
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 where(PVS_EXPR'let_expr(LetBindings, PVSExpr) -> PVSExprout)

  'rule' Gen_PVS_Expr(if_expr(Pos, ValueExpr, Then, _, Elsifs, Else)
					      -> PVSExprout):
	 [|
	   eq(Else, nil)
	   Puterror(Pos)
	   Putmsg("if expressions without else branch not supported")
	   Putnl()
	 |]
	 Gen_PVS_Expr(ValueExpr -> PVSExpr1)
	 Gen_PVS_Expr(Then -> PVSThen)
	 Gen_Elsifs(Elsifs, nil -> PVSElsifs)
	 Gen_Else(Else -> PVSElse)
	 where(PVS_EXPR'if_expr(PVSExpr1, PVSThen, PVSElsifs, PVSElse) -> PVSExprout)

  'rule' Gen_PVS_Expr(case_expr(Pos1, ValueExpr, Pos2, CaseBranches) -> PVSExprout):
	 -- ignore disambiguation
	 (|
	   where(ValueExpr -> disamb(_, ValueExpr1, _))
	 ||
	   where(ValueExpr -> ValueExpr1)
	 |)
	 Gen_PVS_Cases(ValueExpr1, CaseBranches -> PVSExprout)

	 -- not supported
  'rule' Gen_PVS_Expr(while_expr(Pos, _, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("while expressions not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_PVS_Expr(until_expr(Pos, _, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("until expressions not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_PVS_Expr(for_expr(Pos, _, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("for expressions not supported")
	 Putnl()

  'rule' Gen_PVS_Expr(env_class_scope(Pos, instantiation(
                                              name(Pos2,
                                                   id_op(Id)),
                                              nil), _,
                                       ValueExpr)
                      -> PVSExprout):
	 Out_Importings(list(Id,nil))
	 (|
	   eq(ValueExpr, no_val)
	   -- nothing to prove
	   Gen_PVS_Expr(literal_expr(Pos, bool_true) -> PVSExprout)
         ||
	   Gen_PVS_Expr(ValueExpr -> PVSExprout)
         |)

  'rule' Gen_PVS_Expr(env_class_scope(Pos, Class, CE, ValueExpr)
                      -> PVSExprout):
	 Current -> C
	 Current <- current_env(CE, C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil, Paths)
	 Open_TotalDeclareds
	 Trans_Class_expr(Class)
	 Gen_PVS_Expr(ValueExpr -> PVSExprout)
	 Close_TotalDeclareds
	 Current <- C
	 Extend_paths <- Paths

	 -- resolved to class scope expr
  'rule' Gen_PVS_Expr(implementation_relation(Pos, NewClass, OldClass) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("internal error: implementation relation encountered")
	 Putnl()
 
	 -- resolved to class scope expr
  'rule' Gen_PVS_Expr(implementation_expr(Pos, NewObjExpr, OldObjExpr) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("internal error: implementation expression encountered")
	 Putnl()

  'rule' Gen_PVS_Expr(val_occ(Pos, Valueid, OptQual) -> PVSExprout):
	 Valueid'Ident -> IdorOp
	 Valueid'Pos -> Pos1
	 Valueid'Qualifier -> Ids
	 Gen_PVS_Id_Op(Pos, IdorOp -> IdOp)
	 Gen_PVS_Qualification(OptQual, Ids -> NameQual)
	 where(PVS_EXPR'val_occ(val_id(Pos1, IdOp), NameQual) -> PVSExprout)

	 -- not supported
  'rule' Gen_PVS_Expr(var_occ(Pos, _, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("var_occ not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_PVS_Expr(pre_occ(Pos, _, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("pre_occ not supported")
	 Putnl()

  'rule' Gen_PVS_Expr(infix_occ(Pos, LeftValueExpr, Valueid, OptQual,
				RightValueExpr) -> PVSExprout):
	 Valueid'Ident -> IdorOp0
	 -- check for isin dom and isin elems
	 (|
	   where(IdorOp0 -> op_op(O))
	   Built_in(O, Valueid)
	   (| eq(O, isin) || eq(O, notisin) |)
	   Is_dom_or_elems(O, RightValueExpr -> RightValueExpr1, Vid)
	 ||
	   where(RightValueExpr -> RightValueExpr1)
	   where(Valueid -> Vid)
	 |)
	 Vid'Ident -> IdorOp
	 Vid'Pos -> Pos1
	 Gen_PVS_Expr(LeftValueExpr -> LeftPVSExpr)
	 Gen_PVS_Expr(RightValueExpr1 -> RightPVSExpr)
	 Vid'Qualifier -> Ids
	 Gen_PVS_Qualification(OptQual, Ids -> NameQual)
	 Gen_PVS_Id_Op(Pos, IdorOp -> IdOp)
	 (| -- operator symbol
	   where(IdOp -> op_symb(Op))
	   (|
	     where(IdorOp -> op_op(O1))
	     Built_in(O1, Vid)
	     Vid'Type -> T
	     Split_fun_type(T -> D, R)
	     Disambiguate_op(Op, D, R -> Op1)
	   ||
	     where(Op -> Op1)
	   |)
	   (| -- qualified
	     ne(NameQual, nil)
	     where(funct_expr(val_id(Pos1, op_symb(Op1)), NameQual, LeftPVSExpr,
                              RightPVSExpr) -> PVSExprout)
	   ||
	     -- infix_op
	     where(Op1 -> infix_op(_))
	     where(PVS_EXPR'infix_occ(LeftPVSExpr, val_id(Pos1, op_symb(Op1)),
	                      RightPVSExpr) -> PVSExprout)
	   || -- prefix_op
	     where(Op -> prefix_op(_))
	     Puterror(Pos)
	     Putmsg("internal - prefix_op in an infix_occ")
	     Putnl()
	     where(PVS_EXPR'nil -> PVSExprout)
	   || -- function_op
	     where(Op1 -> function_op(_))
	     where(funct_expr(val_id(Pos1, op_symb(Op1)), NameQual, LeftPVSExpr,
                              RightPVSExpr) -> PVSExprout)
	   |)
	 || -- not an operator symbol
	   Puterror(Pos)
	   Putmsg("internal - non-op in an infix_occ")
	   Putnl()
	   where(PVS_EXPR'nil -> PVSExprout)
	 |)

  'rule' Gen_PVS_Expr(prefix_occ(Pos, Valueid, OptQual, ValueExpr)
                      -> PVSExprout):
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 Valueid'Ident -> IdorOp
	 Valueid'Pos -> Pos1
	 Valueid'Qualifier -> Ids
	 Gen_PVS_Id_Op(Pos, IdorOp -> IdOp)
	 Gen_PVS_Qualification(OptQual, Ids -> NameQual)
	 (| -- operator symbol
	   where(IdOp -> op_symb(Op))
	   (|
	     where(IdorOp -> op_op(O))
	     Built_in(O, Valueid)
	     Valueid'Type -> T
	     Split_fun_type(T -> D, R)
	     Disambiguate_op(Op, D, R -> Op1)
	   ||
	     where(Op -> Op1)
	   |)
	   (| -- infix_op
	     where(Op1 -> infix_op(InfixOp))
	     ne(InfixOp, minus)
	     Puterror(Pos)
	     Putmsg("internal - infix_op in an prefix_occ")
	     Putnl()
	     where(PVS_EXPR'nil -> PVSExprout)
	   || -- prefix_op
	     where(Op1 -> prefix_op(_))
	     eq(OptQual, nil)
	     where(PVS_EXPR'prefix_occ(val_id(Pos1, op_symb(Op1)), PVSExpr)
                   -> PVSExprout)
	   || -- function_op
	     (| where(Op1 -> function_op(_)) || ne(OptQual, nil) |)
	     where(funct_expr(val_id(Pos1, op_symb(Op1)), NameQual,
                              PVSExpr, nil) -> PVSExprout)
	   ||
	     eq(Op1, identity)  -- int and real
	     where(PVSExpr -> PVSExprout)
	   |)
	 || -- not an operator symbol
	   where(funct_expr(val_id(Pos1, IdOp), NameQual,
	                             PVSExpr, nil) -> PVSExprout)
	 |)
	 

	 -- not supported
  'rule' Gen_PVS_Expr(ass_occ(Pos, _, _, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("ass_occ not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_PVS_Expr(input_occ(Pos, _, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("input_occ not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_PVS_Expr(output_occ(Pos, _, _, _) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("output_occ not supported")
	 Putnl()

	 -- not supported
  'rule' Gen_PVS_Expr(env_local(Pos, Decls, ClassEnv, ValueExpr) -> PVSExprout):
	 where(PVS_EXPR'not_supported -> PVSExprout)
	 Puterror(Pos)
	 Putmsg("env_local not supported")
	 Putnl()

  'rule' Gen_PVS_Expr(no_val -> PVSExprout):
	 where(PVS_EXPR'no_val -> PVSExprout)

  'rule' Gen_PVS_Expr(cc_expr(OptPos, String, _, ValueExpr) -> PVSExprout):
	 Gen_PVS_Expr(ValueExpr -> PVSExprout)

--------------------------------------------------
'action' Gen_PVS_Cases(VALUE_EXPR, CASE_BRANCHES -> PVS_EXPR)

  'rule' Gen_PVS_Cases(V, list(case(_, Patt, V1, _), BRS) -> PVSExpr)
	 Pattern_match(V, Patt -> Cond, LetDefs)
	 Process_Let_Defs(LetDefs -> LetBindings)
	 Gen_PVS_Expr(V1 -> PVSExpr1)
	 where(PVS_EXPR'let_expr(LetBindings, PVSExpr1) -> PVSExpr2)
	 (|
	   eq(BRS, nil)
	   -- last case: ignore Cond
	   where(PVSExpr2 -> PVSExpr)
         ||
	   Gen_PVS_Cases(V, BRS -> PVSExpr3)
	   Simplify(Cond -> Cond1)
	   Gen_PVS_Expr(Cond1 -> PVSCond)
	   where(PVS_EXPR'if_expr(PVSCond, PVSExpr2, nil, else(PVSExpr3)) -> PVSExpr)
	 |)


--------------------------------------------------
'action' Gen_PVS_Qualification(OPT_QUALIFICATION, Object_ids -> NAME_QUALIF)

  'rule' Gen_PVS_Qualification(qualification(ObjectExpr), _ -> NameQual):
	 Process_Object_Expr(ObjectExpr -> NameQual)

  'rule' Gen_PVS_Qualification(nil, nil -> nil):

  'rule' Gen_PVS_Qualification(nil, list(I, nil) -> NameQual):
	 GetTheoryId(I -> Id)
         (|
	   IsCurrentTheory(Id)
	   where(NAME_QUALIF'nil -> NameQual)
	 ||
	   IsCurrentObject(I)
	   where(NAME_QUALIF'nil -> NameQual)
	 ||
           Dummy_id1 -> Dummy_id1
           ne(Id, Dummy_id1)
           Dummy_id2 -> Dummy_id2
           ne(Id, Dummy_id2)
	   where(qualif(nil, id(Id), nil) -> NameQual)
	 ||
	   where(NAME_QUALIF'nil -> NameQual)
	 |)

  'rule' Gen_PVS_Qualification(nil, list(_, Is) -> NameQual):
	 Gen_PVS_Qualification(nil, Is -> NameQual)

--------------------------------------------------
-- OP must be isin or notisin
'condition' Is_dom_or_elems(OP, VALUE_EXPR -> VALUE_EXPR, Value_id)

  'rule' Is_dom_or_elems(O, prefix_occ(_, I, nil, V) -> V, I1):
	 I'Ident -> op_op(Op)
	 Built_in(Op, I)
	 (|
	   eq(Op, dom)
	   (|
	     eq(O, isin)
	     Id_of_isin_map -> I1
	   ||
             Id_of_notisin_map -> I1
	   |)
	 ||
	   eq(Op, elems)
	   (|
	     eq(O, isin)
	     Id_of_isin_list -> I1
	   ||
             Id_of_notisin_list -> I1
	   |)
	 |)

  'rule' Is_dom_or_elems(O, bracket(_, V) -> V1, I1):
	 Is_dom_or_elems(O, V -> V1, I1)

  'rule' Is_dom_or_elems(O, disamb(P, V, T) -> disamb(P, V1, T), I1):
	 Is_dom_or_elems(O, V -> V1, I1) 



--------------------------------------------------
'action' Process_Object_Expr(OBJECT_EXPR -> NAME_QUALIF)

  'rule' Process_Object_Expr(obj_name(Name) -> NameQual):
	 where(NAME_QUALIF'nil -> NameQual)

	 --                                       Params
  'rule' Process_Object_Expr(obj_appl(ObjectExpr, ValueExprs)
                             ->  NameQual):
	 where(NAME_QUALIF'nil -> NameQual)

	 --                            Params
  'rule' Process_Object_Expr(obj_array(Typings, ObjectExpr) -> NameQual):
	 where(NAME_QUALIF'nil -> NameQual)

  'rule' Process_Object_Expr(obj_fit(ObjectExpr, Renames) -> NameQual):
	 Process_Object_Expr(ObjectExpr -> NameQual)

  'rule' Process_Object_Expr(obj_occ(Pos, Objectid) -> NameQual):
	 GetTheoryId(Objectid -> Ident)
	 where(qualif(nil, id(Ident), nil) -> NameQual)

	 --                                Qualif
  'rule' Process_Object_Expr(qual_occ(Pos, ObjectExpr, Objectid) -> NameQual):
	 Process_Object_Expr(obj_occ(Pos, Objectid) -> NameQual)


--------------------------------------------------
'action' Gen_PVS_Name(NAME -> PVS_NAME)

  'rule' Gen_PVS_Name(name(Pos, IdorOp) -> PVSName):
	 Gen_PVS_Id_Op(Pos, IdorOp -> IdOp)
	 where(PVS_NAME'id_op(IdOp) -> PVSName)

	 --                          Qualif
  'rule' Gen_PVS_Name(qual_name(Pos, ObjectExpr, IdorOp) -> PVSName):
	 Gen_PVS_Id_Op(Pos, IdorOp -> IdOp)
	 Process_Object_Expr(ObjectExpr -> NameQualif)
	 where(PVS_NAME'qual_name(IdOp, NameQualif)
               -> PVSName)


--------------------------------------------------
'action' Gen_PVS_applic_Expr(TYPE_EXPR, VALUE_EXPR, ACTUAL_FUNCTION_PARAMETER
						    -> PVS_EXPR)

  'rule' Gen_PVS_applic_Expr(TypeExpr, ValueExpr, Arg -> PVSExprout):
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 Gen_PVS_Arguments(Arg -> PVSArg)
	 (|
	   Make_function_type(TypeExpr -> TypeExpr1)
	   ne(TypeExpr1, none)
	   where(PVS_EXPR'funct_applic(PVSExpr, PVSArg)
					      -> PVSExprout)
         ||
	   Make_map_type(TypeExpr -> TypeExpr1)
	   ne(TypeExpr1, none)
	   where(PVS_EXPR'map_applic(PVSExpr, PVSArg)
					      -> PVSExprout)
         || -- must be a list
	   where(PVS_EXPR'list_applic(PVSExpr, PVSArg)
					      -> PVSExprout)
	 |)


--------------------------------------------------
'action' Gen_PVS_literal_expr(POS, VALUE_LITERAL -> PVS_EXPR)

  'rule' Gen_PVS_literal_expr(Pos, unit -> PVSExpr):
	 where(PVS_EXPR'not_supported -> PVSExpr)
	 Puterror(Pos)
	 Putmsg("unit not supported")
	 Putnl()
         
  'rule' Gen_PVS_literal_expr(Pos, bool_true -> PVSExpr):
	 where(PVS_EXPR'literal_expr(bool_true) -> PVSExpr)
        
  'rule' Gen_PVS_literal_expr(Pos, bool_false -> PVSExpr):
	 where(PVS_EXPR'literal_expr(bool_false) -> PVSExpr)
	
  'rule' Gen_PVS_literal_expr(Pos, int(Val) -> PVSExpr):
	 where(PVS_EXPR'literal_expr(int(Val)) -> PVSExpr)
	
  'rule' Gen_PVS_literal_expr(Pos, real(Val) -> PVSExpr):
	 where(PVS_EXPR'literal_expr(real(Val)) -> PVSExpr)
	 
  'rule' Gen_PVS_literal_expr(Pos, text(Val) -> PVSExpr):
	 where(PVS_EXPR'literal_expr(text(Val)) -> PVSExpr)
--	 where(PVS_EXPR'not_supported -> PVSExpr)
--	 Puterror(Pos)
--	 Putmsg("text not supported")
--	 Putnl()
	 
  'rule' Gen_PVS_literal_expr(Pos, char(Val) -> PVSExpr):
	 where(PVS_EXPR'literal_expr(char(Val)) -> PVSExpr)
--	 where(PVS_EXPR'not_supported -> PVSExpr)
--	 Puterror(Pos)
--	 Putmsg("char not supported")
--	 Putnl()

--------------------------------------------------
'action' Gen_PVS_Arguments(ACTUAL_FUNCTION_PARAMETER -> ARGUMENTS)

  'rule' Gen_PVS_Arguments(fun_arg(Pos, ValueExprs) -> Argumentsout):
	 Gen_PVS_Exprs(ValueExprs, nil -> PVSExprs)
	 where(argument(Pos, PVSExprs) -> Argumentsout)



--------------------------------------------------
'action' Gen_Elsifs(ELSIF_BRANCHES, PVS_ELSIF_BRANCHES -> PVS_ELSIF_BRANCHES)

  'rule' Gen_Elsifs(list(Elsif, ElsifTail), PVSElsifs -> PVSElsifsout):
	 Gen_Elsif(Elsif -> PVSElsif)
	 Insert_Elsif(PVSElsif, PVSElsifs -> PVSElsifs1)
	 Gen_Elsifs(ElsifTail, PVSElsifs1 -> PVSElsifsout)

  'rule' Gen_Elsifs(nil, PVSElsifs -> PVSElsifs):


	   

--------------------------------------------------
'action' Gen_Elsif(ELSIF_BRANCH -> PVS_ELSIF_BRANCH)

  'rule' Gen_Elsif(elsif(Pos, If, Then, _) -> PVSElsif):
	 Gen_PVS_Expr(If -> PVSIf)
	 Gen_PVS_Expr(Then -> PVSThen)
	 where(PVS_ELSIF_BRANCH'elsif(PVSIf, PVSThen) -> PVSElsif)
	   

--------------------------------------------------
'action' Gen_Else(ELSE_BRANCH -> PVS_ELSE_BRANCH)

  'rule' Gen_Else(else(Pos, ValueExpr) -> PVSElse):
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 where(PVS_ELSE_BRANCH'else(PVSExpr) -> PVSElse)

  'rule' Gen_Else(nil -> PVSElse):
	 where(PVS_ELSE_BRANCH'nil -> PVSElse)


------------------------------------------------------
-- Generate LetBindings
--------------------------------------------------

--------------------------------------------------
'action' Process_Let_Defs(LET_DEFS -> LETBINDINGS)

  'rule' Process_Let_Defs(list(LetDef, LetDefsTail) -> LetBindingsout):
	 Process_Let_Def(LetDef -> LetBindings1)
	 Process_Let_Defs(LetDefsTail -> LetBindings2)
	 Concat_LetBindings(LetBindings1, LetBindings2 -> LetBindingsout)

  'rule' Process_Let_Defs(nil -> nil):

--------------------------------------------------

'action' Concat_LetBindings(LETBINDINGS, LETBINDINGS -> LETBINDINGS)

  'rule' Concat_LetBindings(list(B, BS), BS1 -> list(B, BS2)):
	 Concat_LetBindings(BS, BS1 -> BS2)

  'rule' Concat_LetBindings(nil, BS -> BS):

--------------------------------------------------
'action' Process_Let_Def(LET_DEF -> LETBINDINGS)

  'rule' Process_Let_Def(explicit(_, binding(_, single(P, Id)), ValueExpr)
				        -> list(LetBindingout, nil)):
	 -- ignore disambiguation introduced by resolving
--	 (|
--	   where(ValueExpr -> disamb(_, ValueExpr1, _))
--	 ||
--	   where(ValueExpr -> ValueExpr1)
--	 |)
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 Gen_PVS_Id_Op(P, Id -> IdOp)
	 where(let_bind(let_idop(IdOp, nil, nil), PVSExpr) -> LetBindingout)

  'rule' Process_Let_Def(explicit(_, binding(_, product(_, BS)),  ValueExpr)
				        -> LBS):
	 -- ignore disambiguation introduced by resolving
	 (|
	   where(ValueExpr -> disamb(_, ValueExpr1, _))
	 ||
	   where(ValueExpr -> ValueExpr1)
	 |)
	 Gen_PVS_Expr(ValueExpr1 -> PVSExpr)
	 Process_Let_Bindings(BS, nil -> LetBinds, LBS1)
	 where(LETBINDINGS'list(let_binds(LetBinds, PVSExpr), LBS1) -> LBS)

  'rule' Process_Let_Def(explicit(Pos, pattern(Pos2, Pattern),
                         ValueExpr) -> LetBindingsout):
	 -- ignore disambiguation introduced by resolving
	 (|
	   where(ValueExpr -> disamb(_, ValueExpr1, _))
	 ||
	   where(ValueExpr -> ValueExpr1)
	 |)
	 Pattern_match(ValueExpr1, Pattern -> ValueExpr2, LetDefs)
	 -- condition ValueExpr2 ignored as generates a CC in RSL
	 Process_Let_Defs(LetDefs -> LetBindingsout)

  'rule' Process_Let_Def(implicit(Pos, Typing, Restriction) -> LetBindingsout):
	 Typing_to_expr(Pos, Typing -> Expr)
	 Id_of_hd_set -> Ihd
	 where(VALUE_EXPR'comp_set(Pos, Expr, 
			     set_limit(Pos, list(Typing, nil), Restriction))
							 -> Set)
	 where(VALUE_EXPR'prefix_occ(Pos, Ihd, nil, Set) -> Expr2)
	 where(Typing -> single(_, Binding, _))
	 Process_Let_Def(explicit(Pos, binding(Pos, Binding), Expr2)
						     -> LetBindingsout)

'action' Process_Let_Bindings(BINDINGS, LETBINDINGS -> LETBINDS, LETBINDINGS)

  'rule' Process_Let_Bindings(list(single(P, Id), BS), LBGS ->
					     list(LB, LBS), LBGS1):
	 Gen_PVS_Id_Op(P, Id -> IdOp)
	 where(let_idop(IdOp, nil, nil) -> LB)
	 Process_Let_Bindings(BS, LBGS -> LBS, LBGS1)

  'rule' Process_Let_Bindings(list(product(_, BS), BS1), LBGS ->
					     list(LB, LBS), LBGSOut):
	 Gen_Prod_Ident("" -> IdProd)
	 where(let_idop(id(IdProd), nil, nil) -> LB)
	 Process_Let_Bindings(BS, LBGS -> LBS1, LBGS1)
	 Process_Let_Bindings(BS1, LBGS1 -> LBS, LBGS2)
	 where(LETBINDINGS'list(let_binds(LBS1,
				named_val(id_op(id(IdProd)))), LBGS2) -> LBGSOut)

  'rule' Process_Let_Bindings(nil, LBGS -> nil, LBGS):
         
------------------------------------------------------
-- Generate PVS Bindings from RSL Typings and Bindings
------------------------------------------------------

--------------------------------------------------
'action' Gen_LambdaBindings(TYPINGS -> LAMBDABINDINGS)

  'rule' Gen_LambdaBindings(list(Typing, TypingsTail) ->
					 list(LambdaBinding, LambdaBindings)):
	 Gen_PVSBindings_from_Typing(Typing -> PVSBindings)
	 where(LAMBDABINDING'bindings(PVSBindings) -> LambdaBinding)
	 Gen_LambdaBindings(TypingsTail -> LambdaBindings)

  'rule' Gen_LambdaBindings(nil -> nil):

--------------------------------------------------
'action' Gen_LambdaBinding(LAMBDA_PARAMETER -> LAMBDABINDINGS)

  'rule' Gen_LambdaBinding(l_typing(Pos, nil) -> nil):
	 Puterror(Pos)
	 Putmsg("Unit type not supported")
	 Putnl()

  'rule' Gen_LambdaBinding(l_typing(Pos, Typings) -> LambdaBindingsout):
	 Gen_LambdaBindings(Typings -> LambdaBindingsout)

  'rule' Gen_LambdaBinding(s_typing(Pos, Typing) ->
					 list(LambdaBinding, nil)):
	 Gen_PVSBindings_from_Typing(Typing -> PVSBindings)
	 where(LAMBDABINDING'bindings(PVSBindings) -> LambdaBinding)

	   

--------------------------------------------------
'action' Gen_PVS_Id_Op(POS, ID_OR_OP -> ID_OP)

  'rule' Gen_PVS_Id_Op(Pos, id_op(Ident) -> PVS_Id_or_op):
	 where(ID_OP'id(Ident) -> PVS_Id_or_op)

  'rule' Gen_PVS_Id_Op(Pos, op_op(Op) -> PVS_Id_or_op):
	 Gen_PVS_Op(Pos, Op -> PVSOp)
	 where(op_symb(PVSOp) -> PVS_Id_or_op)
	   

--------------------------------------------------
'action' Gen_PVS_Op(POS, OP -> PVS_OP)

  'rule' Gen_PVS_Op(Pos, eq -> PVSOp):
	 where(infix_op(eq) -> PVSOp)
  'rule' Gen_PVS_Op(Pos, neq -> PVSOp):
	 where(infix_op(neq) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, gt -> PVSOp):
	 where(infix_op(gt) -> PVSOp)
  'rule' Gen_PVS_Op(Pos, lt -> PVSOp):
	 where(infix_op(lt) -> PVSOp)
  'rule' Gen_PVS_Op(Pos, ge -> PVSOp):
	 where(infix_op(ge) -> PVSOp)
  'rule' Gen_PVS_Op(Pos, le -> PVSOp):
	 where(infix_op(le) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, supset -> PVSOp):
	 where(function_op(supset) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, subset -> PVSOp):
	 where(function_op(subset) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, supseteq -> PVSOp):
	 where(function_op(supseteq) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, subseteq -> PVSOp):
	 where(function_op(subseteq) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, isin -> PVSOp):
	 where(function_op(isin) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, notisin -> PVSOp):
	 where(function_op(notisin) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, rem -> PVSOp):
	 where(function_op(rem) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, caret -> PVSOp):
	 where(PVS_OP'function_op(append) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, union -> PVSOp):
	 where(function_op(union) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, override -> PVSOp):
	 where(function_op(override) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, mult -> PVSOp):
	 where(infix_op(mult) -> PVSOp)
  'rule' Gen_PVS_Op(Pos, div -> PVSOp):
	 where(infix_op(div) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, hash -> PVSOp):
	 where(function_op(hash) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, inter -> PVSOp):
	 where(function_op(inter) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, exp -> PVSOp):
	 where(function_op(exp) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, abs -> PVSOp):
	 where(function_op(abs) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, int -> PVSOp):
	 where(identity -> PVSOp)

  'rule' Gen_PVS_Op(Pos, real -> PVSOp):
	 where(identity -> PVSOp)

  'rule' Gen_PVS_Op(Pos, card -> PVSOp):
	 where(function_op(card) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, len -> PVSOp):
	 where(function_op(len) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, inds -> PVSOp):
	 where(function_op(inds) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, elems -> PVSOp):
	 where(function_op(elems) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, hd -> PVSOp):
	 where(function_op(hd) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, tl -> PVSOp):
	 where(function_op(tl) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, dom -> PVSOp):
	 where(function_op(dom) -> PVSOp)
  'rule' Gen_PVS_Op(Pos, rng -> PVSOp):
	 where(function_op(rng) -> PVSOp)

-- not supported
  'rule' Gen_PVS_Op(Pos, wait -> PVSOp):	-- only used in TRSL
	 where(PVS_OP'not_supported -> PVSOp)
	 Puterror(Pos)
	 Putmsg("wait, not supported")
	 Putnl()

  'rule' Gen_PVS_Op(Pos, plus -> PVSOp):
	 where(infix_op(plus) -> PVSOp)

  'rule' Gen_PVS_Op(Pos, minus -> PVSOp):
	 where(infix_op(minus) -> PVSOp)

'action' Disambiguate_op(PVS_OP, TYPE_EXPR, TYPE_EXPR -> PVS_OP)

  'rule' Disambiguate_op(function_op(rem), _, R -> function_op(difference)):
	 Type_is_set(R -> _)
	   
  'rule' Disambiguate_op(function_op(rem),_,R -> function_op(restriction_by)):
	 Type_is_map(R -> _, _)

  'rule' Disambiguate_op(infix_op(div), _, R -> function_op(int_div)):
	 Match(R, up, int)

  'rule' Disambiguate_op(infix_op(div), _, R -> function_op(restriction_to)):
	 Type_is_map(R -> _, _)

  'rule' Disambiguate_op(function_op(hd), D, _ -> function_op(hd_set)):
	 Type_is_set(D -> _)

  'rule' Disambiguate_op(function_op(hd), D, _ -> function_op(hd_map)):
	 Type_is_map(D -> _, _)

  'rule' Disambiguate_op(function_op(isin), D, _ -> function_op(isin_map)):
	 where(D -> product(list(_, list(X, nil))))
	 Type_is_map(X -> _, _)

  'rule' Disambiguate_op(function_op(notisin),D,_ -> function_op(notisin_map)):
	 where(D -> product(list(_, list(X, nil))))
	 Type_is_map(X -> _, _)

  'rule' Disambiguate_op(Op, _, _ -> Op):

--------------------------------------------------
'action' Gen_PVS_Connective(CONNECTIVE -> PVS_CONNECTIVE)

  'rule' Gen_PVS_Connective(implies -> PVSConn):
	 where(PVS_CONNECTIVE'implies -> PVSConn)
  'rule' Gen_PVS_Connective(or -> PVSConn):
	 where(PVS_CONNECTIVE'or -> PVSConn)
  'rule' Gen_PVS_Connective(and -> PVSConn):
	 where(PVS_CONNECTIVE'and -> PVSConn)
  'rule' Gen_PVS_Connective(not -> PVSConn):
	 where(PVS_CONNECTIVE'not -> PVSConn)
	   

--------------------------------------------------
'action' Gen_PVS_Quantifier(QUANTIFIER -> BINDING_OP)

  'rule' Gen_PVS_Quantifier(all -> PVSQuantifier):
	 where(BINDING_OP'forall -> PVSQuantifier)

  'rule' Gen_PVS_Quantifier(exists -> PVSQuantifier):
	 where(BINDING_OP'exists -> PVSQuantifier)

  'rule' Gen_PVS_Quantifier(exists1 -> PVSQuantifier):
	 where(BINDING_OP'exists1 -> PVSQuantifier)


--------------------------------------------------
--  Auxiliary Actions
--------------------------------------------------


--------------------------------------------------
'action' Get_Type_of_Value_Expr(VALUE_EXPR -> TYPE_EXPR)

  'rule' Get_Type_of_Value_Expr(ValueExpr -> TypeExpr):
         (|
           Make_results(ValueExpr -> list(result(TypeExpr,_,_,_,_),nil))
         ||
           Putmsg("Internal error: expression with type that is not unique")
           Putnl()
	   where(TYPE_EXPR'none -> TypeExpr)
         |)



--------------------------------------------------
'action' Gen_ListLimit(LIST_LIMITATION -> LIST_LIMIT)

  'rule' Gen_ListLimit(list_limit(Pos, Binding, ValueExpr, Restriction)
							   -> ListLimit):
	 Get_Type_of_Value_Expr(ValueExpr -> TypeExpr)
	 Make_list_type(TypeExpr -> TypeExpr1)
	 (|
	   where(TypeExpr1 -> fin_list(ListTypeExpr))
	 ||
	   where(TypeExpr1 -> infin_list(ListTypeExpr))
	   Puterror(Pos)
	   Putmsg("infinite lists not supported")
	   Putnl()
	 |)
	 Gen_PVS_Expr(ValueExpr -> PVSExpr)
	 Gen_PVS_Restriction(Restriction -> PVSRestriction)
	 Gen_PVSBindings_from_Typing(single(Pos, Binding, ListTypeExpr) 
							  -> PVSBindings)
	 where(limit(PVSBindings, PVSExpr, PVSRestriction) -> ListLimit)

 


--------------------------------------------------
--  Prints for debugging
--------------------------------------------------

/*
print("*********************************")
print("*********************************")
print("        TheoryElements:")
print(TheoryElements)
print("********** end of TheoryElements")
print("*********************************")
print("                                 ")
print("*********************************")
print("*********************************")
print("        TheoryElements1:")
print(TheoryElements1)
print("********** end of TheoryElements1")
print("*********************************")
print("                                 ")
print("*********************************")
print("*********************************")
print("        DeclaredsTail:")
print(DeclaredsTail)
print("********** end of DeclaredsTail")
print("*********************************")
print("                                 ")
*/


/*
print("*********************************")
print("*********************************")
print("        TheoryElementsout:")
print(TheoryElementsout)
print("********** end of TheoryElementsout")
*/

/*
print("                                 ")
print("                                 ")
print("*********************************")
print("        TheoryElements3:")
print(TheoryElements3)
print("********** end of TheoryElements3")
print("                                 ")
*/
