-- RSL Type Checker
-- Copyright (C) 1998 - 2005 UNU/IIST

-- raise@iist.unu.edu

-- This module contains the auxiliary functions
-- for the SAL code generation procedure

 
'module' sal_gen_code_aux

'use' ast 
      print 
      ext   -- C_id_to_string
	    -- WriteFile
      env objects values types pp cc
      sal_aux
      sal_ast
      sal_gen_code --SAL_Out_Value_Expr
      sal_gen_code_types
      sal_global_vars
      sal_print

'export' 
	 SAL_Out_Idents
	 SAL_Out_Ident
	 SAL_Out_Variable_Id

	 SAL_Out_IdOps
	 SAL_Out_IdOp

	 SAL_Out_Op
	 SAL_Out_cc_Op

	 SAL_Out_Qualif_for_Sets
	 SAL_Out_Qualif_for_Maps
	 
--------------------------------------------------
'action' SAL_Out_Idents(IDENTS)

  'rule' SAL_Out_Idents(list(Ident, IdentsTail)):
	 SAL_Out_Ident(Ident)
	 SAL_Out_Idents(IdentsTail)

  'rule' SAL_Out_Idents(nil):


--------------------------------------------------
'action' SAL_Out_Ident(IDENT)

  'rule' SAL_Out_Ident(Ident):
	 C_id_to_string(Ident -> IdentString)
	 WriteFile(IdentString)
--------------------------------------------------
'action' SAL_Out_Variable_Id(IDENT)

  'rule' SAL_Out_Variable_Id(Ident)
	 id_to_string(Ident -> Str)
	 WriteFile(Str)
--------------------------------------------------
'action' SAL_Out_IdOps(SAL_ID_OP)

  'rule' SAL_Out_IdOps(IdOp):
	 SAL_Out_IdOp(IdOp)

--------------------------------------------------
'action' SAL_Out_IdOp(SAL_ID_OP)

  'rule' SAL_Out_IdOp(id(Ident)):
	 SAL_Out_Ident(Ident)

  'rule' SAL_Out_IdOp(sal_op_symb(Op)):
	 SAL_Out_Op(Op)


  'rule' SAL_Out_IdOp(sal_list_op(Op, Tid))
	 SAL_Out_Qualif_from_Tid(Tid)
	 SAL_Out_Op(Op)

--CWG 24/6/06
  'rule' SAL_Out_IdOp(sal_int_op(Op, Tid)):
-- error here.  We presumably should have
--	 SAL_Out_Qualif_from_Tid(Tid)
-- but in fact we need
         WriteFile("Int__OPS!")
	 SAL_Out_Op(Op)

  'rule' SAL_Out_IdOp(sal_set_op(Op, TE, Tid))
	 SAL_Out_Qualif_for_Sets(Tid,TE)
	/* Tid'OperationsCid -> cid(Cid)
	 SAL_Current_Cid -> CCid
	 [|
	     ne(Cid, CCid)
	     Cid'Ident -> Ident
	     SAL_Out_Ident(Ident)
	     WriteFile("{")
	     SAL_Out_Type_Expr(TE)
	     WriteFile("}!")
	 |]*/
	 SAL_Out_Op(Op)

  'rule' SAL_Out_IdOp(sal_map_op(Op, TD, TR, Tid))
	 SAL_Out_Qualif_for_Maps(Tid,TD,TR)
	 SAL_Out_Op(Op)

  'rule' SAL_Out_IdOp(sal_cc_op(Op, Tid))
	 SAL_Out_OPS_Qualif_from_Tid(Tid)
	 SAL_Out_cc_Op(Op)

  'rule' SAL_Out_IdOp(nil)
	 WriteFile("nil")


---------------------------------------------------
'action' SAL_Out_Op(SAL_OP)

  -- Infix Operators
  'rule' SAL_Out_Op(sal_infix_op(eq)):
	 WriteFile(" = ")
  'rule' SAL_Out_Op(sal_infix_op(neq)):
	 WriteFile(" /= ")
  'rule' SAL_Out_Op(sal_infix_op(gt)):
	 WriteFile(" > ")
  'rule' SAL_Out_Op(sal_infix_op(lt)):
	 WriteFile(" < ")
  'rule' SAL_Out_Op(sal_infix_op(ge)):
	 WriteFile(" >= ")
  'rule' SAL_Out_Op(sal_infix_op(le)):
	 WriteFile(" <= ")
  'rule' SAL_Out_Op(sal_infix_op(mult)):
	 WriteFile(" * ")
  'rule' SAL_Out_Op(sal_infix_op(div)):
	 WriteFile(" / ")
  'rule' SAL_Out_Op(sal_infix_op(plus)):
	 WriteFile(" + ")
  'rule' SAL_Out_Op(sal_infix_op(minus)):
	 WriteFile(" - ")
  'rule' SAL_Out_Op(sal_infix_op(int_div)):
	 WriteFile(" DIV ")
-- LTL operators:
  'rule' SAL_Out_Op(sal_prefix_op(g)):
	 WriteFile("G")
  'rule' SAL_Out_Op(sal_prefix_op(x)):
	 WriteFile("X")
  'rule' SAL_Out_Op(sal_prefix_op(f)):
	 WriteFile("F")

  -- Function operators
  'rule' SAL_Out_Op(sal_function_op(supset)):
	 WriteFile("strict_supset?")
  'rule' SAL_Out_Op(sal_function_op(subset)):
	 WriteFile("strict_subset?")
  'rule' SAL_Out_Op(sal_function_op(supseteq)):
	 WriteFile("supset?")
  'rule' SAL_Out_Op(sal_function_op(subseteq)):
	 WriteFile("subset?")
  'rule' SAL_Out_Op(sal_function_op(isin)):
	 WriteFile("isin")
  'rule' SAL_Out_Op(sal_function_op(notisin)):
 	 WriteFile("not_isin")
  'rule' SAL_Out_Op(sal_function_op(rem)):
 	 WriteFile("modulo")
  'rule' SAL_Out_Op(sal_function_op(difference)):
 	 WriteFile("difference")
  'rule' SAL_Out_Op(sal_function_op(restriction_by)):
 	 WriteFile("restriction_by")
  'rule' SAL_Out_Op(sal_function_op(restriction_to)):
	 WriteFile("restriction_to")
  'rule' SAL_Out_Op(sal_function_op(union)):
	 WriteFile("union")
  'rule' SAL_Out_Op(sal_function_op(override)):
	 WriteFile("override")
  'rule' SAL_Out_Op(sal_function_op(inter)):
	 WriteFile("intersection")
  'rule' SAL_Out_Op(sal_function_op(exp)):
	 WriteFile("expt")
  'rule' SAL_Out_Op(sal_function_op(abs)):
	 WriteFile("abs")
  'rule' SAL_Out_Op(sal_function_op(inds)):
	 WriteFile("inds")
  'rule' SAL_Out_Op(sal_function_op(dom)):
	 WriteFile("dom")
  'rule' SAL_Out_Op(sal_function_op(rng)):
	 WriteFile("rng")
  'rule' SAL_Out_Op(sal_function_op(add_set)):
	 WriteFile("add")
  'rule' SAL_Out_Op(sal_function_op(add_map)):
	 WriteFile("add")

  'rule' SAL_Out_Op(sal_identity):

  'rule' SAL_Out_Op(not_supported):
	 WriteFile("Operator not supported")

  'rule' SAL_Out_Op(T)
	 Putmsg("Debugging predicate activated in SAL_Out_Op\n")
	 print(T)
-----------------------------------------------------------
'action' SAL_Out_Qualif_for_Sets(SAL_type_id, SAL_TYPE_EXPR)
	
  'rule' SAL_Out_Qualif_for_Sets(Tid, TExpr):
	 SAL_Current_Cid -> CCid
	 Tid'OperationsCid -> OptCid
	 (|
	     where(OptCid -> cid(Cid))
	     [|
		ne(Cid, CCid)
		Cid'Ident -> Id
		SAL_Out_Ident(Id)
		WriteFile("!")
	     |]
	 ||
	     Putmsg("INTERNAL ERROR! Invalid type id qualif for set.")
	     SAL_Print_Tid(Tid)
	     Putnl()
	 |)

-----------------------------------------------------------

'action' SAL_Out_Qualif_for_Maps(SAL_type_id, SAL_TYPE_EXPR, SAL_TYPE_EXPR)
	
  'rule' SAL_Out_Qualif_for_Maps(Tid, Dom, Rng):
	 SAL_Current_Cid -> CCid
	 Tid'OperationsCid -> OptCid
	 (|
	     where(OptCid -> cid(Cid))
	     [|
		ne(Cid, CCid)
		Cid'Ident -> Id
		SAL_Out_Ident(Id)
--		WriteFile("{")
--		SAL_Out_Type_Expr(Dom)
--		WriteFile(", ")
--		SAL_Out_Type_Expr(Rng)
--		WriteFile("}!")
		WriteFile("!")
	     |]
	 ||
	     Putmsg("INTERNAL ERROR! Invalid type id qualif for map.")
	     SAL_Print_Tid(Tid)
	     Putnl()
	 |)

------------------------------------------------------------------------
'action' SAL_Out_OPS_Qualif_from_Tid(SAL_type_id)

  'rule' SAL_Out_OPS_Qualif_from_Tid(Tid)
	 SAL_Current_Cid -> CCid
	 Tid'OperationsCid -> OptCid
	 (|
	     where(OptCid -> cid(Cid))
	     [|
		ne(Cid, CCid)
		Cid'Ident -> Id
		SAL_Out_Ident(Id)
--		WriteFile("{")
--		SAL_Out_Type_Expr(Dom)
--		WriteFile(", ")
--		SAL_Out_Type_Expr(Rng)
--		WriteFile("}!")
		WriteFile("!")
	     |]
	 ||
	     Putmsg("INTERNAL ERROR! Invalid type id qualif for operation...")
	     SAL_Print_Tid(Tid)
	     Putnl()
	 |)

------------------------------------------------------------------------
'action' SAL_Out_cc_Op(SAL_OP)

  'rule' SAL_Out_cc_Op(sal_infix_op(eq)):
	 WriteFile("eq")
  'rule' SAL_Out_cc_Op(sal_infix_op(neq)):
	 WriteFile("neq")
  'rule' SAL_Out_cc_Op(sal_infix_op(gt)):
	 WriteFile("gt")
  'rule' SAL_Out_cc_Op(sal_infix_op(lt)):
	 WriteFile("lt")
  'rule' SAL_Out_cc_Op(sal_infix_op(ge)):
	 WriteFile("ge")
  'rule' SAL_Out_cc_Op(sal_infix_op(le)):
	 WriteFile("le")
  'rule' SAL_Out_cc_Op(sal_infix_op(mult)):
	 WriteFile("cc_mult")
  'rule' SAL_Out_cc_Op(sal_infix_op(div)):
	 WriteFile("cc_div")
  'rule' SAL_Out_cc_Op(sal_infix_op(plus)):
	 WriteFile("cc_add")
  'rule' SAL_Out_cc_Op(sal_infix_op(minus)):
	 WriteFile("cc_sub")
  'rule' SAL_Out_cc_Op(sal_infix_op(int_div)):
	 WriteFile("cc_div")

  -- special infix operations turned to prefixed ones:
  'rule' SAL_Out_cc_Op(sal_infix_op(and)) :
	 WriteFile("cc_and")

  'rule' SAL_Out_cc_Op(sal_prefix_op(not)):
	 WriteFile("cc_not")

  'rule' SAL_Out_cc_Op(sal_infix_op(implies)):
	 WriteFile("cc_implies")

  'rule' SAL_Out_cc_Op(sal_infix_op(or)):
	 WriteFile("cc_or")

  'rule' SAL_Out_cc_Op(sal_prefix_op(minus)):
	 WriteFile("cc_neg")

  -- Function operators
  'rule' SAL_Out_cc_Op(sal_function_op(supset)):
	 WriteFile("strict_supset?")
  'rule' SAL_Out_cc_Op(sal_function_op(subset)):
	 WriteFile("strict_subset?")
  'rule' SAL_Out_cc_Op(sal_function_op(supseteq)):
	 WriteFile("supset?")
  'rule' SAL_Out_cc_Op(sal_function_op(subseteq)):
	 WriteFile("subset?")
  'rule' SAL_Out_cc_Op(sal_function_op(isin)):
	 WriteFile("isin")
  'rule' SAL_Out_cc_Op(sal_function_op(notisin)):
 	 WriteFile("not_isin")
  'rule' SAL_Out_cc_Op(sal_function_op(rem)):
 	 WriteFile("cc_modulo")
  'rule' SAL_Out_cc_Op(sal_function_op(difference)):
 	 WriteFile("difference")
  'rule' SAL_Out_cc_Op(sal_function_op(restriction_by)):
 	 WriteFile("restriction_by")
  'rule' SAL_Out_cc_Op(sal_function_op(restriction_to)):
	 WriteFile("restriction_to")
  'rule' SAL_Out_cc_Op(sal_function_op(union)):
	 WriteFile("union")
  'rule' SAL_Out_cc_Op(sal_function_op(override)):
	 WriteFile("override")
  'rule' SAL_Out_cc_Op(sal_function_op(inter)):
	 WriteFile("intersection")
  'rule' SAL_Out_cc_Op(sal_function_op(exp)):
	 WriteFile("expt")
  'rule' SAL_Out_cc_Op(sal_function_op(abs)):
	 WriteFile("abs")
  'rule' SAL_Out_cc_Op(sal_function_op(inds)):
	 WriteFile("inds")
  'rule' SAL_Out_cc_Op(sal_function_op(dom)):
	 WriteFile("dom")
  'rule' SAL_Out_cc_Op(sal_function_op(rng)):
	 WriteFile("rng")
  'rule' SAL_Out_cc_Op(sal_function_op(add_set)):
	 WriteFile("add")
  'rule' SAL_Out_cc_Op(sal_function_op(add_map)):
	 WriteFile("add")

  'rule' SAL_Out_cc_Op(sal_function_op(is_true)):
	 WriteFile("is_true")

  'rule' SAL_Out_cc_Op(sal_function_op(is_bool)):
	 WriteFile("is_bool")

  'rule' SAL_Out_cc_Op(T)
	 Putmsg("Debugging activated in SAL_Out_cc_Op\n")
	 print(T)
