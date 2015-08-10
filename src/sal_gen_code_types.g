-- RSL Type Checker
-- Copyright (C) 1998 - 2005 UNU/IIST

-- raise@iist.unu.edu

-- This module generates the SAL type expression
-- code from the SAL abstract syntax tree

 
'module' sal_gen_code_types

'use' ast print 
      ext -- DefaultPos
      env 
      objects 
      values 
      types 
      pp 
      cc	
      sal_aux
      sal_ast
      sal_gen_ast
      sal_gen_code_aux
      sal_gen_code_bindings
      sal_gen_code
      sal_print 
      sal_global_vars     -- for accesing SAL_Current_Cid


'export' 
	 SAL_Out_Type_Expr
--	 SAL_Out_NameQualif	 

	 -- Exported because the routine is also used
	 -- by 'sal_gen_code' for CONTEXT parameter genereation
	 SAL_Out_Qualif_from_Vid
	 SAL_Out_Value_from_Vid
	 SAL_Out_Qualif_from_Tid
	 SAL_Out_Type_from_Tid
----------------------------------------------------------------
--
----------------------------------------------------------------

'action' SAL_Out_Type_Expr(SAL_TYPE_EXPR)

   -- Sort is handled specially due to macro processing:
  'rule' SAL_Out_Type_Expr(user_defined(sal_sort(Tid))):
	 WriteFile("Internal error! Sort type not supported\n")
/*	 WriteFile("M4_Generate_Sort('")
	 Tid'Ident -> Ident
	 SAL_Out_Ident(Ident)
	 WriteFile("', ")
	 Tid'MacroArgs -> ArgList
	 SAL_Out_Macro_Args(ArgList)
	 WriteFile(")")
*/
  -- Specially non-default mapped List definitions are also handled
  -- specially due to macro processing:
  
  'rule' SAL_Out_Type_Expr(rsl_built_in(sal_list_type(Tid, TExpr))):
	 SAL_Out_Qualif_from_Tid(Tid)
	 Tid'Ident -> Id2
	 SAL_Out_Ident(Id2)

  'rule' SAL_Out_Type_Expr(rsl_built_in(sal_finite_set(Tid, TExpr)))
	 SAL_Out_Qualif_from_Tid(Tid)
	 Tid'Ident -> Id2
	 SAL_Out_Ident(Id2)

  'rule' SAL_Out_Type_Expr(rsl_built_in(sal_finite_map(Tid, TE1, TE2)))
	 SAL_Out_Qualif_from_Tid(Tid)
	 Tid'Ident -> Id2
	 SAL_Out_Ident(Id2)

  'rule' SAL_Out_Type_Expr(rsl_built_in(boolean(Tid)))
	 SAL_Out_Qualif_from_Tid(Tid)
	 Tid'Ident -> Id
	 SAL_Out_Ident(Id)

  'rule' SAL_Out_Type_Expr(rsl_built_in(integer(Tid)))
	 SAL_Out_Qualif_from_Tid(Tid)
	 Tid'Ident -> Id
	 SAL_Out_Ident(Id)

  'rule' SAL_Out_Type_Expr(rsl_built_in(natural(Tid)))
	 SAL_Out_Qualif_from_Tid(Tid)
	 Tid'Ident -> Id
	 SAL_Out_Ident(Id)

  'rule' SAL_Out_Type_Expr(rsl_built_in(unit)):
	 -- added CWG. Error should have been reported earlier

 -- Output the rest of the built-in types:
--  'rule' SAL_Out_Type_Expr(rsl_built_in(TExpr)):
--	 SAL_Out_Contex_Qualif_from_Tid(Tid)
         -- CWG this just loops!!  So removed
--	 SAL_Out_Type_Expr(rsl_built_in(TExpr))

  'rule' SAL_Out_Type_Expr(user_defined(sal_tuple_type(TupleList))):
	 WriteFile("[")
	 SAL_Out_Tuple_List(TupleList)
	 WriteFile("]")

  'rule' SAL_Out_Type_Expr(user_defined(sal_tuple_type(list(Tuple, nil)))):
	 SAL_Out_Tuple_List(list(Tuple, nil))
	
  'rule' SAL_Out_Type_Expr(user_defined(sal_abbrev(TExpr)))
	 SAL_Out_Type_Expr(TExpr)

  'rule' SAL_Out_Type_Expr(user_defined(sal_fun_type(D,R)))
	 WriteFile("[")
	 SAL_Out_Type_Expr(D)
	 WriteFile(" -> ")
	 SAL_Out_Type_Expr(R)	 
	 WriteFile("]")

--CWG 24/6/06
  'rule' SAL_Out_Type_Expr(user_defined(sal_ranged_type(L,R))):
	 WriteFile("[")
	 SAL_Out_Expr(L)
	 WriteFile(" .. ")
	 SAL_Out_Expr(R)	 
	 WriteFile("]")
	 

  'rule' SAL_Out_Type_Expr(user_defined(sal_subtype(Id,Type,NS, RestrictionExpr))):
	 WriteFile("{")
	 SAL_Out_IdOp(Id)
	 WriteFile(" : ")
	 SAL_Out_Type_Expr2(Type)
	 WriteFile(" | ")
	 [|
	     ne(NS, nil)
	     Push_Namespace(NS)
  	 |]
	 SAL_Out_Expr(RestrictionExpr)
	 [|
	     ne(NS, nil)
	     Pop_Namespace()
	 |]
	 WriteFile("}")

  'rule' SAL_Out_Type_Expr(user_defined(sal_scalar_type(Vids))):
	 WriteFile("{")
	 SAL_Out_Value_Ids(Vids)
	 WriteFile("}")
	 
  'rule' SAL_Out_Type_Expr(user_defined(sal_record_type(FieldDecls))):
	 WriteFile("[#")
	 SAL_Out_fields(FieldDecls) 
	 WriteFile("#]")

  'rule' SAL_Out_Type_Expr(user_defined(sal_variant_type(DataTypeParts))):
	 WriteFile("DATATYPE")
	 WriteIndntFile(2)
	 WritelnFile(1)
	 SAL_Out_DataTypeParts(DataTypeParts)
	 WritelnFile(1)
	 WriteIndntFile(2)
	 WriteFile("END")

  'rule' SAL_Out_Type_Expr(user_defined(sal_bracket_type(TypeExpr))):
	 SAL_Out_Type_Expr(TypeExpr)

  -- Type References, Qualification required:
  'rule' SAL_Out_Type_Expr(type_refs(TExpr)):
	 where(TExpr -> sal_defined(_,Ident, Tid))
	 SAL_Out_Contex_Qualif_from_Tid(Tid)
	 SAL_Out_Ident(Ident)

  -- Used for generating the native SAL types (not the lifted ones)
  'rule' SAL_Out_Type_Expr(sal_basic(sal_integer)):
	 WriteFile("INTEGER")
  
  'rule' SAL_Out_Type_Expr(sal_basic(sal_boolean)):
	 WriteFile("BOOLEAN")

  'rule' SAL_Out_Type_Expr(sal_basic(sal_rectricted_integer(L,H))):
	 WriteFile("[")
	 SAL_Out_Expr(L)
	 WriteFile(" .. ")
	 SAL_Out_Expr(H)	 
	 WriteFile("]")

  'rule' SAL_Out_Type_Expr(sal_basic(sal_type))
	 WriteFile("TYPE")
 
  'rule' SAL_Out_Type_Expr(sal_basic(sal_total_function(D,R)))
	 WriteFile("[")
	 SAL_Out_Type_Expr(D)
	 WriteFile(" -> ")
	 SAL_Out_Type_Expr(R)	 
	 WriteFile("]")

  'rule' SAL_Out_Type_Expr(user_defined(sal_cc_type(TE, _)))
	 SAL_Out_Type_Expr(TE)

  -- Error debugging:
  'rule' SAL_Out_Type_Expr(nil):
	 WriteFile("nil")

  'rule' SAL_Out_Type_Expr(rsl_built_in(sal_array(Tid,TI,TV)))
	 SAL_Out_Qualif_from_Tid(Tid)
	 Tid'Ident -> Id2
	 SAL_Out_Ident(Id2)
         /*WriteFile("ARRAY ")
         SAL_Out_Type_Expr(TI)
         WriteFile(" OF ")
         SAL_Out_Type_Expr(TV)*/

  'rule' SAL_Out_Type_Expr(sal_basic(sal_array(TI,TV)))
	 /*SAL_Out_Qualif_from_Tid(Tid)
	 Tid'Ident -> Id2
	 SAL_Out_Ident(Id2)*/
         WriteFile("ARRAY ")
         SAL_Out_Type_Expr(TI)
         WriteFile(" OF ")
         SAL_Out_Type_Expr(TV)

  'rule' SAL_Out_Type_Expr(lifted_int)
         WriteFile("IT_AN!Int_")

  'rule' SAL_Out_Type_Expr(TE)
	 Putmsg("Debugging predicate activated int SAL_Out_Type_Expr\n")
	 print(TE)


'action' SAL_Out_Type_Expr2(SAL_TYPE_EXPR)
  'rule' SAL_Out_Type_Expr2(sal_basic(sal_integer)):
	 WriteFile("IT_AN!Int_")
  
  'rule' SAL_Out_Type_Expr2(sal_basic(sal_boolean)):
	 WriteFile("BT_AN!Bool_")

  'rule' SAL_Out_Type_Expr2(T)
         SAL_Out_Type_Expr(T)

----------------------------------------------------------
-- Outputs the restriction for subtype declaration	--
----------------------------------------------------------

'action' SAL_Out_Subtype(SAL_SET_BINDING, SAL_VALUE_EXPR)

  'rule' SAL_Out_Subtype(bindings(BS), Expr):
	 SAL_Out_Bindings(BS, nil, nil -> LBS)
	 [|
	   ne(LBS, nil)
	   SAL_Out_LetBindings(LBS)
	 |]
	 WriteFile(" | ")
	 SAL_Out_Expr(Expr)

-----------------------------------------------------------
-- This function prints in the output file the field     --
-- declaration for the RECORD type			 --
-----------------------------------------------------------

'action' SAL_Out_fields(SAL_DATA_TYPE_PARTS)

  'rule' SAL_Out_fields(list(Head, nil)):
	 SAL_Out_field(Head)

  'rule' SAL_Out_fields(list(Head, Rest)):
	 SAL_Out_field(Head)
	 WriteFile(",\n\t")
	 SAL_Out_fields(Rest)

  'rule' SAL_Out_fields(nil)
	 WriteFile("nil in the fields list")

'action' SAL_Out_field(SAL_DATA_TYPE_PART)

  'rule' SAL_Out_field(sal_part(sal_construc(IdOp, _, _,_), Type)):
	 SAL_Out_IdOp(IdOp)
	 WriteFile(" : ")
	 SAL_Out_Type_Expr(Type)


-----------------------------------------------------------
-- Tuple type constructor				 --
-----------------------------------------------------------
'action' SAL_Out_Tuple_List(SAL_TUPLE_ELEMS)

  'rule' SAL_Out_Tuple_List(list(sal_tuple(TypeExpr), TupleListTail)):
	 SAL_Out_Type_Expr(TypeExpr)
	 [|
	   ne(TupleListTail, nil)
	   WriteFile(", ")
	 |]
	 SAL_Out_Tuple_List(TupleListTail)

  'rule' SAL_Out_Tuple_List(nil):

-----------------------------------------------------------
-- Datatype declaration...
-----------------------------------------------------------

'action' SAL_Out_DataTypeParts(SAL_DATA_TYPE_PARTS)

  'rule' SAL_Out_DataTypeParts(list(DataTypePart, DataTypeParts)):
	 WriteIndntFile(4)
	 SAL_Out_DataTypePart(DataTypePart)
	 [|
	   ne(DataTypeParts, nil)
	   WriteFile(",")
	   WritelnFile(1)
	 |]
	 SAL_Out_DataTypeParts(DataTypeParts)

  'rule' SAL_Out_DataTypeParts(nil):


--------------------------------------------------

'action' SAL_Out_DataTypePart(SAL_DATA_TYPE_PART)

  'rule' SAL_Out_DataTypePart(sal_part(sal_construc(
				IdOp, Vid, Accesors,_), _)):
	 SAL_Out_IdOp(IdOp)
	 [|
	   ne(Accesors, nil)
	   WriteFile("(")
	   SAL_Out_Accesors(Accesors)
	   WriteFile(")")
	 |]



'action' SAL_Out_Contex_Qualif_from_Tid(SAL_type_id)

  'rule' SAL_Out_Contex_Qualif_from_Tid(Tid):
	 SAL_Current_Cid -> CCid
	 Tid'Cid -> OptCid
	 (|
	     where(OptCid -> cid(Cid))
	     [|
		ne(Cid, CCid)
		Cid'Ident -> Id
		SAL_Out_Ident(Id)
		WriteFile("!")
	     |]
	 ||
	     Putmsg("INTERNAL ERROR! Invalid value id qualif.")
	 |)

	 	 

'action' SAL_Out_Qualif_from_Vid(SAL_value_id)

  'rule' SAL_Out_Qualif_from_Vid(Vid):
	 SAL_Current_Cid -> CCid
--Putmsg("Entering to qualify Vid ")
--Vid'IdOp -> id(Id4)
--Print_id(Id4)
--Putmsg(" when generating context ")
--CCid'Ident -> Id1
--Print_id(Id1)
--Putnl()
	 Vid'Cid -> OptCid
	    (|
		where(OptCid -> cid(Cid))
--Vid'Pos -> P
--PrintPos(P)
--Cid'Ident -> Id3
--Print_id(Id3)
--Putnl()

		[|
		   ne(Cid, CCid)
		   Cid'Ident -> Id
		   SAL_Out_Ident(Id)
		   WriteFile("!")
		|]
	    ||
	        Putmsg("INTERNAL ERROR! Invalid value id qualif.")
	    |)
-- The following is deprecated...
/*	 (|
	    Vid'DeclCids -> List
	    ne(List,nil)
	    (|
       	        -- The current context belongs to the set of contexts
		-- where the value was replicated
		SAL_Check_Cid_in_Cids(CCid, List)
		-- No qualification needed
	    ||
	        -- Qualification needed:
		-- Taking any:
		where(List -> list(Cid, Rest))
		Cid'Ident -> Id
		SAL_Out_Ident(Id)
		WriteFile("!")
	    |)
	 ||
	    Vid'Cid -> OptCid
	    (|
		where(OptCid -> cid(Cid))
		[|
		   ne(Cid, CCid)
		   Cid'Ident -> Id
		   SAL_Out_Ident(Id)
		   WriteFile("!")
		|]
	    ||
	        Putmsg("INTERNAL ERROR! Invalid value id qualif.")
	    |)
	 |)
*/

'action' SAL_Out_Qualif_from_Tid(SAL_type_id)

  'rule' SAL_Out_Qualif_from_Tid(Tid):
	 SAL_Current_Cid -> CCid
	 Tid'Cid -> OptCid
	 (|
	     where(OptCid -> cid(Cid))
	     [|
		ne(Cid, CCid)
		Cid'Ident -> Id
		SAL_Out_Ident(Id)
		WriteFile("!")
	     |]
	 ||
	     Putmsg("INTERNAL ERROR! Invalid type id qualif in getting qualif from Tid.")
	 |)


'action' SAL_Out_Type_from_Tid(SAL_type_id)

  'rule' SAL_Out_Type_from_Tid(Tid):
	 SAL_Out_Qualif_from_Tid(Tid)
	 Tid'Ident -> Id
	 SAL_Out_Ident(Id)

'action' SAL_Out_Value_from_Vid(SAL_value_id)

  'rule' SAL_Out_Value_from_Vid(Vid):
	 SAL_Out_Qualif_from_Vid(Vid)
	 Vid'IdOp -> Id
	 SAL_Out_IdOp(Id)

'action' SAL_Out_Macro_Args(SAL_VALUE_IDS)

  'rule' SAL_Out_Macro_Args(list(Vid,Rest))
	 SAL_Out_Qualif_from_Vid(Vid)
	 Vid'IdOp -> IdOp
	 SAL_Out_IdOp(IdOp)
	 SAL_Out_Macro_Args(Rest)

  'rule' SAL_Out_Macro_Args(nil)

'action' SAL_Out_Value_Ids(SAL_VALUE_IDS)

  'rule' SAL_Out_Value_Ids(list(Vid, Vids)):
	 Vid'IdOp -> IdOp
	 SAL_Out_IdOp(IdOp)
	 (|
	   eq(Vids, nil)
	 ||
	   WriteFile(", ")
	   SAL_Out_Value_Ids(Vids)
	 |)
