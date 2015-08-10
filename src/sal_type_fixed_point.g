-- RSL Type Checker
-- Copyright (C) 2005 UNU/IIST

-- raise@iist.unu.edu

-- This module generates processes a type declaration and computes the
-- fixed point that comprises all the values (and, possibly, other
-- type declarations) involved in the type declaration.

'module' sal_type_fixed_point

'use' 
      ast print ext env objects values 
      sal_print
      sal_ast
      sal_aux   -- SAL_Concatenate_Value_Ids
                -- SAL_Concatenate_Context_Constants
      sal_global_vars
'export'
        
      SAL_compute_fixed_point


-- Asumptions:
-- * The type declaration that initiates the fixed point calculation
--   was removed from the original context before invocation.
'action' SAL_compute_fixed_point(SAL_CONTEXT_CONSTANT, SAL_CONTEXTS, SAL_CONTEXT_CONSTANTS 
           -> SAL_CONTEXT_CONSTANTS, SAL_CONTEXTS)
 
   -- Type declaration with fixed point (already calculated)
  'rule' SAL_compute_fixed_point(sal_type_decl(Ident, Tid, TElem), 
                 OriginalContexts,     -- context where the type was declared
                 InProcessList         -- declarations being processed
                                       -- (to avoid recalculation)
                 -> FixedPoint,   -- Body of the new context (with the fixed point)
                    ModifiedContexts) -- The Original Contexts (with
                                      -- the elements in the fixed point removed)

         Tid'FPStatus -> CFlag
         eq(CFlag, calculated)
         -- Nothing must be done to the contexts:
         where(OriginalContexts -> ModifiedContexts)
         -- Retrieve the fixed point stored in the tid:
         Tid'FixedPoint -> FixedPoint         
--Putmsg("Calculating the fixed point for: ")
--Print_id(Ident)
--Putnl()
--print(Tid)
--Putmsg("Fixed point already calculated!\n")
--Print_Fixed_Point(FixedPoint)
--Putmsg("Finished fixed point for: ")
--Print_id(Ident)
--Putnl()


  -- Processing type declarations:
  'rule' SAL_compute_fixed_point(sal_type_decl(Ident, Tid, TElem), 
                 OriginalContexts,     -- context where the type was declared
                 InProcessList         -- declarations being processed
                                       -- (to avoid recalculation)
                 -> FixedPoint,   -- Body of the new context (with the fixed point)
                    ModifiedContexts) -- The Original Contexts (with
                                      -- the elements in the fixed point removed)

--Putmsg("---------------------------------------------------------\n")
--Putmsg("Calculating the fixed point for: ")
--Print_id(Ident)
--Putnl()
--Putmsg("---------------------------------------------------------\n")
--print(Tid)

         -- Extending the 'In process' list to include the current decl
         where(
           SAL_CONTEXT_CONSTANTS'list(sal_type_decl(Ident, Tid, TElem),InProcessList) -> InProcessList1)
         SAL_Collect_VIds_from_Type_Expr(TElem -> ValueIds1, TypeIds1)
         
         Tid'Lifted_fields -> LiftedDataParts
         SAL_Collect_VIds_from_Data_Type_Parts(LiftedDataParts -> Vids,Tids)
         SAL_Concatenate_Value_Ids(ValueIds1, Vids -> ValueIds2)
         SAL_Concatenate_Type_Ids(TypeIds1,Tids -> TypeIds2)

         Remove_duplicates_from_Vids(ValueIds2 -> ValueIds3)
         Remove_duplicates_from_Tids(TypeIds2 -> TypeIds)
	 -- reconstructors should depend on the type, not the other
         -- way round
	 Remove_reconstructors(ValueIds3 -> ValueIds)

--Putmsg(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n")
--Putmsg("Valores colectados: \n")
--SAL_Print_Vids(ValueIds)
--Putmsg("Tipos colectados: \n")
--SAL_Print_Tids(TypeIds)
--Putmsg(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n")
--print(TElem)
         (|
            eq(ValueIds, nil)
            (|
               eq(TypeIds,nil)
               -- Simplest case:
               -- The type declaration does not contain any value reference
               -- neither references to types (other than the basic ones)
               -- Just generate the new context elements:
               where(SAL_CONTEXT_CONSTANTS'list(sal_type_decl(Ident, Tid, TElem),nil) -> FixedPoint)
               -- No need to modify the contexts (see asumptions)
               where(OriginalContexts -> ModifiedContexts)
            ||
               -- Some Types were collected...
               SAL_Collect_Type_Declarations(TypeIds,
                   OriginalContexts, InProcessList1 -> FixedPoint1, ModifiedContexts)
               SAL_Append_Decl(sal_type_decl(Ident, Tid, TElem),FixedPoint1-> FixedPoint2)
               SAL_Remove_Duplicates_from_Fixed_Point(FixedPoint2 -> FixedPoint)
            |)
         ||
            (|
               eq(TypeIds,nil)
               -- There are, however, values to collect:
               -- Collect the declaration:
               SAL_Collect_Value_Declarations(ValueIds,
                    OriginalContexts, InProcessList1 -> FixedPoint1, Reconstructor, ModifiedContexts)
               SAL_Append_Decl(sal_type_decl(Ident, Tid, TElem),FixedPoint1-> FixedPoint2)
               SAL_Remove_Duplicates_from_Fixed_Point(FixedPoint2 -> FixedPoint3)
               SAL_Concatenate_Context_Constants(FixedPoint3,Reconstructor -> FixedPoint4)
               SAL_Remove_Duplicates_from_Decls(FixedPoint4 -> FixedPoint)
            ||
               SAL_Collect_Value_Declarations(ValueIds,
                   OriginalContexts, InProcessList1 -> FixedPoint1, Recons, ModifiedContexts1)
--Putmsg("Despues de colectar valores para: ")
--Print_id(Ident)
--Putnl()
--Putmsg("Se colectaron los reconstructores:\n")
--Print_Fixed_Point(Recons)
--Putmsg("Plus:\n")
--Print_Fixed_Point(FixedPoint1)
               SAL_Collect_Type_Declarations(TypeIds,
                   ModifiedContexts1, InProcessList1 -> FixedPoint2, ModifiedContexts)
               SAL_Concatenate_Context_Constants(FixedPoint1, FixedPoint2 -> FixedPoint3)
               SAL_Append_Decl(sal_type_decl(Ident, Tid,
               TElem),FixedPoint3-> FixedPoint4)
               SAL_Remove_Duplicates_from_Fixed_Point(FixedPoint4 -> FixedPoint5)
               SAL_Concatenate_Context_Constants(FixedPoint5,Recons -> FixedPoint6)
--Putmsg("Fixed point for: ")
--Print_id(Ident)
--Putmsg(" in the most complex case...\nBefore removing duplicates:\n")
--Print_Fixed_Point(FixedPoint6)
--Putmsg(" -----------------------------------------------------------\n")
               SAL_Remove_Duplicates_from_Decls(FixedPoint6 -> FixedPoint)
            |)
         |)
         -- Storing the fixed point:
         Tid'FixedPoint <- FixedPoint
         -- Setting the flag:
         Tid'FPStatus <- calculated
--Putmsg("Finishing Fixed point for: ")
--Tid'Ident -> Ident11
--Print_id(Ident11)
--Putnl()
--Print_Fixed_Point(FixedPoint)
--Putmsg("Finished fixed point for: ")
--Print_id(Ident)
--Putnl()

  'rule' SAL_compute_fixed_point(sal_const_decl(Decl), 
                 OriginalContexts,     -- context where the type was declared
                 InProcessList         -- declarations being processed
                                       -- (to avoid recalculation)
                 -> FixedPoint,   -- Body of the new context (with the fixed point)
                    ModifiedContexts) -- The Original Contexts (with
                                      -- the elements in the fixed point removed)

         -- Extending the 'In process' list to include the current decl
         where(
           SAL_CONTEXT_CONSTANTS'list(sal_const_decl(Decl),InProcessList) -> InProcessList1)

         (|
             where(Decl -> sal_expl_const(IdOp,Vid,TE,VE))
             SAL_Collect_VIds_from_Type_Expr(TE -> Vids1, Tids1)
             SAL_Collect_Value_Ids_from_Value_Expr(VE -> Vids2, Tids2)
             SAL_Concatenate_Value_Ids(Vids1,Vids2 -> ValueIds1)
             SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds1)
         ||
             where(Decl -> sal_fun_const(IdOp,Vid,_,Params,TE,_,VE,_))
             SAL_Collect_Vids_from_Formal_Params(Params -> Vids1,Tids1)
             SAL_Collect_VIds_from_Type_Expr(TE -> Vids2, Tids2)
             SAL_Collect_Value_Ids_from_Value_Expr(VE -> Vids6, Tids6)
             SAL_Concatenate_Value_Ids(Vids1,Vids2 -> Vids5)
             SAL_Concatenate_Value_Ids(Vids5, Vids6 -> ValueIds1)
             SAL_Concatenate_Type_Ids(Tids1,Tids2 -> Tids5)
             SAL_Concatenate_Type_Ids(Tids5, Tids6 -> TypeIds1)
         |)
--Putmsg("Entering to calculate the Fixed point for: ")
--Vid'IdOp -> IdOp1
--SAL_Print_IdOp(IdOp1)
--Putnl()  
         
         Remove_duplicates_from_Vids(ValueIds1 -> ValueIds)
         Remove_duplicates_from_Tids(TypeIds1 -> TypeIds)
--Putmsg(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n")
--Putmsg("Valores colectados: \n")
--SAL_Print_Vids(ValueIds)
--Putmsg("Tipos colectados: \n")
--SAL_Print_Tids(TypeIds)
--Putmsg(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n")
         (|
            eq(ValueIds, nil)
            (|
               eq(TypeIds,nil)
               -- Simplest case:
               -- The type declaration does not contain any value reference
               -- neither references to types (other than the basic ones)
               -- Just generate the new context elements:
               where(SAL_CONTEXT_CONSTANTS'list(sal_const_decl(Decl),nil) -> FixedPoint)
               -- No need to modify the contexts (see asumptions)
               where(OriginalContexts -> ModifiedContexts)
            ||
               -- Some Types were collected...
               SAL_Collect_Type_Declarations(TypeIds,
                   OriginalContexts, InProcessList1 -> FixedPoint1, ModifiedContexts)
               SAL_Append_Decl(sal_const_decl(Decl),FixedPoint1-> FixedPoint2)     
               SAL_Remove_Duplicates_from_Fixed_Point(FixedPoint2 -> FixedPoint) 
            |)
         ||
            (|
               eq(TypeIds,nil)
               -- There are, however, values to collect:
               -- Collect the declaration:
               SAL_Collect_Value_Declarations(ValueIds,
                   OriginalContexts, InProcessList1 -> FixedPoint1,_, ModifiedContexts)
--Putmsg("Fixed point 1:\n")
--Print_Fixed_Point(FixedPoint1)
               SAL_Append_Decl(sal_const_decl(Decl),FixedPoint1-> FixedPoint2)
--Putmsg("Fixed point 2:\n")
--Print_Fixed_Point(FixedPoint2)
               SAL_Remove_Duplicates_from_Fixed_Point(FixedPoint2 -> FixedPoint)
            ||
               SAL_Collect_Value_Declarations(ValueIds,
                   OriginalContexts, InProcessList1 -> FixedPoint1,_, ModifiedContexts1)
--Putmsg("Fixed point 1:\n")
--Print_Fixed_Point(FixedPoint1)
               SAL_Collect_Type_Declarations(TypeIds,
                   ModifiedContexts1, InProcessList1 -> FixedPoint2, ModifiedContexts)
--Putmsg("Fixed point 2:\n")
--Print_Fixed_Point(FixedPoint2)
               SAL_Concatenate_Context_Constants(FixedPoint1,FixedPoint2 -> FixedPoint3)
--Putmsg("Fixed point 3:\n")
--Print_Fixed_Point(FixedPoint3)
               SAL_Append_Decl(sal_const_decl(Decl),FixedPoint3-> FixedPoint4)   
--Putmsg("Fixed point 4:\n")
--Print_Fixed_Point(FixedPoint4)
               SAL_Remove_Duplicates_from_Fixed_Point(FixedPoint4 -> FixedPoint)
            |)
--Putmsg("Final fixed point:\n")
--Print_Fixed_Point(FixedPoint)
         |)
         -- Storing the fixed point:
         Vid'FixedPoint <- FixedPoint
         -- Setting the flag:
         Vid'FPStatus <- calculated
--Putmsg("Fixed point for: ")
--Vid'IdOp -> IdOp11
--SAL_Print_IdOp(IdOp11)
--Putnl()
--Print_Fixed_Point(FixedPoint)  
--Putmsg("Finished fixed point for: ")
--SAL_Print_IdOp(IdOp1)
--Putnl()  

  'rule' SAL_compute_fixed_point(Decl, List,_ -> nil, List)
         Putmsg("Debugging predicate activated in SAL_compute_fixed_point\n")
         print(Decl)

--------------------------------------------------------------------
-- SAL_Collect_Value_Ids_from_Type_Expr
--------------------------------------------------------------------
-- This predicate collects all the value ids that are involved in
-- the type declaration.
--------------------------------------------------------------------

'action' SAL_Collect_VIds_from_Type_Expr(SAL_TYPE_EXPR -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  ------------ RSL basic types... No vids included

  'rule' SAL_Collect_VIds_from_Type_Expr(rsl_built_in(boolean(_)) -> nil,nil)

  'rule' SAL_Collect_VIds_from_Type_Expr(rsl_built_in(integer(_)) -> nil,nil)

  'rule' SAL_Collect_VIds_from_Type_Expr(rsl_built_in(natural(_)) -> nil,nil)

  'rule' SAL_Collect_VIds_from_Type_Expr(rsl_built_in(unit) -> nil,nil)

  ------------ RSL structured types... Collecting from the involved:

  'rule' SAL_Collect_VIds_from_Type_Expr(
                rsl_built_in(sal_finite_set(Tid,TElem)) -> ValueIds, list(Tid, TypeIds))
         SAL_Collect_VIds_from_Type_Expr(TElem -> ValueIds,TypeIds)

--  'rule' SAL_Collect_VIds_from_Type_Expr(
--              rsl_built_in(sal_list_type(_,TElem)) -> ValueIds,TypeIds)
--       SAL_Collect_VIds_from_Type_Expr(TElem -> ValueIds,TypeIds)

  'rule' SAL_Collect_VIds_from_Type_Expr(
           rsl_built_in(sal_list_type(Tid,_)) -> nil,list(Tid,nil))
      
  'rule' SAL_Collect_VIds_from_Type_Expr(
                rsl_built_in(sal_finite_map(Tid,TE1,TE2)) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Type_Expr(TE1 -> VIds1, TIds1)
         SAL_Collect_VIds_from_Type_Expr(TE2 -> VIds2, TIds2)
         SAL_Concatenate_Value_Ids(VIds1,VIds2 -> ValueIds)
         SAL_Concatenate_Type_Ids(TIds1,TIds2 -> TIds3)
         where(SAL_TYPE_IDS'list(Tid, TIds3) -> TypeIds)


  'rule' SAL_Collect_VIds_from_Type_Expr( 
           rsl_built_in(sal_array(Tid,TE1,TE2)) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Type_Expr(TE1 -> VIds1, TIds1)
         SAL_Collect_VIds_from_Type_Expr(TE2 -> VIds2, TIds2)
         SAL_Concatenate_Value_Ids(VIds1, VIds2 -> ValueIds)
         SAL_Concatenate_Type_Ids(TIds1, TIds2 -> TIds3)
         where(SAL_TYPE_IDS'list(Tid, TIds3) -> TypeIds)
         
  ------------ User defined types

  'rule' SAL_Collect_VIds_from_Type_Expr( 
           user_defined(sal_tuple_type(TupleElems)) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Tuple(TupleElems -> ValueIds,TypeIds)     

  'rule' SAL_Collect_VIds_from_Type_Expr( 
           user_defined(sal_abbrev(TElem)) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Type_Expr(TElem -> ValueIds,TypeIds)      

  'rule' SAL_Collect_VIds_from_Type_Expr( 
           user_defined(sal_fun_type(TE1,TE2)) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Type_Expr(TE1 -> VIds1, TIds1)
         SAL_Collect_VIds_from_Type_Expr(TE2 -> VIds2, TIds2)
         SAL_Concatenate_Value_Ids(VIds1,VIds2 -> ValueIds)
         SAL_Concatenate_Type_Ids(TIds1,TIds2 -> TypeIds)

-- CWG 24/6/06
  'rule' SAL_Collect_VIds_from_Type_Expr(
           user_defined(sal_ranged_type(LVE, RVE)) -> ValueIds,TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(LVE -> VIds1, TIds1)
         SAL_Collect_Value_Ids_from_Value_Expr(RVE -> VIds2, TIds2)
         SAL_Concatenate_Value_Ids(VIds1,VIds2 -> ValueIds)
         SAL_Concatenate_Type_Ids(TIds1,TIds2 -> TypeIds)

  'rule' SAL_Collect_VIds_from_Type_Expr( 
           user_defined(sal_subtype(_,TE,_, VE)) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Type_Expr(TE -> VIds1, TIds1)
         SAL_Collect_Value_Ids_from_Value_Expr(VE -> VIds2, TIds2)
         SAL_Concatenate_Value_Ids(VIds1,VIds2 -> ValueIds)
         SAL_Concatenate_Type_Ids(TIds1,TIds2 -> TypeIds)

  'rule' SAL_Collect_VIds_from_Type_Expr(
	   user_defined(sal_scalar_type(Vids)) -> Vids,nil):

  'rule' SAL_Collect_VIds_from_Type_Expr( 
           user_defined(sal_record_type(Fields)) -> ValueIds,TypeIds)
--       SAL_Collect_Value_Ids_from_Fields(Fields -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Data_Type_Parts(Fields -> ValueIds,TypeIds)
 
  'rule' SAL_Collect_VIds_from_Type_Expr( 
           user_defined(sal_variant_type(Variants)) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Data_Type_Parts(Variants -> ValueIds,TypeIds)

  'rule' SAL_Collect_VIds_from_Type_Expr(
           user_defined(sal_bracket_type(TElem)) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Type_Expr(TElem -> ValueIds,TypeIds)

  'rule' SAL_Collect_VIds_from_Type_Expr( 
           user_defined(sal_sort) -> nil,nil)


  ------------ Type references

  -- Avoid including the basic types in the fixed point...
  'rule' SAL_Collect_VIds_from_Type_Expr(type_refs(sal_defined(_,_,Tid)) -> nil,nil)
         (|
            Default_Int_Tid -> IntTid
            eq(IntTid, Tid)
         ||
            Default_Bool_Tid -> BoolTid
            eq(BoolTid, Tid)
         |)

  'rule' SAL_Collect_VIds_from_Type_Expr(type_refs(sal_defined(_,_,Tid)) -> nil,list(Tid,nil))

  'rule' SAL_Collect_VIds_from_Type_Expr(nil -> nil,nil)

  -- SAL types:
 
  'rule' SAL_Collect_VIds_from_Type_Expr(sal_basic(
           sal_total_function(D,R)) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Type_Expr(D -> Vids1, Tids1)
         SAL_Collect_VIds_from_Type_Expr(R -> Vids2, Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2 -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)
 
  'rule' SAL_Collect_VIds_from_Type_Expr(sal_basic(sal_integer) -> nil,nil)

  'rule' SAL_Collect_VIds_from_Type_Expr(sal_basic(sal_boolean) -> nil,nil)

  'rule' SAL_Collect_VIds_from_Type_Expr(sal_basic(sal_rectricted_integer(VE1,VE2)) -> nil,nil)

  'rule' SAL_Collect_VIds_from_Type_Expr(user_defined(sal_cc_type(LTE, _)) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Type_Expr(LTE -> ValueIds, TypeIds)

  'rule' SAL_Collect_VIds_from_Type_Expr(sal_basic(sal_array(_,_)) -> nil, nil)

  'rule' SAL_Collect_VIds_from_Type_Expr(T -> nil,nil)
         Putmsg("Debugging in fixed point\n")
         print(T)
---------------------------------------------------------------------------

'action' SAL_Collect_VIds_from_Tuple(SAL_TUPLE_ELEMS -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_VIds_from_Tuple(list(sal_tuple(TElem), Rest) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Type_Expr(TElem -> VIds1, TIds1)
         SAL_Collect_VIds_from_Tuple(Rest -> VIds2, TIds2)
         SAL_Concatenate_Value_Ids(VIds1,VIds2 -> ValueIds)
         SAL_Concatenate_Type_Ids(TIds1,TIds2 -> TypeIds)

  'rule' SAL_Collect_VIds_from_Tuple(nil -> nil,nil)

---------------------------------------------------------------------------

'action' SAL_Collect_Value_Ids_from_Set_Bindings(SAL_SET_BINDING -> SAL_VALUE_IDS, SAL_TYPE_IDS)
         
  'rule' SAL_Collect_Value_Ids_from_Set_Bindings(bindings(BS) -> ValueIds,TypeIds)
         SAL_Collect_Value_Ids_from_Bindings(BS -> ValueIds,TypeIds)

---------------------------------------------------------------------------

'action' SAL_Collect_Value_Ids_from_Bindings(SAL_BINDINGS -> SAL_VALUE_IDS, SAL_TYPE_IDS)
         
  'rule' SAL_Collect_Value_Ids_from_Bindings(list(B,BS) -> ValueIds,TypeIds)
         SAL_Collect_Value_Ids_from_Binding(B -> VIds1, TIds1)
         SAL_Collect_Value_Ids_from_Bindings(BS -> VIds2, TIds2) 
         SAL_Concatenate_Value_Ids(VIds1,VIds2 -> ValueIds)
         SAL_Concatenate_Type_Ids(TIds1,TIds2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Bindings(nil -> nil,nil)

----------------------------------------------------------------------------

'action' SAL_Collect_Value_Ids_from_Binding(SAL_BINDING -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_Value_Ids_from_Binding(sal_prod_binding(Pos, BS) -> ValueIds,TypeIds)
         SAL_Collect_Value_Ids_from_Bindings(BS -> ValueIds,TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Binding(sal_typed_prod(_,BS, TElem) -> ValueIds,TypeIds)
         SAL_Collect_Value_Ids_from_Bindings(BS -> VIds1, TIds1)
         SAL_Collect_VIds_from_Type_Expr(TElem -> VIds2, TIds2)
         SAL_Concatenate_Value_Ids(VIds1,VIds2 -> ValueIds)
         SAL_Concatenate_Type_Ids(TIds1,TIds2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Binding(sal_typed_id(_,_, TElem) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Type_Expr(TElem -> ValueIds,TypeIds)

----------------------------------------------------------------------------

'action' SAL_Collect_Value_Ids_from_Fields(SAL_FIELD_DECLS -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_Value_Ids_from_Fields(list(F,FS) -> ValueIds,TypeIds)
         SAL_Collect_Value_Ids_from_Field(F -> VIds1, TIds1)
         SAL_Collect_Value_Ids_from_Fields(FS -> VIds2, TIds2)
         SAL_Concatenate_Value_Ids(VIds1,VIds2 -> ValueIds)
         SAL_Concatenate_Type_Ids(TIds1,TIds2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Fields(nil -> nil,nil)

'action' SAL_Collect_Value_Ids_from_Field(SAL_FIELD_DECL -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_Value_Ids_from_Field(field(_, Vid, Texpr) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Type_Expr(Texpr -> Vids1, TypeIds)
         where(SAL_VALUE_IDS'list(Vid, Vids1) -> ValueIds)

  'rule' SAL_Collect_Value_Ids_from_Field(nil -> nil,nil)

----------------------------------------------------------------------------

'action' SAL_Collect_VIds_from_Data_Type_Parts(SAL_DATA_TYPE_PARTS -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_VIds_from_Data_Type_Parts(list(DT,DTS) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Data_Type_Part(DT -> VIds1, TIds1)
         SAL_Collect_VIds_from_Data_Type_Parts(DTS -> VIds2, TIds2)
         SAL_Concatenate_Value_Ids(VIds1,VIds2 -> ValueIds)
         SAL_Concatenate_Type_Ids(TIds1,TIds2 -> TypeIds)

  'rule' SAL_Collect_VIds_from_Data_Type_Parts(nil -> nil,nil)


'action' SAL_Collect_VIds_from_Data_Type_Part(SAL_DATA_TYPE_PART -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_VIds_from_Data_Type_Part(sal_part(Constr, TExpr) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Constructor(Constr -> VIds1, TIds1)
         SAL_Collect_VIds_from_Type_Expr(TExpr -> VIds2, TIds2)
         SAL_Concatenate_Value_Ids(VIds1,VIds2 -> ValueIds)
         SAL_Concatenate_Type_Ids(TIds1,TIds2 -> TypeIds)

'action' SAL_Collect_VIds_from_Constructor(SAL_CONSTRUCTOR -> SAL_VALUE_IDS, SAL_TYPE_IDS)
         
  'rule' SAL_Collect_VIds_from_Constructor(
           sal_construc(_,Vid, Accs, Recons) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Accesors(Accs -> VIds1, TIds1)
         SAL_Collect_VIds_from_Reconstructors(Recons -> VIds2, TIds2)
         SAL_Concatenate_Value_Ids(VIds1,VIds2 -> VIds3)
         where(SAL_VALUE_IDS'list(Vid, VIds3) -> ValueIds)
	 -- ignore type from reconstructors
         --SAL_Concatenate_Type_Ids(TIds1,TIds2 -> TypeIds)
	 where(TIds1 -> TypeIds)

'action' SAL_Collect_VIds_from_Accesors(SAL_DESTRUCTORS -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_VIds_from_Accesors(list(A,As) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Accesor(A -> VIds1, TIds1)
         SAL_Collect_VIds_from_Accesors(As-> VIds2, TIds2)
         SAL_Concatenate_Value_Ids(VIds1,VIds2 -> ValueIds)
         SAL_Concatenate_Type_Ids(TIds1,TIds2 -> TypeIds)

  'rule' SAL_Collect_VIds_from_Accesors(nil -> nil,nil)

'action' SAL_Collect_VIds_from_Accesor(SAL_DESTRUCTOR -> SAL_VALUE_IDS, SAL_TYPE_IDS)
         
  'rule' SAL_Collect_VIds_from_Accesor(sal_destructor(_, Vid, TElem,_) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Type_Expr(TElem -> VIds1, TypeIds)
         where(SAL_VALUE_IDS'list(Vid, VIds1) -> ValueIds)

'action' SAL_Collect_VIds_from_Reconstructors(SAL_RECONSTRUCTORS -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_VIds_from_Reconstructors(list(A,As) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Reconstructor(A -> VIds1, TIds1)
         SAL_Collect_VIds_from_Reconstructors(As-> VIds2, TIds2)
         SAL_Concatenate_Value_Ids(VIds1,VIds2  -> ValueIds)
         SAL_Concatenate_Type_Ids(TIds1,TIds2 -> TypeIds)

  'rule' SAL_Collect_VIds_from_Reconstructors(nil -> nil,nil)

'action' SAL_Collect_VIds_from_Reconstructor(SAL_RECONSTRUCTOR -> SAL_VALUE_IDS, SAL_TYPE_IDS)
         
  'rule' SAL_Collect_VIds_from_Reconstructor(sal_reconstructor(_, Vid, TElem,_,_) -> ValueIds,TypeIds)
         SAL_Collect_VIds_from_Type_Expr(TElem -> VIds1, TypeIds)
         where(SAL_VALUE_IDS'list(Vid, VIds1) -> ValueIds)

---------------------------------------------------------------------------
-- SAL_Collect_Value_Ids_from_Value_Expr
---------------------------------------------------------------------------
-- Collects the values from value expressions...
---------------------------------------------------------------------------

'action' SAL_Collect_Value_Ids_from_Value_Expr(SAL_VALUE_EXPR -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_literal(_) -> nil,nil)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_named_val(_) -> nil, nil)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_product(Exprs) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Exprs(Exprs -> ValueIds, TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_ranged_set(V1,V2,T) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids1, Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(V2 -> Vids2, Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_enum_set(Tid,TExpr,Exprs) -> ValueIds, TypeIds)
         SAL_Collect_VIds_from_Type_Expr(TExpr -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Value_Exprs(Exprs -> Vids2, Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2 -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> Tids3)
         where(SAL_TYPE_IDS'list(Tid, Tids3) -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_comp_simp_set(SB, Expr) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Set_Bindings(SB -> Vids1, Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(Expr -> Vids2, Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2 -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_comp_set(VE1,TExpr,SB,VE2) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(VE1 -> Vids1,Tids1)
         SAL_Collect_VIds_from_Type_Expr(TExpr -> Vids2,Tids2)
         SAL_Collect_Value_Ids_from_Set_Bindings(SB -> Vids3, Tids3)
         SAL_Collect_Value_Ids_from_Value_Expr(VE2 -> Vids4,Tids4)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> Vids5)
         SAL_Concatenate_Value_Ids(Vids3,Vids4  -> Vids6)
         SAL_Concatenate_Value_Ids(Vids5,Vids6  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> Tids5)
         SAL_Concatenate_Type_Ids(Tids3,Tids4 -> Tids6)
         SAL_Concatenate_Type_Ids(Tids5,Tids6 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_ranged_list(VE1,VE2) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(VE1 -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(VE2 -> Vids2,Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_enum_list(Exprs) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Exprs(Exprs -> ValueIds, TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_comp_list(Expr,Limit) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(Expr -> Vids1, Tids1)
         SAL_Collect_Value_Ids_from_Limit(Limit -> Vids2, Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_enum_map(Tid, D, R, ExprPairs) -> ValueIds, TypeIds)
         SAL_Collect_VIds_from_Type_Expr(D -> Vids1,Tids1)
         SAL_Collect_VIds_from_Type_Expr(R -> Vids2,Tids2)
         SAL_Collect_Value_Ids_from_Expr_Pairs(ExprPairs -> Vids3, Tids3)
         SAL_Concatenate_Value_Ids(Vids1,Vids2 -> Vids4)
         SAL_Concatenate_Value_Ids(Vids4,Vids3 -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> Tids4)
         SAL_Concatenate_Type_Ids(Tids4,Tids3 -> Tids5)
         where(SAL_TYPE_IDS'list(Tid, Tids5) -> TypeIds)

         

  'rule'
         SAL_Collect_Value_Ids_from_Value_Expr(sal_comp_rng_map(V1,Vid, Nid,SB,V2) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Set_Bindings(SB -> Vids4,Tids4)
         SAL_Collect_Value_Ids_from_Value_Expr(V2 -> Vids5,Tids5)
         SAL_Concatenate_Value_Ids(Vids1,Vids4  -> Vids6)
         SAL_Concatenate_Value_Ids(Vids5,Vids6  -> Vids7)
	 where(SAL_VALUE_IDS'list(Vid, list(Nid, Vids7)) -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids4  -> Tids7)
         SAL_Concatenate_Type_Ids(Tids5,Tids7  -> TypeIds)


  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_comp_map(EP,Tid, SB,V2)  -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Expr_Pairs(list(EP,nil) -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Set_Bindings(SB -> Vids4,Tids4)
         SAL_Collect_Value_Ids_from_Value_Expr(V2 -> Vids5,Tids5)
         SAL_Concatenate_Value_Ids(Vids1,Vids4  -> Vids6)
         SAL_Concatenate_Value_Ids(Vids5,Vids6  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids4  -> Tids7)
         SAL_Concatenate_Type_Ids(Tids5,Tids7  -> Tids8)
         where(SAL_TYPE_IDS'list(Tid, Tids8) -> TypeIds)


  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_function(LB,Expr) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Lambda_Binding(LB -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(Expr -> Vids2,Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_list_applic(V1,Args) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Arguments(Args -> Vids2,Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_map_applic(Tid, V1,Args) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Arguments(Args -> Vids2,Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_funct_applic(V1,Args) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Arguments(Args -> Vids2,Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_destr_applic(V1,V2) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids1, Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(V2 -> Vids2, Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_quantified(_, SB, V1) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Set_Bindings(SB -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids2, Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_equivalence(V1,V2,V3) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(V2 -> Vids2, Tids2)
         SAL_Collect_Value_Ids_from_Value_Expr(V3 -> Vids3,Tids3)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> Vids4)
         SAL_Concatenate_Value_Ids(Vids4,Vids3  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2  -> Tids4)
         SAL_Concatenate_Type_Ids(Tids4,Tids3  -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_bracket(V1) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> ValueIds, TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_funct_expr(VAL_ID,_,VE1,VE2) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(VE1 -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(VE2 -> Vids2,Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> Tids3)
         SAL_Extract_Tid_from_value_id(VAL_ID -> Tids4)
         SAL_Concatenate_Type_Ids(Tids4,Tids3  -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_ax_infix(VE1,_,VE2) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(VE1 -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(VE2 -> Vids2,Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_ax_prefix(_, V1) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> ValueIds, TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_let_expr(_,T,N,_,V1,V2) -> ValueIds, TypeIds)
         SAL_Collect_VIds_from_Type_Expr(T -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids2,Tids2)
         SAL_Collect_Value_Ids_from_Value_Expr(V2 -> Vids3,Tids3)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> Vids4)
         SAL_Concatenate_Value_Ids(Vids4,Vids3  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2  -> Tids4)
         SAL_Concatenate_Type_Ids(Tids4,Tids3  -> TypeIds)


  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_if_expr(V1,V2,ES,Else) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(V2 -> Vids2,Tids2)
         SAL_Collect_Value_Ids_from_Elsifs(ES -> Vids3,Tids3)
         (|
             where(Else -> else(V3))
             SAL_Collect_Value_Ids_from_Value_Expr(V3 -> Vids4,Tids4)
         ||
             where(SAL_VALUE_IDS'nil -> Vids4)
             where(SAL_TYPE_IDS'nil -> Tids4)
         |)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> Vids5)
         SAL_Concatenate_Value_Ids(Vids3,Vids4  -> Vids6)
         SAL_Concatenate_Value_Ids(Vids5,Vids6  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2  -> Tids5)
         SAL_Concatenate_Type_Ids(Tids3,Tids4  -> Tids6)
         SAL_Concatenate_Type_Ids(Tids5,Tids6  -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_value_occ(VAL_ID,_) -> nil, Tids)
         SAL_Extract_Tid_from_value_id(VAL_ID -> Tids)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_esp_value_occ(Vid) -> list(Vid,nil), nil)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_esp_prefix_occ(SAL_IdOp, V1, V2) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids1, Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(V2 -> Vids2, Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> Tids3)
         SAL_Extract_Tid_from_value_id(SAL_IdOp -> Tids4)
         SAL_Concatenate_Type_Ids(Tids3, Tids4 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_esp_unary_prefix_occ(SAL_IdOp, V) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V -> ValueIds, Tids1)
         SAL_Extract_Tid_from_value_id(SAL_IdOp -> Tids2)
         SAL_Concatenate_Type_Ids(Tids1, Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_infix_occ(V1,SAL_IdOp,V2) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids1, Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(V2 -> Vids2, Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> Tids3)
         SAL_Extract_Tid_from_value_id(SAL_IdOp -> Tids4)
         SAL_Concatenate_Type_Ids(Tids3, Tids4 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_prefix_occ(VAL_ID,_,V) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V -> ValueIds, Tids1)
         SAL_Extract_Tid_from_value_id(VAL_ID -> Tids2)
         SAL_Concatenate_Type_Ids(Tids1, Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_assignment(_,V) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V -> ValueIds, TypeIds)

  -- Processing speciall cc expressions:
  'rule' SAL_Collect_Value_Ids_from_Value_Expr(sal_ranged_cc_set(_, SetTE, ElemTE, Restriction, T) -> ValueIds, TypeIds)
         SAL_Collect_VIds_from_Type_Expr(SetTE -> Vids1,Tids1)
         SAL_Collect_VIds_from_Type_Expr(ElemTE -> Vids2,Tids2)
         SAL_Collect_Value_Ids_from_Value_Expr(Restriction -> Vids3, Tids3)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> Vids4)
         SAL_Concatenate_Value_Ids(Vids4,Vids3  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2  -> Tids4)
         SAL_Concatenate_Type_Ids(Tids4,Tids3  -> TypeIds)

  'rule'
  SAL_Collect_Value_Ids_from_Value_Expr(sal_cc_map_applic(MapTid, MapVE, sal_argument(VEs)) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(MapVE -> Vids1,Tids1)
         SAL_Collect_Value_Ids_from_Value_Exprs(VEs -> Vids2, Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> Tids3)
         where(SAL_TYPE_IDS'list(MapTid, Tids3) -> TypeIds)

         -- Collects from (collects nothing actually)    
         --    not_supported
         --    no_val
         --    no_def
         --    nil      
  'rule' SAL_Collect_Value_Ids_from_Value_Expr(_ -> nil, nil)

----------------------------------------------------------------------------------------
'action' SAL_Collect_Value_Ids_from_Value_Exprs(SAL_VALUE_EXPRS -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_Value_Ids_from_Value_Exprs(list(V, Rest) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V -> Vids1, Tids1)
         SAL_Collect_Value_Ids_from_Value_Exprs(Rest -> Vids2, Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Value_Exprs(nil -> nil, nil)
---------------------------------------------------------------------------------------
'action' SAL_Collect_Value_Ids_from_Limit(SAL_LIST_LIMIT -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_Value_Ids_from_Limit(sal_limit(BS, V1,V2) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Bindings(BS -> Vids1, Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids2, Tids2)
         SAL_Collect_Value_Ids_from_Value_Expr(V2 -> Vids3, Tids3)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> Vids4)
         SAL_Concatenate_Value_Ids(Vids4,Vids3  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2  -> Tids4)
         SAL_Concatenate_Type_Ids(Tids4,Tids3  -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Limit(nil -> nil,nil)
---------------------------------------------------------------------------------------
'action' SAL_Collect_Value_Ids_from_Expr_Pairs(SAL_VALUE_EXPR_PAIRS -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_Value_Ids_from_Expr_Pairs(list(H,T) -> ValueIds, TypeIds)
         (|
            where(H -> pair(V1,V2))
            SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids1, Tids1)
            SAL_Collect_Value_Ids_from_Value_Expr(V2 -> Vids2, Tids2)
            SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
            SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)
         ||
            where(SAL_VALUE_IDS'nil -> ValueIds)
            where(SAL_TYPE_IDS'nil -> TypeIds)
         |)   

  'rule' SAL_Collect_Value_Ids_from_Expr_Pairs(nil -> nil, nil)
----------------------------------------------------------------------------------------
'action' SAL_Collect_Value_Ids_from_Lambda_Binding(SAL_LAMBDA_BINDINGS -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_Value_Ids_from_Lambda_Binding(
           list(bindings(BS), Rest) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Bindings(BS -> Vids1, Tids1)
         SAL_Collect_Value_Ids_from_Lambda_Binding(Rest -> Vids2, Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Lambda_Binding(nil -> nil,nil)

----------------------------------------------------------------------------------------
'action' SAL_Collect_Value_Ids_from_Arguments(SAL_ARGS -> SAL_VALUE_IDS, SAL_TYPE_IDS)
         
  'rule' SAL_Collect_Value_Ids_from_Arguments(sal_argument(Exprs) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Exprs(Exprs -> ValueIds, TypeIds)

----------------------------------------------------------------------------------------
'action' SAL_Collect_Value_Ids_from_Elsifs(SAL_ELSIF_BRANCHES -> SAL_VALUE_IDS, SAL_TYPE_IDS)

  'rule' SAL_Collect_Value_Ids_from_Elsifs(list(elsif(V1,V2), Rest) -> ValueIds, TypeIds)
         SAL_Collect_Value_Ids_from_Value_Expr(V1 -> Vids1, Tids1)
         SAL_Collect_Value_Ids_from_Value_Expr(V2 -> Vids2, Tids2)
         SAL_Collect_Value_Ids_from_Elsifs(Rest -> Vids3, Tids3)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> Vids4)
         SAL_Concatenate_Value_Ids(Vids4,Vids3  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2  -> Tids4)
         SAL_Concatenate_Type_Ids(Tids4,Tids3  -> TypeIds)

  'rule' SAL_Collect_Value_Ids_from_Elsifs(nil -> nil,nil)
----------------------------------------------------------------------------------------
'action' SAL_Collect_Vids_from_Formal_Params(SAL_FORMAL_FUN_PARAMETERS -> SAL_VALUE_IDS, SAL_TYPE_IDS) 

  'rule' SAL_Collect_Vids_from_Formal_Params(list(formal_param(_,T,_), Rest) -> ValueIds, TypeIds)
         SAL_Collect_VIds_from_Type_Expr(T -> Vids1,Tids1)
         SAL_Collect_Vids_from_Formal_Params(Rest -> Vids2,Tids2)
         SAL_Concatenate_Value_Ids(Vids1,Vids2  -> ValueIds)
         SAL_Concatenate_Type_Ids(Tids1,Tids2 -> TypeIds)

  'rule' SAL_Collect_Vids_from_Formal_Params(nil -> nil,nil)
----------------------------------------------------------------------------
-- SAL_Collect_Value_Declarations
----------------------------------------------------------------------------
-- This predicate collects the value declarations that matches with
-- the ones included in the value-id list passed as argument.
-- The algorithm first tries to use some (if any) already-calculated
-- fixed point. For those ones not calculated, the algorithm will
-- calculate it by itself.
----------------------------------------------------------------------------

'action' SAL_Collect_Value_Declarations(SAL_VALUE_IDS, SAL_CONTEXTS, SAL_CONTEXT_CONSTANTS
                        -> SAL_CONTEXT_CONSTANTS,SAL_CONTEXT_CONSTANTS,SAL_CONTEXTS)

  'rule' SAL_Collect_Value_Declarations(list(Vid, Vids), Contexts, InProcessList ->  
                                          Result, Reconstructors, ModifiedContexts)
         SAL_Collect_Value_Declaration(Vid, Contexts, InProcessList ->
                                            Decls1, Recons1, ModifiedContexts1)
         SAL_Collect_Value_Declarations(Vids, ModifiedContexts1,
                         InProcessList -> Decls2, Recons2, ModifiedContexts)
         SAL_Concatenate_Context_Constants(Decls1, Decls2 -> Result)
         SAL_Concatenate_Context_Constants(Recons1,Recons2 -> Reconstructors)


  'rule' SAL_Collect_Value_Declarations(nil, Contexts,_ -> nil, nil, Contexts)

'action' SAL_Collect_Value_Declaration(SAL_value_id, SAL_CONTEXTS, SAL_CONTEXT_CONSTANTS 
                -> SAL_CONTEXT_CONSTANTS, SAL_CONTEXT_CONSTANTS, SAL_CONTEXTS)

  -- If the current tid belongs to set being processed currently, then
  -- do not recalculate it!
  'rule' SAL_Collect_Value_Declaration(Vid,OrigContexts,InProcessList -> nil, Reconstructor, OrigContexts)
         Is_Vid_Included_in_Decls(Vid, InProcessList)
--Putmsg("Collecting value declarations (and fixed points) for: ")
--SAL_Print_Vid(Vid)
--Putnl()
--Putmsg("Skipping (currently calculating it!\n")
         Vid'VType -> VType
         (|
            eq(VType, reconstructor_value)
            -- As it is in the list, the Vid must have the declaration:
            Vid'Declaration -> Decl
            where(SAL_CONTEXT_CONSTANTS'list(Decl,nil) -> Reconstructor)
--Putmsg("(But it is a reconstructor)\n")
         ||
            where(SAL_CONTEXT_CONSTANTS'nil -> Reconstructor)
         |)



  'rule' SAL_Collect_Value_Declaration(Vid, OrigContexts,
            InProcessList -> Decls, Reconstructor, ModifiedContexts)

         
--Putmsg("Procesando valor: ")
--SAL_Print_Vid(Vid)     
--Putnl()
         (|
            Vid'VType -> VType
            (| eq(VType, record_field) || eq(VType, constructor_value) || eq(VType, global_parameter) |)
            -- The value corresponds to a record field
            -- No further calculation is needed (the types in the
            -- field where collected already when processing the record)
            where(OrigContexts -> ModifiedContexts)
            where(SAL_CONTEXT_CONSTANTS'nil -> Decls)
            where(SAL_CONTEXT_CONSTANT'nil -> Decl)
--Putmsg("Record/Constructor field... skipping\n")
         ||
            Vid'FPStatus -> Status
            -- The fixed point was not calculated before...
            (|
               eq(Status, not_calculated)
               SAL_Extract_Value_Decl_from_Contexts(Vid, OrigContexts -> Decl,ModifiedContexts1)
               (|
                   eq(Decl, nil)
                   (|
                      Vid'Declaration -> Decl1
                      Vid'VType -> VType
                      eq(VType, reconstructor_value)
--Putmsg("It is a reconstructor\n")
                      ne(Decl1,nil)
--Putmsg("Declaration not found... solving with Vid's internal data\n")
                      SAL_compute_fixed_point(Decl1, ModifiedContexts1,InProcessList  ->  Decls, ModifiedContexts)
                      -- Storing the fixed point in the vid (optimization):
                      Vid'FixedPoint <- Decls
                      Vid'FPStatus <- calculated
                   ||                         
--Putmsg("Declaration not found... solving with type\n")
                      -- The value doesn't have a declaration...
                      -- case, for example, of constructors
                      Vid'Type -> TExpr
                      (|
                        where(TExpr -> type_refs(sal_defined(_,_,Tid)))
                        Tid'FPStatus -> TStatus
                        (|
                          eq(TStatus, calculated)
                          Tid'FixedPoint -> Decls
                          Tid'Declaration -> Decl1
                          where(calculated -> NewStatus)
                        ||
                          Tid'Declaration -> Decl1
                          where(SAL_CONTEXT_CONSTANTS'nil -> Decls)
                          where(not_calculated -> NewStatus)
                        |)
                        Vid'FixedPoint <- Decls
                        Vid'Declaration <- Decl1
                        Vid'FPStatus <- NewStatus
                     ||
                        where(OrigContexts -> ModifiedContexts)
                        where(SAL_CONTEXT_CONSTANTS'nil -> Decls)
                        Vid'FixedPoint <- Decls
                        Vid'FPStatus <- not_calculated
                     |)
                     where(OrigContexts -> ModifiedContexts)
                   |)
               ||
--Putmsg("Declaration FOUND...\n")
                   -- Calculate the fixed point:
                   SAL_compute_fixed_point(Decl, ModifiedContexts1,InProcessList  ->  Decls, ModifiedContexts)
                   -- Storing the fixed point in the vid (optimization):
                   Vid'FixedPoint <- Decls
                   Vid'Declaration <- Decl
                   Vid'FPStatus <- calculated
               |)
            ||
--Putmsg("Ya tengo un fixed point...(")
--SAL_Print_Vid(Vid)     
--Putmsg(")\n")
               -- The fixed point was already calculated and is inside
               -- the value id:
               where(OrigContexts -> ModifiedContexts)
               Vid'Declaration -> Decl
               Vid'FixedPoint -> FP
               -- Append the fixed point if it is not nil:
               (|
                  ne(FP,nil)
--Putmsg("Non nil fixed point\nDe hecho tengo en el FP:\n")
--Print_Fixed_Point(FP)
                  SAL_Append_Decl(Decl,FP -> Decls)
               ||
--Putmsg("nil fixed point (skipping)\n")
                  where(SAL_CONTEXT_CONSTANTS'list(Decl,nil) -> Decls)
               |)
            |)
         |)
         Vid'VType -> VType1
         (|        
            eq(VType1, reconstructor_value)
            where(SAL_CONTEXT_CONSTANTS'list(Decl,nil) -> Reconstructor)
--Putmsg("Procesando valor: ")
--SAL_Print_Vid(Vid)     
--Putnl()
--Putmsg("(But it is a reconstructor)\n")
         ||
            where(SAL_CONTEXT_CONSTANTS'nil -> Reconstructor)
         |)


'action' SAL_Extract_Value_Decl_from_Contexts(SAL_value_id, SAL_CONTEXTS 
                                     -> SAL_CONTEXT_CONSTANT, SAL_CONTEXTS)

  'rule' SAL_Extract_Value_Decl_from_Contexts(Vid, 
             list(context(Ident, CCid, Elems), Rest) -> Decl, Contexts):
         -- The Vid contains the Cid of the context of declaration:
         Vid'Cid -> OptCid
         where(OptCid -> cid(Cid))
         where(CCid -> cid(Cid1))
--Putmsg("Comparando... \nEl Cid donde se supone que esta es: ")
--Cid'Ident -> Id1
--Print_id(Id1)
--print(Cid)
--Putmsg("y el contexto actual es: ")
--Cid1'Ident -> Id2
--Print_id(Id2)
--Putnl()
--print(Cid1)
         (|
            eq(Cid, Cid1)
--Putmsg("Coincidieron\n")
            -- This is the context where the valus is declared:
            SAL_Extract_Value_Decl_from_Context_Elems(Vid,Elems -> Decl, ModifiedElems)
--Putmsg("Se encontro la declaracion en el contexto\n")
--print(Decl)
            where(context(Ident, CCid, ModifiedElems) -> ModifiedContext)
            -- remove from the static:
            Remove_Decl_from_Static(Cid1, Decl)
            where(SAL_CONTEXTS'list(ModifiedContext, Rest) ->  Contexts)
         ||
--Putmsg("Buscando en otro contexto\n")
            -- This is not the context... process the next
            SAL_Extract_Value_Decl_from_Contexts(Vid, Rest -> Decl, Contexts1)
            where(SAL_CONTEXTS'list(context(Ident, CCid, Elems), Contexts1) -> Contexts)
         |)

  'rule' SAL_Extract_Value_Decl_from_Contexts(Vid, nil -> nil,nil)
--Putmsg("Search failed\n")
--       Putmsg("Warning... declaration not found for: ")
--       SAL_Print_Vid(Vid)
--       Putnl()

'action' SAL_Extract_Value_Decl_from_Context_Elems(SAL_value_id, SAL_CONTEXT_CONSTANTS 
                -> SAL_CONTEXT_CONSTANT, SAL_CONTEXT_CONSTANTS)         

  'rule' SAL_Extract_Value_Decl_from_Context_Elems(Vid, 
                list(sal_const_decl(Decl),Rest) -> DeclOut, Decls)
         (|
            SAL_match_Vid_with_Decl(Vid,Decl)
--Putmsg("Hizo match")
            where(Rest -> Decls)
            where(sal_const_decl(Decl) -> DeclOut)
         ||
            SAL_Extract_Value_Decl_from_Context_Elems(Vid, Rest -> DeclOut, Decls1)
            where(SAL_CONTEXT_CONSTANTS'list(sal_const_decl(Decl), Decls1) -> Decls)
         |)     

  'rule' SAL_Extract_Value_Decl_from_Context_Elems(Vid, list(Elem, Rest) ->
                DeclOut, Decls)
         SAL_Extract_Value_Decl_from_Context_Elems(Vid, Rest -> DeclOut, Decls1)
         where(SAL_CONTEXT_CONSTANTS'list(Elem, Decls1) -> Decls)

  'rule' SAL_Extract_Value_Decl_from_Context_Elems(_, nil -> nil, nil)
--Putmsg("No Hizo match con nada")

'condition' SAL_match_Vid_with_Decl(SAL_value_id, SAL_CONSTANT_DECL)

  'rule' SAL_match_Vid_with_Decl(Vid, sal_expl_const(_, Vid1, _,_))
--Putmsg("Chequeando: ")
--SAL_Print_Vid(Vid)
--Putmsg("Contra: ")
--SAL_Print_Vid(Vid1)
         eq(Vid, Vid1)


  'rule' SAL_match_Vid_with_Decl(Vid, sal_fun_const(_, Vid1,  _,_,_,_,_,_))
         eq(Vid, Vid1)

 -- The rest of the values do not introduce Vids....



--------------------------------------------------------------------------------
-- SAL_Collect_Type_Declarations
--------------------------------------------------------------------------------
-- This predicate collects the value declarations that matches with
-- the ones included in the type-id list passed as argument.
-- The algorithm first tries to use some (if any) already-calculated
-- fixed point. For those ones not calculated, the algorithm will
-- calculate it by itself.
--------------------------------------------------------------------------------

'action' SAL_Collect_Type_Declarations(SAL_TYPE_IDS, SAL_CONTEXTS, SAL_CONTEXT_CONSTANTS 
                                                   -> SAL_CONTEXT_CONSTANTS,SAL_CONTEXTS)

  'rule' SAL_Collect_Type_Declarations(list(Tid, Tids), Contexts, InProcessList ->  
                                                  Result, ModifiedContexts)
         SAL_Collect_Type_Declaration(Tid, Contexts, InProcessList -> Decls1, ModifiedContexts1)
         SAL_Collect_Type_Declarations(Tids, ModifiedContexts1, InProcessList -> Decls2, ModifiedContexts)
         SAL_Concatenate_Context_Constants(Decls1, Decls2 -> Result)

  'rule' SAL_Collect_Type_Declarations(nil, Contexts,_ -> nil, Contexts)

-----------------------------------------------------------------------------

'action' SAL_Collect_Type_Declaration(SAL_type_id, SAL_CONTEXTS, SAL_CONTEXT_CONSTANTS 
                                                 -> SAL_CONTEXT_CONSTANTS, SAL_CONTEXTS)

  -- If the current tid belongs to set being processed currently, then
  -- do not recalculate it!
  'rule' SAL_Collect_Type_Declaration(Tid,OrigContexts,InProcessList -> nil, OrigContexts)
         Is_Tid_Included_in_Decls(Tid, InProcessList)
--Putmsg("Collecting type declarations (and fixed points) for: ")
--SAL_Print_Tid(Tid)
--Putnl()
--Putmsg("Skipping (currently calculating it!\n")

  'rule' SAL_Collect_Type_Declaration(Tid, OrigContexts, InProcessList -> Decls, ModifiedContexts)

--Putmsg("Collecting type declarations (and fixed points) for: ")
--SAL_Print_Tid(Tid)
--Putnl()

         Tid'FPStatus -> FPStatus
         (|
               -- The fixed point was calculated before...
               eq(FPStatus, calculated)
               Tid'FixedPoint -> FP
               Tid'Declaration -> DC
--Putmsg("Fixed point already calculated\n")
               where(OrigContexts -> ModifiedContexts)
               -- The fixed point was already calculated and is inside
               -- the type id.
               where(FP -> Decls)
         ||
               Tid'Declaration -> DC
               ne(DC, nil)
--Putmsg("No fixed point, but declaration included in Tid\n")
--print(DC)
               -- The Tid contains the declaration.... no need for look up
               SAL_compute_fixed_point(DC, OrigContexts, InProcessList ->  Decls, ModifiedContexts)
               -- Storing the fixed point in the tid (optimization):
               Tid'FixedPoint <- Decls
               -- Setting the calculated flag:
               Tid'FPStatus <- calculated
         ||
               -- Collect the declaration for the type:
--Putmsg("Neither fixed point nor Decl in Tid\n")
               SAL_Extract_Type_Decl_from_Contexts(Tid, OrigContexts -> Decl,ModifiedContexts1)
               -- Calculate the fixed point:
               SAL_compute_fixed_point(Decl, ModifiedContexts1,InProcessList ->  Decls, ModifiedContexts)
               -- Storing the fixed point in the tid (optimization):
               Tid'FixedPoint <- Decls
               -- Storing the declaration in the tid (optimization):
               Tid'Declaration <- Decl
               -- Setting the calculated flag:
               Tid'FPStatus <- calculated
         |)

---------------------------------------------------------------------------

'action' SAL_Extract_Type_Decl_from_Contexts(SAL_type_id, SAL_CONTEXTS 
                                                 -> SAL_CONTEXT_CONSTANT, SAL_CONTEXTS)

  'rule' SAL_Extract_Type_Decl_from_Contexts(Tid,  
             list(context(Ident, CCid, Elems), Rest) -> Decl, Contexts):
         -- The Tid contains the Cid of the context of declaration:
         Tid'Cid -> OptCid
         where(OptCid -> cid(Cid))
         where(CCid -> cid(Cid1))
------
--Putmsg("Analizing in context: ")
--SAL_Print_Cid(Cid1)
--Putnl()
------
         (|
            eq(Cid, Cid1)
            -- This is the context where the valus is declared:
--Putmsg("Contexto encontrado\n")
            SAL_Print_Context(context(Ident, CCid, Elems))
            SAL_Extract_Type_Decl_from_Context_Elems(Tid,Elems -> Decl, ModifiedElems)
            where(context(Ident, CCid, ModifiedElems) -> ModifiedContext)
            -- remove from the static:
            Remove_Decl_from_Static(Cid1, Decl)
            where(SAL_CONTEXTS'list(ModifiedContext, Rest) ->  Contexts)
         ||
            -- This is not the context... process the next
            SAL_Extract_Type_Decl_from_Contexts(Tid, Rest -> Decl, Contexts1)
            where(SAL_CONTEXTS'list(context(Ident, CCid, Elems), Contexts1) -> Contexts)
         |)


  'rule' SAL_Extract_Type_Decl_from_Contexts(Tid, nil -> nil,nil)
         Putmsg("Warning... Type declaration not found for type: ")
         SAL_Print_Tid(Tid)
         Putnl()

'action' SAL_Extract_Type_Decl_from_Context_Elems(SAL_type_id, SAL_CONTEXT_CONSTANTS 
                -> SAL_CONTEXT_CONSTANT, SAL_CONTEXT_CONSTANTS)         

  'rule' SAL_Extract_Type_Decl_from_Context_Elems(Tid, 
                list(Decl,Rest) -> DeclOut, Decls)
         (|
            SAL_match_Tid_with_Decl(Tid,Decl)
            where(Rest -> Decls)
            where(Decl -> DeclOut)
         ||
            SAL_Extract_Type_Decl_from_Context_Elems(Tid, Rest -> DeclOut, Decls1)
            where(SAL_CONTEXT_CONSTANTS'list(Decl, Decls1) -> Decls)
         |)     

  'rule' SAL_Extract_Type_Decl_from_Context_Elems(Tid, list(Elem, Rest) ->
                DeclOut, Decls)
         SAL_Extract_Type_Decl_from_Context_Elems(Tid, Rest -> DeclOut, Decls1)
         where(SAL_CONTEXT_CONSTANTS'list(Elem, Decls1) -> Decls)

  'rule' SAL_Extract_Type_Decl_from_Context_Elems(_, nil -> nil, nil)


'condition' SAL_match_Tid_with_Decl(SAL_type_id, SAL_CONTEXT_CONSTANT)

  'rule' SAL_match_Tid_with_Decl(Tid, sal_type_decl(_,Tid1,_))
         eq(Tid, Tid1)


---------------------------------------------------------------------
-- SAL_Extract_Tid_from_<functor>
---------------------------------------------------------------------
-- This function extracts the Tid from the <functor> when
-- they refer to sets or maps operations. In particular, this
-- is used in order to collect dependencies that may arise
-- due to type definitions involving set/map OPS. As these 
-- operations do NOT have a value_id in the SAL translator, they
-- must be handled specially...
---------------------------------------------------------------------

'action' SAL_Extract_Tid_from_value_id(SAL_VALUE_ID -> SAL_TYPE_IDS)

  'rule' SAL_Extract_Tid_from_value_id(val_id(IdOp) -> Tids)
         SAL_Extract_Tid_from_ID_OP(IdOp -> Tids)

  'rule' SAL_Extract_Tid_from_value_id(record_val_id(_, IdOp,_) -> Tids)
         SAL_Extract_Tid_from_ID_OP(IdOp -> Tids)

-------------------------------------------------------------

'action' SAL_Extract_Tid_from_ID_OP(SAL_ID_OP -> SAL_TYPE_IDS)

  -- Collecting the type_ids for sets and maps (those are the only ones of interest)
  'rule' SAL_Extract_Tid_from_ID_OP(sal_set_op(_,_,Tid) -> list(Tid,nil))
  'rule' SAL_Extract_Tid_from_ID_OP(sal_map_op(_,_,_,Tid) -> list(Tid,nil))

  -- The rest of the ID_OPS are normal ops handled in a different way in the
  -- normal path...
  'rule' SAL_Extract_Tid_from_ID_OP(_ -> nil)
