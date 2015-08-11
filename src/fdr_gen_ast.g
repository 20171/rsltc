
'module' fdr_gen_ast

'use' ast print ext env objects values types pp cc cpp sml


      fdr_ast          -- fdr Abstract Syntax
      fdr_gen_code     -- Generates fdr code

     ltl_trans_delta  -- Translate from LTL to LTL delta

'export' 
	 Translate_Decls_To_Fdr_scripts
	 Is_empty_alphabet

     Init_Trans_LTL  			            -- LTL translation
     Translate_Value_expr_To_Fdr_value_expr	-- LTL translation


--------------------------------------------------------------
--------  Translate from LTL properties to LTL delta----------
--------------------------------------------------------------

'action' Init_Trans_LTL(DECLS,DECLS)

  'rule' Init_Trans_LTL(D1,D2)
         Init_LTL_file
         Translate_Decls_LTL(D1,D2)
         Close_LTL_file


'action' Translate_Decls_LTL(DECLS,DECLS)

  'rule' Translate_Decls_LTL(list(Decl,DeclsTail),Decls):
         Translate_Decl_LTL(Decl,Decls)
         Translate_Decls_LTL(DeclsTail,Decls)

  'rule' Translate_Decls_LTL(nil,Decls)


'action' Translate_Decl_LTL(DECL,DECLS)

  'rule' Translate_Decl_LTL(property_decl(_,Defs),Decls)
         Translate_LTL_Property_Defs(Defs,Decls)

   'rule'Translate_Decl_LTL(Decl,Decls)


'action' Translate_LTL_Property_Defs(PROPERTY_DECLS,DECLS)

  'rule' Translate_LTL_Property_Defs(list(H, T),Decls):
         where(H -> property_def(Pos, _, _,_))
         Get_current_properties(all -> Prop_env)
         Lookup_property(Pos, Prop_env -> PropId)

        -- Enable the use of LTL operators:
         Set_LTL_Wanted()
         PropId'Resolved_Prop -> r_prop_csp(Pos1, Id, Process_Id, Prop)

         -- Translate from LTL to LTL delta
         TransDeltaProperty(Prop,Process_Id,Decls)
      
	     Translate_LTL_Property_Defs(T,Decls)

	    -- Disable the use of LTL operators:
	     Clear_LTL_Wanted() 

  'rule' Translate_LTL_Property_Defs(L,Decls)

-------------------------------------------------------------



'action' Translate_Property_Defs_To_Fdr_scripts(PROPERTY_DECLS,DECLS)

  'rule' Translate_Property_Defs_To_Fdr_scripts(L,Decls)


'action' Translate_Decls_To_Fdr_scripts(DECLS ->FDR_SCRIPTS)

  'rule' Translate_Decls_To_Fdr_scripts(list(Decl,DeclsTail) -> list(Fdr_script,Fdr_scriptsTail)):
         Translate_Decl_To_Fdr_script(Decl -> Fdr_script)
         Translate_Decls_To_Fdr_scripts(DeclsTail ->Fdr_scriptsTail)

  'rule' Translate_Decls_To_Fdr_scripts(nil -> nil)


'action' Translate_Decl_To_Fdr_script(DECL -> FDR_SCRIPT)
         
         --------datatype and nametype
  'rule' Translate_Decl_To_Fdr_script(type_decl(_,Type_defs)->Fdr_script):
         Translate_Type_defs_To_Fdr_script(Type_defs -> Fdr_script)
  
         --------value,process and function-------------
  'rule' Translate_Decl_To_Fdr_script(value_decl(_,Value_defs)->Fdr_script):
         Translate_Value_defs_To_Fdr_script(Value_defs -> Fdr_script)

  'rule' Translate_Decl_To_Fdr_script(variable_decl(Pos,_) -> nil):
         Puterror(Pos)
         Putmsg("Variable declarations cannot be translated\n")

         -----------------channel-----------------------
  'rule' Translate_Decl_To_Fdr_script(channel_decl(_,Channel_defs)->Fdr_script)
         Translate_Channel_defs_To_Fdr_script(Channel_defs -> Fdr_script)

         --------------channel arrays-----------------------
  'rule' Translate_Decl_To_Fdr_script(object_decl(Pos,Object_defs) -> Fdr_script):
	 Translate_Object_defs_To_Fdr_script(Object_defs -> Fdr_script)

         --------value,process and function-------------
  'rule' Translate_Decl_To_Fdr_script(axiom_decl(_,Axiom_defs) ->Fdr_script):
         Translate_Axiom_defs_To_Fdr_script(Axiom_defs -> Fdr_script) 

  'rule' Translate_Decl_To_Fdr_script(test_case_decl(Pos,_) -> nil):
         Puterror(Pos)
         Putmsg("Test case declarations will be ignored\n")
      
  'rule' Translate_Decl_To_Fdr_script(trans_system_decl(Pos,_) -> nil):
         Puterror(Pos)
         Putmsg("Translate system declarations cannot be translated\n") 

  'rule' Translate_Decl_To_Fdr_script(property_decl(_,Defs) -> nil):
         Translate_Property_Defs_Fdr_scripts(Defs)

-------------------------------------------------------------------------

-- Here only type check, LTL translation is later
'action' Translate_Property_Defs_Fdr_scripts(PROPERTY_DECLS)


  'rule' Translate_Property_Defs_Fdr_scripts(list(H, T)):

         where(H -> property_def(Pos, _, _,_))
  	     Get_current_properties(all -> Prop_env)
	     Lookup_property(Pos, Prop_env -> PropId)
	     -- Enable the use of LTL operators:
	     Set_LTL_Wanted()

         Translate_Property_Defs_Fdr_scripts(T)

	     -- Disable the use of LTL operators:
	     Clear_LTL_Wanted() 

  'rule' Translate_Property_Defs_Fdr_scripts(L)





-------------------------------------------------------------------------------------------------
-------------------------------- TYPE_DEFS TO  FDR_SCRIPT ---------------------------------------
-------------------------------------------------------------------------------------------------

'action' Translate_Type_defs_To_Fdr_script(TYPE_DEFS -> FDR_SCRIPT)

  'rule' Translate_Type_defs_To_Fdr_script(list(Type_def,Type_defsTail) -> fdr_def(Fdr_def,Fdr_scriptTail)):
         Translate_Type_def_To_Fdr_def(Type_def -> Fdr_def)
         Translate_Type_defs_To_Fdr_script(Type_defsTail ->Fdr_scriptTail)

  'rule' Translate_Type_defs_To_Fdr_script(nil -> nil)


'action' Translate_Type_def_To_Fdr_def(TYPE_DEF ->FDR_DEF)

------------- abstract type -- not supported

  'rule' Translate_Type_def_To_Fdr_def(sort(Pos,_) ->nil):
         Puterror(Pos)
         Putmsg("abstract type definition cannot be translated\n") 

------------- abbrev to nametype

  'rule' Translate_Type_def_To_Fdr_def(abbrev(Pos,Ident,_) -> fdr_nametype_def(Fdr_ident,Fdr_value_expr)):
	 Lookup_type_id(Pos, Ident -> type_id(I))
	 I'Def -> abbreviation(Type_expr)
         where(Ident->Fdr_ident)
	 Translate_Type_expr_To_Fdr_value_expr(Type_expr ->Fdr_value_expr)

------------ variant to datatype

  'rule' Translate_Type_def_To_Fdr_def(variant(Pos,Ident,_)->fdr_datatype_def(Fdr_ident,Fdr_choices)):
	 where(Ident -> Fdr_ident)
	 Lookup_type_id(Pos, Ident -> type_id(I))
	 I'Type -> sort(variant(Variants))
	 Translate_Variants_To_Fdr_choices(Variants -> Fdr_choices)

------------ record to datatype

  'rule' Translate_Type_def_To_Fdr_def(record(Pos,Ident,_)->fdr_datatype_def(Fdr_ident,list(Fdr_choice,nil))):
	 where(Ident -> Fdr_ident)
	 Lookup_type_id(Pos, Ident -> type_id(I))
	 I'Type -> sort(record(Components))
        -----concat mk with  Ident to generate Fdr_ident--------
         C_id_to_string(Ident -> IdentString)
         Concatenate("mk_", IdentString -> IdentString2)
         string_to_id (IdentString2 ->Ident2 )
        --------------------------------------------------------

         Translate_Components_To_Fdr_pattern_exprs(Components,Ident2 ->Fdr_pattern_expr)
	 Translate_Components_To_Fdr_choice(Components,Ident2,Fdr_pattern_expr ->Fdr_choice)

------------- union  type -- not supported

  'rule' Translate_Type_def_To_Fdr_def(union(Pos,_,_) -> nil):
	 Puterror(Pos)
         Putmsg("union type definition cannot be translated\n") 

 
-------------------------------------------------------------------------------------------------
--------------------------------TYPE_EXPR to  FDR_VALUE_EXPR-------------------------------------
-------------------------------------------------------------------------------------------------
    
'action' Translate_Type_expr_To_Fdr_value_expr(TYPE_EXPR -> FDR_VALUE_EXPR)

  'rule' Translate_Type_expr_To_Fdr_value_expr(unit->fdr_Unit)

  'rule' Translate_Type_expr_To_Fdr_value_expr(int->fdr_Int)

  'rule' Translate_Type_expr_To_Fdr_value_expr(nat->Fdr_value_expr):
	 string_to_id ("0" ->Ident)
	 where(fdr_set_expr(fdr_o_ranged_set(Ident)) -> Fdr_value_expr)


  'rule' Translate_Type_expr_To_Fdr_value_expr(bool-> fdr_Bool)

  'rule' Translate_Type_expr_To_Fdr_value_expr(real-> nil):
         --Puterror(Pos)
         Putmsg("real type cannot be translated\n")

  'rule' Translate_Type_expr_To_Fdr_value_expr(text-> nil):
         --Puterror(Pos)
         Putmsg("text type cannot be translated\n")

  'rule' Translate_Type_expr_To_Fdr_value_expr(char-> nil):
         --Puterror(Pos)
         Putmsg("char type cannot be translated\n")

  'rule' Translate_Type_expr_To_Fdr_value_expr(time-> nil):
         --Puterror(Pos)
         Putmsg("time type cannot be translated\n")

  'rule' Translate_Type_expr_To_Fdr_value_expr(defined(I,_)->fdr_named_val(Fdr_ident)):
	 I'Ident -> Fdr_ident

  'rule' Translate_Type_expr_To_Fdr_value_expr(product(Product_type)-> fdr_tup_expr(Fdr_value_exprs)):
         Translate_Product_type_To_Fdr_value_exprs(Product_type -> Fdr_value_exprs)

-- special case {| i : T :- i isin s |} translates to s
  'rule' Translate_Type_expr_To_Fdr_value_expr(subtype(Typing,Restriction)->Fdr_value_expr):
  	 where(Restriction -> restriction(_, Value_expr))
  	 where(Value_expr -> infix_occ(_,Left,Op,nil,Right))
	 Id_of_isin_set -> I
	 eq(Op, I)
	 where(Typing -> single(_, Binding, _))
	 Matches_binding(Left, Binding)
	 Translate_Value_expr_To_Fdr_value_expr(Right -> Fdr_value_expr)

  'rule' Translate_Type_expr_To_Fdr_value_expr(subtype(Typing,Restriction)->fdr_set_expr(Set)):
  	 where(Typing -> single(_, Binding, _))
	 where(Binding -> single(_, Id_or_op))
	 Translate_Id_or_op_To_Ident(Id_or_op ->Ident)
	 Translate_Typing_To_Fdr_binding(Typing ->Fdr_binding)
         Translate_Restriction_To_Fdr_value_expr(Restriction ->Fdr_value_expr)
	 where(fdr_comp_set(fdr_named_val(Ident),
		list(Fdr_binding, nil),
		Fdr_value_expr) -> Set)

  'rule' Translate_Type_expr_To_Fdr_value_expr(fin_map(_,_)-> nil):
         --Puterror(Pos)
         Putmsg("map type cannot be translated\n")

  'rule' Translate_Type_expr_To_Fdr_value_expr(infin_map(_,_)-> nil):
         --Puterror(Pos)
         Putmsg("infinite map type cannot be translated\n")

  'rule' Translate_Type_expr_To_Fdr_value_expr(named_type(name(_,Id_or_op))->fdr_named_val(Fdr_ident)):
	 Translate_Id_or_op_To_Ident(Id_or_op ->Fdr_ident)

  'rule' Translate_Type_expr_To_Fdr_value_expr(Type_expr -> nil)
--print(Type_expr)
--Putnl()

--------------PRODUCT TO TUPLE ----------------------

'action' Translate_Product_type_To_Fdr_value_exprs(PRODUCT_TYPE -> FDR_VALUE_EXPRS)

  'rule' Translate_Product_type_To_Fdr_value_exprs(list(Type_expr,Product_typeTail)->list(Fdr_value_expr,Fdr_value_exprsTail)):
         Translate_Type_expr_To_Fdr_value_expr(Type_expr -> Fdr_value_expr)
         Translate_Product_type_To_Fdr_value_exprs(Product_typeTail -> Fdr_value_exprsTail)

  'rule' Translate_Product_type_To_Fdr_value_exprs(nil -> nil)

------------ SUBTYPE TO FDR_SET_EXPR----------------------------

'action' Translate_Restriction_To_Fdr_value_expr(RESTRICTION ->FDR_VALUE_EXPR)

--  'rule' Translate_Restriction_To_Fdr_value_expr(restriction(_,Value_expr)->fdr_set_expr(Fdr_set_value_expr)):
--         where(Value_expr ->infix_occ(_,_,Op,nil,ranged_set(_,Value_expr1,Value_expr2)))
--         Translate_Value_expr_To_Fdr_set_value_expr(Value_expr ->Fdr_set_value_expr)

  'rule' Translate_Restriction_To_Fdr_value_expr(restriction(_,Value_expr)->Fdr_value_expr):
         Translate_Value_expr_To_Fdr_value_expr(Value_expr ->Fdr_value_expr)

  'rule' Translate_Restriction_To_Fdr_value_expr(nil -> nil)


--'action' Translate_Value_expr_To_Fdr_set_value_expr(VALUE_EXPR ->FDR_SET_VALUE_EXPR)

--  'rule' Translate_Value_expr_To_Fdr_set_value_expr(infix_occ(_,_,Op,nil,ranged_set(_,Value_expr1,Value_expr2))
--                                                    -> fdr_ranged_set(Ident1,Ident2)):
--	 Id_of_isin_set -> I
--	 eq(Op, I)
--         Translate_Value_expr_To_Ident(Value_expr1 -> Ident1)
--         Translate_Value_expr_To_Ident(Value_expr2 -> Ident2)

 
'action' Translate_Value_expr_To_Ident(VALUE_EXPR -> IDENT)

  'rule' Translate_Value_expr_To_Ident(literal_expr(_,int(Ident))->Fdr_ident):
         where(Ident -> Fdr_ident)

  'rule' Translate_Value_expr_To_Ident(val_occ(_, I, _)->Fdr_ident):
	 I'Ident -> Id_or_Op
         Translate_Id_or_op_To_Ident(Id_or_Op ->Fdr_ident)

  'rule' Translate_Value_expr_To_Ident(named_val(_,name(_,Id_or_op))->Fdr_ident):
         Translate_Id_or_op_To_Ident(Id_or_op ->Fdr_ident)

  'rule' Translate_Value_expr_To_Ident(Value_expr->Fdr_ident):
	 string_to_id ("0" ->Fdr_ident )
	 Putmsg("Value_expr to Ident cannot be translate\n")
--print(Value_expr)
--Putnl()
---------------------VARIANTS ->FDR_CHOICES------------------------------------

'action' Translate_Variants_To_Fdr_choices(VARIANTS ->FDR_CHOICES)

  'rule' Translate_Variants_To_Fdr_choices(list(Variant,VariantsTail) -> list(Fdr_choice,Fdr_choicesTail)):
         Translate_Variant_To_Fdr_choice(Variant ->Fdr_choice) 
         Translate_Variants_To_Fdr_choices(VariantsTail ->Fdr_choicesTail)
 
  'rule' Translate_Variants_To_Fdr_choices(nil -> nil)


'action' Translate_Variant_To_Fdr_choice(VARIANT ->FDR_CHOICE)

  'rule' Translate_Variant_To_Fdr_choice(record(_,Constructor,Components)->fdr_complex_choice(Fdr_ident,Fdr_value_exprs,Fdr_script)):
         Translate_Constructor_To_Ident(Constructor -> Fdr_ident)
         Translate_Components_To_Fdr_pattern_exprs(Components,Fdr_ident ->Fdr_pattern_expr)
         Translate_Components_To_Fdr_value_exprs(Components,Fdr_pattern_expr -> Fdr_value_exprs,Fdr_script)


'action' Translate_Constructor_To_Ident(CONSTRUCTOR -> IDENT)

  'rule' Translate_Constructor_To_Ident(con_ref(I) -> Fdr_ident):
	 I'Ident -> Id_or_op
         Translate_Id_or_op_To_Ident(Id_or_op->Fdr_ident)


'action' Translate_Components_To_Fdr_value_exprs(COMPONENTS,FDR_PATTERN_EXPR -> FDR_VALUE_EXPRS,FDR_SCRIPT)

  'rule' Translate_Components_To_Fdr_value_exprs(list(Component,ComponentsTail),Fdr_pattern_expr -> 
                                                 list(Fdr_value_expr,Fdr_value_exprsTail), 
                                                 fdr_def(Fdr_def2,fdr_def(Fdr_def1,Fdr_scriptTail))):
         ------Translate the component with his destructor
         Translate_Component_To_Fdr_value_expr(Component,Fdr_pattern_expr -> Fdr_value_expr,Fdr_def1,Fdr_def2)
         Translate_Components_To_Fdr_value_exprs(ComponentsTail,Fdr_pattern_expr -> Fdr_value_exprsTail,Fdr_scriptTail)

  'rule' Translate_Components_To_Fdr_value_exprs(nil,Fdr_pattern_expr -> nil,nil)


'action' Translate_Component_To_Fdr_value_expr(COMPONENT,FDR_PATTERN_EXPR -> FDR_VALUE_EXPR,FDR_DEF,FDR_DEF)

  'rule' Translate_Component_To_Fdr_value_expr(component(_,Destructor,Type_expr,Reconstructor),Fdr_pattern_expr->
                                               Fdr_value_expr,Fdr_def1,Fdr_def2):
         Translate_Type_expr_To_Fdr_value_expr(Type_expr -> Fdr_value_expr)
         ------Fdr_def is the destructor function
	 Translate_Destructor_To_Fdr_def(Destructor,Fdr_pattern_expr -> Fdr_def1)
        ------Fdr_def is the reconstructor function
	 Translate_Reconstructor_To_Fdr_def(Destructor,Reconstructor,Fdr_pattern_expr -> Fdr_def2) 


--------------------- pattern to generate the destructor(auxiliar function)------------------------
-------------------------------------------------------------------------------------------

'action' Translate_Components_To_Fdr_pattern_exprs(COMPONENTS,IDENT ->FDR_PATTERN_EXPR)

  'rule' Translate_Components_To_Fdr_pattern_exprs(Components,Ident ->
                                                   fdr_dot_patt(list(fdr_singl_patt(fdr_named_val(Fdr_ident)),Fdr_pattern_exprsTail))):
         where(Ident ->Fdr_ident)
         Translate_Components_To_pe(Components ->Fdr_pattern_exprsTail)
	 

'action' Translate_Components_To_pe(COMPONENTS ->FDR_PATTERN_EXPRS)

  'rule' Translate_Components_To_pe(list(Component,ComponentsTail) ->list(Fdr_pattern_expr,Fdr_pattern_exprsTail)):
         Translate_Component_To_pe(Component ->Fdr_pattern_expr)
	 Translate_Components_To_pe(ComponentsTail ->Fdr_pattern_exprsTail)

  'rule' Translate_Components_To_pe(nil -> nil)


'action' Translate_Component_To_pe(COMPONENT ->FDR_PATTERN_EXPR)

  'rule' Translate_Component_To_pe(component(_,dest_ref(I),_,_) ->Fdr_pattern_expr):
	 I'Ident -> id_op(Ident)
        -----concat v with  Ident to generate Fdr_ident - used to generate the args of the destructor function--------
         C_id_to_string(Ident -> IdentString)
         Concatenate("v", IdentString -> IdentString2)
         string_to_id (IdentString2 ->Ident2 )
        --------------------------------------------------------
	 where(fdr_singl_patt(fdr_named_val(Ident2)) ->Fdr_pattern_expr)


--------------------- pattern to generate the constructor (mk_ fdr datatype------------------------
----------------------------------------------------------------------------------------------------
'action' Translate_Actual_function_parameters_To_Fdr_pattern_exprs(ACTUAL_FUNCTION_PARAMETERS ->FDR_PATTERN_EXPRS)

  'rule' Translate_Actual_function_parameters_To_Fdr_pattern_exprs(list(fun_arg(_,Value_exprs),nil) -> Fdr_pattern_exprs):
	 Translate_Value_exprs_To_Fdr_pattern_exprs(Value_exprs ->Fdr_pattern_exprs)

  'rule' Translate_Actual_function_parameters_To_Fdr_pattern_exprs(list(fun_arg(Pos,_),FAs) -> nil):
	 Puterror(Pos)
         Putmsg("Actual function parameters cannot be translated\n")

'action' Translate_Value_exprs_To_Fdr_pattern_exprs(VALUE_EXPRS ->FDR_PATTERN_EXPRS)

  'rule' Translate_Value_exprs_To_Fdr_pattern_exprs(list(Value_expr,Value_exprsTail) -> list(Fdr_pattern_expr,Fdr_pattern_exprsTail)):
         Translate_Value_expr_To_Fdr_pattern_expr(Value_expr ->Fdr_pattern_expr)
	 Translate_Value_exprs_To_Fdr_pattern_exprs(Value_exprsTail ->Fdr_pattern_exprsTail)

  'rule' Translate_Value_exprs_To_Fdr_pattern_exprs(nil -> nil)

'action' Translate_Value_expr_To_Fdr_pattern_expr(VALUE_EXPR ->FDR_PATTERN_EXPR)

  'rule' Translate_Value_expr_To_Fdr_pattern_expr(Value_expr -> fdr_singl_patt(Fdr_value_expr)):
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr ->Fdr_value_expr)

----------------------------------------------------------------------------
--------------------------- generate the destructor ------------------------

'action' Translate_Destructor_To_Fdr_def(DESTRUCTOR,FDR_PATTERN_EXPR -> FDR_DEF)

  'rule' Translate_Destructor_To_Fdr_def(dest_ref(I),Fdr_pattern_expr ->
                             fdr_fun_def(Fdr_ident,list(Fdr_pattern_expr,nil),Fdr_function)):
	 I'Ident -> id_op(Ident)
         Translate_Id_or_op_To_Ident(id_op(Ident)->Fdr_ident)
         Translate_Ident_To_Fdr_value_expr(Ident ->Fdr_function)


'action' Translate_Ident_To_Fdr_value_expr(IDENT ->FDR_VALUE_EXPR)

  'rule' Translate_Ident_To_Fdr_value_expr(Ident ->fdr_named_val(Fdr_ident)):
        -----concat v with  Ident to generate Fdr_ident--------
         C_id_to_string(Ident -> IdentString)
         Concatenate("v", IdentString -> IdentString2)
         string_to_id (IdentString2 ->Ident2 )
        --------------------------------------------------------
	 where(Ident2 ->Fdr_ident)

-----------------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------
--------------------------- generate the reconstructor ------------------------

'action' Translate_Reconstructor_To_Fdr_def(DESTRUCTOR,RECONSTRUCTOR,FDR_PATTERN_EXPR -> FDR_DEF)

  'rule' Translate_Reconstructor_To_Fdr_def(dest_ref(I),recon_ref(I2),Fdr_pattern_expr ->
                             fdr_fun_def2(Fdr_ident,Ident3,list(Fdr_pattern_expr,nil),Fdr_function)):
	 I'Ident -> id_op(Ident2)
         I2'Ident -> id_op(Ident)
         Translate_Id_or_op_To_Ident(id_op(Ident)->Fdr_ident)
         string_to_id ("nv" ->Ident3 )
	 Translate_Fdr_pattern_expr_To_Fdr_pattern_expr(Fdr_pattern_expr,Ident3,Ident2 -> Fdr_pattern_expr1)
	 where(fdr_patt_expr(Fdr_pattern_expr1)->Fdr_function)

  'rule' Translate_Reconstructor_To_Fdr_def(_,nil,_ ->nil)
--------------------- pattern to generate the destructor(auxiliar function)------------------------
-------------------------------------------------------------------------------------------

'action' Translate_Fdr_pattern_expr_To_Fdr_pattern_expr(FDR_PATTERN_EXPR,IDENT,IDENT ->FDR_PATTERN_EXPR)

  'rule' Translate_Fdr_pattern_expr_To_Fdr_pattern_expr(fdr_dot_patt(list(fdr_singl_patt(fdr_named_val(Fdr_ident)),Fdr_pattern_exprsTail)),Ident,Ident2 ->
                                                   fdr_dot_patt(list(fdr_singl_patt(fdr_named_val(Fdr_ident)),Fdr_pattern_exprsTail1))):
         Translate_patterns_to_patterns(Fdr_pattern_exprsTail,Ident,Ident2  ->Fdr_pattern_exprsTail1)
	 

'action' Translate_patterns_to_patterns(FDR_PATTERN_EXPRS,IDENT,IDENT ->FDR_PATTERN_EXPRS)

  'rule' Translate_patterns_to_patterns(list(Fdr_pattern_expr,Fdr_pattern_exprsTail),Ident,Ident2 ->
                                        list(Fdr_pattern_expr1,Fdr_pattern_exprsTail1)):
         Translate_pattern_to_pattern(Fdr_pattern_expr,Ident,Ident2 ->Fdr_pattern_expr1)
	 Translate_patterns_to_patterns(Fdr_pattern_exprsTail,Ident,Ident2 ->Fdr_pattern_exprsTail1)

  'rule' Translate_patterns_to_patterns(nil, Ident,Ident2-> nil)


'action' Translate_pattern_to_pattern(FDR_PATTERN_EXPR,IDENT,IDENT->FDR_PATTERN_EXPR)

  'rule' Translate_pattern_to_pattern(fdr_singl_patt(fdr_named_val(Fdr_ident)),Ident,Ident2 -> fdr_singl_patt(fdr_named_val(Fdr_ident1))):
	 
       
         C_id_to_string(Ident2 -> IdentString)
	 C_id_to_string(Fdr_ident -> IdentString3)
         Concatenate("v", IdentString -> IdentString2)
         (|Compare_string(IdentString2,IdentString3)
	   where(Ident ->Fdr_ident1)
         ||
           where(Fdr_ident ->Fdr_ident1)
         |)
-----------------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------------

------------------------------------------------------
----------- RECORD TO CHOICE -------------------------
------------------------------------------------------

        
'action' Translate_Components_To_Fdr_choice(COMPONENTS,IDENT,FDR_PATTERN_EXPR->FDR_CHOICE)

  'rule' Translate_Components_To_Fdr_choice(Components,Ident,Fdr_pattern_expr ->fdr_complex_choice(Fdr_ident,Fdr_value_exprs,Fdr_script)):

         where(Ident -> Fdr_ident)
         Translate_Components_To_Fdr_value_exprs(Components,Fdr_pattern_expr -> Fdr_value_exprs,Fdr_script)

'action' Translate_Id_or_op_To_Ident(ID_OR_OP->IDENT)

  'rule' Translate_Id_or_op_To_Ident(id_op(Ident)->Fdr_ident):
         where(Ident -> Fdr_ident) 

-------------------------------------------------------------------------------------------------
------------------------------------ CHANNEL_DEFS TO  FDR_SCRIPT --------------------------------
-------------------------------------------------------------------------------------------------

'action' Translate_Channel_defs_To_Fdr_script(CHANNEL_DEFS -> FDR_SCRIPT)

  'rule' Translate_Channel_defs_To_Fdr_script(list(Channel_def,Channel_defsTail)->fdr_def(Fdr_def,Fdr_scriptTail)):
	 Translate_Channel_def_To_Fdr_def(Channel_def -> Fdr_def)
	 Translate_Channel_defs_To_Fdr_script(Channel_defsTail -> Fdr_scriptTail)

  'rule' Translate_Channel_defs_To_Fdr_script(nil -> nil)


'action' Translate_Channel_def_To_Fdr_def(CHANNEL_DEF->FDR_DEF)

  'rule' Translate_Channel_def_To_Fdr_def(single(_,Ident,_)->fdr_channel_def(fdr_single_channel_id(Fdr_ident),Fdr_value_exprs)):
	 Get_current_channels(-> CHS)
	 Lookup_env_channel_id(Ident, CHS -> channel_id(I))
	 I'Type -> Type_expr
         where(Ident -> Fdr_ident) 
         Translate_Type_expr_To_Fdr_value_expr(Type_expr -> Fdr_value_expr)
         where(FDR_VALUE_EXPRS'list(Fdr_value_expr,nil) -> Fdr_value_exprs)

  'rule' Translate_Channel_def_To_Fdr_def(multiple(_,Idents,_)->fdr_channel_def(fdr_multiple_channel_id(Fdr_idents),Fdr_value_exprs)):
         where(Idents -> Fdr_idents)
	 where(Idents -> list(Ident, _))
	 Get_current_channels(-> CHS)
	 Lookup_env_channel_id(Ident, CHS -> channel_id(I))
	 I'Type -> Type_expr
         Translate_Type_expr_To_Fdr_value_expr(Type_expr -> Fdr_value_expr)
	 where(FDR_VALUE_EXPRS'list(Fdr_value_expr,nil) -> Fdr_value_exprs)


-------------------------------------------------------------------------------------------------
------------------------ OBJECT_DEFS TO  FDR_SCRIPT (channel arrays)-----------------------------
-------------------------------------------------------------------------------------------------

'action' Translate_Object_defs_To_Fdr_script(OBJECT_DEFS -> FDR_SCRIPT)

  'rule' Translate_Object_defs_To_Fdr_script(list(Object_def,Object_defsTail)->fdr_def(Fdr_def,Fdr_scriptTail)):
	 Translate_Object_def_To_Fdr_def(Object_def -> Fdr_def)
	 Translate_Object_defs_To_Fdr_script(Object_defsTail -> Fdr_scriptTail)

  'rule' Translate_Object_defs_To_Fdr_script(nil -> nil)

'action' Translate_Object_def_To_Fdr_def(OBJECT_DEF -> FDR_DEF)

  'rule' Translate_Object_def_To_Fdr_def(Object_def -> Fdr_def):
	 where(Object_def ->odef(Pos,Ident,Typings,Class))
	 (|where(Class -> basic(list(channel_decl(Pos2,Channel_defs),nil)))
           (|where(Channel_defs ->list(Channel_def,nil))
             Translate_Object_channel_To_Fdr_def(Object_def -> Fdr_def)
           ||
	     Puterror(Pos2)
             Putmsg("Channels definition cannot be translated\n")
             where(FDR_DEF'nil ->Fdr_def)
           |)
         ||      
           Puterror(Pos)
           Putmsg("Object declarations cannot be translated\n")
           where(FDR_DEF'nil ->Fdr_def)
         |)


'action' Translate_Object_channel_To_Fdr_def(OBJECT_DEF -> FDR_DEF)

  'rule' Translate_Object_channel_To_Fdr_def(Object_def -> Fdr_def):
	 where(Object_def ->odef(Pos,Ident,Typings,Class))
	 Resolve_value_typings(Typings -> Typings1)
	 Translate_Typings_To_Fdr_value_exprs(Typings1 ->Fdr_value_exprs)
         (|eq(Fdr_value_exprs,nil)
	   where(FDR_DEF'nil ->Fdr_def)
         ||
	   where(Class -> basic(list(channel_decl(Pos2,list(Channel_def,nil)),nil)))
	   (|where(Channel_def ->single(Pos3,Ident1,Type_expr))
             Resolve_type(Type_expr ->Type_expr1)
             Translate_Type_expr_To_Fdr_value_expr(Type_expr1 -> Fdr_value_expr)
             Conc_Fdr_value_exprs(Fdr_value_exprs,list(Fdr_value_expr,nil)->Fdr_value_exprs1)
	     Translate_OIdent_To_OFdr_ident(Ident,Ident1 ->Ident2)
	     where(fdr_channel_def(fdr_single_channel_id(Ident2),Fdr_value_exprs1) ->Fdr_def)
           ||
	     where(Channel_def ->multiple(Pos3,Idents,Type_expr))
	     Resolve_type(Type_expr ->Type_expr1)
             Translate_Type_expr_To_Fdr_value_expr(Type_expr1 -> Fdr_value_expr)
             Conc_Fdr_value_exprs(Fdr_value_exprs,list(Fdr_value_expr,nil)->Fdr_value_exprs1)
	     Translate_OIdents_To_OFdr_idents(Ident,Idents ->Idents2)
	     where(fdr_channel_def(fdr_multiple_channel_id(Idents2),Fdr_value_exprs1) ->Fdr_def)
           |)
         |)

'action' Translate_Typings_To_Fdr_value_exprs(TYPINGS ->FDR_VALUE_EXPRS)

  'rule' Translate_Typings_To_Fdr_value_exprs(nil -> nil)

  'rule' Translate_Typings_To_Fdr_value_exprs(list(Typing,TypingsTail)->Fdr_value_exprs):
	 
	 Translate_Typing_To_Fdr_value_expr(Typing ->Fdr_value_expr)
         (|ne(Fdr_value_expr,nil)
	   Translate_Typings_To_Fdr_value_exprs(TypingsTail->Fdr_value_exprsTail)
           (|ne(TypingsTail,nil)
             ne(Fdr_value_exprsTail,nil)	 
             where(FDR_VALUE_EXPRS'list(Fdr_value_expr,Fdr_value_exprsTail)-> Fdr_value_exprs)
           ||ne(TypingsTail,nil)
             eq(Fdr_value_exprsTail,nil)
             where(FDR_VALUE_EXPRS'nil-> Fdr_value_exprs)
           ||eq(TypingsTail,nil)
             where(FDR_VALUE_EXPRS'list(Fdr_value_expr,Fdr_value_exprsTail)-> Fdr_value_exprs)
           |)
         ||
           where(FDR_VALUE_EXPRS'nil-> Fdr_value_exprs)
         |)


'action' Translate_Typing_To_Fdr_value_expr(TYPING ->FDR_VALUE_EXPR)

  'rule' Translate_Typing_To_Fdr_value_expr(single(Pos,_,Type_expr) ->Fdr_value_expr):
         (|eq(Type_expr,unit)
	   Puterror(Pos)
           Putmsg("Unit typing cannot be translated\n")
           where(FDR_VALUE_EXPR'nil -> Fdr_value_expr)
         ||
	   Translate_Type_expr_To_Fdr_value_expr(Type_expr ->Fdr_value_expr)
         |)

  'rule' Translate_Typing_To_Fdr_value_expr(multiple(Pos,_,_) ->nil):
	 Puterror(Pos)
         Putmsg("Multiple typing cannot be translated\n")


'action' Conc_Fdr_value_exprs(FDR_VALUE_EXPRS,FDR_VALUE_EXPRS ->FDR_VALUE_EXPRS)

  'rule' Conc_Fdr_value_exprs(list(Fdr_value_expr,Fdr_value_exprs ), Fdr_value_exprs1 -> list(Fdr_value_expr, Fdr_value_exprs2)):
	 Conc_Fdr_value_exprs(Fdr_value_exprs, Fdr_value_exprs1 -> Fdr_value_exprs2)

  'rule' Conc_Fdr_value_exprs(nil, Fdr_value_exprs ->Fdr_value_exprs)


'action' Translate_OIdents_To_OFdr_idents(IDENT,IDENTS ->IDENTS)

  'rule' Translate_OIdents_To_OFdr_idents(Ident,list(Ident1,IdentsTail) ->list(OIdent1,OIdentsTail)):
	 Translate_OIdent_To_OFdr_ident(Ident,Ident1 ->OIdent1)
	 Translate_OIdents_To_OFdr_idents(Ident,IdentsTail ->OIdentsTail)

  'rule' Translate_OIdents_To_OFdr_idents(Ident,nil -> nil)


'action' Translate_OIdent_To_OFdr_ident(IDENT,IDENT ->IDENT)

  'rule' Translate_OIdent_To_OFdr_ident(Ident,Ident1 ->Ident2)
	 -----concat channel array name--------
         C_id_to_string(Ident -> IdentString)
	 C_id_to_string(Ident1 -> IdentString1)
	 Concatenate3(IdentString,"_", IdentString1 -> IdentString2)
         string_to_id (IdentString2 ->Ident2 )
         --------------------------------------------------------

-------------------------------------------------------------------------------------------------
------------------------------------ VALUE_DEFS TO FDR_SCRIPT ---------------------------------------
-------------------------------------------------------------------------------------------------

'action' Translate_Value_defs_To_Fdr_script(VALUE_DEFS -> FDR_SCRIPT)

  'rule' Translate_Value_defs_To_Fdr_script(list(Value_def,Value_defsTail)->fdr_def(Fdr_def,Fdr_scriptTail)):
	 Translate_Value_def_To_Fdr_def(Value_def -> Fdr_def)
	 Translate_Value_defs_To_Fdr_script(Value_defsTail->Fdr_scriptTail)

  'rule' Translate_Value_defs_To_Fdr_script(nil -> nil)


'action' Translate_Value_def_To_Fdr_def(VALUE_DEF ->FDR_DEF)

---------Typing is ignored---------------------------------------------
  'rule' Translate_Value_def_To_Fdr_def(typing(_,_)-> nil)
        
-------- explicit value like iTask = 5 ----------------------------------------
  'rule' Translate_Value_def_To_Fdr_def(exp_val(_,Typing,_)->fdr_value_def(Ident,Fdr_value_expr)):
         Translate_Typing_To_Pos_Result_Access(Typing ->Pos,_,_)
         Translate_Typing_To_Ident(Typing ->Ident)
	 Get_current_top_values(-> VE)
         Select_id_by_pos(Pos, VE -> value_id(I))
	 I'Def -> expl_val(Value_expr, _)
         Translate_Value_expr_To_Fdr_value_expr(Value_expr->Fdr_value_expr)

-------- explicit function and process ----------------------------------------
  'rule' Translate_Value_def_To_Fdr_def(exp_fun(_,Typing,_,_,_,_,_) ->Fdr_def)

         Translate_Typing_To_Pos_Result_Access(Typing ->Pos,Type_expr_resul,Access_descs)               
	 Get_current_top_values(-> VE)
         Select_id_by_pos(Pos, VE -> value_id(I))
	 I'Def -> expl_fun(Formal_function_parameters, Value_expr, _, _, _, _)
         I'Type -> Type_expr
	 I'Ident -> Id_or_op
         Translate_Id_or_op_To_Ident(Id_or_op->Fdr_ident)
         Translate_Formal_function_parameters_To_Fdr_pattern_exprs(Formal_function_parameters -> Fdr_pattern_exprs)
         (|
           eq(Type_expr_resul,unit)          
           ----------- alphabet --------------

           -----concat Alph_ with  Fdr_ident to generate Ident--------
           C_id_to_string(Fdr_ident -> IdentString)
           Concatenate("Alph_in_", IdentString -> IdentString_in)
           string_to_id(IdentString_in ->Ident_in)
	   Concatenate("Alph_out_", IdentString -> IdentString_out)
           string_to_id(IdentString_out ->Ident_out)
           --------------------------------------------------------
	   Generate_alphabet(Fdr_ident,Formal_function_parameters,Access_descs,Value_expr ->Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag)
	   where(fdr_alpha_def(Ident_in,Fdr_pattern_exprs,Fdr_alpha_expr_in)->Fdr_alphabet_in)
	   where(fdr_alpha_def(Ident_out,Fdr_pattern_exprs,Fdr_alpha_expr_out)->Fdr_alphabet_out)
	   I'Type_alpha <-Flag
           ----------- process -----------        
           Translate_Value_expr_To_Fdr_process_combination(Value_expr ->Fdr_process_combination)
           where(fdr_process_def(Fdr_ident,Fdr_pattern_exprs,Fdr_process_combination,Fdr_alphabet_in,Fdr_alphabet_out) ->Fdr_def)
         ||
           --------- function -------------     
	   Translate_Value_expr_To_Fdr_value_expr(Value_expr ->Fdr_value_expr)
           where(fdr_fun_def(Fdr_ident,Fdr_pattern_exprs,Fdr_value_expr)->Fdr_def)         
         |)
         
-------- implicit value not supported------------------------------------
  'rule' Translate_Value_def_To_Fdr_def(imp_val(Pos,_,_)-> nil)
         Puterror(Pos)
         Putmsg("Implicit value cannot be translated\n") 

-------- implicit function not supported -----------------------------------
  'rule' Translate_Value_def_To_Fdr_def(imp_fun(Pos,_,_,_,_)-> nil)
         Puterror(Pos)
         Putmsg("Implicit function cannot be translated\n")


-------------------- for value -------------------------------------------

-------------------- typing ---------------------------
'action' Translate_Typing_To_Ident(TYPING ->IDENT)

  'rule' Translate_Typing_To_Ident(single(_,single(_,Id_or_op),_)->Fdr_ident):
         Translate_Id_or_op_To_Ident(Id_or_op->Fdr_ident)

  'rule' Translate_Typing_To_Ident(multiple(_,list(single(_,Id_or_op),_),_) ->Fdr_ident):
	 Translate_Id_or_op_To_Ident(Id_or_op->Fdr_ident)
  
 
'action' Translate_Typing_To_Pos_Result_Access(TYPING ->POS,TYPE_EXPR,ACCESS_DESCS)

  'rule' Translate_Typing_To_Pos_Result_Access(single(_,single(Pos,_),TE)->Pos,Type_expr,Access_descs):
	 where(TE ->function(_,_,result(Access_descs,Type_expr)))

  'rule' Translate_Typing_To_Pos_Result_Access(single(P,single(Pos,_),TE)->Pos,none,nil):

  'rule' Translate_Typing_To_Pos_Result_Access(multiple(P,list(single(Pos,_),_),TE)->Pos,Type_expr,Access_descs):  
	 where(TE ->function(_,_,result(Access_descs,Type_expr)))

  'rule' Translate_Typing_To_Pos_Result_Access(multiple(_,list(single(Pos,_),_),TE)->Pos,none,nil):  


--------------------- value expresion --------------

'action' Translate_Value_exprs_To_Fdr_value_exprs(VALUE_EXPRS -> FDR_VALUE_EXPRS)

  'rule' Translate_Value_exprs_To_Fdr_value_exprs(list(Value_expr,Value_exprsTail) -> list (Fdr_value_expr,Fdr_value_exprsTail)):
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr->Fdr_value_expr)
	 Translate_Value_exprs_To_Fdr_value_exprs(Value_exprsTail -> Fdr_value_exprsTail)

  'rule' Translate_Value_exprs_To_Fdr_value_exprs(nil -> nil)


'action' Translate_Value_expr_To_Fdr_value_expr(VALUE_EXPR->FDR_VALUE_EXPR)

  'rule' Translate_Value_expr_To_Fdr_value_expr(literal_expr(_,Value_literal)->fdr_literal_expr(Fdr_value_literal)):
	 Translate_Value_literal_To_Fdr_value_literal(Value_literal ->Fdr_value_literal)

  'rule' Translate_Value_expr_To_Fdr_value_expr(val_occ(_, I, _)->fdr_named_val(Ident)):
	 I'Ident -> Id_or_op
	 Translate_Id_or_op_To_Ident(Id_or_op ->Ident)

  'rule' Translate_Value_expr_To_Fdr_value_expr(named_val(_,name(_,Id_or_op))->fdr_named_val(Ident)):
	 Translate_Id_or_op_To_Ident(Id_or_op ->Ident)

  'rule' Translate_Value_expr_To_Fdr_value_expr(ranged_set(_,Value_expr1,Value_expr2)->fdr_set_expr(fdr_ranged_set(Ident1,Ident2))):
	 Translate_Value_expr_To_Ident(Value_expr1 -> Ident1)
         Translate_Value_expr_To_Ident(Value_expr2 -> Ident2)

  'rule' Translate_Value_expr_To_Fdr_value_expr(enum_set(_,Value_exprs)->fdr_set_expr(fdr_enum_set(Fdr_value_exprs))):
	 Translate_Value_exprs_To_Fdr_value_exprs(Value_exprs -> Fdr_value_exprs)

  'rule' Translate_Value_expr_To_Fdr_value_expr(comp_set(_,Value_expr,set_limit	(_,Typings,Restriction))->
                                                fdr_set_expr(fdr_comp_set(Fdr_value_expr,Fdr_bindings,Fdr_value_expr_cond))):
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr->Fdr_value_expr)					
	 Translate_Typings_To_Fdr_bindings(Typings -> Fdr_bindings)
         Translate_Restriction_Fdr_value_expr_cond(Restriction ->Fdr_value_expr_cond)

  'rule' Translate_Value_expr_To_Fdr_value_expr(ranged_list(_,Value_expr1,Value_expr2)->fdr_seq_expr(fdr_ranged_seq(Ident1,Ident2))):
	 Translate_Value_expr_To_Ident(Value_expr1 -> Ident1)
         Translate_Value_expr_To_Ident(Value_expr2 -> Ident2)

  'rule' Translate_Value_expr_To_Fdr_value_expr(enum_list(_,Value_exprs)->fdr_seq_expr(fdr_enum_seq(Fdr_value_exprs))):
	 Translate_Value_exprs_To_Fdr_value_exprs(Value_exprs -> Fdr_value_exprs)

  'rule' Translate_Value_expr_To_Fdr_value_expr(comp_list(_,Value_expr,list_limit(_,Binding,Value_expr1,Restriction))->
                                                fdr_set_expr(fdr_comp_set(Fdr_value_expr,Fdr_bindings,Fdr_value_expr_cond))):
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr->Fdr_value_expr)					
	 Translate_Binding_To_Fdr_binding(Binding,Value_expr1 -> Fdr_binding)
	 where(FDR_BINDINGS'list(Fdr_binding,nil) -> Fdr_bindings)
         Translate_Restriction_Fdr_value_expr_cond(Restriction ->Fdr_value_expr_cond)

  'rule' Translate_Value_expr_To_Fdr_value_expr(application(Pos,Value_expr,Actual_function_parameters)->
                                                Fdr_value_expr):	

	 where(Value_expr -> val_occ(_, I, _))
 	 Translate_Value_expr_To_Ident(Value_expr -> Fdr_ident)
         C_id_to_string(Fdr_ident -> IdentString)
         (|Compare_substring(IdentString,"mk_",3)  
	   Translate_Actual_function_parameters_To_Fdr_pattern_exprs(Actual_function_parameters ->Fdr_pattern_exprs)
           where(fdr_patt_expr(fdr_dot_patt(list(fdr_id_patt(Fdr_ident),Fdr_pattern_exprs))) ->Fdr_value_expr)
         ||
           Translate_Actual_function_parameters_To_Fdr_value_exprs(Actual_function_parameters ->Fdr_value_exprs)
           where(fdr_function(Fdr_ident,Fdr_value_exprs) ->Fdr_value_expr)
         |)


  'rule' Translate_Value_expr_To_Fdr_value_expr(disamb(_, E, _) ->Fdr_value_expr):
	 Translate_Value_expr_To_Fdr_value_expr(E ->Fdr_value_expr)

  'rule' Translate_Value_expr_To_Fdr_value_expr(bracket	(_,Value_expr)-> fdr_bracket(Fdr_value_expr)):
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr -> Fdr_value_expr)

  'rule' Translate_Value_expr_To_Fdr_value_expr(infix_occ(_,Value_expr1,Op,_,Value_expr2)->
						fdr_fun_appl2(Fdr_fun,Fdr_value_expr1,Fdr_value_expr2)):
         Op'Ident ->op_op(Op2)
 	 (|eq(Op2,hd)||eq(Op2,tl)||eq(Op2,card)||eq(Op2,union)||eq(Op2,inter)||eq(Op2,rem)||eq(Op2,isin)|)
         Id_of_rem_int -> I
	 ne(Op, I)     
         Translate_Value_expr_To_Fdr_value_expr(Value_expr1 -> Fdr_value_expr1)
	 Translate_Op_To_Fdr_fun(Op2->Fdr_fun)
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr2 -> Fdr_value_expr2)

  'rule' Translate_Value_expr_To_Fdr_value_expr(infix_occ(_,Value_expr1,Op,_,Value_expr2)->
                                                fdr_infi_expr(Fdr_value_expr1,Fdr_op,Fdr_value_expr2)):
         Op'Ident ->op_op(Op2)   
         Translate_Value_expr_To_Fdr_value_expr(Value_expr1 -> Fdr_value_expr1)     
	 Translate_Op_To_Fdr_op(Op2 -> Fdr_op)
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr2 -> Fdr_value_expr2)
	
  'rule' Translate_Value_expr_To_Fdr_value_expr(ax_infix(_,Value_expr1,Connective,Value_expr2,_)-> 
						fdr_infi_expr(Fdr_value_expr1,Fdr_op,Fdr_value_expr2)):
         Translate_Value_expr_To_Fdr_value_expr(Value_expr1 -> Fdr_value_expr1)
	 Translate_Connective_To_Fdr_op(Connective ->Fdr_op)
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr2 -> Fdr_value_expr2)

  'rule' Translate_Value_expr_To_Fdr_value_expr(prefix_occ(_,Op,_,Value_expr) -> fdr_fun_appl1(Fdr_fun,Fdr_value_expr)):
	 Op'Ident ->op_op(Op2)
	 Translate_Op_To_Fdr_fun(Op2->Fdr_fun)
         Translate_Value_expr_To_Fdr_value_expr(Value_expr -> Fdr_value_expr) 

  'rule' Translate_Value_expr_To_Fdr_value_expr(product(_,Value_exprs) -> fdr_tup_expr(Fdr_value_exprs))
	 Translate_Value_exprs_To_Fdr_value_exprs(Value_exprs ->Fdr_value_exprs)

  'rule' Translate_Value_expr_To_Fdr_value_expr(let_expr(_,Let_defs,Value_expr) -> fdr_let_expr(Fdr_let_defs,Fdr_value_expr)):
	 Translate_Let_defs_To_Fdr_let_defs(Let_defs -> Fdr_let_defs)
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr -> Fdr_value_expr)

  'rule' Translate_Value_expr_To_Fdr_value_expr(if_expr(P1,If,Then,Rg,Elsifs,Else) -> Fdr):
  	 where(Elsifs -> list(elsif(P2,If1,Then1,_), Elsifs1))
	 Translate_Value_expr_To_Fdr_value_expr(
	   if_expr(P1,If,Then,Rg,nil,else(P2,if_expr(P2,If1,Then1,Rg,Elsifs1,Else)))
			-> Fdr)

  'rule' Translate_Value_expr_To_Fdr_value_expr(if_expr(P,If,Then,Rg,Elsifs,nil) -> Fdr):
  	 Translate_Value_expr_To_Fdr_value_expr(if_expr(P,If,Then,Rg,Elsifs,else(P,skip(P))) -> Fdr)

  'rule' Translate_Value_expr_To_Fdr_value_expr(if_expr(_,If,Then,_,nil,else(_,Value_expr)) -> 
                                                fdr_if_expr(If_value_expr,Then_value_expr,Else_value_expr)):
	 Translate_Value_expr_To_Fdr_value_expr(If -> If_value_expr)
	 Translate_Value_expr_To_Fdr_value_expr(Then ->Then_value_expr)
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr ->Else_value_expr)

  'rule' Translate_Value_expr_To_Fdr_value_expr(case_expr(Pos,Value_expr1,Pos1,Case) -> Fdr_function):
         where(case_expr(Pos,Value_expr1,Pos1,Case) -> Case_expr)  
         Rewrite_Case_expr_To_LetIf_expr(Case_expr -> If_value_expr)
--Putnl
--Print_expr(If_value_expr)
--Putnl
--Putnl
         Translate_Value_expr_To_Fdr_value_expr(If_value_expr ->Fdr_function)

  'rule' Translate_Value_expr_To_Fdr_value_expr(quantified(_,_,_,restriction(_,Value_expr)) -> Fdr_value_expr):
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr -> Fdr_value_expr)




 ---- LTL translation --

  'rule' Translate_Value_expr_To_Fdr_value_expr(ax_prefix(P1,C1,E1) -> fdr_ax_prefix(P2,C2,E2)):
         where(P1->P2)
         where(C1->C2)
         where(E1->E2)

  'rule' Translate_Value_expr_To_Fdr_value_expr(infix_occ(P1,L1,OP1,Q1,R1)->fdr_infix_occ(P2,L2,OP2,Q2,R2) )
         where(P1->P2)
         where(L1->L2)
         where(OP1->OP2)
         where(Q1->Q2)
         where(R1->R2)

  'rule' Translate_Value_expr_To_Fdr_value_expr(ax_infix(POS1,VL1,C1,VR1,PRE1)->fdr_ax_infix(POS2,VL2,C2,VR2,PRE2) )
         where(POS1->POS2)
         where(VL1->VL2)
         where(C1->C2)
         where(VR1->VR2)
         where(PRE1->PRE2)
                                                

  'rule' Translate_Value_expr_To_Fdr_value_expr(chan_occ(P1,ID1,Q1) -> fdr_chan_occ(Id_CH)):
	     ID1'Ident -> Id_CH

-------------------------



  'rule' Translate_Value_expr_To_Fdr_value_expr(Value_expr -> nil):
	 Putmsg("value expression cannot be translated\n")
print(Value_expr)
Putnl()


'action' Translate_Value_literal_To_Fdr_value_literal(VALUE_LITERAL->FDR_VALUE_LITERAL)

  'rule' Translate_Value_literal_To_Fdr_value_literal(bool_true->fdr_bool_true)

  'rule' Translate_Value_literal_To_Fdr_value_literal(bool_false->fdr_bool_false)

  'rule' Translate_Value_literal_To_Fdr_value_literal(int(Ident)->fdr_int_lit(Fdr_ident)):
	 where(Ident ->Fdr_ident)


 ---- LTL translation ---

  'rule' Translate_Value_literal_To_Fdr_value_literal(delta->fdr_delta)

------------------------



--------------- bindings ------------------------

'action' Translate_Binding_To_Idents(BINDING -> IDENTS)

  'rule' Translate_Binding_To_Idents(product(_,list(Binding,BindingsTail)) -> list(Fdr_ident,Fdr_identsTail)):
	 Translate_Binding_To_Ident(Binding -> Fdr_ident)
	 Translate_Bindings_To_Idents(BindingsTail -> Fdr_identsTail)

'action' Translate_Bindings_To_Idents(BINDINGS -> IDENTS)

  'rule' Translate_Bindings_To_Idents(list(Binding,BindingsTail) -> list(Fdr_ident,Fdr_identsTail)):
	 Translate_Binding_To_Ident(Binding -> Fdr_ident)
	 Translate_Bindings_To_Idents(BindingsTail -> Fdr_identsTail)

  'rule' Translate_Bindings_To_Idents(nil -> nil)


'action' Translate_Binding_To_Ident(BINDING -> IDENT)

  'rule' Translate_Binding_To_Ident(single(_,Id_or_op) -> Fdr_ident):
	 Translate_Id_or_op_To_Ident(Id_or_op ->Fdr_ident)

  'rule' Translate_Binding_To_Ident(product(Pos,_) ->Fdr_ident):
	 string_to_id ("error_" ->Fdr_ident)
	 Puterror(Pos)
         Putmsg("Product Bindings  cannot be translated\n")


'action' Translate_Bindings_To_Fdr_pattern_exprs(BINDINGS -> FDR_PATTERN_EXPRS)

  'rule' Translate_Bindings_To_Fdr_pattern_exprs(list(Binding,BindingsTail)
                                                 -> list(Fdr_pattern_expr,Fdr_pattern_exprsTail)):
	 Translate_Binding_To_Fdr_pattern_expr(Binding  -> Fdr_pattern_expr)
	 Translate_Bindings_To_Fdr_pattern_exprs(BindingsTail -> Fdr_pattern_exprsTail)
				 
  'rule' Translate_Bindings_To_Fdr_pattern_exprs(nil -> nil)


'action' Translate_Binding_To_Fdr_pattern_expr(BINDING  -> FDR_PATTERN_EXPR)

  'rule' Translate_Binding_To_Fdr_pattern_expr(single(_,Id_or_op)->fdr_id_patt(Fdr_ident)):
         Translate_Id_or_op_To_Ident(Id_or_op->Fdr_ident)

  'rule' Translate_Binding_To_Fdr_pattern_expr(product(Pos,_) ->fdr_underscore_patt):
	 Puterror(Pos)
         Putmsg("Product Bindings  cannot be translated\n")


'action' Translate_Binding_To_Fdr_binding(BINDING,VALUE_EXPR -> FDR_BINDING)

  'rule' Translate_Binding_To_Fdr_binding(Binding,Value_expr -> fdr_binding(Fdr_ident,Fdr_value_expr)):
	 Translate_Binding_To_Ident(Binding -> Fdr_ident)
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr-> Fdr_value_expr)


'action' Translate_Typings_To_Fdr_bindings(TYPINGS -> FDR_BINDINGS)

  'rule' Translate_Typings_To_Fdr_bindings(list(Typing,TypingsTail) -> list(Fdr_binding,Fdr_bindingsTail)):
	 Translate_Typing_To_Fdr_binding(Typing ->Fdr_binding)
	 Translate_Typings_To_Fdr_bindings(TypingsTail ->Fdr_bindingsTail)

  'rule' Translate_Typings_To_Fdr_bindings(nil -> nil)


'action' Translate_Typing_To_Fdr_binding(TYPING ->FDR_BINDING)

  'rule' Translate_Typing_To_Fdr_binding(single(_,Binding,Type_expr) -> Fdr_binding):
	 Translate_Type_Binding_To_Fdr_binding(Binding,Type_expr ->Fdr_binding)


'action' Translate_Type_Binding_To_Fdr_binding(BINDING,TYPE_EXPR ->FDR_BINDING)

  'rule' Translate_Type_Binding_To_Fdr_binding(single(_,Id_or_op),Type_expr ->fdr_binding (Fdr_ident,Fdr_value_expr)):
	 Translate_Id_or_op_To_Ident(Id_or_op ->Fdr_ident)
	 Translate_Type_expr_To_Fdr_value_expr(Type_expr ->Fdr_value_expr)

  'rule' Translate_Type_Binding_To_Fdr_binding(product(Pos,_),Type_expr ->Fdr_binding):
	 Puterror(Pos)
         Putmsg("Binding cannot be translated\n")
	 where(FDR_BINDING'none -> Fdr_binding)



----------------------------------------------------------------------------
'action' Translate_Actual_function_parameters_To_Fdr_value_exprs(ACTUAL_FUNCTION_PARAMETERS ->FDR_VALUE_EXPRS)

  'rule' Translate_Actual_function_parameters_To_Fdr_value_exprs(list(fun_arg(_,Value_exprs),nil) -> Fdr_value_exprs):
	 Translate_Value_exprs_To_Fdr_value_exprs(Value_exprs -> Fdr_value_exprs)

  'rule' Translate_Actual_function_parameters_To_Fdr_value_exprs(list(fun_arg(Pos,_),FAs) -> nil):
	 Puterror(Pos)
         Putmsg("Actual function parameters cannot be translated\n")


'action' Translate_Restriction_Fdr_value_expr_cond(RESTRICTION ->FDR_VALUE_EXPR)

  'rule' Translate_Restriction_Fdr_value_expr_cond(restriction(_,Value_expr) -> Fdr_value_expr):
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr->Fdr_value_expr)
         
  'rule' Translate_Restriction_Fdr_value_expr_cond(nil -> nil)


'action' Translate_Formal_function_parameters_To_Fdr_idents(FORMAL_FUNCTION_PARAMETERS -> IDENTS)

  'rule' Translate_Formal_function_parameters_To_Fdr_idents(list(form_parm(_,Bindings),nil) -> Fdr_idents):
	 Translate_Bindings_To_Idents(Bindings -> Fdr_idents)

  'rule' Translate_Formal_function_parameters_To_Fdr_idents(list(form_parm(Pos,Bindings),FPs)->nil):
         Puterror(Pos)
         Putmsg("Formal function parameters cannot be translated\n")


------------------- operators and connectives ----------------------------

'action' Translate_Op_To_Fdr_op(OP -> FDR_OP)

  'rule' Translate_Op_To_Fdr_op(eq -> fdr_equal)

  'rule' Translate_Op_To_Fdr_op(neq -> fdr_diffent)

  'rule' Translate_Op_To_Fdr_op(eqeq -> fdr_equal_equal)

  'rule' Translate_Op_To_Fdr_op(gt -> fdr_gt)

  'rule' Translate_Op_To_Fdr_op(lt -> fdr_lt)

  'rule' Translate_Op_To_Fdr_op(ge -> fdr_ge)

  'rule' Translate_Op_To_Fdr_op(le -> fdr_le)

  'rule' Translate_Op_To_Fdr_op(mult -> fdr_product)

  'rule' Translate_Op_To_Fdr_op(div -> fdr_quotient)

  'rule' Translate_Op_To_Fdr_op(plus -> fdr_plus )

  'rule' Translate_Op_To_Fdr_op(minus -> fdr_minus)

  'rule' Translate_Op_To_Fdr_op(rem -> fdr_remainder)

  'rule' Translate_Op_To_Fdr_op(len -> fdr_len)

  'rule' Translate_Op_To_Fdr_op(caret ->fdr_catenation)



'action' Translate_Op_To_Fdr_fun(OP->FDR_FUN)

  'rule' Translate_Op_To_Fdr_fun(hd ->fdr_head)

  'rule' Translate_Op_To_Fdr_fun(tl ->fdr_tail)

  'rule' Translate_Op_To_Fdr_fun(card ->fdr_card)

  'rule' Translate_Op_To_Fdr_fun(union ->fdr_union)

  'rule' Translate_Op_To_Fdr_fun(inter ->fdr_inter)

  'rule' Translate_Op_To_Fdr_fun(rem ->fdr_diff)

  'rule' Translate_Op_To_Fdr_fun(len ->fdr_length)

  'rule' Translate_Op_To_Fdr_fun(isin -> fdr_member)

 ---- LTL translation --

  'rule' Translate_Op_To_Fdr_fun(R ->fdr_R)

  'rule' Translate_Op_To_Fdr_fun(U -> fdr_U)

  'rule' Translate_Op_To_Fdr_fun(W -> fdr_W)

  'rule' Translate_Op_To_Fdr_fun(G ->fdr_G)

  'rule' Translate_Op_To_Fdr_fun(F -> fdr_F)

  'rule' Translate_Op_To_Fdr_fun(X -> fdr_X)

------------------------
	
'action' Translate_Connective_To_Fdr_op(CONNECTIVE ->FDR_OP)

  'rule' Translate_Connective_To_Fdr_op(or ->fdr_or)

  'rule' Translate_Connective_To_Fdr_op(and ->fdr_and)

  'rule' Translate_Connective_To_Fdr_op(not ->fdr_not)

  'rule' Translate_Connective_To_Fdr_op(implies -> fdr_implies)


--------------------------------------------------------------------------------------------------------------
-----------------------------------------for an alphabet------------------------------------------------------
--------------------------------------------------------------------------------------------------------------
/*'action' Generate_alphabet(IDENT,FORMAL_FUNCTION_PARAMETERS,ACCESS_DESCS,VALUE_EXPR ->FDR_ALPHA_EXPR,FDR_ALPHA_EXPR,FDR_FLAG_PROCESS_OPE)

  'rule' Generate_alphabet(Fdr_ident,Formal_function_parameters,Access_descs,Value_expr 
                           ->Fdr_alpha_expr_in,Fdr_alpha_expr_out,Fdr_flag_process_ope):
         Translate_Value_expr_To_alpha_expr(Value_expr,Fdr_ident,fdr_Access -> 
                                            Fdr_alpha_expr_in1,Fdr_alpha_expr_out1,Fdr_flag_process_ope) 
         (|eq(Fdr_flag_process_ope,fdr_No_Access)
	   Simplify_alphabet(Fdr_alpha_expr_in1, nil ->Fdr_alpha_expr_in)
	   Simplify_alphabet(Fdr_alpha_expr_out1, nil->Fdr_alpha_expr_out)           
         ||Generate_alphabet_From_Accesses(Access_descs,Formal_function_parameters ->Fdr_alpha_expr_in2,Fdr_alpha_expr_out2)
           Simplify_alphabet(Fdr_alpha_expr_in2, nil->Fdr_alpha_expr_in)
	   Simplify_alphabet(Fdr_alpha_expr_out2, nil->Fdr_alpha_expr_out)
         |)

*/
'action' Generate_alphabet(IDENT,FORMAL_FUNCTION_PARAMETERS,ACCESS_DESCS,VALUE_EXPR ->FDR_ALPHA_EXPR,FDR_ALPHA_EXPR,FDR_FLAG_PROCESS_OPE)

  'rule' Generate_alphabet(Fdr_ident,Formal_function_parameters,Access_descs,Value_expr 
                           ->Fdr_alpha_expr_in,Fdr_alpha_expr_out,Fdr_flag_process_ope):
	 Collect_application(Value_expr,nil -> VEs1)
	 Collect_parallel(Value_expr,nil -> VEs2)	 		            
         (|eq(VEs2,nil)
	   Is_application_equal(VEs1,Fdr_ident,Formal_function_parameters)
	   Generate_alphabet_From_Accesses(Access_descs,Formal_function_parameters ->Fdr_alpha_expr_in2,Fdr_alpha_expr_out2)
           Simplify_alphabet(Fdr_alpha_expr_in2, nil->Fdr_alpha_expr_in)
	   Simplify_alphabet(Fdr_alpha_expr_out2, nil->Fdr_alpha_expr_out)
	   where(FDR_FLAG_PROCESS_OPE'fdr_Access-> Fdr_flag_process_ope)	            
         ||
	   Translate_Value_expr_To_alpha_expr(Value_expr,Fdr_ident,fdr_Access -> 
                                            Fdr_alpha_expr_in1,Fdr_alpha_expr_out1,Fdr_flag_process_ope) 
	   Simplify_alphabet(Fdr_alpha_expr_in1, nil ->Fdr_alpha_expr_in)
	   Simplify_alphabet(Fdr_alpha_expr_out1, nil->Fdr_alpha_expr_out)  
         |)

--------------------------------Decide how to get the alphabet ----------------------------------
'sweep' Collect_parallel(ANY, VALUE_EXPRS ->VALUE_EXPRS )

  'rule' Collect_parallel(VALUE_EXPR'stmt_infix(P,VE1,parallel,VE2), VEs -> VEs1):
	 
	 where(VALUE_EXPRS'list(stmt_infix(P,VE1,parallel,VE2),VEs ) ->VEs1)

  'rule' Collect_parallel(VALUE_EXPR'comprehended(P,parallel,VE,SL), VEs -> VEs1):
	 
	 where(VALUE_EXPRS'list(comprehended(P,parallel,VE,SL),VEs ) ->VEs1)


'sweep' Collect_application(ANY, VALUE_EXPRS ->VALUE_EXPRS)

  'rule' Collect_application(VALUE_EXPR'application(P,F,A), VEs -> VEs1):
	 
	   where(VALUE_EXPRS'list(application(P,F,A),VEs ) ->VEs1)
	

-- succeeds if all applications in the first parameter are either
-- 1.  Applications of a function different from the second parameter, or
-- 2.  Applications of the second parameter with actual aguments matching the formal ones
'condition' Is_application_equal(VALUE_EXPRS,IDENT,FORMAL_FUNCTION_PARAMETERS)

  'rule' Is_application_equal(list(application(_,VE,list(fun_arg(_,Value_exprs),nil)),VES),ID, list(form_parm(P,Bindings),nil)):
	 where(VE -> val_occ(_, I, _))	 
	 I'Ident -> Id_or_Op
         Translate_Id_or_op_To_Ident(Id_or_Op ->Fdr_ident)
	 (|
	   ne(ID,Fdr_ident)
	 ||
	   Matches_product_binding(Value_exprs, Bindings)
         |)
	 where(FORMAL_FUNCTION_PARAMETERS'list(form_parm(P,Bindings),nil) -> X)
	 Is_application_equal(VES,ID,X)

  'rule' Is_application_equal(nil,ID, list(form_parm(_,Bindings),nil))
-------------------------------------------------------------------------------------------------
--------------------Generate_alphabet_From_Accesse-----------------------------------------------

'action' Generate_alphabet_From_Accesses(ACCESS_DESCS,FORMAL_FUNCTION_PARAMETERS ->FDR_ALPHA_EXPR,FDR_ALPHA_EXPR)

  'rule' Generate_alphabet_From_Accesses(Access_descs,Formal_function_parameters ->Fdr_alpha_expr_in,Fdr_alpha_expr_out):
         Translate_Access_descs_To_Accesses(Access_descs,nil,nil ->Accesses_in,Accesses_out)
         Flat_Accesses(Accesses_in ->Accesses_in_flat)
	 Split_Accesses(Accesses_in_flat,nil,nil -> Accesses_in_split1,Accesses_in_split2)
	 Flat_Accesses(Accesses_out ->Accesses_out_flat)
	 Split_Accesses(Accesses_out_flat,nil,nil -> Accesses_out_split1,Accesses_out_split2)
	 Translate_NAccesses_To_Fdr_alpha_expr(Accesses_in_split1 -> Fdr_alpha_expr_in1)
         Translate_NAccesses_To_Fdr_alpha_expr(Accesses_out_split1 -> Fdr_alpha_expr_out1)
	 Translate_CAccesses_To_Fdr_alpha_expr(Accesses_in_split2,Formal_function_parameters  -> Fdr_alpha_expr_in2)
         Translate_CAccesses_To_Fdr_alpha_expr(Accesses_out_split2,Formal_function_parameters  -> Fdr_alpha_expr_out2)
	 Simplify_alphabet(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_in1,Fdr_alpha_expr_in2), nil ->Fdr_alpha_expr_in)
	 Simplify_alphabet(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_out1,Fdr_alpha_expr_out2), nil ->Fdr_alpha_expr_out)

'action' Translate_Access_descs_To_Accesses(ACCESS_DESCS,ACCESSES,ACCESSES ->ACCESSES,ACCESSES)

  'rule' Translate_Access_descs_To_Accesses(list(access(Access_mode,Accesses),Access_descsTail),Accesses_in,Accesses_out -> 
                                            Accesses_total_in,Accesses_total_out):
         (| (|eq(Access_mode,read) ||eq(Access_mode,write)|)
            Putmsg("access to variables  cannot be translated\n")
	    Translate_Access_descs_To_Accesses(Access_descsTail,Accesses_in,Accesses_out -> Accesses_total_in,Accesses_total_out)
         ||
            (|eq(Access_mode,in) 
              Conc_Accesses(Accesses,Accesses_in -> Accesses_partial_in)
              Translate_Access_descs_To_Accesses(Access_descsTail,Accesses_partial_in,Accesses_out -> 
                                                 Accesses_total_in,Accesses_total_out) 
            ||eq(Access_mode,out)
              Conc_Accesses(Accesses,Accesses_out -> Accesses_partial_out)
              Translate_Access_descs_To_Accesses(Access_descsTail,Accesses_in,Accesses_partial_out -> 
                                                 Accesses_total_in,Accesses_total_out) 
            |)
         |)

  'rule' Translate_Access_descs_To_Accesses(nil,Accesses_in,Accesses_out -> Accesses_in,Accesses_out) 


------  enumerated access -----------------------

'action' Flat_Accesses(ACCESSES -> ACCESSES)

  'rule' Flat_Accesses(nil ->nil)

  'rule' Flat_Accesses(list(enumerated_access(_,Accesses),Accesses1) -> Accesses2):
	 Conc_Accesses(Accesses,Accesses1 ->Accesses3)
         Flat_Accesses(Accesses3 -> Accesses2)

  'rule' Flat_Accesses(list(Access,Accesses) -> list(Access,Accesses1)):
	 Flat_Accesses(Accesses ->Accesses1)


'action' Conc_Accesses(ACCESSES,ACCESSES -> ACCESSES)

  'rule' Conc_Accesses(list(Access, Accesses), Accesses1 -> list(Access, Accesses2)):
	 Conc_Accesses(Accesses, Accesses1 -> Accesses2)

  'rule' Conc_Accesses(nil, Accesses -> Accesses):
--------------------------------------------------------------------

------split in comprehended access and enumerated access-----------------

'action' Split_Accesses(ACCESSES,ACCESSES,ACCESSES-> ACCESSES,ACCESSES)

  'rule' Split_Accesses(list(Access,Accesses),Accesses1,Accesses2->Accesses3,Accesses4):
	 (|where(Access ->completed_access(Pos,D))
	   Puterror(Pos)
           Putmsg("any access cannot be translated\n")
           where(Accesses1 ->Accesses_3)
	   where(Accesses2 ->Accesses_4)
	   Split_Accesses(Accesses,Accesses_3,Accesses_4 ->Accesses3,Accesses4)
         ||
           where(Access ->named_access(P,name(P2,Id_or_op)))
           where(ACCESSES'list(Access,Accesses1) ->Accesses_3)
	   where(Accesses2 ->Accesses_4)
	   Split_Accesses(Accesses,Accesses_3,Accesses_4 ->Accesses3,Accesses4)
         ||
	   where(Access ->comprehended_access(P,A,SL))
           where(ACCESSES'list(Access,Accesses2) ->Accesses_4)
	   where(Accesses1 ->Accesses_3)
	   Split_Accesses(Accesses,Accesses_3,Accesses_4 ->Accesses3,Accesses4)
	 ||
	   where(Access -> channel(_, _, _))
           where(ACCESSES'list(Access,Accesses1) ->Accesses_3)
	   where(Accesses2 ->Accesses_4)
	   Split_Accesses(Accesses,Accesses_3,Accesses_4 ->Accesses3,Accesses4)
	 ||
           Putmsg("Access cannot be translated\n")
           where(Accesses1 ->Accesses_3)
	   where(Accesses2 ->Accesses_4)
	   Split_Accesses(Accesses,Accesses_3,Accesses_4 ->Accesses3,Accesses4)
--print(Access)
--Putnl()
         |)

  'rule' Split_Accesses(nil,Accesses1,Accesses2->Accesses1,Accesses2):


---- enumerated access--------

'action' Translate_NAccesses_To_Fdr_alpha_expr(ACCESSES ->FDR_ALPHA_EXPR)

  'rule' Translate_NAccesses_To_Fdr_alpha_expr(list(Access,Accesses) -> fdr_enum_alpha(list(Fdr_enum_alpha_expr,Fdr_enum_alpha_exprs))):
         Translate_NAccess_To_Fdr_enum_alpha_expr(Access ->Fdr_enum_alpha_expr)
	 Translate_NAccesses_To_Fdr_alpha_expr(Accesses -> Fdr_alpha_expr)
	 where(Fdr_alpha_expr ->fdr_enum_alpha(Fdr_enum_alpha_exprs))

  'rule' Translate_NAccesses_To_Fdr_alpha_expr(nil ->fdr_enum_alpha(nil))


'action' Translate_NAccess_To_Fdr_enum_alpha_expr(ACCESS ->FDR_ENUM_ALPHA_EXPR)

  'rule' Translate_NAccess_To_Fdr_enum_alpha_expr(channel(_,I,nil) -> fdr_enum_alpha_expr (Fdr_ident,nil)):
	  I'Ident -> Fdr_ident

  'rule' Translate_NAccess_To_Fdr_enum_alpha_expr(channel(_,I2,qualification(Obj)) -> fdr_enum_alpha_expr (Fdr_ident,Fdr_value_exprs)):
	 I2'Ident -> Fdr_ident2
	 where(Obj -> obj_appl(obj_occ(_,I1),Value_exprs))
	 I1'Ident -> Fdr_ident1
	 Translate_OIdent_To_OFdr_ident(Fdr_ident1,Fdr_ident2 ->Fdr_ident)
	 Translate_Value_exprs_To_Fdr_value_exprs(Value_exprs ->Fdr_value_exprs)

  'rule' Translate_NAccess_To_Fdr_enum_alpha_expr(named_access(_,name(_,Id_or_op)) -> fdr_enum_alpha_expr (Fdr_ident,nil)):
	 Translate_Id_or_op_To_Ident(Id_or_op ->Fdr_ident)

  'rule' Translate_NAccess_To_Fdr_enum_alpha_expr(named_access(_,qual_name(_,obj_appl(obj_name(name(_,Id_or_op1)),Value_exprs),Id_or_op2))
                                                  -> fdr_enum_alpha_expr(Fdr_ident,Fdr_value_exprs)):
	 Translate_Id_or_op_To_Ident(Id_or_op1 ->Fdr_ident1)
	 Translate_Id_or_op_To_Ident(Id_or_op2 ->Fdr_ident2)
	 Translate_OIdent_To_OFdr_ident(Fdr_ident1,Fdr_ident2 ->Fdr_ident)
	 Translate_Value_exprs_To_Fdr_value_exprs(Value_exprs ->Fdr_value_exprs)

  'rule' Translate_NAccess_To_Fdr_enum_alpha_expr(completed_access(Pos,_) -> fdr_enum_alpha_expr (Fdr_ident,nil)):
	 Puterror(Pos)
         Putmsg("any access cannot be translated\n")
	 string_to_id ("error_" ->Fdr_ident)

  'rule' Translate_NAccess_To_Fdr_enum_alpha_expr(Access-> fdr_enum_alpha_expr (Fdr_ident,nil)):
	 string_to_id ("error_" ->Fdr_ident)

------ comprehended access ----------------------

'action' Translate_CAccesses_To_Fdr_alpha_expr(ACCESSES,FORMAL_FUNCTION_PARAMETERS ->FDR_ALPHA_EXPR)

  'rule' Translate_CAccesses_To_Fdr_alpha_expr(list(Access,Accesses),Formal_function_parameters ->Fdr_alpha_expr):
	 Translate_CAccess_To_Fdr_alpha_expr(Access,Formal_function_parameters ->Fdr_alpha_expr1)
	 Translate_CAccesses_To_Fdr_alpha_expr(Accesses,Formal_function_parameters ->Fdr_alpha_expr2)
	 where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr1,Fdr_alpha_expr2) ->Fdr_alpha_expr)

  'rule' Translate_CAccesses_To_Fdr_alpha_expr(nil,Formal_function_parameters ->Fdr_alpha_expr):
	 where(FDR_ALPHA_EXPR'fdr_empty ->Fdr_alpha_expr)


'action' Translate_CAccess_To_Fdr_alpha_expr(ACCESS,FORMAL_FUNCTION_PARAMETERS ->FDR_ALPHA_EXPR)

  'rule' Translate_CAccess_To_Fdr_alpha_expr(comprehended_access(_,enumerated_access(_,Accesses),set_limit(_,Typings,Restriction)),
                                             list(form_parm(Pos,Bindings),FPs) -> Fdr_alpha_expr_comp):
	 (|eq(FPs,nil)
	   Translate_NAccesses_To_Fdr_alpha_expr(Accesses ->Fdr_alpha_expr)
	   Compare_paramenters_To_Fdr_bindings(Typings,Bindings,nil -> Fdr_bindings)
	   (|eq(Fdr_bindings,nil)
	     where(Fdr_alpha_expr ->Fdr_alpha_expr_comp)
           ||
	     Translate_Restriction_To_Fdr_value_expr(Restriction ->Fdr_value_expr)
	     where(fdr_comp_alpha(Fdr_alpha_expr,Fdr_bindings,Fdr_value_expr) -> Fdr_alpha_expr_comp)
           |)
         ||
	   Puterror(Pos)
           Putmsg("Comprehended access cannot be translated\n")
	   where(FDR_ALPHA_EXPR'fdr_empty ->Fdr_alpha_expr_comp)
         |)

  'rule' Translate_CAccess_To_Fdr_alpha_expr(comprehended_access(_,Access,set_limit(_,Typings,Restriction)),
                                             list(form_parm(Pos,Bindings),FPs) -> Fdr_alpha_expr_comp):
	 (|eq(FPs,nil)
	   Translate_NAccess_To_Fdr_enum_alpha_expr(Access ->Fdr_enum_alpha_expr)
	   Compare_paramenters_To_Fdr_bindings(Typings,Bindings,nil -> Fdr_bindings)
	   (|eq(Fdr_bindings,nil)
	     where(fdr_enum_alpha(list(Fdr_enum_alpha_expr,nil)) ->Fdr_alpha_expr_comp)
           ||
	     Translate_Restriction_To_Fdr_value_expr(Restriction ->Fdr_value_expr)
	     where(fdr_comp_alpha(fdr_enum_alpha(list(Fdr_enum_alpha_expr,nil)),Fdr_bindings,Fdr_value_expr) -> Fdr_alpha_expr_comp)
           |)
         ||
	   Puterror(Pos)
           Putmsg("Comprehended access cannot be translated\n")
	   where(FDR_ALPHA_EXPR'fdr_empty ->Fdr_alpha_expr_comp)
         |)

--------------------- to know wich bindings have to be included in the comprehended alphabet----------------
------------------------------------------------------------------------------------------------------------
'action'Compare_paramenters_To_Fdr_bindings(TYPINGS,BINDINGS,FDR_BINDINGS -> FDR_BINDINGS)

 'rule' Compare_paramenters_To_Fdr_bindings(list(Typing,TypingsTail),nil,Binds -> Fdr_bindings):
	Translate_Typing_To_Fdr_binding(Typing ->Fdr_binding)
	Compare_paramenters_To_Fdr_bindings(TypingsTail,nil,list(Fdr_binding,Binds) -> Fdr_bindings)

  'rule' Compare_paramenters_To_Fdr_bindings(list(Typing,TypingsTail),Bindings,Binds -> Fdr_bindings):
	 Compare_paramenter_To_Fdr_binding(Typing,Bindings -> Fdr_binding)
	 (|eq(Fdr_binding, none)
	   Compare_paramenters_To_Fdr_bindings(TypingsTail,Bindings,Binds -> Fdr_bindings)
	 ||
	   Compare_paramenters_To_Fdr_bindings(TypingsTail,Bindings,list(Fdr_binding,Binds) -> Fdr_bindings)
         |)
     
  'rule' Compare_paramenters_To_Fdr_bindings(nil,_,Binds -> Binds)


'action' Compare_paramenter_To_Fdr_binding(TYPING,BINDINGS -> FDR_BINDING)

  'rule' Compare_paramenter_To_Fdr_binding(Typing,list(single(_,Id),BindingsTail) ->Fdr_binding):
	 (|where(Typing -> single(_,single(_,Id1),Type_expr))
	   (|eq(Id1,Id)
	     where(FDR_BINDING'none -> Fdr_binding) 
	   ||
	     Compare_paramenter_To_Fdr_binding(Typing,BindingsTail ->Fdr_binding)
           |)
         ||
	   (|where(Typing -> single(_,product(Pos,_),Type_expr)) || where(Typing -> multiple(Pos,Bind,Type_expr))|)
	   Puterror(Pos)
           Putmsg("Typing cannot be translated\n")
	   where(FDR_BINDING'none -> Fdr_binding)
         |) 

  'rule' Compare_paramenter_To_Fdr_binding(Typing,nil ->Fdr_binding):
	 where(Typing -> single(_,Binding1,Type_expr))
         Translate_Type_Binding_To_Fdr_binding(Binding1,Type_expr ->Fdr_binding) 

  'rule' Compare_paramenter_To_Fdr_binding(Typing,list(product(Pos,_),BindingsTail) ->Fdr_binding):
	 Puterror(Pos)
         Putmsg("Binding cannot be translated\n")
	 where(FDR_BINDING'none -> Fdr_binding)

---------------------------------------------------------------------------------------           
---------------------------------------------------------------------------------------
-------------------------Translate_Value_expr_To_alpha_expr----------------------------
---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------

'action' Translate_Value_expr_To_alpha_expr(VALUE_EXPR,IDENT,FDR_FLAG_PROCESS_OPE -> FDR_ALPHA_EXPR,FDR_ALPHA_EXPR,FDR_FLAG_PROCESS_OPE)

  'rule' Translate_Value_expr_To_alpha_expr(bracket(_,Value_expr),Ident,Flag->Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1):
	 Translate_Value_expr_To_alpha_expr(Value_expr,Ident,Flag->Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1)

  'rule' Translate_Value_expr_To_alpha_expr(chaos(_),Ident,Flag->fdr_empty,fdr_empty,Flag)

  'rule' Translate_Value_expr_To_alpha_expr(skip(_),Ident,Flag->fdr_empty,fdr_empty,Flag)

  'rule' Translate_Value_expr_To_alpha_expr(stop(_),Ident,Flag->fdr_empty,fdr_empty,Flag)

  'rule' Translate_Value_expr_To_alpha_expr(application(_,Value_expr,Actual_function_parameters),Ident,Flag ->
					   Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1):
	 where(Value_expr -> val_occ(_, I, _))	 
	 I'Ident -> Id_or_Op
         Translate_Id_or_op_To_Ident(Id_or_Op ->Fdr_ident)
         (|ne(Ident,Fdr_ident)
           -----concat Alph_ with  Fdr_ident to generate Ident--------
           C_id_to_string(Fdr_ident -> IdentString)
           Concatenate("Alph_in_", IdentString -> IdentString_in)
           string_to_id(IdentString_in ->Ident_in)
	   Concatenate("Alph_out_", IdentString -> IdentString_out)
           string_to_id(IdentString_out ->Ident_out)
           -----------------------------------------------------------
           Translate_Actual_function_parameters_To_Fdr_value_exprs(Actual_function_parameters -> Fdr_value_exprs)
	   I'Def -> expl_fun(Formal_function_parameters, Def_expr, _, _, _, _)
	   I'Type -> fun(_, _, result(_,_,_,In_acc, Out_acc))
	   where(ACCESS_DESCS'list(access(in,In_acc),
			list(access(out,Out_acc),nil)) -> Access_descs)
	   Generate_alphabet(Fdr_ident,Formal_function_parameters,Access_descs,Def_expr ->Alpha_in,Alpha_out,_)
	   I'Type_alpha ->Flag1
           where(fdr_named_alpha(Ident_in,Fdr_value_exprs,Alpha_in)-> Fdr_alpha_expr_in)
           where(fdr_named_alpha(Ident_out,Fdr_value_exprs,Alpha_out)->Fdr_alpha_expr_out)
         ||
           where(FDR_ALPHA_EXPR'fdr_empty-> Fdr_alpha_expr_in)
           where(FDR_ALPHA_EXPR'fdr_empty->Fdr_alpha_expr_out)
	   where(Flag ->Flag1)
         |) 	

  'rule' Translate_Value_expr_To_alpha_expr(stmt_infix(Pos,Value_expr1,sequence,Value_expr2),Ident,Flag -> 
                                            Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1):
         where(Value_expr2 -> bracket(_,stmt_infix(P,V1,Op,V2)))
         where(stmt_infix(P,V1,Op,V2) ->Value_expr3)
	 Translate_Value_expr_To_alpha_expr(Value_expr3,Ident,Flag -> Fdr_alpha_expr_in_Partial2,Fdr_alpha_expr_out_Partial2,Flag1)
         (|where(Value_expr1->input_occ(PI,I,Q))
	   Translate_Value_expr_To_Fdr_enum_alpha(Value_expr1 -> fdr_enum_alpha(list(Fdr_enum_alpha_expr,nil)))
           where(fdr_enum_alpha(list(Fdr_enum_alpha_expr,nil)) ->Fdr_alpha_expr_in_Partial1)
           where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_in_Partial1,Fdr_alpha_expr_in_Partial2) ->Fdr_alpha_expr_in)
           where(Fdr_alpha_expr_out_Partial2 ->Fdr_alpha_expr_out)
         ||where(Value_expr1->output_occ(PO,I,Q,VE))
           Translate_Value_expr_To_Fdr_enum_alpha(Value_expr1 -> fdr_enum_alpha(list(Fdr_enum_alpha_expr,nil)))
           where(fdr_enum_alpha(list(Fdr_enum_alpha_expr,nil)) ->Fdr_alpha_expr_out_Partial1)
	   where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_out_Partial1,Fdr_alpha_expr_out_Partial2) ->Fdr_alpha_expr_out)
	   where(Fdr_alpha_expr_in_Partial2 ->Fdr_alpha_expr_in)
         ||
	   Puterror(Pos)
           Putmsg("Alphabet expression cannot be translated\n")
	   where(FDR_ALPHA_EXPR'fdr_empty ->Fdr_alpha_expr_in)
	   where(FDR_ALPHA_EXPR'fdr_empty ->Fdr_alpha_expr_out)
         |)			


  'rule' Translate_Value_expr_To_alpha_expr(stmt_infix(Pos,Value_expr1,sequence,Value_expr2),Ident,Flag ->
                                            Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1):
         Translate_Value_expr_To_alpha_expr(Value_expr2 ,Ident,Flag-> Fdr_alpha_expr_in_Partial2,Fdr_alpha_expr_out_Partial2,Flag1)
         (|where(Value_expr1->input_occ(P,I,Q))
	   Translate_Value_expr_To_Fdr_enum_alpha(Value_expr1 -> fdr_enum_alpha(list(Fdr_enum_alpha_expr,nil)))
           where(fdr_enum_alpha(list(Fdr_enum_alpha_expr,nil)) ->Fdr_alpha_expr_in_Partial1)
           where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_in_Partial1,Fdr_alpha_expr_in_Partial2) ->Fdr_alpha_expr_in)
           where(Fdr_alpha_expr_out_Partial2 ->Fdr_alpha_expr_out)
         ||where(Value_expr1->output_occ(P,I,Q,VE))
           Translate_Value_expr_To_Fdr_enum_alpha(Value_expr1 -> fdr_enum_alpha(list(Fdr_enum_alpha_expr,nil)))
           where(fdr_enum_alpha(list(Fdr_enum_alpha_expr,nil)) ->Fdr_alpha_expr_out_Partial1)
	   where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_out_Partial1,Fdr_alpha_expr_out_Partial2) ->Fdr_alpha_expr_out)
	   where(Fdr_alpha_expr_in_Partial2 ->Fdr_alpha_expr_in)
	 ||
	   Puterror(Pos)
           Putmsg("Alphabet expression cannot be translated\n")
	   where(FDR_ALPHA_EXPR'fdr_empty ->Fdr_alpha_expr_in)
	   where(FDR_ALPHA_EXPR'fdr_empty ->Fdr_alpha_expr_out)
         |)	

  'rule' Translate_Value_expr_To_alpha_expr(let_expr(Pos,list(explicit(Pos2,binding(Pos3,single(Pos4,Id_or_op)),Value_expr1),
                                                nil),Value_expr2),Ident,Flag->
                                            Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1):	 				    
         (|where(Value_expr1 ->input_occ(P,I,Q))
	   Translate_Value_expr_To_Fdr_enum_alpha(Value_expr1 -> fdr_enum_alpha(list(Fdr_enum_alpha_expr,nil)))
	   where(fdr_enum_alpha(list(Fdr_enum_alpha_expr,nil)) ->Fdr_alpha_expr_in_Partial1)
           Translate_Value_expr_To_alpha_expr(Value_expr2 ,Ident,Flag-> Fdr_alpha_expr_in_Partial2,Fdr_alpha_expr_out_Partial2,Flag1)
	   where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_in_Partial1,Fdr_alpha_expr_in_Partial2) ->Fdr_alpha_expr_in)
           where(Fdr_alpha_expr_out_Partial2 ->Fdr_alpha_expr_out)
         ||
           where(Value_expr1 ->disamb(P,Value_expr3,T))
           where(LET_DEFS'list(explicit(Pos2,binding(Pos3,single(Pos4,Id_or_op)),Value_expr3),nil) -> Let_expr)
           where(let_expr(Pos,Let_expr,Value_expr2) -> Value_expr4)
           Translate_Value_expr_To_alpha_expr(Value_expr4,Ident,Flag -> Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1)
         |)

  'rule' Translate_Value_expr_To_alpha_expr(if_expr(P1,If,Then,Rg,Elsifs,Else),Ident,Flag -> In, Out, Flag1):
  	 where(Elsifs -> list(elsif(P2,If1,Then1,_), Elsifs1))
	 Translate_Value_expr_To_alpha_expr(
	   if_expr(P1,If,Then,Rg,nil,else(P2,if_expr(P2,If1,Then1,Rg,Elsifs1,Else))),Ident,Flag
			-> In, Out, Flag1)

  'rule' Translate_Value_expr_To_alpha_expr(if_expr(_,If,Then,_,_,nil),Ident,Flag ->
					    Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1):
         Translate_Value_expr_To_alpha_expr(Then,Ident,Flag -> Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1)


  'rule' Translate_Value_expr_To_alpha_expr(if_expr(_,If,Then,_,nil,else(_,Value_expr)),Ident,Flag ->
                                            Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag3): 
	 Translate_Value_expr_To_alpha_expr(Then,Ident,Flag -> Fdr_alpha_expr_in_Partial1,Fdr_alpha_expr_out_Partial1,Flag1)
         Translate_Value_expr_To_alpha_expr(Value_expr,Ident,Flag -> Fdr_alpha_expr_in_Partial2,Fdr_alpha_expr_out_Partial2,Flag2)
         (|(|eq(Flag1,fdr_No_Access)||eq(Flag2,fdr_No_Access)|)
           where(FDR_FLAG_PROCESS_OPE'fdr_No_Access -> Flag3)
         ||
           where(Flag -> Flag3)
         |)
	 where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_in_Partial1,Fdr_alpha_expr_in_Partial2) -> Fdr_alpha_expr_in)
	 where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_out_Partial1,Fdr_alpha_expr_out_Partial2) -> Fdr_alpha_expr_out)

  'rule' Translate_Value_expr_To_alpha_expr(let_expr(_,Let_defs,Value_expr),Ident,Flag->
					    Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1):	 				      
	 Translate_Value_expr_To_alpha_expr(Value_expr,Ident,Flag ->Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1)	


  'rule' Translate_Value_expr_To_alpha_expr(case_expr(Pos,Value_expr1,Pos1,Case),Ident,Flag ->
                                            Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1):
         where(case_expr(Pos,Value_expr1,Pos1,Case) -> Case_expr)        
         Rewrite_Case_expr_To_LetIf_expr(Case_expr -> If_value_expr)
         Translate_Value_expr_To_alpha_expr(If_value_expr,Ident,Flag ->
					    Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1)		       

  'rule' Translate_Value_expr_To_alpha_expr(stmt_infix(_,Value_expr1,Combinator,Value_expr2),Ident,Flag->
                                            Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag3):
         (|eq(Combinator, ext_choice) || eq(Combinator, int_choice)|)
         Translate_Value_expr_To_alpha_expr(Value_expr1,Ident,Flag -> Fdr_alpha_expr_in_Partial1,Fdr_alpha_expr_out_Partial1,Flag1)
         Translate_Value_expr_To_alpha_expr(Value_expr2,Ident,Flag -> Fdr_alpha_expr_in_Partial2,Fdr_alpha_expr_out_Partial2,Flag2)
         (|eq(Flag1,fdr_No_Access)
	   where(fdr_No_Access ->Flag3)
         ||
           eq(Flag2,fdr_No_Access)
           where(fdr_No_Access ->Flag3)
         ||
           where(fdr_Access ->Flag3)
         |)
         where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_in_Partial1,Fdr_alpha_expr_in_Partial2) ->Fdr_alpha_expr_in1)
         where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_out_Partial1,Fdr_alpha_expr_out_Partial2) ->Fdr_alpha_expr_out1)
	 Simplify_alphabet(Fdr_alpha_expr_in1, nil -> Fdr_alpha_expr_in)
	 Simplify_alphabet(Fdr_alpha_expr_out1, nil -> Fdr_alpha_expr_out)
        	
         --- to X||Y ---> in: union(diff(in(X),H),diff(in(Y),H)) -- out: union(diff(out(X),H),diff(out(Y),H))  
  'rule' Translate_Value_expr_To_alpha_expr(stmt_infix(_,Value_expr1,parallel,Value_expr2),Ident,Flag->
                                            Fdr_alpha_expr_in,Fdr_alpha_expr_out,fdr_No_Access):
         Translate_Value_expr_To_alpha_expr(Value_expr1,Ident,Flag -> Fdr_alpha_expr_in_Partial1,Fdr_alpha_expr_out_Partial1,Flag1)
         Translate_Value_expr_To_alpha_expr(Value_expr2,Ident,Flag -> Fdr_alpha_expr_in_Partial2,Fdr_alpha_expr_out_Partial2,Flag2)
	 Generate_hidden_set(Fdr_alpha_expr_in_Partial1,Fdr_alpha_expr_out_Partial1,
                             Fdr_alpha_expr_in_Partial2,Fdr_alpha_expr_out_Partial2 ->Fdr_alpha_expr_hidden)

         where(fdr_fun_alpha2(fdr_diff,Fdr_alpha_expr_in_Partial1,Fdr_alpha_expr_hidden) -> Fdr_alpha_expr_in_1)       
         where(fdr_fun_alpha2(fdr_diff,Fdr_alpha_expr_out_Partial1,Fdr_alpha_expr_hidden) -> Fdr_alpha_expr_out_1)
         where(fdr_fun_alpha2(fdr_diff,Fdr_alpha_expr_in_Partial2,Fdr_alpha_expr_hidden) -> Fdr_alpha_expr_in_2)
         where(fdr_fun_alpha2(fdr_diff,Fdr_alpha_expr_out_Partial2,Fdr_alpha_expr_hidden) -> Fdr_alpha_expr_out_2)
         where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_in_1,Fdr_alpha_expr_in_2) ->Fdr_alpha_expr_in1)
         where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_out_1,Fdr_alpha_expr_out_2) ->Fdr_alpha_expr_out1)
	 Simplify_alphabet(Fdr_alpha_expr_in1, nil -> Fdr_alpha_expr_in)
	 Simplify_alphabet(Fdr_alpha_expr_out1, nil -> Fdr_alpha_expr_out)

	 ---- to []X(i) or |~|X(i) ----> in: Union(in(X(i))) -- out: Union(out(X(i)))
  'rule' Translate_Value_expr_To_alpha_expr (comprehended(_,Combinator,Value_expr,set_limit(_,Typings,Restriction)),Ident,Flag->
                                             Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1)
         (|eq(Combinator, ext_choice)||eq(Combinator, int_choice)|)
	 Translate_Value_expr_To_alpha_expr(Value_expr,Ident,Flag -> Fdr_alpha_expr_inp,Fdr_alpha_expr_outp,Flag1)
	 Translate_Typings_To_Fdr_bindings(Typings -> Fdr_bindings)
	 Translate_Restriction_To_Fdr_value_expr(Restriction ->Fdr_value_expr)
	 where(fdr_fun_alpha1(fdr_Union,fdr_comp_alpha(Fdr_alpha_expr_inp,Fdr_bindings,Fdr_value_expr)) 
               ->Fdr_alpha_expr_in )
	 where(fdr_fun_alpha1(fdr_Union,fdr_comp_alpha(Fdr_alpha_expr_outp,Fdr_bindings,Fdr_value_expr)) 
               -> Fdr_alpha_expr_out)
         

	 ---- to ||X(i) ----> in: diff(Union(in(X(i))),H) -- out: diff(Union(out(X(i))),H)
  'rule' Translate_Value_expr_To_alpha_expr (comprehended(_,parallel,Value_expr,set_limit(_,Typings,Restriction)),Ident,Flag->
                                             Fdr_alpha_expr_in_total,Fdr_alpha_expr_out_total,fdr_No_Access)                
         Translate_Value_expr_To_alpha_expr(Value_expr,Ident,Flag -> Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag1)
	 Translate_Typings_To_Fdr_bindings(Typings -> Fdr_bindings)
	 Translate_Restriction_To_Fdr_value_expr(Restriction ->Fdr_value_expr)
	 Generate_Compreh_hidden_set(Fdr_alpha_expr_in,Fdr_alpha_expr_out,Fdr_bindings,Fdr_value_expr -> Fdr_alpha_expr_hidden)
	 
         where(fdr_fun_alpha1(fdr_Union,fdr_comp_alpha(Fdr_alpha_expr_in,Fdr_bindings,Fdr_value_expr)) 
               -> Fdr_alpha_expr_in_partial)
	 where(fdr_fun_alpha1(fdr_Union,fdr_comp_alpha(Fdr_alpha_expr_out,Fdr_bindings,Fdr_value_expr)) 
               -> Fdr_alpha_expr_out_partial)
	 where(fdr_fun_alpha2(fdr_diff,Fdr_alpha_expr_in_partial,Fdr_alpha_expr_hidden) -> Fdr_alpha_expr_in_total)
	 where(fdr_fun_alpha2(fdr_diff,Fdr_alpha_expr_out_partial,Fdr_alpha_expr_hidden) -> Fdr_alpha_expr_out_total)

  'rule' Translate_Value_expr_To_alpha_expr(Value_expr,Ident,Flag -> fdr_empty,fdr_empty,Flag)
	 Putmsg("alphabet cannot be translated\n")
print(Value_expr)
Putnl()



			     
----- hidden set------

--- to X||Y ---> union(inter(in(X) ,out(Y)), inter(out(X),in(Y))) 
'action' Generate_hidden_set(FDR_ALPHA_EXPR,FDR_ALPHA_EXPR,FDR_ALPHA_EXPR,FDR_ALPHA_EXPR ->FDR_ALPHA_EXPR)

  'rule' Generate_hidden_set(Fdr_alpha_expr_in_1,Fdr_alpha_expr_out_1,Fdr_alpha_expr_in_2,Fdr_alpha_expr_out_2 
                             ->Fdr_alpha_expr_hidden_simp):
         where(fdr_fun_alpha2(fdr_inter,Fdr_alpha_expr_in_1,Fdr_alpha_expr_out_2) -> Fdr_alpha_inter1)
         where(fdr_fun_alpha2(fdr_inter,Fdr_alpha_expr_in_2,Fdr_alpha_expr_out_1) -> Fdr_alpha_inter2)
         where(fdr_fun_alpha2(fdr_union,Fdr_alpha_inter1,Fdr_alpha_inter2) -> Fdr_alpha_expr_hidden)
	 Simplify_alphabet(Fdr_alpha_expr_hidden, nil ->Fdr_alpha_expr_hidden_simp)

---- to ||X(i) ----> inter(Union(in(X(i))),Union(out(X(i))))
'action' Generate_Compreh_hidden_set(FDR_ALPHA_EXPR, FDR_ALPHA_EXPR,FDR_BINDINGS,FDR_VALUE_EXPR-> FDR_ALPHA_EXPR)

  'rule' Generate_Compreh_hidden_set(Fdr_alpha_expr_in,Fdr_alpha_expr_out,Fdr_bindings,Fdr_value_expr -> Fdr_alpha_expr_hidden_simp):
	 where(fdr_fun_alpha1(fdr_Union,fdr_comp_alpha(Fdr_alpha_expr_in,Fdr_bindings,Fdr_value_expr)) -> Fdr_alpha_Union1)
         where(fdr_fun_alpha1(fdr_Union,fdr_comp_alpha(Fdr_alpha_expr_out,Fdr_bindings,Fdr_value_expr)) -> Fdr_alpha_Union2)
         where(fdr_fun_alpha2(fdr_inter,Fdr_alpha_Union1,Fdr_alpha_Union2) -> Fdr_alpha_expr_hidden)
	 Simplify_alphabet(Fdr_alpha_expr_hidden, nil ->Fdr_alpha_expr_hidden_simp)


---error condition------- 

--- to X||Y ---> inter(in(X),in(Y)) == {} and inter(out(X),out(Y)) == {}
-- if this condition is true then process else chaos 
'action' Generate_error_condition(FDR_ALPHA_EXPR,FDR_ALPHA_EXPR,FDR_ALPHA_EXPR,FDR_ALPHA_EXPR -> FDR_VALUE_EXPR)

  'rule' Generate_error_condition(Fdr_alpha_expr_in_1,Fdr_alpha_expr_out_1,Fdr_alpha_expr_in_2,Fdr_alpha_expr_out_2 -> Fdr_value_expr):
	 where(fdr_fun_alpha2(fdr_inter,Fdr_alpha_expr_in_1,Fdr_alpha_expr_in_2) -> Fdr_alpha_inter1)
	 Simplify_alphabet(Fdr_alpha_inter1, nil ->Fdr_alpha_inter1_simp)
         where(fdr_fun_alpha2(fdr_inter,Fdr_alpha_expr_out_1,Fdr_alpha_expr_out_2) -> Fdr_alpha_inter2)
	 Simplify_alphabet(Fdr_alpha_inter2, nil ->Fdr_alpha_inter2_simp)
	 (|
	   Is_empty_alphabet(Fdr_alpha_inter1_simp)
	   (|
	     Is_empty_alphabet(Fdr_alpha_inter2_simp)
	     where(fdr_literal_expr(fdr_bool_true) -> Fdr_value_expr)
	   ||
	     where(fdr_infi_expr(fdr_alpha_expr(Fdr_alpha_inter2_simp),fdr_equal,fdr_alpha_expr(fdr_empty)) ->Fdr_value_expr)
	   |)
	 ||
	   (|
	     Is_empty_alphabet(Fdr_alpha_inter2_simp)
	     where(fdr_infi_expr(fdr_alpha_expr(Fdr_alpha_inter1_simp),fdr_equal,fdr_alpha_expr(fdr_empty)) ->Fdr_value_expr)
	   ||
	     where(fdr_infi_expr(fdr_alpha_expr(Fdr_alpha_inter1_simp),fdr_equal,fdr_alpha_expr(fdr_empty)) ->Fdr_value_expr_in)
	     where(fdr_infi_expr(fdr_alpha_expr(Fdr_alpha_inter2_simp),fdr_equal,fdr_alpha_expr(fdr_empty)) ->Fdr_value_expr_out)
	     where(fdr_infi_expr(Fdr_value_expr_in,fdr_and,Fdr_value_expr_out) ->Fdr_value_expr)
	   |)
	 |)

---- to ||X(i) ---->Inter(in(X(i)) == {} and Inter(out(X(i))) = {}
-- if this condition is true then process else chaos 
'action' Generate_Comprh_error_condition(FDR_ALPHA_EXPR,FDR_ALPHA_EXPR,FDR_BINDINGS,FDR_VALUE_EXPR ->FDR_VALUE_EXPR)

  'rule' Generate_Comprh_error_condition(Fdr_alpha_expr_in,Fdr_alpha_expr_out,Fdr_bindings,Fdr_value_expr_cond ->Fdr_value_expr):
	 where(fdr_fun_alpha1(fdr_Inter,fdr_comp_alpha(Fdr_alpha_expr_in,Fdr_bindings,Fdr_value_expr_cond)) -> Fdr_alpha_inter1)
	 where(fdr_fun_alpha1(fdr_Inter,fdr_comp_alpha(Fdr_alpha_expr_out,Fdr_bindings,Fdr_value_expr_cond)) -> Fdr_alpha_inter2)
	 Simplify_alphabet(Fdr_alpha_inter1, nil ->Fdr_alpha_inter1_simp)
	 Simplify_alphabet(Fdr_alpha_inter2, nil ->Fdr_alpha_inter2_simp)
	 (|
	   Is_empty_alphabet(Fdr_alpha_inter1_simp)
	   (|
	     Is_empty_alphabet(Fdr_alpha_inter2_simp)
	     where(fdr_literal_expr(fdr_bool_true) -> Fdr_value_expr)
	   ||
	     where(fdr_infi_expr(fdr_alpha_expr(Fdr_alpha_inter2_simp),fdr_equal,fdr_alpha_expr(fdr_empty)) ->Fdr_value_expr)
	   |)
	 ||
	   (|
	     Is_empty_alphabet(Fdr_alpha_inter2_simp)
	     where(fdr_infi_expr(fdr_alpha_expr(Fdr_alpha_inter1_simp),fdr_equal,fdr_alpha_expr(fdr_empty)) ->Fdr_value_expr)
	   ||
	     where(fdr_infi_expr(fdr_alpha_expr(Fdr_alpha_inter1_simp),fdr_equal,fdr_alpha_expr(fdr_empty)) ->Fdr_value_expr_in)
	     where(fdr_infi_expr(fdr_alpha_expr(Fdr_alpha_inter2_simp),fdr_equal,fdr_alpha_expr(fdr_empty)) ->Fdr_value_expr_out)
	     where(fdr_infi_expr(Fdr_value_expr_in,fdr_and,Fdr_value_expr_out) ->Fdr_value_expr)
	   |)
	 |)


---- enumerated alphabet ---------

'action' Translate_Value_expr_To_Fdr_enum_alpha(VALUE_EXPR ->FDR_ALPHA_EXPR)

  'rule' Translate_Value_expr_To_Fdr_enum_alpha(Value_expr -> fdr_enum_alpha(list(Fdr_enum_alpha_expr,nil))):
         Translate_Value_expr_To_Fdr_enum_alpha_expr(Value_expr->Fdr_enum_alpha_expr)

'action' Translate_Value_expr_To_Fdr_enum_alpha_expr(VALUE_EXPR -> FDR_ENUM_ALPHA_EXPR)

  'rule' Translate_Value_expr_To_Fdr_enum_alpha_expr(Value_expr ->fdr_enum_alpha_expr(Fdr_ident,Fdr_value_exprs)):
	 (|where(Value_expr->input_occ(P,I,Q)) ||where(Value_expr->output_occ(P,I,Q,VE))|)
         (|ne(Q,nil)
	   where(Q -> qualification(obj_appl(obj_occ(_,O_id),Value_exprs)))
	   O_id'Ident -> Fdr_ident1
	   I'Ident -> Fdr_ident2
	   Translate_OIdent_To_OFdr_ident(Fdr_ident1,Fdr_ident2 ->Fdr_ident)
           Translate_Value_exprs_To_Fdr_value_exprs(Value_exprs ->Fdr_value_exprs)
	 ||
	   I'Ident -> Fdr_ident
	   where(FDR_VALUE_EXPRS'nil->Fdr_value_exprs)
         |)


----- Simplify_alphabet-----
-- second parameter is named alphabets already unfolded
-- which we need to avoid infinite recursion with 
-- mutually recursive processes
'action' Simplify_alphabet(FDR_ALPHA_EXPR, IDENTS ->FDR_ALPHA_EXPR)

   -- this allows more alphabets to be treated as enumerations
  'rule' Simplify_alphabet(fdr_empty, Ids -> fdr_enum_alpha(nil)):

  'rule' Simplify_alphabet(fdr_enum_alpha(Alphas), Ids -> fdr_enum_alpha(Alphas1)):
 	 Remove_duplicate_channels(Alphas -> Alphas1)

  -- effectively unfolds alphabets of named processes
  -- but only if there are no parameters
  -- If Id is in Ids then its alphabet is already unfolded
  -- perhaps needs this check for mutually recursive processes
  -- but even this unfolding blows up for the MUX_ABP example
  -- so only done if specification hs an LTL declaration
  'rule' Simplify_alphabet(fdr_named_alpha(Id,nil,Alpha), Ids -> Alpha1):
  	 Has_LTL()
  	 (|
	   Is_in_ids(Id, Ids)
	   where(fdr_enum_alpha(nil) -> Alpha1)
	 ||
  	   Simplify_alphabet(Alpha, list(Id, Ids) -> Alpha1)
	 |)

  -- or unfold if the alphabet is empty
  'rule' Simplify_alphabet(fdr_named_alpha(Id,_,Alpha), Ids -> fdr_enum_alpha(nil)):
  	 Has_LTL()
  	 (|
	   Is_in_ids(Id, Ids)
	 ||
  	   Simplify_alphabet(Alpha, list(Id, Ids) -> fdr_enum_alpha(nil))
         |)

  -- or unfold if there are no parameter dependencies
  'rule' Simplify_alphabet(fdr_named_alpha(Id,Args,Alpha), Ids -> Alpha1)
  	 Has_LTL()
  	 (|
	   Is_in_ids(Id, Ids)
	   where(fdr_enum_alpha(nil) -> Alpha1)
	 ||
	   Can_unfold(Alpha)
  	   Simplify_alphabet(Alpha, list(Id, Ids) -> Alpha1)
	 |)

  'rule' Simplify_alphabet(fdr_fun_alpha1(fdr_Union, Alpha), Ids -> fdr_enum_alpha(nil)):
  	 Simplify_alphabet(Alpha, Ids -> fdr_enum_alpha(nil))

  'rule' Simplify_alphabet(fdr_fun_alpha1(fdr_Inter, Alpha), Ids -> fdr_enum_alpha(nil)):
  	 Simplify_alphabet(Alpha, Ids -> fdr_enum_alpha(nil))

  'rule' Simplify_alphabet(fdr_fun_alpha2(fdr_union, Alpha1, Alpha2), Ids -> Alpha):
  	 Simplify_alphabet(Alpha1, Ids -> fdr_enum_alpha(nil))
	 Simplify_alphabet(Alpha2, Ids -> Alpha)

  'rule' Simplify_alphabet(fdr_fun_alpha2(fdr_union, Alpha1, Alpha2), Ids -> Alpha):
  	 Simplify_alphabet(Alpha2, Ids -> fdr_enum_alpha(nil))
	 Simplify_alphabet(Alpha1, Ids -> Alpha)

  'rule' Simplify_alphabet(fdr_fun_alpha2(fdr_union, Alpha1, Alpha2), Ids -> Alpha):
  	 Simplify_alphabet(Alpha1, Ids -> Alpha11)
  	 Simplify_alphabet(Alpha2, Ids -> Alpha22)
  	 Simplify_union_alphabet(Alpha11, Alpha22 -> Alpha)

  'rule' Simplify_alphabet(fdr_fun_alpha2(fdr_inter, Alpha1, Alpha2), Ids -> fdr_enum_alpha(nil)):
  	 Simplify_alphabet(Alpha1, Ids -> fdr_enum_alpha(nil))

  'rule' Simplify_alphabet(fdr_fun_alpha2(fdr_inter, Alpha1, Alpha2), Ids -> fdr_enum_alpha(nil)):
  	 Simplify_alphabet(Alpha2, Ids -> fdr_enum_alpha(nil))

  'rule' Simplify_alphabet(fdr_fun_alpha2(fdr_inter, Alpha1, Alpha2), Ids -> Alpha):
  	 Simplify_alphabet(Alpha1, Ids -> Alpha11)
  	 Simplify_alphabet(Alpha2, Ids -> Alpha22)
  	 Simplify_inter_alphabet(Alpha11, Alpha22 -> Alpha)

  'rule' Simplify_alphabet(fdr_fun_alpha2(fdr_diff, Alpha1, Alpha2), Ids -> fdr_enum_alpha(nil)):
  	 Simplify_alphabet(Alpha1, Ids -> fdr_enum_alpha(nil))

  'rule' Simplify_alphabet(fdr_fun_alpha2(fdr_diff, Alpha1, Alpha2), Ids -> Alpha):
  	 Simplify_alphabet(Alpha2, Ids -> fdr_enum_alpha(nil))
	 Simplify_alphabet(Alpha1, Ids -> Alpha)

  'rule' Simplify_alphabet(fdr_fun_alpha2(fdr_diff, Alpha1, Alpha2), Ids -> Alpha):  	 Simplify_alphabet(Alpha1, Ids -> Alpha11)
  	 Simplify_alphabet(Alpha2, Ids -> Alpha22)
  	 Simplify_diff_alphabet(Alpha11, Alpha22 -> Alpha)

  'rule' Simplify_alphabet(fdr_comp_alpha(Alpha,_,_), Ids -> fdr_enum_alpha(nil)):
	 Simplify_alphabet(Alpha, Ids -> fdr_enum_alpha(nil))

  -- {| c.i | i<-T |} simplifies to {|c|}
  'rule' Simplify_alphabet(fdr_comp_alpha(Alpha, Bs, nil), _ -> Alpha1):
  	 where(Alpha -> fdr_enum_alpha(list(Alpha_expr, nil)))
	 where(Alpha_expr -> fdr_enum_alpha_expr(Id, Vs))
	 where(Vs -> list(fdr_named_val(Id1), nil))
	 where(Bs -> list(fdr_binding(Id2, _), nil))
	 eq(Id1, Id2)
	 where(fdr_enum_alpha(list(fdr_enum_alpha_expr(Id, nil), nil)) -> Alpha1)

  'rule' Simplify_alphabet(Fdr_alpha_expr, _ -> Fdr_alpha_expr):

'action' Simplify_union_alphabet(FDR_ALPHA_EXPR,  FDR_ALPHA_EXPR -> FDR_ALPHA_EXPR)

  'rule' Simplify_union_alphabet(fdr_enum_alpha(Chs1), fdr_enum_alpha(Chs2) -> fdr_enum_alpha(Chs)):
	 Simplify_union_channels(Chs1, Chs2 -> Chs)

	 -- since for comprehensions impossible to see if channel there or not,
	 -- we can fail to simplify
  'rule' Simplify_union_alphabet(Alpha1, Alpha2 -> fdr_fun_alpha2(fdr_union, Alpha1, Alpha2)):


'action' Simplify_inter_alphabet(FDR_ALPHA_EXPR,  FDR_ALPHA_EXPR -> FDR_ALPHA_EXPR)

  'rule' Simplify_inter_alphabet(fdr_enum_alpha(Chs1), fdr_enum_alpha(Chs2) -> fdr_enum_alpha(Chs)):
	 Simplify_inter_channels(Chs1, Chs2 -> Chs)

	 -- since for comprehensions impossible to see if channel there or not,
	 -- we can fail to simplify
  'rule' Simplify_inter_alphabet(Alpha1, Alpha2 -> fdr_fun_alpha2(fdr_inter, Alpha1, Alpha2)):


'action' Simplify_diff_alphabet(FDR_ALPHA_EXPR,  FDR_ALPHA_EXPR -> FDR_ALPHA_EXPR)

  'rule' Simplify_diff_alphabet(fdr_enum_alpha(Chs1), fdr_enum_alpha(Chs2) -> fdr_enum_alpha(Chs)):
	 Simplify_diff_channels(Chs1, Chs2 -> Chs)

	 -- since for comprehensions impossible to see if channel there or not,
	 -- we can fail to simplify
  'rule' Simplify_diff_alphabet(Alpha1, Alpha2 -> fdr_fun_alpha2(fdr_diff, Alpha1, Alpha2)):


'condition' Simplify_union_channels(FDR_ENUM_ALPHA_EXPRS, FDR_ENUM_ALPHA_EXPRS -> FDR_ENUM_ALPHA_EXPRS)

  'rule' Simplify_union_channels(list(fdr_enum_alpha_expr(Id, nil), Tl), Chs1 -> Chs):
  	 (|
	   Contains_channel(Id, Chs1 -> _)
	   Simplify_union_channels(Tl, Chs1 -> Chs)
	 ||
	   Simplify_union_channels(Tl, Chs1 -> Chs2)
	   where(FDR_ENUM_ALPHA_EXPRS'list(fdr_enum_alpha_expr(Id, nil), Chs2) -> Chs)
	 |)

  'rule' Simplify_union_channels(nil, Chs -> Chs):


'condition' Simplify_inter_channels(FDR_ENUM_ALPHA_EXPRS, FDR_ENUM_ALPHA_EXPRS -> FDR_ENUM_ALPHA_EXPRS)

  'rule' Simplify_inter_channels(list(fdr_enum_alpha_expr(Id, nil), Tl), Chs1 -> Chs):
  	 (|
	   Contains_channel(Id, Chs1 -> Chs11)
	   Simplify_inter_channels(Tl, Chs11 -> Chs2)
	   where(FDR_ENUM_ALPHA_EXPRS'list(fdr_enum_alpha_expr(Id, nil), Chs2) -> Chs)
	 ||
	   Simplify_inter_channels(Tl, Chs1 -> Chs)
	 |)

  'rule' Simplify_inter_channels(nil, Chs -> nil):


'condition' Simplify_diff_channels(FDR_ENUM_ALPHA_EXPRS, FDR_ENUM_ALPHA_EXPRS -> FDR_ENUM_ALPHA_EXPRS)

  'rule' Simplify_diff_channels(list(fdr_enum_alpha_expr(Id, nil), Tl), Chs1 -> Chs):
  	 (|
	   Contains_channel(Id, Chs1 -> _)
	   Simplify_diff_channels(Tl, Chs1 -> Chs)
	 ||
	   Simplify_diff_channels(Tl, Chs1 -> Chs2)
	   where(FDR_ENUM_ALPHA_EXPRS'list(fdr_enum_alpha_expr(Id, nil), Chs2) -> Chs)
	 |)

  'rule' Simplify_diff_channels(nil, Chs -> nil):


-- if succeeds, returns alphabet with channel removed
'condition' Contains_channel(IDENT, FDR_ENUM_ALPHA_EXPRS -> FDR_ENUM_ALPHA_EXPRS)

  'rule' Contains_channel(Id, list(fdr_enum_alpha_expr(Id1, nil), Chs1) -> Chs2):
	 eq(Id, Id1)
	 (| -- try to remove duplicates
	   Contains_channel(Id, Chs1 -> Chs2)
	 ||
	   where(Chs1 -> Chs2)
	 |)

  'rule' Contains_channel(Id, list(fdr_enum_alpha_expr(Id1, Vs), Chs1)
			      		-> list(fdr_enum_alpha_expr(Id1, Vs), Chs))
	 Contains_channel(Id, Chs1 -> Chs)

'action' Remove_duplicate_channels(FDR_ENUM_ALPHA_EXPRS -> FDR_ENUM_ALPHA_EXPRS)

  'rule' Remove_duplicate_channels(nil -> nil):

  'rule' Remove_duplicate_channels(list(fdr_enum_alpha_expr(Id, Vs), Chs1) ->
		list(fdr_enum_alpha_expr(Id, Vs), Chs3)):
  	 (|
	   eq(Vs, nil)
	   Contains_channel(Id, Chs1 -> Chs2)
	 ||
	   where(Chs1 -> Chs2)
	 |)
	 Remove_duplicate_channels(Chs2 -> Chs3)

'condition' Is_empty_alphabet(FDR_ALPHA_EXPR)

  'rule' Is_empty_alphabet(fdr_enum_alpha(nil)):

  'rule' Is_empty_alphabet(fdr_empty):

'action' Length_id_list(IDENTS -> INT)

  'rule' Length_id_list(list(Id, Ids) -> N + 1):
  	 Length_id_list(Ids -> N)

  'rule' Length_id_list(nil -> 0):

-- can unfold alphabet expression if there are no arguments
'condition' Can_unfold(FDR_ALPHA_EXPR)

  'rule' Can_unfold(fdr_named_alpha(_,_,Alpha)):
  	 Can_unfold(Alpha)

  'rule' Can_unfold(fdr_enum_alpha(Exprs)):
  	 Can_unfold_exprs(Exprs)

  'rule' Can_unfold(fdr_fun_alpha1(_, Alpha)):
  	 Can_unfold(Alpha)

  'rule' Can_unfold(fdr_fun_alpha2(_, Alpha1, Alpha2)):
  	 Can_unfold(Alpha1)
  	 Can_unfold(Alpha2)

  'rule' Can_unfold(fdr_empty):

'condition' Can_unfold_exprs(FDR_ENUM_ALPHA_EXPRS)

  'rule' Can_unfold_exprs(list(Expr, Exprs)):
  	 Can_unfold_expr(Expr)
  	 Can_unfold_exprs(Exprs)

  'rule' Can_unfold_exprs(nil):

-- can unfold alphabet expression if there are no arguments
'condition' Can_unfold_expr(FDR_ENUM_ALPHA_EXPR)

  'rule' Can_unfold_expr(fdr_enum_alpha_expr(_, nil)):

--------------------------------------------------------------------------------------------------------------	
--------------------------------------------------------------------------------------------------------------
-----------------------------------------for a process--------------------------------------------------------
--------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------

'action' Translate_Formal_function_parameters_To_Fdr_pattern_exprs(FORMAL_FUNCTION_PARAMETERS -> FDR_PATTERN_EXPRS)

  'rule' Translate_Formal_function_parameters_To_Fdr_pattern_exprs(list(form_parm(_,Bindings),nil)->Fdr_pattern_exprs):
         Translate_Bindings_To_Fdr_pattern_exprs(Bindings -> Fdr_pattern_exprs)

  'rule' Translate_Formal_function_parameters_To_Fdr_pattern_exprs(list(form_parm(Pos,Bindings),FPs)->nil):
         Puterror(Pos)
         Putmsg("Formal function parameters cannot be translated\n")


---------------------- PROCESS_COMBINATION-----------------------------------------

'action' Translate_Value_expr_To_Fdr_process_combination(VALUE_EXPR -> FDR_PROCESS_COMBINATION)

  'rule' Translate_Value_expr_To_Fdr_process_combination(stmt_infix(_,Value_expr1,Combinator,Value_expr2)->
                                                      fdr_proc_inf_ope(Fdr_process_combination1,Fdr_comb_ope,Fdr_process_combination2)):
         (| eq(Combinator, ext_choice) || eq(Combinator, int_choice) |)
         Translate_Value_expr_To_Fdr_process_combination(Value_expr1 -> Fdr_process_combination1)
         Translate_Combinator_To_Fdr_comb_ope(Combinator -> Fdr_comb_ope)
         Translate_Value_expr_To_Fdr_process_combination(Value_expr2 -> Fdr_process_combination2)


  'rule' Translate_Value_expr_To_Fdr_process_combination(comprehended(_,Combinator,Value_expr,set_limit(_,Typings,Restriction))->
                                                  fdr_pro_pre_ope(Fdr_bindings,Fdr_value_expr_cond,Fdr_comb_ope,Fdr_process_combination)):
         (|eq(Combinator, ext_choice)||eq(Combinator, int_choice)|)
         Translate_Typings_To_Fdr_bindings(Typings -> Fdr_bindings)
	 Translate_Restriction_To_Fdr_value_expr(Restriction ->Fdr_value_expr_cond)
         Translate_Combinator_To_Fdr_comb_ope(Combinator -> Fdr_comb_ope)
         Translate_Value_expr_To_Fdr_process_combination(Value_expr -> Fdr_process_combination)

         -- X||Y ----> if error condition then  (X[union(in(X),out(X))||union(in(Y),out(Y))]Y)\H else CHAOS 
  'rule' Translate_Value_expr_To_Fdr_process_combination(stmt_infix(_,Value_expr1,parallel,Value_expr2)->
							 fdr_process(fdr_if_expr(Fdr_condition,Fdr_then,Fdr_else))): 

         Translate_Value_expr_To_Fdr_process_combination(Value_expr1 -> Fdr_process_combination1)
         string_to_id ("_____error@@###_" ->Ident)
         Translate_Value_expr_To_alpha_expr(Value_expr1,Ident,fdr_Access -> Fdr_alpha_expr_in_1,Fdr_alpha_expr_out_1,Flag1)
	 where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_in_1,Fdr_alpha_expr_out_1) -> Fdr_alpha_expr1)
	 Simplify_alphabet(Fdr_alpha_expr1, nil -> Fdr_alpha_expr1_simp)
         Translate_Value_expr_To_Fdr_process_combination(Value_expr2 -> Fdr_process_combination2)
         Translate_Value_expr_To_alpha_expr(Value_expr2,Ident,fdr_Access -> Fdr_alpha_expr_in_2,Fdr_alpha_expr_out_2,Flag2)
         where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_in_2,Fdr_alpha_expr_out_2) -> Fdr_alpha_expr2)
	 Simplify_alphabet(Fdr_alpha_expr2, nil -> Fdr_alpha_expr2_simp)
         Generate_hidden_set(Fdr_alpha_expr_in_1,Fdr_alpha_expr_out_1,Fdr_alpha_expr_in_2,Fdr_alpha_expr_out_2 ->Fdr_alpha_expr_hidden)
         Generate_error_condition(Fdr_alpha_expr_in_1,Fdr_alpha_expr_out_1,Fdr_alpha_expr_in_2,Fdr_alpha_expr_out_2 ->Fdr_condition)
         where(fdr_hiding(fdr_inf_alpha_parallel(Fdr_process_combination1,Fdr_alpha_expr1_simp,
                                                  Fdr_process_combination2,Fdr_alpha_expr2_simp),
                           Fdr_alpha_expr_hidden) -> Fdr_then)
	 Simplify_alphabet(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr1_simp,Fdr_alpha_expr2_simp), nil ->Fdr_chaos_alph)		   
         where(fdr_process(fdr_proc_expr(fdr_chaos(Fdr_chaos_alph))) -> Fdr_else)

	 -- ||X(i) ----> if error condition then  (||[union(in(X(i)),out(X(i)))] X(i))\H else CHAOS 
-- this rule is wrong since it really needs pairwise empty
-- intersections for the condition.  So we don't use the if
-- construction, and only return the "then" part

  'rule' Translate_Value_expr_To_Fdr_process_combination(comprehended(_,parallel,Value_expr,set_limit(_,Typings,Restriction))->
						Fdr_then):
--                                              fdr_process(fdr_if_expr(Fdr_condition,Fdr_then,Fdr_else))):
         string_to_id ("_____error@@###_" ->Ident)
	 Translate_Value_expr_To_alpha_expr(Value_expr,Ident,fdr_Access -> Fdr_alpha_expr_in,Fdr_alpha_expr_out,Flag)
         Translate_Value_expr_To_Fdr_process_combination(Value_expr -> Fdr_process_combination)
	 Translate_Typings_To_Fdr_bindings(Typings -> Fdr_bindings)
	 Translate_Restriction_To_Fdr_value_expr(Restriction ->Fdr_value_expr)
	 Generate_Compreh_hidden_set(Fdr_alpha_expr_in,Fdr_alpha_expr_out,Fdr_bindings,Fdr_value_expr -> Fdr_alpha_expr_hidden)
         Generate_Comprh_error_condition(Fdr_alpha_expr_in,Fdr_alpha_expr_out,Fdr_bindings,Fdr_value_expr ->Fdr_condition)
	 where(fdr_fun_alpha2(fdr_union,Fdr_alpha_expr_in,Fdr_alpha_expr_out) -> Fdr_alpha_expr)
	 Simplify_alphabet(Fdr_alpha_expr, nil -> Fdr_alpha_expr_simp)
         where(fdr_hiding(fdr_pre_alpha_parallel(Fdr_bindings,Fdr_value_expr,Fdr_alpha_expr_simp,Fdr_process_combination),
                          Fdr_alpha_expr_hidden) -> Fdr_then)
	 Simplify_alphabet(Fdr_alpha_expr_simp, nil ->Fdr_chaos_alph)		   
         where(fdr_process(fdr_proc_expr(fdr_chaos(Fdr_chaos_alph))) -> Fdr_else)


  'rule' Translate_Value_expr_To_Fdr_process_combination(Value_expr ->fdr_process(Fdr_process)):
	 Translate_Value_expr_To_Fdr_process(Value_expr -> Fdr_process) 


'action' Translate_Combinator_To_Fdr_comb_ope(COMBINATOR -> FDR_COMB_OPE)

  'rule' Translate_Combinator_To_Fdr_comb_ope(ext_choice -> fdr_ext_choice)
	 
  'rule' Translate_Combinator_To_Fdr_comb_ope(int_choice -> fdr_int_choice)

----------------- process---------------------------------

'action' Translate_Value_expr_To_Fdr_process(VALUE_EXPR->FDR_PROCESS)
 
  'rule' Translate_Value_expr_To_Fdr_process(bracket(_,Value_expr)->Fdr_process):
	 Translate_Value_expr_To_Fdr_process(Value_expr->Fdr_process)

  'rule' Translate_Value_expr_To_Fdr_process(chaos(_)->fdr_proc_expr(fdr_chaos(fdr_empty)))

  'rule' Translate_Value_expr_To_Fdr_process(skip(_)->fdr_proc_expr(fdr_skip))

  'rule' Translate_Value_expr_To_Fdr_process(stop(_)->fdr_proc_expr(fdr_stop))


  'rule' Translate_Value_expr_To_Fdr_process(application(_,Value_expr,Actual_function_parameters)->
                                             fdr_func_proc_expr	(Ident,Fdr_value_exprs)):
         Translate_Value_expr_To_Ident(Value_expr -> Ident)
         Translate_Actual_function_parameters_To_Fdr_value_exprs(Actual_function_parameters -> Fdr_value_exprs)

  'rule' Translate_Value_expr_To_Fdr_process(stmt_infix(Pos,Value_expr1,sequence,Value_expr2) -> X): 
         where(Value_expr1 -> let_expr(P, Defs, Expr))
         Translate_Value_expr_To_Fdr_process(let_expr(P, Defs, stmt_infix(Pos, Expr, sequence, Value_expr2)) -> X) 

  'rule' Translate_Value_expr_To_Fdr_process(stmt_infix(Pos,Value_expr1,sequence,Value_expr2) -> fdr_let_expr(nil, X)): 
         where(Value_expr1 -> stmt_infix(P, Left, Comb, Right))
         (| eq(Comb, ext_choice) || eq(Comb, int_choice) |)
	 where(stmt_infix(Pos,Left,sequence,Value_expr2) -> Left1)
	 where(stmt_infix(Pos,Right,sequence,Value_expr2) -> Right1)
         Translate_Value_expr_To_Fdr_process_combination(stmt_infix(P, Left1, Comb, Right1) -> X) 

  'rule' Translate_Value_expr_To_Fdr_process(stmt_infix(Pos,Value_expr1,sequence,Value_expr2)
                                              -> fdr_arrow_comb_expr(Fdr_chann_expr,Fdr_process_combination)):
         where(Value_expr2 -> bracket(_,stmt_infix(P,V1,Op,V2)))
         (|
           (|where(Value_expr1->input_occ(PI,I,Q)) ||where(Value_expr1->output_occ(PO,I,Q,VE))|)
	   Translate_Value_expr_To_Fdr_chann_expr(Value_expr1 -> Fdr_chann_expr)          
         ||
           Puterror(Pos)
           Putmsg("channel expression cannot be translated\n")
	   where(FDR_CHANN_EXPR'nil->Fdr_chann_expr)
         |)
         where(stmt_infix(P,V1,Op,V2) ->Value_expr3)
	 Translate_Value_expr_To_Fdr_process_combination(Value_expr3 -> Fdr_process_combination)

  'rule' Translate_Value_expr_To_Fdr_process(stmt_infix(Pos,Value_expr1,sequence,Value_expr2)
                                              -> fdr_arrow_expr(Fdr_chann_expr,Fdr_process)):
         (|
           (|where(Value_expr1->input_occ(PI,I,Q)) ||where(Value_expr1->output_occ(PO,I,Q,VE))|)
	    Translate_Value_expr_To_Fdr_chann_expr(Value_expr1 -> Fdr_chann_expr)
         ||
           Puterror(Pos)
           Putmsg("channel expression cannot be translated\n")
	   where(FDR_CHANN_EXPR'nil->Fdr_chann_expr)
         |)
	 Translate_Value_expr_To_Fdr_process(Value_expr2 -> Fdr_process)

  'rule' Translate_Value_expr_To_Fdr_process(let_expr(Pos,list(explicit(Pos2,Let_binding,Value_expr1),nil),Value_expr2)->Fdr_process2):
         
           (|where(Value_expr1 ->input_occ(P,C,O))
             Translate_Value_expr_To_Fdr_chann_expr_in(Let_binding,Value_expr1 ->Fdr_chann_expr)
	     Translate_Value_expr_To_Fdr_process(Value_expr2 -> Fdr_process)
             where(fdr_arrow_expr(Fdr_chann_expr,Fdr_process) ->Fdr_process2)
           ||
             where(Value_expr1 ->disamb(P,Value_expr3,T))
             where(LET_DEFS'list(explicit(Pos2,Let_binding,Value_expr3),nil) -> Let_expr)
             where(let_expr(Pos,Let_expr,Value_expr2) -> Value_expr4)
             Translate_Value_expr_To_Fdr_process(Value_expr4 -> Fdr_process2)
           |)

  'rule' Translate_Value_expr_To_Fdr_process(if_expr(P1,If,Then,Rg,Elsifs,Else) -> Fdr):
  	 where(Elsifs -> list(elsif(P2,If1,Then1,_), Elsifs1))
	 Translate_Value_expr_To_Fdr_process(
	   if_expr(P1,If,Then,Rg,nil,else(P2,if_expr(P2,If1,Then1,Rg,Elsifs1,Else)))
			-> Fdr)

  'rule' Translate_Value_expr_To_Fdr_process(if_expr(_,If,Then,_,_,nil) ->
					     fdr_if_expr(Fdr_if,Then_process_combination,fdr_process(fdr_proc_expr(fdr_skip)))):	
	 Translate_Value_expr_To_Fdr_value_expr(If -> Fdr_if)
	 Translate_Value_expr_To_Fdr_process_combination(Then ->Then_process_combination)


  'rule' Translate_Value_expr_To_Fdr_process(if_expr(_,If,Then,_,nil,else(_,Value_expr)) ->
                                             fdr_if_expr(Fdr_if,Then_process_combination,Else_process_combination)):
	 Translate_Value_expr_To_Fdr_value_expr(If -> Fdr_if)
	 Translate_Value_expr_To_Fdr_process_combination(Then ->Then_process_combination)
	 Translate_Value_expr_To_Fdr_process_combination(Value_expr ->Else_process_combination)


  'rule' Translate_Value_expr_To_Fdr_process(let_expr(_,Let_defs,Value_expr)->
					      fdr_let_expr(Fdr_let_defs,Fdr_process_combination)):
	 Translate_Let_defs_To_Fdr_let_defs(Let_defs -> Fdr_let_defs)				      
	 Translate_Value_expr_To_Fdr_process_combination(Value_expr ->Fdr_process_combination)		


  'rule' Translate_Value_expr_To_Fdr_process(case_expr(Pos,Value_expr1,Pos1,Case) -> Fdr_process):
         where(case_expr(Pos,Value_expr1,Pos1,Case) -> Case_expr)        
         Rewrite_Case_expr_To_LetIf_expr(Case_expr -> If_value_expr)
         Translate_Value_expr_To_Fdr_process(If_value_expr ->Fdr_process)

  'rule' Translate_Value_expr_To_Fdr_process(V:output_occ(_,_,_,_) -> fdr_arrow_expr(Fdr_chann_expr,fdr_proc_expr(fdr_skip))):
         Translate_Value_expr_To_Fdr_chann_expr(V -> Fdr_chann_expr)

  'rule' Translate_Value_expr_To_Fdr_process(V:input_occ(_,_,_) -> fdr_arrow_expr(Fdr_chann_expr,fdr_proc_expr(fdr_skip))):
         Translate_Value_expr_To_Fdr_chann_expr(V -> Fdr_chann_expr)

  'rule' Translate_Value_expr_To_Fdr_process(Value_expr -> fdr_proc_expr(fdr_chaos(fdr_empty)))
	 Putmsg("process cannot be translated\n")
Print_expr(Value_expr)
--print(Value_expr)
Putnl()

------------------------ channel expresion ----------------------------------------

'action' Translate_Value_expr_To_Fdr_chann_expr(VALUE_EXPR -> FDR_CHANN_EXPR)
			      
  'rule' Translate_Value_expr_To_Fdr_chann_expr(input_occ(_,I,O)-> fdr_chan_expr(Fdr_ident,Fdr_chan_values)):
	 (|ne(O,nil)
	   where(O -> qualification(obj_appl(obj_occ(_,O_id),Value_exprs)))
	   O_id'Ident -> Fdr_ident1
	   I'Ident -> Fdr_ident2
	   Translate_OIdent_To_OFdr_ident(Fdr_ident1,Fdr_ident2 ->Fdr_ident)
           Translate_Value_exprs_To_Fdr_chan_values(Value_exprs ->Fdr_chan_values)
	 ||
	   I'Ident -> Fdr_ident
	   where(FDR_CHAN_VALUES'nil->Fdr_chan_values)
         |)
	 
  'rule' Translate_Value_expr_To_Fdr_chann_expr(output_occ(_,I,O,literal_expr(_,unit))-> 
                                                fdr_chan_expr(Fdr_ident,Fdr_chan_values)):
	 (|ne(O,nil)
	   where(O -> qualification(obj_appl(obj_occ(_,O_id),Value_exprs)))
	   O_id'Ident -> Fdr_ident1
	   I'Ident -> Fdr_ident2
	   Translate_OIdent_To_OFdr_ident(Fdr_ident1,Fdr_ident2 ->Fdr_ident)
	   Translate_Value_exprs_To_Fdr_chan_values(Value_exprs ->Fdr_chan_values)
	 ||
	   I'Ident -> Fdr_ident
	   where(FDR_CHAN_VALUES'nil->Fdr_chan_values)
         |)

  'rule' Translate_Value_expr_To_Fdr_chann_expr(output_occ(_,I,O,Value_expr)-> 
                                                fdr_chan_expr(Fdr_ident, Fdr_chan_values)):
	 (|ne(O,nil)
	   where(O -> qualification(obj_appl(obj_occ(_,O_id),Value_exprs)))
	   O_id'Ident -> Fdr_ident1
	   I'Ident -> Fdr_ident2
	   Translate_OIdent_To_OFdr_ident(Fdr_ident1,Fdr_ident2 ->Fdr_ident)
           Translate_Value_exprs_To_Fdr_chan_values(Value_exprs->Fdr_chan_values1)
	   Translate_Value_expr_To_Fdr_chan_out_value(Value_expr -> Fdr_chan_value) 
           Conc_Fdr_chan_values(Fdr_chan_values1,list(Fdr_chan_value,nil) -> Fdr_chan_values)
	 ||
	   I'Ident -> Fdr_ident
	   Translate_Value_expr_To_Fdr_chan_out_value(Value_expr -> Fdr_chan_value) 
	   where(FDR_CHAN_VALUES'list(Fdr_chan_value,nil)->Fdr_chan_values)
         |)
	 

'action' Translate_Value_exprs_To_Fdr_chan_values(VALUE_EXPRS->FDR_CHAN_VALUES)

  'rule' Translate_Value_exprs_To_Fdr_chan_values(list(Value_expr,Value_exprsTail)->list(Fdr_chan_value,Fdr_chan_valuesTail)):
	 Translate_Value_expr_To_Fdr_chan_value(Value_expr ->Fdr_chan_value)
	 Translate_Value_exprs_To_Fdr_chan_values(Value_exprsTail->Fdr_chan_valuesTail)

  'rule' Translate_Value_exprs_To_Fdr_chan_values(nil -> nil)


'action' Translate_Value_expr_To_Fdr_chan_value(VALUE_EXPR->FDR_CHAN_VALUE)

  'rule' Translate_Value_expr_To_Fdr_chan_value(Value_expr ->fdr_chan_value(fdr_chan_point,Fdr_value_expr)):
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr ->Fdr_value_expr)
	 

'action' Translate_Value_expr_To_Fdr_chan_out_value(VALUE_EXPR -> FDR_CHAN_VALUE) 

  'rule' Translate_Value_expr_To_Fdr_chan_out_value(Value_expr -> fdr_chan_value(fdr_chan_out,Fdr_value_expr)):	
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr ->Fdr_value_expr)

 
'action' Translate_Value_expr_To_Fdr_chann_expr_in(LET_BINDING,VALUE_EXPR->FDR_CHANN_EXPR)

  'rule' Translate_Value_expr_To_Fdr_chann_expr_in(X, disamb(_, Y, _) ->FCE):
	 Translate_Value_expr_To_Fdr_chann_expr_in(X, Y -> FCE)

  'rule' Translate_Value_expr_To_Fdr_chann_expr_in(binding(_,single(_,id_op(Ident1))),input_occ(_,I,O)->
						fdr_chan_expr(Fdr_ident,Fdr_chan_values)):
	 (|ne(O,nil)
	   where(O -> qualification(obj_appl(obj_occ(_,O_id),Value_exprs)))
	   O_id'Ident -> Fdr_ident1
	   I'Ident -> Fdr_ident2
	   Translate_OIdent_To_OFdr_ident(Fdr_ident1,Fdr_ident2 ->Fdr_ident)
           Translate_Value_exprs_To_Fdr_chan_values(Value_exprs ->Fdr_chan_values1)
	   Translate_Ident_To_Fdr_chan_in_value(Ident1 -> Fdr_chan_value)
	   Conc_Fdr_chan_values(Fdr_chan_values1,list(Fdr_chan_value,nil) -> Fdr_chan_values)
	 ||
	   I'Ident -> Fdr_ident
	   Translate_Ident_To_Fdr_chan_in_value(Ident1 -> Fdr_chan_value)
	   where(FDR_CHAN_VALUES'list(Fdr_chan_value,nil) -> Fdr_chan_values)
         |)

  'rule' Translate_Value_expr_To_Fdr_chann_expr_in(binding(_,product(_,Bindings)),input_occ(_,I,O)->
						fdr_chan_expr(Fdr_ident,Fdr_chan_values)):
	 (|ne(O,nil)
	   where(O -> qualification(obj_appl(obj_occ(_,O_id),Value_exprs)))
	   O_id'Ident -> Fdr_ident1
	   I'Ident -> Fdr_ident2
	   Translate_OIdent_To_OFdr_ident(Fdr_ident1,Fdr_ident2 ->Fdr_ident)
           Translate_Value_exprs_To_Fdr_chan_values(Value_exprs ->Fdr_chan_values1)
	   Translate_Bindings_To_Fdr_pattern_exprs(Bindings -> Fdr_pattern_exprs)
           where(fdr_chan_value	(fdr_chan_in,fdr_patt_expr(fdr_tup_patt(Fdr_pattern_exprs))) -> Fdr_chan_value)
	   Conc_Fdr_chan_values(Fdr_chan_values1,list(Fdr_chan_value,nil) -> Fdr_chan_values)
	 ||
	   I'Ident -> Fdr_ident
	   Translate_Bindings_To_Fdr_pattern_exprs(Bindings -> Fdr_pattern_exprs)
           where(fdr_chan_value	(fdr_chan_in,fdr_patt_expr(fdr_tup_patt(Fdr_pattern_exprs))) -> Fdr_chan_value)
	   where(FDR_CHAN_VALUES'list(Fdr_chan_value,nil) -> Fdr_chan_values)
         |)

  'rule' Translate_Value_expr_To_Fdr_chann_expr_in(pattern(_,Pattern),input_occ(_,I,O)->
						fdr_chan_expr(Fdr_ident,Fdr_chan_values)):
	 (|ne(O,nil)
	   where(O -> qualification(obj_appl(obj_occ(_,O_id),Value_exprs)))
	   O_id'Ident -> Fdr_ident1
	   I'Ident -> Fdr_ident2
	   Translate_OIdent_To_OFdr_ident(Fdr_ident1,Fdr_ident2 ->Fdr_ident)
           Translate_Value_exprs_To_Fdr_chan_values(Value_exprs ->Fdr_chan_values1)
	   Translate_Pattern_To_Fdr_pattern_expr(Pattern -> Fdr_pattern_expr)
           where(fdr_chan_value	(fdr_chan_in,fdr_patt_expr(Fdr_pattern_expr)) -> Fdr_chan_value)
	   Conc_Fdr_chan_values(Fdr_chan_values1,list(Fdr_chan_value,nil) -> Fdr_chan_values)
	 ||
	   I'Ident -> Fdr_ident
	   Translate_Pattern_To_Fdr_pattern_expr(Pattern -> Fdr_pattern_expr)
           where(fdr_chan_value	(fdr_chan_in,fdr_patt_expr(Fdr_pattern_expr)) -> Fdr_chan_value)
	   where(FDR_CHAN_VALUES'list(Fdr_chan_value,nil) -> Fdr_chan_values)
         |)


'action' Translate_Ident_To_Fdr_chan_in_value(IDENT -> FDR_CHAN_VALUE)

  'rule' Translate_Ident_To_Fdr_chan_in_value(Ident  ->fdr_chan_value(fdr_chan_in,fdr_named_val(Fdr_ident))):
	 where(Ident ->Fdr_ident)



'action' Conc_Fdr_chan_values(FDR_CHAN_VALUES,FDR_CHAN_VALUES ->FDR_CHAN_VALUES)

  'rule' Conc_Fdr_chan_values(list(Fdr_chan_value,Fdr_chan_values),Fdr_chan_values1 -> list(Fdr_chan_value, Fdr_chan_values2)):
	 Conc_Fdr_chan_values(Fdr_chan_values, Fdr_chan_values1 -> Fdr_chan_values2)

  'rule' Conc_Fdr_chan_values(nil, Fdr_chan_values ->Fdr_chan_values)


--------------- Rewrite_Case_expr_To_LetIf_expr --------------------------

'action' Rewrite_Case_expr_To_LetIf_expr(VALUE_EXPR -> VALUE_EXPR)
   ---- translate to a let expr
  'rule' Rewrite_Case_expr_To_LetIf_expr(case_expr(Pos,Value_expr1,_,list(Case_branch,nil)) -> Let_value_expr):
	 where(Case_branch ->  case(_,Pattern,Value_expr2,_))
	 Pattern_match(Value_expr1, Pattern -> _,Let_defs)
         (| eq(Let_defs,nil)
            where(Value_expr2 -> Let_value_expr)
         ||
            where(let_expr(Pos,Let_defs,Value_expr2) -> Let_value_expr)
         |)

   ---- translate to a if expr
  'rule' Rewrite_Case_expr_To_LetIf_expr(case_expr (Pos,Value_expr1,_,list(Case_branch,Case_branchsTail)) -> If_value_expr):
	 where(Case_branch ->  case(_,Pattern,Value_expr2,_))
	 Pattern_match(Value_expr1, Pattern -> Value_expr_cond,Let_defs)
         where(case_expr(Pos,Value_expr1,Pos,Case_branchsTail) -> Case_expr)
         Rewrite_Case_expr_To_LetIf_expr(Case_expr -> If_value_expr_temp)
         (| eq(Let_defs,nil)
            where(Value_expr2 -> Let_value_expr_temp)
         ||
            where(let_expr(Pos,Let_defs,Value_expr2) -> Let_value_expr_temp)
         |)
	 Simplify(Value_expr_cond -> Value_expr_simp_cond)
         where(if_expr(Pos,Value_expr_simp_cond,Let_value_expr_temp,region(Pos,Pos),nil,else(Pos,If_value_expr_temp)) ->If_value_expr)
       

---------------- LET -------------------

'action' Translate_Let_defs_To_Fdr_let_defs(LET_DEFS -> FDR_LET_DEFS)

  'rule' Translate_Let_defs_To_Fdr_let_defs(list(Let_def,Let_defsTail) -> list(Fdr_let_def,Fdr_let_defsTail)):
	 Translate_Let_def_To_Fdr_let_def(Let_def -> Fdr_let_def)
	 Translate_Let_defs_To_Fdr_let_defs(Let_defsTail -> Fdr_let_defsTail)

  'rule' Translate_Let_defs_To_Fdr_let_defs(nil -> nil)


'action' Translate_Let_def_To_Fdr_let_def(LET_DEF -> FDR_LET_DEF)

  'rule' Translate_Let_def_To_Fdr_let_def(explicit(_, pattern(_,Pattern),Value_expr) -> let_def_patt(Fdr_pattern_expr,Fdr_value_expr)):
         Translate_Pattern_To_Fdr_pattern_expr(Pattern ->Fdr_pattern_expr)
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr ->Fdr_value_expr)

  'rule' Translate_Let_def_To_Fdr_let_def(explicit(_, binding(_,Binding),Value_expr) -> let_def_bin(Fdr_ident,Fdr_value_expr)):  
         where(Binding ->single(Pos,Id_or_op))
	 Translate_Binding_To_Ident(Binding -> Fdr_ident)
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr -> Fdr_value_expr)

  'rule' Translate_Let_def_To_Fdr_let_def(explicit(_, binding(_,Binding),Value_expr) -> let_def_bins(Fdr_idents,Fdr_value_expr)):
	 Translate_Binding_To_Idents(Binding -> Fdr_idents)
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr -> Fdr_value_expr)
       
  'rule' Translate_Let_def_To_Fdr_let_def(implicit(Pos,_,_) -> nil):
         Puterror(Pos)
         Putmsg("Implicit let cannot be translated\n") 

  'rule' Translate_Let_def_To_Fdr_let_def(Let_def -> nil):
         Putmsg("Let cannot be translated\n") 

--------------------------------------------------------------------------------------------
---------------------- PATTERN TRANSLATION -------------------------------------------------
--------------------------------------------------------------------------------------------

'action' Translate_Patterns_To_Fdr_pattern_exprs(PATTERNS ->FDR_PATTERN_EXPRS)

  'rule' Translate_Patterns_To_Fdr_pattern_exprs(list(Pattern,PatternsTail) -> list(Fdr_pattern_expr,Fdr_pattern_exprsTail)):
	 Translate_Pattern_To_Fdr_pattern_expr(Pattern ->Fdr_pattern_expr)
	 Translate_Patterns_To_Fdr_pattern_exprs(PatternsTail ->Fdr_pattern_exprsTail)

  'rule' Translate_Patterns_To_Fdr_pattern_exprs(nil -> nil)


'action' Translate_Pattern_To_Fdr_pattern_expr(PATTERN ->FDR_PATTERN_EXPR)

  'rule' Translate_Pattern_To_Fdr_pattern_expr(literal_pattern(_,int(Ident)) -> fdr_int_literal_patt(Fdr_ident)):
         where(Ident -> Fdr_ident)

  'rule' Translate_Pattern_To_Fdr_pattern_expr(name_occ_pattern(_, I, _) -> fdr_id_patt(Fdr_ident)):
	 I'Ident -> Id_or_op
	 Translate_Id_or_op_To_Ident(Id_or_op ->Fdr_ident)

  'rule' Translate_Pattern_To_Fdr_pattern_expr(id_pattern(_,Id_or_op) -> fdr_id_patt(Fdr_ident)):
	 Translate_Id_or_op_To_Ident(Id_or_op ->Fdr_ident)

  'rule' Translate_Pattern_To_Fdr_pattern_expr(wildcard_pattern(_) -> fdr_underscore_patt)

  'rule' Translate_Pattern_To_Fdr_pattern_expr(product_pattern (_,Patterns) -> fdr_tup_patt(Fdr_pattern_exprs)):
	 Translate_Patterns_To_Fdr_pattern_exprs(Patterns -> Fdr_pattern_exprs)
       
  'rule' Translate_Pattern_To_Fdr_pattern_expr(enum_list(_,Patterns) -> fdr_seq_patt(Fdr_pattern_exprs)):
	 Translate_Patterns_To_Fdr_pattern_exprs(Patterns -> Fdr_pattern_exprs)

  'rule' Translate_Pattern_To_Fdr_pattern_expr(conc_list(_,Patterns,Pattern) -> fdr_cat_patt(Fdr_pattern_exprs,Fdr_pattern_expr)):
	 Translate_Pattern_To_Fdr_pattern_expr(Pattern ->Fdr_pattern_expr)
	 Translate_Patterns_To_Fdr_pattern_exprs(Patterns -> Fdr_pattern_exprs)

  'rule' Translate_Pattern_To_Fdr_pattern_expr(Pattern -> fdr_underscore_patt):
print(Pattern)
Putnl()


-------------------------------------------------------------------------------------------------
------------------------------------ AXIOM_DEFS TO FDR_SCRIPT ---------------------------------------
-------------------------------------------------------------------------------------------------

'action' Translate_Axiom_defs_To_Fdr_script(AXIOM_DEFS -> FDR_SCRIPT) 

  'rule' Translate_Axiom_defs_To_Fdr_script(list(Axiom_def,Axiom_defsTail)->fdr_def(Fdr_def,Fdr_scriptTail)):
	 Translate_Axiom_def_To_Fdr_def(Axiom_def -> Fdr_def)
	 Translate_Axiom_defs_To_Fdr_script(Axiom_defsTail->Fdr_scriptTail)

  'rule' Translate_Axiom_defs_To_Fdr_script(nil -> nil)


'action' Translate_Axiom_def_To_Fdr_def(AXIOM_DEF ->FDR_DEF)

  'rule' Translate_Axiom_def_To_Fdr_def(axiom_def(Pos,_,_)->fdr_value_def(Fdr_ident,Fdr_value_expr)):
         Get_current_axioms(-> AXS)
	 Lookup_axiom(Pos, AXS -> I)
	 I'Axiom -> V
         where(V -> infix_occ(_,val_occ(_,I2,_),Op,_,Value_expr2))
	 I2'Ident -> Id_or_op
         Translate_Id_or_op_To_Ident(Id_or_op ->Fdr_ident) 
	 Translate_Value_expr_To_Fdr_value_expr(Value_expr2->Fdr_value_expr)


--  'rule' Translate_Axiom_def_To_Fdr_def(axiom_def(Pos,_,_)->fdr_value_def(Fdr_ident,Fdr_value_expr)):
--         Get_current_axioms(-> AXS)
--	 Lookup_axiom(Pos, AXS -> I)
--	 I'Axiom -> V
--         where(V -> equivalence(_,VALUE_EXPR,VALUE_EXPR,_))

--	 I2'Ident -> Id_or_op
--         Translate_Id_or_op_To_Ident(Id_or_op ->Fdr_ident) 
--	 Translate_Value_expr_To_Fdr_value_expr(Value_expr2->Fdr_value_expr)


  'rule' Translate_Axiom_def_To_Fdr_def(axiom_def(Pos,_,_)->nil):

	 Get_current_axioms(-> AXS)
	 Lookup_axiom(Pos, AXS -> I)
	 I'Axiom -> V
print(V)
Putnl



