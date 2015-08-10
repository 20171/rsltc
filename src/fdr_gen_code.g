'module' fdr_gen_code

'use' ast print ext env objects values types pp cc pvs_gen_code

      fdr
      fdr_ast          -- fdr Abstract Syntax
      fdr_gen_ast      -- Generates fdr Abstract Syntax Tree


'export'
      GenCode_Fdr_scripts
      GenCode_Fdr_value_expr   -- LTL translation


'action' GenCode_Fdr_scripts(FDR_SCRIPTS)

  'rule' GenCode_Fdr_scripts(list(Fdr_script, Fdr_scripts)):                                                              
         GenCode_Fdr_script(Fdr_script)
	 WritelnFile(1)
         GenCode_Fdr_scripts(Fdr_scripts)
 
  'rule' GenCode_Fdr_scripts(nil)


'action' GenCode_Fdr_script(FDR_SCRIPT)

  'rule' GenCode_Fdr_script(fdr_def(Fdr_def, Fdr_script)):     
         GenCode_Fdr_def(Fdr_def)
         GenCode_Fdr_script(Fdr_script)

  'rule' GenCode_Fdr_script(nil)


'action' GenCode_Fdr_def(FDR_DEF)

  'rule' GenCode_Fdr_def(fdr_datatype_def(Ident,Fdr_choices)):
         WriteFile("datatype ")
         Out_Ident(Ident)
         WriteFile(" = ")
         GenCode_Fdr_choices(Fdr_choices)
         WritelnFile(1)

  'rule' GenCode_Fdr_def(fdr_value_def(Ident, Fdr_value_expr)):
         [|ne(Fdr_value_expr,nil)
           Out_Ident(Ident)
           WriteFile(" = ")   
           GenCode_Fdr_value_expr(Fdr_value_expr)
           WritelnFile(1)
         |]

  'rule' GenCode_Fdr_def(fdr_nametype_def(Ident, Fdr_value_expr)):
         [|ne(Fdr_value_expr,nil)
           WriteFile("nametype ")
           Out_Ident(Ident)
           WriteFile(" = ")   
           GenCode_Fdr_value_expr(Fdr_value_expr)
           WritelnFile(1)
         |]
   
  'rule' GenCode_Fdr_def(fdr_channel_def(Fdr_channel_id,Fdr_value_exprs)):
         WriteFile("channel ")   
   	 GenCode_Fdr_channel_id(Fdr_channel_id)
         (|where(Fdr_value_exprs ->list(Fdr_value_expr,nil))
           [|ne(Fdr_value_expr,fdr_Unit)
             WriteFile(" : ")
           |]    
           GenCode_Fdr_value_expr(Fdr_value_expr)
         ||
           WriteFile(" : ")
           GenCode_Fdr_value_exprs_channel(Fdr_value_exprs)
         |)
         WritelnFile(1)   

  'rule' GenCode_Fdr_def(fdr_process_def(Ident,Fdr_pattern_exprs,Fdr_process_combination,Fdr_alphabet_in,Fdr_alphabet_out)):
	 WritelnFile(1) 
	 GenCode_Fdr_alphabet(Fdr_alphabet_in)
	 GenCode_Fdr_alphabet(Fdr_alphabet_out)   
	 Out_Ident(Ident)
         [|ne(Fdr_pattern_exprs,nil)
           WriteFile("(")  
	   GenCode_Fdr_pattern_exprs(Fdr_pattern_exprs)
           WriteFile(")")  
         |]   
         WriteFile(" = ")   
	 GenCode_Fdr_process_combination(Fdr_process_combination)
         WritelnFile(2) 
	 

  'rule' GenCode_Fdr_def(fdr_fun_def(Ident,Fdr_pattern_exprs,Fdr_value_expr)):
         WritelnFile(1) 
 	 Out_Ident(Ident)
         WriteFile("(")
	 GenCode_Fdr_pattern_exprs(Fdr_pattern_exprs)
         WriteFile(")")
         WriteFile(" = ") 
	 GenCode_Fdr_value_expr(Fdr_value_expr)
         WritelnFile(1)    

   'rule' GenCode_Fdr_def(fdr_fun_def2(Ident,Ident2,Fdr_pattern_exprs,Fdr_value_expr)):
         WritelnFile(1) 
 	 Out_Ident(Ident)
         WriteFile("(")
	 Out_Ident(Ident2)
	 WriteFile(",")
	 GenCode_Fdr_pattern_exprs(Fdr_pattern_exprs)
         WriteFile(")")
         WriteFile(" = ") 
	 GenCode_Fdr_value_expr(Fdr_value_expr)
         WritelnFile(1)    

 'rule' GenCode_Fdr_def(nil)



---------------------------------------
-----------datatype definition---------
---------------------------------------
'action' GenCode_Fdr_choices(FDR_CHOICES)

  'rule' GenCode_Fdr_choices(list(fdr_complex_choice(Ident,Fdr_value_exprs,Fdr_script), Fdr_choicesTail)):
	 GenCode_Fdr_choice(Ident,Fdr_value_exprs)
         [|ne(Fdr_choicesTail,nil)
           WriteFile("|") 
         |]
         
	 GenCode_Fdr_choices(Fdr_choicesTail)
         GenCode_Fdr_script(Fdr_script)
 
   -- no more Fdr_Choices
  'rule' GenCode_Fdr_choices(nil)

'action' GenCode_Fdr_choice(IDENT,FDR_VALUE_EXPRS)

  'rule' GenCode_Fdr_choice(Ident,Fdr_value_exprs):
         Out_Ident(Ident)
         [|ne(Fdr_value_exprs,nil)
           WriteFile(".") 
         |]
         GenCode_Fdr_type_components(Fdr_value_exprs)


'action' GenCode_Fdr_type_components(FDR_VALUE_EXPRS)

  'rule' GenCode_Fdr_type_components(list(Fdr_value_expr,Fdr_value_exprsTail)):
	 GenCode_Fdr_value_expr(Fdr_value_expr)
         [|ne(Fdr_value_exprsTail,nil)
           WriteFile(".") 
         |]
	 GenCode_Fdr_type_components(Fdr_value_exprsTail)
  
  'rule' GenCode_Fdr_type_components(nil)


---------------------------------------
-----------value definition------------
---------------------------------------
'action' GenCode_Fdr_value_exprs(FDR_VALUE_EXPRS)

  'rule' GenCode_Fdr_value_exprs(list(Fdr_value_expr,Fdr_value_exprsTail)):
	 GenCode_Fdr_value_expr(Fdr_value_expr)
         [|ne(Fdr_value_exprsTail,nil)
           WriteFile(",") 
         |]
	 GenCode_Fdr_value_exprs(Fdr_value_exprsTail)

  'rule' GenCode_Fdr_value_exprs(nil)


'action' GenCode_Fdr_value_expr(FDR_VALUE_EXPR)

  'rule' GenCode_Fdr_value_expr(fdr_Unit)

  'rule' GenCode_Fdr_value_expr(fdr_Int):WriteFile("Int")

  'rule' GenCode_Fdr_value_expr(fdr_Bool):WriteFile("Bool")

  'rule' GenCode_Fdr_value_expr(fdr_set_expr(Fdr_set_value_expr)):
         GenCode_Fdr_set_value_expr(Fdr_set_value_expr)

  'rule' GenCode_Fdr_value_expr(fdr_seq_expr(Fdr_seq_value_expr)):
         GenCode_Fdr_seq_value_expr(Fdr_seq_value_expr)      

  'rule' GenCode_Fdr_value_expr(fdr_tup_expr(Fdr_value_exprs)):
         WriteFile("(") 
         GenCode_Fdr_value_exprs(Fdr_value_exprs)
         WriteFile(")")        

  'rule' GenCode_Fdr_value_expr(fdr_pref_expr(Fdr_op,Fdr_value_expr)):
         [|ne(Fdr_op,nil)
           GenCode_Fdr_op(Fdr_op)
           GenCode_Fdr_value_expr(Fdr_value_expr)
         |]

  'rule' GenCode_Fdr_value_expr(fdr_infi_expr(Fdr_value_expr1,Fdr_op,Fdr_value_expr2)):
	 [|ne(Fdr_op,nil)
           GenCode_Fdr_value_expr(Fdr_value_expr1)  
           GenCode_Fdr_op(Fdr_op)       
           GenCode_Fdr_value_expr(Fdr_value_expr2)       
	 |]

  'rule' GenCode_Fdr_value_expr(fdr_fun_appl1(Fdr_fun,Fdr_value_expr)):
         [|ne(Fdr_fun,nil)
           GenCode_Fdr_fun(Fdr_fun)
           WriteFile("(")   
           GenCode_Fdr_value_expr(Fdr_value_expr)
           WriteFile(")")   
	 |]

  'rule' GenCode_Fdr_value_expr(fdr_fun_appl2(Fdr_fun,Fdr_value_expr1,Fdr_value_expr2)):
         [|ne(Fdr_fun,nil)
           GenCode_Fdr_fun(Fdr_fun)
           WriteFile("(")   
           GenCode_Fdr_value_expr(Fdr_value_expr1)
	   WriteFile(",")
           GenCode_Fdr_value_expr(Fdr_value_expr2)
           WriteFile(")")   
	 |]

  'rule' GenCode_Fdr_value_expr(fdr_function(Ident,Fdr_value_exprs)):
	 Out_Ident(Ident)
	 WriteFile("(")   
         GenCode_Fdr_value_exprs(Fdr_value_exprs)
         WriteFile(")")

  'rule' GenCode_Fdr_value_expr(fdr_patt_expr(Fdr_pattern_expr)):
         GenCode_Fdr_pattern_expr(Fdr_pattern_expr)   

  'rule' GenCode_Fdr_value_expr(fdr_alpha_expr(Fdr_alpha_expr)):
         GenCode_Fdr_alpha_expr(Fdr_alpha_expr)    

  'rule' GenCode_Fdr_value_expr(fdr_named_val(Ident)):
         Out_Ident(Ident)

  'rule' GenCode_Fdr_value_expr(fdr_literal_expr(Fdr_value_literal)):
         GenCode_Fdr_value_literal(Fdr_value_literal) 

  'rule' GenCode_Fdr_value_expr(fdr_bracket (Fdr_value_expr)):
	 WriteFile("(")   
         GenCode_Fdr_value_expr(Fdr_value_expr)
         WriteFile(")") 

  'rule' GenCode_Fdr_value_expr(fdr_let_expr(nil,Fdr_value_expr)):
         GenCode_Fdr_value_expr(Fdr_value_expr)



  'rule' GenCode_Fdr_value_expr(fdr_let_expr(Fdr_let_defs,Fdr_value_expr)):
	 where(Fdr_let_defs -> list(Fdr_let_def,Fdr_let_defsTail))
	 (|ne(Fdr_let_def, nil)
           WriteFile(" let ") 
           GenCode_Fdr_let_defs(Fdr_let_defs)
           WriteFile(" within ")
           GenCode_Fdr_value_expr(Fdr_value_expr)
         ||
           WriteFile(" 0 ")
         |)

  'rule' GenCode_Fdr_value_expr(fdr_if_expr(If_value_expr,Then_value_expr,Else_value_expr)):
  	 where(If_value_expr -> fdr_literal_expr(fdr_bool_true))
	 GenCode_Fdr_value_expr(Then_value_expr)

  'rule' GenCode_Fdr_value_expr(fdr_if_expr(If_value_expr,Then_value_expr,Else_value_expr)):
  	 where(If_value_expr -> fdr_literal_expr(fdr_bool_false))
	 GenCode_Fdr_value_expr(Else_value_expr)

  'rule' GenCode_Fdr_value_expr(fdr_if_expr(If_value_expr,Then_value_expr,Else_value_expr)):
         WriteFile(" if ")
         GenCode_Fdr_value_expr(If_value_expr)
         WriteFile(" then ")
         GenCode_Fdr_value_expr(Then_value_expr)
         WriteFile(" else ")
         GenCode_Fdr_value_expr(Else_value_expr)

  'rule' GenCode_Fdr_value_expr(nil)

------set------
'action' GenCode_Fdr_set_value_expr(FDR_SET_VALUE_EXPR)

  'rule' GenCode_Fdr_set_value_expr(fdr_enum_set(Fdr_value_exprs)):
         WriteFile("{") 
         GenCode_Fdr_value_exprs(Fdr_value_exprs) 
         WriteFile("}")           

  'rule' GenCode_Fdr_set_value_expr(fdr_ranged_set(Ident1,Ident2)):
         WriteFile("{")            
         Out_Ident(Ident1)            
         WriteFile("..") 
         Out_Ident(Ident2)            
         WriteFile("}")           

  'rule' GenCode_Fdr_set_value_expr(fdr_o_ranged_set(Ident)):
         WriteFile("{")            
         Out_Ident(Ident)            
         WriteFile("..}")           

  'rule' GenCode_Fdr_set_value_expr(fdr_comp_set(Fdr_value_expr,Fdr_bindings,Fdr_value_expr_cond)):
         WriteFile("{")         
         GenCode_Fdr_value_expr(Fdr_value_expr) 
         WriteFile("|")        
         GenCode_Fdr_bindings(Fdr_bindings)
         [|ne(Fdr_value_expr_cond,nil)
           WriteFile(",")   
         |]
         GenCode_Fdr_value_expr(Fdr_value_expr_cond)        
         WriteFile("}")                 

------seq------
'action' GenCode_Fdr_seq_value_expr(FDR_SEQ_VALUE_EXPR)

  'rule' GenCode_Fdr_seq_value_expr(fdr_enum_seq(Fdr_value_exprs)):
         WriteFile("<") 
         GenCode_Fdr_value_exprs(Fdr_value_exprs) 
         WriteFile(">")           

  'rule' GenCode_Fdr_seq_value_expr(fdr_ranged_seq(Ident1,Ident2)):
         WriteFile("<")            
         Out_Ident(Ident1)            
         WriteFile("..") 
         Out_Ident(Ident2)            
         WriteFile(">")           

  'rule' GenCode_Fdr_seq_value_expr(fdr_o_ranged_seq(Ident)):
         WriteFile("<")            
         Out_Ident(Ident)            
         WriteFile("..>")           

  'rule' GenCode_Fdr_seq_value_expr(fdr_comp_seq(Fdr_value_exprs,Fdr_bindings,Fdr_value_expr)):
         WriteFile("<")         
         GenCode_Fdr_value_exprs(Fdr_value_exprs)
         WriteFile("|")        
         GenCode_Fdr_bindings(Fdr_bindings)
         WriteFile(",")        
         GenCode_Fdr_value_expr(Fdr_value_expr)        
         WriteFile(">")                 

'action' GenCode_Fdr_bindings(FDR_BINDINGS)

  'rule' GenCode_Fdr_bindings(list(Fdr_binding,Fdr_bindingsTail)):
	 GenCode_Fdr_binding(Fdr_binding)
         [|ne(Fdr_bindingsTail,nil)
           WriteFile(",") 
         |]
	 GenCode_Fdr_bindings(Fdr_bindingsTail)
  
  'rule' GenCode_Fdr_bindings(nil)


'action' GenCode_Fdr_binding(FDR_BINDING)

  'rule' GenCode_Fdr_binding(fdr_binding(Ident,Fdr_value_expr)):
         Out_Ident(Ident)         
         WriteFile("<-") 
         GenCode_Fdr_value_expr(Fdr_value_expr)       

------pattern------
'action' GenCode_Fdr_pattern_exprs(FDR_PATTERN_EXPRS)

  'rule' GenCode_Fdr_pattern_exprs (list(Fdr_pattern_expr,Fdr_pattern_exprsTail)):
	 GenCode_Fdr_pattern_expr(Fdr_pattern_expr)
         [|ne(Fdr_pattern_exprsTail,nil)
           WriteFile(",") 
         |]
	 GenCode_Fdr_pattern_exprs(Fdr_pattern_exprsTail)

  'rule' GenCode_Fdr_pattern_exprs(nil)


'action' GenCode_Fdr_pattern_expr(FDR_PATTERN_EXPR) 

  'rule' GenCode_Fdr_pattern_expr(fdr_underscore_patt): WriteFile("_") 

  'rule' GenCode_Fdr_pattern_expr(fdr_eset_patt): WriteFile("{}") 

  'rule' GenCode_Fdr_pattern_expr(fdr_int_literal_patt(Ident)): Out_Ident(Ident)

  'rule' GenCode_Fdr_pattern_expr(fdr_id_patt(Ident)): Out_Ident(Ident)

  'rule' GenCode_Fdr_pattern_expr(fdr_tup_patt(Fdr_pattern_exprs)):
         WriteFile("(") 
         GenCode_Fdr_pattern_exprs(Fdr_pattern_exprs)
         WriteFile(")") 
 
  'rule' GenCode_Fdr_pattern_expr(fdr_seq_patt(Fdr_pattern_exprs)):
         WriteFile("<") 
         GenCode_Fdr_pattern_exprs(Fdr_pattern_exprs)
         WriteFile(">")
  
  'rule' GenCode_Fdr_pattern_expr(fdr_cat_patt(Fdr_pattern_exprs,Fdr_pattern_expr)):
	 WriteFile("<") 
         GenCode_Fdr_pattern_exprs(Fdr_pattern_exprs) 
	 WriteFile(">")  
         WriteFile("^") 
         GenCode_Fdr_pattern_expr(Fdr_pattern_expr)

  'rule' GenCode_Fdr_pattern_expr(fdr_singl_patt(Fdr_value_expr)):
         GenCode_Fdr_value_expr(Fdr_value_expr)  

  'rule' GenCode_Fdr_pattern_expr(fdr_dot_patt(Fdr_pattern_exprs)):
         GenCode_Fdr_dot_patt(Fdr_pattern_exprs) 


'action' GenCode_Fdr_dot_patt(FDR_PATTERN_EXPRS) 

  'rule' GenCode_Fdr_dot_patt(list(Fdr_pattern_expr,Fdr_pattern_exprsTail)):
	 GenCode_Fdr_pattern_expr(Fdr_pattern_expr)
         [|ne(Fdr_pattern_exprsTail,nil)
           WriteFile(".") 
         |]
	 GenCode_Fdr_dot_patt(Fdr_pattern_exprsTail)
  
  'rule' GenCode_Fdr_dot_patt(nil)


-----literal-------
'action' GenCode_Fdr_value_literal(FDR_VALUE_LITERAL)

  'rule' GenCode_Fdr_value_literal(fdr_bool_true): WriteFile(" true ")

  'rule' GenCode_Fdr_value_literal(fdr_bool_false): WriteFile(" false ")

  'rule' GenCode_Fdr_value_literal(fdr_int_lit(Ident)): Out_Ident(Ident)


-----prefix, infix operator----------
'action' GenCode_Fdr_op (FDR_OP)

  'rule' GenCode_Fdr_op(fdr_plus):WriteFile("+")

  'rule' GenCode_Fdr_op(fdr_minus):WriteFile("-")

  'rule' GenCode_Fdr_op(fdr_product):WriteFile("*")

  'rule' GenCode_Fdr_op(fdr_quotient):WriteFile("/")

  'rule' GenCode_Fdr_op(fdr_remainder):WriteFile("%")

  'rule' GenCode_Fdr_op(fdr_equal):WriteFile("==")

  'rule' GenCode_Fdr_op(fdr_diffent):WriteFile("!=")

  'rule' GenCode_Fdr_op(fdr_lt):WriteFile("<")

  'rule' GenCode_Fdr_op(fdr_gt):WriteFile(">")

  'rule' GenCode_Fdr_op(fdr_le):WriteFile("<=")

  'rule' GenCode_Fdr_op(fdr_ge):WriteFile(">=")

  'rule' GenCode_Fdr_op(fdr_catenation):WriteFile("^")

  'rule' GenCode_Fdr_op(fdr_len):WriteFile("#")

  'rule' GenCode_Fdr_op(fdr_and):WriteFile(" and ")

  'rule' GenCode_Fdr_op(fdr_or):WriteFile(" or ")

  'rule' GenCode_Fdr_op(fdr_not):WriteFile(" not ")

  'rule' GenCode_Fdr_op(nil):WriteFile(" ")


-------function application-------
'action' GenCode_Fdr_fun(FDR_FUN)

  'rule' GenCode_Fdr_fun(fdr_length): WriteFile(" length")

  'rule' GenCode_Fdr_fun(fdr_null): WriteFile(" null")

  'rule' GenCode_Fdr_fun(fdr_head): WriteFile(" head")

  'rule' GenCode_Fdr_fun(fdr_tail): WriteFile(" tail")

  'rule' GenCode_Fdr_fun(fdr_concat): WriteFile(" concat")

  'rule' GenCode_Fdr_fun(fdr_elem): WriteFile(" elem")

  'rule' GenCode_Fdr_fun(fdr_union): WriteFile(" union")

  'rule' GenCode_Fdr_fun(fdr_inter): WriteFile(" inter")

  'rule' GenCode_Fdr_fun(fdr_diff): WriteFile(" diff")

  'rule' GenCode_Fdr_fun(fdr_Union): WriteFile(" Union")

  'rule' GenCode_Fdr_fun(fdr_Inter): WriteFile(" Inter")

  'rule' GenCode_Fdr_fun(fdr_card): WriteFile(" card")

  'rule' GenCode_Fdr_fun(fdr_empty): WriteFile(" empty")

  'rule' GenCode_Fdr_fun(fdr_set): WriteFile(" set")

  'rule' GenCode_Fdr_fun(fdr_Set): WriteFile(" Set")

  'rule' GenCode_Fdr_fun(fdr_Seq): WriteFile(" Seq")

  'rule' GenCode_Fdr_fun(fdr_member): WriteFile(" member")

  'rule' GenCode_Fdr_fun(nil):



---------------------------------------
-----------channel definition----------
---------------------------------------
'action' GenCode_Fdr_channel_id(FDR_CHANNEL_ID)

  'rule' GenCode_Fdr_channel_id(fdr_single_channel_id(Ident)):Out_Ident(Ident)

  'rule' GenCode_Fdr_channel_id(fdr_multiple_channel_id(Idents)):
         GenCode_Fdr_out_idents_channel(Idents)


'action' GenCode_Fdr_out_idents_channel(IDENTS) 

  'rule' GenCode_Fdr_out_idents_channel(list(Ident,IdentsTail)):
	 Out_Ident(Ident)
         [|ne(IdentsTail,nil)
           WriteFile(",") 
         |]
	 GenCode_Fdr_out_idents_channel(IdentsTail)
  
  'rule' GenCode_Fdr_out_idents_channel(nil)


'action' GenCode_Fdr_value_exprs_channel(FDR_VALUE_EXPRS)

  'rule' GenCode_Fdr_value_exprs_channel(list(Fdr_value_expr,list(Fdr_value_expr1,Fdr_value_exprsTail))):
	 GenCode_Fdr_value_expr(Fdr_value_expr)
	 [|ne(Fdr_value_expr1,fdr_Unit)
           WriteFile(".") 
         |]
         where(FDR_VALUE_EXPRS'list(Fdr_value_expr1,Fdr_value_exprsTail) -> Fdr_value_exprs)
	 GenCode_Fdr_value_exprs_channel (Fdr_value_exprs)

  'rule' GenCode_Fdr_value_exprs_channel(list(Fdr_value_expr,Fdr_value_exprsTail)):
	 GenCode_Fdr_value_expr(Fdr_value_expr)
	 [|ne(Fdr_value_exprsTail,nil)
           WriteFile(".") 
         |]
	 GenCode_Fdr_value_exprs_channel(Fdr_value_exprsTail)

  'rule' GenCode_Fdr_value_exprs_channel(nil)



---------------------------------------
-----------process definition----------
---------------------------------------
'action' GenCode_Fdr_process_combination(FDR_PROCESS_COMBINATION)

  'rule' GenCode_Fdr_process_combination(fdr_process(Fdr_process)):
         GenCode_Fdr_process(Fdr_process)

  'rule' GenCode_Fdr_process_combination(fdr_hiding(Fdr_process_combination,Fdr_alpha_expr)): 
  	 Is_empty_alphabet(Fdr_alpha_expr)
  	 GenCode_Fdr_process_combination(Fdr_process_combination)

  'rule' GenCode_Fdr_process_combination(fdr_hiding(Fdr_process_combination,Fdr_alpha_expr)):
         --WriteFile("(")    
         GenCode_Fdr_process_combination(Fdr_process_combination)
         WriteFile("\\")    
         GenCode_Fdr_alpha_expr(Fdr_alpha_expr)
         --WriteFile(")")    

  'rule' GenCode_Fdr_process_combination(fdr_proc_inf_ope(Fdr_process_combination1,Fdr_comb_ope,Fdr_process_combination2)):
         --WriteFile("(")    
         GenCode_Fdr_process_combination(Fdr_process_combination1)   
         GenCode_Fdr_comb_ope(Fdr_comb_ope)   
         GenCode_Fdr_process_combination(Fdr_process_combination2) 
         --WriteFile(")")    

  'rule' GenCode_Fdr_process_combination(fdr_pro_pre_ope(Fdr_bindings,Fdr_value_expr_cond,Fdr_comb_ope,Fdr_process_combination)):
         GenCode_Fdr_comb_ope(Fdr_comb_ope)    
         GenCode_Fdr_bindings_proc(Fdr_bindings)
	 [|ne(Fdr_value_expr_cond,nil)
           WriteFile(",")   
         |]
         GenCode_Fdr_value_expr(Fdr_value_expr_cond) 
         WriteFile("@")
         GenCode_Fdr_process_combination(Fdr_process_combination)    

  'rule' GenCode_Fdr_process_combination(fdr_inf_alpha_parallel(Fdr_process_combination1,Fdr_alpha_expr1,
                                                                Fdr_process_combination2,Fdr_alpha_expr2)):
         WriteFile("(")    
         GenCode_Fdr_process_combination(Fdr_process_combination1)
         WriteFile("[")
         GenCode_Fdr_alpha_expr(Fdr_alpha_expr1)   
         WriteFile("||")  
         GenCode_Fdr_alpha_expr(Fdr_alpha_expr2) 
         WriteFile("]")   
         GenCode_Fdr_process_combination(Fdr_process_combination2) 
         WriteFile(")")   

  'rule' GenCode_Fdr_process_combination(fdr_pre_alpha_parallel(Fdr_bindings,Fdr_value_expr_cond,Fdr_alpha_expr,Fdr_process_combination)):
         WriteFile("||")      
         GenCode_Fdr_bindings_proc(Fdr_bindings)	 
	 [|ne(Fdr_value_expr_cond,nil)
           WriteFile(",")   
         |]
         GenCode_Fdr_value_expr(Fdr_value_expr_cond) 
         WriteFile("@")
         WriteFile("[") 
         GenCode_Fdr_alpha_expr(Fdr_alpha_expr) 
         WriteFile("]")    
         GenCode_Fdr_process_combination(Fdr_process_combination)    



'action' GenCode_Fdr_bindings_proc(FDR_BINDINGS)

  'rule' GenCode_Fdr_bindings_proc(list(Fdr_binding,Fdr_bindingsTail)):
	 GenCode_Fdr_binding_proc(Fdr_binding)
         [|ne(Fdr_bindingsTail,nil)
           WriteFile(",") 
         |]
	 GenCode_Fdr_bindings_proc(Fdr_bindingsTail)

  'rule' GenCode_Fdr_bindings_proc(nil)


'action' GenCode_Fdr_binding_proc(FDR_BINDING)

  'rule' GenCode_Fdr_binding_proc(fdr_binding(Ident,Fdr_value_expr)):
         Out_Ident(Ident)         
         WriteFile(":") 
         GenCode_Fdr_value_expr(Fdr_value_expr)  

-------process-------
'action' GenCode_Fdr_process(FDR_PROCESS) 

  'rule' GenCode_Fdr_process(fdr_proc_expr(Fdr_proc_value_expr)):
         GenCode_Fdr_proc_value_expr(Fdr_proc_value_expr) 

  'rule' GenCode_Fdr_process(fdr_func_proc_expr(Ident,Fdr_value_exprs)):
         Out_Ident(Ident)    
         [|ne(Fdr_value_exprs,nil)
           WriteFile("(")  
	   GenCode_Fdr_value_exprs(Fdr_value_exprs)
           WriteFile(")")  
         |] 
  
  'rule' GenCode_Fdr_process(fdr_arrow_expr(Fdr_chann_expr,Fdr_process)):
         GenCode_Fdr_chann_expr(Fdr_chann_expr)
         WriteFile(" -> (") 
         GenCode_Fdr_process(Fdr_process)
	 WriteFile(")")

  'rule' GenCode_Fdr_process(fdr_arrow_comb_expr(Fdr_chann_expr,Fdr_process_combination)):
         GenCode_Fdr_chann_expr(Fdr_chann_expr)
         WriteFile(" -> ") 
	 WriteFile("(")
         GenCode_Fdr_process_combination(Fdr_process_combination)
	 WriteFile(")") 

  'rule' GenCode_Fdr_process(fdr_if_expr(Fdr_value_expr,Fdr_process_combination1,Fdr_process_combination2)):
  	 where(Fdr_value_expr -> fdr_literal_expr(fdr_bool_true))
	 GenCode_Fdr_process_combination(Fdr_process_combination1)

  'rule' GenCode_Fdr_process(fdr_if_expr(Fdr_value_expr,Fdr_process_combination1,Fdr_process_combination2)):
  	 where(Fdr_value_expr -> fdr_literal_expr(fdr_bool_false))
	 GenCode_Fdr_process_combination(Fdr_process_combination2)

  'rule' GenCode_Fdr_process(fdr_if_expr(Fdr_value_expr,Fdr_process_combination1,Fdr_process_combination2)):
         WriteFile(" if ")
         GenCode_Fdr_value_expr(Fdr_value_expr)
         WriteFile(" then ")
         GenCode_Fdr_process_combination(Fdr_process_combination1)
         WriteFile(" else ")
         GenCode_Fdr_process_combination(Fdr_process_combination2)

  'rule' GenCode_Fdr_process(fdr_let_expr(nil,Fdr_process_combination)):
         GenCode_Fdr_process_combination(Fdr_process_combination)

  'rule' GenCode_Fdr_process(fdr_let_expr(Fdr_let_defs,Fdr_process_combination)):
         WriteFile(" let ") 
         GenCode_Fdr_let_defs(Fdr_let_defs)
         WriteFile(" within ")
         GenCode_Fdr_process_combination(Fdr_process_combination)


'action' GenCode_Fdr_proc_value_expr(FDR_PROC_VALUE_EXPR)

  'rule' GenCode_Fdr_proc_value_expr(fdr_skip):WriteFile(" SKIP") 

  'rule' GenCode_Fdr_proc_value_expr(fdr_stop):WriteFile(" STOP")

  'rule' GenCode_Fdr_proc_value_expr(fdr_chaos(Fdr_alpha_expr)):
	 WriteFile(" CHAOS")
	 WriteFile("(")
         GenCode_Fdr_alpha_expr(Fdr_alpha_expr)
	 WriteFile(")") 

'action' GenCode_Fdr_comb_ope(FDR_COMB_OPE)

  'rule' GenCode_Fdr_comb_ope(fdr_int_choice):WriteFile(" |~| ")

  'rule' GenCode_Fdr_comb_ope(fdr_ext_choice):WriteFile(" [] ")


------ chan expr------
'action' GenCode_Fdr_chann_expr(FDR_CHANN_EXPR)

  'rule' GenCode_Fdr_chann_expr(fdr_chan_expr(Ident,Fdr_chan_values)):
         Out_Ident(Ident)
         GenCode_Fdr_chan_values(Fdr_chan_values)

  'rule' GenCode_Fdr_chann_expr(nil)


'action' GenCode_Fdr_chan_values(FDR_CHAN_VALUES)

  'rule' GenCode_Fdr_chan_values(list(Fdr_chan_value, Fdr_chan_valuesTail)):
	 GenCode_Fdr_chan_value(Fdr_chan_value)
	 GenCode_Fdr_chan_values(Fdr_chan_valuesTail)
  
  'rule' GenCode_Fdr_chan_values(nil)


'action' GenCode_Fdr_chan_value(FDR_CHAN_VALUE)

  'rule' GenCode_Fdr_chan_value(fdr_chan_value(Fdr_io,Fdr_value_expr)):
	 GenCode_Fdr_io(Fdr_io)
         GenCode_Fdr_value_expr(Fdr_value_expr)


'action' GenCode_Fdr_io(FDR_IO)

  'rule' GenCode_Fdr_io(fdr_chan_point):WriteFile(".")

  'rule' GenCode_Fdr_io(fdr_chan_in):WriteFile("?")

  'rule' GenCode_Fdr_io(fdr_chan_out):WriteFile("!")

----- let ------------------
'action' GenCode_Fdr_let_defs(FDR_LET_DEFS) 

  'rule' GenCode_Fdr_let_defs(list(Fdr_let_def,Fdr_let_defsTail)):
	 GenCode_Fdr_let_def(Fdr_let_def)
         [|ne(Fdr_let_defsTail,nil)
           WritelnFile(1) 
         |]
	 GenCode_Fdr_let_defs(Fdr_let_defsTail)
  
  'rule' GenCode_Fdr_let_defs(nil)



'action' GenCode_Fdr_let_def(FDR_LET_DEF)

  'rule' GenCode_Fdr_let_def(let_def_bin(Ident,Fdr_value_expr)):
         Out_Ident(Ident)         
         WriteFile(" = ") 
         GenCode_Fdr_value_expr(Fdr_value_expr) 

  'rule' GenCode_Fdr_let_def(let_def_bins(Idents,Fdr_value_expr)):
         WriteFile("(")
         GenCode_Idents(Idents) 
         WriteFile(")")       
         WriteFile(" = ") 
         GenCode_Fdr_value_expr(Fdr_value_expr) 

  'rule' GenCode_Fdr_let_def(let_def_patt(Fdr_pattern_expr,Fdr_value_expr)):
         GenCode_Fdr_pattern_expr(Fdr_pattern_expr)       
         WriteFile(" = ") 
         GenCode_Fdr_value_expr(Fdr_value_expr) 

  'rule' GenCode_Fdr_let_def(nil)


---------------------------------------
---------alphabet definition-----------
---------------------------------------
'action' GenCode_Fdr_alphabet(FDR_ALPHABET)

  'rule' GenCode_Fdr_alphabet(fdr_alpha_def(Ident,Fdr_pattern_exprs,Fdr_alpha)):
	 Out_Ident(Ident)
         [|ne(Fdr_pattern_exprs,nil)
           WriteFile("(")       
	   GenCode_Fdr_pattern_exprs(Fdr_pattern_exprs)
           WriteFile(") ")
         |]
         WriteFile(" = ")   
	 GenCode_Fdr_alpha_expr(Fdr_alpha)
         WritelnFile(1) 


'action' GenCode_Fdr_alpha_exprs(FDR_ALPHA_EXPRS) 

  'rule' GenCode_Fdr_alpha_exprs(list(Fdr_alpha_expr,Fdr_alpha_exprsTail)):
         GenCode_Fdr_alpha_expr(Fdr_alpha_expr)
         [|ne(Fdr_alpha_exprsTail,nil)
           WriteFile(",") 
         |]
	 GenCode_Fdr_alpha_exprs(Fdr_alpha_exprsTail)
  
  'rule' GenCode_Fdr_alpha_exprs(nil)


'action' GenCode_Fdr_alpha_expr(FDR_ALPHA_EXPR) 

  'rule' GenCode_Fdr_alpha_expr(Alpha):
         (|where(Alpha ->fdr_named_alpha(Ident,Fdr_value_exprs,_))
           Out_Ident(Ident)
           [|ne(Fdr_value_exprs,nil)
             WriteFile("(")
	     GenCode_Fdr_value_exprs(Fdr_value_exprs)
             WriteFile(")")
           |]
         ||
           where(Alpha ->fdr_enum_alpha(Fdr_enum_alpha_exprs))
           WriteFile("{|") 
           GenCode_Fdr_enum_alpha_exprs(Fdr_enum_alpha_exprs)
           WriteFile("|}")
         || 
	   where(Alpha ->fdr_fun_alpha1(Fdr_fun,Fdr_alpha_expr)) 
           GenCode_Fdr_fun(Fdr_fun)
           WriteFile("(")
           GenCode_Fdr_alpha_expr(Fdr_alpha_expr)
           WriteFile(")")
         ||
	   where(Alpha ->fdr_fun_alpha2(Fdr_fun,Fdr_alpha_expr1,Fdr_alpha_expr2)) 
           GenCode_Fdr_fun(Fdr_fun)
           WriteFile("(")
           GenCode_Fdr_alpha_expr(Fdr_alpha_expr1)
	   WriteFile(",")
	   GenCode_Fdr_alpha_expr(Fdr_alpha_expr2)
           WriteFile(")")
         ||
	   where(Alpha ->fdr_comp_alpha(Fdr_alpha_expr,Fdr_bindings,Fdr_value_expr_cond)) 
           WriteFile("{|")
           (|where(Fdr_alpha_expr -> fdr_enum_alpha(Fdr_enum_alpha_exprs))
	     GenCode_Fdr_enum_alpha_exprs(Fdr_enum_alpha_exprs)
           ||    
             GenCode_Fdr_alpha_expr(Fdr_alpha_expr)
           |) 
           WriteFile("|")        
           GenCode_Fdr_bindings(Fdr_bindings)
           [|ne(Fdr_value_expr_cond,nil)
             WriteFile(",")   
           |]
           GenCode_Fdr_value_expr(Fdr_value_expr_cond)        
           WriteFile("|}")	   
	 ||
           where(Alpha ->fdr_empty) 
	   WriteFile("{") 
           WriteFile("}")
         |)



'action' GenCode_Fdr_enum_alpha_exprs(FDR_ENUM_ALPHA_EXPRS)

  'rule' GenCode_Fdr_enum_alpha_exprs(list(Fdr_enum_alpha_expr,Fdr_enum_alpha_exprsTail)):
         GenCode_Fdr_enum_alpha_expr(Fdr_enum_alpha_expr)
         [|ne(Fdr_enum_alpha_exprsTail,nil)
           WriteFile(",") 
         |]
	 GenCode_Fdr_enum_alpha_exprs(Fdr_enum_alpha_exprsTail)
  
  'rule' GenCode_Fdr_enum_alpha_exprs(nil)


'action' GenCode_Fdr_enum_alpha_expr(FDR_ENUM_ALPHA_EXPR)

  'rule' GenCode_Fdr_enum_alpha_expr(fdr_enum_alpha_expr(Ident,Fdr_value_exprs)):
         Out_Ident(Ident)
         GenCode_Fdr_alpha_value_exprs(Fdr_value_exprs)


'action' GenCode_Fdr_alpha_value_exprs(FDR_VALUE_EXPRS)

  'rule' GenCode_Fdr_alpha_value_exprs(list(Fdr_value_expr,Fdr_value_exprsTail))
	 WriteFile(".")
	 GenCode_Fdr_value_expr(Fdr_value_expr)
	 GenCode_Fdr_alpha_value_exprs(Fdr_value_exprsTail)

  'rule' GenCode_Fdr_alpha_value_exprs(nil)

'action' GenCode_Idents(IDENTS) 

  'rule' GenCode_Idents(list(Ident,IdentsTail)):
	 Out_Ident(Ident)
         [|ne(IdentsTail,nil)
           WriteFile(",") 
         |]
	 GenCode_Idents(IdentsTail)
  
  'rule' GenCode_Idents(nil) 
