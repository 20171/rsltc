'module' fdr_ast


'use' ast print ext env objects values types pp cc

      fdr_gen_code     -- Generates fdr code
      fdr_gen_ast
'export'
    FDR_SCRIPTS
	FDR_SCRIPT
	FDR_DEF

	FDR_CHOICES		
	FDR_CHOICE

	FDR_VALUE_EXPRS
	FDR_VALUE_EXPR
	FDR_SET_VALUE_EXPR
	FDR_SEQ_VALUE_EXPR
	FDR_BINDINGS
	FDR_BINDING
	FDR_PATTERN_EXPRS
	FDR_PATTERN_EXPR
	FDR_VALUE_LITERAL
	FDR_OP
	FDR_FUN

	FDR_CHANNEL_ID

	FDR_PROCESS_COMBINATION
	FDR_PROCESS
	FDR_PROC_VALUE_EXPR
	FDR_COMB_OPE
	FDR_CHANN_EXPR
	FDR_CHAN_VALUES
	FDR_CHAN_VALUE
	FDR_IO
	FDR_LET_DEFS
	FDR_LET_DEF

	FDR_ALPHABET
	FDR_ALPHA_EXPRS
	FDR_ALPHA_EXPR
	FDR_ENUM_ALPHA_EXPRS
	FDR_ENUM_ALPHA_EXPR

	FDR_FLAG_PROCESS_OPE


'type' FDR_SCRIPTS

       list	(head	:	FDR_SCRIPT,
		 tail	:	FDR_SCRIPTS)
       nil


'type' FDR_SCRIPT

       fdr_def	    (head   : FDR_DEF,
                     tail   : FDR_SCRIPT)
       nil


'type' FDR_DEF

       fdr_datatype_def		(id	  :	IDENT,
				 choices  :	FDR_CHOICES)
       fdr_value_def		(id	  :	IDENT,
				 value	  :	FDR_VALUE_EXPR)
       fdr_nametype_def		(id	  :	IDENT,
				 value	  :	FDR_VALUE_EXPR)
       fdr_channel_def		(id	  :	FDR_CHANNEL_ID,
				 type	  :	FDR_VALUE_EXPRS)
       fdr_process_def		(id	  :	IDENT,
			 	 args	  :	FDR_PATTERN_EXPRS,
				 proc	  :	FDR_PROCESS_COMBINATION,
                                 alph_in  :     FDR_ALPHABET,
				 alpha_out:	FDR_ALPHABET)
       ------ FOR DESTRUCTOR
       fdr_fun_def		(id	  :	IDENT,
			 	 args	  :	FDR_PATTERN_EXPRS,
				 func  	  :	FDR_VALUE_EXPR)
       ------ FOR RECONSTRUCTOR
       fdr_fun_def2		(id	  :	IDENT,
				 arg	  :	IDENT,
			 	 args	  :	FDR_PATTERN_EXPRS,
				 func  	  :	FDR_VALUE_EXPR)
       
       nil
 
---------------------------------------
-----------datatype definition---------
---------------------------------------

'type' FDR_CHOICES

       list	(head	:	FDR_CHOICE,
		 tail	:	FDR_CHOICES)
       nil


'type' FDR_CHOICE
				 
       fdr_complex_choice	(constr	:  IDENT,
				 comps	:  FDR_VALUE_EXPRS,
                                 destrs	:  FDR_SCRIPT)  -- functions definitions


---------------------------------------
-----------value definition------------
---------------------------------------


'type' FDR_VALUE_EXPRS

       list (head	:	FDR_VALUE_EXPR,
	     tail	:	FDR_VALUE_EXPRS	)
       nil


'type' FDR_VALUE_EXPR


       fdr_Unit
       fdr_Int
       fdr_Bool
       fdr_set_expr	  (FDR_SET_VALUE_EXPR)
       fdr_seq_expr	  (FDR_SEQ_VALUE_EXPR)
       fdr_tup_expr	  (FDR_VALUE_EXPRS) 
       fdr_pref_expr	  (op   :  FDR_OP,
			   expr :  FDR_VALUE_EXPR)
       fdr_infi_expr	  (expr1:  FDR_VALUE_EXPR,
			   op   :  FDR_OP,
			   expr2:  FDR_VALUE_EXPR)	
       fdr_fun_appl1	  (fun	:  FDR_FUN,
			   arg	:  FDR_VALUE_EXPR)
       fdr_fun_appl2	  (fun	:  FDR_FUN,
			   arg1	:  FDR_VALUE_EXPR,
                           arg2	:  FDR_VALUE_EXPR)
       fdr_function	  (fun	:  IDENT,
                           args	:  FDR_VALUE_EXPRS)
       fdr_patt_expr	  (FDR_PATTERN_EXPR)
       fdr_alpha_expr	  (FDR_ALPHA_EXPR)
       fdr_named_val	  (IDENT)	      
       fdr_literal_expr	  (FDR_VALUE_LITERAL)
       fdr_bracket        (FDR_VALUE_EXPR)
       fdr_let_expr	  (defs	:  FDR_LET_DEFS,
			   expr	:  FDR_VALUE_EXPR)
       fdr_if_expr	  (condition	: FDR_VALUE_EXPR,
			   then		: FDR_VALUE_EXPR,
			   else		: FDR_VALUE_EXPR)	

       -- LTL translation --

        fdr_ax_prefix ( pos	    :	POS,
                        conn	:	CONNECTIVE,
                        expr	:	VALUE_EXPR) 
        fdr_infix_occ ( pos	    :	POS,
                        left	:	VALUE_EXPR,
                        op	    :	Value_id,
                        qual	:	OPT_QUALIFICATION,
                        right	:	VALUE_EXPR)
        fdr_ax_infix  ( pos	    :	POS,
                        left	:	VALUE_EXPR,
                        conn	:	CONNECTIVE,
                        right	:	VALUE_EXPR,
                        pre	    :	POS) 
        fdr_chan_occ  ( id	    :	IDENT) 

       ---------------------

       nil


'type' FDR_SET_VALUE_EXPR

       fdr_enum_set	(exprs	:	FDR_VALUE_EXPRS)
       fdr_ranged_set	(left	:	IDENT,
			 right	:	IDENT)
       fdr_o_ranged_set	(left	:	IDENT)
       fdr_comp_set	(expr	:	FDR_VALUE_EXPR,
			 bind	:	FDR_BINDINGS,
			 condition :	FDR_VALUE_EXPR)


'type' FDR_SEQ_VALUE_EXPR

       fdr_enum_seq	(exprs	:	FDR_VALUE_EXPRS)
       fdr_ranged_seq	(left	:	IDENT,
			 right	:	IDENT)
       fdr_o_ranged_seq	(left	:	IDENT)
       fdr_comp_seq	(exprs	:	FDR_VALUE_EXPRS,
			 bind	:	FDR_BINDINGS,
			 condition :	FDR_VALUE_EXPR)

'type' FDR_BINDINGS

       list (head	:	FDR_BINDING,
	     tail	:	FDR_BINDINGS)
       nil


'type' FDR_BINDING

       fdr_binding (id	:	IDENT,
		    type:	FDR_VALUE_EXPR)
       none


'type' FDR_PATTERN_EXPRS

       list (head	:	FDR_PATTERN_EXPR,
	     tail	:	FDR_PATTERN_EXPRS)
       nil


'type' FDR_PATTERN_EXPR

       fdr_underscore_patt
       fdr_eset_patt
       fdr_int_literal_patt	(IDENT)
       fdr_id_patt		(IDENT)
       fdr_tup_patt		(FDR_PATTERN_EXPRS)
       fdr_seq_patt		(FDR_PATTERN_EXPRS)
       fdr_cat_patt		(left	:	FDR_PATTERN_EXPRS,
				 right	:	FDR_PATTERN_EXPR)        
       fdr_singl_patt		(FDR_VALUE_EXPR)
       fdr_dot_patt		(FDR_PATTERN_EXPRS)     
       

'type' FDR_VALUE_LITERAL

       fdr_bool_true
       fdr_bool_false
       fdr_int_lit		(val	:	IDENT)
	
      -- LTL tranlation
       fdr_delta
      ---------------

'type' FDR_OP

       fdr_plus,
       fdr_minus,
       fdr_product,
       fdr_quotient,
       fdr_remainder,
       fdr_equal,
       fdr_equal_equal,
       fdr_diffent,
       fdr_lt,
       fdr_gt,
       fdr_le,
       fdr_ge,
       fdr_catenation,
       fdr_len,
       fdr_and,
       fdr_or,
       fdr_not,

      -- LTL translation
       fdr_implies,
      ---------------
       nil


'type' FDR_FUN

       fdr_length,
       fdr_null,
       fdr_head,
       fdr_tail,
       fdr_concat,
       fdr_elem,
       fdr_union,
       fdr_inter,
       fdr_diff,
       fdr_Union,
       fdr_Inter,
       fdr_member,
       fdr_card,
       fdr_empty,
       fdr_set,
       fdr_Set,
       fdr_Seq,
      -- LTL translation
       fdr_R,
       fdr_U,
       fdr_W,
       fdr_G,
       fdr_F,
       fdr_X,
     -------------------
      nil


---------------------------------------
-----------channel definition----------
---------------------------------------


'type' FDR_CHANNEL_ID

       fdr_single_channel_id	(IDENT)
       fdr_multiple_channel_id	(IDENTS)


---------------------------------------
-----------process definition----------
---------------------------------------


'type' FDR_PROCESS_COMBINATION

       fdr_process		(FDR_PROCESS)
       fdr_hiding		(left		:	FDR_PROCESS_COMBINATION,
				 right		:	FDR_ALPHA_EXPR)
       fdr_proc_inf_ope		(left		:	FDR_PROCESS_COMBINATION,
				 op		:	FDR_COMB_OPE,
				 right		:	FDR_PROCESS_COMBINATION)
       fdr_pro_pre_ope		(bindings	:       FDR_BINDINGS,
				 cond		:	FDR_VALUE_EXPR,
				 op		:	FDR_COMB_OPE,
				 process	:	FDR_PROCESS_COMBINATION)			
       fdr_inf_alpha_parallel	(left		:	FDR_PROCESS_COMBINATION,
				 left_alpha	:	FDR_ALPHA_EXPR,
				 right		:	FDR_PROCESS_COMBINATION,
				 right_alpha	:	FDR_ALPHA_EXPR)
       fdr_pre_alpha_parallel	(bindings	:	FDR_BINDINGS,
				 cond		:	FDR_VALUE_EXPR,
				 alpha		:	FDR_ALPHA_EXPR,
				 process	:	FDR_PROCESS_COMBINATION)



'type' FDR_PROCESS

       fdr_proc_expr		(FDR_PROC_VALUE_EXPR)
       fdr_func_proc_expr	(id		: IDENT,
			 	 args		: FDR_VALUE_EXPRS)
       fdr_arrow_expr		(left		: FDR_CHANN_EXPR,
				 right		: FDR_PROCESS)
       fdr_arrow_comb_expr	(left		: FDR_CHANN_EXPR,
				 right		: FDR_PROCESS_COMBINATION)
       fdr_if_expr	 	(condition	: FDR_VALUE_EXPR,
				 then		: FDR_PROCESS_COMBINATION,
				 else		: FDR_PROCESS_COMBINATION)
       fdr_let_expr	        (defs		: FDR_LET_DEFS,
				 proc		: FDR_PROCESS_COMBINATION)		


'type' FDR_PROC_VALUE_EXPR

       fdr_skip
       fdr_stop
       fdr_chaos (set:	FDR_ALPHA_EXPR)


'type' FDR_COMB_OPE

       fdr_int_choice
       fdr_ext_choice


'type' FDR_CHANN_EXPR

       fdr_chan_expr	(id		: IDENT,
			 values		: FDR_CHAN_VALUES)
       nil
	

'type' FDR_CHAN_VALUES

       list	(head	:	FDR_CHAN_VALUE,
		 tail	:	FDR_CHAN_VALUES)
       nil	


'type' FDR_CHAN_VALUE

       fdr_chan_value	(io	:	FDR_IO,
			 value	:	FDR_VALUE_EXPR)


'type' FDR_IO

       fdr_chan_point  
       fdr_chan_in     
       fdr_chan_out  


'type' FDR_LET_DEFS

        list		(head	:	FDR_LET_DEF,
			 tail	:	FDR_LET_DEFS)
	nil

'type' FDR_LET_DEF

       let_def_bin   (id	: IDENT,
		      type	: FDR_VALUE_EXPR)
       let_def_bins   (ids	: IDENTS,
		      type	: FDR_VALUE_EXPR)
       let_def_patt  (patt	: FDR_PATTERN_EXPR,
		      type	: FDR_VALUE_EXPR)
       nil
       


---------------------------------------
---------alphabet definition-----------
---------------------------------------
'type' FDR_ALPHABET

       fdr_alpha_def		(id	  :	IDENT,
			 	 args	  :	FDR_PATTERN_EXPRS,
				 alph	  :	FDR_ALPHA_EXPR)
'type' FDR_ALPHA_EXPRS

       list		(head	:	FDR_ALPHA_EXPR,
			 tail	:	FDR_ALPHA_EXPRS)
       nil


'type' FDR_ALPHA_EXPR

       fdr_named_alpha		(name	:  IDENT,
				 args	:  FDR_VALUE_EXPRS,
				 alpha	:  FDR_ALPHA_EXPR)
       fdr_enum_alpha		(exprs	:  FDR_ENUM_ALPHA_EXPRS)
       fdr_fun_alpha1		(fun	:  FDR_FUN,
				 arg	:  FDR_ALPHA_EXPR)
       fdr_fun_alpha2		(fun	:  FDR_FUN,
				 arg1	:  FDR_ALPHA_EXPR,
				 arg2	:  FDR_ALPHA_EXPR)
       fdr_comp_alpha		(expr	:  FDR_ALPHA_EXPR,
			         bind	:  FDR_BINDINGS,
			         cond	:  FDR_VALUE_EXPR)		 
       fdr_empty


'type' FDR_ENUM_ALPHA_EXPRS

       list	(head	:	FDR_ENUM_ALPHA_EXPR,
		 tail	:	FDR_ENUM_ALPHA_EXPRS)
       nil	


'type' FDR_ENUM_ALPHA_EXPR

       fdr_enum_alpha_expr	(id	:	IDENT,
			         values	:	FDR_VALUE_EXPRS)


'type' FDR_FLAG_PROCESS_OPE

       fdr_Access
       fdr_No_Access




