
-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the pretty printer

'module' pp

'use' ast ext print types env

'export' Pretty_print Pretty_print_value Id_or_op_to_string Ids_to_object
	 Literal_to_string Op_to_string	Connec_to_string

'action' Pretty_print(LIB_MODULE,INT)

  'rule' Pretty_print(V,L):
	 Libmod_to_box(V -> B)
	 Reopen()
	 Nlcomtag <- 0
	 Nlcom <- string("")
	 Add_comm(B -> CB)
	 Init_var(L)
	 Print_box(CB,h_box -> IR,C)
	 Curline <- 0
	 Curcol <- 0
	 Print_inte(IR)
	 Putstdnl

'action' Pretty_print_value(VALUE_EXPR,INT)

  'rule' Pretty_print_value(V,L):
	 ValExpr_to_box(V -> B)
	 Init_var(L)
	 Print_box(B,h_box -> IR,C)
	 Curline <- 0
	 Curcol <- 0
	 Putstdnl
	 Print_inte(IR)
	 Putstdnl

---------------------------------------------------------------------------
--modules
---------------------------------------------------------------------------
'action' Libmod_to_box(LIB_MODULE -> BOX)

  'rule' Libmod_to_box(scheme(_,IDS,_,D) -> B):
	 ScheDef_to_box(D -> DB)
	 where(box("",list(string("scheme"),list(DB,nil))," ","",h_box) -> D1)
	 (|
	   ne(IDS,nil)
	   Filenames_to_boxes(IDS -> BS)
	   where(box("",BS,", ","",hv_box) -> IB)
	   where(box("",list(IB,list(string("\t"),list(D1,nil))),"","",v_box) -> B)
	 ||
	   where(D1 -> B)
	 |)    

  'rule' Libmod_to_box(object(_,IDS,_,D) -> B):
	 LibObjDef_to_box(D -> DB)
	 where(box("",list(string("object"),list(DB,nil))," ","",h_box) -> D1)
	 (|
	   ne(IDS,nil)
	   Filenames_to_boxes(IDS -> BS)
	   where(box("",BS,", ","",hv_box) -> IB)
	   where(box("",list(IB,list(string("\t"),list(D1,nil))),"","",v_box) -> B)
	 ||
	   where(D1 -> B)
	 |)    

  'rule' Libmod_to_box(theory(_,IDS,_,D) -> B):
	 TheoDef_to_box(D -> DB)
	 where(box("",list(string("theory"),list(DB,nil))," ","",h_box) -> D1)
	 (|
	   ne(IDS,nil)
	   Filenames_to_boxes(IDS -> BS)
	   where(box("",BS,", ","",hv_box) -> IB)
	   where(box("",list(IB,list(string("\t"),list(D1,nil))),"","",v_box) -> B)
	 ||
	   where(D1 -> B)
	 |)    

  'rule' Libmod_to_box(devt_relation(_,IDS,_,D) -> B):
	 DevtDef_to_box(D -> DB)
	 where(box("",list(string("devt_relation"),list(DB,nil))," ","",h_box) -> D1)
	 (|
	   ne(IDS,nil)
	   Filenames_to_boxes(IDS -> BS)
	   where(box("",BS,", ","",hv_box) -> IB)
	   where(box("",list(IB,list(string("\t"),list(D1,nil))),"","",v_box) -> B)
	 ||
	   where(D1 -> B)
	 |)    

------------
--lib_object_def added for consistency with scheme_def etc CWG
------------

'action' LibObjDef_to_box(OBJECT_DEF -> BOX)

  'rule' LibObjDef_to_box(odef(_,Id,TS,C) -> B):
	 id_to_string(Id -> S)
	 ClasExpr_to_box(C -> CB)
	 where(box("",list(CB,nil),"","",i_box) -> C1)
	 (|
	   eq(TS, nil)
	   where(box("",list(string(S),list(C1,nil))," : ","",h_box) -> B)
	 ||
	   Typings_to_boxes(TS -> BS)
	   where(box("",BS,", ","",hv_box) -> B1) 
	   where(box("[",list(B1,nil),"","]",i_box) -> PB)
	   where(box("",list(string(S),list(PB,nil)),"","",h_box) -> NB)  
	   where(box("",list(NB,list(C1,nil))," : ","",h_box) -> B)
	 |)

------------
--scheme_def
------------
'action' ScheDef_to_box(SCHEME_DEF -> BOX)
 
  'rule' ScheDef_to_box(sdef(_,Id,PS,C) -> B):
	 id_to_string(Id -> S)
	 ClasExpr_to_box(C -> CB)
	 where(box("",list(CB,nil),"","",i_box) -> C1)
	 (|
	    eq(PS,nil)
	    where(box("",list(string(S),list(C1,nil))," = ","",h_box) -> B)
	  ||
	    ObjDefs_to_boxes(PS -> BS)
	    where(box("",BS,", ","",hv_box) -> B1) 
	    where(box("(",list(B1,nil),"",")",i_box) -> PB)
	    where(box("",list(string(S),list(PB,nil)),"","",h_box) -> NB)  
	    where(box("",list(NB,list(C1,nil))," = ","",h_box) -> B)
	 |)

-------------
--theory_def
-------------
'action' TheoDef_to_box(THEORY_DEF -> BOX)

  'rule' TheoDef_to_box(theory_def(_,ID,AXS) -> B):
	 id_to_string(ID -> S)
	 (|
	    ne(AXS,nil)
	    AxiDefs_to_boxes(AXS -> BS)
	    where(box("",BS,", ","",v_box) -> AB)
	    where(box("",list(AB,nil),"","",i_box) -> A1)
	    where(box("",list(string("axiom"),list(A1,list(string("end"),nil))),"","",v_box) -> A2)
	    where(box("",list(string(S),list(A2,nil))," :","",h_box) -> B)
	  ||
	    where(box("axiom",nil,""," end",h_box) -> A1)
	    where(box("",list(string(S),list(A1,nil))," : ","",h_box) -> B)
         |) 

-----------------
--devt_relation
-----------------
'action' DevtDef_to_box(DEVT_RELATION_DEF -> BOX)

  'rule' DevtDef_to_box(devt_relation_def(_,Id,Id1,Id2,E) -> B):
	 id_to_string(Id -> S)
	 id_to_string(Id1 -> S1)
	 id_to_string(Id2 -> S2)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(EB,nil),"","",i_box) -> E1)
	 where(box("(",list(string(S1),list(string(S2),nil))," for ",")",h_box)->SB1)
	 where(box("",list(string(S),list(SB1,nil)),"","",h_box) -> SB)
	 where(box("",list(SB,list(E1,nil))," : ","",hov_box) -> B)
---------------------------------------------------------------------------
--declaration
---------------------------------------------------------------------------
'action' Decls_to_boxes(DECLS -> BOXES)

  'rule' Decls_to_boxes(nil -> nil):

  'rule' Decls_to_boxes(list(H,nil) -> list(B,nil)):
	 Decl_to_box(H -> B)

  'rule' Decls_to_boxes(list(H,T) -> list(HB,list(string("\t"),TBS))):
	 Decl_to_box(H -> HB)
	 Decls_to_boxes(T -> TBS)

'action' Decl_to_box(DECL -> BOX)

  'rule' Decl_to_box(object_decl(_,X)->box("",list(string("object"),list(B,nil))," ","",hov_box)):
	 ObjDefs_to_boxes(X -> BS)
	 where(box("",BS,", ","",hov_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B)

  'rule' Decl_to_box(type_decl(_,X) -> box("",list(string("type"),list(B,nil))," ","",hov_box)):
	 TypeDefs_to_boxes(X -> BS)
	 where(box("",BS,", ","",hov_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B)

  'rule' Decl_to_box(value_decl(_,X) -> box("",list(string("value"),list(B,nil))," ","",hov_box)):
	 Valsp <- 0
	 First <- 0
	 ValDefs_to_boxes(X -> BS)
	 where(box("",BS,", ","",v_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B)

  'rule' Decl_to_box(variable_decl(_,X) -> box("",list(string("variable"),list(B,nil))," ","",hov_box)):
	 VarDefs_to_boxes(X -> BS)
	 where(box("",BS,", ","",hov_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B)

  'rule' Decl_to_box(channel_decl(_,X) ->
	 box("",list(string("channel"),list(B,nil))," ", "",hov_box)):
	 ChanDefs_to_boxes(X -> BS)
	 where(box("",BS,", ","",hov_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B)

  'rule' Decl_to_box(axiom_decl(_,X) -> box("",list(string("axiom"),list(B,nil))," ","",hov_box)):
	 AxiDefs_to_boxes(X -> BS)
	 where(box("",BS,", ","",hov_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B)

  'rule' Decl_to_box(test_case_decl(_,X) -> box("",list(string("test_case"),list(B,nil))," ","",hov_box)):
	 TcDefs_to_boxes(X -> BS)
	 where(box("",BS,", ","",hov_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B)

  'rule' Decl_to_box(trans_system_decl(_,X) -> box("",list(string("transition_system"),list(B,nil))," ","",hov_box)):
	 TsDefs_to_boxes(X -> BS)
	 where(box("",BS,", ","",hov_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B)

  'rule' Decl_to_box(property_decl(_,X) -> box("",list(string("ltl_assertion"),list(B,nil))," ","",hov_box)):
	 PropDefs_to_boxes(X -> BS)
	 where(box("",BS,", ","",hov_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B)

--------------
--object_ decl
--------------
'action' ObjDefs_to_boxes(OBJECT_DEFS -> BOXES)

  'rule' ObjDefs_to_boxes(list(H,T) -> list(HB,TBS)):
	 ObjDef_to_box(H -> HB)
	 ObjDefs_to_boxes(T -> TBS)

  'rule' ObjDefs_to_boxes(nil -> nil):

'action' ObjDef_to_box(OBJECT_DEF -> BOX)

  'rule' ObjDef_to_box(odef(_,Id,nil,C)
	 -> box("",list(string(S),list(B1,nil))," : ","",hov_box)):
	 id_to_string(Id -> S)
	 ClasExpr_to_box(C -> B)
	 where(box("",list(B,nil),"","",i_box) -> B1)

  'rule' ObjDef_to_box(odef(_,Id,TS,C) -> box("",list(T,list(B2,nil))," : ","",hov_box)):
	 id_to_string(Id -> S)
	 Typings_to_boxes(TS -> BS)
	 where(box("",BS,", ","",hv_box) -> B1)
	 where(box("[",list(B1,nil),"","]",i_box) -> TB)
	 where(box("",list(string(S),list(TB,nil)),"","",h_box) -> T)
	 ClasExpr_to_box(C -> B)
	 where(box("",list(B,nil),"","",i_box) -> B2)

------------
--type_decl
------------
'action' TypeDefs_to_boxes(TYPE_DEFS -> BOXES)

  'rule' TypeDefs_to_boxes(list(H,T) -> list(HB,TBS)):
	 TypeDef_to_box(H -> HB)
	 TypeDefs_to_boxes(T -> TBS)

  'rule' TypeDefs_to_boxes(nil -> nil):

'action' TypeDef_to_box(TYPE_DEF -> BOX)

  'rule' TypeDef_to_box(sort(_,X) -> string(S)):
	 id_to_string(X -> S)

  'rule' TypeDef_to_box(abbrev(_,Id,T) ->
	 box("",list(string(S),list(B,nil))," = ","",hv_box)):
	 id_to_string(Id -> S)
	 TypeExpr_to_box(T -> B1)
	 where(box("",list(B1,nil),"","",hv_box) -> B2)
	 where(box("",list(B2,nil),"","",i_box) -> B)

  'rule' TypeDef_to_box(variant(_,Id,CHS) ->
	 box("",list(string(S),list(B,nil))," == ","",hov_box)):
	 id_to_string(Id -> S)
	 Variants_to_boxes(CHS -> BS)
	 where(box("",BS," | ","",hov_box) -> CB)
	 where(box("",list(CB,nil),"","",i_box) -> B)

  'rule' TypeDef_to_box(record(_,Id,CS) ->
	 box("",list(string(S),list(CB,nil))," :: ","",hv_box)):
	 id_to_string(Id -> S)
	 Compons_to_boxes(CS -> BS)
	 where(box("",BS,"   ","",hov_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> CB)
     
  'rule' TypeDef_to_box(union(_,Id,NS) ->
	 box("",list(string(S),list(B,nil))," = ","",hv_box)):
	 id_to_string(Id -> S)
	 Choices_to_boxes(NS -> BS)
	 where(box("",BS," | ","",hv_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B)

'action' Variants_to_boxes(VARIANTS -> BOXES)

  'rule' Variants_to_boxes(list(H,T) -> list(HB,TBS)):
	 Variant_to_box(H -> HB)
	 Variants_to_boxes(T -> TBS)

  'rule' Variants_to_boxes(nil -> nil):

'action' Variant_to_box(VARIANT -> BOX)

  'rule' Variant_to_box(record(_,C,CS) -> B):
	 Constru_to_box(C -> CB)
	 (|
	    ne(CS,nil)
	    Compons_to_boxes(CS -> BS)
	    where(box("",BS,", ","",hov_box) -> B1)
	    where(box("(",list(B1,nil),"",")",i_box) -> B2)
	    where(box("",list(CB,list(B2,nil)),"","",hv_box) -> B)
	  ||
	    where(CB -> B)
	 |)

'action' Constru_to_box(CONSTRUCTOR -> BOX)

  'rule' Constru_to_box(constructor(_,X) -> string(S)):
	 Id_or_op_to_string(X -> S)

  'rule' Constru_to_box(wildcard -> string("_")):

'action' Compons_to_boxes(COMPONENTS -> BOXES)

  'rule' Compons_to_boxes(list(H,T) -> list(HB,TBS)):
	 Compon_to_box(H -> HB)
	 Compons_to_boxes(T -> TBS)

  'rule' Compons_to_boxes(nil -> nil):

'action' Compon_to_box(COMPONENT -> BOX)

  'rule' Compon_to_box(component(_,destructor(_,Id),T,nil) -> B):
	 Id_or_op_to_string(Id -> S)
	 TypeExpr_to_box(T -> TB)
	 where(box("",list(TB,nil),"","",i_box) -> T1)
	 where(box("",list(string(S),list(T1,nil))," : ","",hv_box) -> B)

  'rule' Compon_to_box(component(_,destructor(_,Id),T,reconstructor(_,X)) -> B):
	 Id_or_op_to_string(Id -> S)
	 TypeExpr_to_box(T -> TB)
	 Id_or_op_to_string(X -> S1)
	 where(box("",list(TB,list(string(S1),nil))," <-> ","",hv_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B2)
	 where(box("",list(string(S),list(B2,nil))," : ","",hv_box) ->B)

  'rule' Compon_to_box(component(_,nil,T,reconstructor(_,X)) -> B):
	 TypeExpr_to_box(T -> TB)
	 Id_or_op_to_string(X -> S)
	 where(box("",list(TB,list(string(S),nil))," <-> ","",hv_box) -> B)

  'rule' Compon_to_box(component(_,nil,T,nil) -> B):
	 TypeExpr_to_box(T -> B)

'action' Choices_to_boxes(CHOICES -> BOXES)

  'rule' Choices_to_boxes(list(H,T) -> list(HB,TBS)):
	 Choice_to_box(H -> HB)
	 Choices_to_boxes(T -> TBS)

  'rule' Choices_to_boxes(nil -> nil):

'action' Choice_to_box(CHOICE -> BOX)

  'rule' Choice_to_box(choice(_,N) -> B):
	 Name_to_box(N -> B)

  'rule' Choice_to_box(nil -> string("_")):

-------------
--value_ decl
-------------
'action' ValDefs_to_boxes(VALUE_DEFS -> BOXES)

  'rule' ValDefs_to_boxes(list(H,T) -> list(HB,TBS)):
	 ValDef_to_box(H -> HB)
	 ValDefs_to_boxes(T -> TBS)

  'rule' ValDefs_to_boxes(nil -> nil):

'action' ValDef_to_box(VALUE_DEF -> BOX)

  'rule' ValDef_to_box(typing(_,T) -> B):
	 Typing_to_box(T -> B1)
	 (|
	    Valsp -> VS
	    eq(VS,1)
	    Valsp <- 0
	    where(box("",list(string("\t"),list(B1,nil)),"","",v_box) -> B)
	  ||
	    where(B1 -> B)
	 |)
	 [|
	   First -> FI
	   eq(FI,0)
	   First <- 1
	 |]  
     
  'rule' ValDef_to_box(exp_val(_,T,E) -> B):
	 Typing_to_box(T -> TB)
	 ValExpr_to_box(E -> EB1)
	 where(box("",list(EB1,nil),"","",i_box) -> EB)
	 where(box("",list(TB,list(EB,nil))," = ","",hv_box) -> B1)
	 (|
	    Valsp -> VS
	    eq(VS,1)
	    Valsp <- 0
	    where(box("",list(string("\t"),list(B1,nil)),"","",v_box) -> B)
	  ||
	    where(B1 -> B)
	 |)
	 [|
	   First -> FI
	   eq(FI,0)
	   First <- 1
	 |]  

  'rule' ValDef_to_box(imp_val(_,T,R) -> B):
	 Typing_to_box(T -> TB)
	 Restr_to_box(R -> RB1)
	 where(box("",list(RB1,nil),"","",i_box) -> RB)
	 where(box("",list(TB,list(RB,nil))," :- ","",hv_box) -> B1)
	 (|
	    Valsp -> VS
	    eq(VS,1)
	    Valsp <- 0
	    where(box("",list(string("\t"),list(B1,nil)),"","",v_box) -> B)
	  ||
	    where(B1 -> B)
	 |)
	 [|
	   First -> FI
	   eq(FI,0)
	   First <- 1
	 |]  

  'rule' ValDef_to_box(exp_fun(P,T,A,E,PO,PR,_) -> B3):
	 Typing_to_box(T -> TB)
	 Formalapp_to_box(A -> AB)
	 (|
	   Lower_expr_precedence(E, 14)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> EB)
	 where(box("",list(EB,nil),"","",i_box) -> D)
	 where(box("",list(AB,list(D,nil))," is ","",hov_box) -> D1)
	 Pre_cond_to_boxes(PR -> PBS)
	 (|
	   where(PO -> post(POST))
	   Post_cond_to_box(POST -> POB)
	   where(box("",list(D1,list(POB,PBS))," ","",hov_box) -> B)
	 ||
	   where(box("",list(D1,PBS)," ","",hov_box) -> B)
	 |)
	 where(box("",list(TB,list(B,nil)),"","",v_box) -> B2)
	 (|
	    First -> FI
	    eq(FI,0)
	    First <- 1
	    where(B2 -> B3)
	  ||  
	    where(box("",list(string("\t"),list(B2,nil)),"","",v_box) -> B3)
	 |)
	 Valsp <- 1

  'rule' ValDef_to_box(imp_fun(_,T,A,E,PR) -> B3):
	 Typing_to_box(T -> TB)
	 Formalapp_to_box(A -> AB)
	 Post_cond_to_boxes(E -> EB1,EB2)
	 Pre_cond_to_boxes(PR -> PBS)
	 where(box("",list(AB,list(EB1,nil))," ","",hov_box) -> D1)
	 where(box("",list(D1,list(EB2,nil))," ","",hov_box) -> D2)
	 where(box("",list(D2,PBS)," ","",hov_box) -> B)
	 where(box("",list(TB,list(B,nil)),"","",v_box) -> B2)
	 (|
	    First -> FI
	    eq(FI,0)
	    First <- 1
	    where(B2 -> B3)
	  ||
	    where(box("",list(string("\t"),list(B2,nil)),"","",v_box) -> B3)
	 |)
	 Valsp <- 1

'action' Formalapp_to_box(FORMAL_FUNCTION_APPLICATION -> BOX)

  'rule' Formalapp_to_box(form_appl(_,id_op(Id),PS) -> box("",list(string(S),BS),"","",hv_box)):
	 id_to_string(Id -> S)
	 Formparams_to_boxes(PS -> BS)

  'rule' Formalapp_to_box(form_appl(_,op_op(Id),list(PS,nil)) -> B1):
	 Op_to_string(Id -> S)
	 (|
	    where(PS -> form_parm(_,list(B,nil)))
	    Bind_to_box(B -> BB)
	    where(box(S,list(BB,nil),"","",hv_box) -> B1)
	  ||
	    where(PS -> form_parm(_,list(L,list(R,nil))))
	    Bind_to_box(L -> LB)
	    Bind_to_box(R -> RB)
	    where(box("",list(LB,list(RB,nil)),S,"",hv_box) -> B1)
	 |)   	       

'action' Formparams_to_boxes(FORMAL_FUNCTION_PARAMETERS -> BOXES)

  'rule' Formparams_to_boxes(list(H,T) -> list(HB,TBS)):
	 Formparam_to_box(H -> HB)
	 Formparams_to_boxes(T -> TBS)

  'rule' Formparams_to_boxes(nil -> nil):

'action' Formparam_to_box(FORMAL_FUNCTION_PARAMETER -> BOX)

  'rule' Formparam_to_box(form_parm(_,X) ->box("(",list(B,nil),"",")",i_box)):
	 Binds_to_boxes(X -> BS)
	 where(box("",BS,", ","",hv_box) -> B)

---------------
--variable_decl
---------------
'action' VarDefs_to_boxes(VARIABLE_DEFS -> BOXES)

  'rule' VarDefs_to_boxes(list(H,T) -> list(HB,TBS)):
	 VarDef_to_box(H ->HB)
	 VarDefs_to_boxes(T -> TBS)

  'rule' VarDefs_to_boxes(nil -> nil):

'action' VarDef_to_box(VARIABLE_DEF -> BOX)

  /*'rule' VarDef_to_box(single(_,Id,T,initial(array_expr(_,_,V))) -> B):
	 id_to_string(Id -> S)
	 TypeExpr_to_box(T -> TB1)
	 where(box("",list(TB1,nil),"","",i_box) -> TB)
	 ValExpr_to_box(V -> VB1)
	 where(box("",list(VB1,nil),"","",i_box) -> VB)
	 where(box("",list(string(S),list(TB,nil))," : ","",hv_box) ->B1)
	 where(box("",list(B1,list(VB,nil))," := ","",hv_box) ->B)*/

  'rule' VarDef_to_box(single(_,Id,T,I) -> B):
	 id_to_string(Id -> S)
	 TypeExpr_to_box(T -> TB1)
	 where(box("",list(TB1,nil),"","",i_box) -> TB)
	 (|
	    eq(I,nil)
	    where(box("",list(string(S),list(TB,nil))," : ","",hv_box) ->B)
	  ||
	    where(I -> initial(V))
	    ValExpr_to_box(V -> VB1)
	    where(box("",list(VB1,nil),"","",i_box) -> VB)
	    where(box("",list(string(S),list(TB,nil))," : ","",hv_box) ->B1)
	    where(box("",list(B1,list(VB,nil))," := ","",hv_box) ->B)
	 |)
 
  'rule' VarDef_to_box(multiple(_,Ids,T) -> B):
	 Idents_to_boxes(Ids -> BS)
	 where(box("",BS,", ","",hv_box) -> IB)
	 TypeExpr_to_box(T -> TB1)
	 where(box("",list(TB1,nil),"","",i_box) -> TB)
	 where(box("",list(IB,list(TB,nil))," : ","",hov_box) -> B)

--------------
--channel_decl
--------------
'action' ChanDefs_to_boxes(CHANNEL_DEFS -> BOXES)

  'rule' ChanDefs_to_boxes(list(H,T) -> list(HB,TBS)):
	 ChanDef_to_box(H ->HB)
	 ChanDefs_to_boxes(T -> TBS)

  'rule' ChanDefs_to_boxes(nil -> nil):

'action' ChanDef_to_box(CHANNEL_DEF -> BOX)

  'rule' ChanDef_to_box(single(_,Id,T) -> B):
	 id_to_string(Id -> S)
	 TypeExpr_to_box(T -> TB)
	 where(box("",list(TB,nil),"","",i_box) -> B1)
	 where(box("",list(string(S),list(B1,nil))," : ","",hv_box) ->B)

  'rule' ChanDef_to_box(multiple(_,Ids,T) -> B):
	 Idents_to_boxes(Ids -> BS)
	 where(box("",BS,", ","",hv_box) -> IB)
	 TypeExpr_to_box(T -> TB)
	 where(box("",list(TB,nil),"","",i_box) -> B1)
	 where(box("",list(IB,list(B1,nil))," : ","",hov_box) -> B)

--------------
--axiom_decl
--------------
'action' AxiDefs_to_boxes(AXIOM_DEFS -> BOXES)

  'rule' AxiDefs_to_boxes(list(H,T) -> list(HB,TBS)):
	 AxiDef_to_box(H ->HB)
	 AxiDefs_to_boxes(T -> TBS)

  'rule' AxiDefs_to_boxes(nil -> nil):


'action' AxiDef_to_box(AXIOM_DEF -> BOX)

  'rule' AxiDef_to_box(axiom_def(_,nil,E) -> B):
	 ValExpr_to_box(E -> B)

  'rule' AxiDef_to_box(axiom_def(_,ident(N),E) -> box("",list(NB,list(B,nil)),"","",v_box)):
	 id_to_string(N -> S)
	 where(box("[",list(string(S),nil),"","]",h_box) -> NB)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(EB,nil),"","",i_box) -> B)

--------------
--test_case_decl
--------------
'action' TcDefs_to_boxes(TEST_CASE_DEFS -> BOXES)

  'rule' TcDefs_to_boxes(list(H,T) -> list(HB,TBS)):
	 TcDef_to_box(H -> HB)
	 TcDefs_to_boxes(T -> TBS)

  'rule' TcDefs_to_boxes(nil -> nil):


'action' TcDef_to_box(TEST_CASE_DEF -> BOX)

  'rule' TcDef_to_box(test_case_def(_,nil,E) -> B):
	 ValExpr_to_box(E -> B)

  'rule' TcDef_to_box(test_case_def(_,ident(N),E) -> box("",list(NB,list(B,nil)),"","",v_box)):
	 id_to_string(N -> S)
	 where(box("[",list(string(S),nil),"","]",h_box) -> NB)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(EB,nil),"","",i_box) -> B)

--------------
--trans_sys_decl
--------------
'action' TsDefs_to_boxes(TRANSITION_SYS_DEFS -> BOXES)

  'rule' TsDefs_to_boxes(list(H,T) -> list(HB,TBS)):
	 TsDef_to_box(H -> HB)
	 TsDefs_to_boxes(T -> TBS)

  'rule' TsDefs_to_boxes(nil -> nil):

'action' TsDef_to_box(TRANSITION_SYS_DEF -> BOX)

  'rule' TsDef_to_box(trans_sys_def(_,N,SD) -> box("",list(NB,list(SDB,nil)),"","",v_box)):
	 id_to_string(N -> S)
	 where(box("[",list(string(S),nil),"","]",h_box) -> NB)
	 SysDesc_to_box(SD -> SDB)

'action' SysDesc_to_box(SYSTEM_DESCRIPTION -> BOX)

  'rule' SysDesc_to_box(desc(Inp,Loc,Trans) -> B):
         SysVars_to_box(Inp -> IB)
	 where(box("",list(IB,nil),"","",i_box) -> IB1)
	 where(box("",list(string("in"),list(IB1,nil))," ","",hov_box) -> B1)
	 SysVars_to_box(Loc -> LB)
	 where(box("",list(LB,nil),"","",i_box) -> LB1)
	 where(box("",list(string("local"),list(LB1,nil))," ","",hov_box) -> B2)
	 Transition_Operator_to_boxes(Trans -> TBS)
	 where(box("",TBS,"","",v_box) -> TB)
	 where(box("",list(TB,nil),"","",i_box) -> TB1)
	 where(box("",list(string("in"),list(TB1,list(string("end"),nil)))," ","",hov_box) -> B3)
	 where(box("",list(B1,list(B2,list(B3,nil)))," ","",v_box) -> B)

  'rule' SysDesc_to_box(no_input(Loc,Trans) -> B):
	 SysVars_to_box(Loc -> LB)
	 where(box("",list(LB,nil),"","",i_box) -> LB1)
	 where(box("",list(string("local"),list(LB1,nil))," ","",hov_box) -> B2)
	 Transition_Operator_to_boxes(Trans -> TBS)
	 where(box("",TBS,"","",v_box) -> TB)
	 where(box("",list(TB,nil),"","",i_box) -> TB1)
	 where(box("",list(string("in"),list(TB1,list(string("end"),nil)))," ","",hov_box) -> B3)
	 where(box("",list(B2,list(B3,nil))," ","",v_box) -> B)

'action' SysVars_to_box(DECL -> BOX)

  'rule' SysVars_to_box(variable_decl(_, DS) -> B):
	 VarDefs_to_boxes(DS -> BS)
	 where(box("",BS,", ","",hov_box) -> B)

'action' Transition_Operator_to_boxes(TRANSITION_OPERATOR -> BOXES)
  'rule' Transition_Operator_to_boxes(equal_priority(LEFT, RIGHT, EXTRA) -> B)
         Transition_Operator_to_boxes(LEFT -> BL)
         Transition_Operator_to_boxes(RIGHT -> BR)
         Concatenate_boxes(BL, list(string("[=]"),BR) -> B)

  'rule' Transition_Operator_to_boxes(greater_priority(LEFT, RIGHT, EXTRA) -> B)
         Transition_Operator_to_boxes(LEFT -> BL)
         Transition_Operator_to_boxes(RIGHT -> BR)
         Concatenate_boxes(BL, list(string("[>]"),BR) -> B)

  'rule' Transition_Operator_to_boxes(bracketed(TO, EXTRA) -> list(BRes,nil)):
         Transition_Operator_to_boxes(TO -> BTemp)
         Concatenate_boxes(list(string("("), BTemp), list(string(")"),nil) -> B)
         where(box("  ", B, " ","  ",hov_box) -> BRes)

  'rule' Transition_Operator_to_boxes(guarded_command(CMD, EXTRA) -> list(B,nil)):
         Cmd_to_box(CMD -> B)

'action' Concatenate_boxes(BOXES, BOXES -> BOXES)
  'rule' Concatenate_boxes(nil, nil -> nil)
  'rule' Concatenate_boxes(B, nil -> B)
  'rule' Concatenate_boxes(nil, B -> B)

  'rule' Concatenate_boxes(list(H1, T1), B2 -> list(H1, BRes))
         Concatenate_boxes(T1,B2 -> BRes)

'action' Cmd_to_box(GUARDED_COMMAND -> BOX)

  'rule' Cmd_to_box(else_cmd(nil,nil) -> string("else ==>")):

  'rule' Cmd_to_box(else_cmd(ident(N), nil) -> B):
	 id_to_string(N -> S)
	 where(box("[",list(string(S),nil),"","]",h_box) -> NB)
	 where(box("",list(NB,list(string(" else ==>"),nil)),"","",h_box) -> B)

  'rule' Cmd_to_box(else_cmd(nil,US) -> B):
	 Updates_to_boxes(US -> BS)
	 where(box("",BS,", ","",h_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B2)
	 where(box("",list(string("else ==> "),list(B2,nil)),"","",h_box) -> B)

  'rule' Cmd_to_box(else_cmd(ident(N),US) -> B):
	 id_to_string(N -> S)
	 where(box("[",list(string(S),nil),"","]",h_box) -> NB)
	 Updates_to_boxes(US -> BS)
	 where(box("",BS,", ","",h_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B2)
	 where(box("",list(NB,list(string(" else ==> "),list(B2,nil))),"","",h_box) -> B)

  'rule' Cmd_to_box(guarded_cmd(nil,G,US) -> B):
	 ValExpr_to_box(G -> GB)
	 Updates_to_boxes(US -> BS)
	 where(box("",BS,", ","",h_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B2)
	 where(box("",list(GB,list(string(" ==> "),list(B2, nil))),"","",h_box) -> B)

  'rule' Cmd_to_box(guarded_cmd(ident(N),G,US) -> B):
	 id_to_string(N -> S)
	 where(box("[",list(string(S),nil),"","]",h_box) -> NB)
	 ValExpr_to_box(G -> GB)
	 Updates_to_boxes(US -> BS)
	 where(box("",BS,", ","",hov_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B2)
	 where(box("",list(GB,list(string("==>"),nil))," ","",h_box) -> B3)
	 where(box("",list(B3, list(B2, nil))," ","",hov_box) -> B4)
	 where(box("",list(NB,list(B4,nil))," ","",v_box) -> B)

  'rule' Cmd_to_box(comprehended_cmd(TPS,_,Cmd) -> B):
	 Typings_to_boxes(TPS -> TBS)
	 where(box("",TBS,", ","",hv_box) -> TB)
	 where(box("",list(TB,nil),"","",i_box) -> ITB)
	 Cmd_to_box(Cmd -> CB)
	 where(box("",list(CB,nil),"","",i_box) -> ICB)
	 where(box("",list(string("[=]"),list(ITB,list(string(":-"),nil)))," ","",hov_box) -> B1)
	 where(box("(",list(B1,list(ICB,nil))," ",")",hov_box) -> B)

'action' Updates_to_boxes(COMMANDS -> BOXES)

  'rule' Updates_to_boxes(list(Cmd, Cmds) -> list(B, BS)):
	 Update_to_box(Cmd -> B)
	 Updates_to_boxes(Cmds -> BS)

  'rule' Updates_to_boxes(nil -> nil):

'action' Update_to_box(COMMAND -> BOX)

  'rule' Update_to_box(cmd(_,N,E) -> B):
	 Name_to_box(N -> NB)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(EB,nil),"","",i_box) -> IEB)
	 where(box("",list(NB,list(string(" = "),list(IEB,nil))),"","",hov_box)-> B)

  'rule' Update_to_box(array_cmd(_,N,I,V) -> B)
         Name_to_box(N -> NB)
         ValExprs_to_boxes(I -> IB)
         ValExpr_to_box(V -> VB)
         where(box("",list(VB,nil),"","",i_box) -> VEB)
         where(box("[",IB,"][","]",i_box) -> IEB)
	 where(box("",list(NB,list(IEB,list(string(" = "),list(VEB,nil)))),"","",hov_box)-> B)


--------------
-- property_decl
--------------

'action' PropDefs_to_boxes(PROPERTY_DECLS -> BOXES)

  'rule' PropDefs_to_boxes(list(P, PS) -> list(B, BS)):
	 PropDef_to_box(P -> B)
	 PropDefs_to_boxes(PS -> BS)

  'rule' PropDefs_to_boxes(nil -> nil):

'action' PropDef_to_box(PROPERTY_DECL -> BOX)

  'rule' PropDef_to_box(property_def(_, N, S, P) -> B):
	 id_to_string(N -> NS)
	 id_to_string(S -> SS)
	 where(box("[",list(string(NS),nil),"","]",h_box) -> NB)
	 where(box("",list(string(SS),list(string(" |-"),nil)),"","",h_box) -> SB)
	 ValExpr_to_box(P -> PB)
	 where(box("",list(PB,nil),"","",i_box) -> IPB)
	 where(box("",list(SB,list(IPB,nil))," ","",hov_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> IB1)
	 where(box("",list(NB,list(IB1,nil))," ","",hov_box) -> B)

---------------------------------------------------------------------------
--class expr
---------------------------------------------------------------------------
'action' ClasExpr_to_box(CLASS -> BOX)

  'rule' ClasExpr_to_box(basic(X)->box("",list(string("class"),list(X1,list(string("end"),nil)))," ","",hov_box)):
	 Decls_to_boxes(X -> BS)
	 where(box("",BS," ","",hov_box) -> XB)
	 where(box("",list(XB,nil),"","",i_box) -> X1)

  'rule' ClasExpr_to_box(extend(C1,C2) ->box("",list(EB,list(B2,nil))," ","",hv_box)):
	 ClasExpr_to_box(C1 -> BC)
	 where(box("",list(BC,nil),"","",i_box) -> B1)
	 where(box("",list(string("extend"),list(B1,list(string("with"),nil)))," ","",hov_box) -> EB)
	 ClasExpr_to_box(C2 -> B2)

  'rule' ClasExpr_to_box(hide(H,C) ->box("",list(H2,list(CB,nil))," ","",hv_box)):
	 Defineds_to_boxes(H -> BS)
	 ClasExpr_to_box(C -> CB)
	 where(box("",BS,", ","",hv_box) -> HB)
	 where(box("",list(HB,nil),"","",i_box) -> H1)
	 where(box("",list(string("hide"),list(H1,list(string("in"),nil)))," ","",hov_box) -> H2)

  'rule' ClasExpr_to_box(rename(R,C) -> B):
	 Renames_to_boxes(R -> BS)
	 ClasExpr_to_box(C -> CB)
	 where(box("",BS,", ","",hv_box) -> RB)
	 where(box("",list(RB,nil),"","",i_box) -> RB1)
	 where(box("",list(string("use"),list(RB1,list(string("in"),nil)))," ","",hov_box) -> C1)
	 where(box("",list(C1,list(CB,nil))," ","",hov_box) -> B)

  'rule' ClasExpr_to_box(with(_,OS,C) -> B):
	 ObjExprs_to_boxes(OS -> BS)
	 where(box("",BS,", ","",hv_box) -> B1)
	 where(box("",list(B1,nil),"","",i_box) -> B2)
	 where(box("",list(string("with"),list(B2,list(string("in"),nil)))," ","",hov_box) -> OB)
	 ClasExpr_to_box(C -> CB)
	 where(box("",list(OB,list(CB,nil))," ","",hov_box) -> B)
	 
  'rule' ClasExpr_to_box(instantiation(N,PARMS) -> B):
	 Instant_to_box(N,PARMS -> B)

  'rule' ClasExpr_to_box(nil -> box("class",nil,""," end",h_box)):

------
--hide
------
'action' Defineds_to_boxes(DEFINEDS -> BOXES)

  'rule' Defineds_to_boxes(list(H,T) -> list(HB,TBS)):
	 Defined_to_box(H -> HB)
	 Defineds_to_boxes(T -> TBS)

  'rule' Defineds_to_boxes(nil -> nil)

'action' Defined_to_box(DEFINED -> BOX)

  'rule' Defined_to_box(def_name(_,X) -> string(S)):
	 Id_or_op_to_string(X -> S)

  'rule' Defined_to_box(disamb(_,N,T) ->
	 box("",list(string(S),list(TB,nil))," : ","",h_box)):
	 Id_or_op_to_string(N -> S)
	 TypeExpr_to_box(T -> TB)

-----------
--rename
-----------
'action' Renames_to_boxes(RENAMES -> BOXES)

  'rule' Renames_to_boxes(list(H,T) -> list(HB,TBS)):
	 Rename_to_box(H -> HB)
	 Renames_to_boxes(T -> TBS)

  'rule' Renames_to_boxes(nil -> nil):

'action' Rename_to_box(RENAME -> BOX)

  'rule' Rename_to_box(rename(I1,I2) ->box("",list(B1,list(B2,nil))," for ","",hv_box)):
	 Defined_to_box(I1 -> B1)
	 Defined_to_box(I2 -> B2)	 

---------------
--instantiation
---------------
'action' Instant_to_box(NAME,OBJECT_EXPRS -> BOX)

  'rule' Instant_to_box(N,nil -> B):
	 Name_to_box(N -> B)

  'rule' Instant_to_box(N,PARMS ->box("",list(B,list(PB,nil)),"","",hv_box)):
	 Name_to_box(N -> B)
	 ObjExprs_to_boxes(PARMS -> BS)
	 where(box("",BS,", ","",hv_box) -> B1)
	 where(box("(",list(B1,nil),"",")",i_box) -> PB)
---------------------------------------------------------------------------
--object expr
---------------------------------------------------------------------------
'action' ObjExprs_to_boxes(OBJECT_EXPRS -> BOXES)

  'rule' ObjExprs_to_boxes(list(H,T) -> list(HB,TBS)):
	 ObjExpr_to_box(H -> HB)
	 ObjExprs_to_boxes(T -> TBS)

  'rule' ObjExprs_to_boxes(nil -> nil):

'action' ObjExpr_to_box(OBJECT_EXPR -> BOX)
 
  'rule' ObjExpr_to_box(obj_name(N) -> B):
	 Name_to_box(N -> B)

  'rule' ObjExpr_to_box(obj_appl(O,A) ->box("",list(OB,list(AB,nil)),"","",hv_box)):
	 ObjExpr_to_box(O -> OB)
	 ValExprs_to_boxes(A -> BS)
	 where(box("",BS,", ","",hv_box) -> B1)
	 where(box("[",list(B1,nil),"","]",i_box) -> AB)

  'rule' ObjExpr_to_box(obj_array(TS,O)
	 ->box("[|",list(TB,list(OB1,nil))," :- ","|]",hv_box)):
	 Typings_to_boxes(TS -> TBS)
	 ObjExpr_to_box(O -> OB)
	 where(box("",list(OB,nil),"","",i_box) -> OB1)
	 where(box("",TBS,", ","",hv_box) -> TB)

  'rule' ObjExpr_to_box(obj_fit(O,F) ->box("",list(OB,list(FB,nil)),"","",hv_box)):
	 ObjExpr_to_box(O -> OB)
	 Renames_to_boxes(F -> FBS)
	 where(box("",FBS,", ","",hv_box) -> FB1)
	 where(box("{",list(FB1,nil),"","}",i_box) -> FB)

  'rule' ObjExpr_to_box(obj_occ(P, Id) -> B):
--	 (|
--	   Id'Qualifier -> list(Id1,Ids)
--	   Ids_to_object(P, list(Id1,Ids) -> Obj)
--	   ObjExpr_to_box(qual_occ(P, Obj, Id) -> B)
--	 ||
	   Id'Ident -> ID
	   id_to_string(ID -> S)
	   where(string(S) -> B)
--	 |)

  'rule' ObjExpr_to_box(qual_occ(_, Obj, Id) ->
		         box("",list(B,list(string(S),nil)),".","",h_box)):
	 Id'Ident -> ID
	 id_to_string(ID -> S)
	 ObjExpr_to_box(Obj -> B)
	 

---------------------------------------------------------------------------
--type expr
---------------------------------------------------------------------------
'action' TypeExpr_to_box(TYPE_EXPR -> BOX)

  'rule' TypeExpr_to_box(unit -> string("Unit")):

  'rule' TypeExpr_to_box(bool -> string("Bool")):

  'rule' TypeExpr_to_box(int -> string("Int")):

  'rule' TypeExpr_to_box(nat -> string("Nat")):

  'rule' TypeExpr_to_box(real -> string("Real")):

  'rule' TypeExpr_to_box(text -> string("Text")):

  'rule' TypeExpr_to_box(char -> string("Char")):

  'rule' TypeExpr_to_box(time -> string("Time")):

  'rule' TypeExpr_to_box(defined(Id, Q) -> B):
	 Definedtype_to_box(Id, Q -> B)

  'rule' TypeExpr_to_box(named_type(N) -> B):
	 Name_to_box(N -> B)

  'rule' TypeExpr_to_box(product(X) -> box("",BS," >< ","",hv_box)):
	 Prod_type_to_boxes(X -> BS)

  'rule' TypeExpr_to_box(fin_set(X) -> box("",list(B,list(string("-set"),nil)),"","",h_box)):
	 (|
	   Lower_type_precedence(X, 1)
	   where(X -> X1)
	 ||
	   where(TYPE_EXPR'bracket(X) -> X1)
	 |)
	 TypeExpr_to_box(X1 -> B)

  'rule' TypeExpr_to_box(infin_set(X) -> box("",list(B,list(string("-infset"),nil)),"","",h_box)):
	 (|
	   Lower_type_precedence(X, 1)
	   where(X -> X1)
	 ||
	   where(TYPE_EXPR'bracket(X) -> X1)
	 |)
	 TypeExpr_to_box(X1 -> B)

  'rule' TypeExpr_to_box(fin_list(X) -> box("",list(B,list(string("-list"),nil)),"","",h_box)):
	 (|
	   Lower_type_precedence(X, 1)
	   where(X -> X1)
	 ||
	   where(TYPE_EXPR'bracket(X) -> X1)
	 |)
	 TypeExpr_to_box(X1 -> B)

  'rule' TypeExpr_to_box(infin_list(X) -> box("",list(B,list(string("-inflist"),nil)),"","",h_box)):
	 (|
	   Lower_type_precedence(X, 1)
	   where(X -> X1)
	 ||
	   where(TYPE_EXPR'bracket(X) -> X1)
	 |)
	 TypeExpr_to_box(X1 -> B)

  'rule' TypeExpr_to_box(fin_map(D,R) ->box("",list(DB,list(RB,nil))," -m-> ","",hov_box)):
	 (|
	   Lower_type_precedence(D, 3)
	   where(D -> D1)
	 ||
	   where(TYPE_EXPR'bracket(D) -> D1)
	 |)
	 TypeExpr_to_box(D1 -> DB)
	 TypeExpr_to_box(R -> RB1)
	 where(box("",list(RB1,nil),"","",i_box) -> RB)

  'rule' TypeExpr_to_box(infin_map(D,R) ->box("",list(DB,list(RB,nil))," -~m-> ","",hov_box)):
	 (|
	   Lower_type_precedence(D, 3)
	   where(D -> D1)
	 ||
	   where(TYPE_EXPR'bracket(D) -> D1)
	 |)
	 TypeExpr_to_box(D1 -> DB)
	 TypeExpr_to_box(R -> RB1)
	 where(box("",list(RB1,nil),"","",i_box) -> RB)

  'rule' TypeExpr_to_box(function(X,A,R) ->box("",list(XB,list(RB1,nil)),S,"",hov_box)):
	 (|
	   Lower_type_precedence(X, 3)
	   where(X -> X1)
	 ||
	   where(TYPE_EXPR'bracket(X) -> X1)
	 |)
	 TypeExpr_to_box(X1 -> XB)
	 Funarrow_to_string(A -> S)
	 Resudes_to_box(R -> RB)
	 where(box("",list(RB,nil),"","",i_box) -> RB1)

  'rule' TypeExpr_to_box(fun(X,A,R) ->box("",list(XB,list(RB1,nil)),S,"",hov_box)):
	 (|
	   Lower_type_precedence(X, 3)
	   where(X -> X1)
	 ||
	   where(TYPE_EXPR'bracket(X) -> X1)
	 |)
	 TypeExpr_to_box(X1 -> XB)
	 Funarrow_to_string(A -> S)
	 Resut_to_box(R -> RB)
	 where(box("",list(RB,nil),"","",i_box) -> RB1)

--  'rule' TypeExpr_to_box(subtype(T,R) ->box("{| ",list(TB,list(R1,nil))," :- ","",hv_box)):
--	 Typing_to_box(T -> TB)
--	 Restr_to_box(R -> RB)
--	 where(box("",list(RB,nil),""," |}",hv_box) -> R1)

  'rule' TypeExpr_to_box(subtype(T,R) ->box("{| ",list(TB,list(RB,nil))," :- "," |}",hv_box)):
	 Typing_to_box(T -> TB)
	 Restr_to_box(R -> RB)

  'rule' TypeExpr_to_box(bracket(T) -> box("(",list(B,nil),"",")",hv_box)):
	 TypeExpr_to_box(T -> B)
	 
  'rule' TypeExpr_to_box(any -> string("any")):

  'rule' TypeExpr_to_box(none -> string("none")):

  'rule' TypeExpr_to_box(poly(N) -> B):
	 Int_to_string(N -> S)
	 where(box("poly(",list(string(S),nil),"",")",h_box) -> B)

  'rule' TypeExpr_to_box(array(T1,T2) -> box("array ", list(B1,list(B2,nil)), " of ", "", hov_box))
         TypeExpr_to_box(T1 -> B1)
         TypeExpr_to_box(T2 -> B2)

--------------
--defined type
--------------
'action' Definedtype_to_box(Type_id, OPT_QUALIFICATION -> BOX)

  'rule' Definedtype_to_box(I, Q -> B):
         I'Ident -> Id
	 id_to_string(Id -> S)
	 (|
	   eq(Q, nil)
	   I'Qualifier -> list(Id1,Ids)
	   DefaultPos(-> P)
	   Ids_to_object(P, list(Id1,Ids) -> Obj)
	   where(qualification(Obj) -> Q1)
	 ||
	   where(Q -> Q1)
	 |)
	 Qualify_box(Q1, string(S) -> B1)
	 (|
	    HasErrors()
	    I'Type -> abbrev(_)
	    Unfold_type_id(I -> T1)
	    (|
	       where(T1 -> poly(N))
	       where(B1 -> B)
	     ||
	       TypeExpr_to_box(T1 -> TB)	
	       where(box(" (i.e. ",list(TB,nil),"",")",hv_box) -> B2)
	       where(box("",list(B1,list(B2,nil)),"","",hv_box) -> B)
	    |)
	  ||
	       where(B1 -> B)	      
	 |)

'action' Qualify_box(OPT_QUALIFICATION, BOX -> BOX)

  'rule' Qualify_box(nil, B -> B):

  'rule' Qualify_box(qualification(Obj), B -> box("",list(QB,list(B,nil)),".","",h_box)):
	 ObjExpr_to_box(Obj -> QB)

--------------
--product type
--------------
'action' Prod_type_to_boxes(PRODUCT_TYPE -> BOXES)

  'rule' Prod_type_to_boxes(list(H,T) -> list(HB,TBS)):
	 (|
	   Lower_type_precedence(H, 2)
	   where(H -> H1)
	 ||
	   where(TYPE_EXPR'bracket(H) -> H1)
	 |)
	 TypeExpr_to_box(H1 -> HB)
	 Prod_type_to_boxes(T -> TBS)

  'rule' Prod_type_to_boxes(nil -> nil):

----------------
--function type
----------------
'action' Funarrow_to_string(FUNCTION_ARROW -> STRING)

  'rule' Funarrow_to_string(partial -> " -~-> "):

  'rule' Funarrow_to_string(total -> " -> "):

'action' Resudes_to_box(RESULT_DESC -> BOX)

  'rule' Resudes_to_box(result(nil,T) -> B):
	 TypeExpr_to_box(T -> B)

  'rule' Resudes_to_box(result(AS,T) -> B):
	 Accdess_to_boxes(AS -> BS)
	 TypeExpr_to_box(T -> TB)
	 where(box("",BS," ","",hov_box) -> AB)
	 where(box("",list(AB,list(TB,nil))," ","",hv_box) -> B)

'action' Accdess_to_boxes(ACCESS_DESCS -> BOXES)

  'rule' Accdess_to_boxes(list(H,T) -> list(HB,TBS)):
	 Accdes_to_box(H -> HB)
	 Accdess_to_boxes(T -> TBS)

  'rule' Accdess_to_boxes(nil -> nil):

'action' Accdes_to_box(ACCESS_DESC -> BOX)

  'rule' Accdes_to_box(access(M,A) -> box(S,BS,", ","",hv_box)):
	 Accmod_to_string(M -> S)
	 Accs_to_boxes(A -> BS)

'action' Accmod_to_string(ACCESS_MODE -> STRING)

  'rule' Accmod_to_string(read -> "read "):

  'rule' Accmod_to_string(write -> "write "):

  'rule' Accmod_to_string(in -> "in "):

  'rule' Accmod_to_string(out -> "out "):
	 	 
-----------
--fun type
-----------
'action' Resut_to_box(RESULT -> BOX)

  'rule' Resut_to_box(result(T,RD,WR,IN,OUT) -> B):
	 Readaccs_to_box(RD -> RB)
	 Writeaccs_to_box(WR -> WB)
	 Inaccs_to_box(IN -> IB)
	 Outaccs_to_box(OUT -> OB)
	 TypeExpr_to_box(T -> TB)
	 where(box("",list(RB,list(WB,list(IB,list(OB,nil)))),"","",hov_box) -> B1)
	 where(box("",list(B1,list(TB,nil)),"","",hv_box) -> B)
	   
'action' Readaccs_to_box(ACCESSES -> BOX)

  'rule' Readaccs_to_box(nil -> string("")):

  'rule' Readaccs_to_box(A -> B):
	 Accs_to_boxes(A -> BS)
	 where(box("read ",BS,", "," ",hv_box) -> B) 
	   
'action' Writeaccs_to_box(ACCESSES -> BOX)

  'rule' Writeaccs_to_box(nil -> string("")):

  'rule' Writeaccs_to_box(A -> B):
	 Accs_to_boxes(A -> BS)
	 where(box("write ",BS,", "," ",hv_box) -> B) 
	   
'action' Inaccs_to_box(ACCESSES -> BOX)

  'rule' Inaccs_to_box(nil -> string("")):

  'rule' Inaccs_to_box(A -> B):
	 Accs_to_boxes(A -> BS)
	 where(box("in ",BS,", "," ",hv_box) -> B) 
	   
'action' Outaccs_to_box(ACCESSES -> BOX)

  'rule' Outaccs_to_box(nil -> string("")):

  'rule' Outaccs_to_box(A -> B):
	 Accs_to_boxes(A -> BS)
	 where(box("out ",BS,", "," ",hv_box) -> B) 

'action' Accs_to_boxes(ACCESSES -> BOXES)

  'rule' Accs_to_boxes(list(AC,ACS) -> list(AB,ABS)):
	 Acc_to_box(AC -> AB)
	 Accs_to_boxes(ACS -> ABS)

  'rule' Accs_to_boxes(nil -> nil):

'action' Acc_to_box(ACCESS -> BOX)

  'rule' Acc_to_box(named_access(_,N) -> B):
	 Name_to_box(N -> B)

  'rule' Acc_to_box(enumerated_access(_,AS) ->box("{",BS,", ","}",hv_box)):
	 Accs_to_boxes(AS -> BS)

  'rule' Acc_to_box(completed_access(_, Q) -> B):
	 Completacc_to_box(Q -> B)

  'rule' Acc_to_box(comprehended_access(_,A,L) ->
	 box("{",list(AB,list(L1,nil))," | ","}",hov_box)):
	 Acc_to_box(A -> AB)
	 Set_lim_to_box(L -> LB)
	 where(box("",list(LB,nil),"","",i_box) -> L1)

  'rule' Acc_to_box(variable(_, I, Q) -> B):
	 I'Ident -> Id
	 id_to_string(Id -> S)
	 Qualify_box(Q, string(S) -> B)

  'rule' Acc_to_box(channel(_, I, Q) -> B):
	 I'Ident -> Id
	 id_to_string(Id -> S)
	 Qualify_box(Q, string(S) -> B)

  'rule' Acc_to_box(free -> string("free")):

'action' Completacc_to_box(OPT_QUALIFICATION -> BOX)

  'rule' Completacc_to_box(nil -> string("any")):

  'rule' Completacc_to_box(qualification(Q) -> B):
	 ObjExpr_to_box(Q -> QB)
	 where(box("",list(QB,list(string("any"),nil)),".","",h_box)-> B)

---------------------------------------------------------------------------
--value expr
---------------------------------------------------------------------------
'action' ValExprs_to_boxes(VALUE_EXPRS -> BOXES)

  'rule' ValExprs_to_boxes(list(H,T) -> list(HB,TB)):
	 ValExpr_to_box(H -> HB)
	 ValExprs_to_boxes(T -> TB)

  'rule' ValExprs_to_boxes(nil -> nil):

'action' ValExpr_to_box(VALUE_EXPR -> BOX)

  'rule' ValExpr_to_box(literal_expr(_,Lit) -> string(S)):
	 Literal_to_string(Lit -> S)

  'rule' ValExpr_to_box(named_val(_,N) -> B):
	 Name_to_box(N -> B)
  
  'rule' ValExpr_to_box(pre_name(_,N) -> box("",list(B,list(string("`"),nil)),"","",h_box)):
	 Name_to_box(N -> B)

  'rule' ValExpr_to_box(chaos(_) -> string("chaos")):

  'rule' ValExpr_to_box(skip(_) -> string("skip")):

  'rule' ValExpr_to_box(stop(_) -> string("stop")):

  'rule' ValExpr_to_box(swap(_) -> string("swap")):

  'rule' ValExpr_to_box(product(_,X) -> box("(",BS,", ",")",hv_box)):
	 ValExprs_to_boxes(X -> BS)

  'rule' ValExpr_to_box(ranged_set(_,L,R) -> box("{",list(LB,list(RB,nil))," .. ","}",hv_box)):
	 ValExpr_to_box(L -> LB)
	 ValExpr_to_box(R -> RB)

  'rule' ValExpr_to_box(enum_set(_,X) -> box("{",BS,", ","}",hv_box)):
	 ValExprs_to_boxes(X -> BS)

  'rule' ValExpr_to_box(comp_set(_,E,L) ->
	 box("{",list(EB,list(LB,nil))," | ","}",hv_box)):
	 ValExpr_to_box(E -> EB)
	 Set_lim_to_box(L -> LB) 

  'rule' ValExpr_to_box(ranged_list(_,L,R) -> box("<.",list(LB,list(RB,nil))," .. ",".>",hv_box)):
	 ValExpr_to_box(L -> LB)
	 ValExpr_to_box(R -> RB)

  'rule' ValExpr_to_box(enum_list(_,X) -> box("<.",BS,", ",".>",hv_box)):
	 ValExprs_to_boxes(X -> BS)

  'rule' ValExpr_to_box(comp_list(_,E,L) ->
	 box("<.",list(EB,list(LB,nil))," | ",".>",hv_box)):
	 ValExpr_to_box(E -> EB)
	 List_lim_to_box(L -> LB) 

  'rule' ValExpr_to_box(enum_map(_,L) -> box("[",BS,", ","]",hv_box)):
	 Exprs_pair_to_boxes(L -> BS)

  'rule' ValExpr_to_box(comp_map(_,E,L) -> box("[",BS," | ","]",hv_box)):
	 Expr_pair_to_box(E -> EB)
	 Set_lim_to_box(L -> LB)
	 where(BOXES'list(EB,list(LB,nil)) -> BS)

  'rule' ValExpr_to_box(function(_,L,E) -> box("-\\ ",BS," :- ","",hov_box)):
	 Lambda_param_to_box(L -> LB)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(EB,nil),"","",i_box) -> EB1)
	 where(BOXES'list(LB,list(EB1,nil)) -> BS)

  'rule' ValExpr_to_box(application(P,F,A) -> box("",list(FB,BS),"","",hv_box)):
	 (|
	   Lower_expr_precedence(F, 1)
	   where(F -> F1)
	 ||
	   where(VALUE_EXPR'bracket(P,F) -> F1)
	 |)
	 ValExpr_to_box(F1 -> FB)
         Parms_to_boxes(A -> BS)
	 
  'rule' ValExpr_to_box(quantified(_,Q,L,R) -> box("",BS," ","",hov_box)):
	 Quan_to_string(Q -> ST)
	 Typings_to_boxes(L -> LBS)
	 where(box("",LBS,", ","",hv_box) -> LB)
	 Restr_to_box(R -> RB)
	 where(box("",list(RB,nil),"","",i_box) -> RB1)
	 where(box("",list(LB,nil),"","",i_box) -> LB1)
	 where(box("",list(string(ST),list(LB1,list(string(":-"),nil)))," ","",hov_box) -> QT)
	 where(BOXES'list(QT,list(RB1,nil)) -> BS)

  'rule' ValExpr_to_box(equivalence(P,L,R,PR) -> box("",list(B,PBS)," ","",hov_box)):
	 (|
	   Lower_expr_precedence(L, 14)
	   where(L -> L1)
	 ||
	   where(VALUE_EXPR'bracket(P,L) -> L1)
	 |)
	 ValExpr_to_box(L1 -> LB)
	 (|
	   Lower_expr_precedence(R, 14)
	   where(R -> R1)
	 ||
	   where(VALUE_EXPR'bracket(P,R) -> R1)
	 |)
	 ValExpr_to_box(R1 -> RB)
	 where(box("",list(RB,nil),"","",i_box) -> RB1)
	 where(box("",list(LB,list(RB1,nil))," is ","",hov_box) -> B)
	 Pre_cond_to_boxes(PR -> PBS)

  'rule' ValExpr_to_box(post(P,E,C,PR) -> box("",BS," ","",hov_box)):
	 (|
	   Lower_expr_precedence(E, 14)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> EB)
	 Post_cond_to_boxes(C -> CB1,CB2)
	 Pre_cond_to_boxes(PR -> PBS)
	 where(box("",list(EB,list(CB1,nil))," ","",hov_box) -> C1)
	 where(box("",list(C1,list(CB2,nil))," ","",hov_box) -> C2)
	 where(BOXES'list(C2,PBS) -> BS)

  'rule' ValExpr_to_box(disamb(P,E,T) ->
	 box("",list(EB,list(TB,nil))," : ","",hv_box)):
	 (|
	   Lower_expr_precedence(E, 3)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> EB)
	 TypeExpr_to_box(T -> TB)

  'rule' ValExpr_to_box(bracket(_,X) -> box("(",list(B,nil),"",")",hv_box)):
	 ValExpr_to_box(X -> B)
 
  'rule' ValExpr_to_box(ax_infix(P,L,C,R,_) -> box("",list(LB,BS),S,"",hv_box)):
	 Connective_precedence(C -> N)
	 (|
	   Lower_expr_precedence(L, N)
	   where(L -> L1)
	 ||
	   where(VALUE_EXPR'bracket(P,L) -> L1)
	 |)
	 ValExpr_to_box(L1 -> LB)
	 Connec_to_string(C -> S)
	 (|
	    eq(C,implies)
	   (|
	     Lower_expr_precedence(R, 11)
	     where(R -> R1)
	   ||
	     where(VALUE_EXPR'bracket(P,R) -> R1)
	   |)
	    ValExpr_to_box(R1 -> RB)
	    where(BOXES'list(box("",list(RB,nil),"","",i_box),nil) -> BS)
	  ||
	    where(N+1 -> N1)
	    Collect_ax_infix(P,C,N1,R -> BS)
	 |)

  'rule' ValExpr_to_box(val_infix(P,L,O,R) -> box("",BS,SP,"",hv_box)):
	 Op_to_string(O -> SP)
	 Operator_precedence(O -> N)
	 (|
	   Lower_expr_precedence(R, N)
	   where(R -> R1)
	 ||
	   where(VALUE_EXPR'bracket(P,R) -> R1)
	 |)
	 ValExpr_to_box(R1 -> RB)
	 (|
	    Only_binary(O)
	    (|
	      Lower_expr_precedence(L, N)
	      where(L -> L1)
	    ||
	      where(VALUE_EXPR'bracket(P,L) -> L1)
	    |)
	    ValExpr_to_box(L1 -> LB)
	    where(box("",list(RB,nil),"","",i_box) -> IRB)
	    where(BOXES'list(LB,list(IRB,nil)) -> BS)
	  ||
	    where(N+1 -> N1)
	    Collect_val_infix(P, O, N1, L -> LBS)
	    Append_box(LBS, RB -> BS)
	 |)     

  'rule' ValExpr_to_box(stmt_infix(P,L,C,R) -> B):
         Comb_to_string(C -> S)
	 (|
	    eq(C,sequence)
	    (|
	      Lower_expr_precedence(L, 12)
	      where(L -> L1)
	    ||
	      where(VALUE_EXPR'bracket(P,L) -> L1)
	    |)
	    ValExpr_to_box(L1 -> LB)
	    Collect_sequence(P, R -> BS)
	    where(box("",list(LB,BS),S,"",hov_box) -> B)
	  ||
	    (|
	      Lower_expr_precedence(L, 13)
	      where(L -> L1)
	    ||
	      where(VALUE_EXPR'bracket(P,L) -> L1)
	    |)
	    ValExpr_to_box(L1 -> LB)
	    Move_spaces(S -> S1)
	    Collect_stmt_infix(P, C, S1, R -> BS)
	    where(box("",list(LB,list(string(S1),BS))," ","",hov_box) -> B)
	 |)

  'rule' ValExpr_to_box(always(_,E) -> box("",list(string("always "),list(E1,nil)),"","",hv_box)):
	 ValExpr_to_box(E -> EB)
	 where(box("",list(EB,nil),"","",i_box) -> E1)

  'rule' ValExpr_to_box(ax_prefix(P,C,E) -> box(S,list(EB,nil),"","",hv_box)):
	 Connec_to_string(C -> S)
	 (|
	   Lower_expr_precedence(E, 3)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> EB)

  'rule' ValExpr_to_box(val_prefix(P,O,E) -> box(ST,BS,"","",hv_box)):
	 (|
	   Lower_expr_precedence(E, 3)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> B)
	 where(BOXES'list(B,nil) -> BS)
	 Op_to_string(O -> ST1)
	 (|
	    eq(ST1," + ")
	    where("+" -> ST)
	  ||
	    eq(ST1," - ")
	    where("-" -> ST)
	  ||
	    where(ST1 -> ST)
	 |)

  'rule' ValExpr_to_box(comprehended(_,C,E,L) -> B):
         Comb_to_string(C -> S1)
	 Move_spaces(S1 -> S)
	 ValExpr_to_box(E -> EB)
	 where(box("{ ",list(EB,nil),"","",h_box) -> EB1)
	 Set_lim_to_box(L -> LB)
	 where(box(S,list(EB1,list(LB,nil))," | "," }",hv_box) -> B)

  'rule' ValExpr_to_box(initialise(_,Q) -> B):
	 Init_to_box(Q -> B)

  'rule' ValExpr_to_box(assignment(P,N,E) -> box("",BS," := ","",hv_box)):
	 Name_to_box(N -> NB)
	 (|
	   Lower_expr_precedence(E, 11)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> EB)
	 where(BOXES'list(NB,list(EB,nil)) -> BS)

  'rule' ValExpr_to_box(input(_,N) -> box("",list(B,list(string("?"),nil)),"","",h_box)):
	 Name_to_box(N -> B)

  'rule' ValExpr_to_box(output(P,N,E) -> box("",list(NB,list(EB,nil)),"!","",hv_box)):
	 Name_to_box(N -> NB)
	 (|
	   Lower_expr_precedence(E, 11)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> EB)

  'rule' ValExpr_to_box(local_expr(_,DS,E) -> B):
	 Decls_to_boxes(DS -> DBS)
	 where(box("",DBS,"","",v_box) -> DB)
	 where(box("",list(DB,nil),"","",i_box) -> DB1)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(EB,nil),"","",i_box) -> EB1)
	 where(box("",list(string("in"),list(EB1,list(string("end"),nil)))," ","",hov_box) -> B1)
	 where(box("",list(string("local"),list(DB1,list(B1,nil)))," ","",v_box)-> B) 

  'rule' ValExpr_to_box(let_expr(_,L,E) -> box("",BS," ","",hov_box)):
	 Let_def_list_to_boxes(L -> LBS)
	 where(box("",LBS,", ","",hov_box) -> LB1)
	 where(box("",list(LB1,nil),"","",i_box) -> LB)
	 ValExpr_to_box(E -> EB1)
	 where(box("",list(EB1,nil),"","",i_box) -> EB)
	 where(box("",list(string("let"),list(LB,list(string("in"),nil)))," ","",hov_box) -> LB2)
	 where(BOXES'list(LB2,list(EB,list(string("end"),nil))) -> BS)

  'rule' ValExpr_to_box(if_expr(_,I,T,_,EI,E) -> box("",BS," ","",hov_box)):
	 If_then_to_box(I,T -> ITB)
	 Elsif_branch_string_to_boxes(EI -> EIBS)
	 Else_branch_to_boxes(E -> EBS)
	 Union_boxes(EIBS,EBS -> EB)
	 where(BOXES'list(ITB,EB) -> BS)

  'rule' ValExpr_to_box(case_expr(_,E,_,L) -> box("",list(EB1,list(LB1,list(string("end"),nil))),"","",v_box)):
	 ValExpr_to_box(E -> EB)
	 Case_branchs_to_boxes(L -> LBS)
	 where(box("",LBS,",","",v_box) -> LB)
	 where(box("",list(LB,nil),"","",i_box) -> LB1)
	 where(box("",list(EB,nil),"","",i_box) -> B)
	 where(box("",list(string("case"),list(B,list(string("of"),nil)))," ","",hov_box) -> EB1)

  'rule' ValExpr_to_box(while_expr(_,E,D) -> B):
	 ValExpr_to_box(E -> EB)
	 ValExpr_to_box(D -> DB)
	 where(box("",list(DB,nil),"","",i_box) -> DB1)
	 where(box("",list(EB,nil),"","",i_box) -> EB1)
	 where(box("",list(string("while"),list(EB1,list(string("do"),nil)))," ","",hov_box) -> EB2)
	 where(box("",list(EB2,list(DB1,list(string("end"),nil)))," ","",hov_box)->B)

  'rule' ValExpr_to_box(until_expr(_,D,E) -> B):
	 ValExpr_to_box(D -> DB)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(DB,nil),"","",i_box) -> DB1)
	 where(box("",list(EB,nil),"","",i_box) -> EB1)
	 where(box("",list(string("until"),list(EB1,list(string("end"),nil)))," ","",hov_box) -> EB2)
	 where(box("",list(string("do"),list(DB1,list(EB2,nil)))," ","",hov_box)->B)

  'rule' ValExpr_to_box(for_expr(_,L,E) -> B):
	 List_lim_to_box(L -> LB)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(LB,nil),"","",i_box) -> LB1)
	 where(box("",list(EB,nil),"","",i_box) -> EB1)
	 where(box("",list(string("for"),list(LB1,list(string("do"),nil)))," ","",hov_box) -> LB2)
	 where(box("",list(LB2,list(EB1,list(string("end"),nil)))," ","",hov_box)->B)

  'rule' ValExpr_to_box(val_occ(P,Id,Q) -> B):
	 Id'Ident -> ID
	 Id_or_op_to_string(ID -> S)
	 (|
	   eq(Q, nil)
	   Id'Qualifier -> list(Id1,Ids)
	   Ids_to_object(P, list(Id1,Ids) -> Obj)
	   where(qualification(Obj) -> Q1)
	 ||
	   where(Q -> Q1)
	 |)
	 (|
	   where(ID -> op_op(_))
	   where(Q1 -> qualification(_))
	   Move_spaces(S -> S1)
	   where(box("(",list(string(S1),nil),"",")",hv_box) -> B1)
	   Qualify_box(Q1, B1 -> B)
	 ||
	   Qualify_box(Q1, string(S) -> B)
	 |)
	 

  'rule' ValExpr_to_box(var_occ(P,Id,Q) -> B):
	 Id'Ident -> ID
	 id_to_string(ID -> S)
	 (|
	   eq(Q, nil)
	   Id'Qualifier -> list(Id1,Ids)
	   Ids_to_object(P, list(Id1,Ids) -> Obj)
	   where(qualification(Obj) -> Q1)
	 ||
	   where(Q -> Q1)
	 |)
	 Qualify_box(Q1, string(S) -> B)

  'rule' ValExpr_to_box(pre_occ(P,Id,Q) -> box("",list(B,list(string("`"),nil)),"","",h_box)):
	 Id'Ident -> ID
	 id_to_string(ID -> S)
	 (|
	   eq(Q, nil)
	   Id'Qualifier -> list(Id1,Ids)
	   Ids_to_object(P, list(Id1,Ids) -> Obj)
	   where(qualification(Obj) -> Q1)
	 ||
	   where(Q -> Q1)
	 |)
	 Qualify_box(Q1, string(S) -> B)

  'rule' ValExpr_to_box(infix_occ(P,L,Id,nil,R) -> B):
	 (|
	   Id'Qualifier -> list(Id1,Ids)
	   Ids_to_object(P, list(Id1,Ids) -> Obj)
	   ValExpr_to_box(infix_occ(P,L,Id,qualification(Obj),R) -> B)
	 ||
	   Id'Ident -> ID
	   Id_or_op_to_string(ID -> S)
	   where(ID -> op_op(O))
	   Operator_precedence(O -> N)
	   (|
	     Lower_expr_precedence(R, N)
	     where(R -> R1)
	   ||
	     where(VALUE_EXPR'bracket(P,R) -> R1)
	   |)
	   ValExpr_to_box(R1 -> RB)
	   (|
	      Only_binary(O)
	      (|
		Lower_expr_precedence(L, N)
		where(L -> L1)
	      ||
		where(VALUE_EXPR'bracket(P,L) -> L1)
	      |)
	      ValExpr_to_box(L1 -> LB)
	      where(box("",list(RB,nil),"","",i_box) -> IRB)
	      where(BOXES'list(LB,list(IRB,nil)) -> BS)
	    ||
	      where(N+1 -> N1)
	      Collect_val_infix(P, O, N1, L -> LBS)
	      Append_box(LBS, RB -> BS)
	   |)
	   where(box("",BS,S,"",hv_box) -> B)
	 |)

  'rule' ValExpr_to_box(infix_occ(P,L,Id,Q,R) -> B):
	 ValExpr_to_box(application(P,val_occ(P,Id,Q),list(fun_arg(P,list(L,list(R,nil))),nil)) -> B)



  'rule' ValExpr_to_box(prefix_occ(P,Id,Q,E) -> box("",list(B1,list(B,nil)),"","",hv_box)):
	 (|
	   Lower_expr_precedence(E, 3)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> B)
	 Id'Ident -> ID
	 Id_or_op_to_string(ID -> ST1)
	 (|
	   eq(Q, nil)
	   Id'Qualifier -> list(Id1,Ids)
	   Ids_to_object(P, list(Id1,Ids) -> Obj)
	   where(qualification(Obj) -> Q1)
	 ||
	   where(Q -> Q1)
	 |)
	 (|
	    eq(Q1, nil)
	    eq(ST1," + ")
	    where("+" -> ST)
	  ||
	    eq(Q1, nil)
	    eq(ST1," - ")
	    where("-" -> ST)
	  ||
	    where(ST1 -> ST)
	 |)
	 Qualify_box(Q1, string(ST) -> B1)      

  'rule' ValExpr_to_box(ass_occ(P,Id,Q,E) -> box("",BS," := ","",hv_box)):
	 Id'Ident -> ID
	 id_to_string(ID -> S)
	 (|
	   eq(Q, nil)
	   Id'Qualifier -> list(Id1,Ids)
	   Ids_to_object(P, list(Id1,Ids) -> Obj)
	   where(qualification(Obj) -> Q1)
	 ||
	   where(Q -> Q1)
	 |)
	 Qualify_box(Q1, string(S) -> B)
	 (|
	   Lower_expr_precedence(E, 11)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> EB)
	 where(BOXES'list(B,list(EB,nil)) -> BS)

  'rule' ValExpr_to_box(input_occ(P,Id,Q) -> box("",list(B,list(string("?"),nil)),"","",h_box)):
	 Id'Ident -> ID
	 id_to_string(ID -> S)
	 (|
	   eq(Q, nil)
	   Id'Qualifier -> list(Id1,Ids)
	   Ids_to_object(P, list(Id1,Ids) -> Obj)
	   where(qualification(Obj) -> Q1)
	 ||
	   where(Q -> Q1)
	 |)
	 Qualify_box(Q1, string(S) -> B)

  'rule' ValExpr_to_box(output_occ(P,Id,Q,E) -> box("",BS,"!","",hv_box)):
	 Id'Ident -> ID
	 id_to_string(ID -> S)
	 (|
	   eq(Q, nil)
	   Id'Qualifier -> list(Id1,Ids)
	   Ids_to_object(P, list(Id1,Ids) -> Obj)
	   where(qualification(Obj) -> Q1)
	 ||
	   where(Q -> Q1)
	 |)
	 Qualify_box(Q1, string(S) -> B)
	 (|
	   Lower_expr_precedence(E, 11)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> EB)
	 where(BOXES'list(B,list(EB,nil)) -> BS)
	 
  'rule' ValExpr_to_box(env_local(_,DS,_,E) -> B):
	 Decls_to_boxes(DS -> DBS)
	 where(box("",DBS,"","",v_box) -> DB)
	 where(box("",list(DB,nil),"","",i_box) -> DB1)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(EB,nil),"","",i_box) -> EB1)
	 where(box("",list(string("in"),list(EB1,list(string("end"),nil)))," ","",hov_box) -> B1)
	 where(box("",list(string("local"),list(DB1,list(B1,nil)))," ","",v_box)-> B) 

  'rule' ValExpr_to_box(no_val -> string("??")):

  'rule' ValExpr_to_box(class_scope_expr(_,C,E) -> B):
	 ClasExpr_to_box(C -> CB)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(CB,nil),"","",i_box) -> C1)
	 where(box("",list(EB,nil),"","",i_box) -> E1)
	 where(box("",list(string("in"),list(C1,list(string("|-"),nil)))," ","",hov_box) -> C2)
	 where(box("",list(C2,list(E1,nil))," ","",hov_box) -> B)

  'rule' ValExpr_to_box(env_class_scope(P,C,_,E) -> B):
	 ValExpr_to_box(class_scope_expr(P,C,E) -> B)

  'rule' ValExpr_to_box(implementation_relation(_,C1,C2) -> B):
	 ClasExpr_to_box(C1 -> B1)
	 ClasExpr_to_box(C2 -> B2)
	 where(box("|- ",list(B1,list(B2,nil))," {= ","",hv_box) -> B)

  'rule' ValExpr_to_box(implementation_expr(_,O1,O2) -> B):
	 ObjExpr_to_box(O1 -> B1)
	 ObjExpr_to_box(O2 -> B2)
	 where(box("|- ",list(B1,list(B2,nil))," [= ","",hv_box) -> B)

  'rule' ValExpr_to_box(cc_expr(P, STR, _, E) -> B):
	 (|
	   where(P -> pos(P1))
	   PrefixWithPos(P1, STR -> PSTR)
	 ||
	   PrefixAsComment(STR -> PSTR)
	 |)
	 where(line_comm(PSTR, 0) -> B1)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(B1, list(EB,nil)),"","",v_box) -> B)

  'rule' ValExpr_to_box(array_expr(P,T,V) -> box("[|[",list(B1,list(B2,nil)), "] ", "|]",hov_box))
         Typing_to_box(T -> B1)
         ValExpr_to_box(V -> B2)

  'rule' ValExpr_to_box(array_access(P,N,I) -> box("",list(B1,list(B3,nil)), "", "", hov_box))
         ValExpr_to_box(N -> B1)
         ValExpr_to_box(I -> B2)
         where(box("[",list(B2,nil),"","]",hv_box) -> B3)

 'rule' ValExpr_to_box(array_assignment(P,N,I,V) -> B)
         Name_to_box(N -> NB)
         ValExprs_to_boxes(I -> IB)
         ValExpr_to_box(V -> VB)
         where(box("",list(VB,nil),"","",i_box) -> VEB)
         where(box("[",IB,"][","]",hv_box) -> IEB)
         --where(box("[",IB,"","]",i_box) -> IEB)
	 where(box("",list(NB,list(string(" = "),list(IEB,list(VEB,nil)))),"","",hov_box)-> B)


-- last identifier will suffice
-- (because it will have a qualifier of the earlier ones)
'action' Ids_to_object(POS, Object_ids -> OBJECT_EXPR)

  'rule' Ids_to_object(P, list(Id, nil) -> obj_occ(P, Id)):

  'rule' Ids_to_object(P, list(Id, Ids) -> Obj):
	 Ids_to_object(P, Ids -> Obj)

---------
-- Collect infixes to lists
---------

'action' Collect_val_infix(POS, OP, INT, VALUE_EXPR -> BOXES)

  'rule' Collect_val_infix(_, O, N, val_infix(P,L,O1,R) -> BS):
	 eq(O,O1)
	 Collect_val_infix(P, O, N, L -> LBS)
	 (|
	   Lower_expr_precedence(R, N)
	   where(R -> R1)
	 ||
	   where(VALUE_EXPR'bracket(P,R) -> R1)
	 |)
	 ValExpr_to_box(R1 -> RB)
	 Append_box(LBS, RB -> BS)

  'rule' Collect_val_infix(P, O, N, E -> list(B,nil)):
	 (|
	   Lower_expr_precedence(E, N)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> B)

'action' Collect_ax_infix(POS, CONNECTIVE, INT, VALUE_EXPR -> BOXES)

  'rule' Collect_ax_infix(_, C, N, ax_infix(P,L,C1,R,_) -> list(LB,RBS)):
	 eq(C,C1)
	 (|
	   Lower_expr_precedence(L, N)
	   where(L -> L1)
	 ||
	   where(VALUE_EXPR'bracket(P,L) -> L1)
	 |)
	 ValExpr_to_box(L1 -> LB)
	 Collect_ax_infix(P, C, N, R -> RBS)

  'rule' Collect_ax_infix(P, C, N, E -> list(B,nil)):
	 (|
	   Lower_expr_precedence(E, N)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> B)

'action' Collect_sequence(POS, VALUE_EXPR -> BOXES)

  'rule' Collect_sequence(_, stmt_infix(P,L,sequence,R) -> list(LB,RBS)):
	 (|
	   Lower_expr_precedence(L, 12)
	   where(L -> L1)
	 ||
	   where(VALUE_EXPR'bracket(P,L) -> L1)
	 |)
	 ValExpr_to_box(L1 -> LB)
	 Collect_sequence(P, R -> RBS)

  'rule' Collect_sequence(P, E -> list(B,nil)):
	 (|
	   Lower_expr_precedence(E, 12)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> B)

'action' Collect_stmt_infix(POS, COMBINATOR, STRING, VALUE_EXPR -> BOXES)

  'rule' Collect_stmt_infix(_, C, S, stmt_infix(P,L,C1,R) -> list(LB,list(string(S),RBS))):
	 eq(C,C1)
	 (|
	   Lower_expr_precedence(L, 13)
	   where(L -> L1)
	 ||
	   where(VALUE_EXPR'bracket(P,L) -> L1)
	 |)
	 ValExpr_to_box(L1 -> LB)
	 Collect_stmt_infix(P, C, S, R -> RBS)

  'rule' Collect_stmt_infix(P, C, S, E -> list(B,nil)):
	 (|
	   Lower_expr_precedence(E, 13)
	   where(E -> E1)
	 ||
	   where(VALUE_EXPR'bracket(P,E) -> E1)
	 |)
	 ValExpr_to_box(E1 -> B)

'action' Append_box(BOXES, BOX -> BOXES)

  'rule' Append_box(list(B, BS), B1 -> list(B, BS1)):
	 Append_box(BS, B1 -> BS1)

  'rule' Append_box(nil, B -> list(B, nil)):
	 
---------
--literal
---------

'action' Literal_to_string(VALUE_LITERAL -> STRING)
	 
  'rule' Literal_to_string(unit -> "()"):

  'rule' Literal_to_string(bool_true -> "true"):

  'rule' Literal_to_string(bool_false -> "false"):

  'rule' Literal_to_string(int(Id) -> S):
	 id_to_string(Id -> S)

  'rule' Literal_to_string(real(Id) -> S):
	 id_to_string(Id -> S)

  'rule' Literal_to_string(text(Id) -> S):
	 Text_to_string(Id -> S)

  'rule' Literal_to_string(char(Id) -> S):
         Char_to_string(Id -> S)



----------
--comp_set
----------
'action' Set_lim_to_box(SET_LIMITATION -> BOX)

  'rule' Set_lim_to_box(set_limit(_,L,nil) -> box("",LBS,", ","",hv_box)):
	 Typings_to_boxes(L -> LBS)

  'rule' Set_lim_to_box(set_limit(_,L,R) -> B):
	 Typings_to_boxes(L -> LBS)
	 where(box("",LBS,", ","",hv_box) -> LB)
	 Restr_to_box(R -> RB)
	 where(box("",list(RB,nil),"","",i_box) -> RB1)
	 where(box("",list(LB,list(RB1,nil))," :- ","",hov_box) -> B)	 

----------
--comp_list
----------
'action' List_lim_to_box(LIST_LIMITATION -> BOX)

  'rule' List_lim_to_box(list_limit(_,B,E,nil) -> LB):
	 Bind_to_box(B -> BB)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(BB,list(EB,nil))," in ","",hv_box) ->LB)

  'rule' List_lim_to_box(list_limit(_,B,E,R) -> BO):
	 Bind_to_box(B -> BB)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(BB,list(EB,nil))," in ","",hv_box) ->LB)
	 Restr_to_box(R -> RB)
	 where(box("",list(RB,nil),"","",i_box) -> RB1)
	 where(box("",list(LB,list(RB1,nil))," :- ","",hv_box) -> BO)

----------
--enum_map
----------
'action' Exprs_pair_to_boxes(VALUE_EXPR_PAIRS -> BOXES)

  'rule' Exprs_pair_to_boxes(nil -> nil):

  'rule' Exprs_pair_to_boxes(list(H,T) -> list(HB,TBS)):
	 Expr_pair_to_box(H -> HB)
	 Exprs_pair_to_boxes(T -> TBS)

'action' Expr_pair_to_box(VALUE_EXPR_PAIR -> BOX)

  'rule' Expr_pair_to_box(pair(L,R) -> box("",BS," +> ","",hv_box)):
	 ValExpr_to_box(L -> LB)
	 ValExpr_to_box(R -> RB)
	 where(BOXES'list(LB,list(RB,nil)) -> BS)

----------
--function
----------
'action' Lambda_param_to_box(LAMBDA_PARAMETER -> BOX)

  'rule' Lambda_param_to_box(s_typing(_,T) -> B):
	 Typing_to_box(T -> B)

  'rule' Lambda_param_to_box(l_typing(_,T) -> B):
	 Typings_to_boxes(T -> TBS)
	 where(box("(",TBS,", ",")",hv_box) -> B)

------------------
--application parm
------------------
'action' Parms_to_boxes(ACTUAL_FUNCTION_PARAMETERS -> BOXES)

  'rule' Parms_to_boxes(list(H,T) -> list(HB,TB)):
	 Parm_to_box(H -> HB)
	 Parms_to_boxes(T -> TB)

  'rule' Parms_to_boxes(nil -> nil):

'action' Parm_to_box(ACTUAL_FUNCTION_PARAMETER -> BOX)

  'rule' Parm_to_box(fun_arg(_,L) -> box("(",list(B,nil),"",")",i_box)):
	 ValExprs_to_boxes(L -> BS)
	 where(box("",BS,", ","",hv_box) -> B)
-----------------
--quantified_expr
-----------------
'action' Quan_to_string(QUANTIFIER -> STRING)

  'rule' Quan_to_string(all -> "all"):

  'rule' Quan_to_string(exists -> "exists"):

  'rule' Quan_to_string(exists1 -> "exists!"):

'action' Restr_to_box(RESTRICTION -> BOX)

  'rule' Restr_to_box(restriction(_,X) -> B):
	 ValExpr_to_box(X -> B)

--------------
--equivalence
--------------
'action' Pre_cond_to_boxes(PRE_CONDITION -> BOXES)

  'rule' Pre_cond_to_boxes(nil -> nil):

  'rule' Pre_cond_to_boxes(pre_cond(P,X) -> list(B2,nil)):
	 (|
	   Lower_expr_precedence(X, 14)
	   where(X -> X1)
	 ||
	   where(VALUE_EXPR'bracket(P,X) -> X1)
	 |)
	 ValExpr_to_box(X1 -> B)
	 where(box("",list(B,nil),"","",i_box) -> B1)
	 where(box("",list(string("pre"),list(B1,nil))," ","",hv_box) -> B2) 	 

--------
--post
--------
'action' Post_cond_to_box(POST_CONDITION -> BOX)

  'rule' Post_cond_to_box(post_cond(_,nil,E) -> B):
	 ValExpr_to_box(E -> EB1)
	 where(box("",list(EB1,nil),"","",i_box) -> EB)
	 where(box("",list(string("post"),list(EB,nil))," ","",hv_box) -> B)

  'rule' Post_cond_to_box(post_cond(_,R,E) -> B):
	 Result_to_box(R -> RB)
	 ValExpr_to_box(E -> EB1)
	 where(box("",list(EB1,nil),"","",i_box) -> EB)
	 where(box("",list(string("as"),list(RB,list(string("post"),nil)))," ","",hov_box) -> RB1)
	 where(box("",list(RB1,list(EB,nil))," ","",hv_box) -> B)	 

'action' Post_cond_to_boxes(POST_CONDITION -> BOX,BOX)

  'rule' Post_cond_to_boxes(post_cond(_,nil,E) -> SB,EB):
	 ValExpr_to_box(E -> EB1) 
	 where(box("",list(string("post"),nil),"","",i_box) -> SB)
	 where(box("",list(EB1,nil),"","",i_box) -> EB)

  'rule' Post_cond_to_boxes(post_cond(_,R,E) -> RB2,EB):
	 Result_to_box(R -> RB)
	 where(box("",list(RB,nil),"","",i_box) -> R1)
	 ValExpr_to_box(E -> EB1)
	 where(box("",list(EB1,nil),"","",i_box) -> EB)
	 where(box("",list(string("as"),list(R1,list(string("post"),nil)))," ","",hov_box) -> RB1)
	 where(box("",list(RB1,nil),"","",i_box) -> RB2)

'action' Result_to_box(RESULT_NAMING -> BOX)

  'rule' Result_to_box(result(_,B) -> BB):
	 Bind_to_box(B -> BB)
------------
--initialise
------------
'action' Init_to_box(OPT_QUALIFICATION -> BOX)

  'rule' Init_to_box(nil -> string("initialise")):

  'rule' Init_to_box(qualification(Q) -> B):
	 ObjExpr_to_box(Q -> QB)
	 where(box("",list(QB,list(string("initialise"),nil)),".","",h_box) ->B)
	 
----------
--let_expr
----------
'action' Let_def_list_to_boxes(LET_DEFS -> BOXES)

  'rule' Let_def_list_to_boxes(list(H,T) -> list(HB,TB)):
	 Let_def_to_box(H -> HB)
	 Let_def_list_to_boxes(T -> TB)

  'rule' Let_def_list_to_boxes(nil -> nil):

'action' Let_def_to_box(LET_DEF -> BOX)

  'rule' Let_def_to_box(explicit(_,B,E) -> box("",BS," = ","",hv_box)):
	 Let_bind_to_box(B -> BB)
	 ValExpr_to_box(E -> EB1)
	 where(box("",list(EB1,nil),"","",i_box) -> EB)
	 where(BOXES'list(BB,list(EB,nil)) -> BS)

  'rule' Let_def_to_box(implicit(_,T,nil) -> B):
	 Typing_to_box(T -> B)

  'rule' Let_def_to_box(implicit(_,T,R) -> B):
	 Typing_to_box(T -> TB)
	 Restr_to_box(R -> RB1)
	 where(box("",list(RB1,nil),"","",i_box) -> RB)
	 where(box("",list(TB,list(RB,nil))," :- ","",hov_box) -> B)

'action' Let_bind_to_box( LET_BINDING -> BOX)

  'rule' Let_bind_to_box(binding(_,B) -> BB):
	 Bind_to_box(B -> BB)

  'rule' Let_bind_to_box(pattern(_,B) -> BB):
	 Patt_to_box(B -> BB)

/*  'rule' Let_bind_to_box(pattern(_,record_pattern(_,N,PS)) -> B):
	 Rec_patt_to_box(N,PS -> B)

  'rule' Let_bind_to_box(pattern(_,enum_list(_,L)) -> B):
	 Enumlist_patt_to_box(L -> B)

  'rule' Let_bind_to_box(pattern(_,conc_list(_,E,I)) -> B):
	 Conclist_patt_to_box(E,I -> B)
*/
---------
--if_expr
---------
'action' If_then_to_box(VALUE_EXPR,VALUE_EXPR -> BOX)

  'rule' If_then_to_box(I,T -> box("",list(IB,list(TB,nil))," ","",hov_box)):
	 If_to_box(I -> IB)
	 Then_to_box(T -> TB)

'action' If_to_box(VALUE_EXPR -> BOX)

  'rule' If_to_box(I -> box("",list(string("if "),list(IB1,nil)),"","",hov_box)):
	 ValExpr_to_box(I -> IB)
	 where(box("",list(IB,nil),"","",i_box) -> IB1)

'action' Then_to_box(VALUE_EXPR -> BOX)

  'rule' Then_to_box(T -> box("",list(string("then "),list(TB1,nil)),"","",hov_box)):
	 ValExpr_to_box(T -> TB)
	 where(box("",list(TB,nil),"","",i_box) -> TB1)

'action' Elsif_branch_string_to_boxes(ELSIF_BRANCHES -> BOXES)

  'rule' Elsif_branch_string_to_boxes(list(H,T) -> list(HB,TB)):
	 Elsif_branch_to_box(H -> HB)
	 Elsif_branch_string_to_boxes(T -> TB)

  'rule' Elsif_branch_string_to_boxes(nil -> nil):

'action' Elsif_branch_to_box(ELSIF_BRANCH -> BOX)

  'rule' Elsif_branch_to_box(elsif(_,I,T,_) -> box("",list(IB,list(TB1,nil))," ","",hov_box)):
	 Elsif_to_box(I -> IB)
	 Then_to_box(T -> TB)
	 where(box("",list(TB,nil),"","",i_box) -> TB1)

'action' Elsif_to_box(VALUE_EXPR -> BOX)

  'rule' Elsif_to_box(I -> box("",list(string("elsif "),list(IB1,nil)),"","",hov_box)):
	 ValExpr_to_box(I -> IB)
	 where(box("",list(IB,nil),"","",i_box) -> IB1)

'action' Else_branch_to_boxes(ELSE_BRANCH -> BOXES)

  'rule' Else_branch_to_boxes(else(_,E) -> list(EB2,list(string("end"),nil))):
	 ValExpr_to_box(E -> EB)
	 where(box("",list(EB,nil),"","",i_box) -> EB1)
	 where(box("",list(string("else "),list(EB1,nil)),"","",hov_box) -> EB2)

  'rule' Else_branch_to_boxes(nil -> list(string("end"),nil)):

'action' Union_boxes(BOXES,BOXES -> BOXES)

  'rule' Union_boxes(nil,BS -> BS):

  --'rule' Union_boxes(BS,nil -> BS):

  'rule' Union_boxes(list(H,T),BS -> list(H,UBS)):
	 Union_boxes(T,BS -> UBS)

------
--case
------
'action' Case_branchs_to_boxes(CASE_BRANCHES -> BOXES)

  'rule' Case_branchs_to_boxes(nil -> nil):

  'rule' Case_branchs_to_boxes(list(H,T) -> list(HB,TBS)):
	 Case_branch_to_box(H -> HB)
	 Case_branchs_to_boxes(T -> TBS)

'action' Case_branch_to_box(CASE_BRANCH -> BOX)

  'rule' Case_branch_to_box(case(_,X,E,_) -> B):
	 Patt_to_box(X -> XB)
	 ValExpr_to_box(E -> EB)
	 where(box("",list(EB,nil),"","",i_box) -> B1)
	 where(box("",list(XB,list(B1,nil))," -> ","",hov_box) -> B)

---------------------------------------------------------------------------
--Bindings and typings
---------------------------------------------------------------------------
'action' Binds_to_boxes(BINDINGS -> BOXES)

  'rule' Binds_to_boxes(list(H,T) -> list(HB,TBS)):
	 Bind_to_box(H -> HB)
	 Binds_to_boxes(T -> TBS)

  'rule' Binds_to_boxes(nil -> nil):

'action' Bind_to_box( BINDING -> BOX)

  'rule' Bind_to_box(single(_,Id) -> string(S1)):
	 Id_or_op_to_string(Id -> S)
	 (|
	    where(Id -> id_op(_))
	    where(S -> S1)
	  ||
	    Move_spaces(S -> S1)  
	 |)   	   

  'rule' Bind_to_box(product(_,L) ->box("(",BS,", ",")",hv_box)):
	 Binds_to_boxes(L -> BS)

'action' Typings_to_boxes(TYPINGS -> BOXES)

  'rule' Typings_to_boxes(list(H,T) -> list(HB,TBS)):
	 Typing_to_box(H -> HB)
	 Typings_to_boxes(T -> TBS)

  'rule' Typings_to_boxes(nil -> nil):

'action' Typing_to_box(TYPING -> BOX)

  'rule' Typing_to_box(single(_,B,T) -> RB):
	 Bind_to_box(B -> BB)
	 TypeExpr_to_box(T -> TB)
	 where(box("",list(TB,nil),"","",i_box) -> T1)
	 where(box("",list(BB,list(T1,nil))," : ","",hv_box) -> RB)

  'rule' Typing_to_box(multiple(_,B,T) -> RB):
	 Binds_to_boxes(B -> BS)
	 TypeExpr_to_box(T -> TB)
	 where(box("",BS,", ","",hv_box) -> BB)
	 where(box("",list(TB,nil),"","",i_box) -> T1)
	 where(box("",list(BB,list(T1,nil))," : ","",hv_box) -> RB)

----------------------------------------------------------------------------
--Patterns names and operators
----------------------------------------------------------------------------
---------
--pattern
---------
'action' Patt_to_box(PATTERN -> BOX)

  'rule' Patt_to_box(literal_pattern(_,L) -> string(S)):
	 Literal_to_string(L -> S)

  'rule' Patt_to_box(name_pattern(_,N) -> B):
	 Name_to_box(N -> B)

  'rule' Patt_to_box(wildcard_pattern(_) -> string("_")):

  'rule' Patt_to_box(id_pattern(_,Id) -> string(S)):
	 Id_or_op_to_string(Id -> S)

  'rule' Patt_to_box(product_pattern(_,L) -> B):
	 Patts_to_boxes(L -> BS)
	 where(box("(",BS,", ",")",hv_box) -> B)

  'rule' Patt_to_box(record_pattern(_,N,PS) -> B):
	 Rec_patt_to_box(N,PS -> B)

  'rule' Patt_to_box(enum_list(_,L) -> B):
	 Enumlist_patt_to_box(L -> B)

  'rule' Patt_to_box(conc_list(_,E,I) -> B):
	 Conclist_patt_to_box(E,I -> B)

  'rule' Patt_to_box(name_occ_pattern(P,Id,Q) -> B):
	 Id'Ident -> ID
	 Id_or_op_to_string(ID -> S)
--	 (|
--	   eq(Q, nil)
--	   Id'Qualifier -> list(Id1,Ids)
--	   Ids_to_object(P, list(Id1,Ids) -> Obj)
--	   where(qualification(Obj) -> Q1)
--	 ||
--	   where(Q -> Q1)
--	 |)
	 Qualify_box(Q, string(S) -> B)

  'rule' Patt_to_box(record_occ_pattern(P,Id,Q,PS) -> B):
	 Rec_occ_patt_to_box(P,Id,Q,PS -> B)

'action' Rec_patt_to_box(NAME,PATTERNS -> BOX)

  'rule' Rec_patt_to_box(N,PS -> B):
	 Name_to_box(N -> NB)
	 Patts_to_boxes(PS -> PBS)
	 where(box("",PBS,", ","",hv_box) -> P1)
	 where(box("(",list(P1,nil),"",")",i_box) -> PB)
	 where(box("",list(NB,list(PB,nil)),"","",hv_box) -> B)

'action' Rec_occ_patt_to_box(POS,Value_id,OPT_QUALIFICATION,PATTERNS -> BOX)

  'rule' Rec_occ_patt_to_box(P,Id,Q,PS -> B):
	 Id'Ident -> ID
	 Id_or_op_to_string(ID -> S)
	 (|
	   eq(Q, nil)
	   Id'Qualifier -> list(Id1,Ids)
	   Ids_to_object(P, list(Id1,Ids) -> Obj)
	   where(qualification(Obj) -> Q1)
	 ||
	   where(Q -> Q1)
	 |)
	 Qualify_box(Q1, string(S) -> NB)
	 Patts_to_boxes(PS -> PBS)
	 where(box("",PBS,", ","",hv_box) -> P1)
	 where(box("(",list(P1,nil),"",")",i_box) -> PB)
	 where(box("",list(NB,list(PB,nil)),"","",hv_box) -> B)

'action' Enumlist_patt_to_box(PATTERNS -> BOX)

  'rule' Enumlist_patt_to_box(L -> box("<.",LBS,", ",".>",hv_box)):
	 Patts_to_boxes(L -> LBS)

'action' Conclist_patt_to_box(PATTERNS,PATTERN -> BOX)

  'rule' Conclist_patt_to_box(E,I -> box("",list(EB,list(IB,nil))," ^ ","",hv_box)):
	 Patts_to_boxes(E -> EBS)
	 InPatt_to_box(I -> IB)
	 where(box("<.",EBS,", ",".>",hv_box) -> EB)
	 

'action' Patts_to_boxes(PATTERNS -> BOXES)

  'rule' Patts_to_boxes(list(H,T) -> list(HB,TBS)):
	 InPatt_to_box(H -> HB)
	 Patts_to_boxes(T -> TBS)

  'rule' Patts_to_boxes(nil -> nil):

'action' InPatt_to_box(PATTERN -> BOX)
  
  'rule' InPatt_to_box(id_pattern(_,Id) -> string(S)):
	 Id_or_op_to_string(Id -> S) 

  'rule' InPatt_to_box(literal_pattern(_,L) -> string(S)):
	 Literal_to_string(L -> S)

  'rule' InPatt_to_box(name_pattern(_,N) -> box("=",list(B,nil),"","",h_box)):
	 Name_to_box(N -> B)

  'rule' InPatt_to_box(wildcard_pattern(_) -> string("_")):

  'rule' InPatt_to_box(product_pattern(_,L) -> B):
	 Patts_to_boxes(L -> BS)
	 where(box("(",BS,", ",")",hv_box) -> B)

  'rule' InPatt_to_box(record_pattern(_,N,PS) -> B):
	 Rec_patt_to_box(N,PS -> B)

  'rule' InPatt_to_box(enum_list(_,L) -> B):
	 Enumlist_patt_to_box(L -> B)

  'rule' InPatt_to_box(conc_list(_,E,I) -> B):
	 Conclist_patt_to_box(E,I -> B)

  'rule' InPatt_to_box(name_occ_pattern(P,Id,Q) -> box("=",list(B,nil),"","",h_box)):
	 Id'Ident -> ID
	 Id_or_op_to_string(ID -> S)
	 (|
	   eq(Q, nil)
	   Id'Qualifier -> list(Id1,Ids)
	   Ids_to_object(P, list(Id1,Ids) -> Obj)
	   where(qualification(Obj) -> Q1)
	 ||
	   where(Q -> Q1)
	 |)
	 Qualify_box(Q1, string(S) -> B)

  'rule' InPatt_to_box(record_occ_pattern(P,Id,Q,PS) -> B):
	 Rec_occ_patt_to_box(P,Id,Q,PS -> B)

---------
--name
---------
'action' Name_to_box(NAME -> BOX)
 
  'rule' Name_to_box(name(_,id_op(Id)) -> string(S)):
	 id_to_string(Id -> S)

  'rule' Name_to_box(name(_,op_op(Op)) -> B):
	 Op_to_string(Op -> S)
	 Move_spaces(S -> S1)
	 where(box("(",list(string(S1),nil),"",")",hv_box) -> B)

  'rule' Name_to_box(qual_name(_,O,id_op(Id)) -> B):
	 ObjExpr_to_box(O -> OB)
	 id_to_string(Id -> S)
	 where(box("",list(OB,list(string(S),nil)),".","",h_box) -> B)

  'rule' Name_to_box(qual_name(_,O,op_op(Op)) -> B):
	 ObjExpr_to_box(O -> OB)
	 Op_to_string(Op -> S)
	 Move_spaces(S -> S1)
	 where(box("(",list(string(S1),nil),"",")",h_box) -> SB)
	 where(box("",list(OB,list(SB,nil)),".","",h_box) -> B)
-------------
--ident
-------------
'action' Id_or_op_to_string(ID_OR_OP -> STRING)

  'rule' Id_or_op_to_string(id_op(Id) -> S):
	 id_to_string(Id ->S)

  'rule' Id_or_op_to_string(op_op(Op) -> S):
	 Op_to_string(Op -> S)

'action' Idents_to_boxes(IDENTS -> BOXES)

  'rule' Idents_to_boxes(list(H,T) -> list(string(S),TBS)):
	 id_to_string(H -> S)
	 Idents_to_boxes(T -> TBS)

  'rule' Idents_to_boxes(nil -> nil):

'action' Filenames_to_boxes(FILE_NAMES -> BOXES)

  'rule' Filenames_to_boxes(list(H,T) -> list(string(S),TBS)):
	 fileid_to_string(H -> S)
	 Filenames_to_boxes(T -> TBS)

  'rule' Filenames_to_boxes(nil -> nil):


-------------
--operators
-------------
'action' Op_to_string(OP -> STRING)

--infix_op

  'rule' Op_to_string(eq -> " = "):

  'rule' Op_to_string(neq -> " ~= "):

  'rule' Op_to_string(eqeq -> " == "):

  'rule' Op_to_string(gt -> " > "):

  'rule' Op_to_string(lt -> " < "):

  'rule' Op_to_string(ge -> " >= "):

  'rule' Op_to_string(le -> " <= "):

  'rule' Op_to_string(supset -> " >> "):

  'rule' Op_to_string(subset -> " << "):

  'rule' Op_to_string(supseteq -> " >>= "):

  'rule' Op_to_string(subseteq -> " <<= "):

  'rule' Op_to_string(isin -> " isin "):

  'rule' Op_to_string(notisin -> " ~isin "):

  'rule' Op_to_string(rem -> " \\ "):

  'rule' Op_to_string(caret -> " ^ "):

  'rule' Op_to_string(union -> " union "):

  'rule' Op_to_string(override -> " !! "):

  'rule' Op_to_string(mult -> " * "):

  'rule' Op_to_string(div -> " / "):

  'rule' Op_to_string(hash -> " # "):

  'rule' Op_to_string(inter -> " inter "):

  'rule' Op_to_string(exp -> " ** "):

--prefix_op

  'rule' Op_to_string(abs -> "abs "):

  'rule' Op_to_string(int -> "int "):

  'rule' Op_to_string(real -> "real "):

  'rule' Op_to_string(card -> "card "):

  'rule' Op_to_string(len -> "len "):

  'rule' Op_to_string(inds -> "inds "):

  'rule' Op_to_string(elems -> "elems "):

  'rule' Op_to_string(hd -> "hd "):

  'rule' Op_to_string(tl -> "tl "):

  'rule' Op_to_string(dom -> "dom "):

  'rule' Op_to_string(rng -> "rng "):

  'rule' Op_to_string(wait -> "wait "):

--infix_prefix_op

  'rule' Op_to_string(plus -> " + "):

  'rule' Op_to_string(minus -> " - "):

'condition' Only_binary(OP)

  'rule' Only_binary(eq):

  'rule' Only_binary(neq):

  'rule' Only_binary(eqeq):

  'rule' Only_binary(gt):

  'rule' Only_binary(lt):

  'rule' Only_binary(ge):

  'rule' Only_binary(le):

  'rule' Only_binary(supset):

  'rule' Only_binary(subset):

  'rule' Only_binary(supseteq):

  'rule' Only_binary(subseteq):

  'rule' Only_binary(isin):

  'rule' Only_binary(notisin):

  'rule' Only_binary(exp):

------------
--connective
------------
'action' Connec_to_string(CONNECTIVE -> STRING)

  'rule' Connec_to_string(implies -> " => "):

  'rule' Connec_to_string(or -> " \\/ "):

  'rule' Connec_to_string(and -> " /\\ "):

  'rule' Connec_to_string(not -> "~ "):

------------
--combinator
------------
'action' Comb_to_string(COMBINATOR -> STRING)

  'rule' Comb_to_string(ext_choice -> " |=| "):

  'rule' Comb_to_string(int_choice -> " |^| "):

  'rule' Comb_to_string(parallel -> " || "):

  'rule' Comb_to_string(interlock -> " ++ "):

  'rule' Comb_to_string(sequence -> " ; "):

  --'rule' Comb_to_string(override -> "!!"):

-------------------------------------------------------------------------------
--add comments
-------------------------------------------------------------------------------
'action' Add_comm(BOX -> BOX)

  'rule' Add_comm(B -> CB1):
	 Find_comm( -> TP)
	 (|
	    eq(TP,0)
	    Try_box(B -> CB)
	  ||
	    Get_comm(TP -> C,CS)
	    where(box("",list(C,CS),"","",h_box) -> FCB)
	    Try_box(B -> BB)
	    where(box("",list(FCB,list(string("\t"),list(BB,nil))),"","",v_box)-> CB)
	 |)
	 Nlcomtag -> TAG
	 (|
	    eq(TAG,1)
	    Nlcom -> NC
	    where(box("",list(CB,list(NC,nil)),"","",h_box) -> CB1)
	  ||
	    where(CB -> CB1)
	 |)     
	 

'action' Try_box(BOX -> BOX)

  'rule' Try_box(string(S) -> NB):
	 Nlcomtag -> TAG
	 Nlcom -> NC
	 Nlcomtag <- 0
	 (| eq(S,"\t")
	    (|
	      eq(TAG,1)
	      where(box("",list(NC,list(string(S),nil)),"heh","",h_box) -> NB)
	    ||
	      where(string(S) -> NB)
	    |)
	  ||  
	   Str_and_comm(S -> _,B)
	   (|
	      eq(TAG,1)
	      where(box("",list(NC,list(B,nil)),"heh","",h_box) -> NB)
	    ||
	      where(B -> NB)
	   |)     
	 |)  

  'rule' Try_box(box(ST,BS,SP,ED,BTP) -> NB):
	 Nlcomtag -> TAG
	 Nlcom -> NC
	 Nlcomtag <- 0
	 Try_start(ST -> SYN,STB)
	 Try_boxes(BS,SP -> CBS)
	 Try_end_sp(ED -> ETP)
	 (|
	    eq(SYN,0) 
	    where(box(ST,CBS,SP,ED,BTP) -> B1)
	  ||
	    (|
	       eq(CBS,nil)
	       where(box("",list(STB,CBS),"heh",ED,BTP) -> B1)
	     ||
-- next line puts extra separator after start string
-- if it has a comment attached 	
--	       where(box("",list(STB,CBS),SP,ED,BTP) -> B1)
	       where(box("",CBS,SP,"",BTP) -> B11)
	       where(box("",list(STB,list(B11,nil)),"heh",ED,BTP) -> B1)
	    |)	
	 |)
	 Nlcomtag -> TA
	 Nlcomtag <- 0
	 (|
	    eq(TA,1)
	    (| 
	       ne(ED,"")
	       ne(ED," ")
	       Nlcom -> N
	       where(box("",list(B1,list(N,nil)),"heh","",h_box) -> B2)
	     ||
	       where(B1 -> B2)
	       Nlcomtag <- 1
	    |)   
	  ||
	    where(B1 -> B2)
	 |)     
	 (|
	    eq(ETP,0)
	    where(B2 -> B)
	  ||  
	    Get_comm(ETP -> C,CS)
	    Merge(B2,C,CS,"heh" -> B)
	 |)   
	 (|
	    eq(TAG,1)
	    (|
	       ne(BTP,i_box)
	       where(NC -> N1)
	     ||
	       where(box("",list(NC,nil),"","",i_box) -> N1)
	    |)     
	    (|
	       where(B -> box(_,list(string(S),T),_,_,BP))
	       eq(S,"\t") 
	       where(box("",list(string("\t"),list(N1,T)),"heh","",BP) -> NB)
	     ||
	       where(box("",list(N1,list(B,nil)),"heh","",h_box) -> NB)
	    |)
	  ||
	    where(B -> NB)
	 |)     
       
'action' Str_and_comm(STRING -> INT,BOX)

  'rule' Str_and_comm(S -> YN,B):
	 Skip_string(S -> YN)
	 (|
	    eq(YN,0)
	    where(string(S) -> B)
	  ||
	    Get_comm(YN -> C,CS)
	    Merge(string(S),C,CS,"heh" -> B)
	 |)   

'action' Try_start(STRING -> INT,BOX)

  'rule' Try_start(S -> YN,B):
	 (|
	    (|eq(S,"")||eq(S," ")|)
	    where(0 -> YN)
	    where(string(S) -> B)
	  ||
	    Move_spaces(S -> S1)
	    Str_and_comm(S1 -> YN,B) 
	 |)     
	 
'action' Try_end_sp(STRING -> INT)

  'rule' Try_end_sp(S -> TP):
	 (|
	    (|eq(S,"")||eq(S," ")||eq(S,"   ")|)
	    where(0 -> TP)
	  ||
	    Move_spaces(S -> S1)
	    Skip_string(S1 -> TP)
	 |)     
	 

'action' Try_boxes(BOXES,STRING -> BOXES)

  'rule' Try_boxes(nil,_ -> nil):

  'rule' Try_boxes(list(H,nil),_ -> list(HCB,nil)):
	 Try_box(H -> HCB)

  'rule' Try_boxes(list(H,T),SP -> CBS):
	 Try_box(H -> HCB)
	 Try_end_sp(SP -> TP)
	 Nlcomtag -> TA
	 Nlcomtag <- 0
	 (|
	    eq(TA,1)
	    (| 
	       ne(SP,"")
	       ne(SP," ")
	       ne(SP,"   ")
	       Nlcom -> NC
	       where(box("",list(HCB,list(NC,nil)),"heh","",h_box) -> B)
	     ||
	       where(HCB -> B)
	       Nlcomtag <- 1
	    |)   
	  ||
	    where(HCB -> B)
	 |)     
	 (|
	    eq(TP,0)
	    Try_boxes(T,SP -> TCBS)
	    where(BOXES'list(B,TCBS) -> CBS)
	  ||
	    Get_comm(TP -> C,CS)
	    Merge(B,C,CS,SP -> HCB1)
	    Try_boxes(T,SP -> TCBS)
	    where(BOXES'list(HCB1,TCBS) -> CBS)
	 |)

'action' Get_comm(INT -> BOX,BOXES)

  'rule' Get_comm(TP -> C,CS):
	 (|
	    eq(TP,1)
	    Get_blockcomm( -> C,TP1)
	  ||
	    Get_linecomm( -> C,TP1)
	 |)         	       	 	 	    
	 (|
	    eq(TP1,0)
	    where(BOXES'nil -> CS)
	  ||
	    Get_restcomms(TP1 -> CS)
	 |)

'action' Get_restcomms(INT -> BOXES)

  'rule' Get_restcomms(TP -> list(C,CS)):
	 Get_restcomm(TP -> C,TP1)
	 (|
	    eq(TP1,0)
	    where(BOXES'nil -> CS)
	  ||
	    Get_restcomms(TP1 -> CS)
	 |)

'action' Get_restcomm(INT -> BOX,INT)

  'rule' Get_restcomm(TP -> C,TP1):
	 (|
	    eq(TP,1)
	    Get_blockcomm( -> C,TP1)
	  ||
	    Get_linecomm( -> line_comm(S,SF),TP1)
	    (|
	      eq(TP, 3) -- broken line comment
	      Concatenate("-- ", S -> S1)
	      where(line_comm(S1,SF) -> C)
	    ||
	      where(line_comm(S,SF) -> C)
	    |)
	 |)         	       	 	 	    

'action' Get_blockcomm( -> BOX,INT)

  'rule' Get_blockcomm( -> BC,TP):
	 Block_to_str( -> S,SF,SB,TP)
	 where(block_comm(S,SF,SB) -> BC)

'action' Get_linecomm( -> BOX,INT)

  'rule' Get_linecomm( -> LC,TP):
	 Line_to_str( -> S,SF,TP)
	 where(line_comm(S,SF) -> LC)

'action' Merge(BOX,BOX,BOXES,STRING -> BOX)

  'rule' Merge(B,C:block_comm(_,FT,_),CS,SP -> BC):
	 (|
	    eq(FT,0)
	    where(box("",list(B,list(C,nil)),SP,"",h_box) -> B1)
	    where(box("",list(B1,nil),"","",hv_box) -> B2)
	    where(box("",list(B2,CS),SP,"",h_box) -> BC)
	  ||
	    where(box("",list(C,CS),"","",h_box) -> C1)
	    where(B -> BC)
	    Nlcom <- C1
	    Nlcomtag <- 1
	 |)

  'rule' Merge(B,C:line_comm(_,T),CS,SP -> BC):
	 (|
	    eq(T,0)
	    where(box("",list(B,list(C,nil)),SP,"",h_box) -> B1)
	    where(box("",list(B1,nil),"","",hv_box) -> B2)
	    where(box("",list(B2,CS),SP,"",h_box) -> BC)
	  ||
	    where(box("",list(C,CS),"","",h_box) -> C1)
	    where(B -> BC)
	    Nlcom <- C1
	    Nlcomtag <- 1
	 |)
	         	  
--------------------------------------------------------------------------------
--
--------------------------------------------------------------------------------
'action' Print_box(BOX,BOX_TYPE -> INTE_REP,INT)

  'rule' Print_box(string(S),_ -> IR,0):
	 String_to_rep(S -> IR)

  'rule' Print_box(box(ST,BS,SP,ED,h_box),_ -> IR,0):
	 Nline -> Nl
	 [|
	   eq(Nl,1)
	   Get_varpos( -> X,Y,I)
	   Set_varpos(X+1,I,I)
	   Nline <- 0
	 |]
	 (|
	   ne(ST,"")
	   String_to_rep(ST -> STIR)
	   where(STIR -> at(_,_,L))
	   Indent -> I
	   Indent <- I + L
	   Print_hboxes(BS,SP -> BSIR)
	   Indent <- I
	   Ed_to_rep(ED,combine(STIR,BSIR),0 -> IR,_)
	 ||	   
	   Print_hboxes(BS,SP -> BSIR)
	   Ed_to_rep(ED,BSIR,0 -> IR,_)
	 |)  

  'rule' Print_box(box(ST,BS,SP,ED,v_box),_ -> IR,1):
	 Get_varpos( -> X,Y,I)
	 Nline -> Nl
	 (| 
	    (|gt(Y,I)||eq(Nl,1)|)
	    Set_varpos(X+1,I,I)
	    Nline <- 0
	  ||
	    Curcol <- I
	 |)     
	 String_to_rep(ST -> STIR)
	 where(STIR -> at(_,_,L))
	 Indent <- I + L
	 Print_vboxes(BS,SP -> BSIR)
	 Indent <- I
	 Ed_to_rep(ED,combine(STIR,BSIR),1 -> IR,_)

  'rule' Print_box(box(ST,BS,SP,ED,i_box),BT -> IR,CHANGE):
	 Nline -> Nl
	 [|
	   eq(Nl,1)
	   Get_varpos( -> X,Y,I)
	   Set_varpos(X+1,I,I)
	   Nline <- 0
	 |]
	 Indent -> I
	 Print_iboxes(ST,BS,BT,SP -> BSIR,BCHANGE)
	 Indent <- I
	 Ed_to_rep(ED,BSIR,BCHANGE -> IR,CHANGE)

  'rule' Print_box(box(ST,BS,SP,ED,hv_box),_ -> IR,CHANGE):
	 Nline -> Nl
	 [|
	   eq(Nl,1)
	   Get_varpos( -> X,Y,I)
	   Set_varpos(X+1,I,I)
	   Nline <- 0
	 |]
	 Indent -> I
	 Print_hvboxes(ST,BS,SP -> BSIR,BCHANGE)
	 Indent <- I
	 Ed_to_rep(ED,BSIR,BCHANGE -> IR,CHANGE)

  'rule' Print_box(box(ST,BS,SP,ED,hov_box),_ -> IR,CHANGE):
	 Nline -> Nl
	 [|
	   eq(Nl,1)
	   Get_varpos( -> X,Y,I)
	   Set_varpos(X+1,I,I)
	   Nline <- 0
	 |]
	 Indent -> I
	 Print_hovboxes(BS,SP,ST -> BSIR,BCHANGE)
	 Indent <- I
	 Ed_to_rep(ED,BSIR,BCHANGE -> IR,CHANGE)

  'rule' Print_box(block_comm(S,F,B),_ -> IR,0):  
	 [|
	   eq(F,1)
	   Get_varpos( -> X,Y,I)
	   ne(Y,I)
	   Set_varpos(X+1,I,I)
	 |]
	 Block_to_rep(S,B -> IR)
	 where(B -> CHANGE)

  'rule' Print_box(line_comm(S,F),_ -> IR,0):  
	 [|
	   eq(F,1)
	   Get_varpos( -> X,Y,I)
	   ne(Y,I)
	   Set_varpos(X+1,I,I)
	   Nline <- 0
	 |]
	 Line_to_rep(S -> IR)
	 

'action' Print_inte(INTE_REP)

  'rule' Print_inte(at(S,coord(A,B),L)):
	 Goto(A,B)
	 Putstdmsg(S)
	 Curcol <- B + L

  'rule' Print_inte(inden(IR)):
	 Print_inte(IR)

  'rule' Print_inte(adjust(IR,coord(A,B))):
	 Print_adjust(IR,A,B)

  'rule' Print_inte(combine(L,nil)):
	 Print_inte(L)

  'rule' Print_inte(combine(L,R)):
	 Print_inte(L)
	 Print_inte(R)

----------------------------------------------------------------------------
--gloable variables 
----------------------------------------------------------------------------
'var' Nlcom : BOX

'var' Nlcomtag : INT

'var' Valsp : INT

'var' First : INT

'var' Indent : INT

'var' Rightmargin : INT

'var' Curline : INT

'var' Curcol : INT

'var' Nline : INT

'var' Comm : INT

'var' Tail : INT

'action' Init_var(INT)

  'rule' Init_var(L):
	 Indent <- 0
	 Rightmargin <- L
	 Curline <- 0
	 Curcol <- 0
	 Nline <- 0
	 Comm <- 0 
	 Tail <- 0
-----------------------------------------------------------------------------
--string to inte_rep
-----------------------------------------------------------------------------
'action' String_to_rep(STRING -> INTE_REP)

  'rule' String_to_rep(S -> at(S1,P,L)):
	 Nline -> Nl
	 [|
	   eq(Nl,1)
	   ne(S,"")
	   ne(S," ")
	   ne(S,"   ")
	   Get_varpos( -> X,Y,I)
	   Set_varpos(X+1,I,I)
	   Nline <- 0
	 |]
	 Curline -> X
	 Curcol -> Y
	 where(coord(X,Y) -> P)
	 Rightmargin -> R
	 (|
	    eq(S,"")
	    where(0 -> L)
	    where(S -> S1)
	  ||
	    eq(S," ")
	    (|
	      eq(Y,R+1)
	      where("" -> S1)
	      where(0 -> L)
	    ||
	      eq(S," ")
	      where(S -> S1)
	      where(1 -> L)
	      Curcol <- Y + 1
	    |)
	  ||
	    eq(S,"   ")
	    (|
	      (|eq(Y,R-1)||eq(Y,R)||eq(Y,R+1)|)
	      where("" -> S1)
	      where(0 -> L)
	      Curcol <- R + 1
	    ||
	      where("   " -> S1)
	      where(3 -> L)
	      Curcol <- Y + 3
	    |)          
	  ||
	    where(S -> S1)     
	    Len(S -> L)
	    Curcol <- Y + L
	 |)   

-----------------------------------------------------------------------------
--h_box to int_rep
-----------------------------------------------------------------------------
'action' Print_hboxes(BOXES,STRING -> INTE_REP)

  'rule' Print_hboxes(nil,_ -> nil): 

  'rule' Print_hboxes(BOXES'list(H,nil),SP -> IR):
	 Print_box(H,h_box -> HIR,_)
	 where(combine(HIR,nil) -> IR)
	 [|
	   Tail -> Tl
	   (|eq(Tl,1)||eq(SP,"heh")|)
	   Comm <- 0
	   Tail <- 0
	 |]  

  'rule' Print_hboxes(BOXES'list(H,T),SP ->IR):
	 Print_box(H,h_box -> HIR,_)
	 Sp_to_rep(SP,HIR -> SPIR)
	 Print_hboxes(T,SP -> TIR)
	 where(combine(SPIR,TIR) -> IR)

'action' Ed_to_rep(STRING,INTE_REP,INT -> INTE_REP,INT)

  'rule' Ed_to_rep(ED,HIR,HCHANGE -> IR,CHANGE):
	 Curcol -> CY
	 Rightmargin -> R
	 String_to_rep(ED -> EDIR)
	 Get_varpos( -> X,Y,I)
	 (|
	    (|le(Y,R+1)||gt(CY,R+1)|)
	    where(combine(HIR,combine(EDIR,nil)) -> IR)
	    where(HCHANGE -> CHANGE)
	  ||
	    where(1 -> CHANGE)
	    where(adjust(EDIR,coord(1,I-CY)) -> ED1)
	    Set_varpos(X+1,Y+I-CY,I)
	    where(combine(HIR,combine(ED1,nil)) -> IR)
	 |)         
	   
	 
'action' Sp_to_rep(STRING,INTE_REP -> INTE_REP)

  'rule' Sp_to_rep(SP,HIR -> IR):
	 Curcol -> CY
	 Rightmargin -> R
	 (| eq(SP,"heh")
	    Tail <- 1
	    Sp1_to_rep(" " -> SPIR)
	  ||  
	    Sp1_to_rep(SP -> SPIR)
	 |)   
	 where(combine(HIR,SPIR) -> IR)
-----------------------------------------------------------------------------
--v_box to int_rep
-----------------------------------------------------------------------------
'action' Print_vboxes(BOXES,STRING -> INTE_REP)

  'rule' Print_vboxes(nil,_ -> nil):

  'rule' Print_vboxes(list(H,nil),SP -> IR):
	 Get_varpos( -> X,Y,I)
	 Nline -> Nl
	 (| 
	    (|gt(Y,I)||eq(Nl,1)|)
	    Set_varpos(X+1,I,I)
	    Nline <- 0
	  ||
	    Curcol <- I
	 |)     
	 Print_box(H,v_box -> HIR,_)
	 where(combine(HIR,nil) -> IR)
	 [|
	   Tail -> Tl
	   (|eq(Tl,1)||eq(SP,"heh")|)
	   Comm <- 0
	   Tail <- 0
	 |]  

  'rule' Print_vboxes(list(H,T),SP -> IR):
	 Get_varpos( -> X,Y,I)
	 Nline -> Nl
	 (| 
	    (|gt(Y,I)||eq(Nl,1)|)
	    Set_varpos(X+1,I,I)
	    Nline <- 0
	  ||
	    Curcol <- I
	 |)     
	 Print_box(H,v_box -> HIR,_)
	 Sp_to_rep(SP,HIR -> SPIR)
	 Print_vboxes(T,SP -> TIR)
	 where(combine(SPIR,TIR) -> IR)

------------------------------------------------------------------------------
--i_box to inte_rep
------------------------------------------------------------------------------
'action' Print_iboxes(STRING,BOXES,BOX_TYPE,STRING -> INTE_REP,INT)

  'rule' Print_iboxes(ST,nil,_ ,_-> IR,0):
	 String_to_rep(ST -> IR) 

  'rule' Print_iboxes(ST,list(H,nil),BT,SP -> IR,CHANGE):
 	 (|
	    eq(ST,"")	
	    (|	       
	       eq(BT,v_box)  
	       Get_varpos( -> X,Y,I)
	       Set_varpos(X,I+2,I+2)
	       Print_box(H,BT -> IR,CHANGE)
	       Indent <- I
	     ||
	       Indent -> I
	       Curcol -> Y
	       [|
	         eq(Y,I)
		 Curcol <- I+2
	       |]	 
	       Indent <- I+2
	       Print_box(H,i_box -> HIR,CHANGE)
	       Indent <- I
	       where(inden(combine(HIR,nil)) -> IR)
	    |)
	  ||
	    String_to_rep(ST -> STIR) 
	    where(STIR -> at(_,_,L))
	    Indent -> I
	    Curcol -> Y
	    [|
              eq(Y,I)
	      Curcol <- I+2+L
	    |]	 
	    Indent <- I + L + 2
	    Print_box(H,BT -> HIR,CHANGE)
            where(combine(STIR,HIR) -> IR)
 	 |)  
	 [|
	   Tail -> Tl
	   (|eq(Tl,1)||eq(SP,"heh")|)
	   Comm <- 0
	   Tail <- 0
	 |]

  'rule' Print_iboxes(ST,BS,_,SP -> combine(STIR,IR),CHANGE):
	 Indent -> I
	 String_to_rep(ST -> STIR) 
	 where(STIR -> at(_,_,L))
	 Indent <- I + L
	 Fit_h1(BS,SP -> IR,CHANGE)
	 Indent <- I

'action' Fit_h1(BOXES,STRING -> INTE_REP,INT)

  'rule' Fit_h1(list(H,nil),SP -> IR,CHANGE):
	 Print_box(H,i_box -> HIR,HCHANGE)
	 Get_varpos( -> X,Y,I)
	 Rightmargin -> R
	 (|
	    eq(HCHANGE,1)
	    where(combine(adjust(HIR,coord(0,2)),nil) -> IR)
	    Curcol <- Y+2
	    where(1 -> CHANGE)
	  ||
	    gt(Y,R+1)
	    Get_start(HIR,i_box -> coord(A,B))
	    where(combine(adjust(HIR,coord(1,I+2-B)),nil) -> IR)
	    Set_varpos(X+1,Y+I+2-B,I)
	    where(1 -> CHANGE)
	  ||
	    where(combine(HIR,nil) -> IR)
	    where(0 -> CHANGE)
	 |)
	 [|
	   Tail -> Tl
	   (|eq(Tl,1)||eq(SP,"heh")|)
	   Comm <- 0
	   Tail <- 0
	 |]  

  'rule' Fit_h1(list(H,T),SP -> IR,CHANGE):
	 Print_box(H,i_box -> HIR1,HCHANGE)
	 Sp_to_rep(SP,HIR1 -> HIR)
	 Get_varpos( -> X,Y,I)
	 Rightmargin -> R
	 (| eq(HCHANGE,1)
	    where(1 -> CHANGE)
	    where(adjust(HIR,coord(0,2)) -> FAIR)
	    Set_varpos(X,Y+2,I+2)
	    Fit_h2(T,SP -> TIR,_)
	    where(combine(FAIR,TIR) -> IR)
	  ||
	    gt(Y,R+1)
	    where(1 -> CHANGE)
	    Get_start(HIR,i_box -> coord(A,B))
	    where(adjust(HIR,coord(1,I+2-B)) -> FAIR)
	    Set_varpos(X+1,Y+I+2-B,I+2)
	    Fit_h2(T,SP -> TIR,_)
	    where(combine(FAIR,TIR) -> IR)
	  ||  
	    Fit_h1(T,SP -> TIR,CHANGE)
	    where(combine(HIR,TIR) -> IR)
         |)  

	        
------------------------------------------------------------------------------
--hv_box to inte_rep
------------------------------------------------------------------------------
'action' Print_hvboxes(STRING,BOXES,STRING -> INTE_REP,INT)

  'rule' Print_hvboxes(ST,nil,_ -> IR,0):
	 String_to_rep(ST -> IR) 

  'rule' Print_hvboxes(ST,BS,SP -> IR,CHANGE):
	 Get_varpos( -> CX,CY,CI)
	 Rightmargin -> R
	 (| ne(CY,CI)
	    Set_varpos(CX+1,CI,CI)
	    String_to_rep(ST -> STIR)
	    where(STIR -> at(_,_,L))
	    Indent <- CI + L
	    Fit_h2(BS,SP -> FBS,FCHANGE)
	    where(combine(STIR,FBS) -> FIR)
	    (| eq(FCHANGE,1)
	       where(1 -> CHANGE)
	       where(FIR -> IR)
	     ||
	       Curcol-> Y
	       Curline -> X
	       (| 
	          le(Y-CI+CY,R)
		  le(X-CX,1)
		  where(combine(adjust(FIR,coord(-1,CY-CI)),nil) -> IR)
		  Nline -> Nll
		  where(Nll -> CHANGE)
		  Set_varpos(X-1,Y-CI+CY,CI)
		||
		  where(FIR -> IR)
		  where(1 -> CHANGE)
	       |)
	     |)
	   ||
	     String_to_rep(ST -> STIR)
	     where(STIR -> at(_,_,L))
	     Indent <- CI + L
	     Fit_h2(BS,SP -> BSIR,CHANGE)
	     where(combine(STIR,BSIR) -> IR)
	 |)        	      	    
'action' Fit_h2(BOXES,STRING -> INTE_REP,INT)

  'rule' Fit_h2(nil,_ -> nil,0): 

  'rule' Fit_h2(list(H,nil),SP -> IR,CHANGE):
	 Print_box(H,hv_box -> HIR,HCHANGE)
	 Get_varpos( ->X,Y,I)
	 Rightmargin -> R
	 (| gt(Y,R+1)
	    Get_start(HIR,hv_box -> coord(A,B))
	    (|
	       eq(B,I)
	       where(combine(HIR,nil) -> IR)
	     ||  
	       Set_varpos(X+1,Y+I-B,I)
	       where(combine(adjust(HIR,coord(1,I-B)),nil) -> IR)
	    |)   
	    where( 1 -> CHANGE)
	  ||
	    where(combine(HIR,nil) -> IR)
	    where(HCHANGE -> CHANGE)
	 |)
	 [|
	   Tail -> Tl
	   (|eq(Tl,1)||eq(SP,"heh")|)
	   Comm <- 0
	   Tail <- 0
	 |]

  'rule' Fit_h2(list(H,T),SP -> IR,CHANGE):
	 Print_box(H,hv_box -> HIR1,HCHANGE)
	 Sp_to_rep(SP,HIR1 -> HIR)
	 Rightmargin -> R
	 Get_varpos( -> X,Y,I)
	 (|
	    eq(HCHANGE,1)
	    Fit_h2(T,SP -> TIR,TCHANGE)
	    where(combine(HIR,TIR) -> IR)
	    where(1 -> CHANGE)	    
	  ||  
	    gt(Y,R+1)
	    Get_start(HIR,hv_box -> coord(A,B))
	    (|
	       eq(B,I)
	       where(combine(HIR,nil) -> IR1)
	     ||  
	       Set_varpos(X+1,Y+I-B,I)
	       where(combine(adjust(HIR,coord(1,I-B)),nil) -> IR1)
	    |)   
	    Fit_h2(T,SP -> TIR,TCHANGE)
	    where(combine(IR1,TIR) -> IR)
	    where(1 -> CHANGE)
	  ||
	    le(Y,R)
	    Fit_h2(T,SP -> TIR,TCHANGE)
	    where(combine(HIR,TIR) -> IR)
	    where(TCHANGE -> CHANGE)
	  ||
	    Fit_h2(T,SP -> TIR,TCHANGE)
	    where(combine(HIR,TIR) -> IR)
	    where(1 -> CHANGE)
	 |)
	 
	    
	    
	    
----------------------------------------------------------------------------
--hov_box to inte_rep
----------------------------------------------------------------------------

'action' Print_hovboxes(BOXES,STRING,STRING -> INTE_REP,INT)

  'rule' Print_hovboxes(nil,_,ST -> IR,0): 
	 String_to_rep(ST -> IR) 

  'rule' Print_hovboxes(BS,SP,ST -> IR,CHANGE):
	 Get_varpos( -> CX,CY,CI)
	 Rightmargin -> R
	 (| ne(CY,CI)
	    Set_varpos(CX+1,CI,CI)
	    String_to_rep(ST -> STIR)
	    where(STIR -> at(_,_,L))
	    Indent <- CI + L
	    Try_h(BS,SP -> IR1,BS1,CHANGE1)
	    (|
	       eq(CHANGE1,1)
	       where(1 -> CHANGE)
	       Adjust_ir(IR1 -> AIR)
	       Print_vboxes(BS1,SP -> BSIR)
	       where(combine(STIR,combine(AIR,BSIR)) -> IR)
	     ||
	       Curcol -> Y
	       Curline -> X
	       (|
	          le(Y-CI+CY,R)
		  le(X-CX,1)
		  where(combine(STIR,IR1) -> IR2)
		  where(combine(adjust(IR2,coord(-1,CY-CI)),nil) -> IR)
		  Nline -> Nll
		  where(Nll -> CHANGE)
		  Set_varpos(X-1,Y-CI+CY,CI)
		||
		  where(combine(STIR,IR1) -> IR)
		  where(1 -> CHANGE)
	       |)
	    |)
	  ||
	    String_to_rep(ST -> STIR)
	    where(STIR -> at(_,_,L))
	    Indent <- CI + L
	    Try_h(BS,SP -> IR1,BS1,CHANGE1)
	    (|
	       eq(CHANGE1,1)
	       where(1 -> CHANGE)
	       Adjust_ir(IR1 -> AIR)
	       Print_vboxes(BS1,SP -> BSIR)
	       where(combine(STIR,combine(AIR,BSIR)) -> IR)
	     ||
	       where(0 -> CHANGE)
	       where(combine(STIR,IR1) -> IR)
	    |)
	  |)  

'action' Try_h(BOXES,STRING -> INTE_REP,BOXES,INT)

  'rule' Try_h(list(H,nil),SP -> IR,nil,CHANGE):
	 Print_box(H,hov_box -> HIR,HCHANGE)
	 Get_varpos( -> X,Y,I)
	 Rightmargin -> R
	 (| gt(Y,R+1)
	    Get_start(HIR,hv_box -> coord(A,B))
	    (|
	       eq(B,I)
	       where(combine(HIR,nil) -> IR)
	     ||  
	       Set_varpos(X+1,Y+I-B,I)
	       where(combine(adjust(HIR,coord(1,I-B)),nil) -> IR)
	    |)   
	    where( 1 -> CHANGE)
	  ||
	    where(combine(HIR,nil) -> IR)
	    where(HCHANGE -> CHANGE)
	 |)
	 [|
	   Tail -> Tl
	   (|eq(Tl,1)||eq(SP,"heh")|)
	   Comm <- 0
	   Tail <- 0
	 |]

  'rule' Try_h(list(H,T),SP -> IR,BS,CHANGE):
	 Print_box(H,hov_box -> HIR1,HCHANGE)
	 Sp_to_rep(SP,HIR1 -> HIR)
	 Rightmargin -> R
	 Get_varpos( ->X,Y,I)
	 Nline -> Nll
	 (|
	    (|eq(HCHANGE,1)||eq(Nll,1)|)
	    where(1 -> CHANGE)
	    where(combine(HIR,nil) -> IR)
	    where(T -> BS)     
	  ||
	    gt(Y,R+1)
	    Get_start(HIR,hov_box -> coord(A,B))
	    (|
	       eq(B,I)
	       where(combine(HIR,nil) -> IR)
--	       Set_varpos(X+1,I,I)
	     ||  
	       Set_varpos(X+1,Y+I-B,I)
	       where(combine(adjust(HIR,coord(1,I-B)),nil) -> IR)
	    |)   
	    where(1 -> CHANGE)
	    where(T -> BS)  
	  ||
	    le(Y,R)
	    Try_h(T,SP -> TIR,TBS,TCHANGE)
	    where(combine(HIR,TIR) -> IR)
	    where(TBS -> BS)
	    where(TCHANGE -> CHANGE)
	  ||
	    where(combine(HIR,nil) -> IR)
	    where(T -> BS)
	    where(1 -> CHANGE)
	  |)
	        
'action' Adjust_ir(INTE_REP -> INTE_REP)

  'rule' Adjust_ir(combine(L,nil) -> L):

  'rule' Adjust_ir(combine(L,at(S,P,LEN)) -> combine(L,at(S,P,LEN))):
 
  'rule' Adjust_ir(combine(L,R) -> AIR):
	 Get_end(L -> coord(A,_))
	 Adjust_rear(R,A -> AR)
	 where(combine(L,AR) -> AIR)

'action' Adjust_rear(INTE_REP,INT -> INTE_REP)

  'rule' Adjust_rear(combine(L,nil),A -> IR):
	 Get_start(L,hov_box -> coord(LA,LB))
	 Get_varpos( -> X,Y,I)
	 where(adjust(L,coord(A+1-LA,I-LB)) -> AIR)
	 where(combine(AIR,nil) -> IR)
	 Set_varpos(X+A+1-LA,Y+I-LB,I)

  'rule' Adjust_rear(combine(L,R),A -> IR):
	 Get_start(L,hov_box -> coord(LA,LB))
	 Get_end(L -> coord(RA,_))
	 Indent -> I
	 where(adjust(L,coord(A+1-LA,I-LB)) -> LIR)
	 Adjust_rear(R,RA+A+1-LA -> RIR)
	 where(combine(LIR,RIR) -> IR)
	 
'action' Sp1_to_rep(STRING -> INTE_REP)

  'rule' Sp1_to_rep(SP -> IR):
	 Check_sp(SP -> S1)
	 String_to_rep(S1 -> IR)

'action' Check_sp(STRING -> STRING)

  'rule' Check_sp(SP -> S):
	 Comm -> C
	 (|
	    eq(C,1)
	    where("" -> S)
	    Comm <- 0
	  ||
	    where(SP -> S)
	 |)   
	 
----------------------------------------------------------------------------
--block comments to inte_rep
----------------------------------------------------------------------------
'action' Block_to_rep(STRING,INT -> INTE_REP)

  'rule' Block_to_rep(S,B -> IR):
	 Get_varpos( -> X,Y,I)
	 Len(S -> L)
	 where(at(S,coord(X,Y),L) -> IR)
	 Curcol <- Y + L
	 Comm <- 1
	 [|
	   eq(B,1)
	   Nline <- 1
	 |]     

----------------------------------------------------------------------------
--line comments to inte_rep
----------------------------------------------------------------------------
'action' Line_to_rep(STRING -> INTE_REP)

  'rule' Line_to_rep(S -> IR):
	 Get_varpos( -> X,Y,I)
	 Len(S -> L)
	 where(at(S,coord(X,Y),L) -> IR)
	 Curcol <- Y + L
	 Nline <- 1
	 Comm <- 1

----------------------------------------------------------------------------
--
----------------------------------------------------------------------------
'action' Get_start(INTE_REP,BOX_TYPE -> POSN)

  'rule' Get_start(at(_,P,_),_ -> P):

  'rule' Get_start(adjust(IR,coord(A,B)),BT -> P):
	 Get_start(IR,BT -> coord(X,Y))
	 where(coord(X+A,Y+B) -> P)

  'rule' Get_start(inden(IR),BT -> P):
	 (|
	    (|eq(BT,hov_box)||eq(BT,hv_box)|)
       	    Get_start(IR,BT -> coord(X,Y))
	    where(coord(X,Y-2) -> P)
	  ||
	    Get_start(IR,BT -> P)
	 |)   

  'rule' Get_start(combine(L,R),BT -> P):
	 Get_start(L,BT -> P)

'action' Get_end(INTE_REP -> POSN)

  'rule' Get_end(at(_,P,_) -> P):

  'rule' Get_end(adjust(IR,coord(A,B)) -> P):
	 Get_end(IR -> coord(X,Y))
	 where(coord(X+A,Y+B) -> P)

  'rule' Get_end(inden(IR) -> P):
	 Get_end(IR -> P)

  'rule'  Get_end(combine(L,nil) -> P):
	 Get_end(L -> P)

  'rule' Get_end(combine(L,R) -> P):
	 Get_end(R -> P)

'action' Get_varpos( -> INT,INT,INT)

  'rule' Get_varpos( -> X,Y,I):
	 Curline -> X
	 Curcol -> Y
	 Indent -> I

'action' Set_varpos(INT,INT,INT)

  'rule' Set_varpos(X,Y,I):
	 Curline <- X
	 Curcol <- Y
	 Indent <- I

----------------------------------------------------------------------------
--inte_rep to text
----------------------------------------------------------------------------
'action' Goto(INT,INT)

  'rule' Goto(A,B):
	 Curline -> X
	 Curcol -> Y
	 (|
	    eq(X,A)
	    eq(Y,B)
	  ||
	    gt(A,X)
	    Putstdnl
	    Curline <- X +1
	    Curcol <- 0
	    Goto(A,B)
	  ||
	    gt(B,Y)
	    Putstdmsg(" ")
	    Curcol <- Y + 1
	    Goto(A,B)
	 |)

'action' Print_adjust(INTE_REP,INT,INT)

  'rule' Print_adjust(at(S,coord(X,Y),L),A,B):
	 Goto(X+A,Y+B)
	 Putstdmsg(S)
	 Curline <- X + A
	 Curcol <- Y + B + L

  'rule' Print_adjust(inden(IR),A,B):
	 Print_adjust(IR,A,B)

  'rule' Print_adjust(adjust(IR,coord(X,Y)),A,B):
	 Print_adjust(IR,X+A,Y+B)

  'rule' Print_adjust(combine(L,nil),A,B):
	 Print_adjust(L,A,B)

  'rule' Print_adjust(combine(L,R),A,B):
	 Print_adjust(L,A,B)
	 Print_adjust(R,A,B)   	 
