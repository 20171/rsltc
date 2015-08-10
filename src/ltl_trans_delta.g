'module' ltl_trans_delta


'export' TransDeltaProperty  Init_LTL_file Close_LTL_file
'use' ast print ext env objects values types pp cc cpp ltl_out  fdr_gen_ast



-----------------------------
----- open/close file -------
------------------------------

'action' Init_LTL_file

  'rule' Init_LTL_file:
         Module_name -> S	    -- in env.g (STRING)
         string_to_id(S -> Id)  -- in idents.c
         OpenLTLFile(Id -> _)   -- in files.c
         SetFileIndentSpace(4)  -- in files.c


'action' Close_LTL_file

  'rule' Close_LTL_file:
         CloseOutputFile()

-------------------------------
---------  main ---------------
-------------------------------

'action' TransDeltaProperty(VALUE_EXPR,Value_id,DECLS)

  'rule' TransDeltaProperty(E,Process_id,Decls):

         DefaultPos(->P)
         where(ax_prefix(P,not,E) -> E1)
         Move_Not(E1 -> NE)
         Trans_to_Delta(NE->ED)
         LTL_out_expr(ED,Decls,Process_id)


-------------------------------
-----     MoveNot     --------
-------------------------------

'action' Move_Not(VALUE_EXPR -> VALUE_EXPR)

  'rule' Move_Not(ax_prefix(P,C,E)-> NE)
	     (|
	       eq(C, not )
 	       Negate(E -> NE)
         ||
           Move_Not(E->NE1)
           where (ax_prefix(P,C,NE1) -> NE) 
         |)

  'rule' Move_Not(bracket(P,E) -> bracket(P,NE))
	     Move_Not(E->NE)

  'rule' Move_Not(ax_infix(P,E1,C,E2,PRE)-> ax_infix(P,NE1,C,NE2,PRE))
         Move_Not(E1 -> NE1)
	     Move_Not(E2 -> NE2)

  'rule' Move_Not(V:val_occ(_,_,_) -> V):

  'rule' Move_Not(application(P,Fun,Args) -> NE):
	     (|
	       where(Fun -> val_occ(_,I,_))
	       (|
             Id_of_R -> R
             eq(I, R)
	         where(Args -> list(fun_arg(P1,list(E1,list(E2,nil))), nil))
		     Move_Not(E1->NE1)  
             Move_Not(E2->NE2)  
             where(fun_arg(P1,list(NE1, list(NE2, nil))) -> Arg)                     
		     where(application(P, val_occ(P, R, nil), list(Arg, nil)) -> NE)
           ||
	         Id_of_U -> U
	         eq(I, U)
	         where(Args -> list(fun_arg(P1,list(E1,list(E2,nil))), nil))
		     Move_Not(E1->NE1)  
             Move_Not(E2->NE2)  
             where(fun_arg(P1,list(NE1, list(NE2, nil))) -> Arg)                     
		     where(application(P, val_occ(P, U, nil), list(Arg, nil)) -> NE)
	       ||
	         Id_of_G -> G
	         Id_of_F -> F
	         Id_of_X -> X
	         (| eq(I, G) || eq(I, F) || eq(I, X) |)
	         where(Args -> list(fun_arg(P1,list(E,nil)), nil))
		     Move_Not(E->NE1)                         
             where(fun_arg(P1, list(NE1, nil)) -> Arg)                     
		     where(application(P, val_occ(P, I, nil), list(Arg, nil)) -> NE)
           ||
	         where(application(P,Fun,Args) -> NE)
           |)
	     ||
	       where(application(P,Fun,Args) -> NE)
         |) 

----------    Negate   -----------

'action' Negate(VALUE_EXPR -> VALUE_EXPR)

  'rule' Negate(ax_infix(P,E1,C,E2,PRE) -> NE)
	     Negate(E2->NE2)
         (|
           eq(C,implies)
	       where(ax_infix(P,E1,and,NE2,PRE) ->NE1)
           where(VALUE_EXPR'bracket(P,NE1)->NE)    
         ||
           eq(C,and)
	       Negate(E1 -> NE1)
	       where(ax_infix(P,NE1, or,NE2,PRE)->NE3)
           where(VALUE_EXPR'bracket(P,NE3)->NE) 
         ||
           eq(C,or)
	       Negate(E1 -> NE1)
	       where(ax_infix(P,NE1, and,NE2,PRE)->NE3)
           where(VALUE_EXPR'bracket(P,NE3)->NE) 
         |)

  'rule' Negate(V:var_occ(P,_,_) -> ax_prefix(P,not,V))

  'rule' Negate(ax_prefix(P,C,E) -> NE)
         (|
           eq(C,not)
		   where(E -> NE)
	     ||
           where(ax_prefix(P, not, ax_prefix(P,C,E)) -> NE)
         |)

  'rule' Negate(application(P,Fun,Args) -> DE):
	  (|
	    where(Fun -> val_occ(_,I,_))
	    (|
	      Id_of_G -> G
	      eq(I, G)
	      where(Args -> list(fun_arg(P1,list(E,nil)), nil))
		  Negate(E-> NE)
		  where(fun_arg(P1,list(NE, nil)) -> Arg)
		  Id_of_F -> F
		  where(application(P, val_occ(P, F, nil), list(Arg, nil)) -> DE)
        ||
	      Id_of_F -> F
	      eq(I, F)
	      where(Args -> list(fun_arg(P1,list(E,nil)), nil))
		  Negate(E->NE)
		  where(fun_arg(P1,list(NE, nil)) -> Arg)
	      Id_of_G -> G
		  where(application(P, val_occ(P, G, nil), list(Arg, nil)) -> DE)
        ||
	      Id_of_X -> X
	      eq(I, X)
	      where(Args -> list(fun_arg(P1,list(E,nil)), nil))
		  Negate(E->NE)
		  where(fun_arg(P1,list(NE, nil)) -> Arg)
		  where(application(P, val_occ(P, X, nil), list(Arg, nil)) -> DE)
        ||
          Id_of_R -> R
	      eq(I, R)
	      where(Args -> list(fun_arg(P1,list(E1,list(E2,nil))), nil))
		  Negate(E1->NE1)
          Negate(E2->NE2)
          where(fun_arg(P1,list(NE1, list(NE2, nil))) -> Arg)                     
	      Id_of_U -> U
		  where(application(P, val_occ(P, U, nil), list(Arg, nil)) -> DE1)
          where(VALUE_EXPR'bracket(P,DE1)->DE) 
        ||
	      Id_of_U -> U
	      eq(I, U)
	      where(Args -> list(fun_arg(P1,list(E1,list(E2,nil))), nil))
		  Negate(E1->NE1)
          Negate(E2->NE2)  
          where(fun_arg(P1,list(NE1, list(NE2, nil))) -> Arg)                     
          Id_of_R -> R
		  where(application(P, val_occ(P, R, nil), list(Arg, nil)) -> DE1)
          where(VALUE_EXPR'bracket(P,DE1)->DE) 
        |)
	   ||
	     where(ax_prefix(P,not,application(P,Fun,Args)) -> DE)
       |)
	    
-- anything else, just precede with not
  'rule' Negate(E -> ax_prefix(P,not,E)):
  	     DefaultPos(-> P)


------------------------------------
---------  Trans_to_Delta ---------
-----------------------------------


'action' Trans_to_Delta(VALUE_EXPR -> VALUE_EXPR)

  'rule' Trans_to_Delta(bracket(P,E) -> bracket(P,DE))
	     Trans_to_Delta(E->DE)


  'rule' Trans_to_Delta(application(P,Fun,Args) -> DE):
	     (|
	       where(Fun -> val_occ(_,I,_))
	       (|
		   Id_of_G -> G
	       eq(I, G)
	       where(Args -> list(fun_arg(P1,list(E,nil)), nil))
		   Trans_to_Delta(E->DE2)
		   where(application(P, Fun, list(fun_arg(P1,list(literal_expr(P,delta),nil)), nil)) -> DE1) -- G(Delta)
		   where(fun_arg(P1,list(DE1, list(DE2, nil))) -> Arg)
		   Id_of_R -> R
		   where(application(P, val_occ(P, R, nil), list(Arg, nil)) -> DE)
	       ||
		   Id_of_F -> F
	       eq(I, F)
	       where(Args -> list(fun_arg(P1,list(E,nil)), nil))
		   Trans_to_Delta(E->DE2)
		   where(ax_prefix(P,not,literal_expr(P,delta)) -> DE1) -- !Delta
		   where(fun_arg(P1,list(DE1, list(DE2, nil))) -> Arg)
		   Id_of_U -> U
		   where(application(P, val_occ(P, U, nil), list(Arg, nil)) -> DE)
	       ||
		   Id_of_X -> X
	       eq(I, X)
	       where(Args -> list(fun_arg(P1,list(E,nil)), nil))
		   Trans_to_Delta(E->DE2)                         
           where(fun_arg(P1, list(DE2, nil)) -> Arg)   
		   where(ax_prefix(P,not,literal_expr(P,delta)) -> DE1) -- !Delta
		   where(application(P, val_occ(P, X, nil), list(Arg, nil)) -> DE3) ---X(T(phi))
		   where (ax_infix(P,DE1,and,DE3,P) ->DE)   ---!Delta /\ X(T(phi))
           ||
		   Id_of_U -> U
	       eq(I, U)
	       where(Args -> list(fun_arg(P1,list(E1,list(E2,nil))), nil))
		   Trans_to_Delta(E1->DE1) ---T(phi)
           Trans_to_Delta(E2->DE2) --- T(psi)       
		   where(ax_prefix(P,not,literal_expr(P,delta)) -> DE3) -- !Delta
		   where (ax_infix(P,DE3,and,DE1,P) ->DE4)   ---- !Delta /\ T(phi)
           where(fun_arg(P1,list(DE4, list(DE2, nil))) -> Arg)                     
		   where(application(P, val_occ(P, U, nil), list(Arg, nil)) -> DE) --- (!Delta /\ T(phi)) U T(psi)
           ||
		   Id_of_R -> R
	       eq(I, R)
	       where(Args -> list(fun_arg(P1,list(E1,list(E2,nil))), nil))
		   Trans_to_Delta(E1->DE1)  ---T(phi)
           Trans_to_Delta(E2->DE2)  ---T(psi)
           Id_of_G -> G
		   where(application(P, val_occ(P,G,nil), list(fun_arg(P1,list(literal_expr(P,delta),nil)), nil)) -> DE3) -- G(Delta)
		   where (ax_infix(P,DE3,or,DE1,P) ->DE4)   ---- G(Delta) \/ T(phi)
           where(fun_arg(P1,list(DE4, list(DE2, nil))) -> Arg)                     
		   where(application(P, val_occ(P, R, nil), list(Arg, nil)) -> DE) --- (G(Delta) \/ T(phi)) R T(psi)
	       |)
	       ||
	       where(application(P,Fun,Args) -> DE)
	     |)

  'rule' Trans_to_Delta(ax_infix(P,E1,C,E2,PRE)->DE)
         (|
           eq(C,and)
           Trans_to_Delta(E1 ->DE1)
           Trans_to_Delta(E2 ->DE2)
           where(ax_infix(P,DE1,and,DE2,PRE)->DE)
         ||
           eq(C,or)
           Trans_to_Delta(E1 ->DE1)
           Trans_to_Delta(E2 ->DE2)
           where(ax_infix(P,DE1,or,DE2,PRE)->DE)
         ||
           eq(C,implies)
           Trans_to_Delta(E1 ->DE1)
           Trans_to_Delta(E2 ->DE2)
           where(ax_infix(P,DE1,implies,DE2,PRE)->DE)       
         |)

-- anything else - translation is itself
  'rule' Trans_to_Delta(E -> E):


