-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the concrete syntax of RSL and the rules to
-- generate the abstract syntax tree
-- plus the root action
-- plus the actions to deal with the context, scheme parameters,
-- and top level module

-- Note that the make file assumes that all the concrete syntax is
-- defined in this file

'module' grammar

'use' ast ext env print types values objects cc pp cpp sml
      pvs pvs_aux sal sal_global_vars fdr rtt

---------------------------------------------------------------
-- Start
---------------------------------------------------------------

'root'
    Init_env
    lib_module(-> M, G)
    PrintVersion()
    Set_module_name_and_pos(M)
    (|
      PpWanted()
      PpLength( -> L)
      Pretty_print(M, L)
    ||
      GraphWanted()
      Make_dependency_graph(M, G)
    ||
      DepsWanted()
      Print_module_deps(M, G)
    ||
      [|
        RTTWanted()
        gen_rtt_ascii(M)
      |]
      [|
	SMLWanted()
	Init_SML_vars
	Init_SML_file
      |]
      [|
	FDRWanted()
	FDR_init
      |]
      [|
	CPPWanted()
	CPP_init
      |]
      [|
	PVSWanted()
	PVS_init(M)
      |]
      [|
	SALWanted()
	SAL_init
      |]
      Make_env(M, G)
      [|
	SALWanted()
	SAL_Translate
      |]
    |)


'nonterm' Init_env

  'rule' Init_env:
	 Current <- nil
	 Extend_paths <- list(nil,nil)
	 Polynum <- 100
	 Type_numbers <- nil
	 -- Dummy_ids used for checking implementation relations
	 string_to_id("_" -> Dummy_id1)
	 Dummy_id1 <- Dummy_id1
	 string_to_id("__" -> Dummy_id2)
	 Dummy_id2 <- Dummy_id2
	 string_to_id("Time" -> Time_id)
	 Time_id <- Time_id
	 InitCcVar
	 Make_op_types
	 Define_SAL_property_funs
	 Clear_LTL_Wanted
	 Clear_Has_LTL


'action' Make_env(LIB_MODULE, LIB_MODULES)

  'rule' Make_env(M, G):
-- debug
-- Putmsg("Module name and position is ")
-- Module_name -> S
-- Putmsg(S)
-- Putmsg(":")
-- Get_module_pos(-> P)
-- Puterror(P)
-- Putnl()
	 Make_globals(G)
	 Make_top_env(M)

-- The first parameter holds the context files not yet processed
-- The second holds those that could not be processed because they have
-- non-empty contexts - they are waiting
-- The third is used to indicate whether one pass through the globals
-- found a context file it could process
-- When a file is processed it is removed from the contexts of the
-- others
-- If a pass is completed (todo becomes nil) and waiting is not nil
-- then we do another pass with waiting becoming todo if found is not
-- nil; otherwise there is a circular dependency
'action' Make_globals(LIB_MODULES)

  'rule' Make_globals(M):
	 Globals <- nil
	 Parameters <- nil
	 Make_globals1(M,nil,nil)

'action' Make_globals1(todo:LIB_MODULES, waiting:LIB_MODULES, found:FOUND)

  'rule' Make_globals1(list(S, M), W, F):
	 where(S -> scheme(_,Cont,Cont1,D))
	 (|
	   eq(Cont,nil)
	   where(D -> sdef(P, Id, PARMS, CL))
(| CcWanted() Putmsg("Loading ") || Putmsg("Checking ") |)
Print_id(Id)
Putmsg(" ... ")
Putnl()
	   New_scheme_id(P, Id, Cont1 -> I)
	   Parameters <- nil
	   Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,nil,nil),nil)
	   Extend_paths <- list(nil,nil)
	   Make_parameters(P, PARMS, lower)
	   Make_basic_env(CL)
	   Complete_type_env(CL)
	   Make_value_env(CL)
	   Check_value_env(CL)
	   [|
	     PVSWanted()
	     Process_Global_Scheme(Id, Cont1, PARMS, CL)
	   |]
	   Generate_confidence_conditions(CL, lower)
Putmsg("Finished ")
Print_id(Id)
Putnl()
	   Current -> current_env(CE1, C)
	   Current <- C
	   Extend_paths -> list(Path,Paths)
	   Extend_paths <- Paths
	   Parameters -> ME
	   Parameters <- nil
	   I'Params <- ME
	   I'Class <- CL
	   Globals -> G
	   Globals <- scheme_env(I,G)
	   Remove_context_id(Id, M -> M1)
	   Remove_context_id(Id, W -> W1)
	   Make_globals1(M1, W1, found)
	 ||
	   Make_globals1(M, list(S,W), F)
	 |)
  
  'rule' Make_globals1(list(O, M), W, F):
	 where(O -> object(_,Cont,Cont1,D))
	 (|
	   eq(Cont,nil)
	   where(D -> odef(P,Id,TS,CL))
Putmsg("Checking ")
Print_id(Id)
Putmsg(" ... ")
Putnl()
	   New_object_id(P, Id -> I)
	   Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,nil,nil),nil)
	   Extend_paths <- list(nil,nil)
	   Make_basic_env(CL)
	   Complete_type_env(CL)
	   Current -> current_env(CE, C)
	   Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,nil,nil),C)
	   [|
	     ne(TS, nil)
	     Make_single_typing(TS -> TP)
	     Define_value_typing(TP)
	     where(TP -> single(_,_,T))
	     Resolve_type(T -> T1)
	     I'Params <- param_type(T1)
	   |]
	   Current -> current_env(PCE, C1)
	   I'Param_env <- PCE
	   Current <- current_env(CE,current_env(PCE, C1))
	   Extend_paths -> Paths
	   Extend_paths <- list(nil, Paths)
	   Make_value_env(CL)
	   Check_value_env(CL)
Putmsg("Finished ")
Print_id(Id)
Putnl()
	   Generate_confidence_conditions(CL, lower)
	   Current -> current_env(CE1, current_env(PCE1, C2))
	   Qualify_class_env(I, CE1 -> CE2)
	   I'Env <- CE2
	   [|
	     SMLWanted()
	     SML_global_object(Id, I, CL)
	   |]
	   [|
	     FDRWanted()
--	     FDR_global_object(Id, I, CL)
	   |]
	   [|
	     CPPWanted()
	     CPP_global_object(Id, I, CL)
	   |]
	   [|
	     PVSWanted()
	     Process_Global_Object(Id, Cont1, I, CL)
	   |]
	   [|
	     SALWanted()
	     SAL_Process_Top_Level_Object(Id, Cont1, I, CL)
	   |]
	   Globals -> G
	   Globals <- object_env(I,G)
	   Current <- C2
	   Extend_paths -> list(Path, list(Path1, Paths1))
	   Extend_paths <- Paths1
	   Remove_context_id(Id, M -> M1)
	   Remove_context_id(Id, W -> W1)
	   Make_globals1(M1, W1, found)
	 ||
	   Make_globals1(M, list(O,W), F)
	 |)

  'rule' Make_globals1(list(T, M), W, F):
	 where(T -> theory(_,Cont,Cont1,D))
	 (|
	   eq(Cont,nil)
	   where(D -> theory_def(P, Id, Axs))
Putmsg("Checking ")
Print_id(Id)
Putmsg(" ... ")
Putnl()
	   New_theory_id(P, Id -> I)
	   Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,nil,nil),nil)
	   Extend_paths <- list(nil,nil)
	   Make_basic_env(basic(list(axiom_decl(P, Axs),nil)))
	   Complete_type_env(basic(list(axiom_decl(P, Axs),nil)))
	   Make_value_env(basic(list(axiom_decl(P, Axs),nil)))
	   Check_value_env(basic(list(axiom_decl(P, Axs),nil)))
Putmsg("Finished ")
Print_id(Id)
Putnl()
	   [|
	     AllCcWanted()
	     Generate_confidence_conditions(basic(list(axiom_decl(P, Axs),nil)), lower)
	   |]
	   Current -> current_env(CE, C)
	   I'Env <- CE
	   [|
	     PVSWanted()
	     Process_Global_Theory(Id, Cont1, basic(list(axiom_decl(P, Axs),nil)))
	   |]
	   Globals -> G
	   Globals <- theory_env(I,G)
	   Current <- C
	   Extend_paths -> list(Path,Paths)
	   Extend_paths <- Paths
	   Remove_context_id(Id, M -> M1)
	   Remove_context_id(Id, W -> W1)
	   Make_globals1(M1, W1, found)
	 ||
	   Make_globals1(M, list(T,W), F)
	 |)

  'rule' Make_globals1(list(R, M), W, F):
	 where(R -> devt_relation(_,Cont,Cont1,D))
	 (|
	   eq(Cont,nil)
	   where(D -> devt_relation_def(P,Id,Id1,Id2,Ax))
Putmsg("Checking ")
Print_id(Id)
Putmsg(" ... ")
Putnl()
	   New_theory_id(P, Id -> I)
	   Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,nil,nil),nil)
	   Extend_paths <- list(nil,nil)
	   Make_basic_env(basic(list(axiom_decl(P, list(axiom_def(P,nil,Ax),nil)),nil)))
	   Complete_type_env(basic(list(axiom_decl(P, list(axiom_def(P,nil,Ax),nil)),nil)))
	   Make_value_env(basic(list(axiom_decl(P, list(axiom_def(P,nil,Ax),nil)),nil)))
	   Check_value_env(basic(list(axiom_decl(P, list(axiom_def(P,nil,Ax),nil)),nil)))
Putmsg("Finished ")
Print_id(Id)
Putnl()
	   [|
	     AllCcWanted()
	     Generate_confidence_conditions(basic(list(axiom_decl(P, list(axiom_def(P,nil,Ax),nil)),nil)), lower)
	   |]
	   [|
	     PVSWanted()
	     Process_Global_Theory(Id, Cont1, basic(list(axiom_decl(P, list(axiom_def(P,nil,Ax),nil)),nil)))
	   |]
	   Current -> current_env(CE, C)
	   I'Env <- CE
	   Globals -> G
	   Globals <- theory_env(I,G)
	   Current <- C
	   Extend_paths -> list(Path,Paths)
	   Extend_paths <- Paths
	   Remove_context_id(Id, M -> M1)
	   Remove_context_id(Id, W -> W1)
	   Make_globals1(M1, W1, found)
	 ||
	   Make_globals1(M, list(R,W), F)
	 |)

  'rule' Make_globals1(nil, nil, F):

  'rule' Make_globals1(nil, W, F):
	 (|
	   eq(F,found)
	   Make_globals1(W, nil, nil)
	 ||
	   (|
	     where(W -> list(scheme(_,_,_,sdef(_,Id,_,_)),_))
	   ||
	     where(W -> list(object(_,_,_,odef(_,Id,_,_)),_))
	   ||
	     where(W -> list(theory(_,_,_,theory_def(_,Id,_)),_))
	   ||
	     where(W -> list(devt_relation(_,_,_,devt_relation_def(_,Id,_,_,_)),_))
	   |)
	   Putmsg("Dependencies for module ")
	   Print_id(Id)
	   ErrorUsage(" are circular")
	 |)

'action' Make_parameters(POS, OBJECT_DEFS, MODULE_CATEGORY)

  'rule' Make_parameters(_, nil, _):
	 Parameters <- nil

  'rule' Make_parameters(P, DS, Cat):
	 Current -> C
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,nil,nil),C)
	 Extend_paths -> Paths
	 Extend_paths <- list(nil, Paths)
	 Make_basic_env(basic(list(object_decl(P, DS),nil)))
-- debug
-- Putmsg("Type checking parameters")
-- Putnl()
	 Complete_type_env(basic(list(object_decl(P, DS),nil)))
	 Make_value_env(basic(list(object_decl(P, DS),nil)))
	 Check_value_env(basic(list(object_decl(P, DS),nil)))
	 Generate_confidence_conditions(basic(list(object_decl(P, DS),nil)), Cat)
	 Get_current_modules(-> ME)
-- debug
-- Putmsg("Parameters: ")
-- where(ME -> object_env(I,ME1))
-- I'Env -> class_env(TYP,VAL,_,_,_,_,_,_)
-- Print_type_env(TYP)
-- print(TYP)
-- Print_value_envs(VAL)
-- print(VAL)
	 Parameters <- ME
	 Extend_paths <- Paths
	 Current <- C
	 
'action' Make_top_env(LIB_MODULE)

  'rule' Make_top_env(scheme(_, C, _, sdef(P, Id, PARMS, CL))):
Putmsg("Checking ")
Print_id(Id)
Putmsg(" ... ")
Putnl()
	 Parameters <- nil
	 Extend_paths <- list(nil,nil)
	 Current <-
	 current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,nil,nil),nil)
	 Make_parameters(P, PARMS, top)
	 Parameters -> ME
	 Make_basic_env(CL)
	 Complete_type_env(CL)
	 Make_value_env(CL)
	 Check_value_env(CL)
Putmsg("Finished ")
Print_id(Id)
Putnl()
	 (|
	   SMLWanted()
	   (|
	     eq(PARMS, nil)
             Translate_to_SML(Id, CL)
	   ||
	     Puterror(P)
	     Putmsg("Top level scheme may not have parameters")
	     Putnl
	   |)
	 ||
	   CPPWanted()
	   (|
	     eq(PARMS, nil)
             Translate_to_CPP(Id, CL, scheme)
	   ||
	     Puterror(P)
	     Putmsg("Top level scheme may not have parameters")
	     Putnl
	   |)
	 ||
	   PVSWanted()
	   Process_Scheme(Id, C, P, PARMS, CL)
	 ||
	   SALWanted()
	   SAL_Process_Top_Level_Scheme(Id,C,PARMS,CL)
	 ||
	   FDRWanted()         
	   FDR_Translate_Scheme(Id, C, P,PARMS, CL)
         ||
	   Generate_confidence_conditions(CL, top)
	 |)
-- debug
-- Current -> C11
-- print(C11)

-- debug -- J890621
-- Get_current_env(-> basic_env(TYP,VAL,_,_,MOD,_,_,_))
-- Print_type_env(TYP)
-- -- print(TYP)
-- Print_value_envs(VAL)
-- -- print(VAL)
-- Print_module_env(MOD)

  'rule' Make_top_env(object(_, C, _, odef(P, Id, TS, CL))):
Putmsg("Checking ")
Print_id(Id)
Putmsg(" ... ")
Putnl()
	 Current <-
	   current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,nil,nil),nil)
	 Extend_paths <- list(nil,nil)
	 Make_basic_env(CL)
	 Complete_type_env(CL)
	 Current -> current_env(CE, C1)
	 Current <- current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,nil,nil),C1)
	 [|
	   ne(TS, nil)
	   Make_single_typing(TS -> TP)
	   Define_value_typing(TP)
	 |]
	 Current -> current_env(PCE, C2)
	 Current <- current_env(CE,current_env(PCE, C2))
	 Extend_paths -> Paths
	 Extend_paths <- list(nil, Paths)
	 Make_value_env(CL)
	 Check_value_env(CL)
Putmsg("Finished ")
Print_id(Id)
Putnl()
	 (|
	   CPPWanted()
	   (|
	     eq(TS, nil)
             Translate_to_CPP(Id, CL, object)
	   ||
	     Puterror(P)
	     Putmsg("Object arrays cannot be translated.")
	     Putnl()
	   |)
	 ||
	   PVSWanted()
	   (|
	     eq(TS, nil)
             Process_Object(Id, C, CL)
	   ||
	     Puterror(P)
	     Putmsg("Object arrays cannot be translated.")
	     Putnl()
	   |)
	 ||
	   SALWanted()
	   (|
	     eq(TS, nil)
             SAL_Process_Object(Id, C, CL)
	   ||
	     Puterror(P)
	     Putmsg("Object arrays cannot be translated.")
	     Putnl()
	   |)
--	 ||
--	   JavaWanted()
--	   Translate_to_java(Id, CL)
	 ||
	   SMLWanted()
	   (|
	     eq(TS, nil)
             Translate_to_SML(Id, CL)
	   ||
	     Puterror(P)
	     Putmsg("Object arrays cannot be translated.")
	     Putnl()
	   |)
	 ||
           FDRWanted()
	     Puterror(P)
	     Putmsg("Object cannot be translated")
             Putnl()
         ||
	   Generate_confidence_conditions(CL, top)
	 |)

  'rule' Make_top_env(theory(_, C, _, theory_def(P, Id, Axs))):
Putmsg("Checking ")
Print_id(Id)
Putmsg(" ... ")
Putnl()
	 Current <-
	 current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,nil,nil),nil)
	 Extend_paths <- list(nil,nil)
	 Make_basic_env(basic(list(axiom_decl(P, Axs),nil)))
	 Complete_type_env(basic(list(axiom_decl(P, Axs),nil)))
	 Make_value_env(basic(list(axiom_decl(P, Axs),nil)))
	 Check_value_env(basic(list(axiom_decl(P, Axs),nil)))
Putmsg("Finished ")
Print_id(Id)
Putnl()
	 (|
	   PVSWanted()
           Process_Theory(Id, C, basic(list(axiom_decl(P, Axs), nil)))
	 ||
           FDRWanted()
	   Puterror(P)
	   Putmsg("Theory cannot be translated")
           Putnl()
	 ||
	   Generate_confidence_conditions(basic(list(axiom_decl(P, Axs),nil)), top)
         |)
-- debug
-- Current -> C11
-- print(C11)

  'rule' Make_top_env(devt_relation(_, C, _, devt_relation_def(P, Id, Id1, Id2, Ax))):
Putmsg("Checking ")
Print_id(Id)
Putmsg(" ... ")
Putnl()
	 Current <-
	 current_env(basic_env(nil,list(nil,nil),nil,nil,nil,nil,nil,nil,nil,nil,nil),nil)
	 Extend_paths <- list(nil,nil)
	 Make_basic_env(basic(list(axiom_decl(P, list(axiom_def(P,nil,Ax),nil)),nil)))
	 Complete_type_env(basic(list(axiom_decl(P, list(axiom_def(P,nil,Ax),nil)),nil)))
	 Make_value_env(basic(list(axiom_decl(P, list(axiom_def(P,nil,Ax),nil)),nil)))
	 Check_value_env(basic(list(axiom_decl(P, list(axiom_def(P,nil,Ax),nil)),nil)))
Putmsg("Finished ")
Print_id(Id)
Putnl()
	 (|
	   PVSWanted()
	   Process_Theory(Id, C, basic(list(axiom_decl(P, list(axiom_def(P,nil,Ax),nil)),nil)))
	 ||
           FDRWanted()
	   Puterror(P)
	   Putmsg("Devt relation cannot be translated")
           Putnl()
	 ||
	   Generate_confidence_conditions(basic(list(axiom_decl(P, list(axiom_def(P,nil,Ax),nil)),nil)), top)
         |)
-- debug
-- Current -> C11
-- print(C11)

-------------------------------------------------------------------
-- Grammar
------------------------------------------------------------------


'nonterm' lib_module( -> LIB_MODULE, LIB_MODULES)

  'rule' lib_module(-> scheme(P, FS, FS, D), C):
	  @(-> P)
	  context_files(-> FS)
	 "scheme"
	 scheme_def(-> D)
	 eofile
	 context(-> C)

  'rule' lib_module(-> object(P, FS, FS, D), C):
	  @(-> P)
	  context_files(-> FS)
	 "object"
	 object_def(-> D)
	 eofile
	 context(-> C)

  'rule' lib_module(-> theory(P, FS, FS, D), C):
	  @(-> P)
	  context_files(-> FS)
	 "theory"
	 theory_def(-> D)
	 eofile
	 context(-> C)

  'rule' lib_module(-> devt_relation(P, FS, FS, D), C):
	  @(-> P)
	  context_files(-> FS)
	 "devt_relation"
	 devt_relation_def(-> D)
	 eofile
	 context(-> C)

'nonterm' context_files(-> FILE_NAMES)

  'rule' context_files(-> FS):
	 opt_files(-> FS)
	 (|
	   PpWanted()
	 ||
	   Expand_context(FS)
	 |)

'action' Expand_context(FILE_NAMES)

  'rule' Expand_context(list(F, FS)):
-- debug
-- BaseName(F -> Id)
-- id_to_string(Id -> S)
-- Putmsg("Context file ")
-- Putmsg(S)
-- Putnl()
	 InsertContextFile(F)
	 Expand_context(FS)

  'rule' Expand_context(nil):

'nonterm' context (-> LIB_MODULES)

  'rule' context (-> list(Mod, Mods)):
	 nextunit
	 module(-> Mod)
	 eofile
	 context(-> Mods)
	 
  'rule' context(-> nil):

'nonterm' module( -> LIB_MODULE)

  'rule' module(-> scheme(P, FS, FS, D)):
	 context_files(-> FS)
	 "scheme"
	 scheme_def(-> D) @(-> P)

  'rule' module(-> object(P, FS, FS, D)):
	 context_files(-> FS)
	 "object"
	 object_def(-> D) @(-> P)

  'rule' module(-> theory(P, FS, FS, D)):
	  context_files(-> FS)
	 "theory"
	 theory_def(-> D) @(-> P)

  'rule' module(-> devt_relation(P, FS, FS, D)):
	  context_files(-> FS)
	 "devt_relation"
	 devt_relation_def(-> D) @(-> P)

'nonterm' theory_def(-> THEORY_DEF)

   'rule' theory_def(-> theory_def(P, ID, AXS)):
	  id(-> ID)
	  ":"
	  "axiom"
	  opt_theory_axiom_list(-> AXS)
	  "end" @(-> P)

'nonterm' opt_theory_axiom_list(-> AXIOM_DEFS)

  'rule' opt_theory_axiom_list(-> X):
	  theory_axiom_list(-> X)

  'rule' opt_theory_axiom_list(-> nil):

'nonterm' theory_axiom_list(-> AXIOM_DEFS)

  'rule' theory_axiom_list(-> list(H, T)):
	  theory_axiom(-> H)
	  ","
	  theory_axiom_list(-> T)

  'rule' theory_axiom_list(-> list(H, nil)):
	  theory_axiom(-> H)

'nonterm' theory_axiom(-> AXIOM_DEF)

  'rule' theory_axiom(-> axiom_def(P, N, E)):
	  axiom_naming(-> N)
	  theory_expr(-> E) @(-> P)

  'rule' theory_axiom(-> axiom_def(P, nil, E)):
	  theory_expr(-> E) @(-> P)

'nonterm' theory_expr(-> VALUE_EXPR)

  'rule' theory_expr(-> X):
	  class_scope_expr(-> X)

  'rule' theory_expr(-> X):
	  implementation_relation(-> X)

  'rule' theory_expr(-> X):
	  implementation_expr(-> X)

  'rule' theory_expr(-> X):
	  value_expr(-> X)

'nonterm' class_scope_expr(-> VALUE_EXPR)

  'rule' class_scope_expr(-> class_scope_expr(P, C, E)):
	  "in"
	  class_expr(-> C)
	  "|-"
	  theory_expr(-> E) @(-> P) 

  'rule' class_scope_expr(-> X):
	  "("
	  class_scope_expr(-> X)
	  ")"

'nonterm' implementation_relation(-> VALUE_EXPR)

  'rule' implementation_relation(-> implementation_relation(P, C1, C2)):
	  "|-"
	  class_expr(-> C1)
	  "{="
	  class_expr(-> C2) @(-> P)

  'rule' implementation_relation(-> X):
	  "("
	  implementation_relation(-> X)
	  ")"

'nonterm' implementation_expr(-> VALUE_EXPR)

  'rule' implementation_expr(-> implementation_expr(P, O1, O2)):
	  "|-"
	  object_expr(-> O1)
	  "[="
	  object_expr(-> O2) @(-> P)

  'rule' implementation_expr(-> X):
	  "("
	  implementation_expr(-> X)
	  ")"

'nonterm' devt_relation_def(-> DEVT_RELATION_DEF)

  'rule' devt_relation_def(-> devt_relation_def(P, Id, Id1, Id2, E)):
	 id(-> Id)
	 "("
	 id(-> Id1)
	 "for"
	 id(-> Id2)
	 ")"
	 ":"
	 theory_expr(-> E) @(-> P)

--mini -- &bg1 ---------------------------------
--mini -- &up 1d
--mini 'nonterm' specification 
--mini 
--mini   'rule' specification:  
--mini 	  module_decl_string
--mini 
--mini 'nonterm' module_decl_string
--mini 
--mini   'rule' module_decl_string: 
--mini 	  module_decl
--mini 	  module_decl_string
--mini 
--mini   'rule' module_decl_string: 
--mini 	  module_decl
--mini 
--mini -- &up 1
--mini 'nonterm' module_decl(-> MODULE_DECL) 

--mini    'rule' module_decl(-> X):  
--mini  	  scheme_decl(-> X)

--mini   'rule' module_decl:  
--mini 	  object_decl
--mini 
-- &bg1 ---------------------------------
-- &up 1
'nonterm' opt_decl_string(-> DECLS)

 'rule' opt_decl_string(-> X):
	 decl_string(-> X)

 'rule' opt_decl_string(-> nil):

'nonterm' decl_string(-> DECLS)

  'rule'  decl_string(-> list(H,T)):
	   decl(-> H)
	   decl_string(-> T)

  'rule'  decl_string(-> list(X,nil)):
	   decl(-> X)

'nonterm' decl(-> DECL) 

--mini  'rule' decl:  
--mini	  scheme_decl

  'rule' decl(-> object_decl(P,X)):  
	  object_decl(-> X) @(-> P)

  'rule' decl(-> type_decl(P,X)):  
	  type_decl(-> X) @(-> P)

  'rule' decl(-> value_decl(P,X)):  
	  value_decl(-> X) @(-> P)

  'rule' decl( -> variable_decl(P,X)):  
	  variable_decl(-> X) @(-> P)

   'rule' decl(-> channel_decl(P,X)):  
	  channel_decl(-> X) @(-> P)

  'rule' decl(-> axiom_decl(P,X)):  
	  axiom_decl(-> X) @(-> P)

  'rule' decl(-> test_case_decl(P,X)):  
	  test_case_decl(-> X) @(-> P)

  'rule' decl(-> trans_system_decl(P, D)):
	  trans_sys_decl(-> D)  @(-> P)

  'rule' decl(-> property_decl(P, D)):
          property_decl(-> D) @(-> P)
-- &bg2 ---------------------------------
-- &up 2b4
--mini 'nonterm' scheme_decl(-> MODULE_DECL)

--mini   'rule' scheme_decl(-> scheme(P,X)):
--mini 	  "scheme"
--mini 	  scheme_def_list(-> X) @(-> P)

--mini 'nonterm' scheme_def_list(-> SCHEME_DEFS)

--mini   'rule' scheme_def_list(-> list(H,T)):
--mini 	  scheme_def(-> H)
--mini 	  ","
--mini 	  scheme_def_list(-> T)

--mini   'rule' scheme_def_list(-> list(X,nil)):
--mini 	  scheme_def(-> X) 

-- &up 5d1
'nonterm' scheme_def(->  SCHEME_DEF)

  'rule' scheme_def(-> sdef(P, Id, PS, C)):  
--          opt_comment_string
	  id(-> Id)
 	  opt_formal_scheme_parameter(-> PS)
	  "="
	  class_expr(-> C) @(-> P)

-- &up 3b1
'nonterm' opt_formal_scheme_parameter(-> OBJECT_DEFS)

  'rule' opt_formal_scheme_parameter(-> X):
	  formal_scheme_parameter(-> X)

  'rule' opt_formal_scheme_parameter(-> nil):

'nonterm' formal_scheme_parameter(-> OBJECT_DEFS) 

  'rule' formal_scheme_parameter(-> X):
	  "("
	  formal_scheme_argument_list(-> X)
	  ")"

-- &up 1a
'nonterm' formal_scheme_argument_list(-> OBJECT_DEFS)

  'rule' formal_scheme_argument_list(-> list(H, T)):
          formal_scheme_argument(-> H)
 	  ","
 	  formal_scheme_argument_list(-> T)

   'rule' formal_scheme_argument_list(-> list(H, nil)):
          formal_scheme_argument(-> H)

'nonterm' formal_scheme_argument(-> OBJECT_DEF) 

  'rule' formal_scheme_argument(-> X):
 	  object_def(-> X)

-- &bg2 ---------------------------------
-- &up 2b4
'nonterm' object_decl(-> OBJECT_DEFS) 

  'rule' object_decl(-> X):
 	  "object"
	  object_def_list(-> X)

-- &up 5d1
'nonterm' object_def_list(-> OBJECT_DEFS)

  'rule' object_def_list(-> list(H, T)):
 	 object_def(-> H)
  	 ","
 	 object_def_list(-> T)

  'rule' object_def_list(-> list(H, nil)):
 	 object_def(-> H)

'nonterm' object_def(->  OBJECT_DEF) 

  'rule' object_def(->  odef(P, Id, TS, C)):
--	  opt_comment_string
 	  id(-> Id)
	  opt_formal_array_parameter(->TS)
 	  ":"
 	  class_expr(-> C) @(-> P)

-- &up 3b1
'nonterm' opt_formal_array_parameter(-> TYPINGS)

  'rule' opt_formal_array_parameter(-> TS):
	  formal_array_parameter(-> TS) 

  'rule' opt_formal_array_parameter(-> nil):

'nonterm' formal_array_parameter(-> TYPINGS) 

  'rule' formal_array_parameter(-> TS):
	  "["
	  typing_list(-> TS)
	  "]"

-- &bg2 ---------------------------------
-- &up 2b4
'nonterm' type_decl(-> TYPE_DEFS) 

  'rule' type_decl(-> X):
	  "type"
	  type_def_list(-> X)

-- &up 1
'nonterm' type_def_list(-> TYPE_DEFS)

  'rule' type_def_list(-> list(H,T)):
	  type_def(-> H)
	  ","
	  type_def_list(-> T)

  'rule' type_def_list(-> list(X,nil)):
	  type_def(-> X)

'nonterm' type_def(-> TYPE_DEF) 

  'rule' type_def(-> sort(P, X)):  
	  sort_def(-> X) @(-> P)

  'rule' type_def(-> X):  
	  variant_def(-> X)

   'rule' type_def(-> X):  
 	  union_def(-> X)

  'rule' type_def(-> X):  
	  short_record_def(-> X)

  'rule' type_def(-> X):  
	  abbreviation_def(-> X)

-- &bg3 ---------------------------------
-- &up 2d8
'nonterm' sort_def(-> IDENT) 

  'rule' sort_def(-> Id):
--	  opt_comment_string
	  type_id_def(-> Id)

-- &bg3 ---------------------------------
-- &up 4e2
'nonterm' variant_def(-> TYPE_DEF) 

  'rule' variant_def(-> variant(P, Id, CHS)):
--	  opt_comment_string
	  type_id_def(-> Id)
	  "=="
	  variant_choice(-> CHS) @(-> P)

-- &up 1a
'nonterm' variant_choice(-> VARIANTS) 

  'rule' variant_choice(-> list(H, T)):
	  variant(-> H)
	  "|"
	  variant_choice(-> T)

  'rule' variant_choice(-> list(H, nil)):
	  variant(-> H)

'nonterm' variant(-> VARIANT) 

  'rule' variant(-> record(P, C, nil)):
	  constructor(-> C) @(-> P)

  'rule' variant(-> X):  
	  record_variant(-> X)

-- &up 4g1
'nonterm' record_variant(-> VARIANT) 

  'rule' record_variant(-> record(P, C, CS)):
	  constructor(-> C)
	  "("
	  component_kind_list(-> CS)
	  ")" @(-> P)

-- &up 3f1
'nonterm' component_kind_list(-> COMPONENTS) 

  'rule' component_kind_list(-> list(H, T)):
	  component_kind(-> H)
	  ","
	  component_kind_list(-> T)

  'rule' component_kind_list(-> list(H, nil)):
	  component_kind(-> H)

'nonterm' component_kind_string(-> COMPONENTS) 

  'rule' component_kind_string(-> list(H, T)):
	  component_kind(-> H)
	  component_kind_string(-> T)

  'rule' component_kind_string(-> list(H, nil)):
	  component_kind(-> H)

'nonterm' component_kind(-> COMPONENT)

  'rule' component_kind(-> component(P, destructor(P1,id_op(Id)), T, R)):
	  id(-> Id) @(-> P1)
	  ":"
	  type_expr(-> T)
	  opt_reconstructor(-> R) @(-> P)

   'rule' component_kind(-> component(P, destructor(P1,op_op(Op)), T, R)):
	  op(-> Op) @(-> P1)
	  ":"
 	  type_expr(-> T)
 	  opt_reconstructor(-> R) @(-> P)

  'rule' component_kind(-> component(P, nil, T, R)):
	  type_expr(-> T)
	  opt_reconstructor(-> R) @(-> P)

-- &up 1a
'nonterm' constructor(-> CONSTRUCTOR) 

  'rule' constructor(-> constructor(P,X)):
	  id_or_op(-> X) @(-> P)

  'rule' constructor(-> wildcard):
	  "_"

 -- &up 2a2
'nonterm' opt_reconstructor(-> RECONSTRUCTOR) 

  'rule' opt_reconstructor(-> X)
	  reconstructor(-> X)

  'rule' opt_reconstructor(-> nil):

'nonterm' reconstructor(-> RECONSTRUCTOR) 

  'rule' reconstructor(-> reconstructor(P, X)):
	  "<->"
	  id_or_op(-> X) @(-> P) 

-- &bg3 ---------------------------------
-- &up 4e2
'nonterm' union_def(-> TYPE_DEF) 

  'rule' union_def(-> union(P,Id,NS)):
--	  opt_comment_string
	  type_id_def(-> Id)
	  "="
	  name_or_wildcard_choice2(-> NS) @(-> P)

-- &up 1a
'nonterm' name_or_wildcard_choice2(-> CHOICES)

  'rule' name_or_wildcard_choice2(-> list(N, NS)):
	  name_or_wildcard(-> N)
	  "|"
	  name_or_wildcard_choice(-> NS)

'nonterm' name_or_wildcard_choice(-> CHOICES)

  'rule' name_or_wildcard_choice(-> list(N, NS)):
	  name_or_wildcard(-> N)
	  "|"
	  name_or_wildcard_choice(-> NS)

  'rule' name_or_wildcard_choice(-> list(N, nil)):
	  name_or_wildcard(-> N)

'nonterm' name_or_wildcard(-> CHOICE) 

  'rule' name_or_wildcard(-> choice(P, N)):
	  name(-> N) @(-> P)

  'rule' name_or_wildcard(-> nil):  
	  "_"

-- &bg3 ---------------------------------
-- &up 4e2
'nonterm' short_record_def(-> TYPE_DEF) 

  'rule' short_record_def(-> record(P, Id, CS)):
--	  opt_comment_string
	  type_id_def(-> Id)
	  "::"
	  component_kind_string(-> CS) @(-> P)

-- &bg3 ---------------------------------
-- &up 4e2
'nonterm' abbreviation_def(-> TYPE_DEF) 

  'rule' abbreviation_def(-> abbrev(P,Id,T)):
--	  opt_comment_string
	  type_id_def(-> Id)
	  "="
	  type_expr(-> T) @(-> P)

-- &bg2 ---------------------------------
-- &up 2b4a
'nonterm' value_decl(-> VALUE_DEFS) 

  'rule' value_decl(-> X):
	  "value"
	  value_def_list(-> X)

-- &up 1
'nonterm' value_def_list(-> VALUE_DEFS)

  'rule' value_def_list(-> list(H,T)):
	  value_def(-> H)
	  ","
	  value_def_list(-> T)

  'rule' value_def_list(-> list(X,nil)):
	  value_def(-> X)

'nonterm' value_def(-> VALUE_DEF) 

  'rule' value_def(-> X):
	  commented_typing(-> X)

  'rule' value_def(-> X):  
	  explicit_value_def(-> X)

  'rule' value_def(-> X):  
	  implicit_value_def(-> X)

  'rule' value_def(-> X):  
	  explicit_function_def(-> X)

  'rule' value_def(-> X):  
	  implicit_function_def(-> X)

-- &bg3
-- &up 4e3
'nonterm' explicit_value_def(-> VALUE_DEF) 

  'rule' explicit_value_def(-> exp_val(P,T,E)):
--	  opt_comment_string
	  single_typing(-> T)
	  "=" @(-> P)
	  value_expr(-> E)

-- &bg3
-- &up 3f4
'nonterm' implicit_value_def(-> VALUE_DEF)

  'rule' implicit_value_def(-> imp_val(P,T,R)):
--	  opt_comment_string
	  single_typing(-> T) @(-> P)
	  restriction(-> R)

-- &bg3
-- &up 6a1
'nonterm' explicit_function_def(-> VALUE_DEF) 

  'rule' explicit_function_def(-> exp_fun(P,T,A,E,PO,PR,region(PB,PE))):
--	  opt_comment_string
	  single_typing(-> T)
	  formal_function_application(-> A) @(-> P)
	  "is"
	  value_expr_pr12(-> E) @(-> PB)
	  opt_post_condition(-> PO)
	  opt_pre_condition(-> PR)
	  dummy_term @(-> PE) 

-- &up 1a
'nonterm' formal_function_application(-> FORMAL_FUNCTION_APPLICATION) 

  'rule' formal_function_application(-> X):
	  id_application(-> X)

  'rule' formal_function_application(-> X):
 	  prefix_application(-> X)

  'rule' formal_function_application(-> X):
	  infix_application(-> X)

-- &up 2b3
'nonterm' id_application(-> FORMAL_FUNCTION_APPLICATION) 

  'rule' id_application(-> form_appl(P,id_op(Id),PS)):
	  id(-> Id)
	  formal_function_parameter_string(-> PS) @(-> P)

-- &up 3b2
'nonterm' formal_function_parameter_string(-> FORMAL_FUNCTION_PARAMETERS)

  'rule' formal_function_parameter_string(-> list(H,T)):
	  formal_function_parameter(-> H)
	  formal_function_parameter_string(-> T)

  'rule' formal_function_parameter_string(-> list(X,nil)):
	  formal_function_parameter(-> X)

'nonterm' formal_function_parameter(-> FORMAL_FUNCTION_PARAMETER) 

  'rule' formal_function_parameter(-> form_parm(P,X)):
	  "("
	  opt_binding_list(-> X) @(-> P)
	  ")"

-- &up 2a2
'nonterm' prefix_application(-> FORMAL_FUNCTION_APPLICATION) 

  'rule' prefix_application(-> form_appl(P1, op_op(Op), 
                   list(form_parm(P,list(single(P,id_op(Id)),nil)),nil))): 	  
 	  prefix_op(-> Op) @(-> P1)
 	  id(->Id) @(-> P)
	    

   'rule' prefix_application(-> form_appl(P1, op_op(Op), list(form_parm(P,list(single(P,id_op(Id)),nil)),nil))):
 	  infix_prefix_op(-> Op) @(-> P1)
 	  id(->Id) @(-> P)

-- &up 3a2
'nonterm' infix_application(-> FORMAL_FUNCTION_APPLICATION) 

   'rule' infix_application(-> form_appl(P2, op_op(Op), list(form_parm(P1,list(single(P1, id_op(Id1)),list(single(P3, id_op(Id2)),nil))),nil))):
	  id(-> Id1) @(-> P1)
 	  infix_op(-> Op) @(-> P2)
 	  id(-> Id2) @(-> P3)

   'rule' infix_application(-> form_appl(P2, op_op(Op), list(form_parm(P1,list(single(P1, id_op(Id1)),list(single(P3, id_op(Id2)),nil))),nil))):
 	  id(-> Id1) @(-> P1)
	  infix_prefix_op(-> Op) @(-> P2)
	  id(-> Id2) @(-> P3)

-- &bg3
-- &up 5e1
'nonterm' implicit_function_def(-> VALUE_DEF) 

  'rule' implicit_function_def(-> imp_fun(P,T,A,E,PR)):
--	  opt_comment_string
 	  single_typing(-> T)
	  formal_function_application(-> A) @(-> P)
	  post_condition(-> E)
	  opt_pre_condition(-> PR)

-- &bg2 ---------------------------------
-- &up 2b4
'nonterm' variable_decl(-> VARIABLE_DEFS) 

  'rule' variable_decl(-> X):
	  "variable"
	  variable_def_list(-> X)

-- &up 1
'nonterm' variable_def_list(-> VARIABLE_DEFS)

  'rule' variable_def_list(-> list(H,T)):
	  variable_def(-> H)
	  ","
	  variable_def_list(-> T)

  'rule' variable_def_list(-> list (H,nil)):
	  variable_def(-> H)

'nonterm' variable_def(-> VARIABLE_DEF) 

  'rule' variable_def(-> X):
	  single_variable_def(-> X)

  'rule' variable_def(-> X):
	  multiple_variable_def(-> X)

-- &up 5c2
'nonterm' single_variable_def(-> VARIABLE_DEF) 

  'rule' single_variable_def(-> single(P, Id, T, I)):
--	  opt_comment_string
	  id(-> Id)
	  ":"
	  type_expr(-> T)
	  opt_initialisation(-> I) @(-> P)

-- &up 2b5
'nonterm' opt_initialisation(-> INITIALISATION)

  'rule' opt_initialisation(-> X):
	  initialisation(-> X)

  'rule' opt_initialisation(-> nil):

'nonterm' initialisation(-> INITIALISATION) 

  'rule' initialisation(-> initial(V)):
	  ":="
	  value_expr(-> V)

-- &up 4e3
'nonterm' multiple_variable_def(-> VARIABLE_DEF) 

  'rule' multiple_variable_def(-> multiple(P, Ids, T)):
--	  opt_comment_string
	  id_list2(-> Ids)
	  ":"
	  type_expr(-> T) @(-> P)


-- &bg2 ---------------------------------
-- &up 2b4
'nonterm' channel_decl(-> CHANNEL_DEFS) 

  'rule' channel_decl(-> X):
	  "channel"
	  channel_def_list(-> X)

-- &up 1
'nonterm' channel_def_list(-> CHANNEL_DEFS)

  'rule' channel_def_list(-> list(H,T)):
	  channel_def(-> H)
	  ","
	  channel_def_list(-> T) 

  'rule' channel_def_list(-> list(H,nil)):
	  channel_def(-> H)

'nonterm' channel_def(-> CHANNEL_DEF) 

  'rule' channel_def(-> X):
	  single_channel_def(-> X)

  'rule' channel_def(-> X):
	  multiple_channel_def(-> X)

-- &up 4e4
'nonterm' single_channel_def(-> CHANNEL_DEF) 

  'rule' single_channel_def(-> single(P, Id, T)):
--	  opt_comment_string
	  id(-> Id)
	  ":"
	  type_expr(-> T) @(-> P)

-- &up 4e3
'nonterm' multiple_channel_def(-> CHANNEL_DEF) 

  'rule' multiple_channel_def(-> multiple(P, Ids, T)):
--	  opt_comment_string
	  id_list2(-> Ids)
	  ":"
	  type_expr(-> T) @(-> P)

-- &bg2 ---------------------------------
-- &up 2b4
'nonterm' axiom_decl(-> AXIOM_DEFS) 

  'rule' axiom_decl(-> X):
	  "axiom"
	  axiom_def_list(-> X)

-- &up 3f3
'nonterm' axiom_def_list(-> AXIOM_DEFS)

  'rule'  axiom_def_list(-> list(H,T)):
	   axiom_def(-> H)
	   ","
	   axiom_def_list(-> T)

  'rule'  axiom_def_list(-> list(X,nil)):
	   axiom_def(-> X)

'nonterm' axiom_def(-> AXIOM_DEF) 

  'rule' axiom_def(-> axiom_def(P,N,E)):
--	  opt_comment_string
	  axiom_naming(-> N)
	  value_expr(-> E) @(-> P)

  'rule' axiom_def(-> axiom_def(P,nil,E)):
--	  opt_comment_string
	  value_expr(-> E) @(-> P)

'nonterm' axiom_naming(-> OPT_IDENT) 

  'rule' axiom_naming(-> ident(Id)):
	  "["
	  id(-> Id)
	  "]"

-- &bg2 ---------------------------------
-- &up 2b4
'nonterm' test_case_decl(-> TEST_CASE_DEFS) 

  'rule' test_case_decl(-> X):
	  "test_case"
	  test_case_def_list(-> X)

-- &up 3f3
'nonterm' test_case_def_list(-> TEST_CASE_DEFS)

  'rule'  test_case_def_list(-> list(H,T)):
	   test_case_def(-> H)
	   ","
	   test_case_def_list(-> T)

  'rule'  test_case_def_list(-> list(X,nil)):
	   test_case_def(-> X)

'nonterm' test_case_def(-> TEST_CASE_DEF) 

  'rule' test_case_def(-> test_case_def(P,N,E)):
--	  opt_comment_string
	  test_case_naming(-> N)
	  value_expr(-> E) @(-> P)

  'rule' test_case_def(-> test_case_def(P,nil,E)):
--	  opt_comment_string
	  value_expr(-> E) @(-> P)

'nonterm' test_case_naming(-> OPT_IDENT) 

  'rule' test_case_naming(-> ident(Id)):
	  "["
	  id(-> Id)
	  "]"

---------------------------------------------------------
-- transition systems (SAL extension)
---------------------------------------------------------
-- &bg2 ---------------------------------
-- &up 2b4
'nonterm' trans_sys_decl(-> TRANSITION_SYS_DEFS) 

  'rule' trans_sys_decl(-> X):
	  "transition_system"
	  trans_sys_def_list(-> X)

-- &up 3f3
'nonterm' trans_sys_def_list(-> TRANSITION_SYS_DEFS)

  'rule'  trans_sys_def_list(-> list(H,T)):
	   trans_sys_def(-> H)
	   ","
	   trans_sys_def_list(-> T)

  'rule'  trans_sys_def_list(-> list(X,nil)):
	   trans_sys_def(-> X)

'nonterm' trans_sys_def(-> TRANSITION_SYS_DEF) 

  'rule' trans_sys_def(-> trans_sys_def(P,N,D)):
          "["
	  id(-> N)
	  "]"
	  sys_description(-> D) @(-> P)

'nonterm' sys_description(-> SYSTEM_DESCRIPTION)

  'rule' sys_description(-> desc(Input,
				 Local,
				 --Priorities,
				 Transitions)):
	   trans_sys_inputs(-> Input)
	   trans_sys_locals(-> Local)
	   trans_sys_trans(-> Transitions)

  'rule' sys_description(-> no_input(Local,
				 --Priorities,
				 Transitions)):
         trans_sys_locals(-> Local)
	 trans_sys_trans(-> Transitions)
	 
'nonterm' trans_sys_inputs(-> DECL)

  'rule' trans_sys_inputs(-> variable_decl(P, DS))
	    "in" @(-> P)
	    variable_def_list(-> DS)

'nonterm' trans_sys_locals(-> DECL)

  'rule' trans_sys_locals(-> variable_decl(P, DS))
	    "local" @(-> P)
	    variable_def_list(-> DS)

'nonterm' trans_sys_trans(-> TRANSITION_OPERATOR)

  'rule' trans_sys_trans(-> CMDS):
	   "in"
	   transitionsoperator(-> CMDS, _)
	   "end"

'nonterm' transitionsoperator(-> TRANSITION_OPERATOR, EXTRA_GUARD)
  'rule' transitionsoperator(-> TRANS, EXTRA):
           transitionsoperator_equal(-> TRANS, EXTRA)

  'rule' transitionsoperator(-> TRANS, EXTRA):
           transitionsoperator_greater(-> TRANS, EXTRA)

  'rule' transitionsoperator(-> TRANS, EXTRA):
           transitionsoperator_bracketed(-> TRANS, EXTRA)

  'rule' transitionsoperator(-> guarded_command(H, EXTRA), EXTRA):
           guarded_cmd(-> H, EXTRA)

'nonterm' transitionsoperator_greater(-> TRANSITION_OPERATOR, EXTRA_GUARD)
  'rule' transitionsoperator_greater(-> greater_priority(LEFT, RIGHT, EXTRA), EXTRA):
           @(-> Pos)
           transitionsoperator_greater(-> LEFT, EXTRALEFT)
           "[>]"
           transitionsoperator_greater(-> RIGHT, EXTRARIGHT)
           Concat_Extra_Guards(EXTRALEFT, EXTRARIGHT -> EXTRA)

  'rule' transitionsoperator_greater(-> TRANS, EXTRA):
           transitionsoperator_bracketed(-> TRANS, EXTRA)

  'rule' transitionsoperator_greater(-> guarded_command(CM, EXTRA), EXTRA)
           guarded_cmd(-> CM,EXTRA)

'nonterm' transitionsoperator_equal(-> TRANSITION_OPERATOR, EXTRA_GUARD)
  'rule' transitionsoperator_equal(-> equal_priority(LEFT, RIGHT, EXTRA), EXTRA):
           @(-> Pos)
           transitionsoperator_equal(-> LEFT, EXTRALEFT)
           "[=]"
           transitionsoperator_equal(-> RIGHT, EXTRARIGHT)
           Concat_Extra_Guards(EXTRALEFT, EXTRARIGHT -> EXTRA)

  'rule' transitionsoperator_equal(-> TRANS, EXTRA):
           transitionsoperator_bracketed(-> TRANS, EXTRA)

  'rule' transitionsoperator_equal(-> guarded_command(H, EXTRA), EXTRA):
           guarded_cmd(-> H, EXTRA)

'nonterm' transitionsoperator_bracketed(-> TRANSITION_OPERATOR, EXTRA_GUARD)
  'rule' transitionsoperator_bracketed(-> bracketed(OP, EXTRA), EXTRA):
           "("
           transitionsoperator(-> OP, EXTRA)
           ")"


/*'action' Concat_Extra_Guards(EXTRA_GUARD, EXTRA_GUARD -> EXTRA_GUARD)

  'rule' Concat_Extra_Guards(nil, nil -> nil)
  'rule' Concat_Extra_Guards(A, nil -> A)
  'rule' Concat_Extra_Guards(nil, B -> B)

  'rule' Concat_Extra_Guards(guard(Val1,P1), guard(Val2,P2) -> guard(ax_infix(P1,Val1,or,Val2,P2),P1))*/

'nonterm' guarded_cmd(-> GUARDED_COMMAND, EXTRA_GUARD)
	    
  'rule' guarded_cmd(-> else_cmd(Ident,Cmds), nil):
	   transition_name(-> Ident)
	   "else"
	   "==>"
	   sal_update_list(-> Cmds)  

  'rule' guarded_cmd(-> else_cmd(nil,Cmds), nil):
	   "else"
	   "==>"  
	   sal_update_list(-> Cmds)  

  'rule' guarded_cmd(-> else_cmd(Ident,nil), nil):
	   transition_name(-> Ident)
	   "else"
	   "==>"  

  'rule' guarded_cmd(-> else_cmd(nil,nil), nil):
	   "else"
	   "==>"  

  'rule' guarded_cmd(-> guarded_cmd(Ident,Guard,Cmds), guard(Guard,Pos)):
	   @(-> Pos)
	   transition_name(-> Ident)
	   value_expr(-> Guard)
	   "==>"
	   sal_update_list(-> Cmds)

  'rule' guarded_cmd(-> guarded_cmd(nil,Guard,Cmds), guard(Guard,Pos)):
	   @(-> Pos)
	   value_expr(-> Guard)
	   "==>"
	   sal_update_list(-> Cmds)

  'rule' guarded_cmd(-> comprehended_cmd(TS, Pos, Cmd), guard(quantified(P,exists,TS,restriction(P,Val)),P))
	   "([=]"
	   typing_list(-> TS)
           ":-"
	   @(-> Pos)
	   guarded_cmd(-> Cmd, guard(Val,P))
	   ")"

'nonterm' transition_name(-> OPT_IDENT) 

  'rule' transition_name(-> ident(Id)):
	  "["
	  id(-> Id)
	  "]"

'nonterm' sal_update_list(-> COMMANDS)

  'rule'  sal_update_list(-> list(Cmd, Cmds))
	  sal_update_expr(-> Cmd)
	  ","
	  sal_update_list(-> Cmds)

  'rule' sal_update_list(-> list(Cmd, nil))
	 sal_update_expr(-> Cmd)

'nonterm' sal_update_expr(-> COMMAND)

  'rule' sal_update_expr(-> cmd(P, Name, ValueExpr))
	 name(-> Name) @(-> P)
	 "="
	 value_expr(-> ValueExpr)

  'rule' sal_update_expr(-> array_cmd(P,Name, IndexExpr, ValueExpr))
         name(-> Name) @(-> P)
         array_accesses(-> IndexExpr)
         /*"["
         value_expr(-> IndexExpr)
         "]"*/
         "="
         value_expr(-> ValueExpr)

  'rule' sal_update_expr(-> cmd(P, Name, ResValueExpr))
         name(-> Name)
         @(-> P)
         "("
         value_expr(-> I)
         ")"
         "="
         value_expr(-> ValueExpr)
         Convert_name(Name -> Name2)
         map_expr_from_val_right(P, I, ValueExpr -> ValueExprRight)
         map_expr_from_val_left(P, Name2 -> ValueExprLeft)
         map_expr_from_val_union(P, ValueExprLeft, ValueExprRight -> ResValueExpr)

  'rule' sal_update_expr(-> cmd(P1, NA, array_expr(P2,T,V)))
         @(-> P1)
         "all"
         --name(-> name(P3,Id1))
         --id_or_op(-> Id1)
         --":"
         --type_expr(-> T)
         typing(-> T)
         ":-"
         name(-> NA)
         "["
         name(-> name(P4,Id2))
         --id_or_op(-> Id2)
         "]"
         "="
         @(-> P2)
         value_expr(-> V)
         /*(|
         eq(Id1,Id2)
         ||
         ne(Id1,Id2)
         Puterror(P4)
         Print_name(name(P3,Id1))
         Putmsg(" and ")
         Print_name(name(P4,Id2))
         Putmsg(" are different. The same identifier should be used.\n")
         |)*/
         
'action' Convert_name(NAME -> NAME)
  'rule' Convert_name(name(P,Id) -> name(P,Id2))
         Convert_id(Id -> Id2)
         
'action' Convert_id(ID_OR_OP -> ID_OR_OP)
  'rule' Convert_id(id_op(I) -> id_op(I2))
         Convert_Ident(I -> I2)
         
'action' Convert_Ident(IDENT -> IDENT)
  'rule' Convert_Ident(I -> I2)
         id_to_string(I -> S)
         Remove_Prime(S -> S2)
         string_to_id(S2 -> I2)

'action' map_expr_from_val_union(POS, VALUE_EXPR, VALUE_EXPR -> VALUE_EXPR)
  'rule' map_expr_from_val_union(P, LEFT, RIGHT -> val_infix(P,LEFT,override,RIGHT))

'action' map_expr_from_val_right(POS, VALUE_EXPR, VALUE_EXPR -> VALUE_EXPR)
  'rule' map_expr_from_val_right(P, ID, Val -> enum_map(P,list(pair(ID,Val),nil)))

'action' map_expr_from_val_left(POS, NAME -> VALUE_EXPR)
  'rule' map_expr_from_val_left(P, Name -> named_val(P,Name))
         
--------------------------------------------------------
-- LTL assertions
--------------------------------------------------------
'nonterm' property_decl(-> PROPERTY_DECLS) 

  'rule' property_decl(-> X):
	  "ltl_assertion"
	  prop_def_list(-> X)


'nonterm' prop_def_list(-> PROPERTY_DECLS)

  'rule'  prop_def_list(-> list(H,T)):
	   prop_def(-> H)
	   ","
	   prop_def_list(-> T)
  
  'rule' prop_def_list(-> list(X,nil)):
	   prop_def(-> X)

'nonterm' prop_def(-> PROPERTY_DECL)

  'rule' prop_def(-> property_def(P, Ident, TS, Prop)):
	 "["
	  id(-> Ident)
	  "]" 
	  id(-> TS)
	  "|-" @(-> P)
	  value_expr(-> Prop)

-- &bg1 ---------------------------------
-- &up 1
'nonterm' class_expr(-> CLASS) 

  'rule' class_expr(-> basic(X)):
	  basic_class_expr(-> X)

  'rule' class_expr(-> X):  
 	  extending_class_expr(-> X)

   'rule' class_expr(-> X):  
	  hiding_class_expr(-> X)

   'rule' class_expr(-> X):  
 	  renaming_class_expr(-> X)

   'rule' class_expr(-> X):  
	  with_class_expr(-> X)

  'rule' class_expr(-> X):  
 	 scheme_instantiation(-> X)

-- &bg2 ---------------------------------
-- &up 3b4
'nonterm' basic_class_expr(-> DECLS) 

  'rule' basic_class_expr(-> X):
	  "class"
	  opt_decl_string(-> X)
	  "end"

-- &bg2 ---------------------------------
-- &up 4c1
'nonterm' extending_class_expr(-> CLASS) 

  'rule' extending_class_expr(-> extend(C1,C2)):
	  "extend"
	  class_expr(-> C1)
	  "with"
	  class_expr(-> C2)

-- &bg2 ---------------------------------
-- &up 4c1
'nonterm' hiding_class_expr(-> CLASS) 

  'rule' hiding_class_expr(-> hide(H, C)):
	  "hide"
	  defined_item_list(-> H)
	  "in"
	  class_expr(-> C)

-- &bg2 ---------------------------------
-- &up 4c1
'nonterm' renaming_class_expr(-> CLASS) 

  'rule' renaming_class_expr(-> rename(R,C)):
	  "use"
	  rename_pair_list(-> R)
	  "in"
	  class_expr(-> C)

-- &bg2 ---------------------------------
-- &up 4c4
'nonterm' with_class_expr(-> CLASS) 

  'rule' with_class_expr(-> with(P, OS, C)):
	  "with"
	  object_expr_list(-> OS) @(-> P)
	  "in"
	  class_expr(-> C)

-- &bg2 ---------------------------------
-- &up 2d1
'nonterm' scheme_instantiation(-> CLASS) 

  'rule' scheme_instantiation(-> instantiation(N, PARMS)):
	 name(-> N)
 	 opt_actual_scheme_parameter(-> PARMS)

-- &up 3b1
'nonterm' opt_actual_scheme_parameter(-> OBJECT_EXPRS)

  'rule' opt_actual_scheme_parameter(-> X):
 	 actual_scheme_parameter(-> X) 

  'rule' opt_actual_scheme_parameter(-> nil):

'nonterm' actual_scheme_parameter(-> OBJECT_EXPRS) 

  'rule' actual_scheme_parameter(-> X):
	 "("
	 object_expr_list(-> X)
	 ")"	 

-- &bg2 ---------------------------------
-- &up 3c1
'nonterm' rename_pair_list(-> RENAMES)

  'rule' rename_pair_list(-> list(H, T)):
	  rename_pair(-> H)
	  ","
	  rename_pair_list(-> T)

  'rule' rename_pair_list(-> list(H, nil)):
	  rename_pair(-> H)

'nonterm' rename_pair(-> RENAME) 

  'rule' rename_pair(-> rename(It1, It2)):
	  defined_item(-> It1)
	  "for"
	  defined_item(-> It2)

-- &bg2 ---------------------------------
-- &up 1a
'nonterm' defined_item_list(-> DEFINEDS)

  'rule' defined_item_list(-> list(H, T)):
	  defined_item(-> H)
	  ","
	  defined_item_list(-> T) 

  'rule' defined_item_list(-> list(H, nil)):
	  defined_item(-> H)

'nonterm' defined_item(-> DEFINED) 

  'rule' defined_item(-> def_name(P,X)):
	  id_or_op(-> X) @(-> P)

  'rule' defined_item(-> X):
	  disambiguated_item(-> X)

-- &up 3c1
'nonterm' disambiguated_item(-> DEFINED) 

  'rule' disambiguated_item(-> disamb(P, N, T)):
	  id_or_op(-> N)
	  ":"
	  type_expr(-> T) @(-> P)

-- &bg1 ---------------------------------
-- &up 1a
'nonterm' object_expr_list(-> OBJECT_EXPRS)

  'rule' object_expr_list(-> list(H,T)):
	  object_expr(-> H)
	  ","
	  object_expr_list(-> T) 

  'rule' object_expr_list(-> list(H,nil)):
	  object_expr(-> H)

'nonterm' object_expr(-> OBJECT_EXPR) 

  'rule' object_expr(-> obj_name(N)):
	 name(-> N)

  'rule' object_expr(-> X):  
	  element_object_expr(-> X)

  'rule' object_expr(-> X):  
	  array_object_expr(-> X)

  'rule' object_expr(-> X):  
	  fitting_object_expr(-> X)

-- &bg2 ---------------------------------
-- &up 2d2
'nonterm' element_object_expr(-> OBJECT_EXPR)

  'rule' element_object_expr(-> obj_appl(O, A)):
 	  object_expr(-> O)
	  actual_array_parameter(-> A)

-- &up 3b1
'nonterm' actual_array_parameter(-> VALUE_EXPRS) 

  'rule' actual_array_parameter(-> A):
	  "["
	  value_expr_list(-> A)
	  "]"

-- &bg2 ---------------------------------
-- &up 5a1
'nonterm' array_object_expr(-> OBJECT_EXPR) 

  'rule' array_object_expr(-> obj_array(TS, O)):
	  "[|"
	   typing_list(-> TS)
	   ":-"
	   object_expr(-> O)
	   "|]"

-- &bg2 ---------------------------------
-- &up 4g2
'nonterm' fitting_object_expr(-> OBJECT_EXPR)

  'rule' fitting_object_expr(-> obj_fit(O, F)):
	  object_expr(-> O)
 	  "{"
	  rename_pair_list(-> F)
 	  "}"

-- &bg1 ---------------------------------
-- &up 1
'nonterm' type_expr(-> TYPE_EXPR) 

  'rule' type_expr(-> X):
	  type_expr_pr3(-> X)

'nonterm' type_expr_pr3(-> TYPE_EXPR) 

  'rule' type_expr_pr3(-> X):
	  type_expr_pr2(-> X)

  'rule' type_expr_pr3(-> X):
	  map_type_expr(-> X)

  'rule' type_expr_pr3(-> X):
	  function_type_expr(-> X)

  'rule' type_expr_pr3(-> X):
          array_type_expr(-> X)

'nonterm' type_expr_pr2(-> TYPE_EXPR) 

  'rule' type_expr_pr2(-> X):
	  type_expr_pr1(-> X)

  'rule' type_expr_pr2(-> X):
	  product_type_expr(-> X)

'nonterm' type_expr_pr1(-> TYPE_EXPR) 

  'rule' type_expr_pr1(-> X):
	  type_expr_pr0(-> X)

  'rule' type_expr_pr1(-> X):
	  set_type_expr(-> X)

  'rule' type_expr_pr1(-> X):
	  list_type_expr(-> X)

'nonterm' type_expr_pr0(-> TYPE_EXPR) 

  'rule' type_expr_pr0(-> X):
	  type_literal(-> X)

  'rule' type_expr_pr0(-> X):
	  name(-> Y)
	  (|
	    IsTimed()
	    where(Y -> name(P, id_op(Id)))
	    Time_id -> Time_id
	    eq(Id, Time_id)
	    where(time -> X)
	  ||
	    where(named_type(Y) -> X)
	  |)

  'rule' type_expr_pr0(-> X):
	  subtype_expr(-> X)

  'rule' type_expr_pr0(-> X):
	  bracketed_type_expr(-> X)

-- &bg2 ---------------------------------
-- &up 1a
'nonterm' type_literal(-> TYPE_EXPR) 

  'rule' type_literal(-> unit):
	  "Unit"

  'rule' type_literal(-> bool):
	  "Bool"

  'rule' type_literal(-> int):
	  "Int"

  'rule' type_literal(-> nat):
	  "Nat"

  'rule' type_literal(-> real):
	  "Real"

  'rule' type_literal(-> text):
	  "Text"

  'rule' type_literal(-> char):
	  "Char"


-- &bg2 ---------------------------------
-- &up 1a
'nonterm' product_type_expr(-> TYPE_EXPR) 

  'rule' product_type_expr(-> product(X)):
	  type_expr_pr1_product2(-> X)

'nonterm' type_expr_pr1_product2(-> PRODUCT_TYPE)

  'rule' type_expr_pr1_product2(-> list(H,T)):
	  type_expr_pr1(-> H)
	  "><"
	  type_expr_pr1_product(-> T)

'nonterm' type_expr_pr1_product(-> PRODUCT_TYPE)

  'rule' type_expr_pr1_product(-> list(H,T)):
	  type_expr_pr1(-> H)
	  "><"
	  type_expr_pr1_product(-> T)

  'rule' type_expr_pr1_product(-> list(H,nil)):
	  type_expr_pr1(-> H)

-- &bg2 ---------------------------------
-- &up 1a
'nonterm' set_type_expr(-> TYPE_EXPR) 

  'rule' set_type_expr(-> X):
	  finite_set_type_expr(-> X)

  'rule' set_type_expr(-> X):
	  infinite_set_type_expr(-> X)

-- &up 2c2
'nonterm' finite_set_type_expr(-> TYPE_EXPR)

  'rule' finite_set_type_expr(-> fin_set(X)):
	  type_expr_pr0(-> X)
	  "-set" 

-- &up 2c2
'nonterm' infinite_set_type_expr(-> TYPE_EXPR) 

  'rule' infinite_set_type_expr(-> infin_set(X)):
	  type_expr_pr0(-> X)
	  "-infset"

-- &bg2 ---------------------------------
-- &up 1a
'nonterm' list_type_expr(-> TYPE_EXPR) 

  'rule' list_type_expr(-> X):
	  finite_list_type_expr(-> X)

  'rule' list_type_expr(-> X):
	  infinite_list_type_expr(-> X)

-- &up 2c2
'nonterm' finite_list_type_expr(-> TYPE_EXPR) 

  'rule' finite_list_type_expr(-> fin_list(X)):
	  type_expr_pr0(-> X)
	  "-list" 

-- &up 2c2
'nonterm' infinite_list_type_expr(-> TYPE_EXPR) 

  'rule' infinite_list_type_expr(-> infin_list(X)):
	  type_expr_pr0(-> X)
	  "-inflist"

-- &bg2 ---------------------------------
-- &up 1a
'nonterm' map_type_expr(-> TYPE_EXPR) 

  'rule' map_type_expr(-> X):
	  finite_map_type_expr(-> X)

  'rule' map_type_expr(-> X):
	  infinite_map_type_expr(-> X)

-- &up 3e4
'nonterm' finite_map_type_expr(-> TYPE_EXPR) 

  'rule' finite_map_type_expr(-> fin_map(D,R)):
	  type_expr_pr2(-> D)
	  "-m->"
	  type_expr_pr3(-> R)

-- &up 3e4
'nonterm' infinite_map_type_expr(-> TYPE_EXPR) 

  'rule' infinite_map_type_expr(-> infin_map(D,R)):
	  type_expr_pr2(-> D)
	  "-~m->"
	  type_expr_pr3(-> R)

-- &bg2 ---------------------------------
-- &up 3e2
'nonterm' function_type_expr(-> TYPE_EXPR) 

  'rule' function_type_expr(-> function(X,A,R)):
	  type_expr_pr2(-> X)
	  function_arrow(-> A)
	  result_desc(-> R) 

-- &up 1a
'nonterm' function_arrow(-> FUNCTION_ARROW) 

  'rule' function_arrow(-> partial):
	  "-~->"

  'rule' function_arrow(-> total):
	  "->"

-- &up 2d6
'nonterm' result_desc(-> RESULT_DESC) 

  'rule' result_desc(-> result(AS,T)):
	  opt_access_desc_string(-> AS)
	  type_expr_pr3(-> T)

-- &bg2 ---------------------------------
-- &up 4b1
'nonterm' subtype_expr(-> TYPE_EXPR) 

  'rule' subtype_expr(-> subtype(T,R)):
	  "{|"
	  single_typing(-> T)
	  restriction(-> R)
	  "|}"

-----------------------------------------
'nonterm' array_type_expr(-> TYPE_EXPR)
  'rule' array_type_expr(-> array(T1,T2))
         "array"
         type_expr(-> T1)
         "of"
         type_expr(-> T2)

-- &bg2 ---------------------------------
-- &up 3b1
'nonterm' bracketed_type_expr(-> TYPE_EXPR)

  'rule' bracketed_type_expr(-> bracket(T)):
	  "("
	  type_expr(-> T)
	  ")"

-- &bg2 ---------------------------------
-- &up 2b1
'nonterm' opt_access_desc_string(-> ACCESS_DESCS)

  'rule' opt_access_desc_string(-> X):
	  access_desc_string(-> X)

  'rule' opt_access_desc_string(-> nil):

'nonterm' access_desc_string(-> ACCESS_DESCS)

  'rule' access_desc_string(-> list(H,T)):
	  access_desc(-> H)
	  access_desc_string(-> T)

  'rule' access_desc_string(-> list(H,nil)):
	  access_desc(-> H)

'nonterm' access_desc(-> ACCESS_DESC) 

  'rule' access_desc(-> access(M, A)):
	  access_mode(-> M)
	  access_list(-> A)

-- &up 1a
'nonterm' access_mode(-> ACCESS_MODE) 

  'rule' access_mode(-> read):
	  "read"

  'rule' access_mode(-> write):
	  "write"

  'rule' access_mode(-> in):
	  "in"

  'rule' access_mode(-> out):
	  "out"

-- &up 1a
'nonterm' opt_access_list(-> ACCESSES)

  'rule' opt_access_list(-> X):
	  access_list(-> X)

  'rule' opt_access_list(-> nil):

'nonterm' access_list(-> ACCESSES)

  'rule'  access_list(-> list(H,T)):
	   access(-> H)
	   ","
	   access_list(-> T)

  'rule'  access_list(-> list(H,nil)):
	   access(-> H)

'nonterm' access(-> ACCESS) 

  'rule' access(-> named_access(P, N)):
	  name(-> N) @(-> P)

  'rule' access(-> X):
	  enumerated_access(-> X)

  'rule' access(-> X):
	  completed_access(-> X)

  'rule' access(-> X):
	  comprehended_access(-> X)

-- &up 3b2
'nonterm' enumerated_access(-> ACCESS) 

  'rule' enumerated_access(-> enumerated_access(P, AS)):
	  "{"
	  opt_access_list(-> AS)
	  "}" @(-> P)

-- &up 2c4
'nonterm' completed_access(-> ACCESS)

  'rule' completed_access(-> completed_access(P, Q)):
	  opt_qualification(-> Q)
	  "any" @(-> P)

-- &up 5a1
'nonterm' comprehended_access(-> ACCESS) 

  'rule' comprehended_access(-> comprehended_access(P, A, L)):
	  "{"
	  access(-> A)
	  "|"
	  set_limitation(-> L)
	  "}" @(-> P)

-- &bg1 ---------------------------------
-- &up 1
'nonterm' value_expr_list2(-> VALUE_EXPRS)

 'rule' value_expr_list2(-> list(H,T)):
	 value_expr(-> H)
	 ","
	 value_expr_list(-> T) 

'nonterm' opt_value_expr_list(-> VALUE_EXPRS)

  'rule' opt_value_expr_list(-> X):
	  value_expr_list(-> X) 

  'rule' opt_value_expr_list(-> nil):

'nonterm' value_expr_list(-> VALUE_EXPRS) 

  'rule' value_expr_list(-> list(H,T)):
	  value_expr(-> H)
	  ","
	  value_expr_list(-> T)

  'rule' value_expr_list(-> list(H,nil)):
	  value_expr(-> H)

'nonterm' value_expr(-> VALUE_EXPR) 

  'rule' value_expr(-> X):
	  value_expr_pr14(-> X)

'nonterm' value_expr_pr14(-> VALUE_EXPR) 

  'rule' value_expr_pr14(-> X):
	  value_expr_pr13(-> X)

  'rule' value_expr_pr14(-> X):   
	  function_expr(-> X)

  'rule' value_expr_pr14(-> X):   
	  quantified_expr(-> X)

  'rule' value_expr_pr14(-> X):
	 prefix_expr_pr14(-> X)


'nonterm' value_expr_pr13(-> VALUE_EXPR) 

  'rule' value_expr_pr13(-> X):
	  value_expr_pr12(-> X)

  'rule' value_expr_pr13(-> X):  
	  equivalence_expr(-> X)

  'rule' value_expr_pr13(-> X):   
	  post_expr(-> X)

'nonterm' value_expr_pr12(-> VALUE_EXPR) 

  'rule' value_expr_pr12(-> X):
	  value_expr_pr11(-> X)

  'rule' value_expr_pr12(-> X):   
	  infix_expr_pr12(-> X)

'nonterm' value_expr_pr11(-> VALUE_EXPR) 

  'rule' value_expr_pr11(-> X):
	  value_expr_pr10(-> X)

  'rule' value_expr_pr11(-> X):   
	  infix_expr_pr11(-> X)

'nonterm' value_expr_pr10(-> VALUE_EXPR) 

  'rule' value_expr_pr10(-> X):
	  value_expr_pr9(-> X)

  'rule' value_expr_pr10(-> X):   
	  assignment_expr(-> X)

 'rule' value_expr_pr10(-> X):   
	  output_expr(-> X)

'nonterm' value_expr_pr9(-> VALUE_EXPR) 

  'rule' value_expr_pr9(-> X):
	  value_expr_pr8(-> X)

  'rule' value_expr_pr9(-> X):   
	  infix_expr_pr9(-> X)

'nonterm' value_expr_pr8(-> VALUE_EXPR) 

  'rule' value_expr_pr8(-> X):
	  value_expr_pr7(-> X)

  'rule' value_expr_pr8(-> X):   
	  infix_expr_pr8(-> X)

'nonterm' value_expr_pr7(-> VALUE_EXPR) 

  'rule' value_expr_pr7(-> X):
	  value_expr_pr6(-> X)

  'rule' value_expr_pr7(-> X):   
	  infix_expr_pr7(-> X)

'nonterm' value_expr_pr6(-> VALUE_EXPR) 

  'rule' value_expr_pr6(-> X):  
	  value_expr_pr5(-> X)

  'rule' value_expr_pr6(-> X):   
	  infix_expr_pr6(-> X)

'nonterm' value_expr_pr5(-> VALUE_EXPR) 

  'rule' value_expr_pr5(-> X):  
	  value_expr_pr4(-> X)

  'rule' value_expr_pr5(-> X):   
	  infix_expr_pr5(-> X)

'nonterm' value_expr_pr4(-> VALUE_EXPR) 

  'rule' value_expr_pr4(-> X):  
	  value_expr_pr3(-> X)

  'rule' value_expr_pr4(-> X):   
	  infix_expr_pr4(-> X)

'nonterm' value_expr_pr3(-> VALUE_EXPR) 

  'rule' value_expr_pr3(-> X):  
	  value_expr_pr2(-> X)

  'rule' value_expr_pr3(-> X):   
	  infix_expr_pr3(-> X)

'nonterm' value_expr_pr2(-> VALUE_EXPR) 

  'rule' value_expr_pr2(-> X):  
	  value_expr_pr1(-> X)

  'rule' value_expr_pr2(-> X):   
	  disambiguation_expr(-> X)

'nonterm' value_expr_pr1(-> VALUE_EXPR) 

  'rule' value_expr_pr1(-> X):  
	  value_expr_pr0(-> X)

  'rule' value_expr_pr1(-> X):   
	  prefix_expr_pr1(-> X)

'nonterm' value_expr_pr0(-> VALUE_EXPR) 

  'rule' value_expr_pr0(-> X):  
	  value_expr_pr255(-> X)

  'rule' value_expr_pr0(-> X):   
	  application_expr(-> X)

  'rule' value_expr_pr0(-> X):
         array_expr(-> X)


'nonterm' value_expr_pr255(-> VALUE_EXPR) 

  'rule' value_expr_pr255(-> literal_expr(P,X)):  
	  value_literal(-> X) @(-> P)

  'rule' value_expr_pr255(-> named_val(P,X)):  
	  name(-> X) @(-> P)

  'rule' value_expr_pr255(-> X):  
	  pre_name(-> X)

  'rule' value_expr_pr255(-> X):  
	  basic_expr(-> X)

  'rule' value_expr_pr255(-> X):  
	  product_expr(-> X)

  'rule' value_expr_pr255(-> X):  
	  set_expr(-> X)

  'rule' value_expr_pr255(-> X):  
	  list_expr(-> X)

  'rule' value_expr_pr255(-> X):  
	  map_expr(-> X)

  'rule' value_expr_pr255(-> X):   
	  bracketed_expr(-> X)

  'rule' value_expr_pr255(-> X):   
 	  comprehended_expr(-> X)

  'rule' value_expr_pr255(-> X):   
	  initialise_expr(-> X)

  'rule' value_expr_pr255(-> X):   
	  input_expr(-> X)

  'rule' value_expr_pr255(-> X):   
	  structured_expr(-> X)

  'rule' value_expr_pr255(-> X):
         array_access_expr(-> X)


-- &bg2 ---------------------------------
-- &up 1a
'nonterm' value_literal(->  VALUE_LITERAL)

  'rule' value_literal(-> unit):
	  unit_lit

  'rule' value_literal(-> bool_true):
	  bool_true

  'rule' value_literal(-> bool_false):
	  bool_false

  'rule' value_literal(-> int(X)):
	  int_lit(-> X)

  'rule' value_literal(-> real(X)):
	  real_lit(-> X)

  'rule' value_literal(-> text(X)):
	  text_lit(-> X)

  'rule' value_literal(-> char(X)):
	  char_lit(-> X)

-- &up 2a1
'nonterm' unit_lit 

  'rule' unit_lit:
	  "("
	  ")"

-- &up 1a
'nonterm' bool_true 

  'rule' bool_true:
	  "true"

'nonterm' bool_false 

  'rule' bool_false:
	  "false"

-- &bg2 ---------------------------------
-- &up 2c1
'nonterm' pre_name(-> VALUE_EXPR)

  'rule' pre_name(-> pre_name(P,N)):
	  name(-> N)
	  "`" @(-> P)

-- &bg2 ---------------------------------
-- &up 1a
'nonterm' basic_expr(-> VALUE_EXPR) 

  'rule' basic_expr(-> chaos(P)):
	  "chaos" @(-> P)

  'rule' basic_expr(-> skip(P)):
	  "skip" @(-> P)

  'rule' basic_expr(-> stop(P)):
	  "stop" @(-> P)

  'rule' basic_expr(-> swap(P)):
	  "swap" @(-> P)

-- &bg2 ---------------------------------
-- &up 3b1
'nonterm' product_expr(-> VALUE_EXPR) 

  'rule' product_expr(-> product(P,X)):
	 "("
	 value_expr_list2(-> X)
	 ")" @(-> P)

-- &bg2 ---------------------------------
-- &up 1
'nonterm' set_expr(-> VALUE_EXPR) 

  'rule' set_expr(-> X):
	  ranged_set_expr(-> X)

  'rule' set_expr(-> X):
	  enumerated_set_expr(-> X)

  'rule' set_expr(-> X):
	  comprehended_set_expr(-> X)

-- &bg3
-- &up 5a1
'nonterm' ranged_set_expr(-> VALUE_EXPR) 

  'rule' ranged_set_expr(-> ranged_set(P,L,R)):
	  "{"
	  value_expr(-> L)
	  ".."
	  value_expr(-> R)
	  "}" @(-> P)

-- &bg3
-- &up 3b2
'nonterm' enumerated_set_expr(-> VALUE_EXPR) 

  'rule' enumerated_set_expr(-> enum_set(P,X)):
	  "{"
	  opt_value_expr_list(-> X)
	  "}" @(-> P)

-- &bg3
-- &up 5a1
'nonterm' comprehended_set_expr(-> VALUE_EXPR) 

  'rule' comprehended_set_expr(-> comp_set(P,E,L)):
	  "{"
	  value_expr(-> E)
	  "|"
	  set_limitation(-> L)
	  "}" @(-> P)

-- &up 2d4
'nonterm' set_limitation(-> SET_LIMITATION)

  'rule' set_limitation(-> set_limit(P,L,R)):
	  typing_list(-> L)
	  opt_restriction(-> R) @(-> P)

-- &up 2b5
'nonterm' opt_restriction(-> RESTRICTION)

  'rule' opt_restriction(-> X):
	  restriction(-> X) 

  'rule' opt_restriction(-> nil):

'nonterm' restriction(-> RESTRICTION) 

  'rule' restriction(-> restriction(P,X)):
	  ":-"
	  value_expr(-> X) @(-> P)

-- &bg2 ---------------------------------
-- &up 1
'nonterm' list_expr(-> VALUE_EXPR) 

  'rule' list_expr(-> X):
	  ranged_list_expr(-> X)

  'rule' list_expr(-> X):
	  enumerated_list_expr(-> X)

  'rule' list_expr(-> X):
	  comprehended_list_expr(-> X)

-- &bg3
-- &up 5a1
'nonterm' ranged_list_expr(-> VALUE_EXPR) 

  'rule' ranged_list_expr(-> ranged_list(P,L,R)):
	  "<."
	  value_expr(-> L)
	  ".."
	  value_expr(-> R)
	  ".>" @(-> P)

-- &bg3
-- &up 3b2
'nonterm' enumerated_list_expr(-> VALUE_EXPR) 

  'rule' enumerated_list_expr(-> enum_list(P,X)):
	  "<."
	  opt_value_expr_list(-> X)
	  ".>" @(-> P)

-- &bg3
-- &up 5a1
'nonterm' comprehended_list_expr(-> VALUE_EXPR) 

  'rule' comprehended_list_expr(-> comp_list(P,E,L)):
	  "<."
	  value_expr(-> E)
	  "|"
	  list_limitation(-> L)
	  ".>" @(-> P)

-- &up 4f1
'nonterm' list_limitation(-> LIST_LIMITATION) 

  'rule' list_limitation(-> list_limit(P,B,E,R)):
	  binding(-> B)
	  "in"
	  value_expr(-> E)
	  opt_restriction(-> R) @(-> P) 

-- &bg2 ---------------------------------
-- &up 1
'nonterm' map_expr(-> VALUE_EXPR) 

  'rule' map_expr(-> X):  
	  enumerated_map_expr(-> X)

  'rule' map_expr(-> X):  
	  comprehended_map_expr(-> X)

-- &bg3
-- &up 3b2
'nonterm' enumerated_map_expr(-> VALUE_EXPR) 

  'rule' enumerated_map_expr(-> enum_map(P,L)):
	  "["
	  opt_value_expr_pair_list(-> L)
	  "]" @(-> P)

-- &up 3e1
'nonterm' opt_value_expr_pair_list(-> VALUE_EXPR_PAIRS)

  'rule' opt_value_expr_pair_list(-> X):
	  value_expr_pair_list(-> X)

  'rule' opt_value_expr_pair_list(-> nil):

'nonterm' value_expr_pair_list(-> VALUE_EXPR_PAIRS)

  'rule' value_expr_pair_list(-> list(H,T)):
	  value_expr_pair(-> H)
	  ","
	  value_expr_pair_list(-> T)

  'rule' value_expr_pair_list(-> list(H,nil)):
	  value_expr_pair(-> H)

'nonterm' value_expr_pair(-> VALUE_EXPR_PAIR)

  'rule' value_expr_pair(-> pair(L,R)):
	  value_expr(-> L)
	  "+>"
	  value_expr(-> R)

-- &bg3
-- &up 5a1
'nonterm' comprehended_map_expr(-> VALUE_EXPR) 

  'rule' comprehended_map_expr(-> comp_map(P,E,L)):
	  "["
	  value_expr_pair(-> E)
	  "|"
	  set_limitation(-> L)
	  "]" @(-> P)

-- &bg2 ---------------------------------
-- &up 4c2
'nonterm' function_expr(-> VALUE_EXPR) 

  'rule' function_expr(-> function(P,L,E)):
	  "-\\"
	  lambda_parameter(-> L)
	  ":-"
	  value_expr_pr14(-> E) @(-> P)

-- &up 1
'nonterm' lambda_parameter(-> LAMBDA_PARAMETER) 

  'rule' lambda_parameter(-> X):
	  lambda_typing(-> X)

  'rule' lambda_parameter(-> s_typing(P,T)):
	  single_typing(-> T) @(-> P)

-- &up 3b2
'nonterm' lambda_typing(-> LAMBDA_PARAMETER) 

  'rule' lambda_typing(-> l_typing(P,L)):
	  "("
	  opt_typing_list(-> L)
	  ")" @(-> P)

-- &bg2 ---------------------------------

'nonterm' array_expr(-> VALUE_EXPR)
  'rule'  array_expr(-> array_expr(P,T,V))
          
          "[|"
          "["
          --type_expr(-> T)
          single_typing(-> T)
          "]"
          value_expr(-> V)
          "|]" @(-> P)

'nonterm' array_access_expr(-> VALUE_EXPR)
  'rule' array_access_expr(-> array_access(P, named_val(PN,N), I))
         name(-> N) @(-> PN)
         "["
         value_expr(-> I)      
         "]"   
	 @(-> P)

  'rule' array_access_expr(-> array_access(P, N, I))
         value_expr_pr0(-> N)
         "["
         value_expr(-> I)
         "]"
         @(-> P)

'nonterm' array_accesses(-> VALUE_EXPRS)
  'rule' array_accesses(-> list(H, nil))
         "["
         value_expr(-> H)
         "]"

  'rule' array_accesses(-> list(H,T))
         "["
         value_expr(-> H)
         "]"
         array_accesses(-> T)


/*         opt_array_accesses(-> T)
         
'nonterm' opt_array_accesses(-> VALUE_EXPRS)
  'rule' opt_array_accesses(-> list(H,T))
         "["
         value_expr(-> H)
         "]"
         opt_array_accesses(-> T)

  'rule' opt_array_accesses(-> nil)*/

-- &up 2d5
'nonterm' application_expr(-> VALUE_EXPR)

  'rule' application_expr(-> application(P,F,A)):
	  value_expr_pr255(-> F)
	  actual_function_parameter_string(-> A) @(-> P)

-- &up 3b2
'nonterm' actual_function_parameter_string(-> ACTUAL_FUNCTION_PARAMETERS)

  'rule' actual_function_parameter_string(-> list(H,T)):
	  actual_function_parameter(-> H)
	  actual_function_parameter_string(-> T) 

  'rule' actual_function_parameter_string(-> list(H,nil)):
	  actual_function_parameter(-> H)

'nonterm' actual_function_parameter(-> ACTUAL_FUNCTION_PARAMETER) 

  'rule' actual_function_parameter(-> fun_arg(P,L)):
	  "("
	  opt_value_expr_list(-> L)
	  ")" @(-> P)

-- &bg2 ---------------------------------
-- &up 3d2
'nonterm' quantified_expr(-> VALUE_EXPR) 

  'rule' quantified_expr(-> quantified(P,Q,L,R)):
	  quantifier(-> Q)
	  typing_list(-> L)
	  restriction(-> R) @(-> P)

-- &up 1a
'nonterm' quantifier(-> QUANTIFIER) 

  'rule' quantifier(-> all):
	  "all"

  'rule' quantifier(-> exists):
	  "exists"

-- &up 2a1
  'rule' quantifier(-> exists1):
	  "exists!"

-- &bg2 ---------------------------------
-- &up 4f2
'nonterm' equivalence_expr(-> VALUE_EXPR) 

  'rule' equivalence_expr(-> equivalence(P,L,R,PR)):
	  value_expr_pr12(-> L)
	  "is"
	  value_expr_pr12(-> R)
	  opt_pre_condition(-> PR) @(-> P)

-- &up 2b2
'nonterm' opt_pre_condition(-> PRE_CONDITION) 

  'rule' opt_pre_condition(-> X):
	  pre_condition(-> X)

  'rule' opt_pre_condition(-> nil):

'nonterm' pre_condition(-> PRE_CONDITION) 

  'rule' pre_condition(-> pre_cond(P,X)):
	  "pre"
	  value_expr_pr12(-> X) @(-> P)

'nonterm' opt_post_condition(-> OPT_POST_CONDITION)

  'rule' opt_post_condition(-> post(X)):
	 post_condition(-> X)

  'rule' opt_post_condition(-> nil):

-- &bg2 ---------------------------------
-- &up 3f2
'nonterm' post_expr(->  VALUE_EXPR)

  'rule' post_expr(-> post(P,E,C,PR)):
	  value_expr_pr12(-> E)
	  post_condition(-> C)
	  opt_pre_condition(-> PR) @(-> P)

-- &up 3e7
'nonterm' post_condition(-> POST_CONDITION) 

  'rule' post_condition(-> post_cond(P,R,E)):
	  opt_result_naming(-> R)
	  "post"
	  value_expr_pr12(-> E) @(-> P)

-- &up 2b1
'nonterm' opt_result_naming(-> RESULT_NAMING)

  'rule' opt_result_naming(-> X):
	  result_naming(-> X)

  'rule' opt_result_naming(-> nil):

'nonterm' result_naming(-> RESULT_NAMING) 

  'rule' result_naming(-> result(P,B)):
	  "as"
	  binding(-> B) @(-> P)

-- &bg2 ---------------------------------
-- &up 3e2
'nonterm' disambiguation_expr(-> VALUE_EXPR) 

  'rule' disambiguation_expr(-> disamb(P,E,T)):
	  value_expr_pr1(-> E)
	  ":"
	  type_expr(-> T) @(-> P)

-- &bg2 ---------------------------------
-- &up 3b1
'nonterm' bracketed_expr(-> VALUE_EXPR)

  'rule' bracketed_expr(-> bracket(P,E)):
	  "("
	  value_expr(-> E)
	  ")" @(-> P)

-- &bg2 ---------------------------------
-- &up 1
--u 'nonterm' infix_expr 

--u   'rule' infix_expr:
--u 	  infix_expr_pr12

--u   'rule' infix_expr:
--u 	  infix_expr_pr11

--u   'rule' infix_expr:
--u 	  infix_expr_pr9

--u   'rule' infix_expr:
--u 	  infix_expr_pr8

--u   'rule' infix_expr:
--u 	  infix_expr_pr7

--u   'rule' infix_expr:
--u 	  infix_expr_pr6

--u   'rule' infix_expr:
--u 	  infix_expr_pr5

--u   'rule' infix_expr:
--u 	  infix_expr_pr4

--u   'rule' infix_expr:
--u 	  infix_expr_pr3

'nonterm' infix_expr_pr12(-> VALUE_EXPR) 

  'rule' infix_expr_pr12(-> X):  
	  stmt_infix_expr_pr12(-> X)

'nonterm' infix_expr_pr11(-> VALUE_EXPR) 

  'rule' infix_expr_pr11(-> X):  
	  stmt_infix_expr_pr11(-> X)

'nonterm' infix_expr_pr9(-> VALUE_EXPR) 

  'rule' infix_expr_pr9(-> X):  
	  axiom_infix_expr_pr9(-> X)

'nonterm' infix_expr_pr8(-> VALUE_EXPR) 

  'rule' infix_expr_pr8(-> X):  
	  axiom_infix_expr_pr8(-> X)

'nonterm' infix_expr_pr7(-> VALUE_EXPR) 

  'rule' infix_expr_pr7(-> X):  
	  axiom_infix_expr_pr7(-> X)

'nonterm' infix_expr_pr6(-> VALUE_EXPR) 

  'rule' infix_expr_pr6(-> X):  
	  value_infix_expr_pr6(-> X)

'nonterm' infix_expr_pr5(-> VALUE_EXPR) 

  'rule' infix_expr_pr5(-> X):  
	  value_infix_expr_pr5(-> X)

'nonterm' infix_expr_pr4(-> VALUE_EXPR) 

  'rule' infix_expr_pr4(-> X):  
	  value_infix_expr_pr4(-> X)

'nonterm' infix_expr_pr3(-> VALUE_EXPR) 

  'rule' infix_expr_pr3(-> X):  
	  value_infix_expr_pr3(-> X)

-- &bg3
-- &up 3e6
'nonterm' stmt_infix_expr_pr12(-> VALUE_EXPR) 

 'rule' stmt_infix_expr_pr12(-> stmt_infix(P, L, C, R)):
	  value_expr_pr11(-> L)
	  infix_combinator_pr12(-> C)
	  value_expr_pr12(-> R) @(-> P)

'nonterm' stmt_infix_expr_pr11(-> VALUE_EXPR) 

 'rule' stmt_infix_expr_pr11(-> stmt_infix(P, L, C, R)):
	  value_expr_pr10(-> L)
	  infix_combinator_pr11(-> C)
	  value_expr_pr11(-> R) @(-> P)

-- &up 1
--u 'nonterm' stmt_infix_expr 

--u  'rule' stmt_infix_expr:
--u 	  stmt_infix_expr_pr12

--u  'rule' stmt_infix_expr:
--u 	  stmt_infix_expr_pr11

-- &bg3
-- &up 3e5
'nonterm' axiom_infix_expr_pr9(-> VALUE_EXPR) 

  'rule' axiom_infix_expr_pr9(-> ax_infix(P,L,C,R,PRE)):
	  value_expr_pr8(-> L)
	  infix_connective_pr9(-> C)
	  value_expr_pr9(-> R) @(-> P) dummy_term @(-> PRE)

'nonterm' axiom_infix_expr_pr8(-> VALUE_EXPR) 

  'rule' axiom_infix_expr_pr8(-> ax_infix(P,L,C,R,PRE)):
	  value_expr_pr7(-> L)
	  infix_connective_pr8(-> C)
	  value_expr_pr8(-> R) @(-> P) dummy_term @(-> PRE)

'nonterm' axiom_infix_expr_pr7(-> VALUE_EXPR) 

  'rule' axiom_infix_expr_pr7(-> ax_infix(P,L,C,R,PRE)):
	  value_expr_pr6(-> L)
	  infix_connective_pr7(-> C)
	  value_expr_pr7(-> R) @(-> P) dummy_term @(-> PRE)

-- &up 1
--u 'nonterm' axiom_infix_expr 

--u   'rule' axiom_infix_expr:
--u 	  axiom_infix_expr_pr9

--u   'rule' axiom_infix_expr:
--u 	  axiom_infix_expr_pr8

--u   'rule' axiom_infix_expr:
--u 	  axiom_infix_expr_pr7

-- &bg3
-- &up 3e5
'nonterm' value_infix_expr_pr6(-> VALUE_EXPR) 

  'rule' value_infix_expr_pr6(-> val_infix(P,L,O,R)):
	  value_expr_pr5(-> L)
	  infix_op_pr6(-> O)
	  value_expr_pr5(-> R) @(-> P)

'nonterm' value_infix_expr_pr5(-> VALUE_EXPR) 

  'rule' value_infix_expr_pr5(-> val_infix(P,L,O,R)):
	  value_expr_pr5(-> L)
	  infix_op_pr5(-> O)
	  value_expr_pr4(-> R) @(-> P)

  'rule' value_infix_expr_pr5(-> val_infix(P,L,O,R)):
	  value_expr_pr5(-> L)
	  infix_prefix_op(-> O)
	  value_expr_pr4(-> R) @(-> P)

'nonterm' value_infix_expr_pr4(-> VALUE_EXPR) 

  'rule' value_infix_expr_pr4(-> val_infix(P,L,O,R)):
	  value_expr_pr4(-> L)
	  infix_op_pr4(-> O)
	  value_expr_pr3(-> R) @(-> P)

'nonterm' value_infix_expr_pr3(-> VALUE_EXPR) 

  'rule' value_infix_expr_pr3(-> val_infix(P,L,O,R)):
	  value_expr_pr2(-> L)
	  infix_op_pr3(-> O)
	  value_expr_pr2(-> R) @(-> P)

-- &up 1
--u 'nonterm' value_infix_expr 

--u   'rule' value_infix_expr:
--u 	  value_infix_expr_pr6

--u   'rule' value_infix_expr:
--u 	  value_infix_expr_pr5
 
--u   'rule' value_infix_expr:
--u 	  value_infix_expr_pr4

--u   'rule' value_infix_expr:
--u 	  value_infix_expr_pr3

-- &bg2 ---------------------------------
-- &up 1
'nonterm' prefix_expr_pr1(-> VALUE_EXPR) 

  'rule' prefix_expr_pr1(-> X):
	  axiom_prefix_expr(-> X)

  'rule' prefix_expr_pr1(-> X):
	  value_prefix_expr(-> X)

'nonterm' prefix_expr_pr14(-> VALUE_EXPR) 

 'rule' prefix_expr_pr14(-> X):
	  universal_prefix_expr(-> X)

--u 'nonterm' prefix_expr 

--u  'rule' prefix_expr:
--u 	  prefix_expr_pr14

--u   'rule' prefix_expr:
--u 	  prefix_expr_pr1

-- &bg3
-- &up 2b2
'nonterm' axiom_prefix_expr(-> VALUE_EXPR) 

  'rule' axiom_prefix_expr(-> ax_prefix(P,C,E)):
	  prefix_connective(-> C)
	  value_expr_pr1(-> E) @(-> P)

-- &bg3
'nonterm' universal_prefix_expr(-> VALUE_EXPR) 

 'rule' universal_prefix_expr(-> always(P, E)):
	  "always"
	  value_expr_pr14(-> E) @(-> P)

-- &bg3
'nonterm' value_prefix_expr(-> VALUE_EXPR) 

  'rule' value_prefix_expr(-> val_prefix(P,O,E)):
	  prefix_op(-> O)
	  value_expr_pr1(-> E) @(-> P)

  'rule' value_prefix_expr(-> val_prefix(P,O,E)):
	  infix_prefix_op(-> O)
	  value_expr_pr1(-> E) @(-> P)

-- &bg2 ---------------------------------
-- &up 6
'nonterm' comprehended_expr(-> VALUE_EXPR) 

 'rule' comprehended_expr(-> comprehended(P, C, E, L)):
	  infix_combinator(-> C)
	  "{"
	  value_expr(-> E)
	  "|"
	  set_limitation(-> L)
	  "}" @(-> P)

-- &bg2 ---------------------------------
-- &up 2c4
'nonterm' initialise_expr(-> VALUE_EXPR) 

 'rule' initialise_expr(-> initialise(P, Q)):
	  opt_qualification(-> Q)
	  "initialise" @(-> P)

-- &bg2 ---------------------------------
-- &up 3e3
'nonterm' assignment_expr(-> VALUE_EXPR) 

 'rule' assignment_expr(-> assignment(P, N, E)):
	  name(-> N)
	  ":="
	  value_expr_pr9(-> E) @(-> P)

-- &bg2 ---------------------------------
-- &up 2c1
'nonterm' input_expr(-> VALUE_EXPR) 

 'rule' input_expr(-> input(P, N)):
	  name(-> N)
	  "?" @(-> P)

-- &bg2 ---------------------------------
-- &up 3e3
'nonterm' output_expr(-> VALUE_EXPR) 

 'rule' output_expr(-> output(P, N, E)):
	  name(-> N)
	  "!"
	  value_expr_pr9(-> E) @(-> P)

-- &bg2 ---------------------------------
-- &up 1
'nonterm' structured_expr(-> VALUE_EXPR) 

  'rule' structured_expr(-> X):
	  local_expr(-> X)

  'rule' structured_expr(-> X):
	  let_expr(-> X)

  'rule' structured_expr(-> X):
	  if_expr(-> X)

  'rule' structured_expr(-> X):
	  case_expr(-> X)

 'rule' structured_expr(-> X):
	  while_expr(-> X)

 'rule' structured_expr(-> X):
	  until_expr(-> X)

 'rule' structured_expr(-> X):
	  for_expr(-> X)

-- &bg3 ---------------------------------
-- &up 5a3
'nonterm' local_expr(-> VALUE_EXPR) 

 'rule' local_expr(-> local_expr(P, DS, E)):
	  "local"
	  opt_decl_string(-> DS)
	  "in"
	  value_expr(-> E)
	  "end" @(-> P)

-- &bg3 ---------------------------------
-- &up 5a1
'nonterm' let_expr(-> VALUE_EXPR) 

  'rule' let_expr(-> let_expr(P,L,E)):
	  "let"
	  let_def_list(-> L)
	  "in"
	  value_expr(-> E)
	  "end" @(-> P)

-- &up 1
'nonterm' let_def_list(-> LET_DEFS)

  'rule' let_def_list(-> list(H,T)):
	  let_def(-> H)
	  ","
	  let_def_list(-> T) 

  'rule' let_def_list(-> list(H,nil)):
	  let_def(-> H)

'nonterm' let_def(-> LET_DEF) 

  'rule' let_def(-> implicit(P,T,nil)):
	  typing(-> T) @(-> P)

  'rule' let_def(-> X):
	  explicit_let(-> X)

  'rule' let_def(-> X):
	  implicit_let(-> X)

-- &up 3e1
'nonterm' explicit_let(-> LET_DEF) 

  'rule' explicit_let(-> explicit(P,B,E)):
	  let_binding(-> B)
	  "="
	  value_expr(-> E) @(-> P)

-- &up 2d3
'nonterm' implicit_let(-> LET_DEF) 

  'rule' implicit_let(-> implicit(P,T,R)):
	  single_typing(-> T)
	  restriction(-> R) @(-> P)

-- &up 1
'nonterm' let_binding(-> LET_BINDING)

  'rule' let_binding(-> binding(P,B)):
	  binding(-> B) @(-> P)

  'rule' let_binding( -> pattern(P,PATT)):
	  record_pattern(-> PATT) @(->P)

 'rule' let_binding( -> pattern(P,PATT)):
	  list_pattern(-> PATT) @(->P)

-- &bg3 ---------------------------------
-- &up 7
'nonterm' if_expr(-> VALUE_EXPR) 

  'rule' if_expr(-> if_expr(P,I,T,region(PTB,PTE),EI,E)):
	  "if"
	  value_expr(-> I)
	  "then"
	  value_expr(-> T) @(-> PTB)
	  opt_elsif_branch_string(-> EI) @(-> PTE)
	  opt_else_branch(-> E)
	  "end" @(-> P)

-- &up 4c3
'nonterm' opt_elsif_branch_string(-> ELSIF_BRANCHES)

  'rule' opt_elsif_branch_string(-> X):
	  elsif_branch_string(-> X)

  'rule' opt_elsif_branch_string(-> nil):

'nonterm' elsif_branch_string(-> ELSIF_BRANCHES)

  'rule' elsif_branch_string(-> list(H,T)):
	  elsif_branch(-> H)
	  elsif_branch_string(-> T)

  'rule' elsif_branch_string(-> list(H,nil)):
	  elsif_branch(-> H)

'nonterm' elsif_branch(-> ELSIF_BRANCH)

  'rule' elsif_branch(-> elsif(PB,I,T,PE)):
	  "elsif"
	  value_expr(-> I)
	  "then"
	  value_expr(-> T) @(-> PB)
	  dummy_term @(-> PE)

-- &up 2b5
'nonterm' opt_else_branch(-> ELSE_BRANCH) 

  'rule' opt_else_branch(-> X):
	  else_branch(-> X)

  'rule' opt_else_branch(-> nil):

'nonterm' else_branch(-> ELSE_BRANCH)

  'rule' else_branch(-> else(P,E)):
	  "else"
	  value_expr(-> E) @(-> P)

-- &bg3 ---------------------------------
-- &up 5a1
'nonterm' case_expr(-> VALUE_EXPR) 

  'rule' case_expr(-> case_expr(P,E,PE,L)):
	  "case"
	  value_expr(-> E) @(-> PE)
	  "of"
	  case_branch_list(-> L)
	  "end" @(-> P)

-- &up 3e1
'nonterm' case_branch_list(-> CASE_BRANCHES)

  'rule' case_branch_list(-> list(H,T)):
	  case_branch(-> H)
	  ","
	  case_branch_list(-> T) 

  'rule' case_branch_list(-> list(H,nil)):
	  case_branch(-> H)

'nonterm' case_branch(-> CASE_BRANCH)

  'rule' case_branch(-> case(P,X,E,PE)):
	  pattern(-> X)
	  "->"
	  value_expr(-> E) @(-> P)
	  dummy_term @(-> PE)

-- &bg3 ---------------------------------
-- &up 5a1
'nonterm' while_expr(-> VALUE_EXPR) 

 'rule' while_expr(-> while_expr(P, E, D)):
	  "while"
	  value_expr(-> E)
	  "do"
	  value_expr(-> D)
	  "end" @(-> P)

-- &bg3 ---------------------------------
-- &up 5a1
'nonterm' until_expr(-> VALUE_EXPR) 

 'rule' until_expr(-> until_expr(P, D, E)):
	  "do"
	  value_expr(-> D)
	  "until"
	  value_expr(-> E)
	  "end" @(-> P)

-- &bg3 ---------------------------------
-- &up 5a1
'nonterm' for_expr(-> VALUE_EXPR) 

 'rule' for_expr(-> for_expr(P, L, E)):
	  "for"
	  list_limitation(-> L)
	  "do"
	  value_expr(-> E)
	  "end" @(-> P)

-- &bg1 ---------------------------------
-- &up 1
'nonterm' opt_binding_list(-> BINDINGS)

  'rule' opt_binding_list(-> X):
	  binding_list(-> X)

  'rule' opt_binding_list(-> nil):

'nonterm' binding_list2(-> BINDINGS)

  'rule' binding_list2(-> list(H,T)):
	  binding(-> H)
	  ","
	  binding_list(-> T)

'nonterm' binding_list(-> BINDINGS)

  'rule' binding_list(-> list(H,T)):
	  binding(-> H)
	  ","
	  binding_list(-> T)

  'rule' binding_list(-> list(H,nil)):
	  binding(-> H)

'nonterm' binding(-> BINDING) 

  'rule' binding(-> single(P,Id)):
	  id_or_op(-> Id) @(-> P)

  'rule' binding(-> X):
	  product_binding(-> X)

-- &up 3b1
'nonterm' product_binding(-> BINDING) 

  'rule' product_binding(-> product(P,L)):
	  "("
	  binding_list2(-> L)
	  ")" @(-> P)

-- &bg1 ---------------------------------
-- &up 1
'nonterm' opt_typing_list(-> TYPINGS)

  'rule' opt_typing_list(-> X):
	 typing_list(-> X)

  'rule' opt_typing_list(-> nil):

'nonterm' typing_list(-> TYPINGS)

  'rule'  typing_list(-> list(H,T)):
	   typing(-> H)
	   ","
	   typing_list(-> T)

  'rule'  typing_list(-> list(H,nil)):
	   typing(-> H)

'nonterm' typing(-> TYPING) 

  'rule' typing(-> X):
	  single_typing(-> X)

  'rule' typing(-> X):
	  multiple_typing(-> X)

-- &up 3e1
'nonterm' single_typing(-> TYPING) 

  'rule' single_typing(-> single(P,B,T)):
	  binding(-> B)
	  ":"
	  type_expr(-> T) @(-> P)

-- &up 3e1
'nonterm' multiple_typing(-> TYPING) 

  'rule' multiple_typing(-> multiple(P,B,T)):
	  binding_list2(-> B)
	  ":"
	  type_expr(-> T) @(-> P)

-- &up 2d7
'nonterm' commented_typing(-> VALUE_DEF) 

  'rule' commented_typing(-> typing(P,T)):
--	  opt_comment_string
	  typing(-> T) @(-> P)


-- Comments are ignored for now
--'nonterm' opt_comment_string

--  'rule' opt_comment_string:
--	  comment_string
 
--  'rule' opt_comment_string: 

--'nonterm' comment_string

--  'rule' comment_string:
--	  comment
--	  comment_string
 
--  'rule' comment_string:
--	  comment

--'nonterm' comment

--  'rule' comment: "&"
 
-- &bg1 ---------------------------------
-- &up 1
'nonterm' pattern(-> PATTERN) 

  'rule' pattern(-> literal_pattern(P,L)):
	  value_literal(-> L) @(-> P)

  'rule' pattern(-> name_pattern(P,N)):
	  name(-> N) @(-> P)

  'rule' pattern(-> X):
	  wildcard_pattern(-> X)

  'rule' pattern(-> X):
	  product_pattern(-> X)

   'rule' pattern(-> X):
	  record_pattern(-> X)

  'rule' pattern(-> X):
	  list_pattern(-> X)

-- &bg2 ---------------------------------
-- &up 1a
'nonterm' wildcard_pattern(-> PATTERN) 

  'rule' wildcard_pattern(-> wildcard_pattern(P)):
	  "_" @(-> P)

-- &bg2 ---------------------------------
-- &up 3b1
'nonterm' product_pattern(-> PATTERN) 

  'rule' product_pattern(-> product_pattern(P,L)):
	  "("
	  inner_pattern_list2(-> L)
	  ")" @(-> P)

-- &bg2 ---------------------------------
-- &up 4g1
'nonterm' record_pattern(-> PATTERN) 

  'rule' record_pattern(-> record_pattern(P, N, PS)):
	  name(-> N)
 	  "("
 	  inner_pattern_list(-> PS)
	  ")" @(-> P)

-- &bg2 ---------------------------------
-- &up 1
'nonterm' list_pattern(-> PATTERN) 

  'rule' list_pattern(-> enum_list(P,L)):
	  enumerated_list_pattern(-> L) @(-> P)

  'rule' list_pattern(-> X):
	  concatenated_list_pattern(-> X)

--  'rule' list_pattern:
--	  right_list_pattern

-- &bg3
-- &up 3b2
'nonterm' enumerated_list_pattern(-> PATTERNS) 

  'rule' enumerated_list_pattern(-> L):
	  "<."
	  opt_inner_pattern_list(-> L)
	  ".>"

-- &bg3
-- &up 3e1
'nonterm' concatenated_list_pattern(-> PATTERN) 

  'rule' concatenated_list_pattern(-> conc_list(P,E,I)):
	  enumerated_list_pattern(-> E)
	  "^"
	  inner_pattern(-> I) @(-> P)

-- &bg3
-- &up 3c1
--'nonterm' right_list_pattern 

--  'rule' right_list_pattern:
--	  id
--	  "^"
--	  enumerated_list_pattern

-- &bg2 ----------------------------------
-- &up 1
'nonterm' opt_inner_pattern_list(-> PATTERNS)

  'rule' opt_inner_pattern_list(-> X):
	  inner_pattern_list(-> X)

  'rule' opt_inner_pattern_list(-> nil):

'nonterm' inner_pattern_list2(-> PATTERNS)

  'rule' inner_pattern_list2(-> list(H,T)):
	  inner_pattern(-> H)
	  ","
	  inner_pattern_list(-> T)

'nonterm' inner_pattern_list(-> PATTERNS)

  'rule' inner_pattern_list(-> list(H,T)):
	  inner_pattern(-> H)
	  ","
	  inner_pattern_list(-> T) 

  'rule' inner_pattern_list(-> list(H,nil)):
	  inner_pattern(-> H)

'nonterm' inner_pattern(-> PATTERN) 

  'rule' inner_pattern(-> literal_pattern(P,L)):
	  value_literal(-> L) @(-> P)

  'rule' inner_pattern(-> id_pattern(P, Id)):
	  id_or_op(-> Id) @(-> P)

  'rule' inner_pattern(-> X):
	  wildcard_pattern(-> X)

  'rule' inner_pattern(-> X):
	  product_pattern(-> X)

  'rule' inner_pattern(-> X):
	  record_pattern(-> X)

  'rule' inner_pattern(-> X):
	  list_pattern(-> X)

  'rule' inner_pattern(-> X):
	  equality_pattern(-> X)

-- &bg3 ---------------------------------
-- &up 2b4
'nonterm' equality_pattern(-> PATTERN) 

  'rule' equality_pattern(-> name_pattern(P,N)):
	  "="
	  name(-> N) @(-> P)

-- &bg1 ---------------------------------
-- &up 1a
'nonterm' name(-> NAME) 

  'rule' name(-> X):
	  qualified_id(-> X)

   'rule' name(-> X):
	  qualified_op(-> X)

-- &bg2
-- &up 2c3
'nonterm' qualified_id(-> NAME) 

  'rule' qualified_id(-> qual_name(P,O,id_op(Id))):
 	  qualification(-> O)
 	  id(-> Id) @(-> P)

  'rule' qualified_id(-> name(P,id_op(Id))):
	  id(-> Id) @(-> P)

-- &up 2c1
'nonterm' opt_qualification(-> OPT_QUALIFICATION) 

  'rule' opt_qualification(-> qualification(Q)):
	  qualification(-> Q)

  'rule' opt_qualification(-> nil):

'nonterm' qualification(-> OBJECT_EXPR)

  'rule' qualification(-> O):
	  object_expr(-> O)
 	  "."

-- &bg2
-- &up 4a1
'nonterm' qualified_op(-> NAME) 

   'rule' qualified_op(-> qual_name(P,O,op_op(Op))):
 	  qualification(-> O)
 	  "("
 	  op(-> Op)
 	  ")"@(-> P)

   'rule' qualified_op(-> name(P,op_op(Op))):
	  "("
 	  op(-> Op)
 	  ")"@(-> P)

-- &bg1 ---------------------------------
-- &up 1a
'nonterm' id_or_op(-> ID_OR_OP) 

  'rule' id_or_op(-> id_op(I)):
	  id(-> I)

   'rule' id_or_op(-> op_op(Op)):
 	  op(-> Op)

'nonterm' id_list2(-> IDENTS)

  'rule' id_list2(-> list(H,T)):
 	  id(-> H)
 	  ","
	  id_list(-> T)

'nonterm' id_list(-> IDENTS)

  'rule' id_list(-> list(H,T)):
	 id(-> H)
	 ","
	 id_list(-> T)

  'rule' id_list(-> list(H,nil)):
	 id(-> H)

-- &up 1a
'nonterm' op(-> OP) 

  'rule' op(-> X):
	  infix_op(-> X)

   'rule' op(-> X):
 	  prefix_op(-> X)

   'rule' op(-> X):
	  infix_prefix_op(-> X)

-- &bg2
-- &up 1b
'nonterm' infix_op(-> OP) 

  'rule' infix_op(-> X):
	  infix_op_pr6(-> X)

  'rule' infix_op(-> X):
	  infix_op_pr5(-> X)

  'rule' infix_op(-> X):
	  infix_op_pr4(-> X)

  'rule' infix_op(-> X):
	  infix_op_pr3(-> X)

'nonterm' infix_op_pr6(-> OP) 

  'rule' infix_op_pr6(-> eq):
	  "="

  'rule' infix_op_pr6(-> neq):
	  "~="

  'rule' infix_op_pr6(-> eqeq):
	  "=="

  'rule' infix_op_pr6(-> gt):
	  ">"

  'rule' infix_op_pr6(-> lt):
	  "<"

  'rule' infix_op_pr6(-> ge):
	  ">="

  'rule' infix_op_pr6(-> le):
	  "<="

  'rule' infix_op_pr6(-> supset):
	  ">>"

  'rule' infix_op_pr6(-> subset):
	  "<<"

  'rule' infix_op_pr6(-> supseteq):
	  ">>="

  'rule' infix_op_pr6(-> subseteq):
	  "<<="

  'rule' infix_op_pr6(-> isin):
	  "isin"

  'rule' infix_op_pr6(-> notisin):
	  "~isin"

'nonterm' infix_op_pr5(-> OP)

  'rule' infix_op_pr5(-> rem):
	  "\\"

  'rule' infix_op_pr5(-> caret):
	  "^"

  'rule' infix_op_pr5(-> union):
	  "union"

  'rule' infix_op_pr5(-> override):
	  "!!"

'nonterm' infix_op_pr4(-> OP) 

  'rule' infix_op_pr4(-> mult):
	  "*"

  'rule' infix_op_pr4(-> div):
	  "/"

  'rule' infix_op_pr4(-> hash):
	  "#"

  'rule' infix_op_pr4(-> inter):
	  "inter"

'nonterm' infix_op_pr3(-> OP)

  'rule' infix_op_pr3(-> exp):
	  "**"

-- &bg2
-- &up 1b
'nonterm' prefix_op(-> OP) 

  'rule' prefix_op(-> abs):
	  "abs"

  'rule' prefix_op(-> int):
	  "int"

  'rule' prefix_op(-> real):
	  "real"

  'rule' prefix_op(-> card):
	  "card"

  'rule' prefix_op(-> len):
	  "len"

  'rule' prefix_op(-> inds):
	  "inds"

  'rule' prefix_op(-> elems):
	  "elems"

  'rule' prefix_op(-> hd):
	  "hd"

  'rule' prefix_op(-> tl):
	  "tl"

  'rule' prefix_op(-> dom):
	  "dom"

  'rule' prefix_op(-> rng):
	  "rng"

  'rule' prefix_op(-> wait):
	 "wait" @(-> P)

'nonterm' infix_prefix_op(-> OP)

  'rule' infix_prefix_op(-> plus):
	  "+"

  'rule' infix_prefix_op(-> minus):
	  "-"


-- &bg1
-- &up 1a
--u 'nonterm' connective 

--u   'rule' connective:
--u 	  infix_connective

--u   'rule' connective:
--u 	  prefix_connective

-- &bg2
-- &up 1a
--u 'nonterm' infix_connective 

--u   'rule' infix_connective:
--u 	  infix_connective_pr9

--u   'rule' infix_connective:
--u 	  infix_connective_pr8

--u   'rule' infix_connective:
--u 	  infix_connective_pr7

'nonterm' infix_connective_pr9(-> CONNECTIVE) 

  'rule' infix_connective_pr9(-> implies):
	  "=>"

'nonterm' infix_connective_pr8(-> CONNECTIVE) 

  'rule' infix_connective_pr8(-> or):
	  "\\/"

'nonterm' infix_connective_pr7(-> CONNECTIVE) 

  'rule' infix_connective_pr7(-> and):
	  "/\\"

-- &bg2
-- &up 1a
'nonterm' prefix_connective(-> CONNECTIVE) 

  'rule' prefix_connective(-> not):
	  "~" 

-- &bg1
-- &up 1a
'nonterm' infix_combinator(-> COMBINATOR)

  'rule' infix_combinator(-> X):
	  infix_combinator_pr12(-> X)

  'rule' infix_combinator(-> X):
	  infix_combinator_pr11(-> X)

'nonterm' infix_combinator_pr12(-> COMBINATOR) 

  'rule' infix_combinator_pr12(-> ext_choice):
	  "|=|"

  'rule' infix_combinator_pr12(-> int_choice):
	  "|^|"

  'rule' infix_combinator_pr12(-> parallel):
	  "||"

  'rule' infix_combinator_pr12(-> interlock):
	  "++"

'nonterm' infix_combinator_pr11(-> COMBINATOR) 

  'rule' infix_combinator_pr11(-> sequence):
	  ";"

'nonterm' opt_files(-> FILE_NAMES)

  'rule' opt_files(-> X):
	 files(-> X)

  'rule' opt_files(-> nil):

'nonterm' files(-> FILE_NAMES)

  'rule' files(-> list(H,T)):
	 file(-> H)
	 ","
	 files(-> T)

  'rule' files(-> list(H,nil)):
	 file(-> H)

'nonterm' file(-> FILE_NAME)

-- includes ~/, ./ and ../ starts to path
  'rule' file(-> F):
	 filename(-> F)

-- allows / start to path
  'rule' file(-> F):
	 "/"
	 file1(-> S)
	 strings_to_fileid("", S -> F)

-- allows id/ start to path
  'rule' file(-> F)
	 id(-> Id)
	 "/"
	 file1(-> S2)
	 id_to_string(Id -> S1)
	 strings_to_fileid(S1, S2 -> F)

-- allows single id
  'rule' file(-> F)
	 id(-> Id)
	 id_to_string(Id -> S)
	 string_to_fileid(S -> F)

'nonterm' file1(-> STRING)

  'rule' file1(-> S)
	 id(-> Id)
	 "/"
	 file1(-> S2)
	 id_to_string(Id -> S1)
	 prefix_path(S1, S2 -> S)

  'rule' file1(-> S)
	 id(-> Id)
	 id_to_string(Id -> S)

------------------------------------------------------------
-- Deal with "Time" according to timed RSL or not
------------------------------------------------------------

'nonterm' type_id_def(-> IDENT)

  'rule' type_id_def(-> Id)
	 id(-> Id) @(-> P)
	 [|
	   IsTimed()
	   Time_id -> Tid
	   eq(Id, Tid)
	   Puterror(P)
	   Putmsg("The type Time is predefined")
	   Putnl()
	 |]

	 
-------------------------------------------------------------
-- Dummy terminator: used to get a position at the end of an expression
-------------------------------------------------------------
'nonterm' dummy_term

   'rule' dummy_term:

-------------------------------------------------------------
-- Tokens
-------------------------------------------------------------
'token' id(-> IDENT)

-- 'token' comment

'token' int_lit(-> IDENT)

'token' real_lit(-> IDENT)

'token' text_lit(-> STRING)

'token' char_lit(-> CHAR)

'token' eofile

'token' nextunit

'token' filename(-> FILE_NAME)
