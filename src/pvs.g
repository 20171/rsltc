-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module is the main module for
-- the RSL to PVS translator
-- It calls all the other modules

'module' pvs


'use' ast print ext env objects values types pp cc sml
      pvs_ast          -- PVS Abstract Syntax
      pvs_aux          -- Auxiliary Actions
      pvs_col_sort     -- Collects and Sorts the Declareds (define before use)
      pvs_gen_ast      -- Generates PVS Abstract Syntax Tree
      pvs_gen_code     -- Generates PVS code


'export' PVS_init  -- init and open PVS output file
	 Process_Global_Scheme
	 Process_Global_Object
	 Process_Global_Theory
	 Process_Theory
	 Process_Scheme
	 Process_Object
	 Close_PVS_file
	 Trans_Class_expr
	 Process_Decls
	 Gen_PVS_Theory
	 Gen_PVS_End_Theory
	 IsCurrentTheory
	 IsCurrentObject
	 Out_Importings


--------------------------------------------------
-- Action naming conventions
--------------------------------------------------
-- in general troughout the translator:

-- Gen_ are actions that generate an structure from another, most
-- probably a PVS abstract syntax tree structure.

-- Out_ are actions that generate PVS code.

-- Insert_ are actions used for inserting an element in a structure (list).

-- Conc_ are actions used for concatenating two structures (lists).

-- Collect_ or Search_ are sweeps to look for particular structures.

-- Process_ are actions normally used as a first level before Gen_
-- or sweeps.

-- An s or an S is normally added to a name, including TYPEs, to
-- indicate that is a repetition of a more simple structure in the
-- case of TYPEs, or that is an action that treats a complex structure.



--------------------------------------------------
-- variables
--------------------------------------------------

'var' Filename_pvs               : STRING

'var' Current_theory		 : IDENT

'var' Current_object		 : OPT_OBJECT_ID

--------------------------------------------------
-- Actions
--------------------------------------------------


--------------------------------------------------
'action' PVS_init(LIB_MODULE)

  'rule' PVS_init(M)
	 Init_PVS_file
	 -- Initialize variable TheoryIndex
	 Init_TheoryIndex
	 Init_PVS_vars
	 InitTheoryIdMap
	 (|
	   (| where(M -> scheme(_, _, _, _)) ||
	      where(M -> object(_, _, _, _))
	   |)
	   SetTopNotTheory
	 ||
	   SetTopIsTheory -- theory or development relation
	 |)
	 Putnl()


--------------------------------------------------
'action' Init_PVS_vars

  'rule' Init_PVS_vars:
	 -- Initialize variable TotalDeclareds
	 Init_TotalDeclareds
	 Init_Indexes


--------------------------------------------------
'action' Init_PVS_file

  'rule' Init_PVS_file:
         Module_name -> S	-- in env.g (STRING)
         string_to_id(S -> Id)  -- in idents.c
--         OpenPVSFile(Id -> F)  -- in files.c
--         Filename_pvs <- F
         SetFileIndentSpace(4)  -- in files.c


--------------------------------------------------

'action' Process_Global_Scheme(IDENT, FILE_NAMES, OBJECT_DEFS, CLASS)

  'rule' Process_Global_Scheme(Ident, Context, Params, ClassExpr):
         (|
           HasErrors()
           Putmsg("Errors found, so PVS translation cannot be generated")
           Putnl()
         ||
           eq(Params, nil)
	   -- translate parameterless global schemes for theories
	   -- in case they appear as the class in a class scope
	   -- expression, which can then just use IMPORTING 
	   TopIsTheory
	   SetNotTheory  -- this module is not a theory
           Putmsg("Translating ")
	   Print_id(Ident)
	   Putmsg(" ... ")
	   Putnl()
           OpenPVSFile(Ident -> F)  -- in files.c
           Filename_pvs <- F

	   Globals -> ModuleEnv
	   Process_Context(Context, ModuleEnv, nil -> Idents)
	   Process_embedded_objects(ClassExpr, Idents -> Idents1)
	   Gen_PVS_Theory(Ident)
	   Out_Importings(Idents1)

	   Current_object <- nil
	   Trans_Class_expr(ClassExpr)

	   Putmsg("Finished translating ")
	   Print_id(Ident)
	   Putnl()
	   Gen_PVS_End_Theory(Ident)
           Close_PVS_file
         ||
           -- do nothing.  Parameterised schemes translated when instantiated.
         |)


--------------------------------------------------
'action' Process_Scheme(IDENT, FILE_NAMES, POS, OBJECT_DEFS, CLASS)	-- level 1

  'rule' Process_Scheme(Ident, Context, Pos, Params, ClassExpr):
         (|
           HasErrors()
           Putmsg("Errors found, so PVS translation cannot be generated")
           Putnl()
	 ||
	   SetNotTheory  -- is not a theory
           Putmsg("Translating ")
	   Print_id(Ident)
	   Putmsg(" ... ")
	   Putnl()
           OpenPVSFile(Ident -> F)  -- in files.c
           Filename_pvs <- F

	   Globals -> ModuleEnv

	   Process_Context(Context, ModuleEnv, nil -> Idents)
	   Process_embedded_object_defs(Params, nil, nil, Idents -> Idents1)
	   Process_embedded_objects(ClassExpr, Idents1 -> Idents2)
	   Gen_PVS_Theory(Ident)
	   Out_Importings(Idents2)

	   Current_object <- nil
	   Trans_Class_expr(ClassExpr)

	   Putmsg("Finished translating ")
	   Print_id(Ident)
	   Putnl()
	   Gen_PVS_End_Theory(Ident)
           Close_PVS_file
         |)



--------------------------------------------------
'action' Process_Global_Object(IDENT, FILE_NAMES, Object_id, CLASS)	-- level 1

  'rule' Process_Global_Object(Ident, Context, Objectid, ClassExpr):
         (|
           HasErrors()
           Putmsg("Errors found, so PVS translation cannot be generated")
           Putnl()
         ||
           Objectid'Params -> nil
--Putmsg("------------------------------------")
--Putnl()
--Putmsg("PVS Process_Global_Object, no params")
--Putnl()
	   SetNotTheory  -- is not a theory
           Putmsg("Translating ")
	   Print_id(Ident)
	   Putmsg(" ... ")
	   Putnl()
           OpenPVSFile(Ident -> F)  -- in files.c
           Filename_pvs <- F
	   AddTheory(Objectid -> Id)
	   Gen_PVS_Theory(Id)

	   Globals -> ModuleEnv

	   Process_Context(Context, ModuleEnv, nil -> Idents)
	   Process_embedded_objects(ClassExpr, Idents -> Idents1)
	   Out_Importings(Idents1)

	   Current_object <- object_id(Objectid) 
	   Trans_Class_expr(ClassExpr)
	   Current_object <- nil 

	   Putmsg("Finished translating ")
	   Print_id(Ident)
	   Putnl()
	   Gen_PVS_End_Theory(Id)
           Close_PVS_file
         ||
           Objectid'Pos -> Pos
	   Puterror(Pos)
	   Putmsg("object arrays not supported")
	   Putnl()
         |)


--------------------------------------------------
'action' Process_Global_Theory(IDENT, FILE_NAMES, CLASS)	-- level 1

  'rule' Process_Global_Theory(Ident, Context, ClassExpr):
         (|
           HasErrors()
           Putmsg("Errors found, so PVS translation cannot be generated")
           Putnl()
         ||
/*
Putmsg("------------------")
Putnl()
Putmsg("PVS Process_Global_Theory")
Putnl()
*/
	   SetIsTheory  -- is a theory
           Putmsg("Translating ")
	   Print_id(Ident)
	   Putmsg(" ... ")
	   Putnl()
           OpenPVSFile(Ident -> F)  -- in files.c
           Filename_pvs <- F
	   Globals -> ModuleEnv
	   Process_Context(Context, ModuleEnv, nil -> Idents)
	   Process_Class_in_Theory(ClassExpr, Ident, Idents)

	   Putmsg("Finished translating ")
	   Print_id(Ident)
	   Putnl()
           Close_PVS_file
	 |)


--------------------------------------------------
'action' Process_Theory(IDENT, FILE_NAMES, CLASS)	-- level 1

  'rule' Process_Theory(Ident, Context, ClassExpr):
         (|
           HasErrors()
           Putmsg("Errors found, so PVS translation cannot be generated")
           Putnl()
         ||
/*
Putmsg("------------------")
Putnl()
Putmsg("PVS Process_Theory")
Putnl()
*/
	   SetIsTheory  -- is a theory
           Putmsg("Translating ")
	   Print_id(Ident)
	   Putmsg(" ... ")
	   Putnl()
           OpenPVSFile(Ident -> F)  -- in files.c
           Filename_pvs <- F
	   Globals -> ModuleEnv
	   Process_Context(Context, ModuleEnv, nil -> Idents)
	   Process_Class_in_Theory(ClassExpr, Ident, Idents)
	   Putmsg("Finished translating ")
	   Print_id(Ident)
	   Putnl()
           Close_PVS_file
	 |)


--------------------------------------------------
'action' Process_Object(IDENT, FILE_NAMES, CLASS)

  'rule' Process_Object(Ident, Context, ClassExpr):
         (|
           HasErrors()
           Putmsg("Errors found, so PVS translation cannot be generated")
           Putnl()
         ||
--Putmsg("------------------")
--Putnl()
--Putmsg("PVS Process_Object")
--Putnl()
	   SetNotTheory  -- is not a theory
           Putmsg("Translating ")
	   Print_id(Ident)
	   Putmsg(" ... ")
	   Putnl()
           OpenPVSFile(Ident -> F)  -- in files.c
           Filename_pvs <- F

	   Globals -> ModuleEnv

	   Process_Context(Context, ModuleEnv, nil -> Idents)
	   Process_embedded_objects(ClassExpr, Idents -> Idents1)
	   Gen_PVS_Theory(Ident)
	   Out_Importings(Idents1)

	   DefaultPos(-> P)
	   New_object_id(P, Ident -> I)
	   Current_object <- object_id(I)
	   Trans_Class_expr(ClassExpr)
	   Current_object <- nil

	   Putmsg("Finished translating ")
	   Print_id(Ident)
	   Putnl()
	   Gen_PVS_End_Theory(Ident)
           Close_PVS_file
         |)

--------------------------------------------------
'action' Process_embedded_objects(CLASS, IDENTS -> IDENTS)

  'rule' Process_embedded_objects(basic(DS), Idents -> Idents1):
	 Process_embedded_object_decls(DS, Idents -> Idents1)

  'rule' Process_embedded_objects(extend(C1, C2), Idents -> Idents1):
	 In_left
	 Process_embedded_objects(C1, Idents -> Idents2)
	 Left_right
	 Process_embedded_objects(C2, Idents2 -> Idents1)
	 Out_right

  'rule' Process_embedded_objects(hide(_, C), Idents -> Idents1):
	 Process_embedded_objects(C, Idents -> Idents1)

  'rule' Process_embedded_objects(rename(_, C), Idents -> Idents1):
	 Process_embedded_objects(C, Idents -> Idents1)

  'rule' Process_embedded_objects(with(_, _, C), Idents -> Idents1):
	 Process_embedded_objects(C, Idents -> Idents1)

  'rule' Process_embedded_objects(instantiation(name(_, id_op(Id)), Objs),
							Idents -> Idents2):
	 Get_id_of_scheme(Id -> scheme_id(Schemeid))
         Schemeid'With -> With 
         Set_current_with(With)
         Schemeid'Class -> ClassExpr
	 Schemeid'Context -> Context
	 Globals -> ModuleEnv
	 Process_Context(Context, ModuleEnv, Idents -> Idents1)
	 Process_embedded_objects(ClassExpr, Idents1 -> Idents2)

  'rule' Process_embedded_objects(nil, Idents -> Idents)

'action' Process_embedded_object_decls(DECLS, IDENTS -> IDENTS)

  'rule' Process_embedded_object_decls(DS, Idents -> Idents1):
	 Extract_objects_in_declares(DS -> Defs)     
	 Process_embedded_object_defs(Defs, nil, nil, Idents -> Idents1) 


'action' Process_embedded_object_defs(OBJECT_DEFS, OBJECT_DEFS, FOUND, IDENTS -> IDENTS)

  'rule' Process_embedded_object_defs(list(D, DS), Waiting, Found, Idents -> Idents1):
	 where(D -> odef(P, Id, Params, Class))
	 (|
	   Collect_object_idents(Class, nil -> Ids)
	   (| Uses_defs(Ids, DS) || Uses_defs(Ids, Waiting) |)
	   Process_embedded_object_defs(DS, list(D, Waiting), Found, Idents -> Idents1)
	 ||
	   (|
	     Get_current_modules(-> ME)
	     Lookup_object_in_module(Id, ME -> object_id(I))
	   ||
	     Parameters -> PARMS
	     Lookup_object_in_module(Id, PARMS -> object_id(I))
	   |)
	   Current -> C
	   I'Param_env -> PCE
	   I'Env -> CE
	   Current <- current_env(CE,current_env(PCE, C))
	   Extend_paths -> Paths
	   Extend_paths <- list(nil, list(nil, Paths))
	   Process_embedded_objects(Class, Idents -> Idents2)
	   AddTheory(I -> Id1)
	   Gen_PVS_Theory(Id1)
	   Out_Importings(Idents2)
	   Current_object <- object_id(I)
	   Trans_Class_expr(Class)
	   Current_object <- nil
	   Gen_PVS_End_Theory(Id1)
	   Current <- C
	   Extend_paths <- Paths
	   where(IDENTS'list(Id1, Idents) -> Idents3)
	   Process_embedded_object_defs(DS, Waiting, found, Idents3 -> Idents1)
	 |)

  'rule' Process_embedded_object_defs(nil, nil, _, Idents -> Idents):
	   
  'rule' Process_embedded_object_defs(nil, Waiting, Found, Idents -> Idents1):
	 where(Waiting -> list(odef(P, Id, _, _), _))
	 (|
	   eq(Found, nil)
	   Puterror(P)
	   Putmsg("Object ")
	   Print_id(Id)
	   Putmsg(" seems to be involved in mutual recursion.")
	   Putnl()
	   where(Idents -> Idents1)
	 ||
	   Process_embedded_object_defs(Waiting, nil, nil, Idents -> Idents1)
	 |)


--------------------------------------------------
'action' Gen_PVS_Theory(IDENT)

  'rule' Gen_PVS_Theory(Id):
         id_to_string(Id -> S)  -- in idents.c
         WriteFFile("%s : THEORY", S)
         WritelnFile(2)
         WriteFile("BEGIN")
         WritelnFile(2)
	 Current_theory <- Id
-- Putmsg("Starting theory ")
-- Print_id(Id)
-- Putnl
	 Init_Importings
	 Init_PVS_vars

'condition' IsCurrentTheory(IDENT)

  'rule' IsCurrentTheory(Id):
	 Current_theory -> CId
	 eq(Id, CId)

'condition' IsCurrentObject(Object_id)

  'rule' IsCurrentObject(I):
	 Current_object -> object_id(OI)
	 eq(I, OI)


--------------------------------------------------
'action' Gen_PVS_End_Theory(IDENT)

  'rule' Gen_PVS_End_Theory(Id):
         id_to_string(Id -> S)  -- in idents.c
         WriteFFile("END %s", S)
         WritelnFile(3)


--------------------------------------------------
'action' Process_Decls(DECLS)

  'rule' Process_Decls(DeclsRSL):

--Putmsg("      BEGIN Process_Decls, in Gen_Declareds")
--Putnl()
	 Gen_Declareds(DeclsRSL, nil -> Declareds)
--Putmsg("            Process_Decls, out Gen_Declareds")
--Putnl()
--Putmsg("                           in  Sort_Declareds")
--Putnl()

--Putmsg("************************Declareds")
--Putnl()


--print("************************************")
--PrintTotalDeclareds("TotalDeclareds before Sort_Declareds")
--PrintTotalDeclaredsCard("Before Sort_Declareds")
	Sort_Declareds(Declareds,      -- ToDo 
                       nil,            -- Waiting
                       nil,            -- Done
                       nil             -- Found
                       -> SortedDeclareds)
--PrintTotalDeclaredsCard("After Sort_Declareds")
--print("***********************************")
--PrintTotalDeclareds("TotalDeclareds after Sort_Declareds")


--PrintDeclareds(SortedDeclareds)
--print(SortedDeclareds)

--Putmsg("            Process_Decls, out Sort_Declareds") 
--Putnl()
--Putmsg("                           in  Gen_PVS_ast")
--Putnl()
	 Init_Var_Gen_Code
	 Gen_PVS_ast(SortedDeclareds, nil -> TheoryElements)

--Putmsg("            Process_Decls, out Gen_PVS_ast") 
--Putnl()
--Putmsg("                           in  Gen_PVS_Code")
--Putnl()

	 Gen_PVS_Code(TheoryElements)

--Putmsg("      END   Process_Decls, out Gen_PVS_Code")
--Putnl()





--------------------------------------------------
'action' Close_PVS_file

  'rule' Close_PVS_file:
	 Init_TotalDeclareds -- else items declared in scheme
			     -- will be found declared when
			     -- scheme instantiated in object
         CloseOutputFile  -- in files.c
         Filename_pvs -> F
         Putmsg("PVS output is in file ")  -- in ext.g
         Putmsg(F)  -- in ext.g
         Putnl  -- in ext.g


--------------------------------------------------
'action' Trans_Class_expr(CLASS)

  'rule' Trans_Class_expr(basic(Decls)):
--print("---- BEGIN Class_expr basic")
         Resolve_class(basic(Decls))		-- in cc.g
--print("---- Class_expr basic out Resolve_class")
--print("--- Decls ---")
--print(Decls)
	 Process_Decls(Decls)
--print("---- END Class_expr basic")


  'rule' Trans_Class_expr(extend(Class1, Class2)):
--print("---- BEGIN Trans_Class_expr extend")
	 In_left
	 Trans_Class_expr(Class1)
--print("     Trans_Class_expr extend 1")
	 Left_right
	 Trans_Class_expr(Class2)
--print("     Trans_Class_expr extend 2")
	 Out_right
--print("---- END Trans_Class_expr extend")

  'rule' Trans_Class_expr(instantiation(name(Pos,
                                             id_op(Id)),
                                             Objs)):
--print("---- BEGIN Class_expr instantiation")

	 Get_id_of_scheme(Id -> scheme_id(Schemeid))
         Schemeid'With -> With 
         Set_current_with(With)
         Schemeid'Class -> ClassExpr
	 Schemeid'Context -> Context
	 Globals -> ModuleEnv
	 Process_Context(Context, ModuleEnv, nil -> Idents)
	 Out_Importings(Idents)
	 Resolve_class(ClassExpr)
	 Trans_Class_expr(ClassExpr)
--print("---- END Class_expr instantiation")

  'rule' Trans_Class_expr(hide(Defnds, ClassExpr)):
	 [|
	   where(Defnds -> list(Def, _))
	   (|
             where(Def -> def_name(Pos, _))
           ||
             where(Def -> disamb(Pos, _, _))
           |)
	   Putwarning(Pos)
	   Putmsg("hidings are ignored")
	   Putnl()
	 |]
	 Trans_Class_expr(ClassExpr)

  'rule' Trans_Class_expr(rename(Renames, ClassExpr)):
	 [|
	   where(Renames -> list(rename(Def, _), _))
	   (|
             where(Def -> def_name(Pos, _))
           ||
             where(Def -> disamb(Pos, _, _))
           |) 
	   Putwarning(Pos)
	   Putmsg("renamings are ignored")
	   Putnl()
	 |]
	 Trans_Class_expr(ClassExpr)

  'rule' Trans_Class_expr(with(_, _, ClassExpr)):
--	 WriteFile("Class_expr with")
--	 WritelnFile(2)
	 Trans_Class_expr(ClassExpr)

  'rule' Trans_Class_expr(nil):


--------------------------------------------------
'action' Out_Importings(IDENTS)

  'rule' Out_Importings(Idents):
	 Add_Importings(Idents -> Idents1)
	 Out_Importings1(Idents1)

'action' Out_Importings1(IDENTS)

  'rule' Out_Importings1(list(Ident, IdentsTail)):
	 WriteFile("  IMPORTING ")
	 id_to_string(Ident -> IdString)
	 WriteFile(IdString)
	 WriteFile(";")
	 WritelnFile(2)
	 Out_Importings1(IdentsTail)

  'rule' Out_Importings1(nil):


--------------------------------------------------
'action' Process_Context(FILE_NAMES, MODULE_ENV, IDENTS -> IDENTS)

  'rule' Process_Context(list(FileName, FileNamesTail),
                        ModuleEnv, IdentsIn -> IdentsOut):
	 BaseName(FileName -> Ident)
	 (|
	   Is_Id_scheme(Ident, ModuleEnv)
	   where(IdentsIn -> Idents1)
	 ||
	   Insert_Ident(Ident, IdentsIn -> Idents1)
	 |)
	 Process_Context(FileNamesTail, ModuleEnv, Idents1 -> IdentsOut)

  'rule' Process_Context(nil, ModuleEnv, Idents -> Idents):


--------------------------------------------------
'condition' Is_Id_scheme(IDENT, MODULE_ENV)

  'rule' Is_Id_scheme(Id, object_env(I2, ME)):
         Is_Id_scheme(Id, ME)

  'rule' Is_Id_scheme(Id, theory_env(I2, ME)):
         Is_Id_scheme(Id, ME)

  'rule' Is_Id_scheme(Id, scheme_env(I2, ME)):
         I2'Ident -> Id2
         eq(Id, Id2)

  'rule' Is_Id_scheme(Id, scheme_env(I2, ME)):
         Is_Id_scheme(Id, ME)



--------------------------------------------------
'action' Process_Class_in_Theory(CLASS, IDENT, IDENTS)

  'rule' Process_Class_in_Theory(basic(DeclsRSL), Ident, Idents):
         Resolve_class(basic(DeclsRSL))		-- in cc.g
	 Gen_Declareds(DeclsRSL, nil -> Declareds)
	 Init_Var_Gen_Code
	 Process_Theory_Declareds(Declareds, Ident, Idents)


  'rule' Process_Class_in_Theory(_,_,_):
	 Putmsg("no axioms in theory")
	 Putnl()

--------------------------------------------------
'action' Process_Theory_Declareds(DECLAREDS, IDENT, IDENTS)

  'rule' Process_Theory_Declareds(list(lemma_item(Axiomid), DeclsTail),
							    Ident, Idents):
	 Axiomid'Axiom -> Ax
	 (|
	   where(Ax -> env_class_scope(_,Class,CE,_))
	   Current -> C
	   Current <- current_env(CE, C)
	   Extend_paths -> Paths
	   Extend_paths <- list(nil, list(nil, Paths))
	   (|
	     where(Class -> instantiation(Name, nil))
	     where(Idents -> Idents0)
	   ||
	     Process_embedded_objects(Class, Idents -> Idents0)
	     WriteFile("%-------------------")
	     WritelnFile(1)
	   |)
	   Current <- C
	   Extend_paths <- Paths
	 ||
	   where(Idents -> Idents0)
	 |)
         Gen_PVS_Theory(Ident)
	 Out_Importings(Idents0)
	 -- include lemmas which are class scope exprs with the same
	 -- (non-parameterised) scheme
	 -- or are not class scope expressions
	 -- in the same PVS theory
	 (|
	   where(Ax -> env_class_scope(_,Class,_,_))
	   (|
	     where(Class -> instantiation(Name, nil))
	     where(Name -> name(_, id_op(Id)))
	     Collect_same_theory(ident(Id), DeclsTail -> Same, Next)
	   ||
	     where(DECLAREDS'nil -> Same)
	     where(DeclsTail -> Next)
	   |)
	 ||
	   Collect_same_theory(nil, DeclsTail -> Same, Next)
	 |)
	 Prepend_axiom(Axiomid, Same -> Same1)
	 Gen_PVS_ast(Same1, nil -> TheoryElements)
	 Gen_PVS_Code(TheoryElements)
	 Gen_PVS_End_Theory(Ident)
	 WritelnFile(2)
	 -- if some are left, use the name of the first
	 -- (or a generated name) as the name of the next theory
	 [|
	   where(Next -> list(lemma_item(Axiomid2), Tail))
	   Axiomid'Ident -> OptIdent
	   (|
	     where(OptIdent -> ident(Ident2))
	   ||
	     Gen_Theory_Name("Theory_" -> IdSt)
	     string_to_id(IdSt -> Ident2)
	   |)
	   Process_Theory_Declareds(Next, Ident2, Idents)
	 |]	 

'action' Collect_same_theory(OPT_IDENT, DECLAREDS -> DECLAREDS, DECLAREDS)

  'rule' Collect_same_theory(OptId, DS:list(lemma_item(Axiomid), Tail)
							-> Same, Next):
	 Axiomid'Axiom -> Ax
	 (|
	   where(Ax -> env_class_scope(_,Class,_,_))
	   (|
	     where(Class -> instantiation(Name, nil))
	     where(Name -> name(_, id_op(Id)))
	     (|
	       where(OptId -> ident(Id1))
	       (|
	         eq(Id, Id1) -- same schemes: continue
	         Collect_same_theory(ident(Id), Tail -> Same1, Next)
		 Prepend_axiom(Axiomid, Same1 -> Same)
	       || -- different schemes: stop
	         where(DECLAREDS'nil -> Same)
	         where(DS -> Next)
	       |)
	     || -- no current scheme: continue with new scheme
	       Collect_same_theory(ident(Id), Tail -> Same1, Next)
	       where(DECLAREDS'list(lemma_item(Axiomid), Same1) -> Same)
	     |)
	   || -- scheme with parameters: stop
	     where(DECLAREDS'nil -> Same)
	     where(DS -> Next)
	   |)
	 ||  -- not a class scope expr: continue
	   Collect_same_theory(OptId, Tail -> Same1, Next)
	   where(DECLAREDS'list(lemma_item(Axiomid), Same1) -> Same)
	 |)

  'rule' Collect_same_theory(_, nil -> nil, nil):

'action' Prepend_axiom(Axiom_id, DECLAREDS -> DECLAREDS)

-- If the axiom is an env_class_scope 
-- with a conjuction of cc_exprs, then split it.
-- This separates implementation conditions into separate axioms

  'rule' Prepend_axiom(I, Declareds -> list(lemma_item(I1), Declareds1)):
	 I'Axiom -> env_class_scope(P, CL, CE, V)
	 where(V -> ax_infix(_, V1:cc_expr(_, _, Oid, _), and, V2, _))
	 New_axiom_id(P, Oid -> I1)
	 I1'Axiom <- V1
	 I'Axiom <- env_class_scope(P, CL, CE, V2)
	 Prepend_axiom(I, Declareds -> Declareds1)

  'rule' Prepend_axiom(I, Declareds -> list(lemma_item(I), Declareds)):
	 -- If axiom has no name, try to improve on it
	 [|
	   I'Ident -> nil
	   I'Axiom -> env_class_scope(_, _, _, V)
	   where(V -> cc_expr(_, _, ident(Id), _))
	   I'Ident <- ident(Id)
	 |]
