'module' fdr


'use' ast print ext env objects values types pp print cc cpp pvs_gen_code

      fdr_ast          -- fdr Abstract Syntax
      fdr_gen_ast      -- Generates fdr Abstract Syntax Tree
      fdr_gen_code     -- Generates fdr code


'export' FDR_init  -- init and open fdr output file
	 FDR_Translate_Scheme



--------------------------------------------------
-- variables
--------------------------------------------------

--'var' Filename_fdr               : STRING



--------------------------------------------------
-- Actions
--------------------------------------------------

--------------------------------------------------
'action' FDR_init

  'rule' FDR_init
	 Init_FDR_file
	 -- Initialize variable TheoryIndex


--------------------------------------------------
'action' Init_FDR_file

  'rule' Init_FDR_file:
         Module_name -> S	-- in env.g (STRING)
         string_to_id(S -> Id)  -- in idents.c
         
        -- OpenFDRFile(Id -> _)  -- in files.c

-- Ana comments        WriteFile("--rsl to fdr translation")
-- Ana comments        WritelnFile(2)
         SetFileIndentSpace(4)  -- in files.c
-- Ana comments       CloseOutputFile()


--------------------------------------------------
'action' Close_FDR_file

  'rule' Close_FDR_file:
         CloseOutputFile()

'action' FDR_Translate_Scheme(IDENT, FILE_NAMES, POS, OBJECT_DEFS, CLASS)

  'rule' FDR_Translate_Scheme(Id, FNs, P,Parms, Class):
         [|
	   ne(Parms, nil)
	   Puterror(P)
	   Putmsg("Parameters of the scheme cannot be translated")
	   Putnl
	 |] 
         [|
	   ne(FNs, nil)
	   Puterror(P)
	   Putmsg("Context files cannot be translated")
	   Putnl
	 |]   
	 Resolve_class(Class)
         Pass_Class_To_Decls(Class ->Decls)


         -- Ana: Translate all the LTL properties
         Init_Trans_LTL(Decls,Decls)


         -- Ana: Here it is not the LTL properties translation
         OpenFDRFile(Id -> _)  -- in files.c


         Translate_Decls_To_Fdr_scripts(Decls ->Fdr_scripts)
         GenCode_Fdr_scripts(Fdr_scripts)
         Close_FDR_file  -- Ana adds 

        
         --  Close_FDR_file  -- Ana comment
	 Putnl()
	

'action' Pass_Class_To_Decls(CLASS ->DECLS)

  'rule' Pass_Class_To_Decls(basic(Decls) ->Decls1):
         where(Decls ->Decls1)

  'rule' Pass_Class_To_Decls(hide(Defineds,basic(Decls)) ->Decls1):
	 Putmsg("Hide definitions will be ignored")
	 Putnl()
	 where(Decls ->Decls1)

  'rule' Pass_Class_To_Decls(Class ->nil):
	 Putmsg("Class cannot be translated")





