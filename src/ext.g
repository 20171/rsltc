-- RSL Type Checker
-- Copyright (C) 1998 UNU/IIST

-- raise@iist.unu.edu

-- This module defines the interface to the functions written in C

'module' ext

'export'
     CHAR

-- Module: idents
     string_to_id id_to_string Make_mk_name Make_from_name
     Make_to_name Make_disjointness_name Make_induction_name
     Char_to_string Text_to_string Text_to_c_string Len Int_to_string
     Axiom_name_to_string C_id_to_string SML_id_to_string
     PVS_id_to_string
     Contains_E
     Is_primed
     Compare_substring
     Compare_string
     -- convert a RSL real into two INTs
     Convert_Real
     Remove_Prime

-- Module: files
     InsertContextFile PrintDependencies Check_module_name Reopen
     Find_comm Skip_string Move_spaces Block_to_str
     Line_to_str Change_sp PpLength BaseName EqualFileId
     string_to_fileid strings_to_fileid fileid_to_string prefix_path
     PrintFileId
     OpenGraphFile WriteGraphString WriteGraphId CloseGraphFile
     OpenHFile WriteHString WriteHId WriteHText WriteHChar CloseHFile
     OpenJavaFile WriteJavaString WriteJavaId WriteJavaText WriteJavaInt
     WriteJavaChar CloseJavaFile
     OpenCcFile WriteCcString WriteCcId WriteCcText WriteCcChar CloseCcFile
     WriteHCcString
     OpenSMLFile CloseOutputFile WriteFile WritelnFile 
     OpenPVSFile OpenSALFile OpenM4File OpenFDRFile OpenLTLFile OpenRTTFile
     WriteFFile WriteF2File WriteF3File WriteF4File WriteF5File
     WriteFFileInt SetFileIndentSpace IndentFile UnindentFile 
     SetIndentHere PushSetIndentHere PushIndent PopIndent
     WriteIndntFile
     NewSeqNum
     Char_to_int
     GetFString GetF2String
     Char_to_SML_char String_to_SML_string Pos_to_string
     Char_to_PVS_char
     String_to_PVS_string
     Get_env_string Dos_to_Unix

-- Module: errmsg
       HasErrors Putmsg Putchar Putstr Putint Puterror Putwarning Putnl ErrorUsage Error
       Putcc Putstdmsg Putstdnl Print_poly

-- Module: pos
   DefaultPos PrintPos GetColAtPos PosAsString PosDecrypt
   LinePosAsString PrefixWithPos
   PrefixAsComment
   -- Added for SAL translation:
   IncreaseCol   

-- Module: ccgen
   Make_concatenation Concatenate3 Concatenate PruneQuote

-- Module: main
   PrintVersion
   IsTimed  CcWanted AllCcWanted PpWanted DepsWanted GraphWanted
   CPPWanted VisualCPP JavaWanted SMLWanted PVSWanted PccWanted
   SQLWanted SALWanted FDRWanted RTTWanted

'use' ast

'type' CHAR

----------------------------------------------------------------------------
-- Module: idents
----------------------------------------------------------------------------


-- convert a RSL real into a PVS number and a Divisor
-- ex. 3.14159 is: PVSNumber= 314159 and Divisor= 100000
--                    RSLReal -> PVSNumber, Divisor
'action' Convert_Real(IDENT   -> INT      , INT)
'action' string_to_id (STRING -> IDENT)
'action' id_to_string (IDENT -> STRING)
'action' Make_mk_name(STRING -> STRING)
'action' Make_from_name(STRING, STRING -> STRING)
'action' Make_to_name(STRING, STRING -> STRING)
'action' Make_disjointness_name(STRING -> STRING)
'action' Make_induction_name(STRING -> STRING)
'action' Char_to_string(CHAR -> STRING)
'action' Text_to_string(STRING -> STRING)
'action' Text_to_c_string(STRING -> STRING)
'action' Len(STRING -> INT)
'action' Int_to_string(INT -> STRING)
'action' Axiom_name_to_string(IDENT -> STRING)
'action' C_id_to_string(IDENT -> STRING)
'action' SML_id_to_string(IDENT -> STRING)
'action' PVS_id_to_string(IDENT -> STRING)
'action' FDR_id_to_string(IDENT -> STRING)
'condition' Contains_E(STRING)
-- Added for SAL
'condition' Is_primed(STRING)
'action' Remove_Prime(STRING -> STRING)
--Added for FDR translator
'condition' Compare_substring(STRING,STRING,INT)
'condition' Compare_string(STRING,STRING)
----------------------------------------------------------------------------
-- Module: files
----------------------------------------------------------------------------

'action' InsertContextFile (FILE_NAME)
'action' PrintDependencies
'action' Check_module_name(POS, STRING)
'action' Reopen()
'action' Find_comm( -> INT)
'action' Skip_string(STRING -> INT)
'action' Move_spaces(STRING -> STRING)
'action' Block_to_str( -> STRING,INT,INT,INT)
'action' Line_to_str( -> STRING,INT,INT)
'action' Change_sp(STRING -> STRING)
'action' PpLength(-> INT)
'action' BaseName(FILE_NAME -> IDENT)
'condition' EqualFileId(IDENT, IDENT)
'action' string_to_fileid(STRING -> FILE_NAME)
'action' strings_to_fileid(STRING, STRING -> FILE_NAME)
'action' fileid_to_string(FILE_NAME -> STRING)
'action' prefix_path(STRING, STRING -> STRING)
'action' PrintFileId(FILE_NAME)
'action' OpenGraphFile(IDENT -> STRING)
'action' WriteGraphString(STRING)
'action' WriteGraphId(IDENT)
'action' CloseGraphFile
'action' OpenHFile(IDENT -> STRING)
'action' WriteHString(STRING)
'action' WriteHId(IDENT)
'action' WriteHText(STRING)
'action' WriteHChar(CHAR)
'action' CloseHFile
'action' OpenJavaFile(IDENT -> STRING)
'action' WriteJavaString(STRING)
'action' WriteJavaId(IDENT)
'action' WriteJavaText(STRING)
'action' WriteJavaChar(CHAR)
'action' WriteJavaInt(INT)
'action' CloseJavaFile
'action' OpenCcFile(IDENT -> STRING)
'action' WriteCcString(STRING)
'action' WriteCcId(IDENT)
'action' WriteCcText(STRING)
'action' WriteCcChar(CHAR)
'action' CloseCcFile
'action' WriteHCcString(STRING)
'action' OpenSMLFile(IDENT -> STRING)
'action' OpenPVSFile(IDENT -> STRING)
'action' OpenSALFile(IDENT -> STRING)
'action' OpenM4File(IDENT -> STRING)
'action' OpenFDRFile(IDENT -> STRING)
'action' OpenLTLFile(IDENT -> STRING)
'action' OpenRTTFile(IDENT -> STRING)
'action' CloseOutputFile
'action' WriteFile(STRING)
'action' WritelnFile(INT)
'action' WriteIndntFile(INT)
'action' WriteFFile(STRING, STRING)
'action' WriteF2File(STRING, STRING, STRING)
'action' WriteF3File(STRING, STRING, STRING, STRING)
'action' WriteF4File(STRING, STRING, STRING, STRING, STRING)
'action' WriteF5File(STRING, STRING, STRING, STRING, STRING, STRING)
'action' WriteFFileInt(STRING, INT)
'action' SetFileIndentSpace(INT)
'action' IndentFile
'action' UnindentFile
'action' SetIndentHere(INT)
'action' PushSetIndentHere(INT)
'action' PushIndent
'action' PopIndent
'action' NewSeqNum(-> INT)
'action' Char_to_int(CHAR -> INT)
'action' GetFString(STRING, STRING -> STRING)
'action' GetF2String(STRING, STRING, STRING -> STRING)
'action' Char_to_SML_char(CHAR -> STRING)
'action' String_to_SML_string(STRING -> STRING)
'action' Char_to_PVS_char(CHAR -> STRING)
'action' String_to_PVS_string(STRING -> STRING)
'action' Char_to_FDR_char(CHAR -> STRING)
'action' String_to_FDR_string(STRING -> STRING)
'action' Pos_to_string(POS -> STRING)
'action' Get_env_string(STRING, STRING -> STRING)
'action' Dos_to_Unix(STRING -> STRING)

----------------------------------------------------------------------------
-- Module: errmsg
----------------------------------------------------------------------------

'condition' HasErrors

'action' Putmsg(STRING)
'action' Putchar(CHAR)
'action' Putstr(STRING)
'action' Putint(INT)
'action' Puterror(POS)
'action' Putwarning(POS)
'action' Putnl

'action' ErrorUsage (STRING)
'action' Error(STRING, POS)

'action' Putcc(POS)
'action' Putstdmsg(STRING)
'action' Putstdnl

'action' Print_poly(INT)

----------------------------------------------------------------------------
-- Module: pos
----------------------------------------------------------------------------

'action' DefaultPos(-> POS)
'action' PrintPos(POS)
'action' GetColAtPos(POS -> INT)
'action' PosAsString(POS -> STRING)
'action' PosDecrypt(POS -> STRING, STRING, STRING)
'action' LinePosAsString(POS -> STRING)
'action' PrefixWithPos(POS, STRING -> STRING)
'action' PrefixAsComment(STRING -> STRING)
-- Added for SAL:
'action' IncreaseCol(POS -> POS)
----------------------------------------------------------------------------
-- Module: ccgen
----------------------------------------------------------------------------

'action' Make_concatenation(STRING, INT -> STRING)
'action' Concatenate3(STRING, STRING, STRING -> STRING)
'action' Concatenate(STRING, STRING -> STRING)
'action' PruneQuote(STRING -> STRING)

----------------------------------------------------------------------------
-- Module: main
----------------------------------------------------------------------------

'action' PrintVersion
'condition' IsTimed
'condition' CcWanted
'condition' AllCcWanted
'condition' PpWanted
'condition' DepsWanted
'condition' GraphWanted
'condition' CPPWanted
'condition' VisualCPP
'condition' JavaWanted
'condition' SMLWanted
'condition' PVSWanted
'condition' PccWanted
'condition' SQLWanted
'condition' SALWanted
'condition' FDRWanted
'condition' RTTWanted
'end'
