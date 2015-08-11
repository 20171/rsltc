FILE(GLOB T_FILES RELATIVE "${CMAKE_CURRENT_SOURCE_DIR}" "${CMAKE_CURRENT_SOURCE_DIR}/*.t" "${CMAKE_CURRENT_SOURCE_DIR}/*.b")
set(TOKENS)
FOREACH(tfileName ${T_FILES})
    # Generate output file name
    SET(outfile "${CMAKE_CURRENT_BINARY_DIR}/${tfileName}")

    # Custom command to do the processing
    ADD_CUSTOM_COMMAND(OUTPUT "${outfile}"
        COMMAND cp "${tfileName}" "${outfile}"
        COMMENT "Copy ${tfileName} to build folder"
        DEPENDS "${tfileName}"
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
        VERBATIM)

    # Finally remember the output file for dependencies
    SET(TOKENS ${TOKENS} "${outfile}")
ENDFOREACH(tfileName)

FILE(GLOB GENTLE_SOURCES RELATIVE "${CMAKE_CURRENT_SOURCE_DIR}" "${CMAKE_CURRENT_SOURCE_DIR}/*.g")

set(RSLTC_SOURCES
    ccgen.c
    errmsg.c
    files.c
    idents.c
    main.c
    pos.c
    strings.c
    ${GENTLE}/gentle/grts.o
)

# we will handle grammar.g separately, as it generates gen.* files
LIST(REMOVE_ITEM GENTLE_SOURCES grammar.g)
FOREACH(gfileName ${GENTLE_SOURCES})
    # MESSAGE(STATUS "Process file: ${gfileName}")
    # Generate output file name
    STRING(REGEX REPLACE ".g\$" ".c" cfileName "${gfileName}")
    SET(outfile "${CMAKE_CURRENT_BINARY_DIR}/${cfileName}")
    # MESSAGE(STATUS "Output file: ${outfile}")

    # Generate input file name
    SET(infile "${CMAKE_CURRENT_SOURCE_DIR}/${infileName}")

    # Custom command to do the processing
    ADD_CUSTOM_COMMAND(OUTPUT "${outfile}"
        COMMAND ${GENTLE}/gentle/gentle "${gfileName}"
        COMMAND mv "${cfileName}" "${outfile}"
        COMMENT "Generate C source files from ${gfileName}"
        DEPENDS "${gfileName}"
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
        VERBATIM)

    # Finally remember the output file for dependencies
    SET(RSLTC_SOURCES ${RSLTC_SOURCES} "${outfile}")
ENDFOREACH(gfileName)

# Setup a target to drive the conversion
ADD_CUSTOM_TARGET(GenerateGentleFiles ALL DEPENDS ${RSLTC_SOURCES})

# Custom command to do the processing
ADD_CUSTOM_COMMAND(OUTPUT 
    "${CMAKE_CURRENT_BINARY_DIR}/gen.tkn"
    "${CMAKE_CURRENT_BINARY_DIR}/gen.lit"
    "${CMAKE_CURRENT_BINARY_DIR}/gen.h"
    "${CMAKE_CURRENT_BINARY_DIR}/gen.y"
    "${CMAKE_CURRENT_BINARY_DIR}/grammar.c"
    COMMAND ${GENTLE}/gentle/gentle "grammar.g"
    COMMAND mv "gen.tkn" "${CMAKE_CURRENT_BINARY_DIR}/gen.tkn"
    COMMAND mv "gen.lit" "${CMAKE_CURRENT_BINARY_DIR}/gen.lit"
    COMMAND mv "gen.h" "${CMAKE_CURRENT_BINARY_DIR}/gen.h"
    COMMAND mv "gen.y" "${CMAKE_CURRENT_BINARY_DIR}/gen.y"
    COMMAND mv "grammar.c" "${CMAKE_CURRENT_BINARY_DIR}/grammar.c"
    COMMENT "Generate gen.* and grammar.c files"
    DEPENDS "grammar.g"
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    VERBATIM)
SET(RSLTC_SOURCES ${RSLTC_SOURCES} "${CMAKE_CURRENT_BINARY_DIR}/grammar.c")

ADD_CUSTOM_COMMAND(OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/gen.l"
        COMMAND ${GENTLE}/reflex/reflex
        DEPENDS ${TOKENS} ${RSLTC_SOURCES}
        COMMENT "Generate gen.l by Gentle's reflex"
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
        VERBATIM)

BISON_TARGET(rsltc_B "${CMAKE_CURRENT_BINARY_DIR}/gen.y" ${CMAKE_CURRENT_BINARY_DIR}/gen.tab.c)
FLEX_TARGET(rsltc_F "${CMAKE_CURRENT_BINARY_DIR}/gen.l" ${CMAKE_CURRENT_BINARY_DIR}/lex.yy.c)
ADD_FLEX_BISON_DEPENDENCY( rsltc_F rsltc_B )

add_executable(rsltc
    ${RSLTC_SOURCES}
    ${BISON_rsltc_B_OUTPUTS}
    ${FLEX_rsltc_F_OUTPUTS}
    )

INSTALL(FILES "${CMAKE_CURRENT_BINARY_DIR}/rsltc" DESTINATION bin
        PERMISSIONS OWNER_EXECUTE OWNER_WRITE OWNER_READ GROUP_EXECUTE GROUP_READ)
