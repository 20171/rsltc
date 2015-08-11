FILE(GLOB T_FILES RELATIVE "${CMAKE_CURRENT_SOURCE_DIR}" "${CMAKE_CURRENT_SOURCE_DIR}/*.t" "${CMAKE_CURRENT_SOURCE_DIR}/*.b")
set(TOKENS)
FOREACH(tfileName ${T_FILES})
    # Generate output file name
    SET(outfile "${CMAKE_CURRENT_BINARY_DIR}/${tfileName}")

    # Custom command to do the processing
    ADD_CUSTOM_COMMAND(OUTPUT "${outfile}"
        COMMAND cp -v "${tfileName}" "${outfile}"
        COMMENT "Copy token and block files"
        DEPENDS "${tfileName}"
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
        VERBATIM)

    # Finally remember the output file for dependencies
    SET(TOKENS ${TOKENS} "${outfile}")
ENDFOREACH(tfileName)

FILE(GLOB GENTLE_SOURCES RELATIVE "${CMAKE_CURRENT_SOURCE_DIR}" "${CMAKE_CURRENT_SOURCE_DIR}/*.g")

set(GENTLE_DIR "/usr/share/gentle")

set(RSLTC_SOURCES
    ccgen.c
    errmsg.c
    files.c
    idents.c
    main.c
    pos.c
    strings.c
    gen.h
    ${GENTLE_DIR}/gentle/grts.o
)

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
        COMMAND ${GENTLE_DIR}/gentle/gentle "${gfileName}"
        COMMAND mv -v "${cfileName}" "${outfile}"
        COMMENT "Generate Gentle files"
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
    COMMAND ${GENTLE_DIR}/gentle/gentle "grammar.g"
    COMMAND mv -v "gen.tkn" "${CMAKE_CURRENT_BINARY_DIR}/gen.tkn"
    COMMAND mv -v "gen.lit" "${CMAKE_CURRENT_BINARY_DIR}/gen.lit"
    COMMAND mv -v "gen.h" "${CMAKE_CURRENT_BINARY_DIR}/gen.h"
    COMMAND mv -v "gen.y" "${CMAKE_CURRENT_BINARY_DIR}/gen.y"
    COMMENT "Generate gen.* files"
    DEPENDS "grammar.g"
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    VERBATIM)

ADD_CUSTOM_COMMAND(OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/gen.l"
        COMMAND ${GENTLE_DIR}/reflex/reflex
        DEPENDS ${TOKENS} ${RSLTC_SOURCES}
        COMMENT "Generate Reflex files"
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
        VERBATIM)

BISON_TARGET(rsltc_B "${CMAKE_CURRENT_BINARY_DIR}/gen.y" ${CMAKE_CURRENT_BINARY_DIR}/gen.tab.c)
FLEX_TARGET(rsltc_F "${CMAKE_CURRENT_BINARY_DIR}/gen.l" ${CMAKE_CURRENT_BINARY_DIR}/lex.yy.c)
ADD_FLEX_BISON_DEPENDENCY( rsltc_F rsltc_B )

add_executable(rsltc 
    ${GENTLE_SOURCES}
    ${RSLTC_SOURCES}
    ${BISON_rsltc_B_OUTPUTS}
    ${FLEX_rsltc_F_OUTPUTS}
    )

INSTALL(FILES rsltc DESTINATION bin)
