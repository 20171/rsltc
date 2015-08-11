set(SAL_FILES
    sal_make
    bool_cc_prelude
    cc_type_prelude
    int_cc_prelude
    int_prelude
    map_cc_prelude
    map_prelude
    set_cc_prelude
    set_prelude
    array_cc_prelude
)

INSTALL(FILES ${SAL_FILES} DESTINATION sal)
