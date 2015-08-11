CMAKE_MINIMUM_REQUIRED( VERSION 2.8.11 )

# diable in-source builds
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)
set(CMAKE_DISABLE_SOURCE_CHANGES  ON)

if ("${CMAKE_SOURCE_DIR}" STREQUAL "${CMAKE_BINARY_DIR}")
  message(SEND_ERROR "In-source builds are not allowed.")
endif ()

PROJECT ( rsltc )

###############################################################
# Handling for other libraries and tools
###############################################################
FIND_PACKAGE ( BISON )
FIND_PACKAGE ( FLEX ) 

###############################################################
# Included folders
###############################################################
include_directories(
    "${CMAKE_SOURCE_DIR}/src")
###############################################################
# Add subdirectories to be built.
###############################################################
add_subdirectory( cpp )
add_subdirectory( doc )
add_subdirectory( latex )
add_subdirectory( lisp )
add_subdirectory( pvs )
add_subdirectory( sal )
add_subdirectory( sml )
add_subdirectory( src )
add_subdirectory( ug )
add_subdirectory( UML2RSL )

###############################################################
# Build installer targets
###############################################################
if(CMAKE_INSTALL_PREFIX_INITIALIZED_TO_DEFAULT)
    set(CMAKE_INSTALL_PREFIX "/opt/rsltc" CACHE PATH "Install path prefix." FORCE)
endif(CMAKE_INSTALL_PREFIX_INITIALIZED_TO_DEFAULT)
MESSAGE(STATUS "Installation path: ${CMAKE_INSTALL_PREFIX}")

INSTALL(FILES LICENSE DESTINATION . )
INSTALL(FILES README.orig DESTINATION . )
INSTALL(FILES rslcomp DESTINATION bin )


