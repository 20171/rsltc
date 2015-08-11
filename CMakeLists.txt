CMAKE_MINIMUM_REQUIRED( VERSION 2.8.11 )

# diable in-source builds
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)
set(CMAKE_DISABLE_SOURCE_CHANGES  ON)

if ("${CMAKE_SOURCE_DIR}" STREQUAL "${CMAKE_BINARY_DIR}")
  message(SEND_ERROR "In-source builds are not allowed.")
endif ()

PROJECT ( rsltc )

###############################################################
# define make date and version number in flags
###############################################################
SET(MAJOR_VERSION "3")
SET(MINOR_VERSION "0")
SET(PATCH_VERSION "0")
set(VERSION_NUM "${MAJOR_VERSION}.${MINOR_VERSION}.${PATCH_VERSION}")
string(TIMESTAMP MAKE_DATE)
# ${MAKE_DATE} and ${VERSION_NUM} must be quoted
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -D RSLTC_MAKE_DATE='\"${MAKE_DATE}\"' -D RSLTC_VERSION='\"${VERSION_NUM}\"'") 

###############################################################
# Gentle path
###############################################################
set(GENTLE "/usr/share/gentle" CACHE STRING "Path to Gentle installation, default to /usr/share/gentle (-gentle)")

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
    set(CMAKE_INSTALL_PREFIX "/usr/share/rsltc" CACHE PATH "Install path prefix." FORCE)
endif(CMAKE_INSTALL_PREFIX_INITIALIZED_TO_DEFAULT)
MESSAGE(STATUS "Installation path: ${CMAKE_INSTALL_PREFIX}")

INSTALL(FILES LICENSE DESTINATION . )
INSTALL(FILES README.orig DESTINATION . )
INSTALL(FILES rslcomp DESTINATION bin 
        PERMISSIONS OWNER_EXECUTE OWNER_WRITE OWNER_READ GROUP_EXECUTE GROUP_READ)

###############################################################
# uninstall target
###############################################################
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake_uninstall.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
    IMMEDIATE @ONLY)

add_custom_target(uninstall
    COMMAND ${CMAKE_COMMAND} -P ${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake)

###############################################################
# make debian package
###############################################################
SET(CPACK_SET_DESTDIR "on")
SET(CPACK_PACKAGING_INSTALL_PREFIX "/usr")
SET(CPACK_GENERATOR "DEB")
 
SET(CPACK_PACKAGE_DESCRIPTION "RSL Type Checker (modified)")
SET(CPACK_PACKAGE_DESCRIPTION_SUMMARY "Type checker for RAISE Specification Language (RSL)")
SET(CPACK_PACKAGE_VENDOR "UNU/IIST")
SET(CPACK_PACKAGE_CONTACT "unknown@nowhere.com")
SET(CPACK_PACKAGE_VERSION_MAJOR "${MAJOR_VERSION}")
SET(CPACK_PACKAGE_VERSION_MINOR "${MINOR_VERSION}")
SET(CPACK_PACKAGE_VERSION_PATCH "${PATCH_VERSION}")
SET(CPACK_PACKAGE_FILE_NAME "${CMAKE_PROJECT_NAME}_${MAJOR_VERSION}.${MINOR_VERSION}.${CPACK_PACKAGE_VERSION_PATCH}")
SET(CPACK_SOURCE_PACKAGE_FILE_NAME "${CMAKE_PROJECT_NAME}_${MAJOR_VERSION}.${MINOR_VERSION}.${CPACK_PACKAGE_VERSION_PATCH}")
#SET(CPACK_DEBIAN_PACKAGE_DEPENDS " kate , dolphin ")

INCLUDE(CPack)
