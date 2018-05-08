cmake_minimum_required(VERSION 2.8)

option(QTGUI "QTGUI" OFF)
option(GCOV "GCOV" OFF)

IF (WIN32)
    # set stuff for windows
    find_library(WSOCK32_LIBRARY wsock32)
    find_library(WS2_32_LIBRARY ws2_32)
	  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} /W4 /WX")
ELSE()
    # set stuff for other systems
    IF(APPLE)
        set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -std=c11 -O2 -Werror")
        set(COMPILE_DEFINITIONS -Werror)
    ELSE()
        set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -std=c11 -O2 -pthread -Werror")
        set(COMPILE_DEFINITIONS -Werror)
        set(CMAKE_EXE_LINKER_FLAGS "-pthread")
    ENDIF()
ENDIF()

if (GCOV)
message(STATUS "using GCOV")
set(CMAKE_C_FLAGS "-std=c11 -fprofile-arcs -ftest-coverage -g -O0 -pthread -Wall -Werror")
endif(GCOV)

add_subdirectory(core-tis-test)

if(QTGUI)
message(STATUS "build qt gui -- use -DQTGUI=OFF (default) to disable")
add_subdirectory(qt-gui)
else()
message(STATUS "use -DQTGUI=ON to build qt gui")
endif(QTGUI)
