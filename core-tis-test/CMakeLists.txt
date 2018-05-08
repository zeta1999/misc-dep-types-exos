cmake_minimum_required(VERSION 2.8)

project(TisTest)
file(GLOB CORE_APP_SRC "*.h" "*.c")
add_executable(${PROJECT_NAME} ${CORE_APP_SRC})

if(WIN32)
  target_link_libraries(${PROJECT_NAME} wsock32 ws2_32)
else()
  target_link_libraries(${PROJECT_NAME} -lm)
endif()
