cmake_minimum_required(VERSION 3.22)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

 set(CMAKE_BUILD_TYPE Debug)
# Only set default build type if none specified
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif()
cmake_policy(SET CMP0144 NEW)
cmake_policy(SET CMP0167 NEW)

# ingnore deprecation warnings
add_compile_options(-Wno-deprecated-declarations)

# Only enable AddressSanitizer for Debug builds --> this helps finding memory issues 
if(CMAKE_BUILD_TYPE MATCHES "Debug")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=address -g")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fsanitize=address")
endif()

# Project name
project(DRFS_CG)

include_directories(${OpenMP_CXX_INCLUDE_DIRS})
link_libraries(${OpenMP_CXX_LIBRARIES})

# Threads 
find_package(Threads REQUIRED)

# CPLEX (for apple silicon)
set(CPLEX_DIR /Applications/CPLEX_Studio2211)
include_directories(${CPLEX_DIR}/cplex/include)
include_directories(${CPLEX_DIR}/concert/include)
link_directories(${CPLEX_DIR}/cplex/lib/arm64_osx/static_pic)
link_directories(${CPLEX_DIR}/concert/lib/arm64_osx/static_pic)

# Add any include file 
include_directories(${PROJECT_SOURCE_DIR}/include)

# Add all .cpp files in src folder to the executable
file(GLOB_RECURSE SRC_FILES "src/*.cpp")

# Add excutionable
add_executable(DRFS_CG ${SRC_FILES})

# Link libraries to executable 
target_link_libraries(DRFS_CG ${OpenMP_CXX_LIBRARIES})
target_link_libraries(DRFS_CG Threads::Threads)
target_link_libraries(DRFS_CG ilocplex cplex concert pthread m)

# Set compiler flags 
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")

# For inellisense config 
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)



# Enable verbose linking
#set(CMAKE_VERBOSE_MAKEFILE ON)