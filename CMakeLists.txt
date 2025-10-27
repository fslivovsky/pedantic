cmake_minimum_required(VERSION 3.12)
project(DQBF_Solver)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Add cadical_interface as subdirectory
add_subdirectory(cadical-interface)

# Add CLI11 for command-line argument parsing
include(FetchContent)
FetchContent_Declare(cli11_project
    URL https://github.com/CLIUtils/CLI11/archive/refs/tags/v2.4.1.tar.gz
)
FetchContent_MakeAvailable(cli11_project)

# Add main library
add_library(dqbf_lib
    src/counter.hpp
    src/dqcir_parser.hpp
    src/dqcir_parser.cpp
    src/dqbf_solver.hpp
    src/dqbf_solver.cpp
)

target_include_directories(dqbf_lib PUBLIC 
    ${CMAKE_CURRENT_SOURCE_DIR}/src
    ${CMAKE_CURRENT_SOURCE_DIR}/cadical-interface/include
)

target_link_libraries(dqbf_lib PUBLIC cadical_solver)

# Add executable
add_executable(dqbf_solver src/dqbf_solver_main.cpp)
target_link_libraries(dqbf_solver PRIVATE dqbf_lib CLI11::CLI11)

# Enable testing (optional)
enable_testing()
