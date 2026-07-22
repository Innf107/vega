cmake_minimum_required(VERSION 3.16)
project(VegaShadowStackPlugin C CXX)


add_compile_options("-Wall" "-Werror=return-type" "-fPIC")


set(LLVM_LINK_LLVM_DYLIB ON)

find_package(LLVM REQUIRED CONFIG)
list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
include(AddLLVM)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${LLVM_CXX_FLAGS}")

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})

llvm_map_components_to_libnames(llvm_libs Core Support IRReader Passes Target Analysis)

add_library(VegaShadowStackPlugin src/VegaShadowStackPlugin.cpp)

# target_link_libraries(VegaShadowStackPlugin PUBLIC ${llvm_libs})
