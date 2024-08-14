cmake_minimum_required(VERSION 3.14)
project(cminify LANGUAGES C CXX)

add_executable(cminify "")
set(DEFAULT_CMAKE_BUILD_TYPE Release)
set_property(TARGET cminify PROPERTY CXX_STANDARD 17)
set_property(TARGET cminify PROPERTY CXX_STANDARD_REQUIRED ON)
set_property(TARGET cminify PROPERTY CXX_EXTENSIONS OFF)

find_package(Clang REQUIRED)
find_package(LLVM REQUIRED)

if(CLANG_LINK_CLANG_DYLIB)
  target_link_libraries(cminify PRIVATE clang-cpp)
else()
  target_link_libraries(cminify PRIVATE
    clangIndex
    clangFormat
    clangTooling
    clangToolingInclusions
    clangToolingCore
    clangFrontend
    clangParse
    clangSerialization
    clangSema
    clangAST
    clangLex
    clangDriver
    clangBasic
  )
endif()

if(LLVM_LINK_LLVM_DYLIB)
  target_link_libraries(cminify PRIVATE LLVM)
else()
  target_link_libraries(cminify PRIVATE LLVMOption LLVMSupport)
  if(LLVM_VERSION_MAJOR GREATER_EQUAL 16)
    target_link_libraries(cminify PRIVATE LLVMTargetParser)
  endif()
endif()

if(NOT LLVM_ENABLE_RTTI)
  # releases.llvm.org libraries are compiled with -fno-rtti
  # The mismatch between lib{clang,LLVM}* and cminify can make libstdc++ std::make_shared return nullptr
  # _Sp_counted_ptr_inplace::_M_get_deleter
  if(MSVC)
    target_compile_options(cminify PRIVATE /GR-)
  else()
    target_compile_options(cminify PRIVATE -fno-rtti)
  endif()
endif()

target_sources(cminify PRIVATE main.cc)

foreach(include_dir ${LLVM_INCLUDE_DIRS} ${CLANG_INCLUDE_DIRS})
  get_filename_component(include_dir_realpath ${include_dir} REALPATH)
  # Don't add as SYSTEM if they are in CMAKE_CXX_IMPLICIT_INCLUDE_DIRECTORIES.
  # It would reorder the system search paths and cause issues with libstdc++'s
  # use of #include_next. See https://github.com/MaskRay/ccls/pull/417
  if(NOT "${include_dir_realpath}" IN_LIST CMAKE_CXX_IMPLICIT_INCLUDE_DIRECTORIES)
    target_include_directories(cminify SYSTEM PRIVATE ${include_dir})
  endif()
endforeach()

install(TARGETS cminify RUNTIME DESTINATION bin)
