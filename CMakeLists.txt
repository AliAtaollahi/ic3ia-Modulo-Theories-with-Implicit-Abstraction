cmake_minimum_required(VERSION 2.8)
project(ic3ia CXX)

# ------------------------ User options ------------------------
# Point this at your MathSAT unpacked directory (or pass at configure time).
set(MATHSAT_DIR "" CACHE PATH "Directory of MathSAT (root)")

# If you prefer to pass include/lib dirs directly, you still can:
set(MSAT_INCLUDE_DIR "" CACHE PATH "Include dir for MathSAT")
set(MSAT_LIB_DIR     "" CACHE PATH "Library dir for MathSAT")

option(BUILD_STATIC "Build a static executable" OFF)

# ------------------------ Defaults & flags ------------------------
# Default to Debug (so you get -g) unless user overrides
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Debug CACHE STRING
      "Build type (Debug, Release, RelWithDebInfo, MinSizeRel)" FORCE)
endif()

# C++ standard
add_definitions(-std=c++11)

# Enable PIC for shared/static mixing (except when forced static)
if(NOT BUILD_STATIC)
  add_definitions(-fPIC)
endif()

# Nice warnings
if(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
  add_definitions(-Wall -Wextra -Wno-unused-parameter)
endif()

# Per-config flags
set(CMAKE_CXX_FLAGS_DEBUG          "${CMAKE_CXX_FLAGS_DEBUG} -O0 -g")
set(CMAKE_CXX_FLAGS_RELEASE        "${CMAKE_CXX_FLAGS_RELEASE} -O3")

# Where to put build artifacts
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)

# ------------------------ MathSAT & deps ------------------------
# If MATHSAT_DIR is given, infer include/lib unless explicitly set
if(MATHSAT_DIR)
  if(NOT MSAT_INCLUDE_DIR)
    set(MSAT_INCLUDE_DIR "${MATHSAT_DIR}/include" CACHE PATH "" FORCE)
  endif()
  if(NOT MSAT_LIB_DIR)
    set(MSAT_LIB_DIR "${MATHSAT_DIR}/lib" CACHE PATH "" FORCE)
  endif()
endif()

# Locate libraries
find_library(mathsat NAMES mathsat PATHS "${MSAT_LIB_DIR}")
if(NOT mathsat)
  message(FATAL_ERROR "MathSAT not found. Set MATHSAT_DIR or MSAT_LIB_DIR.")
endif()

find_library(gmpxx NAMES gmpxx)
find_library(gmp   NAMES gmp)
if(NOT gmp OR NOT gmpxx)
  message(FATAL_ERROR "GMP/GMPXX not found (needed by MathSAT).")
endif()

# Include path for MathSAT headers
if(NOT MSAT_INCLUDE_DIR)
  message(FATAL_ERROR "MSAT_INCLUDE_DIR not set. Set MATHSAT_DIR or MSAT_INCLUDE_DIR.")
endif()
include_directories(. ${MSAT_INCLUDE_DIR})

# RPATH so the binary can find libmathsat at runtime from the given lib dir
# (you can skip this if you prefer setting LD_LIBRARY_PATH manually)
set(CMAKE_BUILD_WITH_INSTALL_RPATH ON)
set(CMAKE_INSTALL_RPATH "${MSAT_LIB_DIR}")
set(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)
# Also set build-time rpath for convenience:
set(CMAKE_BUILD_RPATH "${MSAT_LIB_DIR}")

# ------------------------ Sources ------------------------
set(SRCS
    utils.cpp
    ia.cpp
    ic3.cpp
    solver.cpp
    ts.cpp
    unroll.cpp
    live.cpp
    bmc.cpp
    ltl.cpp
    proof.cpp
    api.cpp
    ic3ia.cpp
    invred.cpp
)

# ------------------------ Targets ------------------------
add_library(ic3ia ${SRCS})

# Main binary (named "ic3ia")
add_executable(ic3ia_main main.cpp)
set_target_properties(ic3ia_main PROPERTIES OUTPUT_NAME ic3ia)
target_link_libraries(ic3ia_main ic3ia ${mathsat} ${gmpxx} ${gmp})

# horn2vmt tool
add_executable(horn2vmt horn2vmt.cpp)
target_link_libraries(horn2vmt ic3ia ${mathsat} ${gmpxx} ${gmp})

# proofchecker convenience copy
add_custom_target(proofchecker ALL
  COMMAND ${CMAKE_COMMAND} -E copy_if_different
          "${PROJECT_SOURCE_DIR}/proofchecker.py" proofchecker.py
  WORKING_DIRECTORY "${CMAKE_BINARY_DIR}"
)

# ------------------------ Optional SWIG/Python ------------------------
# Keep your original optional Python binding step (safe to ignore if missing)
find_package(PythonInterp)
find_package(SWIG)
find_package(PythonLibs)
if(SWIG_FOUND AND PYTHONLIBS_FOUND)
  add_custom_target(py
    COMMAND "${PYTHON_EXECUTABLE}"
            "${PROJECT_SOURCE_DIR}/python_api_setup.py"
            --msat-lib-dir="${MSAT_LIB_DIR}"
            --msat-include-dir="${MSAT_INCLUDE_DIR}"
            --swig-tool="${SWIG_EXECUTABLE}"
            --build-dir="${CMAKE_BINARY_DIR}"
    COMMENT "Building Python bindings"
    DEPENDS ic3ia
    WORKING_DIRECTORY "${CMAKE_BINARY_DIR}"
  )
endif()

# ------------------------ Static build knob ------------------------
if(BUILD_STATIC)
  # Ask the linker for static, if your system has static libs around
  set(CMAKE_EXE_LINKER_FLAGS "-static ${CMAKE_EXE_LINKER_FLAGS}")
  # Also drop PIC flags that some static toolchains dislike
  remove_definitions(-fPIC)
endif()
