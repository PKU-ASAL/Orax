add_check_c_cxx_flag("-fPIC")


set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
add_definitions(
  -DAFL_CC_PATH="/usr/local/bin/afl-clang-lto"
  -DAFL_BIN_PATH="/usr/local/bin/afl-fuzz"
  )

# orax
add_library(wrafl OBJECT wrafl.cpp wrafl.h)
add_library(aufbv-wrafl OBJECT aufbv-wrafl.cpp aufbv-wrafl.h ${CMAKE_SOURCE_DIR}/fsolver/include/fsolve.h)

# orax
target_link_libraries(wrafl PUBLIC ${Boost_LIBRARIES})
target_link_libraries(aufbv-wrafl PUBLIC ${Boost_LIBRARIES})
if (NOT TARGET fsolve)
  message(FATAL_ERROR "fsolve not found")
endif()
target_link_libraries(aufbv-wrafl PUBLIC fsolve)