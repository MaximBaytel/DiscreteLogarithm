cmake_minimum_required(VERSION 3.5)

project(d_log LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_executable(d_log main.cpp)

target_compile_options(d_log PRIVATE -std=c++20 -Wall -Wextra -Werror )

include(GNUInstallDirs)
install(TARGETS d_log
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
    RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
)
