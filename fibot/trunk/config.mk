INCS = -I. -I/usr/include 
LIBS = -lc

# flags
CXXFLAGS = -pedantic -Wall -Wextra -O -ggdb ${INCS} 
LDFLAGS = ${LIBS}

CXX = g++
