include config.mk

SRC = main.cpp state.cpp
OBJ = ${SRC:.cpp=.o}

all: options qid0

options:
	@echo build options:
	@echo "CXXFLAGS  = ${CXXFLAGS}"
	@echo "LDFLAGS   = ${LDFLAGS}"
	@echo "CXX       = ${CXX}"

.cpp.o:
	@echo CXX $<
	@${CXX} -c ${CXXFLAGS} $<

${OBJ}: config.mk

qid0: ${OBJ}
	@echo CXX -o $@
	@${CXX} -o $@ ${OBJ} ${LDFLAGS}

clean:
	@echo cleaning
	@rm -f qid0 ${OBJ}

.PHONY: all options clean
