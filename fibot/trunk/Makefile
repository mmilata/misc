include config.mk

SRC = main.cpp state.cpp generator.cpp
OBJ = ${SRC:.cpp=.o}
DEMODIR = demo

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

demo1: qid0
	@cp qid0 ${DEMODIR}/strategie/tym35
	@(cd ${DEMODIR}; ./play demo1)

demo2: qid0
	@cp qid0 ${DEMODIR}/strategie/tym35
	@(cd ${DEMODIR}; ./play demo2)

demo3: qid0
	@cp qid0 ${DEMODIR}/strategie/tym35
	@(cd ${DEMODIR}; ./play demo3)

.PHONY: all options clean
