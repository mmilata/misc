#ifndef FB_GENERATOR_H
#define FB_GENERATOR_H

#include "state.h"

class Generator {
public:
	Generator(const State &st, bool ourTurn);
	State* next() const;
	bool isLast(State &st) const;
};

#endif
