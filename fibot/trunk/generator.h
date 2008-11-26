#ifndef FB_GENERATOR_H
#define FB_GENERATOR_H

#include "state.h"

class Generator {
public:
	Generator(const State &init, bool ourTurn);
	bool next(State &state, botPos &moved, Action &action);

	std::vector<botPos>::iterator curBot;
	std::vector<botPos>::iterator endBot;
	Action curAction;
	bool ourTurn;
	State initstate;
private:
	void increment(void);
};

#endif
