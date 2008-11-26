#ifndef FB_GENERATOR_H
#define FB_GENERATOR_H

#include "state.h"

class Generator {
public:
	Generator(const State &init);
	bool next(State &state, botPos &moved, Action &action);

	std::vector<botPos>::iterator curBot;
	std::vector<botPos>::iterator endBot;
	Action curAction;
	State initstate;
private:
	void increment(void);
};

#endif
