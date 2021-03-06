#ifndef FB_GENERATOR_H
#define FB_GENERATOR_H

#include "state.h"

class Generator {
public:
	Generator(const State &init);
	bool next(State &state, char &moved, Action &action);

	std::map<Pos, char>::const_iterator curBot;
	std::map<Pos, char>::const_iterator endBot;
	Action curAction;
	State initstate;
private:
	void increment(void);
};

#endif
