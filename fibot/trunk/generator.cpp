#include "error.h"
#include "state.h"
#include "generator.h"
#include <vector>
#include <algorithm>

using namespace std;

Generator::Generator(const State &st) : initstate(st)
{
	curBot = initstate.fBots[initstate.tah_hrace].begin();
	endBot = initstate.fBots[initstate.tah_hrace].end();
	curAction = aNOOP;
}

/*
 * pokud se vraci action == aNOOP je hodnota moved nedefinovana
 * pokud se bot hybal, v moved je jeho puvodni pozice
 */
bool Generator::next(State &state, botPos &moved, Action &action)
{
	state = initstate;
	if(state.tah_hrace == PRVNI){
		state.tah_hrace = DRUHY;
	}else{
		state.tah_hrace = PRVNI;
		state.zbyva_kol--;
	}

	//nastane jen pri prvnim volani
	if(curAction == aNOOP){
		action = aNOOP;
		curAction = aSever;
		return true;
	}

	//jsme na konci?
	if(curBot == endBot)
		return false;

	action = curAction;
	moved = *curBot;
	//snizit pocet zbyvajicich tahu?

	if(curAction == aBoom){
		int x = curBot->first.x;
		int y = curBot->first.y;

		state.set(x,y,ftEmpty);
		state.killBot(Pos(x,y));

		for(int nx = x+1;
		    nx < state.columns && state.get(nx,y) != ftWall;
		    nx++){
			state.set(nx,y,ftEmpty);
			state.killBot(Pos(nx,y));
		}

		for(int nx = x-1;
		    nx >= 0 && state.get(nx,y) != ftWall;
		    nx--){
			state.set(nx,y,ftEmpty);
			state.killBot(Pos(nx,y));
		}

		for(int ny = y+1;
		    ny < state.rows && state.get(x,ny) != ftWall;
		    ny++){
			state.set(x,ny,ftEmpty);
			state.killBot(Pos(x,ny));
		}

		for(int ny = y-1;
		    ny >= 0 && state.get(x,ny) != ftWall;
		    ny--){
			state.set(x,ny,ftEmpty);
			state.killBot(Pos(x,ny));
		}

		increment();
		return true;
	}

	Pos dest = state.getDestination(curBot->first, action);
	if(dest == curBot->first){
		increment();
		return next(state, moved, action);
	}
	state.set(moved.first.x, moved.first.y, ftEmpty);
	state.set(dest.x, dest.y, (initstate.tah_hrace == initstate.nase_cislo ? ftOurBot : ftTheirBot));

	vector<botPos>::iterator it;
	for(it = state.fBots[initstate.tah_hrace].begin(); it != state.fBots[initstate.tah_hrace].end(); it++){
		if(*it == moved){
			it->first = dest;
		}
	}

	increment();
	return true;
}

void Generator::increment()
{
	switch(curAction){
		case aSever:
			curAction = aJih;
			break;
		case aJih:
			curAction = aZapad;
			break;
		case aZapad:
			curAction = aVychod;
			break;
		case aVychod:
			curAction = aBoom;
			break;
		case aBoom:
			curAction = aSever;
			curBot++;
			break;
		case aNOOP:
			throw Error("aNOOP in switch in Generator::increment()");
			break;
	}
}

