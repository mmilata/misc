#include "error.h"
#include "state.h"
#include "generator.h"
#include <vector>
#include <algorithm>

using namespace std;

static void deletebot(State &st, int x, int y);

Generator::Generator(State &st, bool ourTurn) : ourTurn(ourTurn), initstate(st)
{
	if(ourTurn){
		curBot = initstate.fOurBots.begin();
		endBot = initstate.fOurBots.end();
	}else{
		curBot = initstate.fTheirBots.begin();
		endBot = initstate.fTheirBots.end();
	}
	curAction = aNOOP;
}

/*
 * pokud se vraci action == aNOOP je hodnota moved nedefinovana
 * pokud se bot hybal, v moved je jeho puvodni pozice
 */
bool Generator::next(State &state, botPos &moved, Action &action)
{
	state = initstate;
	if(state.tah_hrace == 1){
		state.tah_hrace = 2;
	}else{
		state.tah_hrace = 1;
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
		int i=1;
		state.set(x,y,ftEmpty);
		deletebot(state,x,y);
		while(x+i < state.columns && state.get(x+i,y)!=ftWall){
			if(state.get(x+i,y) == ftOurBot || state.get(x+i,y) == ftTheirBot){
				state.set(x+i,y,ftEmpty);
				deletebot(state, x+i, y);
			}
			i++;
		}
		i=1;
		while(x-i >= 0 && state.get(x-i,y)!=ftWall){
			if(state.get(x-i,y) == ftOurBot || state.get(x-i,y) == ftTheirBot){
				state.set(x-i,y,ftEmpty);
				deletebot(state, x-i, y);
			}
			i++;
		}
		i=1;
		while(y+i < state.rows && state.get(x,y+i)!=ftWall){
			if(state.get(x,y+i) == ftOurBot || state.get(x,y+i) == ftTheirBot){
				state.set(x,y+i,ftEmpty);
				deletebot(state, x, y+i);
			}
			i++;
		}
		i=1;
		while(y-i >= 0 && state.get(x,y-i)!=ftWall){
			if(state.get(x,y-i) == ftOurBot || state.get(x,y-i) == ftTheirBot){
				state.set(x,y-i,ftEmpty);
				deletebot(state, x, y-i);
			}
			i++;
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
	state.set(dest.x, dest.y, (ourTurn ? ftOurBot : ftTheirBot));

	if(ourTurn){
		for(vector<botPos>::iterator it = state.fOurBots.begin(); it != state.fOurBots.end(); it++){
			if(*it == moved){
				it->first = dest;
			}
		}
	}else{
		for(vector<botPos>::iterator it = state.fTheirBots.begin(); it != state.fTheirBots.end(); it++){
			if(*it == moved){
				it->first = dest;
			}
		}
	}

	increment();
	return true;
}

void deletebot(State &st, int x, int y)
{
	for(vector<botPos>::iterator it = st.fOurBots.begin(); it != st.fOurBots.end(); it++){
		if(it->first.x == x && it->first.y == y){
			st.fOurBots.erase(it);
			break;
		}
	}

	for(vector<botPos>::iterator it = st.fTheirBots.begin(); it != st.fTheirBots.end(); it++){
		if(it->first.x == x&& it->first.y == y){
			st.fTheirBots.erase(it);
			break;
		}
	}
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

