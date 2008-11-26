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
bool Generator::next(State &state, Pos &moved, Action &action)
{
	state = initstate;
	// postup vysledneho stavu do dalsiho kola
	state.tah_hrace = !state.tah_hrace;
	if (!state.tah_hrace)
		state.zbyva_kol--;

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
	moved = curBot->first;
	//snizit pocet zbyvajicich tahu?


	if(curAction == aBoom){
		Pos p = curBot->first;
		Pos cur;
		/* zacatek */
		//spocitame kolik nepratel minus kolik pratel by zabil vybuch
		int deadCounter = -1; // ten co vybuchl

		state.killBot(p);
		
		for(cur = Pos(p.x+1, p.y); state.inMap(cur) && state.get(cur) != ftWall; cur.x += 1)
			if (state.get(cur) == ftBot) {
				deadCounter += state.isEnemy(cur) ? +1 : -1;
				state.killBot(cur);
			}
		for(cur = Pos(p.x, p.y+1); state.inMap(cur) && state.get(cur) != ftWall; cur.y += 1)
			if (state.get(cur) == ftBot) {
				deadCounter += state.isEnemy(cur) ? +1 : -1;
				state.killBot(cur);
			}

		for(cur = Pos(p.x-1, p.y); state.inMap(cur) && state.get(cur) != ftWall; cur.x -= 1)
			if (state.get(cur) == ftBot) {
				deadCounter += state.isEnemy(cur) ? +1 : -1;
				state.killBot(cur);
			}

		for(cur = Pos(p.x, p.y-1); state.inMap(cur) && state.get(cur) != ftWall; cur.y -= 1)
			if (state.get(cur) == ftBot) {
				deadCounter += state.isEnemy(cur) ? +1 : -1;
				state.killBot(cur);
			}

		if (deadCounter >= 0) {
			increment();
			return next(state, moved, action);
		}

		increment();
		return true;
	}

	Pos dest = state.getDestination(curBot->first, action);
	if(dest == curBot->first){
		increment();
		return next(state, moved, action);
	}
	state.set(moved, ftEmpty);
	state.set(dest, ftBot);

	state.fBots[initstate.tah_hrace][dest] = state.fBots[initstate.tah_hrace][moved];
	state.fBots[initstate.tah_hrace].erase(state.fBots[initstate.tah_hrace].find(moved));

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

