#include "scorefun.h"
#include "generator.h"
#include "state.h"

#include <cmath>
#include <vector>

using namespace std;

double averageFlagDistance(const State &st)
{
	vector<botPos>::const_iterator i;
	double ret_val = 0;
	for (i = st.fOurBots.begin(); i != st.fOurBots.end(); i++) {
		ret_val += st.fTheirFlag.distance(i->first);
	}

	return 100.0 - (ret_val/st.fOurBots.size());
}

double testWhatever(const State &st)
{
	//rozdil v poctu botu
	//kolik tahu jsme prumerne u vlajky
	//a nepritel
	//skore na zacatku by melo byt 0, pokud je mapa symetricka ... ?
	//pokud stojime na vlajce INFINITY
	//pokud stoji nepritel, -INF
}

double minimax(const State &st, ScoreFun scf, int depth)
{
	double bestScore = -INFINITY;

	if(depth==0)
		return scf(st);

	Generator generator(st,true);
	double newScore;
	State newState(st);
	botPos newBot;
	Action newAction;

	while(generator.next(newState, newBot, newAction)){
		newScore = -minimax(newState, scf, depth-1);

		if(newScore > bestScore){
			bestScore = newScore;
		}
	}

	return bestScore;
}
