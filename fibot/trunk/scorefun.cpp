#include "scorefun.h"
#include "generator.h"
#include "state.h"

#include <cmath>
#include <vector>

using namespace std;

double averageFlagDistance(const State &st)
{
	int tahnul = st.tah_hrace;
	int na_tahu = 1-st.tah_hrace;
	bool flag = 1;

	vector<botPos>::const_iterator i;
	vector<botPos> bots = st.fBots[tahnul];

	double ret_val = 1000.0;
	for (i = bots.begin(); i != bots.end(); i++) {
		ret_val += st.fFlag[na_tahu].distance(i->first);
		if(flag)
			ret_val -= 1000.0;
	}

	return 100.0 - (ret_val/bots.size());
}

double testWhatever(const State &st)
{
	//rozdil v poctu botu
	//kolik tahu jsme prumerne u vlajky
	//a nepritel
	//skore na zacatku by melo vychazet 0, pokud je mapa symetricka ... ?
	//pokud stojime na vlajce INFINITY
	//pokud stoji nepritel, -INF
}

double nonsenseScore(const State &st)
{
	int tahnul = 1 - st.tah_hrace;
	int na_tahu = st.tah_hrace;

	vector<botPos>::const_iterator i;
	vector<botPos> bots = st.fBots[tahnul];

	double ret_val = 0;
	for (i = bots.begin(); i != bots.end(); i++){
		//ret_val += (st.rows - i->first.y);
		if(i->first == st.fFlag[PRVNI])
			ret_val += 100.0;
	}

	return ret_val;
}

double minimax(const State &st, ScoreFun scf, int depth)
{
	double bestScore = -INFINITY;

	//jeste by to chtelo osetrit vyhru/prohru

	if(depth==0 || st.endGame())
		return scf(st);

	Generator generator(st);
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
