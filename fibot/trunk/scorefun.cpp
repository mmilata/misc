#include "scorefun.h"
#include "generator.h"
#include "state.h"

#include <cmath>
#include <vector>

using namespace std;

double averageFlagDistance(const State &st)
{
	int na_tahu = st.tah_hrace;
	int tahnul = 1-st.tah_hrace;
	bool flag = 1;

	vector<botPos>::const_iterator i;
	vector<botPos> bots = st.fBots[na_tahu];

	double ret_val = 1000.0;
	for (i = bots.begin(); i != bots.end(); i++) {
		ret_val += st.fFlag[tahnul].distance(i->first);
		if(flag)
			ret_val -= 1000.0;
	}

	bots = st.fBots[tahnul];
	double mindist = INFINITY;
	for (i = bots.begin(); i != bots.end(); i++) {
		double t = st.fFlag[na_tahu].distance(i->first);

		if(t < mindist)
			mindist = t;
	}

	return 100.0 - (ret_val/bots.size()) - (200.0/mindist);
}

double testWhatever(const State &st)
{
	int na_tahu = st.tah_hrace;
	int tahnul = 1 - na_tahu;

	if (st.endGame) {
		if (st.vyhral == na_tahu)
			return INFINITY;
		else
			return -INFINITY;

	double ret_val = 10.0*(st.fBots[na_tahu].size()) - (20*bots.size());

	return ret_val+averageFlagDistance(st);
	//preferovat ty stavy kdy jde nejaky bot po ceste ktera vede k vlajce, ne se jen tupe priblizuje nez narazi na zed
	//rozdil v poctu botu
	//kolik tahu jsme prumerne u vlajky
	//a nepritel
	//skore na zacatku by melo vychazet 0, pokud je mapa symetricka ... ?
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

double alphabeta(const State &st, ScoreFun scf, double alpha, double beta, int depth)
{
	if(depth==0 || st.endGame())
		return scf(st);

	Generator generator(st);
	double newScore = -INFINITY;
	State newState(st);
	botPos newBot;
	Action newAction;

	while(generator.next(newState, newBot, newAction)){

		newScore = -alphabeta(newState, scf, -beta, -alpha, depth-1);

		if(newScore > alpha){
			alpha = newScore;
		}

		if(beta <= alpha)
			break;
	}

	return alpha;

}
