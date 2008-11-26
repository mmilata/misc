#include "scorefun.h"
#include "generator.h"
#include "state.h"

#include <cmath>
#include <vector>

using namespace std;

static const double avgDistanceInfluence = 0.7; // jaky vliv na vzdalenost aktualniho hrace ma protihracova pozice

double averageFlagDistance(const State &st)
{
	int na_tahu = st.tah_hrace;
	int tahnul = 1-st.tah_hrace;
	bool flag = 1;
	double result = 0;

	vector<botPos>::const_iterator i;
	vector<botPos> bots = st.fBots[na_tahu];

	for (i = bots.begin(); i != bots.end(); i++)
		result += st.fFlag[tahnul].distance(i->first);

	bots = st.fBots[tahnul];
	for (i = bots.begin(); i != bots.end(); i++)
		result -= st.fFlag[na_tahu].distance(i->first) * avgDistanceInfluence;

	return 1.0 - (result / (st.fFlag[PRVNI].size() + st.fFlag[DRUHY].size()));
}

/*
double testWhatever(const State &st)
{
	int na_tahu = st.tah_hrace;
	int tahnul = 1 - na_tahu;
	vector<botPos> bots = st.fBots[na_tahu];

	if (st.endGame()) {
		if (st.vyhral() == na_tahu)
			return INFINITY;
		else
			return -INFINITY;
	}

	double ret_val = - (7*bots.size());

	return ret_val+averageFlagDistance(st);
	//preferovat ty stavy kdy jde nejaky bot po ceste ktera vede k vlajce, ne se jen tupe priblizuje nez narazi na zed
	//rozdil v poctu botu
	//kolik tahu jsme prumerne u vlajky
	//a nepritel
	//skore na zacatku by melo vychazet 0, pokud je mapa symetricka ... ?
}
*/

double sensibleScore(const State &st)
{
	bool flag = 1;
	int na_tahu = st.tah_hrace;
	int tahnul  = 1 - st.tah_hrace;
	double x = 1000.0;
	vector<botPos>::const_iterator i;
	vector<botPos> bots = st.fBots[na_tahu];
	for (i = bots.begin(); i != bots.end(); i++) {
		x += st.fFlag[tahnul].distance(i->first);
		if(flag)
			x -= 1000.0;
	}

	bots = st.fBots[tahnul];
	double mindist = INFINITY;
	for (i = bots.begin(); i != bots.end(); i++) {
		double t = st.fFlag[na_tahu].distance(i->first);

		if(t < mindist)
			mindist = t;
	}

	double ret_val = 0;
	int pocet_ohrozenych = 0;
	int kroku_k_vlajce = 0;
	//State temp = st;

	bots = st.fBots[na_tahu];
	//vyhra
	for (i = bots.begin(); i != bots.end(); i++){
		if(i->first == st.fFlag[tahnul])
			return INFINITY;
		if(st.isThreat(i->first, tahnul))
			pocet_ohrozenych++;
		//int distance = temp.countStepsTo(i->first, st.fFlag[tahnul], 10);
		/*
		if(distance > 0){
			ret_val += 500.0/distance;
		}
		*/
	}
	int pocet_nasich = bots.size();
	ret_val += 100.0 - (x/pocet_nasich);


	//prohra
	bots = st.fBots[tahnul];
	for (i = bots.begin(); i != bots.end(); i++){
		if(i->first == st.fFlag[na_tahu])
			return -INFINITY;
		//int distance = temp.countStepsTo(i->first, st.fFlag[na_tahu], 10);
		/*
		if(distance > 0){
			ret_val -= 600.0/distance;
		}
		*/
	}
	int pocet_nepratel = bots.size();

	//bonus za niceni, penalizace za ztraty
	ret_val += 20.0*(pocet_nasich - pocet_nepratel);
	//penalizace za ohrozene
	ret_val -= 15.0*pocet_ohrozenych;

	return ret_val;
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
