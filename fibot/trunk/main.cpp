#include "state.h"
#include "error.h"
#include "generator.h"
#include "scorefun.h"
#include <iostream>
#include <fstream>
#include <cstring>
#include <cmath>
#include <stdlib.h>
#include <signal.h>

#define DEPTH 5

using namespace std;

static void sighandler(int);

static Action bestAction(aNOOP);
//static Pos bestBot;
static char bestBot;
static State gstate;
static bool end = false;

void sighandler(int unused)
{
	(void)unused;
	cerr << "timeout!!" << endl;
	end = true;
}

//vypise nasledniky
void vypisNasledniky(State state, ScoreFun scf)
{
	Generator g(state);
	State next(state);
	char b;
	Action a;
	while(g.next(next,b,a)){
		cerr << "---" << endl;
		//cerr << "Akce: " << strAction(a, state.botName(b)) << endl;
		cerr << "Skore: " << scf(next) << endl;
		next.dump();
	}
}

int
main(int argc, char **argv)
{
	char filename[256];

	//bez prorerazvani je limitni hloubka asi tak 3
	signal(SIGALRM, sighandler);
	alarm(2);

	ScoreFun scf;
	//scf = nonsenseScore;
	scf = sensibleScore;
	if (getenv("YASF")) {
		cerr << "Pouzivam YASF" << endl;
		scf = yetAnotherScoreFunction;
	}

	try {
		if(argc < 2)
			throw Error("chybny pocet argumentu programu");
		strcpy(filename, argv[1]);
		strcat(filename, "/state");
		
		gstate = State(filename);
		//gstate.dump();

		if(argc == 3){
			vypisNasledniky(gstate, scf);
			return EXIT_SUCCESS;
		}

		// samotny kod na vypocet pozice
		State newState(gstate);
		char newBot;
		Action newAction;
		Generator generator(gstate);
		double newScore, bestScore = -INFINITY;

		while(generator.next(newState, newBot, newAction) && !end) {
			//newScore = -minimax(newState, scf, DEPTH);
			//newScore = -scf(newState);
			newScore = -alphabeta(newState, scf, -INFINITY, INFINITY, DEPTH);

			if(newScore > bestScore){
				bestScore = newScore;
				bestBot = newBot;
				bestAction = newAction;
			}
		}

		alarm(0);
		//cerr << "bestscore: " << bestScore << endl;
		//cout << strAction(bestAction, gstate.botName(bestBot)) << endl;
		cout << strAction(bestAction, bestBot) << endl;
	}
	catch (exception &e) {
		cerr << "Nastala chyba: " << e.what() << endl << flush;
		cout << "-" << endl;
		return EXIT_FAILURE;
	}

	delete gstate.distMap[0];
	delete gstate.distMap[1];

	return EXIT_SUCCESS;
}
/* vim: set noexpandtab: */
