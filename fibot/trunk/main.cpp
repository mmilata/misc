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

void sighandler(int unused)
{
	(void)unused;

	cerr << "timeout!\n";
	cout << "-" << endl;
	exit(EXIT_SUCCESS);
}

//vypise nasledniky
void vypisNasledniky(State initstate, ScoreFun scf)
{
	Generator g(initstate);
	State next(initstate);
	botPos b;
	Action a;
	while(g.next(next,b,a)){
		cerr << "---" << endl;
		cerr << "Akce: " << strAction(a,b) << endl;
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
	scf = testWhatever;

	try {
		if(argc < 2)
			throw Error("chybny pocet argumentu programu");
		strcpy(filename, argv[1]);
		strcat(filename, "/state");
		State initstate(filename);
		//initstate.dump();

		if(argc == 3){
			vypisNasledniky(initstate, scf);
			return EXIT_SUCCESS;
		}

		// samotny kod na vypocet pozice
		State newState(initstate);
		botPos newBot, bestBot;
		Action newAction, bestAction(aNOOP);
		Generator generator(initstate);
		double newScore, bestScore = -INFINITY;

		while(generator.next(newState, newBot, newAction)){
			//newScore = -minimax(newState, scf, DEPTH);
			//newScore = -scf(newState);
			newScore = -alphabeta(newState, scf, -INFINITY, INFINITY, DEPTH);

			if(newScore > bestScore){
				bestScore = newScore;
				bestBot = newBot;
				bestAction = newAction;
			}
		}

		//cerr << "bestscore: " << bestScore << endl;
		cout << strAction(bestAction, bestBot) << endl;
	}
	catch (exception &e) {
		cerr << "Nastala chyba: " << e.what() << endl << flush;
		return EXIT_FAILURE;
	}

	return EXIT_SUCCESS;
}
/* vim: set noexpandtab: */
