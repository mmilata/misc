#include "state.h"
#include "error.h"
#include "generator.h"
#include <iostream>
#include <fstream>
#include <cstring>
#include <stdlib.h>
#include <signal.h>

using namespace std;

static void sighandler(int);

void sighandler(int unused)
{
	(void)unused;

	cout << "-" << endl;
	exit(EXIT_SUCCESS);
}

//vypise nasledniky
void vypisNasledniky(State initstate)
{
	Generator g(initstate, true);
	State next(initstate);
	botPos b;
	Action a;
	while(g.next(next,b,a)){
		cerr << "---" << endl;
		cerr << "Akce: " << strAction(a,b) << endl;
		cerr << "Skore: " << next.getScore(next.fOurBots, next.fTheirFlag) << endl;
		next.dump();
	}
}

int
main(int argc, char **argv)
{
	char filename[256];

	signal(SIGALRM, sighandler);
	alarm(2);

	try {
		if(argc < 2)
			throw Error("chybny pocet argumentu programu");
		strcpy(filename, argv[1]);
		strcat(filename, "/state");
		State initstate(filename);

		if(argc == 3){
			vypisNasledniky(initstate);
			return EXIT_SUCCESS;
		}

		// samotny kod na vypocet pozice
		State newState(initstate);
		botPos newBot, bestBot;
		Action newAction, bestAction(aNOOP);
		Generator generator(initstate,true);
		double newScore, bestScore = -1.0;

		while (generator.next(newState, newBot, newAction)) {
			newScore = newState.getScore(newState.fOurBots, newState.fTheirFlag);
			
			if (newScore < 0)
				continue; // neplatna pozice;
			if (newScore > bestScore) {
				bestScore = newScore;
				bestBot = newBot;
				bestAction = newAction;
			}
		}

		cout << strAction(bestAction, bestBot) << endl;
	}
	catch (exception &e) {
		cerr << "Nastala chyba: " << e.what() << endl << flush;
		return EXIT_FAILURE;
	}

	return EXIT_SUCCESS;
}
/* vim: set noexpandtab: */
