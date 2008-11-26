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

int
main(int argc, char **argv)
{
	char filename[256];

	signal(SIGALRM, sighandler);
	alarm(2);

	try {
		if(argc != 2)
			throw Error("chybny pocet argumentu programu");
		strcpy(filename, argv[1]);
		strcat(filename, "/state");
		State initstate(filename);
		initstate.dump();

		Generator g(initstate, true);
		State next(initstate);
		botPos b;
		Action a;
		while(g.next(next,b,a)){
			cerr << "---" << endl;
			cerr << "Akce: " << strAction(a,b) << endl;
			next.dump();
		}

		/*
		// samotny kod na vypocet pozice
		State newState;
		botPost newBot, bestBot;
		Action newAction, bestAction(aNOOP);
		Generator generator(initstate);
		double newScore, bestScore = -1.0;

		while (generator.next(newState, newBot, newAction)) {
			newScore = newState.getScore(newState.fOurBots, fTheirFlag);
			
			if (newScore < 0)
				continue; // neplatna pozice;
			if (newScore > bestScore) {
				bestScore = newScore;
				bestBot = newBot;
				bestAction = newAction;
			}
		}

		if (bestAction == aNOOP) {
			cout << "-" << endl;
		}
		else {
			char bot = bestBot->second;
			char cmd;

			switch (newAction) {
				case aBoom:
					cmd = 'D';
					break;
				case aServer:
					cmd = 'S';
					break;
				case aVychod:
					cmd = 'V';
					break;
				case aJih:
					cmd = 'J';
					break;
				case aZapad:
					cmd = 'Z';
					break;
				default:
					throw new Error("Neznama action");
			}

			cout << bot << " " << cmd << endl;
		}
		*/
	}
	catch (exception &e) {
		cerr << "Nastala chyba: " << e.what() << endl << flush;
		return EXIT_FAILURE;
	}

	return EXIT_SUCCESS;
}
/* vim: set noexpandtab: */
