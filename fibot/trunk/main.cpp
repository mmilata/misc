#include "state.h"
#include "error.h"
#include <iostream>
#include <fstream>
#include <stdlib.h>

using namespace std;

static void run();

/*
State*
loadState(void)
{
	int sirka, vyska, zbyvatahu, hracnatahu;
	int flag1s, flag1r, flag2s, flag2r;
	char square;

	ifstream statefile("state");

	statefile >> sirka >> vyska >> zbyvatahu >> hracnatahu;
	statefile >> flag1s >> flag1r >> flag2s >> flag2r;

	cout << "vyska: "<< vyska << endl;
	cout << "sirka: "<< sirka << endl;

	for(int i=0; i<vyska; i++){
		for(int j=0; j<sirka; j++){
			statefile >> square;
			cout << square;
		}
		cout << endl;
	}

	return new State();
}*/

void run()
{
}

int
main(int argc, char **argv)
{
	(void)argc; (void)argv;
	State test("state");
	test.dump();
	try {
    Pos dst = test.getDestination(Pos(2,2), 'S');
    cout << dst.x << dst.y << endl;
		run();
	}
	catch (exception &e) {
		cerr << "Nastala chyba: " << e.what() << endl << flush;
		return EXIT_FAILURE;
	}

	return EXIT_SUCCESS;
}

