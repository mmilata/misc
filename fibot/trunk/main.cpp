#include "state.h"
#include "error.h"
#include <iostream>
#include <fstream>
#include <cstring>
#include <stdlib.h>

using namespace std;

static void run(State &state);

void run(State &state)
{
	
}

int
main(int argc, char **argv)
{
	char filename[256];

	try {
		if(argc != 2)
			throw Error("chybny pocet argumentu programu");
		strcpy(filename, argv[1]);
		strcat(filename, "/state");
		State initstate(filename);
		initstate.dump();

		Pos dst = initstate.getDestination(Pos(3,4), aSever);
		cout << dst.x << dst.y << endl;
		run(initstate);
	}
	catch (exception &e) {
		cerr << "Nastala chyba: " << e.what() << endl << flush;
		return EXIT_FAILURE;
	}

	return EXIT_SUCCESS;
}
/* vim: set noexpandtab: */
