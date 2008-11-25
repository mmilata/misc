#include "state.h"
#include "error.h"
#include <iostream>
#include <fstream>
#include <stdlib.h>

using namespace std;

static void run();

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
		Pos dst = test.getDestination(Pos(3,4), 'S');
		cout << dst.x << dst.y << endl;
		run();
	}
	catch (exception &e) {
		cerr << "Nastala chyba: " << e.what() << endl << flush;
		return EXIT_FAILURE;
	}

	return EXIT_SUCCESS;
}
/* vim: set noexpandtab: */
