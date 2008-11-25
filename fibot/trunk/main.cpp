#include "state.h"
#include "error.h"
#include <iostream>
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
	try {
		run();
	}
	catch (exception &e) {
		cerr << "Nastala chyba: " << e.what() << endl << flush;
		return EXIT_FAILURE;
	}

	return EXIT_SUCCESS;
}

