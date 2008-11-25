#include "state.h"

using namespace std;

void State::setDimensions(int inRows, int inColumns)
{
	rows = inRows;
	columns = inColumns;

	fMap.resize(inRows * inColumns);
	for (vector<FieldType>::iterator it = fMap.begin(); it != fMap.end(); it++) {
		*it = ftEmpty;
	};

}


