#include "state.h"

using namespace std;

State::setDimensions(int inRows, int inColumns)
{
	fRows = inRows;
	fColumns = inColumns;

	fMap.resize(inRows * inColumns);
	for (vector<FieldType>::iterator it = fMap.begin(); it != fMap.end(); it++) {
		*it = ftEmpty;
	};

}


