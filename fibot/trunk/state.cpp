#include <cmath>
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

Pos State::getDestination(const Pos position, const char direction) {
  int moveX = 0, moveY = 0, newX = 0, newY = 0;

  Pos destination(position.x, position.y);

  switch (direction) {
    case 'S':
      moveX = 0; moveY = -1;
      break;
    case 'V':
      moveX = 1; moveY = 0;
      break;
    case 'J':
      moveX = 0; moveY = 1;
      break;
    case 'Z': 
      moveX = -1; moveY = 0;
      break;
  }
  
  newX = position.x + moveX; newY = position.y + moveY;

  while ( 
    get(newX, newY) == ftEmpty ||
    get(newX, newY) == ftFlag
  ) {
    destination.x = newX;
    destination.y = newY;
    newX = newX + moveX; newY = newY + moveY;
  }

  return destination;
}

int State::getDistance(const Pos position1, const Pos position2) {
  double dist;
  dist = sqrt(
    (position1.x - position2.x) * (position1.x - position2.x)
    +
    (position1.y - position2.y) * (position1.y - position2.y)
  );

  return round(dist);
}

    
    





