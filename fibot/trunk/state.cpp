#include "error.h"
#include "state.h"
#include <cmath>
#include <fstream>
#include <iostream>

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
    newX > 0 && newX <= columns && newY > 0 && newY <= rows && (
      get(newX, newY) == ftEmpty ||
      get(newX, newY) == ftFlag 
    )
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

State::State(const char *filename)
{
	int sirka, vyska, hracnatahu;
	int flag1s, flag1r, flag2s, flag2r;
	char square;
	ifstream statefile(filename);

	statefile >> sirka >> vyska >> zbyva_kol >> hracnatahu;
	statefile >> flag1s >> flag1r >> flag2s >> flag2r;

	setDimensions(vyska, sirka);

	for(int i=0; i<vyska; i++){
		for(int j=0; j<sirka; j++){
			statefile >> square;
			FieldType t;
			if(square == '#'){
				t = ftWall;
			}else if(square >= 'A' && square <= 'Z'){
				if((hracnatahu==1 && square <= 'M') || (hracnatahu==2 && square >= 'N')){
					t = ftOurBot;
					fOurBots.push_back(Pos(j,i));
				}else{
					t = ftTheirBot;
					fTheirBots.push_back(Pos(j,i));
				}
			}else{ /* melo by byt square == '.' */
				t = ftEmpty;
			}
			set(j,i,t);
		}
	}
	set(flag1s-1, flag1r-1, ftFlag);
	set(flag2s-1, flag2r-1, ftFlag);

	if(hracnatahu==1){
		fOurFlag.x = flag1s-1;
		fOurFlag.y = flag1r-1;
		fTheirFlag.x = flag2s-1;
		fTheirFlag.y = flag2r-1;
	}else{
		fOurFlag.x = flag2s-1;
		fOurFlag.y = flag2r-1;
		fTheirFlag.x = flag1s-1;
		fTheirFlag.y = flag1r-1;
	}

	statefile.close();
}

void State::dump(void)
{
	for(int i=0; i<rows; i++){
		for(int j=0; j<columns; j++){
			switch(get(j,i)){
				case ftEmpty:
					cout << '.';
					break;
				case ftWall:
					cout << '#';
					break;
				case ftOurBot:
					cout << 'O';
					break;
				case ftTheirBot:
					cout << 'T';
					break;
				case ftFlag:
					cout << 'f';
					break;
				default:
					throw new Error("dump: neznamy typ policka");
					break;
			}
		}
		cout << endl;
	}
	cout << "Nase vlajka: (" << fOurFlag.x << "," << fOurFlag.y << ")\n";
	cout << "Jejich vlajka: (" << fTheirFlag.x << "," << fTheirFlag.y << ")\n";
	cout << "Zbyva kol: " << zbyva_kol << endl;
	cout << "Nasi boti:";
	for(vector<Pos>::iterator it = fOurBots.begin(); it != fOurBots.end(); it++){
		cout << " (" << it->x << "," << it->y << ")";
	}
	cout << endl;
	cout << "Jejich boti:";
	for(vector<Pos>::iterator it = fTheirBots.begin(); it != fTheirBots.end(); it++){
		cout << " (" << it->x << "," << it->y << ")";
	}
	cout << endl;
}
