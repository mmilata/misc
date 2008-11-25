#include "error.h"
#include "state.h"
#include <cmath>
#include <fstream>
#include <iostream>
#include <vector>

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

Pos State::getDestination(const Pos &position, Direction direction) const {
	Pos delta;
	Pos destination;
	Pos tmp(position);

	switch (direction) {
		case dSever:
			delta = Pos(0, -1);
			break;
		case dVychod:
			delta = Pos(1, 0);
			break;
		case dJih:
			delta = Pos(0, 1);
			break;
		case dZapad: 
			delta = Pos(-1, 0);
			break;
	}

	do {
		destination = tmp;
		tmp += delta;

	} while ( 
		tmp.x >= 0 && tmp.x < columns && tmp.y >= 0 && tmp.y < rows && (
			get(tmp) == ftEmpty ||
			get(tmp) == ftFlag 
		)
	);

	return destination;
}

int State::getDistance(const Pos &position1, const Pos &position2) const {
	double dist;
	dist = sqrt(
		(position1.x - position2.x) * (position1.x - position2.x)
		+
		(position1.y - position2.y) * (position1.y - position2.y)
	);

	return round(dist);
}

/* vrati nejmensi vzdalenost jednotlivych robotu bots od vlajky flag
 */
int State::getScore(vector<botPos> &bots, const Pos &flag) {
	vector<botPos>::iterator i;
	int ret_val = 0;
	for (i = bots.begin(); i != bots.end(); i++) {
		int dist = getDistance(i->first, flag);
		if (dist < ret_val) {
			ret_val = dist;
		}
	}

	return ret_val;
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
					fOurBots.push_back(botPos(Pos(j,i),square));
				}else{
					t = ftTheirBot;
					fTheirBots.push_back(botPos(Pos(j,i),square));
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

void State::dump(void) const
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
	for(vector<botPos>::const_iterator it = fOurBots.begin(); it != fOurBots.end(); it++){
		cout << " " << it->second << "(" << it->first.x << "," << it->first.y << ")";
	}
	cout << endl;
	cout << "Jejich boti:";
	for(vector<botPos>::const_iterator it = fTheirBots.begin(); it != fTheirBots.end(); it++){
		cout << " " << it->second << "(" << it->first.x << "," << it->first.y << ")";
	}
	cout << endl;
}
/* vim: set noexpandtab: */
