#include "error.h"
#include "state.h"
#include <cmath>
#include <fstream>
#include <iostream>
#include <vector>

using namespace std;

double Pos::distance(const Pos &pos) const
{
	Pos tmp = *this - pos;

	return sqrt((tmp.x*tmp.x) + (tmp.y*tmp.y));
}

void State::setDimensions(int inRows, int inColumns)
{
	rows = inRows;
	columns = inColumns;

	fMap.resize(inRows * inColumns);
	for (vector<FieldType>::iterator it = fMap.begin(); it != fMap.end(); it++) {
		*it = ftEmpty;
	};

}

Pos State::getDestination(const Pos &position, Action action) const {
	Pos delta;
	Pos destination;
	Pos tmp(position);

	switch (action) {
		case aSever:
			delta = Pos(0, -1);
			break;
		case aVychod:
			delta = Pos(1, 0);
			break;
		case aJih:
			delta = Pos(0, 1);
			break;
		case aZapad: 
			delta = Pos(-1, 0);
			break;
		case aBoom:
		case aNOOP:
			return position;
	}

	do {
		destination = tmp;
		tmp += delta;

	} while ( 
		tmp.x >= 0 && tmp.x < columns && tmp.y >= 0 && tmp.y < rows && (
			get(tmp) == ftEmpty
		)
	);

	return destination;
}

/* vrati nejmensi vzdalenost jednotlivych robotu bots od vlajky flag
 */
double State::getScore(vector<botPos> &bots, const Pos &flag) const {
	vector<botPos>::iterator i;
	double ret_val = -1;
	for (i = bots.begin(); i != bots.end(); i++) {
		int dist = flag.distance(i->first);
		if (dist < ret_val || ret_val < 0) {
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
					cerr << '.';
					break;
				case ftWall:
					cerr << '#';
					break;
				case ftOurBot:
					cerr << 'O';
					break;
				case ftTheirBot:
					cerr << 'T';
					break;
				default:
					throw new Error("dump: neznamy typ policka");
					break;
			}
		}
		cerr << endl;
	}
	cerr << "Nase vlajka: (" << fOurFlag.x << "," << fOurFlag.y << ")\n";
	cerr << "Jejich vlajka: (" << fTheirFlag.x << "," << fTheirFlag.y << ")\n";
	cerr << "Zbyva kol: " << zbyva_kol << endl;
	cerr << "Nasi boti:";
	for(vector<botPos>::const_iterator it = fOurBots.begin(); it != fOurBots.end(); it++){
		cerr << " " << it->second << "(" << it->first.x << "," << it->first.y << ")";
	}
	cerr << endl;
	cerr << "Jejich boti:";
	for(vector<botPos>::const_iterator it = fTheirBots.begin(); it != fTheirBots.end(); it++){
		cerr << " " << it->second << "(" << it->first.x << "," << it->first.y << ")";
	}
	cerr << endl;
}
/* vim: set noexpandtab: */
