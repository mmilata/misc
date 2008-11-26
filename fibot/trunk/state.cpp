#include "error.h"
#include "state.h"
#include <cmath>
#include <fstream>
#include <iostream>
#include <vector>
#include <assert.h>

using namespace std;

double Pos::distance(const Pos &pos) const
{
	Pos tmp = *this - pos;

	return sqrt((tmp.x*tmp.x) + (tmp.y*tmp.y));
}

void State::setDimensions(int inRows, int inColumns)
{
	assert(inRows > 0 && inColumns > 0);

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

State::State(const char *filename)
{
	int sirka, vyska, hracnatahu;
	int flag1s, flag1r, flag2s, flag2r;
	char square;
	ifstream statefile(filename);

	statefile >> sirka >> vyska >> zbyva_kol >> hracnatahu;
	statefile >> flag1s >> flag1r >> flag2s >> flag2r;

	setDimensions(vyska, sirka);
	tah_hrace = hracnatahu;

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
	Pos p;

	for(int i=0; i<rows; i++){
		for(int j=0; j<columns; j++){
			p = Pos(j,i);
			switch(get(j,i)){
				case ftEmpty:
					if(p == fOurFlag){
						cerr << 'o';
					}else if(p == fTheirFlag){
						cerr << 't';
					}else{
						cerr << '.';
					}
					break;
				case ftWall:
					cerr << '#';
					break;
				case ftOurBot:
					for(vector<botPos>::const_iterator it = fOurBots.begin(); it != fOurBots.end(); it++){
						if(p == it->first){
							cerr << it->second;
							break;
						}
					}
					break;
				case ftTheirBot:
					for(vector<botPos>::const_iterator it = fTheirBots.begin(); it != fTheirBots.end(); it++){
						if(p == it->first){
							cerr << it->second;
							break;
						}
					}
					break;
			}
		}
		cerr << endl;
	}
	cerr << "Nase vlajka: (" << fOurFlag.x << "," << fOurFlag.y << ")\n";
	cerr << "Jejich vlajka: (" << fTheirFlag.x << "," << fTheirFlag.y << ")\n";
	cerr << "Zbyva kol: " << zbyva_kol << " " << "cislo hrace na tahu: " << tah_hrace << endl;
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
	cerr << (endGame() ? "Hra skoncila" : "Jeste neni konec hry") << endl;
	cerr << endl;
}

bool State::endGame(void) const
{
	if(zbyva_kol==0)
		return true;

	for(vector<botPos>::const_iterator it = fOurBots.begin(); it != fOurBots.end(); it++){
		if(it->first == fTheirFlag)
			return true; /* wheee, mame vlajku */
	}
	for(vector<botPos>::const_iterator it = fTheirBots.begin(); it != fTheirBots.end(); it++){
		if(it->first == fOurFlag)
			return true;
	}

	return false;
}

/*
 * !Nevymaze bota z mapy, jen ze seznamu
 */
void State::killBot(Pos p)
{
	for(vector<botPos>::iterator it = fOurBots.begin(); it != fOurBots.end(); it++){
		if(it->first == p){
			fOurBots.erase(it);
			return;;
		}
	}
	for(vector<botPos>::iterator it = fTheirBots.begin(); it != fTheirBots.end(); it++){
		if(it->first == p){
			fTheirBots.erase(it);
			return;;
		}
	}
}

const char *strAction(Action a, botPos p)
{
	if(a == aNOOP){
		return "-";
	}

	static char ret[4] = "A S";

	ret[0] = p.second;

	switch(a){
		case aSever:
			ret[2] = 'S';
			break;
		case aVychod:
			ret[2] = 'V';
			break;
		case aJih:
			ret[2] = 'J';
			break;
		case aZapad:
			ret[2] = 'Z';
			break;
		case aBoom:
			ret[2] = 'D';
			break;
		case aNOOP:
			throw Error("this should never happen");
			break;
	}

	return ret;
}
/* vim: set noexpandtab: */
