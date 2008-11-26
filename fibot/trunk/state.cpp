#include "error.h"
#include "state.h"
#include <cmath>
#include <fstream>
#include <iostream>
#include <vector>
#include <assert.h>

#define MAX(a, b) ((a) > (b) ? (a) : (b))

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
	tah_hrace = nase_cislo = (hracnatahu-1);
	jejich_cislo = 1 - nase_cislo;

	for(int i=0; i<vyska; i++){
		for(int j=0; j<sirka; j++){
			statefile >> square;
			FieldType t;
			if(square == '#'){
				t = ftWall;
			}else if(square >= 'A' && square <= 'Z'){
				if(square <= 'M'){
					t = (nase_cislo == PRVNI ? ftOurBot : ftTheirBot);
					fBots[PRVNI].push_back(botPos(Pos(j,i),square));
				}else{
					t = (nase_cislo == DRUHY ? ftOurBot : ftTheirBot);
					fBots[DRUHY].push_back(botPos(Pos(j,i),square));
				
				}
			}else{ /* melo by byt square == '.' */
				t = ftEmpty;
			}
			set(j,i,t);
		}
	}

	fFlag[PRVNI] = Pos(flag1s-1,flag1r-1);
	fFlag[DRUHY] = Pos(flag2s-1,flag2r-1);

	maxDistance = 0.0;
	for (int i = 0; i <= 1; i++) {
		maxDistance = MAX(maxDistance, fFlag[i].distance(Pos(0,0)));
		maxDistance = MAX(maxDistance, fFlag[i].distance(Pos(rows-1, columns-1)));
		maxDistance = MAX(maxDistance, fFlag[i].distance(Pos(rows-1, 0)));
		maxDistance = MAX(maxDistance, fFlag[i].distance(Pos(0, columns-1)));
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
					if(p == fFlag[nase_cislo]){
						cerr << 'o';
					}else if(p == fFlag[jejich_cislo]){
						cerr << 't';
					}else{
						cerr << '.';
					}
					break;
				case ftWall:
					cerr << '#';
					break;
				case ftOurBot:
					for(vector<botPos>::const_iterator it = fBots[nase_cislo].begin(); it != fBots[nase_cislo].end(); it++){
						if(p == it->first){
							cerr << it->second;
							break;
						}
					}
					break;
				case ftTheirBot:
					for(vector<botPos>::const_iterator it = fBots[jejich_cislo].begin(); it != fBots[jejich_cislo].end(); it++){
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
	cerr << "Nase vlajka: (" << fFlag[nase_cislo].x << "," << fFlag[nase_cislo].y << ")\n";
	cerr << "Jejich vlajka: (" << fFlag[jejich_cislo].x << "," << fFlag[jejich_cislo].y << ")\n";
	cerr << "Zbyva kol: " << zbyva_kol << " " << "cislo hrace na tahu: " << (tah_hrace+1) << " (my jsme hrac " << nase_cislo+1 << ")\n";
	cerr << "Nasi boti:";
	for(vector<botPos>::const_iterator it = fBots[nase_cislo].begin(); it != fBots[nase_cislo].end(); it++){
		cerr << " " << it->second << "(" << it->first.x << "," << it->first.y << ")";
	}
	cerr << endl;
	cerr << "Jejich boti:";
	for(vector<botPos>::const_iterator it = fBots[jejich_cislo].begin(); it != fBots[jejich_cislo].end(); it++){
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

	for(vector<botPos>::const_iterator it = fBots[nase_cislo].begin(); it != fBots[nase_cislo].end(); it++){
		if(it->first == fFlag[jejich_cislo]) {
			return true; /* wheee, mame vlajku */
		}
	}
	for(vector<botPos>::const_iterator it = fBots[jejich_cislo].begin(); it != fBots[jejich_cislo].end(); it++){
		if(it->first == fFlag[nase_cislo]) {
			return true;
		}
	}

	return false;
}

int State::vyhral() const
{
	for(vector<botPos>::const_iterator it = fBots[nase_cislo].begin(); it != fBots[nase_cislo].end(); it++)
		if(it->first == fFlag[jejich_cislo])
			return nase_cislo;
	for(vector<botPos>::const_iterator it = fBots[jejich_cislo].begin(); it != fBots[jejich_cislo].end(); it++)
		if(it->first == fFlag[nase_cislo])
			return jejich_cislo;
	return -1;
}


/*
 * !Nevymaze bota z mapy, jen ze seznamu
 */
void State::killBot(Pos p)
{
	for(vector<botPos>::iterator it = fBots[nase_cislo].begin(); it != fBots[nase_cislo].end(); it++){
		if(it->first == p){
			fBots[nase_cislo].erase(it);
			return;;
		}
	}
	for(vector<botPos>::iterator it = fBots[jejich_cislo].begin(); it != fBots[jejich_cislo].end(); it++){
		if(it->first == p){
			fBots[jejich_cislo].erase(it);
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

int State::_get(vector<int> matrix, const Pos &pos) {
	return matrix[(pos.y * columns) + pos.x];
}

void State::_set(vector<int> matrix, const Pos &pos, int val) {
	matrix[(pos.y * columns) + pos.x] = val;
}
	
int State::countStepsTo(const Pos &posFrom, const Pos &posTo, const int &limit) {
	vector<int> matrix;

	matrix.resize(rows * columns);
	for (vector<int>::iterator it = matrix.begin(); it != matrix.end(); it++) {
		*it = 10000;
	};
	_set(matrix, posFrom, 0);

	Pos fPos;
	vector<Pos> nPositions, fPositions;
	fPositions.push_back(posFrom);

	for (int n = 1; n <= limit; n++) {
		nPositions.clear();
		vector<Pos>::iterator p_i;
		for (p_i = fPositions.begin(); p_i != fPositions.end(); p_i++) {
			//cerr << "position " << p_i->x << " " << p_i->y << " " << n <<  endl;
			Pos nPos;
			nPos = _getDestination((*p_i), aSever);
			if (nPos != fPos) {
				if (nPos == posTo) {
					return n;
				}
				if (_get(matrix, nPos) > n)  {
					_set(matrix, nPos, n);
					nPositions.push_back(nPos);
				//cerr << "nPosition " << nPos.x << " " << nPos.y << " " << n <<  endl;
				}
			}
			nPos = _getDestination((*p_i), aVychod);
			if (nPos != fPos) {
				if (nPos == posTo) {
					return n;
				}
				if (_get(matrix, nPos) > n) {
					_set(matrix, nPos, n);
					nPositions.push_back(nPos);
				//cerr << "nPosition " << nPos.x << " " << nPos.y << " " << n <<  endl;
				}
			}
			nPos = _getDestination((*p_i), aJih);
			if (nPos != fPos) {
				if (nPos == posTo) {
					return n;
				}
				if (_get(matrix, nPos) > n) {
					_set(matrix, nPos, n);
					nPositions.push_back(nPos);
				//cerr << "nPosition " << nPos.x << " " << nPos.y << " " << n <<  endl;
				}
			}
			nPos = _getDestination((*p_i), aZapad);
			if (nPos != fPos) {
				if (nPos == posTo) {
					return n;
				}
				if (_get(matrix, nPos) > n) {
					_set(matrix, nPos, n);
					nPositions.push_back(nPos);
				//cerr << "nPosition " << nPos.x << " " << nPos.y << " " << n <<  endl;
				}
			}
		}
		fPositions = nPositions;
	}
	return -1;
}

Pos State::_getDestination(const Pos &position, Action action) const {
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
			get(tmp) != ftWall
		)
	);

	return destination;
}


bool State::isThreat(Pos p, int player) const
{
	int x = p.x;
	int y = p.y;
	FieldType f;

	for(int nx = x+1;
	    nx < columns && get(nx,y) != ftWall;
	    nx++){
		f = get(nx,y);
		if(f == ftOurBot){
			if(tah_hrace != player)
				return true;
		}else if(f == ftTheirBot){
			if(tah_hrace == player)
				return true;
		}
	}

	for(int nx = x-1;
	    nx >= 0 && get(nx,y) != ftWall;
	    nx--){
		f = get(nx,y);
		if(f == ftOurBot){
			if(tah_hrace != player)
				return true;
		}else if(f == ftTheirBot){
			if(tah_hrace == player)
				return true;
		}
	}

	for(int ny = y+1;
	    ny < rows && get(x,ny) != ftWall;
	    ny++){
		f = get(x,ny);
		if(f == ftOurBot){
			if(tah_hrace != player)
				return true;
		}else if(f == ftTheirBot){
			if(tah_hrace == player)
				return true;
		}
	}

	for(int ny = y-1;
	    ny >= 0 && get(x,ny) != ftWall;
	    ny--){
		f = get(x,ny);
		if(f == ftOurBot){
			if(tah_hrace != player)
				return true;
		}else if(f == ftTheirBot){
			if(tah_hrace == player)
				return true;
		}
	}
	return false;
}
/* vim: set noexpandtab: */
