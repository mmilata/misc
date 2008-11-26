#include "error.h"
#include "state.h"
#include <cmath>
#include <fstream>
#include <iostream>
#include <vector>
#include <assert.h>
#include <cstdio>

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

	} while (inMap(tmp) && get(tmp) == ftEmpty);

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
				t = ftBot;
				int botnum = square <= 'M' ? PRVNI : DRUHY;
				fBots[botnum][Pos(j,i)] = square;
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

	distMap[PRVNI] = computeFlagDst(fFlag[PRVNI]);
	distMap[DRUHY] = computeFlagDst(fFlag[DRUHY]);
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
				case ftBot:
					for (int i = 0; i < 2; i++) 
						for (map<Pos, char>::const_iterator it = fBots[i].begin(); it != fBots[i].end(); it++) 
							if (p == it->first)
								cerr << it->second;
					break;
			}
		}
		cerr << endl;
	}
	cerr << "Nase vlajka: (" << fFlag[nase_cislo].x << "," << fFlag[nase_cislo].y << ")\n";
	cerr << "Jejich vlajka: (" << fFlag[jejich_cislo].x << "," << fFlag[jejich_cislo].y << ")\n";
	cerr << "Zbyva kol: " << zbyva_kol << " " << "cislo hrace na tahu: " << (tah_hrace+1) << " (my jsme hrac " << nase_cislo+1 << ")\n";
	cerr << "Nasi boti:";
	for(map<Pos, char>::const_iterator it = fBots[nase_cislo].begin(); it != fBots[nase_cislo].end(); it++){
		cerr << " " << it->second << "(" << it->first.x << "," << it->first.y << ")";
	}
	cerr << endl;
	cerr << "Jejich boti:";
	for(map<Pos, char>::const_iterator it = fBots[jejich_cislo].begin(); it != fBots[jejich_cislo].end(); it++){
		cerr << " " << it->second << "(" << it->first.x << "," << it->first.y << ")";
	}
	cerr << endl;
	cerr << (endGame() ? "Hra skoncila" : "Jeste neni konec hry") << endl;
	cerr << endl;


	for(int pl=0; pl<=1; pl++){
		cerr << "flagDist hrace " << pl+1 << endl;
		for(int i=0; i<rows; i++){
			for(int j=0; j<columns; j++){
				p = Pos(j,i);
				int fd = flagDist(pl, p);
				if(fd == -1)
					fprintf(stderr, "  .");
				else
					fprintf(stderr, "%3d", fd);
			}
			cerr << endl;
		}
		cerr << endl;
	}
}

bool State::endGame(void) const
{
	if(zbyva_kol==0)
		return true;

	for(map<Pos, char>::const_iterator it = fBots[nase_cislo].begin(); it != fBots[nase_cislo].end(); it++){
		if(it->first == fFlag[jejich_cislo]) {
			return true; /* wheee, mame vlajku */
		}
	}
	for(map<Pos, char>::const_iterator it = fBots[jejich_cislo].begin(); it != fBots[jejich_cislo].end(); it++){
		if(it->first == fFlag[nase_cislo]) {
			return true;
		}
	}

	return false;
}

int State::vyhral() const
{
	for(map<Pos, char>::const_iterator it = fBots[nase_cislo].begin(); it != fBots[nase_cislo].end(); it++)
		if(it->first == fFlag[jejich_cislo])
			return nase_cislo;
	for(map<Pos, char>::const_iterator it = fBots[jejich_cislo].begin(); it != fBots[jejich_cislo].end(); it++)
		if(it->first == fFlag[nase_cislo])
			return jejich_cislo;
	return -1;
}

void State::killBot(const Pos &p)
{
	map<Pos, char>::iterator it;

	for (int i = 0; i < 2; i++) {
		it = fBots[i].find(p);
		if (it != fBots[i].end())
			fBots[i].erase(it);
	}
	set(p, ftEmpty);
}

const char *strAction(Action a, const char bot)
{
	if(a == aNOOP){
		return "-";
	}

	static char ret[4] = "A S";

	ret[0] = bot;

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

/*
int State::_get(vector<int> matrix, const Pos &pos) const {
	return matrix[(pos.y * columns) + pos.x];
}

void State::_set(vector<int> matrix, const Pos &pos, int val) const {
	matrix[(pos.y * columns) + pos.x] = val;
}
*/

int State::dstGet(vector<int>* m, const Pos &pos) const
{
	return (*m)[(pos.y * columns) + pos.x];
}

void State::dstSet(vector<int>* m, const Pos &pos, const int &val) const
{
	(*m)[(pos.y * columns) + pos.x] = val;
}

vector<int>* State::computeFlagDst(const Pos &p) const
{
	vector<int> *matrix = new vector<int>(rows * columns, -1);
	dstSet(matrix, p, 0);

	vector<Pos> nPositions, fPositions;
	fPositions.push_back(p);

	for (int n = 1; n <= zbyva_kol; n++)
	{
		nPositions.clear();
		vector<Pos>::iterator p_i;
		for (p_i = fPositions.begin(); p_i != fPositions.end(); p_i++) {
			//cerr << "position " << p_i->x << " " << p_i->y << " " << n <<  endl;
			Pos nPos;
			nPos = getDestination((*p_i), aSever);
				if (dstGet(matrix, nPos) == -1)  {
					dstSet(matrix, nPos, n);
					nPositions.push_back(nPos);
				//cerr << "nPosition " << nPos.x << " " << nPos.y << " " << n <<  endl;
				}
			nPos = getDestination((*p_i), aVychod);
				if (dstGet(matrix, nPos) == -1) {
					dstSet(matrix, nPos, n);
					nPositions.push_back(nPos);
				//cerr << "nPosition " << nPos.x << " " << nPos.y << " " << n <<  endl;
				}
			nPos = getDestination((*p_i), aJih);
				if (dstGet(matrix, nPos) == -1) {
					dstSet(matrix, nPos, n);
					nPositions.push_back(nPos);
				//cerr << "nPosition " << nPos.x << " " << nPos.y << " " << n <<  endl;
				}
			nPos = getDestination((*p_i), aZapad);
				if (dstGet(matrix, nPos) == -1) {
					dstSet(matrix, nPos, n);
					nPositions.push_back(nPos);
				//cerr << "nPosition " << nPos.x << " " << nPos.y << " " << n <<  endl;
				}
		}
		fPositions = nPositions;
	}
	return matrix;
}
/*
int State::countStepsTo(const Pos &posFrom, const Pos &posTo, const int &limit) const {
	vector<int> matrix(rows * columns, 10000);

	Pos fPos;
	vector<Pos> nPositions, fPositions;
	fPositions.push_back(posFrom);

	for (int n = 1; n <= limit; n++) {
		nPositions.clear();
		vector<Pos>::iterator p_i;
		for (p_i = fPositions.begin(); p_i != fPositions.end(); p_i++) {
			//cerr << "position " << p_i->x << " " << p_i->y << " " << n <<  endl;
			Pos nPos;
			nPos = getDestination((*p_i), aSever);
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
			nPos = getDestination((*p_i), aVychod);
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
			nPos = getDestination((*p_i), aJih);
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
			nPos = getDestination((*p_i), aZapad);
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
*/

int State::flagDist(int player, const Pos &p) const
{
	return dstGet(distMap[player], p);
}

bool State::inMap(const Pos& pos) const
{
	if (pos.x < 0 || pos.y < 0 || pos.x >= columns || pos.y >= rows)
		return false;
	return true;
}


bool State::inThreat(Pos p, int player) const
{
	Pos cur;
	const map<Pos, char> &bots(fBots[player]);

	for(cur = Pos(p.x+1, p.y); inMap(cur) && get(cur) != ftWall; cur.x += 1)
		if (get(cur) == ftBot && bots.find(cur) != bots.end())
			return true;
	
	for(cur = Pos(p.x, p.y+1); inMap(cur) && get(cur) != ftWall; cur.y += 1)
		if (get(cur) == ftBot && bots.find(cur) != bots.end())
			return true;
	
	for(cur = Pos(p.x-1, p.y); inMap(cur) && get(cur) != ftWall; cur.x -= 1)
		if (get(cur) == ftBot && bots.find(cur) != bots.end())
			return true;
	
	for(cur = Pos(p.x, p.y-1); inMap(cur) && get(cur) != ftWall; cur.y -= 1)
		if (get(cur) == ftBot && bots.find(cur) != bots.end())
			return true;

	return false;
}

char State::botName(const Pos &pos) const
{
	map<Pos, char>::const_iterator it;

	it = fBots[tah_hrace].find(pos);

	if (it == fBots[tah_hrace].end())
		throw new Error("Zadany bot k vyhledani neexistuje v ramci botu aktualniho hrace");
	
	return it->second;
}

bool State::isEnemy(const Pos &pos) const
{
	return fBots[!tah_hrace].find(pos) == fBots[!tah_hrace].end();
}

/* vim: set noexpandtab: */

