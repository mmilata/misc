#ifndef FB_STATE_H
#define FB_STATE_H

#define PRVNI 0
#define DRUHY 1

#include <vector>
#include "assert.h"

enum FieldType {
	ftEmpty,
	ftOurBot,
	ftTheirBot,
	ftWall
};

enum Action {
	aSever,
	aJih,
	aZapad,
	aVychod,
	aBoom,
	aNOOP
};

class Pos {
	public:
		int x,y;
		Pos(int x, int y):x(x),y(y) {};
		Pos() : x(0),y(0) {};

		Pos& operator += (const Pos &pos) {x += pos.x; y += pos.y; return *this;};
		bool operator == (const Pos &pos) const { return x == pos.x && y == pos.y; };
		bool operator != (const Pos &pos) const { return !(this->operator ==(pos));};
		Pos operator - (const Pos &pos) const {return Pos(x - pos.x, y - pos.y);};

		double distance(const Pos &pos) const;
};

typedef std::pair<Pos,char> botPos;

const char *strAction(Action a, botPos p);

class State {
	public:
		State(const char *filename);
		FieldType get(int x, int y) const {
			assert(x >= 0 && y >= 0 && x < columns && y < rows); 
			return fMap[(y*columns) + x];
		};
		FieldType get(const Pos &pos) const {return get(pos.x, pos.y);};
		void set(int x, int y, FieldType ft) {
			assert(x >= 0 && y >= 0 && x < columns && y < rows); 
			fMap[(y*columns) + x] = ft;
		};
		void set(const Pos &pos, FieldType ft) {set(pos.x, pos.y, ft);};
		void setDimensions(int inRows, int inColumns);
		void killBot(Pos p);
		bool endGame(void) const;
		void dump(void) const;
		int vyhral() const;
		bool isThreat(Pos p, int player) const;

		Pos getDestination(const Pos&, Action) const;

		int _get(std::vector<int> matrix, const Pos &pos);
		void _set(std::vector<int> matrix, const Pos &pos, int val);
		int countStepsTo(const Pos &posFrom, const Pos &posTo, const int &limit);
		Pos _getDestination(const Pos &position, Action action) const;

		int rows, columns;
		std::vector<FieldType> fMap;
		std::vector<botPos> fBots[2];
		Pos fFlag[2];
		int nase_cislo; // nase cislo hrace
		int jejich_cislo; // druhe cislo
		int tah_hrace; // hrac, ktery je aktualne na tahu
		int zbyva_kol;
		double maxDistance; // nejvetsi vzdalenost od vlajky
};

#endif
/* vim: set noexpandtab: */
