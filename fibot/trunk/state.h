#ifndef FB_STATE_H
#define FB_STATE_H


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

		Pos getDestination(const Pos&, Action) const;
		double getScore(std::vector<botPos> &bots, const Pos &flag) const;

		std::vector<FieldType> fMap;
		std::vector<botPos> fOurBots;
		std::vector<botPos> fTheirBots;
		int rows, columns;
		int zbyva_kol;
		int tah_hrace;
		Pos fOurFlag, fTheirFlag;
};

#endif
/* vim: set noexpandtab: */
