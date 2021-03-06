#ifndef FB_STATE_H
#define FB_STATE_H

#define PRVNI 0
#define DRUHY 1

#include <vector>
#include <map>
#include "assert.h"

enum FieldType {
	ftEmpty,
	ftBot,
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
		Pos operator + (const Pos &pos) const {Pos p(*this); p += pos; return p;}
		//bool operator <(const Pos &pos) const {return x < pos.x && y < pos.y;};
		bool operator <(const Pos& pos) const { if(x == pos.x) return y < pos.y; else return x < pos.x; };

		double distance(const Pos &pos) const;
		double distanceNormalized(const Pos &pos, double max) const { return distance(pos)/max; };
};

const char *strAction(Action a, const char);

class State {
	public:
		State() {};
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
		void killBot(const Pos &p);
		bool endGame(void) const;
		void dump(void) const;
		int vyhral() const;
		bool inThreat(Pos p, int player) const; // vraci true, kdyz je bot na dane pozici ohrozen
												// player udava od ktereho hrace se ocekava ohrozeni

		Pos getDestination(const Pos&, Action) const;
		Pos getDestinationNoBot(const Pos&, Action) const;
		bool inMap(const Pos&) const;
		char botName(const Pos&) const;
		bool isEnemy(const Pos&) const;

		int dstGet(std::vector<int> *m, const Pos &p) const;
		void dstSet(std::vector<int> *m, const Pos &p, const int &i) const;
		std::vector<int>* computeFlagDst(const Pos &p) const;
		int flagDist(int player, const Pos &p) const;

		int rows, columns;
		std::vector<FieldType> fMap;
		std::map<Pos, char> fBots[2];
		Pos fFlag[2];
		int nase_cislo; // nase cislo hrace
		int jejich_cislo; // druhe cislo
		int tah_hrace; // hrac, ktery je aktualne na tahu
		int zbyva_kol;
		double maxDistance; // nejvetsi vzdalenost od vlajky
		std::vector<int>* distMap[2];

		void slide(std::vector<int>* m, Pos from, Pos delta, Pos end, int n) const;
};

#endif
/* vim: set noexpandtab: */
