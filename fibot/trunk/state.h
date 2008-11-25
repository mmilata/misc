#ifndef FB_STATE_H
#define FB_STATE_H


#include <vector>

enum FieldType {
	ftEmpty,
	ftOurBot,
	ftTheirBot,
	ftWall,
	ftFlag
};

enum Direction {
	dSever,
	dJih,
	dZapad,
	dVychod
};

class Pos {
	public:
		int x,y;
		Pos(int x, int y):x(x),y(y) {};
		Pos() : x(0),y(0) {};

		Pos& operator += (const Pos &pos) {x += pos.x; y += pos.y; return *this;};
		bool operator == (const Pos &pos) const { return x == pos.x && y == pos.y; };
		bool operator != (const Pos &pos) const { return !(this->operator ==(pos));};
};

typedef std::pair<Pos,char> botPos;

class State {
	public:
		State(const char *filename);
		FieldType get(int x, int y) const {return fMap[(y*columns) + x];};
		FieldType get(const Pos &pos) const {return get(pos.x, pos.y);};
		void set(int x, int y, FieldType ft) {fMap[(y*columns) + x] = ft;};
		void setDimensions(int inRows, int inColumns);
		void dump(void) const;

		Pos getDestination(const Pos&, Direction) const;
		int getDistance(const Pos&, const Pos&) const;
		int getScore(std::vector<botPos> &bots, const Pos &flag);

		std::vector<FieldType> fMap;
		std::vector<botPos> fOurBots;
		std::vector<botPos> fTheirBots;
		int rows, columns;
		int zbyva_kol;
		Pos fOurFlag, fTheirFlag;
};

#endif
/* vim: set noexpandtab: */
