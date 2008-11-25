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

class Pos {
	public:
		int x,y;
		Pos(int x, int y):x(x),y(y) {};
		Pos() {};
};

typedef std::pair<Pos,char> botPos;

class State {
	public:
		State(const char *filename);
		FieldType get(int x, int y) const {return fMap[(y*columns) + x];};
		void set(int x, int y, FieldType ft) {fMap[(y*columns) + x] = ft;};
		void setDimensions(int inRows, int inColumns);
		void dump(void);

		Pos getDestination(const Pos, const char);
		int getDistance(const Pos, const Pos);

		std::vector<FieldType> fMap;
		std::vector<botPos> fOurBots;
		std::vector<botPos> fTheirBots;
		int rows, columns;
		int zbyva_kol;
		Pos fOurFlag, fTheirFlag;
};

#endif
/* vim: noexpandtab */
