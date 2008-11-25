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
	int x,y;
};

class State {
	public:
		FieldType get(int x, int y) const {return fMap[(y*columns) + x];};
		void set(int x, int y, FieldType ft) {fMap[(y*columns) + x] = ft;};
		void setDimensions(int inRows, int inColumns);

		std::vector<FieldType> fMap;
		std::vector<Pos*> fOurBots;
		std::vector<Pos*> fTheirBots;
		int rows, columns;
		int kolo;
		Pos fOurFlag, fTheirFlag;
};

#endif
