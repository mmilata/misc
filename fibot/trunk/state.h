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
		std::vector<std::vector<FieldType>*> fMap;
		std::vector<Pos*> fOurBots;
		std::vector<Pos*> fTheirBots;
		int sizeX, sizeY;
		Pos fOurFlag, fTheirFlag;
};

#endif
