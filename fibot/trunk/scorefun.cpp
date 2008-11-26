#include "scorefun.h"
#include "state.h"

#include <vector>

using namespace std;

double averageFlagDistance(const State &st)
{
	vector<botPos>::const_iterator i;
	double ret_val = 0;
	for (i = st.fOurBots.begin(); i != st.fOurBots.end(); i++) {
		ret_val += st.fTheirFlag.distance(i->first);
	}

	return 100.0 - (ret_val/st.fOurBots.size());
}
