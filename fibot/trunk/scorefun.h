#ifndef FB_SCOREFUN_H
#define FB_SCOREFUN_H

#include "state.h"

typedef double (*ScoreFun)(const State &st);

double minimax(const State &st, ScoreFun scf, int depth);
double alphabeta(const State &st, ScoreFun scf, double alpha, double beta, int depth);

double averageFlagDistance(const State &st);
double sensibleScore(const State &st);
double testWhatever(const State &st);

#endif
