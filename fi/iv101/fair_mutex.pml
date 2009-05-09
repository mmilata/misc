#ifndef QUEUED_MUTEXES
#define QUEUED_MUTEXES
#endif

#include "posix.pml"

pthread_mutex_t mootex;

bool p_in_cs = 0;
bool q_in_cs = 0;

proctype P()
{
	do
	::
		pthread_mutex_lock(mootex);
		p_in_cs++;
		printf("P in CS\n");
		p_in_cs--;
		pthread_mutex_unlock(mootex);
	od
}

proctype Q()
{
	do
	::
		pthread_mutex_lock(mootex);
		q_in_cs++;
		printf("Q in CS\n");
		q_in_cs--;
		pthread_mutex_unlock(mootex);
	od
}

init
{
	pthread_mutex_init(mootex);
	atomic {
		run P();
		run Q();
	}
}
