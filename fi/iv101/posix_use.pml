#ifndef THREADS
#define THREADS 2
#endif

#include "posix.pml"

pthread_mutex_t cs_mutex;
byte in_cs = 0;

proctype Thread()
{
	do
	::	pthread_mutex_lock(cs_mutex);

		in_cs++;
		assert(in_cs == 1);
		in_cs--;

		pthread_mutex_unlock(cs_mutex);
	od
}

init
{
	pthread_mutex_init(cs_mutex);

	byte i = THREADS;

	atomic {
		do
		:: i == 0 -> break;
		:: else ->
			run Thread();
			i--;
		od;
	}
}
