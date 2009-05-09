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

		printf("Thread %d entered CS\n", _pid);
cs:		in_cs++;
		in_cs--;
		printf("Thread %d leaving CS\n", _pid);

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

// atomic propositions
#define mutual_exclusion (in_cs == 0 || in_cs == 1)
#define thread1_cs (Thread[1]@cs)
#define somethread_in_cs (in_cs > 0)
