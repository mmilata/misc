#include "posix.pml"

#ifndef THREADS
#define THREADS 2
#endif

#define ZEROSTUFF 16
#define MAXSTUFF 31

pthread_mutex_t mutex;
pthread_cond_t wait_empty;
pthread_cond_t wait_full;
byte stuff = ZEROSTUFF;

proctype Producer()
{
	do
	::
		pthread_mutex_lock(mutex);
		do
		:: stuff < MAXSTUFF -> break;
		:: else ->
			pthread_cond_wait(wait_full,mutex);
		od;
		stuff = (stuff + THREADS > MAXSTUFF -> MAXSTUFF : stuff + THREADS);

		assert(stuff <= MAXSTUFF);

		pthread_cond_signal(wait_empty);
		pthread_mutex_unlock(mutex);
	od;
}

proctype Consumer()
{
	do
	::
		pthread_mutex_lock(mutex);
		do
		:: stuff > ZEROSTUFF -> break;
		:: else ->
			pthread_cond_wait(wait_empty,mutex);
		od;
		stuff--;

		assert(stuff >= ZEROSTUFF);

		pthread_cond_signal(wait_full);
		pthread_mutex_unlock(mutex);
	od;
}

init
{
	pthread_mutex_init(mutex);
	pthread_cond_init(wait_full);
	pthread_cond_init(wait_empty);

	byte i = THREADS;

	atomic {
		run Producer();
		do
		:: i == 0 -> break;
		:: else ->
			run Consumer();
			i--;
		od;
	}
}
