#include "rwlock.pml"

#ifndef THREADS
#define THREADS 2
#endif

mylib_rwlock_t the_lock;

byte readers_in_cs = 0;
byte writers_in_cs = 0;

proctype Thread()
{
	do ::
		if
		// writer
		:: true ->
			mylib_rwlock_rlock(the_lock);
			printf("Reader entered CS\n");
			readers_in_cs++;
			assert(readers_in_cs > 0);
			assert(writers_in_cs == 0);
			readers_in_cs--;

		// reader
		:: true ->
			mylib_rwlock_wlock(the_lock);
			printf("Writer entered CS\n");
			writers_in_cs++;
			assert(readers_in_cs == 0);
			assert(writers_in_cs == 1);
			writers_in_cs--;
		fi;

		mylib_rwlock_unlock(the_lock);
		printf("unlocked\n");
	od;
}

init
{
	mylib_rwlock_init(the_lock);

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
#define multiple_readers_in_cs	(readers_in_cs > 1)
#define one_writer		(writers_in_cs == 1)
#define writer_in_cs		(writers_in_cs > 0)
#define readers_in_cs		(readers_in_cs > 0)
