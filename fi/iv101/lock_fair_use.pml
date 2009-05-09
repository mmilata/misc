#define QUEUED_MUTEXES
#include "rwlock.pml"

#ifndef WRITERS
#define WRITERS 2
#endif

#ifndef READERS
#define READERS 2
#endif

mylib_rwlock_t the_lock;

byte readers_in_cs = 0;
byte writers_in_cs = 0;

proctype Writer()
{
	do ::
		mylib_rwlock_wlock(the_lock);
		printf("Writer entered CS\n");
		writers_in_cs++;
		writers_in_cs--;

		mylib_rwlock_unlock(the_lock);
		printf("Writer unlocked\n");
	od;
}

proctype Reader()
{
	do ::
		mylib_rwlock_rlock(the_lock);
		printf("Reader entered CS\n");
		readers_in_cs++;
		readers_in_cs--;

		mylib_rwlock_unlock(the_lock);
		printf("Reader unlocked\n");
	od;
}

init
{
	mylib_rwlock_init(the_lock);

	atomic {
		byte i = READERS;
		do
		:: i == 0 -> break;
		:: else ->
			run Reader();
			i--;
		od;
		i = WRITERS;
		do
		:: i == 0 -> break;
		:: else ->
			run Writer();
			i--;
		od;
	}
}

#define multiple_readers_in_cs	(readers_in_cs > 1)
#define one_writer		(writers_in_cs == 1)
#define writer_in_cs		(writers_in_cs > 0)
#define readers_in_cs		(readers_in_cs > 0)
