#ifdef USE_CORRECT_RWLOCK
#include "rwlock_correct.pml"
#else
#include "rwlock.pml"
#endif

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
		printf("Writer leaving CS\n");

		mylib_rwlock_unlock(the_lock);
	od;
}

proctype Reader()
{
	do ::
		mylib_rwlock_rlock(the_lock);

		printf("Reader entered CS\n");
		readers_in_cs++;
		readers_in_cs--;
		printf("Reader leaving CS\n");

		mylib_rwlock_unlock(the_lock);
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

#define lock_consistent		(the_lock.pending_writers <= WRITERS && the_lock.readers <= READERS && readers_in_cs <= the_lock.readers)
#define one_writer		(writers_in_cs == 1)
#define writers_in_cs		(writers_in_cs > 0)
#define readers_in_cs		(readers_in_cs > 0)
#define multiple_readers_in_cs	(readers_in_cs > 1)
