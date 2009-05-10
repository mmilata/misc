#include "posix.pml"

#ifndef CONSUMERS
#define CONSUMERS 2
#endif

#ifndef PRODUCERS
#define PRODUCERS 2
#endif

#define ZEROSTUFF 4
#define MAXSTUFF 31

pthread_mutex_t mutex;
pthread_cond_t wait_empty;
pthread_cond_t wait_full;

byte stuff = ZEROSTUFF;
byte producer_in_cs = 0;
byte consumer_in_cs = 0;

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
		producer_in_cs++;
		stuff = (stuff + CONSUMERS > MAXSTUFF -> MAXSTUFF : stuff + CONSUMERS);
		producer_in_cs--;

		pthread_cond_broadcast(wait_empty);
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
		consumer_in_cs++;
		stuff--;
		consumer_in_cs--;

		pthread_cond_signal(wait_full);
		pthread_mutex_unlock(mutex);
	od;
}

init
{
	pthread_mutex_init(mutex);
	pthread_cond_init(wait_full);
	pthread_cond_init(wait_empty);

	atomic {
		byte i = PRODUCERS;
		do
		:: i == 0 -> break;
		:: else ->
			run Consumer();
			i--;
		od;
		i = CONSUMERS;
		do
		:: i == 0 -> break;
		:: else ->
			run Producer();
			i--;
		od;
	}
}

#define right_amount_of_stuff (ZEROSTUFF <= stuff && stuff <= MAXSTUFF)
#define mutual_exclusion (producer_in_cs + consumer_in_cs <= 1)
