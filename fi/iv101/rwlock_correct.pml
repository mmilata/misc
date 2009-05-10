#include "posix.pml"

typedef mylib_rwlock_t {
	byte readers;
	bool writer;
	pthread_cond_t readers_proceed;
	pthread_cond_t writer_proceed;
	byte pending_writers;
	pthread_mutex_t read_write_lock;
};

inline mylib_rwlock_init(l)
{
	l.readers = 0;
	l.writer = 0;
	l.pending_writers = 0;
	pthread_mutex_init(l.read_write_lock);
	pthread_cond_init(l.readers_proceed);
	pthread_cond_init(l.writer_proceed);
}

inline mylib_rwlock_rlock(l)
{
	pthread_mutex_lock(l.read_write_lock);
	do
	:: (l.pending_writers > 0) || (l.writer > 0) ->
		pthread_cond_wait(l.readers_proceed, l.read_write_lock);
	:: else ->
		break;
	od;
	l.readers++;
	pthread_mutex_unlock(l.read_write_lock);
}

inline mylib_rwlock_wlock(l)
{
	pthread_mutex_lock(l.read_write_lock);
	l.pending_writers++;
	do
	:: (l.writer > 0) || (l.readers > 0) ->
		pthread_cond_wait(l.writer_proceed, l.read_write_lock);
	:: else ->
		break;
	od;
	l.pending_writers--;
	l.writer = 1;
	pthread_mutex_unlock(l.read_write_lock);
}

inline mylib_rwlock_unlock(l)
{
	pthread_mutex_lock(l.read_write_lock);
	if
	:: l.writer > 0 ->
		l.writer = 0;
	:: else ->
		l.readers--;
	fi;
	pthread_mutex_unlock(l.read_write_lock);
	if
	:: (l.readers == 0) && (l.pending_writers > 0) ->
		pthread_cond_signal(l.writer_proceed);
	:: else ->
		pthread_cond_broadcast(l.readers_proceed);
	fi;
}
