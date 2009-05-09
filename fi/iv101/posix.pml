#ifdef QUEUED_MUTEXES

  typedef pthread_mutex_t {
  	byte mutex;
  	chan queue = [32] of { pid };
  };
  
  inline pthread_mutex_init(m)
  {
  	m.mutex = 0;
  }
  
  inline pthread_mutex_lock(m)
  {
  	m.queue ! _pid;
  	atomic {
  		m.queue ? [eval(_pid)] && m.mutex == 0;
		m.queue ? _;
  		m.mutex++;
  	}
  }
  
  inline pthread_mutex_unlock(m)
  {
  	assert(m.mutex > 0);
  	m.mutex = 0;
  }

#else

  #define pthread_mutex_t byte
  
  inline pthread_mutex_init(mutex)
  {
  	mutex = 0;
  }
  
  inline pthread_mutex_lock(mutex)
  {
  	atomic{ mutex == 0; mutex++; };
  }
  
  inline pthread_mutex_unlock(mutex)
  {
  	assert(mutex > 0);
  	mutex = 0;
  }

#endif /* QUEUED_MUTEXES */

typedef pthread_cond_t {
	byte enqueued;
	byte ready
};

inline pthread_cond_init(cond_var)
{
	cond_var.enqueued = 0;
	cond_var.ready = 0;
}

inline pthread_cond_wait(cond_var, mutex)
{
	atomic {
		cond_var.enqueued++;
		pthread_mutex_unlock(mutex);
	}

	if
	:: atomic{ (cond_var.ready > 0) -> cond_var.ready--; };

#ifdef COND_WAIT_SPURIOUS_WAKEUPS
	:: atomic{ true ->
			if :: cond_var.enqueued > 0 -> cond_var.enqueued--;
			   :: else -> cond_var.ready--;
			fi;
		};
#endif
	fi;

	pthread_mutex_lock(mutex);
}

inline pthread_cond_signal(cond_var)
{
	atomic {
		if
		:: cond_var.enqueued > 0 ->
			cond_var.ready++;
			cond_var.enqueued--;
		:: else -> skip;
		fi
	}
}

inline pthread_cond_broadcast(cond_var)
{
	atomic {
		if
		:: cond_var.enqueued > 0 ->
			cond_var.ready = cond_var.enqueued;
			cond_var.enqueued = 0;
		:: else -> skip;
		fi
	}
}
