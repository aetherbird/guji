/* guji concurrency runtime core (spec §17, RFC-003 §7) — Stage H4a.
 *
 * Tasks are language-level fire-and-forget over joinable pthreads (1:1). The
 * task-to-thread mapping is an implementation detail under spec §17.6.
 * Completed pthreads are reaped internally so their resources stay bounded and
 * normal process exit cannot race thread teardown under LeakSanitizer. Channels
 * are the ONE shared object in the system: their control blocks are atomically
 * counted and internally locked, while every guji heap object stays
 * non-atomically counted because no counted object is ever reachable from two
 * tasks (per-task heap discipline, RFC-003 §7.1). Message payloads enter a
 * channel already detached — generated code deep-copies (or move-when-unique
 * transfers) the value graph BEFORE send — so between send and recv a message
 * is exclusively owned by the channel and no refcount is touched concurrently.
 *
 * This file is appended to the generated translation unit after the runtime
 * header (it uses guji_panic) and is exercised directly by the Stage H4a
 * harness tests under ASan/UBSan/LSan and TSan.
 */

#include <pthread.h>
#include <stdatomic.h>
#include <errno.h>
#include <time.h>

/* ---- scheduler accounting (deadlock detection, §17.6; program exit, §17.1) ----
 *
 * guji_sched_mu guards the task counters and the progress counter. Lock order
 * is channel mutex -> scheduler mutex, never the reverse.
 *
 * guji_progress is bumped on every scheduler-visible event (message deposited
 * or taken, close, task spawn/exit, any wake from a blocked wait). Deadlock
 * detection is event-driven with a confirmation window: blocked == live can be
 * TRANSIENTLY true while a signaled task has not yet rescheduled (it is still
 * counted blocked between the broadcast and its wake), so a task that observes
 * the candidate condition re-waits with a timeout and panics only if no
 * progress happened across the window. A real deadlock has no pending wakes,
 * so progress is frozen and the panic fires after one window; a false
 * candidate requires the runnable wakee to stay unscheduled for the whole
 * window, which the kernel scheduler does not do with idle CPUs. */
static pthread_mutex_t guji_sched_mu = PTHREAD_MUTEX_INITIALIZER;
static int64_t guji_live_tasks = 1; /* main counts as a task (§17.6) */
static int64_t guji_blocked_tasks = 0;
static uint64_t guji_progress = 0;
static int guji_main_exiting = 0; /* set by guji_conc_main_exit: the process is
                                     dying by §17.1; suppress deadlock panics
                                     racing the imminent _exit */
static int guji_deadlock_panicking = 0;

#define GUJI_DEADLOCK_CONFIRM_NS (250 * 1000 * 1000)

/* guji_sched_cv lets a task parked in `select` (§17.5) wake on ANY
   scheduler-visible channel event without holding a specific channel's mutex.
   Every guji_progress_bump broadcasts it, so a select waiter watching the
   progress counter is woken by any send deposit, recv take, or close. */
static pthread_cond_t guji_sched_cv;

static void guji_progress_bump(void) {
	pthread_mutex_lock(&guji_sched_mu);
	guji_progress++;
	pthread_cond_broadcast(&guji_sched_cv);
	pthread_mutex_unlock(&guji_sched_mu);
}

/* Called with guji_sched_mu HELD; never returns. */
static void guji_deadlock_panic_locked(void) {
	if (guji_deadlock_panicking) {
		/* another task is already panicking; let it own the message */
		pthread_mutex_unlock(&guji_sched_mu);
		for (;;) {
			pause();
		}
	}
	guji_deadlock_panicking = 1;
	pthread_mutex_unlock(&guji_sched_mu);
	guji_panic("all tasks are blocked — deadlock");
}

/* Channel condvars use CLOCK_MONOTONIC so the deadlock confirmation window is
   immune to wall-clock jumps. */
static pthread_condattr_t guji_cond_attr;
static pthread_once_t guji_cond_attr_once = PTHREAD_ONCE_INIT;
static void guji_cond_attr_init(void) {
	pthread_condattr_init(&guji_cond_attr);
	pthread_condattr_setclock(&guji_cond_attr, CLOCK_MONOTONIC);
	pthread_cond_init(&guji_sched_cv, &guji_cond_attr);
}

/* Block the calling task on cv (mu HELD, standard condvar contract). Wraps
   the wait in blocked-task accounting and runs the deadlock candidate check
   on the transition to blocked. Callers loop on their own condition around
   this, so a timeout that is NOT a confirmed deadlock simply re-checks. */
static void guji_task_block_wait(pthread_cond_t* cv, pthread_mutex_t* mu) {
	int suspect = 0;
	uint64_t seen = 0;
	pthread_mutex_lock(&guji_sched_mu);
	guji_blocked_tasks++;
	if (guji_blocked_tasks == guji_live_tasks && !guji_main_exiting) {
		suspect = 1;
		seen = guji_progress;
	}
	pthread_mutex_unlock(&guji_sched_mu);
	if (!suspect) {
		pthread_cond_wait(cv, mu);
	} else {
		struct timespec ts;
		clock_gettime(CLOCK_MONOTONIC, &ts);
		ts.tv_nsec += GUJI_DEADLOCK_CONFIRM_NS;
		if (ts.tv_nsec >= 1000000000L) {
			ts.tv_sec += 1;
			ts.tv_nsec -= 1000000000L;
		}
		int rc = pthread_cond_timedwait(cv, mu, &ts);
		if (rc == ETIMEDOUT) {
			pthread_mutex_lock(&guji_sched_mu);
			if (guji_blocked_tasks == guji_live_tasks &&
			    guji_progress == seen && !guji_main_exiting) {
				guji_deadlock_panic_locked(); /* never returns */
			}
			pthread_mutex_unlock(&guji_sched_mu);
		}
	}
	pthread_mutex_lock(&guji_sched_mu);
	guji_blocked_tasks--;
	guji_progress++; /* a wake is scheduler-visible */
	pthread_mutex_unlock(&guji_sched_mu);
}

/* ---- tasks (§17.1) ---- */

typedef struct guji_task_boot {
	void (*fn)(void*);
	void* arg;
	pthread_t thread;
	struct guji_task_boot* next_completed;
} guji_task_boot_t;

static guji_task_boot_t* guji_completed_tasks = NULL;

static void* guji_task_trampoline(void* p) {
	guji_task_boot_t* boot = (guji_task_boot_t*)p;
	boot->thread = pthread_self();
	boot->fn(boot->arg);
	/* Task exit can complete an all-blocked deadlock (the remaining tasks ran
	   their candidate checks while this task was still live), so the exiting
	   task runs the confirmation on their behalf. Queue the join record before
	   decrementing live: a zero-live main can then reap every completed task
	   and wait for actual pthread teardown before returning to libc/LSan. */
	pthread_mutex_lock(&guji_sched_mu);
	boot->next_completed = guji_completed_tasks;
	guji_completed_tasks = boot;
	guji_live_tasks--;
	guji_progress++;
	if (guji_live_tasks > 0 && guji_blocked_tasks == guji_live_tasks &&
	    !guji_main_exiting) {
		uint64_t seen = guji_progress;
		pthread_mutex_unlock(&guji_sched_mu);
		struct timespec ts = {0, GUJI_DEADLOCK_CONFIRM_NS};
		nanosleep(&ts, NULL);
		pthread_mutex_lock(&guji_sched_mu);
		if (guji_live_tasks > 0 && guji_blocked_tasks == guji_live_tasks &&
		    guji_progress == seen && !guji_main_exiting) {
			guji_deadlock_panic_locked(); /* never returns */
		}
	}
	pthread_mutex_unlock(&guji_sched_mu);
	return NULL;
}

/* Claim completed join records while holding the scheduler mutex, then join
   outside it: a just-completed trampoline may still need that mutex before
   pthread return. Concurrent reapers claim disjoint lists. */
static void guji_task_reap_completed(void) {
	pthread_mutex_lock(&guji_sched_mu);
	guji_task_boot_t* completed = guji_completed_tasks;
	guji_completed_tasks = NULL;
	pthread_mutex_unlock(&guji_sched_mu);

	while (completed) {
		guji_task_boot_t* next = completed->next_completed;
		if (pthread_join(completed->thread, NULL) != 0) {
			guji_panic("cannot reap task");
		}
		free(completed);
		completed = next;
	}
}

static void guji_task_spawn(void (*fn)(void*), void* arg) {
	/* Bound resources from prior fire-and-forget tasks at every spawn boundary. */
	guji_task_reap_completed();
	guji_task_boot_t* boot = (guji_task_boot_t*)malloc(sizeof(guji_task_boot_t));
	if (!boot) {
		guji_panic("out of memory");
	}
	boot->fn = fn;
	boot->arg = arg;
	boot->next_completed = NULL;
	pthread_mutex_lock(&guji_sched_mu);
	guji_live_tasks++;
	guji_progress++;
	pthread_mutex_unlock(&guji_sched_mu);
	pthread_t t;
	if (pthread_create(&t, NULL, guji_task_trampoline, boot) != 0) {
		guji_panic("cannot spawn task");
	}
}

/* §17.1 program exit: when main returns, the process terminates immediately;
   live tasks are not waited for. Generated main calls this as its epilogue
   when the program uses §17. With tasks still live we must _exit: in-flight
   tasks make atexit handlers (including LeakSanitizer's end-of-process scan)
   racy and meaningless, and fflush preserves piped stdout for the semantic
   oracle — the same structural exemption as guji_panic (RFC-003 §6). With
   every spawned task has finished its language body, reap/join the completed
   pthreads before returning normally so sanitized runs see deterministic
   thread teardown and keep full leak checking. */
static int guji_conc_main_exit(int code) {
	pthread_mutex_lock(&guji_sched_mu);
	guji_main_exiting = 1;
	guji_live_tasks--;
	int remaining = guji_live_tasks > 0;
	pthread_mutex_unlock(&guji_sched_mu);
	if (remaining) {
		fflush(NULL);
		_exit(code);
	}
	guji_task_reap_completed();
	return code;
}

/* ---- channels (§17.2/§17.3, RFC-003 §7.4) ----
 *
 * The control block is the one atomic-rc exception in the system: handles are
 * held by several tasks at once by design. Slots are elem_size-byte values
 * memcpy'd in and out; the element's C type is tracked statically by codegen.
 * elem_drop (NULL for scalar elements) drops ONE detached message in place —
 * the channel owns queued messages exclusively, and the last handle release
 * drops any never-delivered ones.
 *
 * One condvar, broadcast on every state change: simpler waiter logic and
 * uniform deadlock accounting beat wakeup precision at v1's scale. */
typedef struct guji_chan {
	_Atomic uint32_t rc;
	pthread_mutex_t mu;
	pthread_cond_t cv;
	int64_t cap; /* 0 = unbuffered rendezvous */
	size_t elem_size;
	void (*elem_drop)(void* slot);
	char* buf; /* ring of cap slots; the single handoff slot when cap == 0 */
	int64_t len;
	int64_t head;
	int closed;
	int handoff; /* unbuffered: 0 = empty, 1 = value offered, 2 = value taken */
	int64_t recv_waiters; /* blocking recv waiters; used by unbuffered select send */
} guji_chan_t;

static guji_chan_t* guji_chan_new(int64_t cap, size_t elem_size,
                                  void (*elem_drop)(void* slot)) {
	if (cap < 0) {
		guji_panic("channel capacity must be non-negative");
	}
	guji_chan_t* ch = (guji_chan_t*)malloc(sizeof(guji_chan_t));
	if (!ch) {
		guji_panic("out of memory");
	}
	atomic_init(&ch->rc, 1);
	pthread_mutex_init(&ch->mu, NULL);
	pthread_once(&guji_cond_attr_once, guji_cond_attr_init);
	pthread_cond_init(&ch->cv, &guji_cond_attr);
	ch->cap = cap;
	ch->elem_size = elem_size;
	ch->elem_drop = elem_drop;
	ch->buf = (char*)malloc(elem_size * (size_t)(cap > 0 ? cap : 1));
	if (!ch->buf) {
		guji_panic("out of memory");
	}
	ch->len = 0;
	ch->head = 0;
	ch->closed = 0;
	ch->handoff = 0;
	ch->recv_waiters = 0;
	return ch;
}

static guji_chan_t* guji_chan_retain(guji_chan_t* ch) {
	if (ch) {
		atomic_fetch_add_explicit(&ch->rc, 1, memory_order_relaxed);
	}
	return ch;
}

static void guji_chan_release(guji_chan_t* ch) {
	if (!ch) {
		return;
	}
	if (atomic_fetch_sub_explicit(&ch->rc, 1, memory_order_acq_rel) != 1) {
		return;
	}
	/* Last handle anywhere: no task can be blocked on ch (a blocked op holds a
	   handle), so the state is private now. Drop undelivered messages — they
	   were exclusively owned by the channel. */
	if (ch->elem_drop) {
		int64_t ring = ch->cap > 0 ? ch->cap : 1;
		for (int64_t i = 0; i < ch->len; i++) {
			ch->elem_drop(ch->buf + (size_t)((ch->head + i) % ring) * ch->elem_size);
		}
		if (ch->cap == 0 && ch->handoff == 1) {
			ch->elem_drop(ch->buf);
		}
	}
	pthread_cond_destroy(&ch->cv);
	pthread_mutex_destroy(&ch->mu);
	free(ch->buf);
	free(ch);
}

/* send consumes the message in EVERY outcome: on success the channel (then
   the receiver) owns it; on Err(Closed) the runtime drops the caller's
   already-detached copy here, so generated code never branches on ownership.
   Returns 1 = Ok(()), 0 = Err(Closed). */
static int guji_chan_send(guji_chan_t* ch, const void* elem) {
	pthread_mutex_lock(&ch->mu);
	if (ch->cap == 0) {
		/* rendezvous: claim the offer slot, then wait until a receiver takes
		   the value (§17.2: send blocks until another task recvs) */
		while (ch->handoff != 0 && !ch->closed) {
			guji_task_block_wait(&ch->cv, &ch->mu);
		}
		if (ch->closed) {
			goto closed;
		}
		memcpy(ch->buf, elem, ch->elem_size);
		ch->handoff = 1;
		guji_progress_bump();
		pthread_cond_broadcast(&ch->cv);
		while (ch->handoff == 1 && !ch->closed) {
			guji_task_block_wait(&ch->cv, &ch->mu);
		}
		if (ch->handoff == 2) {
			ch->handoff = 0;
			pthread_cond_broadcast(&ch->cv); /* free the slot for other senders */
			pthread_mutex_unlock(&ch->mu);
			return 1;
		}
		/* closed while the offer sat untaken: reclaim the undelivered copy */
		ch->handoff = 0;
		if (ch->elem_drop) {
			ch->elem_drop(ch->buf);
		}
		pthread_mutex_unlock(&ch->mu);
		return 0;
	}
	while (ch->len == ch->cap && !ch->closed) {
		guji_task_block_wait(&ch->cv, &ch->mu);
	}
	if (ch->closed) {
		goto closed;
	}
	memcpy(ch->buf + (size_t)((ch->head + ch->len) % ch->cap) * ch->elem_size,
	       elem, ch->elem_size);
	ch->len++;
	guji_progress_bump();
	pthread_cond_broadcast(&ch->cv);
	pthread_mutex_unlock(&ch->mu);
	return 1;
closed:
	pthread_mutex_unlock(&ch->mu);
	if (ch->elem_drop) {
		ch->elem_drop((void*)(uintptr_t)elem);
	}
	return 0;
}

/* Non-blocking send for `select` (§17.5). Consumes the caller's already-detached
   message in EVERY outcome: delivered, closed, or would-block. Returns
     1  the message was sent (the arm is ready, binds Ok(())),
     0  the channel is closed (the arm is ready, binds Err(Closed)),
    -1  the operation would block (the arm is not ready).
   For unbuffered channels, a send is ready only when a blocking receiver is
   already parked on the channel. Once chosen, it deposits into the handoff slot
   and waits for that guaranteed receiver to take the value, mirroring
   guji_chan_send's rendezvous ownership transfer. */
static int guji_chan_try_send(guji_chan_t* ch, const void* elem) {
	pthread_mutex_lock(&ch->mu);
	if (ch->closed) {
		pthread_mutex_unlock(&ch->mu);
		if (ch->elem_drop) {
			ch->elem_drop((void*)(uintptr_t)elem);
		}
		return 0;
	}
	if (ch->cap == 0) {
		if (ch->handoff != 0 || ch->recv_waiters == 0) {
			pthread_mutex_unlock(&ch->mu);
			if (ch->elem_drop) {
				ch->elem_drop((void*)(uintptr_t)elem);
			}
			return -1;
		}
		memcpy(ch->buf, elem, ch->elem_size);
		ch->handoff = 1;
		guji_progress_bump();
		pthread_cond_broadcast(&ch->cv);
		while (ch->handoff == 1 && !ch->closed) {
			guji_task_block_wait(&ch->cv, &ch->mu);
		}
		if (ch->handoff == 2) {
			ch->handoff = 0;
			pthread_cond_broadcast(&ch->cv);
			pthread_mutex_unlock(&ch->mu);
			return 1;
		}
		ch->handoff = 0;
		pthread_mutex_unlock(&ch->mu);
		if (ch->elem_drop) {
			ch->elem_drop((void*)(uintptr_t)elem);
		}
		return 0;
	}
	if (ch->len == ch->cap) {
		pthread_mutex_unlock(&ch->mu);
		if (ch->elem_drop) {
			ch->elem_drop((void*)(uintptr_t)elem);
		}
		return -1;
	}
	memcpy(ch->buf + (size_t)((ch->head + ch->len) % ch->cap) * ch->elem_size,
	       elem, ch->elem_size);
	ch->len++;
	guji_progress_bump();
	pthread_cond_broadcast(&ch->cv);
	pthread_mutex_unlock(&ch->mu);
	return 1;
}

/* Returns 1 and copies the next message into out (Some), or 0 once the
   channel is closed and drained (None, §17.3). The receiving task adopts the
   message graph as its own. */
static int guji_chan_recv(guji_chan_t* ch, void* out) {
	pthread_mutex_lock(&ch->mu);
	for (;;) {
		if (ch->cap == 0 && ch->handoff == 1) {
			memcpy(out, ch->buf, ch->elem_size);
			ch->handoff = 2;
			guji_progress_bump();
			pthread_cond_broadcast(&ch->cv);
			pthread_mutex_unlock(&ch->mu);
			return 1;
		}
		if (ch->cap > 0 && ch->len > 0) {
			memcpy(out, ch->buf + (size_t)ch->head * ch->elem_size, ch->elem_size);
			ch->head = (ch->head + 1) % ch->cap;
			ch->len--;
			guji_progress_bump();
			pthread_cond_broadcast(&ch->cv);
			pthread_mutex_unlock(&ch->mu);
			return 1;
		}
		if (ch->closed) {
			pthread_mutex_unlock(&ch->mu);
			return 0;
		}
		ch->recv_waiters++;
		guji_progress_bump();
		guji_task_block_wait(&ch->cv, &ch->mu);
		ch->recv_waiters--;
	}
}

/* Non-blocking recv for `select` (§17.5). Never blocks: returns
     1  a value was taken into out (the arm is ready, binds Some),
     0  the channel is closed and drained (the arm is ready, binds None),
    -1  the operation would block (no value, not closed — the arm is not ready).
   When it takes a value it adopts the message graph exactly as guji_chan_recv
   does, so generated select code reuses the same ownership conventions. */
static int guji_chan_try_recv(guji_chan_t* ch, void* out) {
	pthread_mutex_lock(&ch->mu);
	if (ch->cap == 0 && ch->handoff == 1) {
		memcpy(out, ch->buf, ch->elem_size);
		ch->handoff = 2;
		guji_progress_bump();
		pthread_cond_broadcast(&ch->cv);
		pthread_mutex_unlock(&ch->mu);
		return 1;
	}
	if (ch->cap > 0 && ch->len > 0) {
		memcpy(out, ch->buf + (size_t)ch->head * ch->elem_size, ch->elem_size);
		ch->head = (ch->head + 1) % ch->cap;
		ch->len--;
		guji_progress_bump();
		pthread_cond_broadcast(&ch->cv);
		pthread_mutex_unlock(&ch->mu);
		return 1;
	}
	if (ch->closed) {
		pthread_mutex_unlock(&ch->mu);
		return 0;
	}
	pthread_mutex_unlock(&ch->mu);
	return -1;
}

/* Snapshot the scheduler progress counter (§17.5). A select loop reads this
   BEFORE polling its arms, then waits for it to advance: any channel event that
   could make an arm ready bumps the counter, so a state change between the poll
   and the wait cannot be lost (the wait returns immediately when it observes a
   different value). */
static uint64_t guji_progress_snapshot(void) {
	pthread_mutex_lock(&guji_sched_mu);
	uint64_t p = guji_progress;
	pthread_mutex_unlock(&guji_sched_mu);
	return p;
}

/* Park a task whose `select` found no ready arm and has no `else` (§17.5), until
   the scheduler progress counter advances past `seen`. Participates in the same
   blocked-task / deadlock accounting as guji_task_block_wait: an all-blocked
   program with a frozen progress counter is a real deadlock (§17.6) and panics
   after one confirmation window. The caller re-polls every arm on return. */
static void guji_select_wait(uint64_t seen) {
	pthread_once(&guji_cond_attr_once, guji_cond_attr_init);
	pthread_mutex_lock(&guji_sched_mu);
	guji_blocked_tasks++;
	while (guji_progress == seen && !guji_main_exiting) {
		if (guji_blocked_tasks == guji_live_tasks) {
			struct timespec ts;
			clock_gettime(CLOCK_MONOTONIC, &ts);
			ts.tv_nsec += GUJI_DEADLOCK_CONFIRM_NS;
			if (ts.tv_nsec >= 1000000000L) {
				ts.tv_sec += 1;
				ts.tv_nsec -= 1000000000L;
			}
			int rc = pthread_cond_timedwait(&guji_sched_cv, &guji_sched_mu, &ts);
			if (rc == ETIMEDOUT && guji_blocked_tasks == guji_live_tasks &&
			    guji_progress == seen && !guji_main_exiting) {
				guji_deadlock_panic_locked(); /* never returns */
			}
		} else {
			pthread_cond_wait(&guji_sched_cv, &guji_sched_mu);
		}
	}
	guji_blocked_tasks--;
	guji_progress++; /* a wake is scheduler-visible */
	pthread_mutex_unlock(&guji_sched_mu);
}

/* Returns 1 = Ok(()), 0 = Err(Closed) on double close (§17.3: guji returns
   Err where Go panics). Buffered messages already queued remain receivable
   (recv drains, then None). */
static int guji_chan_close(guji_chan_t* ch) {
	pthread_mutex_lock(&ch->mu);
	if (ch->closed) {
		pthread_mutex_unlock(&ch->mu);
		return 0;
	}
	ch->closed = 1;
	guji_progress_bump();
	pthread_cond_broadcast(&ch->cv);
	pthread_mutex_unlock(&ch->mu);
	return 1;
}

/* §15.4 Handle.lines(): eagerly split the remaining stream and enqueue owned
   Str messages into a closed channel.  This mirrors the native compiler's
   deterministic producer and lets ordinary channel iteration consume lines. */
static guji_chan_t* guji_reader_lines(guji_reader_t* r) {
	const char* text = guji_slurp(r);
	int64_t len = 0;
	const char** lines = guji_lines(text, &len);
	guji_chan_t* ch = guji_chan_new(len, sizeof(const char*), guji_chan_drop_str);
	for (int64_t i = 0; i < len; i++) {
		const char* msg = guji_str_copy(lines[i]);
		guji_chan_send(ch, &msg);
	}
	guji_chan_close(ch);
	guji_release(lines);
	guji_release(text);
	return ch;
}
