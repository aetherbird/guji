/*
 * Appended after runtime_prologue.c and guji_conc.c by
 * test_concurrency_reaper.sh. A delayed TLS destructor makes pthread teardown
 * observable after the language task body and trampoline have both returned.
 */

static pthread_key_t guji_test_key;
static _Atomic int guji_test_destructors_entered = 0;
static _Atomic int guji_test_destructors_done = 0;

static void guji_test_tls_destructor(void* value) {
	(void)value;
	atomic_fetch_add_explicit(
		&guji_test_destructors_entered, 1, memory_order_release);
	struct timespec delay = {0, 50 * 1000 * 1000};
	nanosleep(&delay, NULL);
	atomic_fetch_add_explicit(
		&guji_test_destructors_done, 1, memory_order_release);
}

static void guji_test_task(void* arg) {
	(void)arg;
	if (pthread_setspecific(guji_test_key, (void*)1) != 0) {
		guji_panic("reaper test cannot set thread-specific value");
	}
}

static int guji_test_wait_for(_Atomic int* value, int want) {
	struct timespec delay = {0, 1000 * 1000};
	for (int i = 0; i < 10000; i++) {
		if (atomic_load_explicit(value, memory_order_acquire) >= want) {
			return 1;
		}
		nanosleep(&delay, NULL);
	}
	return 0;
}

int main(void) {
	if (pthread_key_create(&guji_test_key, guji_test_tls_destructor) != 0) {
		fprintf(stderr, "cannot create reaper-test TLS key\n");
		return 1;
	}

	guji_task_spawn(guji_test_task, NULL);
	if (!guji_test_wait_for(&guji_test_destructors_entered, 1)) {
		fprintf(stderr, "first task did not reach pthread teardown\n");
		return 1;
	}

	/* The second spawn must join/reap the first completed task. */
	guji_task_spawn(guji_test_task, NULL);
	if (atomic_load_explicit(
		    &guji_test_destructors_done, memory_order_acquire) < 1) {
		fprintf(stderr, "spawn boundary did not reap first task\n");
		return 1;
	}
	if (!guji_test_wait_for(&guji_test_destructors_entered, 2)) {
		fprintf(stderr, "second task did not reach pthread teardown\n");
		return 1;
	}

	/* With no live language tasks, normal exit must join the final pthread. */
	int code = guji_conc_main_exit(0);
	if (code != 0 ||
	    atomic_load_explicit(
		    &guji_test_destructors_done, memory_order_acquire) != 2) {
		fprintf(stderr, "normal exit did not finish pthread teardown\n");
		return 1;
	}

	pthread_key_delete(guji_test_key);
	puts("concurrency-reaper: PASS");
	return 0;
}
