#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <locale.h>
#include <wchar.h>
#include <wctype.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <poll.h>
#include <sys/wait.h>

/* guji_panic terminates the process with no unwinding (RFC-003 §6). _exit
   (not exit) skips atexit handlers -- including LeakSanitizer's end-of-process
   check -- so panicking programs are structurally leak-exempt. The fflush is
   load-bearing: the acceptance gate pipes stdout (fully buffered) and _exit
   does not flush stdio, so without it pre-panic output would be lost and the
   semantic oracle would diverge. */
static void guji_panic(const char* msg) {
	fprintf(stderr, "panic: %s\n", msg);
	fflush(NULL);
	_exit(1);
}

/* guji_exit implements §15.4 exit($code): flush stdout (the acceptance gate
   pipes it fully buffered) then terminate with the caller's code. Like
   guji_panic it uses _exit, not exit, so it skips atexit handlers -- including
   LeakSanitizer's end-of-process check -- making an exiting program leak-exempt
   exactly as a panicking one is (the program is torn down mid-flight, so live
   allocations are not leaks). The code may be 0 (success). */
static void guji_exit(int code) {
	fflush(NULL);
	_exit(code);
}

/* ---- RC core (RFC-003 §2): counted heap objects ----
   Every counted heap object carries a 16-byte header immediately BEFORE its
   payload; guji value pointers point at the payload, so the value ABI is
   unchanged. count is kind-defined (byte length for Str). */
typedef struct {
	uint32_t rc;     /* non-atomic reference count; new objects start at 1 */
	uint16_t kind;   /* index into guji_drop_table */
	uint16_t flags;  /* bit 0: GUJI_IMMORTAL */
	int64_t count;
} guji_obj_t;

#define GUJI_IMMORTAL 0x1u
#define GUJI_REGEX_PRIVATE 0x2u
#define GUJI_HDR(p) (((guji_obj_t*)(uintptr_t)(p)) - 1)

/* Fixed kind numbering is pinned by RFC-003 §2.2; later RC1 slices append
   their kinds (and drop entries) in this order as each becomes allocatable:
   8 MATCH, 9 BUSH, 10 READER, then codegen-generated kinds. */
#define GUJI_KIND_STR 0
#define GUJI_KIND_ARR_SCALAR 1
#define GUJI_KIND_ARR_STR 2
#define GUJI_KIND_ARR_SLICE 3
#define GUJI_KIND_ARR_MAP 4
#define GUJI_KIND_ARR_FN 5
#define GUJI_KIND_ARR_PTR 6
#define GUJI_KIND_ENV 7
#define GUJI_KIND_MATCH 8
#define GUJI_KIND_BUSH 9
#define GUJI_KIND_READER 10

typedef struct {
	void* fn;
	void* env;
	/* Channel transfer must detach a closure environment into the receiving
	   task's heap.  Each capturing lambda supplies a layout-aware copier;
	   non-capturing and top-level functions leave it NULL. */
	void* (*copy_env)(void*);
} guji_fn_t;

/* guji_slice_t is a by-value handle (RFC-003 §2.3), not a heap object: a view
   of counted element storage plus a length. Ownership flows through .data,
   which always points at the START of a guji_arr_alloc payload (the
   no-interior-pointer invariant, RFC-003 §1.3). The element C type is tracked
   statically by codegen. */
typedef struct {
	void* data;
	int64_t len;
} guji_slice_t;

/* guji_map_t models a Map[Str,V] stored as a list element. The keys and vals
   pointers refer to heap arrays copied from a source map; V's C type is tracked
   statically by codegen. */
typedef struct {
	const char** keys;
	void* vals;
	int64_t len;
} guji_map_t;

typedef struct {
	FILE* f;
	int no_close; /* 1 for the shared stdin/stdout/stderr handles: drop frees only the header */
	int writable; /* 1 for a write handle (stdout/stderr/create); 0 for a read handle (open/stdin) */
} guji_reader_t;

static void guji_release(const void* p);
static void* guji_copy_arr(const void* arr);
static void* guji_copy_value(const void* p);
static int guji_str_compare(const char* a, const char* b);
static int guji_str_equal(const char* a, const char* b);

static void guji_drop_str(void* p) {
	free(GUJI_HDR(p));
}

/* Array drops release the slots their kind owns, then free the storage.
   count is the SLOT CAPACITY and guji_arr_alloc zero-fills, so dropping a
   partially filled array releases NULLs (a no-op) for the unfilled tail.
   The element releases encode the eventual ownership contract (container
   stores own +1, RFC-003 §5 rule 4): until the RC1.2 ownership slice emits
   element retains at store sites and storage releases at binding death,
   generated code must not release these arrays. ARR_MAP element drops further
   require counted map storage (RC1.3); ARR_FN / ARR_PTR require counted
   closure envs / boxes (RC1.4). */
static void guji_drop_arr_scalar(void* p) {
	free(GUJI_HDR(p));
}

static void guji_drop_arr_str(void* p) {
	const char** a = (const char**)p;
	int64_t n = GUJI_HDR(p)->count;
	for (int64_t i = 0; i < n; i++) {
		guji_release(a[i]);
	}
	free(GUJI_HDR(p));
}

static void guji_drop_arr_slice(void* p) {
	guji_slice_t* a = (guji_slice_t*)p;
	int64_t n = GUJI_HDR(p)->count;
	for (int64_t i = 0; i < n; i++) {
		guji_release(a[i].data);
	}
	free(GUJI_HDR(p));
}

static void guji_drop_arr_map(void* p) {
	guji_map_t* a = (guji_map_t*)p;
	int64_t n = GUJI_HDR(p)->count;
	for (int64_t i = 0; i < n; i++) {
		guji_release((const void*)a[i].keys);
		guji_release(a[i].vals);
	}
	free(GUJI_HDR(p));
}

static void guji_drop_arr_fn(void* p) {
	guji_fn_t* a = (guji_fn_t*)p;
	int64_t n = GUJI_HDR(p)->count;
	for (int64_t i = 0; i < n; i++) {
		guji_release(a[i].env);
	}
	free(GUJI_HDR(p));
}

static void guji_drop_arr_ptr(void* p) {
	void** a = (void**)p;
	int64_t n = GUJI_HDR(p)->count;
	for (int64_t i = 0; i < n; i++) {
		guji_release(a[i]);
	}
	free(GUJI_HDR(p));
}

/* Closure environments (RFC-003 §2.2): codegen lays out every genv_* struct
   with its owned pointer fields FIRST and allocates with count = their number,
   so one fixed drop releases exactly the owned slots. Str uses its counted
   pointer directly; captured class/enum values use counted one-element user-type
   array boxes, and captured List/Map values use counted ARR_SLICE/ARR_MAP wrapper
   boxes. Their kind-specific drops recursively release the copied fields/backing
   arrays. Unowned Int/Bool/Float slots follow the leading pointers. */
static void guji_drop_env(void* p) {
	const char** a = (const char**)p;
	int64_t n = GUJI_HDR(p)->count;
	for (int64_t i = 0; i < n; i++) {
		guji_release(a[i]);
	}
	free(GUJI_HDR(p));
}

/* Match values (RFC-003 §2.2/§4): text, capture groups, and capture names are
   header-backed Strs. The groups array is ARR_STR and group_names is ARR_PTR,
   so the match owns the complete graph independently of a compiled program. */
typedef struct guji_match {
	const char* text;
	int group_count;
	const char** groups;
	const char** group_names;
} guji_match_t;

static void guji_drop_match(void* p) {
	guji_match_t* m = (guji_match_t*)p;
	guji_release(m->text);
	guji_release(m->groups);
	guji_release(m->group_names);
	free(GUJI_HDR(p));
}

static void guji_drop_reader(void* p) {
	guji_reader_t* r = (guji_reader_t*)p;
	if (r->f != NULL && !r->no_close) {
		fclose(r->f);
	}
	r->f = NULL;
	free(GUJI_HDR(p));
}

/* guji_match_equal compares two Match values by CAPTURE STATE, mirroring
   eval.MatchVal.Equal exactly (spec §13.3): equal iff same whole-match text,
   same group count, and for every group the same participation (a NULL group
   slot is a non-participating capture), the same captured text, and the same
   group name. A NULL group_names array means every group is unnamed. Two
   structurally-identical fresh matches therefore compare equal even though they
   are distinct heap allocations — the native backend must not lower this to
   pointer identity. */
static int64_t guji_match_equal(guji_match_t* a, guji_match_t* b) {
	if (a == b) {
		return 1;
	}
	if (a == NULL || b == NULL) {
		return 0;
	}
	if (!guji_str_equal(a->text, b->text)) {
		return 0;
	}
	if (a->group_count != b->group_count) {
		return 0;
	}
	for (int i = 0; i < a->group_count; i++) {
		const char* ga = a->groups[i];
		const char* gb = b->groups[i];
		if ((ga == NULL) != (gb == NULL)) {
			return 0;
		}
		if (ga != NULL && !guji_str_equal(ga, gb)) {
			return 0;
		}
		const char* na = (a->group_names != NULL) ? a->group_names[i] : NULL;
		const char* nb = (b->group_names != NULL) ? b->group_names[i] : NULL;
		if ((na == NULL) != (nb == NULL)) {
			return 0;
		}
		if (na != NULL && strcmp(na, nb) != 0) {
			return 0;
		}
	}
	return 1;
}

typedef void (*guji_drop_fn)(void*);
/* The drop table is completed after codegen emits generated kinds for boxed
   recursive-enum payloads (RC1.4d). Fixed entries occupy indices 0-10; the array
   definition follows the generated helper declarations. */
static const guji_drop_fn guji_drop_table[];

static void* guji_alloc(uint16_t kind, int64_t count, size_t payload_bytes) {
	guji_obj_t* h = (guji_obj_t*)malloc(sizeof(guji_obj_t) + payload_bytes);
	if (!h) {
		guji_panic("out of memory");
	}
	h->rc = 1;
	h->kind = kind;
	h->flags = 0;
	h->count = count;
	return (void*)(h + 1);
}

static const void* guji_retain(const void* p) {
	if (p && !(GUJI_HDR(p)->flags & GUJI_IMMORTAL)) {
		GUJI_HDR(p)->rc++;
	}
	return p;
}

static void guji_release(const void* p) {
	if (!p) {
		return;
	}
	guji_obj_t* h = GUJI_HDR(p);
	if (h->flags & GUJI_IMMORTAL) {
		return;
	}
	if (--h->rc == 0) {
		guji_drop_table[h->kind]((void*)(uintptr_t)p);
	}
}

/* guji_str_alloc returns a counted Str payload for len bytes + NUL; the
   caller fills it. */
static char* guji_str_alloc(size_t len) {
	return (char*)guji_alloc(GUJI_KIND_STR, (int64_t)len, len + 1);
}

/* guji_str_grow reallocates a uniquely-owned (rc==1) header-backed Str buffer
   to newcap payload bytes; builders use it instead of raw realloc. */
static char* guji_str_grow(char* p, size_t newcap) {
	guji_obj_t* h = (guji_obj_t*)realloc(GUJI_HDR(p), sizeof(guji_obj_t) + newcap);
	if (!h) {
		guji_panic("out of memory");
	}
	return (char*)(h + 1);
}

/* guji_str_copy returns a fresh rc==1 deep copy of a Str value, detached from
   any shared refcount. §17 copy-on-send (RFC-003 §7.3) uses it so a Str sent
   over a channel never shares a count with the sender's per-task heap. The
   header count is the exact byte length, so embedded NULs copy faithfully. */
static const char* guji_str_copy(const char* s) {
	int64_t n = GUJI_HDR(s)->count;
	char* r = guji_str_alloc((size_t)n);
	memcpy(r, s, (size_t)n);
	r[n] = '\0';
	GUJI_HDR(r)->flags |= GUJI_HDR(s)->flags & GUJI_REGEX_PRIVATE;
	return r;
}

static const char* guji_str_from_c(const char* s) {
	size_t n = strlen(s);
	char* r = guji_str_alloc(n);
	memcpy(r, s, n + 1);
	return r;
}

/* Return the width of the well-formed UTF-8 scalar starting at s, or zero when
   the first byte cannot begin a complete scalar encoding within n bytes. The
   checks reject stray continuation bytes, overlong encodings, UTF-16 surrogates,
   and values above U+10FFFF. ASCII includes NUL: Str length is header-counted,
   so U+0000 is data rather than a terminator. */
static size_t guji_utf8_valid_width(const unsigned char* s, size_t n) {
	unsigned char c0, c1;
	if (n == 0) {
		return 0;
	}
	c0 = s[0];
	if (c0 <= 0x7F) {
		return 1;
	}
	if (c0 >= 0xC2 && c0 <= 0xDF) {
		return n >= 2 && s[1] >= 0x80 && s[1] <= 0xBF ? 2 : 0;
	}
	if (c0 >= 0xE0 && c0 <= 0xEF) {
		if (n < 3) {
			return 0;
		}
		c1 = s[1];
		if ((c0 == 0xE0 && (c1 < 0xA0 || c1 > 0xBF))
				|| (c0 == 0xED && (c1 < 0x80 || c1 > 0x9F))
				|| ((c0 != 0xE0 && c0 != 0xED) && (c1 < 0x80 || c1 > 0xBF))
				|| s[2] < 0x80 || s[2] > 0xBF) {
			return 0;
		}
		return 3;
	}
	if (c0 >= 0xF0 && c0 <= 0xF4) {
		if (n < 4) {
			return 0;
		}
		c1 = s[1];
		if ((c0 == 0xF0 && (c1 < 0x90 || c1 > 0xBF))
				|| (c0 == 0xF4 && (c1 < 0x80 || c1 > 0x8F))
				|| ((c0 != 0xF0 && c0 != 0xF4) && (c1 < 0x80 || c1 > 0xBF))
				|| s[2] < 0x80 || s[2] > 0xBF
				|| s[3] < 0x80 || s[3] > 0xBF) {
			return 0;
		}
		return 4;
	}
	return 0;
}

/* Convert untrusted external bytes to Guji's canonical UTF-8 Str form. Valid
   scalar encodings and ASCII bytes (including embedded NUL) are copied exactly.
   Each malformed byte becomes one U+FFFD encoding and consumes one input byte,
   matching utf8.DecodeRune's width-one error rule. The first pass computes an
   overflow-checked exact allocation; the second pass fills the counted payload. */
static const char* guji_str_from_external(const void* bytes, size_t n) {
	static const unsigned char replacement[] = {0xEF, 0xBF, 0xBD};
	const unsigned char* in = (const unsigned char*)bytes;
	size_t i = 0, out_len = 0;
	while (i < n) {
		size_t width = guji_utf8_valid_width(in + i, n - i);
		size_t add = width != 0 ? width : sizeof(replacement);
		if (out_len > SIZE_MAX - add) {
			guji_panic("string is too large");
		}
		out_len += add;
		i += width != 0 ? width : 1;
	}
	if (out_len > (size_t)INT64_MAX || out_len == SIZE_MAX) {
		guji_panic("string is too large");
	}

	char* out = guji_str_alloc(out_len);
	size_t j = 0;
	i = 0;
	while (i < n) {
		size_t width = guji_utf8_valid_width(in + i, n - i);
		if (width != 0) {
			memcpy(out + j, in + i, width);
			i += width;
			j += width;
		} else {
			memcpy(out + j, replacement, sizeof(replacement));
			i++;
			j += sizeof(replacement);
		}
	}
	out[j] = '\0';
	return out;
}

/* guji_chan_drop_str is the elem_drop for Chan[Str]: it releases one detached
   Str message held in a channel slot (an undelivered copy, or a copy rejected
   by send-on-closed). The channel owns these copies exclusively. */
static void guji_chan_drop_str(void* slot) {
	guji_release(*(const char**)slot);
}

/* guji_chan_drop_list is the elem_drop for Chan[List[scalar]]: it releases the
   detached list storage held in an undelivered channel slot. */
static void guji_chan_drop_list(void* slot) {
	guji_slice_t s = *(guji_slice_t*)slot;
	guji_release(s.data);
}

/* guji_chan_drop_map is the elem_drop for Chan[Map[Str, V]]: it releases the
   detached key array (ARR_STR -> guji_drop_arr_str frees each key string) and
   the value array held in an undelivered channel slot. The value array's kind
   tag drives its element release: ARR_STR releases value strings, ARR_SLICE
   releases nested list rows, and ARR_MAP releases nested map rows. */
static void guji_chan_drop_map(void* slot) {
	guji_map_t m = *(guji_map_t*)slot;
	guji_release((const void*)m.keys);
	guji_release(m.vals);
}

/* A function message owns the detached closure environment installed by the
   sender.  The code pointer and environment-copy callback are process-static. */
static void guji_chan_drop_fn(void* slot) {
	guji_fn_t f = *(guji_fn_t*)slot;
	guji_release(f.env);
}

/* guji_arr_alloc returns counted, ZERO-FILLED list element storage for n
   slots of elem_size bytes (at least one slot, so empty lists still hold a
   valid storage pointer). count records the slot capacity: drops walk every
   slot, which is safe because unfilled slots stay NULL/zero. */
static void* guji_arr_alloc(uint16_t kind, size_t elem_size, int64_t n) {
	size_t slots = (size_t)(n > 0 ? n : 1);
	void* p = guji_alloc(kind, (int64_t)slots, elem_size * slots);
	memset(p, 0, elem_size * slots);
	return p;
}

static int64_t guji_arg_count = 0;
static char** guji_arg_values = NULL;

static void guji_set_args(int argc, char** argv) {
	if (argc > 1) {
		guji_arg_count = (int64_t)(argc - 1);
		guji_arg_values = argv + 1;
	} else {
		guji_arg_count = 0;
		guji_arg_values = NULL;
	}
}

static const char** guji_args(int64_t* out_len) {
	const char** out = (const char**)guji_arr_alloc(GUJI_KIND_ARR_STR, sizeof(const char*), guji_arg_count);
	for (int64_t i = 0; i < guji_arg_count; i++) {
		size_t n = strlen(guji_arg_values[i]);
		/* POSIX argv cannot contain NUL, but its bytes need not be valid UTF-8. */
		out[i] = guji_str_from_external(guji_arg_values[i], n);
	}
	*out_len = guji_arg_count;
	return out;
}

/* guji_arr_grow reallocates a uniquely-owned (rc==1) counted array to newcap
   slots, zero-filling the new tail; builders (guji_str_list_append) use it
   instead of raw realloc. */
static void* guji_arr_grow(void* p, size_t elem_size, int64_t newcap) {
	guji_obj_t* h = (guji_obj_t*)realloc(GUJI_HDR(p), sizeof(guji_obj_t) + elem_size * (size_t)newcap);
	if (!h) {
		guji_panic("out of memory");
	}
	int64_t old = h->count;
	h->count = newcap;
	{
		void* q = (void*)(h + 1);
		if (newcap > old) {
			memset((char*)q + elem_size * (size_t)old, 0, elem_size * (size_t)(newcap - old));
		}
		return q;
	}
}

/* Generic deep-copy support for §17 copy-on-send (H4c-gen-a). The runtime
   kind tag carries the element layout, so copy mirrors drop: scalar arrays
   memcpy, Str arrays allocate fresh Strs, and nested List/Map arrays recurse
   through their counted storage pointers. The result is always a fresh rc==1
   graph detached from the source heap. */
static void* guji_copy_value(const void* p) {
	if (!p) {
		return NULL;
	}
	switch (GUJI_HDR(p)->kind) {
	case GUJI_KIND_STR:
		return (void*)guji_str_copy((const char*)p);
	case GUJI_KIND_ARR_SCALAR:
	case GUJI_KIND_ARR_STR:
	case GUJI_KIND_ARR_SLICE:
	case GUJI_KIND_ARR_MAP:
	case GUJI_KIND_ARR_PTR:
		return guji_copy_arr(p);
	default:
		guji_panic("generic copy does not support this heap kind");
		return NULL;
	}
}

static void* guji_copy_arr(const void* arr) {
	if (!arr) {
		return NULL;
	}
	guji_obj_t* h = GUJI_HDR(arr);
	int64_t n = h->count;
	switch (h->kind) {
	case GUJI_KIND_ARR_SCALAR: {
		int64_t* out = (int64_t*)guji_arr_alloc(GUJI_KIND_ARR_SCALAR, sizeof(int64_t), n);
		memcpy(out, arr, sizeof(int64_t) * (size_t)n);
		return out;
	}
	case GUJI_KIND_ARR_STR: {
		const char** src = (const char**)arr;
		const char** out = (const char**)guji_arr_alloc(GUJI_KIND_ARR_STR, sizeof(const char*), n);
		for (int64_t i = 0; i < n; i++) {
			out[i] = src[i] ? guji_str_copy(src[i]) : NULL;
		}
		return (void*)out;
	}
	case GUJI_KIND_ARR_SLICE: {
		guji_slice_t* src = (guji_slice_t*)arr;
		guji_slice_t* out = (guji_slice_t*)guji_arr_alloc(GUJI_KIND_ARR_SLICE, sizeof(guji_slice_t), n);
		for (int64_t i = 0; i < n; i++) {
			out[i].len = src[i].len;
			out[i].data = guji_copy_arr(src[i].data);
		}
		return out;
	}
	case GUJI_KIND_ARR_MAP: {
		guji_map_t* src = (guji_map_t*)arr;
		guji_map_t* out = (guji_map_t*)guji_arr_alloc(GUJI_KIND_ARR_MAP, sizeof(guji_map_t), n);
		for (int64_t i = 0; i < n; i++) {
			out[i].len = src[i].len;
			out[i].keys = (const char**)guji_copy_arr(src[i].keys);
			out[i].vals = guji_copy_arr(src[i].vals);
		}
		return out;
	}
	case GUJI_KIND_ARR_PTR: {
		void** src = (void**)arr;
		void** out = (void**)guji_arr_alloc(GUJI_KIND_ARR_PTR, sizeof(void*), n);
		for (int64_t i = 0; i < n; i++) {
			out[i] = guji_copy_value(src[i]);
		}
		return out;
	}
	default:
		guji_panic("guji_copy_arr expects ARR_* storage");
		return NULL;
	}
}

/* Immortal statics (RFC-003 §3): header-backed, never counted, never freed.
   Helpers that yield a fixed string as a guji VALUE must return one of these,
   never a bare C literal -- releasing a bare literal is heap corruption. */
typedef struct {
	guji_obj_t h;
	char b[8];
} guji_static_str_t;
static const guji_static_str_t guji_empty_str_s = {{0, GUJI_KIND_STR, GUJI_IMMORTAL, 0}, ""};
static const guji_static_str_t guji_true_str_s = {{0, GUJI_KIND_STR, GUJI_IMMORTAL, 4}, "true"};
static const guji_static_str_t guji_false_str_s = {{0, GUJI_KIND_STR, GUJI_IMMORTAL, 5}, "false"};
static const guji_static_str_t guji_nan_str_s = {{0, GUJI_KIND_STR, GUJI_IMMORTAL, 3}, "NaN"};
static const guji_static_str_t guji_pinf_str_s = {{0, GUJI_KIND_STR, GUJI_IMMORTAL, 4}, "+Inf"};
static const guji_static_str_t guji_ninf_str_s = {{0, GUJI_KIND_STR, GUJI_IMMORTAL, 4}, "-Inf"};
#define GUJI_EMPTY_STR (guji_empty_str_s.b)

static int64_t guji_add(int64_t a, int64_t b) {
	int64_t r = a + b;
	if ((a > 0 && b > 0 && r < 0) || (a < 0 && b < 0 && r > 0)) {
		guji_panic("integer overflow");
	}
	return r;
}

static int64_t guji_sub(int64_t a, int64_t b) {
	int64_t r = a - b;
	if ((a >= 0 && b < 0 && r < 0) || (a < 0 && b > 0 && r >= 0)) {
		guji_panic("integer overflow");
	}
	return r;
}

static int64_t guji_mul(int64_t a, int64_t b) {
	if (a == 0 || b == 0) {
		return 0;
	}
	if ((a == INT64_MIN && b == -1) || (b == INT64_MIN && a == -1)) {
		guji_panic("integer overflow");
	}
	int64_t p = a * b;
	if (p / b != a) {
		guji_panic("integer overflow");
	}
	return p;
}

static int64_t guji_div(int64_t a, int64_t b) {
	if (b == 0) {
		guji_panic("integer division by zero");
	}
	if (a == INT64_MIN && b == -1) {
		guji_panic("integer overflow");
	}
	return a / b;
}

static int64_t guji_mod(int64_t a, int64_t b) {
	if (b == 0) {
		guji_panic("integer modulo by zero");
	}
	if (a == INT64_MIN && b == -1) {
		return 0;
	}
	return a % b;
}

static int64_t guji_pow(int64_t a, int64_t b) {
	if (b < 0) {
		guji_panic("negative exponent for integer power");
	}
	int64_t result = 1;
	int64_t base = a;
	int64_t exp = b;
	while (exp > 0) {
		if (exp & 1) {
			result = guji_mul(result, base);
		}
		exp >>= 1;
		if (exp == 0) {
			break;
		}
		base = guji_mul(base, base);
	}
	return result;
}

static int64_t guji_neg(int64_t a) {
	if (a == INT64_MIN) {
		guji_panic("integer overflow");
	}
	return -a;
}

static const char* guji_concat(const char* a, const char* b) {
	size_t la = strlen(a);
	size_t lb = strlen(b);
	char* r = guji_str_alloc(la + lb);
	memcpy(r, a, la);
	memcpy(r + la, b, lb + 1);
	return r;
}

/* guji_str_cat concatenates two header-backed guji Str VALUES using their exact
   byte counts (GUJI_HDR->count), so embedded NUL bytes are preserved -- unlike
   guji_concat, which uses strlen and stops at the first NUL. The interpreter
   builds Go strings of the exact length, so the tilde concat operator and string
   interpolation MUST be NUL-faithful to match it (D1). Both arguments are always
   header-backed guji Str values here (literals are immortal counted statics,
   computed Strs are guji_str_alloc'd), never bare C literals -- the raw-literal
   error builders keep using guji_concat. */
static const char* guji_str_cat(const char* a, const char* b) {
	int64_t la = GUJI_HDR(a)->count;
	int64_t lb = GUJI_HDR(b)->count;
	char* r = guji_str_alloc((size_t)(la + lb));
	if (la > 0) { memcpy(r, a, (size_t)la); }
	if (lb > 0) { memcpy(r + la, b, (size_t)lb); }
	r[la + lb] = '\0';
	return r;
}

/* Build an owned error string from a raw C prefix and a counted Guji Str.
   Unlike guji_concat, this preserves an embedded NUL in the Guji value. */
static const char* guji_prefixed_str(const char* prefix, const char* value) {
	size_t prefix_len = strlen(prefix);
	int64_t value_len = GUJI_HDR(value)->count;
	if (prefix_len > SIZE_MAX - sizeof(guji_obj_t) - 1
			|| value_len < 0
			|| (uint64_t)value_len > SIZE_MAX - sizeof(guji_obj_t) - 1 - prefix_len) {
		guji_panic("string is too large");
	}
	size_t total = prefix_len + (size_t)value_len;
	char* out = guji_str_alloc(total);
	memcpy(out, prefix, prefix_len);
	if (value_len > 0) {
		memcpy(out + prefix_len, value, (size_t)value_len);
	}
	out[total] = '\0';
	return out;
}

static int guji_str_has_nul(const char* s) {
	int64_t n = GUJI_HDR(s)->count;
	return n > 0 && memchr(s, '\0', (size_t)n) != NULL;
}

static const char* guji_substr_n(const char* s, size_t n) {
	char* r = guji_str_alloc(n);
	memcpy(r, s, n);
	r[n] = '\0';
	return r;
}

static void guji_str_list_append(const char*** out, int64_t* len, int64_t* cap, const char* s) {
	if (*len >= *cap) {
		*cap = *cap > 0 ? *cap * 2 : 1;
		*out = (const char**)guji_arr_grow((void*)*out, sizeof(const char*), *cap);
	}
	(*out)[*len] = s;
	*len = guji_add(*len, 1);
}

static const char* guji_find_bytes(const char* haystack, size_t hay_len, const char* needle, size_t needle_len) {
	if (needle_len == 0) return haystack;
	if (hay_len < needle_len) return NULL;
	for (size_t i = 0; i <= hay_len - needle_len; i++) {
		if (memcmp(haystack + i, needle, needle_len) == 0) return haystack + i;
	}
	return NULL;
}

static const char** guji_split(const char* s, const char* sep, int64_t* out_len) {
	int64_t cap = 4;
	const char** out = (const char**)guji_arr_alloc(GUJI_KIND_ARR_STR, sizeof(const char*), cap);
	*out_len = 0;
	size_t total = (size_t)GUJI_HDR(s)->count;
	size_t sep_len = (size_t)GUJI_HDR(sep)->count;
	if (sep_len == 0) {
		/* Empty separator yields each character. Iterate by the Str's COUNTED
		   byte length (GUJI_HDR->count), NOT NUL-termination -- a byte-preserving
		   Str (from read_file/run/...) may carry interior NUL bytes, and the
		   interpreter (Go range over a length-counted string) decodes every one
		   of them (NUL is the valid rune U+0000). A while-(*p) loop would stop
		   at the first NUL and diverge. Clamp a truncated trailing multibyte
		   sequence to the remaining bytes so we never read past the count. */
		const char* p = s;
		const char* end = s + total;
		while (p < end) {
			size_t n;
			unsigned char c = (unsigned char)*p;
			if (c < 0x80) n = 1;
			else if ((c & 0xE0) == 0xC0) n = 2;
			else if ((c & 0xF0) == 0xE0) n = 3;
			else if ((c & 0xF8) == 0xF0) n = 4;
			else n = 1;
			if (n > (size_t)(end - p)) n = (size_t)(end - p);
			guji_str_list_append(&out, out_len, &cap, guji_substr_n(p, n));
			p += n;
		}
		return out;
	}
	const char* start = s;
	const char* end = s + total;
	const char* p = guji_find_bytes(start, (size_t)(end - start), sep, sep_len);
	while (p != NULL) {
		guji_str_list_append(&out, out_len, &cap, guji_substr_n(start, (size_t)(p - start)));
		start = p + sep_len;
		p = guji_find_bytes(start, (size_t)(end - start), sep, sep_len);
	}
	guji_str_list_append(&out, out_len, &cap, guji_substr_n(start, (size_t)(end - start)));
	return out;
}

/* guji_lines splits a header-backed guji Str into chomped lines. It reads the
   exact byte count (GUJI_HDR->count), normalizes CRLF, drops a single trailing
   newline, and splits on '\n' INLINE -- not via guji_split, whose strlen/strstr
   would stop at an embedded NUL. This keeps every byte (including NULs inside a
   line) faithful to the interpreter, which splits a length-counted Go string. */
static const char** guji_lines(const char* s, int64_t* out_len) {
	int64_t n = GUJI_HDR(s)->count;
	char* norm;
	int64_t j = 0;
	if (n == 0) {
		const char** out = (const char**)guji_arr_alloc(GUJI_KIND_ARR_STR, sizeof(const char*), 0);
		*out_len = 0;
		return out;
	}
	norm = (char*)malloc((size_t)n + 1);
	if (!norm) {
		guji_panic("out of memory");
	}
	for (int64_t i = 0; i < n; i++) {
		if (s[i] == '\r') {
			if (i + 1 < n && s[i + 1] == '\n') {
				i++;
			}
			norm[j++] = '\n';
		} else {
			norm[j++] = s[i];
		}
	}
	if (j > 0 && norm[j - 1] == '\n') {
		j--;
	}
	{
		int64_t cap = 4;
		const char** out = (const char**)guji_arr_alloc(GUJI_KIND_ARR_STR, sizeof(const char*), cap);
		int64_t start = 0;
		*out_len = 0;
		for (int64_t i = 0; i < j; i++) {
			if (norm[i] == '\n') {
				guji_str_list_append(&out, out_len, &cap, guji_substr_n(norm + start, (size_t)(i - start)));
				start = i + 1;
			}
		}
		guji_str_list_append(&out, out_len, &cap, guji_substr_n(norm + start, (size_t)(j - start)));
		free(norm);
		return out;
	}
}

static const char* guji_int_str(int64_t v) {
	char buf[32];
	snprintf(buf, sizeof buf, "%lld", (long long)v);
	size_t n = strlen(buf);
	char* r = guji_str_alloc(n);
	memcpy(r, buf, n + 1);
	return r;
}

static const char* guji_bool_str(int64_t v) {
	return v ? guji_true_str_s.b : guji_false_str_s.b;
}

/* Parse a lexer-validated Guji Float literal with the C library's correctly
   rounded decimal conversion.  The evaluator receives literal source text at
   run time, while ordinary native code emits that same text as a C `double`
   constant.  Building the value with repeated Float division can double-round
   (314 / 10 / 10 is below the direct 3.14 conversion), so the compiler lowers
   the evaluator's private eval_float_literal call to this helper.

   Guji permits `_` digit separators and always spells the radix point `.`.
   strtod follows LC_NUMERIC, so translate the radix point to the active
   locale's spelling while copying.  The lexer already proved the remaining
   syntax valid; ERANGE naturally produces the specified IEEE infinity or
   underflow value. */
static double guji_parse_float_literal(const char* text) {
	const char* decimal = localeconv()->decimal_point;
	size_t decimal_len = strlen(decimal);
	size_t text_len = (size_t)GUJI_HDR(text)->count;
	size_t cap = text_len + decimal_len + 1;
	char* clean = (char*)malloc(cap);
	size_t j = 0;
	double value;
	if (!clean) {
		guji_panic("out of memory");
	}
	for (size_t i = 0; i < text_len; i++) {
		if (text[i] == '_') {
			continue;
		}
		if (text[i] == '.') {
			memcpy(clean + j, decimal, decimal_len);
			j += decimal_len;
		} else {
			clean[j++] = text[i];
		}
	}
	clean[j] = '\0';
	value = strtod(clean, NULL);
	free(clean);
	return value;
}

/* guji_float_str renders a double exactly like the interpreter's Go fmt "%g":
   the shortest decimal digit string that round-trips to the same IEEE-754
   value, formatted scientifically iff the decimal exponent is < -4 or >= 6
   (Go strconv's shortest-'g' rule; C's own %g defaults to 6 significant
   digits and a different exponent threshold, so it cannot be used directly). */
static const char* guji_float_str(double v) {
	char buf[64];
	int d, exp;
	const char* ep;
	char* r;
	size_t n;
	if (isnan(v)) {
		return guji_nan_str_s.b;
	}
	if (isinf(v)) {
		return v > 0 ? guji_pinf_str_s.b : guji_ninf_str_s.b;
	}
	for (d = 1; d < 17; d++) {
		snprintf(buf, sizeof buf, "%.*e", d - 1, v);
		if (strtod(buf, NULL) == v) {
			break;
		}
	}
	if (d == 17) {
		snprintf(buf, sizeof buf, "%.16e", v);
	}
	ep = strchr(buf, 'e');
	exp = (int)strtol(ep + 1, NULL, 10);
	if (exp >= -4 && exp < 6) {
		snprintf(buf, sizeof buf, "%.*f", d - 1 - exp > 0 ? d - 1 - exp : 0, v);
	}
	n = strlen(buf);
	r = guji_str_alloc(n);
	memcpy(r, buf, n + 1);
	return r;
}

/* guji_print writes the exact byte count (GUJI_HDR->count) of a header-backed
   guji Str + a newline, via fwrite NOT fputs -- so a Str holding an embedded NUL
   (e.g. a file slurped with read_file) prints every byte, matching the
   interpreter, which writes a length-counted Go string (D1). */
static void guji_print(const char* s) {
	int64_t n = GUJI_HDR(s)->count;
	if (n > 0) { fwrite(s, 1, (size_t)n, stdout); }
	fputc('\n', stdout);
}

/* guji_note implements §15.4 note($value): the display form + newline to STDERR
   instead of stdout. It is print's diagnostic twin -- same rendering, different
   stream -- so the program's stdout (which the acceptance gate compares
   byte-for-byte) stays clean. Byte-count write (not fputs) for NUL fidelity,
   matching guji_print. */
static void guji_note(const char* s) {
	int64_t n = GUJI_HDR(s)->count;
	if (n > 0) { fwrite(s, 1, (size_t)n, stderr); }
	fputc('\n', stderr);
}

/* ---- Generic value display (A-print) ----
   print renders arbitrarily-nested List/Map values by recursing over the
   runtime ARR_* KIND tags, exactly like guji_copy_arr / guji_drop_arr_*. The
   header KIND distinguishes scalar/Str/list/map STORAGE but cannot encode a
   scalar's guji TYPE (Int, Bool, Float, and Unit all live in ARR_SCALAR as
   int64_t/double), so the one thing the tags cannot carry -- the leaf scalar
   kind -- is threaded down as a leafkind argument (uniform along every path of
   a statically typed value). Nesting depth is unbounded: every nested child is
   counted heap storage (guji_arr_alloc), so each step reads the child's header
   to recurse. Output is byte-identical to the interpreter's Value.String()
   (§15.4): lists "[a, b]", maps "{\"k\": v}" with Go %q keys in ascending byte
   order, and Int/Float/Bool/Unit/Str leaves rendered exactly like scalar print. */
#define GUJI_LEAF_INT   0
#define GUJI_LEAF_BOOL  1
#define GUJI_LEAF_FLOAT 2
#define GUJI_LEAF_UNIT  3

typedef struct {
	char* p;
	size_t len;
	size_t cap;
} guji_disp_buf;

static void guji_disp_putn(guji_disp_buf* b, const char* s, size_t n) {
	if (b->len + n + 1 > b->cap) {
		size_t nc = b->cap ? b->cap : 64;
		while (nc < b->len + n + 1) {
			nc *= 2;
		}
		b->p = (char*)realloc(b->p, nc);
		if (!b->p) {
			guji_panic("out of memory");
		}
		b->cap = nc;
	}
	memcpy(b->p + b->len, s, n);
	b->len += n;
	b->p[b->len] = '\0';
}

static void guji_disp_puts(guji_disp_buf* b, const char* s) {
	guji_disp_putn(b, s, strlen(s));
}

/* Render one ARR_SCALAR slot using the static leaf kind. Int/Float reuse the
   scalar-print helpers verbatim so a list element formats identically to a
   bare scalar print; Bool/Unit are fixed words. */
static void guji_disp_scalar(guji_disp_buf* b, const void* data, int64_t i, int leafkind) {
	switch (leafkind) {
	case GUJI_LEAF_BOOL:
		guji_disp_puts(b, ((const int64_t*)data)[i] ? "true" : "false");
		break;
	case GUJI_LEAF_UNIT:
		guji_disp_puts(b, "()");
		break;
	case GUJI_LEAF_FLOAT: {
		const char* s = guji_float_str(((const double*)data)[i]);
		guji_disp_puts(b, s);
		guji_release(s);
		break;
	}
	default: {
		const char* s = guji_int_str(((const int64_t*)data)[i]);
		guji_disp_puts(b, s);
		guji_release(s);
		break;
	}
	}
}

/* Append a Go strconv.Quote-style quoted key, matching the interpreter's "%q"
   for ASCII and printable UTF-8: standard C escapes, control bytes and DEL as
   \xHH, bytes >= 0x80 pass through (printable multibyte UTF-8). */
static void guji_disp_quote(guji_disp_buf* b, const char* s) {
	int64_t n = GUJI_HDR(s)->count;
	guji_disp_puts(b, "\"");
	for (int64_t i = 0; i < n; i++) {
		unsigned char c = (unsigned char)s[i];
		switch (c) {
		case '"':  guji_disp_puts(b, "\\\""); break;
		case '\\': guji_disp_puts(b, "\\\\"); break;
		case '\n': guji_disp_puts(b, "\\n"); break;
		case '\t': guji_disp_puts(b, "\\t"); break;
		case '\r': guji_disp_puts(b, "\\r"); break;
		case '\a': guji_disp_puts(b, "\\a"); break;
		case '\b': guji_disp_puts(b, "\\b"); break;
		case '\f': guji_disp_puts(b, "\\f"); break;
		case '\v': guji_disp_puts(b, "\\v"); break;
		default:
			if (c < 0x20 || c == 0x7f) {
				char tmp[8];
				snprintf(tmp, sizeof tmp, "\\x%02x", c);
				guji_disp_puts(b, tmp);
			} else {
				char ch = (char)c;
				guji_disp_putn(b, &ch, 1);
			}
		}
	}
	guji_disp_puts(b, "\"");
}

static void guji_disp_list(guji_disp_buf* b, const void* data, int64_t len, int kind, int leafkind);
static void guji_disp_map(guji_disp_buf* b, const char** keys, const void* vals, int64_t len, int valkind, int leafkind);

/* Render the element at index i of a kind-tagged array. Lists/maps recurse,
   reading the child's header to discover its own kind (children are always
   counted heap storage). An empty nested collection keeps a valid storage
   pointer, but len==0 short-circuits to the bracket pair so the kind it would
   read is never needed. */
static void guji_disp_elem(guji_disp_buf* b, const void* data, int kind, int64_t i, int leafkind) {
	switch (kind) {
	case GUJI_KIND_ARR_SCALAR:
		guji_disp_scalar(b, data, i, leafkind);
		break;
	case GUJI_KIND_ARR_STR: {
		const char* s = ((const char**)data)[i];
		if (s) {
			guji_disp_putn(b, s, (size_t)GUJI_HDR(s)->count);
		}
		break;
	}
	case GUJI_KIND_ARR_SLICE: {
		guji_slice_t e = ((const guji_slice_t*)data)[i];
		if (e.len > 0) {
			guji_disp_list(b, e.data, e.len, (int)GUJI_HDR(e.data)->kind, leafkind);
		} else {
			guji_disp_puts(b, "[]");
		}
		break;
	}
	case GUJI_KIND_ARR_MAP: {
		guji_map_t m = ((const guji_map_t*)data)[i];
		if (m.len > 0) {
			guji_disp_map(b, m.keys, m.vals, m.len, (int)GUJI_HDR(m.vals)->kind, leafkind);
		} else {
			guji_disp_puts(b, "{}");
		}
		break;
	}
	default:
		guji_panic("display: unsupported list element kind");
	}
}

static void guji_disp_list(guji_disp_buf* b, const void* data, int64_t len, int kind, int leafkind) {
	guji_disp_puts(b, "[");
	for (int64_t i = 0; i < len; i++) {
		if (i) {
			guji_disp_puts(b, ", ");
		}
		guji_disp_elem(b, data, kind, i, leafkind);
	}
	guji_disp_puts(b, "]");
}

/* Map keys use the canonical counted-byte Str order, including embedded NULs. */
static int guji_disp_key_less(const char* a, const char* b) {
	return guji_str_compare(a, b) < 0;
}

static void guji_disp_map(guji_disp_buf* b, const char** keys, const void* vals, int64_t len, int valkind, int leafkind) {
	/* Render entries in ascending key order (the interpreter sorts keys). Build
	   a sorted index permutation via insertion sort -- maps are small. */
	int64_t* ord = (int64_t*)malloc((size_t)len * sizeof(int64_t));
	if (!ord) {
		guji_panic("out of memory");
	}
	for (int64_t i = 0; i < len; i++) {
		int64_t j = i;
		ord[i] = i;
		while (j > 0 && guji_disp_key_less(keys[ord[j]], keys[ord[j - 1]])) {
			int64_t t = ord[j];
			ord[j] = ord[j - 1];
			ord[j - 1] = t;
			j--;
		}
	}
	guji_disp_puts(b, "{");
	for (int64_t i = 0; i < len; i++) {
		int64_t k = ord[i];
		if (i) {
			guji_disp_puts(b, ", ");
		}
		guji_disp_quote(b, keys[k]);
		guji_disp_puts(b, ": ");
		guji_disp_elem(b, vals, valkind, k, leafkind);
	}
	guji_disp_puts(b, "}");
	free(ord);
}

/* guji_disp_finish wraps the built buffer as a FRESH counted Str (the header
   count is the exact byte length, so embedded NULs survive) and frees the
   builder. */
static const char* guji_disp_finish(guji_disp_buf* b) {
	char* r = guji_str_alloc(b->len);
	if (b->len > 0) {
		memcpy(r, b->p, b->len);
	}
	r[b->len] = '\0';
	free(b->p);
	return r;
}

/* Entry points. Codegen passes the top-level kind explicitly because the value
   may be stack-allocated fixed-capacity storage with no header (its kind cannot
   be read at runtime); nested children, always heap, are read from headers.
   Each returns a FRESH counted Str the caller releases. */
static const char* guji_list_str(const void* data, int64_t len, int kind, int leafkind) {
	guji_disp_buf b = {0, 0, 0};
	guji_disp_list(&b, data, len, kind, leafkind);
	return guji_disp_finish(&b);
}

static const char* guji_map_str(const char** keys, const void* vals, int64_t len, int valkind, int leafkind) {
	guji_disp_buf b = {0, 0, 0};
	if (len > 0) {
		guji_disp_map(&b, keys, vals, len, valkind, leafkind);
	} else {
		guji_disp_puts(&b, "{}");
	}
	return guji_disp_finish(&b);
}

/* ---- Generic collection equality (A-compare-equality) ----
   Recurses over ARR_* KIND tags like copy/drop/display. List equality is
   order-sensitive; map equality is key-based and therefore independent of the
   backing storage order. The leafkind parameter supplies the scalar type for
   ARR_SCALAR slots, which the runtime KIND tag cannot distinguish. */
/* Counted unsigned-byte lexicographic comparison. UTF-8 preserves scalar order,
   and byte counts make prefixes and embedded NULs unambiguous. */
static int guji_str_compare(const char* a, const char* b) {
	if (a == b) {
		return 0;
	}
	if (a == NULL || b == NULL) {
		return a == NULL ? -1 : 1;
	}
	int64_t na = GUJI_HDR(a)->count, nb = GUJI_HDR(b)->count;
	int64_t n = na < nb ? na : nb;
	int c = n > 0 ? memcmp(a, b, (size_t)n) : 0;
	if (c < 0) {
		return -1;
	}
	if (c > 0) {
		return 1;
	}
	return na < nb ? -1 : na > nb ? 1 : 0;
}

static int guji_str_equal(const char* a, const char* b) {
	return guji_str_compare(a, b) == 0;
}

static int guji_elem_equal(const void* a, int akind, int64_t ai, const void* b, int bkind, int64_t bi, int leafkind);

static int guji_scalar_equal(const void* a, int64_t ai, const void* b, int64_t bi, int leafkind) {
	switch (leafkind) {
	case GUJI_LEAF_FLOAT:
		return ((const double*)a)[ai] == ((const double*)b)[bi];
	case GUJI_LEAF_UNIT:
		return 1;
	default:
		return ((const int64_t*)a)[ai] == ((const int64_t*)b)[bi];
	}
}

static int guji_list_equal(const void* a, int64_t alen, int akind, const void* b, int64_t blen, int bkind, int leafkind) {
	if (alen != blen) {
		return 0;
	}
	if (alen == 0) {
		return 1;
	}
	if (akind != bkind) {
		return 0;
	}
	for (int64_t i = 0; i < alen; i++) {
		if (!guji_elem_equal(a, akind, i, b, bkind, i, leafkind)) {
			return 0;
		}
	}
	return 1;
}

static int guji_map_equal(const char** akeys, const void* avals, int64_t alen, int avkind, const char** bkeys, const void* bvals, int64_t blen, int bvkind, int leafkind) {
	if (alen != blen) {
		return 0;
	}
	if (alen == 0) {
		return 1;
	}
	if (avkind != bvkind) {
		return 0;
	}
	for (int64_t i = 0; i < alen; i++) {
		int found = 0;
		for (int64_t j = 0; j < blen; j++) {
			if (guji_str_equal(akeys[i], bkeys[j])) {
				if (!guji_elem_equal(avals, avkind, i, bvals, bvkind, j, leafkind)) {
					return 0;
				}
				found = 1;
				break;
			}
		}
		if (!found) {
			return 0;
		}
	}
	return 1;
}

static int guji_elem_equal(const void* a, int akind, int64_t ai, const void* b, int bkind, int64_t bi, int leafkind) {
	if (akind != bkind) {
		return 0;
	}
	switch (akind) {
	case GUJI_KIND_ARR_SCALAR:
		return guji_scalar_equal(a, ai, b, bi, leafkind);
	case GUJI_KIND_ARR_STR:
		return guji_str_equal(((const char* const*)a)[ai], ((const char* const*)b)[bi]);
	case GUJI_KIND_ARR_SLICE: {
		guji_slice_t av = ((const guji_slice_t*)a)[ai];
		guji_slice_t bv = ((const guji_slice_t*)b)[bi];
		int avkind = av.len > 0 ? (int)GUJI_HDR(av.data)->kind : GUJI_KIND_ARR_SCALAR;
		int bvkind = bv.len > 0 ? (int)GUJI_HDR(bv.data)->kind : GUJI_KIND_ARR_SCALAR;
		return guji_list_equal(av.data, av.len, avkind, bv.data, bv.len, bvkind, leafkind);
	}
	case GUJI_KIND_ARR_MAP: {
		guji_map_t av = ((const guji_map_t*)a)[ai];
		guji_map_t bv = ((const guji_map_t*)b)[bi];
		int avkind = av.len > 0 ? (int)GUJI_HDR(av.vals)->kind : GUJI_KIND_ARR_SCALAR;
		int bvkind = bv.len > 0 ? (int)GUJI_HDR(bv.vals)->kind : GUJI_KIND_ARR_SCALAR;
		return guji_map_equal(av.keys, av.vals, av.len, avkind, bv.keys, bv.vals, bv.len, bvkind, leafkind);
	}
	default:
		guji_panic("equality: unsupported collection element kind");
		return 0;
	}
}

static const char* guji_trim(const char* s) {
	const char* start = s;
	mbstate_t st;
	memset(&st, 0, sizeof(st));
	while (*start) {
		wchar_t wc;
		size_t n = mbrtowc(&wc, start, strlen(start), &st);
		if (n == (size_t)-1 || n == (size_t)-2 || n == 0) break;
		if (!iswspace(wc)) break;
		start += n;
	}
	if (*start == '\0') return GUJI_EMPTY_STR;
	const char* end = start;
	const char* p = start;
	memset(&st, 0, sizeof(st));
	while (*p) {
		wchar_t wc;
		size_t n = mbrtowc(&wc, p, strlen(p), &st);
		if (n == (size_t)-1 || n == (size_t)-2 || n == 0) break;
		if (!iswspace(wc)) end = p + n;
		p += n;
	}
	size_t len = (size_t)(end - start);
	char* out = guji_str_alloc(len);
	memcpy(out, start, len);
	out[len] = '\0';
	return out;
}

static const char* guji_case(const char* s, int upper) {
	size_t in_len = strlen(s);
	/* allocated at worst-case capacity; the header count is set to the
	   rendered length below */
	char* out = (char*)guji_alloc(GUJI_KIND_STR, 0, in_len * 4 + 1);
	char* q = out;
	const char* p = s;
	mbstate_t st;
	memset(&st, 0, sizeof(st));
	while (*p) {
		wchar_t wc;
		size_t n = mbrtowc(&wc, p, strlen(p), &st);
		if (n == (size_t)-1 || n == (size_t)-2 || n == 0) break;
		wc = upper ? towupper(wc) : towlower(wc);
		int wn = wcrtomb(q, wc, NULL);
		if (wn < 0) { *q = *p; wn = 1; }
		q += wn;
		p += n;
	}
	*q = '\0';
	GUJI_HDR(out)->count = (int64_t)(q - out);
	return out;
}

static const char* guji_upper(const char* s) { return guji_case(s, 1); }
static const char* guji_lower(const char* s) { return guji_case(s, 0); }

/* guji_parse_int parses a base-10 integer from a string, trimming ASCII
   whitespace. It returns NULL on success (and sets *out_ok) or an error
   string on failure. The error message matches the interpreter:
   "invalid integer: <original>". */
static const char* guji_parse_int(const char* s, int64_t* out_ok) {
	const char* p = s;
	while (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r' || *p == '\f' || *p == '\v') p++;
	const char* q = p + strlen(p);
	while (q > p && (*(q - 1) == ' ' || *(q - 1) == '\t' || *(q - 1) == '\n' || *(q - 1) == '\r' || *(q - 1) == '\f' || *(q - 1) == '\v')) q--;
	if (p == q) {
		*out_ok = 0;
		return guji_concat("invalid integer: ", s);
	}
	int neg = 0;
	if (*p == '-') { neg = 1; p++; }
	else if (*p == '+') { p++; }
	if (p == q) {
		*out_ok = 0;
		return guji_concat("invalid integer: ", s);
	}
	int64_t val = 0;
	for (const char* r = p; r < q; r++) {
		if (*r < '0' || *r > '9') {
			*out_ok = 0;
			return guji_concat("invalid integer: ", s);
		}
		int digit = *r - '0';
		if (val > (INT64_MAX - digit) / 10) {
			*out_ok = 0;
			return guji_concat("invalid integer: ", s);
		}
		val = val * 10 + digit;
	}
	if (neg) {
		if (val > (uint64_t)INT64_MAX + 1) {
			*out_ok = 0;
			return guji_concat("invalid integer: ", s);
		}
		val = -val;
	}
	*out_ok = val;
	return NULL;
}

/* guji_read_file reads the entire contents of the file at the given path with no
   chomping and terminators intact, then converts malformed UTF-8 bytes to U+FFFD
   before exposing the text as a Str. Valid UTF-8 bytes, including NUL, remain
   unchanged. It returns NULL on success -- setting *out_ok to a fresh owned
   counted Str -- or an owned error string on failure (§15.4). The error message
   is intentionally OS-reason-free
   ("cannot read file: <path>") so the native binary and the interpreter produce
   byte-identical output: Go's *os.PathError text and C strerror differ, which
   would break the differential gate. A chunked read loop (not fseek/ftell) is
   used so non-seekable inputs like /dev/null read correctly; ferror after the
   loop distinguishes EOF from a real read error (e.g. a directory), matching
   os.ReadFile's error-on-directory. */
static const char* guji_read_file(const char* path, const char** out_ok) {
	if (guji_str_has_nul(path)) {
		return guji_prefixed_str("cannot read file: ", path);
	}
	FILE* f = fopen(path, "rb");
	if (!f) {
		return guji_concat("cannot read file: ", path);
	}
	size_t cap = 4096, len = 0;
	char* buf = (char*)malloc(cap);
	if (!buf) { fclose(f); guji_panic("out of memory"); }
	for (;;) {
		if (len == cap) {
			cap *= 2;
			char* nb = (char*)realloc(buf, cap);
			if (!nb) { free(buf); fclose(f); guji_panic("out of memory"); }
			buf = nb;
		}
		size_t got = fread(buf + len, 1, cap - len, f);
		len += got;
		if (got == 0) { break; }
	}
	if (ferror(f)) {
		free(buf);
		fclose(f);
		return guji_concat("cannot read file: ", path);
	}
	fclose(f);
	const char* r = guji_str_from_external(buf, len);
	free(buf);
	*out_ok = r;
	return NULL;
}

static const char* guji_open(const char* path, guji_reader_t** out_ok) {
	if (guji_str_has_nul(path)) {
		return guji_prefixed_str("cannot open file: ", path);
	}
	FILE* f = fopen(path, "rb");
	if (!f) {
		return guji_concat("cannot open file: ", path);
	}
	guji_reader_t* r = (guji_reader_t*)guji_alloc(GUJI_KIND_READER, 0, sizeof(guji_reader_t));
	r->f = f;
	r->no_close = 0;
	r->writable = 0;
	*out_ok = r;
	return NULL;
}

static const char* guji_create(const char* path, guji_reader_t** out_ok) {
	if (guji_str_has_nul(path)) {
		return guji_prefixed_str("cannot create file: ", path);
	}
	FILE* f = fopen(path, "wb");
	if (!f) {
		return guji_concat("cannot create file: ", path);
	}
	guji_reader_t* r = (guji_reader_t*)guji_alloc(GUJI_KIND_READER, 0, sizeof(guji_reader_t));
	r->f = f;
	r->no_close = 0;
	r->writable = 1;
	*out_ok = r;
	return NULL;
}

/* guji_write_file truncates-or-creates the file at path and writes content
   VERBATIM (the counted Str length, so embedded NULs are preserved), then closes
   it. Returns NULL on success or an owned, OS-reason-free error string
   ("cannot write file: <path>"), mirroring write_file in the interpreter and the
   Section 15.4 fixed-message rule that keeps both engines byte-identical. */
static const char* guji_write_file(const char* path, const char* content) {
	if (guji_str_has_nul(path)) {
		return guji_prefixed_str("cannot write file: ", path);
	}
	FILE* f = fopen(path, "wb");
	if (!f) {
		return guji_concat("cannot write file: ", path);
	}
	int64_t n = GUJI_HDR(content)->count;
	if (n > 0 && fwrite(content, 1, (size_t)n, f) != (size_t)n) {
		fclose(f);
		return guji_concat("cannot write file: ", path);
	}
	if (fclose(f) != 0) {
		return guji_concat("cannot write file: ", path);
	}
	return NULL;
}

/* guji_append_file appends content VERBATIM to the end of the file at path,
   creating it if absent and never truncating it, then closes it. Returns NULL on
   success or an owned "cannot append file: <path>" error string on failure (same
   fixed-message rule as guji_write_file). */
static const char* guji_append_file(const char* path, const char* content) {
	if (guji_str_has_nul(path)) {
		return guji_prefixed_str("cannot append file: ", path);
	}
	FILE* f = fopen(path, "ab");
	if (!f) {
		return guji_concat("cannot append file: ", path);
	}
	int64_t n = GUJI_HDR(content)->count;
	if (n > 0 && fwrite(content, 1, (size_t)n, f) != (size_t)n) {
		fclose(f);
		return guji_concat("cannot append file: ", path);
	}
	if (fclose(f) != 0) {
		return guji_concat("cannot append file: ", path);
	}
	return NULL;
}

/* guji_run implements §15.6 run($cmd, $args): spawn $cmd PATH-resolved (NO
   shell, like execvp), with argv [$cmd] ++ $args, wait for it to finish, and
   capture its standard output and standard error SEPARATELY without chomping.
   Valid UTF-8 bytes and interior NULs are preserved; each malformed UTF-8 byte
   is converted to U+FFFD before the capture becomes a Str. It returns NULL
   whenever the process ACTUALLY RAN (any exit code, including non-zero), filling *out_exit
   with the child's exit status (128 + signal when killed by a signal -- the
   conventional shell encoding, matching the interpreter's procExitCode) and
   *out_stdout / *out_stderr with the captured bytes. It returns an owned,
   OS-reason-free error Str ("cannot run command: <cmd>") ONLY when the process
   could not be spawned (ENOENT / permission denied); the message names the
   command but not the OS reason so it is byte-identical to the interpreter
   (§15.6, same fixed-message rule as guji_read_file). A close-on-exec status
   pipe lets the parent tell a failed exec in the child apart from a successful
   spawn, and stdout/stderr are drained concurrently with poll() so a child that
   fills one pipe buffer while the parent reads the other cannot deadlock. */
static void guji_run_close2(int a, int b) { close(a); close(b); }

static void guji_run_grow(char** buf, size_t* cap, size_t need) {
	if (need <= *cap) {
		return;
	}
	size_t nc = *cap;
	while (nc < need) {
		nc *= 2;
	}
	char* nb = (char*)realloc(*buf, nc);
	if (!nb) {
		free(*buf);
		guji_panic("out of memory");
	}
	*buf = nb;
	*cap = nc;
}

static const char* guji_run(const char* cmd, const char** extra, int64_t nextra,
                            int64_t* out_exit, const char** out_stdout, const char** out_stderr) {
	int out_pipe[2], err_pipe[2], exec_pipe[2];
	if (guji_str_has_nul(cmd)) {
		return guji_prefixed_str("cannot run command: ", cmd);
	}
	for (int64_t i = 0; i < nextra; i++) {
		if (guji_str_has_nul(extra[i])) {
			return guji_prefixed_str("cannot run command: ", cmd);
		}
	}
	if (pipe(out_pipe) != 0) {
		return guji_concat("cannot run command: ", cmd);
	}
	if (pipe(err_pipe) != 0) {
		guji_run_close2(out_pipe[0], out_pipe[1]);
		return guji_concat("cannot run command: ", cmd);
	}
	if (pipe(exec_pipe) != 0) {
		guji_run_close2(out_pipe[0], out_pipe[1]);
		guji_run_close2(err_pipe[0], err_pipe[1]);
		return guji_concat("cannot run command: ", cmd);
	}
	/* The exec-status pipe's write end closes automatically on a successful
	   exec (parent reads EOF); a failed exec writes errno and the child exits. */
	fcntl(exec_pipe[1], F_SETFD, FD_CLOEXEC);

	int64_t argc = nextra > 0 ? nextra : 0;
	char** argv = (char**)malloc(sizeof(char*) * (size_t)(argc + 2));
	if (!argv) {
		guji_run_close2(out_pipe[0], out_pipe[1]);
		guji_run_close2(err_pipe[0], err_pipe[1]);
		guji_run_close2(exec_pipe[0], exec_pipe[1]);
		guji_panic("out of memory");
	}
	argv[0] = (char*)cmd;
	for (int64_t i = 0; i < argc; i++) {
		argv[i + 1] = (char*)extra[i];
	}
	argv[argc + 1] = NULL;

	pid_t pid = fork();
	if (pid < 0) {
		free(argv);
		guji_run_close2(out_pipe[0], out_pipe[1]);
		guji_run_close2(err_pipe[0], err_pipe[1]);
		guji_run_close2(exec_pipe[0], exec_pipe[1]);
		return guji_concat("cannot run command: ", cmd);
	}
	if (pid == 0) {
		/* child: wire stdout/stderr to the pipes, then exec. */
		dup2(out_pipe[1], STDOUT_FILENO);
		dup2(err_pipe[1], STDERR_FILENO);
		close(out_pipe[0]);
		close(out_pipe[1]);
		close(err_pipe[0]);
		close(err_pipe[1]);
		close(exec_pipe[0]);
		execvp(cmd, argv);
		int e = errno;
		ssize_t w = write(exec_pipe[1], &e, sizeof(e));
		(void)w;
		_exit(127);
	}

	/* parent */
	free(argv);
	close(out_pipe[1]);
	close(err_pipe[1]);
	close(exec_pipe[1]);

	int exec_errno = 0;
	ssize_t er = read(exec_pipe[0], &exec_errno, sizeof(exec_errno));
	close(exec_pipe[0]);
	if (er > 0) {
		/* exec failed in the child: reap it and report a spawn failure. */
		close(out_pipe[0]);
		close(err_pipe[0]);
		int st = 0;
		while (waitpid(pid, &st, 0) < 0 && errno == EINTR) {
		}
		return guji_concat("cannot run command: ", cmd);
	}

	size_t ocap = 4096, olen = 0;
	size_t ecap = 4096, elen = 0;
	char* obuf = (char*)malloc(ocap);
	char* ebuf = (char*)malloc(ecap);
	if (!obuf || !ebuf) {
		guji_panic("out of memory");
	}
	int odone = 0, edone = 0;
	while (!odone || !edone) {
		struct pollfd pfds[2];
		int slot_out = -1, slot_err = -1, nf = 0;
		if (!odone) {
			pfds[nf].fd = out_pipe[0];
			pfds[nf].events = POLLIN;
			pfds[nf].revents = 0;
			slot_out = nf;
			nf++;
		}
		if (!edone) {
			pfds[nf].fd = err_pipe[0];
			pfds[nf].events = POLLIN;
			pfds[nf].revents = 0;
			slot_err = nf;
			nf++;
		}
		int pr = poll(pfds, (nfds_t)nf, -1);
		if (pr < 0) {
			if (errno == EINTR) {
				continue;
			}
			break;
		}
		if (slot_out >= 0 && (pfds[slot_out].revents & (POLLIN | POLLHUP | POLLERR))) {
			char chunk[4096];
			ssize_t r = read(out_pipe[0], chunk, sizeof(chunk));
			if (r > 0) {
				guji_run_grow(&obuf, &ocap, olen + (size_t)r);
				memcpy(obuf + olen, chunk, (size_t)r);
				olen += (size_t)r;
			} else if (r == 0) {
				odone = 1;
			} else if (errno != EINTR) {
				odone = 1;
			}
		}
		if (slot_err >= 0 && (pfds[slot_err].revents & (POLLIN | POLLHUP | POLLERR))) {
			char chunk[4096];
			ssize_t r = read(err_pipe[0], chunk, sizeof(chunk));
			if (r > 0) {
				guji_run_grow(&ebuf, &ecap, elen + (size_t)r);
				memcpy(ebuf + elen, chunk, (size_t)r);
				elen += (size_t)r;
			} else if (r == 0) {
				edone = 1;
			} else if (errno != EINTR) {
				edone = 1;
			}
		}
	}
	close(out_pipe[0]);
	close(err_pipe[0]);

	int status = 0;
	while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {
	}
	int64_t code;
	if (WIFSIGNALED(status)) {
		code = 128 + WTERMSIG(status);
	} else if (WIFEXITED(status)) {
		code = WEXITSTATUS(status);
	} else {
		code = 0;
	}

	const char* so = guji_str_from_external(obuf, olen);
	free(obuf);
	const char* se = guji_str_from_external(ebuf, elen);
	free(ebuf);

	*out_exit = code;
	*out_stdout = so;
	*out_stderr = se;
	return NULL;
}

/* guji_stdin returns a fresh counted Handle wrapping the process stdin. It is
   marked no_close so dropping the handle frees only its header and never closes
   the shared stream — mirroring the interpreter, which reads from ev.in without
   closing it. Each stdin reference makes a new wrapper over the same FILE*, so
   sequential reads advance one shared stream, exactly as the interpreter does. */
static guji_reader_t* guji_stdin(void) {
	guji_reader_t* r = (guji_reader_t*)guji_alloc(GUJI_KIND_READER, 0, sizeof(guji_reader_t));
	r->f = stdin;
	r->no_close = 1;
	r->writable = 0;
	return r;
}

/* guji_stdout / guji_stderr return a fresh counted WRITE Handle wrapping the
   process stdout / stderr (no_close: drop frees only the header). Mirrors the
   interpreter's stdout/stderr HandleVals, which carry a writer and no reader. */
static guji_reader_t* guji_stdout(void) {
	guji_reader_t* r = (guji_reader_t*)guji_alloc(GUJI_KIND_READER, 0, sizeof(guji_reader_t));
	r->f = stdout;
	r->no_close = 1;
	r->writable = 1;
	return r;
}

static guji_reader_t* guji_stderr(void) {
	guji_reader_t* r = (guji_reader_t*)guji_alloc(GUJI_KIND_READER, 0, sizeof(guji_reader_t));
	r->f = stderr;
	r->no_close = 1;
	r->writable = 1;
	return r;
}

/* guji_write implements the §15.4 $h.write($s) method: write the raw bytes of s
   to a writable Handle with NO trailing newline. Writing to a read handle (one
   with writable == 0, e.g. an open'd file or stdin) is a runtime error, matching
   the interpreter exactly. Writes the exact byte count (GUJI_HDR->count) via
   fwrite NOT fputs, so a Str holding an embedded NUL (e.g. a file slurped with
   read_file) is written verbatim, matching the interpreter's length-counted
   write (same fidelity as guji_print -- D1). */
static void guji_write(guji_reader_t* h, const char* s) {
	if (h == NULL || !h->writable) {
		guji_panic("write: handle is not writable");
	}
	if (s != NULL) {
		int64_t n = GUJI_HDR(s)->count;
		if (n > 0 && fwrite(s, 1, (size_t)n, h->f) != (size_t)n) {
			guji_panic("write failed");
		}
	}
	if (fflush(h->f) == EOF) {
		guji_panic("write failed");
	}
}

static const char* guji_slurp(guji_reader_t* r) {
	if (r != NULL && r->writable) {
		/* A write-only handle (stdout/stderr/create) has no reader. Match the
		   interpreter: slurping it is a runtime error, not a silent empty Str. */
		guji_panic("slurp: handle is not readable");
	}
	if (r == NULL || r->f == NULL) {
		return GUJI_EMPTY_STR;
	}
	size_t cap = 4096, len = 0;
	char* buf = (char*)malloc(cap);
	if (!buf) { guji_panic("out of memory"); }
	for (;;) {
		if (len == cap) {
			cap *= 2;
			char* nb = (char*)realloc(buf, cap);
			if (!nb) { free(buf); guji_panic("out of memory"); }
			buf = nb;
		}
		size_t got = fread(buf + len, 1, cap - len, r->f);
		len += got;
		if (got == 0) { break; }
	}
	if (ferror(r->f)) {
		free(buf);
		guji_panic("slurp failed");
	}
	/* A Handle is text ingress: preserve valid bytes and NUL, and convert each
	   malformed UTF-8 byte before constructing the returned Str. */
	const char* out = guji_str_from_external(buf, len);
	free(buf);
	return out;
}

/* guji_map_order fills order[0..len) with map-entry indices sorted by key
   (stable insertion sort over counted Str bytes), so map iteration visits keys
   in deterministic lexicographic order even when a key contains NUL. */
static void guji_map_order(const char** keys, int64_t len, int64_t* order) {
	int64_t i, j;
	for (i = 0; i < len; i++) {
		order[i] = i;
	}
	for (i = 1; i < len; i++) {
		int64_t cur = order[i];
		j = i - 1;
		while (j >= 0 && guji_str_compare(keys[order[j]], keys[cur]) > 0) {
			order[j + 1] = order[j];
			j--;
		}
		order[j + 1] = cur;
	}
}

/* guji_match_cap resolves a named capture at runtime: the group's text, or
   NULL when the name is unknown or the group did not participate. */
static const char* guji_match_cap(guji_match_t* m, const char* name) {
	if (m->group_names == NULL) {
		return NULL;
	}
	for (int i = 0; i < m->group_count; i++) {
		if (m->group_names[i] != NULL && strcmp(m->group_names[i], name) == 0) {
			return m->groups[i];
		}
	}
	return NULL;
}

/* guji_buf_append appends n bytes to a header-backed Str buffer (allocated
   with guji_alloc(GUJI_KIND_STR, ...)); never pass it a raw malloc buffer. */
static char* guji_buf_append(char* out, size_t* out_len, size_t* cap, const char* s, size_t n) {
	if (*out_len + n + 1 > *cap) {
		*cap = (*out_len + n + 1) * 2;
		out = guji_str_grow(out, *cap);
	}
	memcpy(out + *out_len, s, n);
	*out_len += n;
	out[*out_len] = '\0';
	return out;
}



/* guji_bush_t is a grammar parse-tree node (§14.2): the production name, the
   matched text, and the captured direct sub-nodes in match order (cap_names[i]
   is the referenced production's name). Bushes are counted heap objects
   (GUJI_KIND_BUSH, RC1.4e): a bush owns its text (+1 header-backed Str) and
   one +1 on each captured child. name and the cap_names ELEMENTS are raw
   static C literals with NO object header — they must never be released. */
typedef struct guji_bush {
	const char* name;
	const char* text;
	int64_t ncaps;
	const char** cap_names;
	struct guji_bush** caps;
} guji_bush_t;

static const char* guji_substr(const char* s, int64_t start, int64_t end) {
	int64_t n = end - start;
	char* r = guji_str_alloc((size_t)n);
	memcpy(r, s + start, n);
	r[n] = '\0';
	return r;
}

/* guji_bush_new takes ownership of text (the caller's fresh +1 from
   guji_substr) and of the +1 each child carries when the caller fills caps.
   cap_names is ARR_PTR with header count 0 so its drop frees the storage but
   never touches the raw-literal elements; caps is ARR_PTR with header count
   ncaps so its drop releases exactly the filled children. */
static guji_bush_t* guji_bush_new(const char* name, const char* text, int64_t ncaps) {
	guji_bush_t* b = (guji_bush_t*)guji_alloc(GUJI_KIND_BUSH, 0, sizeof(guji_bush_t));
	b->name = name;
	b->text = text;
	b->ncaps = ncaps;
	b->cap_names = (const char**)guji_alloc(GUJI_KIND_ARR_PTR, 0, sizeof(const char*) * (size_t)(ncaps > 0 ? ncaps : 1));
	b->caps = (guji_bush_t**)guji_alloc(GUJI_KIND_ARR_PTR, ncaps, sizeof(guji_bush_t*) * (size_t)(ncaps > 0 ? ncaps : 1));
	return b;
}

/* Dropping a bush cascades into its children through the caps ARR_PTR drop
   (count = ncaps). b->name stays untouched: it is a raw static literal. */
static void guji_drop_bush(void* p) {
	guji_bush_t* b = (guji_bush_t*)p;
	guji_release(b->text);
	guji_release(b->caps);
	guji_release(b->cap_names);
	free(GUJI_HDR(p));
}

/* guji_bush_cap returns the first captured sub-node with the given name, or
   NULL — the runtime behind the $b<name> accessor. */
static guji_bush_t* guji_bush_cap(guji_bush_t* b, const char* name) {
	int64_t i;
	for (i = 0; i < b->ncaps; i++) {
		if (strcmp(b->cap_names[i], name) == 0) {
			return b->caps[i];
		}
	}
	return NULL;
}

/* guji_bush_copy returns a fresh rc==1 deep copy of a Bush parse tree,
   detached from any shared refcount. §17 copy-on-send uses it for
   Option[Bush] channel elements: text and every captured child are copied
   recursively, cap_names/caps arrays are fresh, and name/cap_names elements
   point at the same raw static production-name literals (never counted). */
static guji_bush_t* guji_bush_copy(guji_bush_t* src) {
	if (src == NULL) {
		return NULL;
	}
	int64_t n = src->ncaps;
	guji_bush_t* b = (guji_bush_t*)guji_alloc(GUJI_KIND_BUSH, 0, sizeof(guji_bush_t));
	b->name = src->name;
	b->text = guji_str_copy(src->text);
	b->ncaps = n;
	b->cap_names = (const char**)guji_alloc(GUJI_KIND_ARR_PTR, 0, sizeof(const char*) * (size_t)(n > 0 ? n : 1));
	b->caps = (guji_bush_t**)guji_alloc(GUJI_KIND_ARR_PTR, n, sizeof(guji_bush_t*) * (size_t)(n > 0 ? n : 1));
	for (int64_t i = 0; i < n; i++) {
		b->cap_names[i] = src->cap_names[i];
		b->caps[i] = guji_bush_copy(src->caps[i]);
	}
	return b;
}

/* PEG matching primitives for compiled grammar productions. Each returns the
   new position on a match at exactly pos, or -1 on failure. */
static int64_t guji_peg_lit(const char* s, int64_t pos, const char* lit) {
	size_t n = strlen(lit);
	if (strncmp(s + pos, lit, n) != 0) {
		return -1;
	}
	return pos + (int64_t)n;
}

/* guji_peg_ws skips the implicit rule whitespace: the same [\t\n\f\r ] set
   the interpreter's \s* matches. It always succeeds. */
static int64_t guji_peg_ws(const char* s, int64_t pos) {
	while (s[pos] == ' ' || s[pos] == '\t' || s[pos] == '\n' || s[pos] == '\f' || s[pos] == '\r') {
		pos++;
	}
	return pos;
}



/* Generated Unicode tables; see THIRD_PARTY_NOTICES.md. DO NOT EDIT BY HAND. */
/* Unicode data version: 15.0.0. */
/* Self-contained property, grapheme, folding, and emoji data for the native
   runtime. Native binaries are one translation unit, and the regex engine is
   concatenated after these tables. */

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define GUJI_UNICODE_VERSION "15.0.0"
#define GUJI_MAX_RUNE 0x10FFFF

typedef struct { int32_t lo; int32_t hi; } guji_rune_range_t;
typedef struct { const char *name; const guji_rune_range_t *ranges; int32_t count; } guji_unicode_table_t;
typedef struct { int32_t from; int32_t to; } guji_fold_pair_t;
typedef struct { int32_t lo; int32_t hi; uint8_t cls; } guji_gcb_range_t;

enum {
	GUJI_GCB_OTHER = 0,
	GUJI_GCB_CR = 1,
	GUJI_GCB_LF = 2,
	GUJI_GCB_CONTROL = 3,
	GUJI_GCB_EXTEND = 4,
	GUJI_GCB_ZWJ = 5,
	GUJI_GCB_REGIONAL_INDICATOR = 6,
	GUJI_GCB_PREPEND = 7,
	GUJI_GCB_SPACINGMARK = 8,
	GUJI_GCB_L = 9,
	GUJI_GCB_V = 10,
	GUJI_GCB_T = 11,
	GUJI_GCB_LV = 12,
	GUJI_GCB_LVT = 13,
};

static const guji_rune_range_t guji_prop_Adlam[] = {
	{0x1E900, 0x1E94B}, {0x1E950, 0x1E959}, {0x1E95E, 0x1E95F}, 
};
static const guji_rune_range_t guji_prop_Ahom[] = {
	{0x11700, 0x1171A}, {0x1171D, 0x1172B}, {0x11730, 0x11746}, 
};
static const guji_rune_range_t guji_prop_Alphabetic[] = {
	{0x0041, 0x005A}, {0x0061, 0x007A}, {0x00AA, 0x00AA}, {0x00B5, 0x00B5}, 
	{0x00BA, 0x00BA}, {0x00C0, 0x00D6}, {0x00D8, 0x00F6}, {0x00F8, 0x02C1}, 
	{0x02C6, 0x02D1}, {0x02E0, 0x02E4}, {0x02EC, 0x02EC}, {0x02EE, 0x02EE}, 
	{0x0345, 0x0345}, {0x0370, 0x0374}, {0x0376, 0x0377}, {0x037A, 0x037D}, 
	{0x037F, 0x037F}, {0x0386, 0x0386}, {0x0388, 0x038A}, {0x038C, 0x038C}, 
	{0x038E, 0x03A1}, {0x03A3, 0x03F5}, {0x03F7, 0x0481}, {0x048A, 0x052F}, 
	{0x0531, 0x0556}, {0x0559, 0x0559}, {0x0560, 0x0588}, {0x05B0, 0x05BD}, 
	{0x05BF, 0x05BF}, {0x05C1, 0x05C2}, {0x05C4, 0x05C5}, {0x05C7, 0x05C7}, 
	{0x05D0, 0x05EA}, {0x05EF, 0x05F2}, {0x0610, 0x061A}, {0x0620, 0x0657}, 
	{0x0659, 0x065F}, {0x066E, 0x06D3}, {0x06D5, 0x06DC}, {0x06E1, 0x06E8}, 
	{0x06ED, 0x06EF}, {0x06FA, 0x06FC}, {0x06FF, 0x06FF}, {0x0710, 0x073F}, 
	{0x074D, 0x07B1}, {0x07CA, 0x07EA}, {0x07F4, 0x07F5}, {0x07FA, 0x07FA}, 
	{0x0800, 0x0817}, {0x081A, 0x082C}, {0x0840, 0x0858}, {0x0860, 0x086A}, 
	{0x0870, 0x0887}, {0x0889, 0x088E}, {0x08A0, 0x08C9}, {0x08D4, 0x08DF}, 
	{0x08E3, 0x08E9}, {0x08F0, 0x093B}, {0x093D, 0x094C}, {0x094E, 0x0950}, 
	{0x0955, 0x0963}, {0x0971, 0x0983}, {0x0985, 0x098C}, {0x098F, 0x0990}, 
	{0x0993, 0x09A8}, {0x09AA, 0x09B0}, {0x09B2, 0x09B2}, {0x09B6, 0x09B9}, 
	{0x09BD, 0x09C4}, {0x09C7, 0x09C8}, {0x09CB, 0x09CC}, {0x09CE, 0x09CE}, 
	{0x09D7, 0x09D7}, {0x09DC, 0x09DD}, {0x09DF, 0x09E3}, {0x09F0, 0x09F1}, 
	{0x09FC, 0x09FC}, {0x0A01, 0x0A03}, {0x0A05, 0x0A0A}, {0x0A0F, 0x0A10}, 
	{0x0A13, 0x0A28}, {0x0A2A, 0x0A30}, {0x0A32, 0x0A33}, {0x0A35, 0x0A36}, 
	{0x0A38, 0x0A39}, {0x0A3E, 0x0A42}, {0x0A47, 0x0A48}, {0x0A4B, 0x0A4C}, 
	{0x0A51, 0x0A51}, {0x0A59, 0x0A5C}, {0x0A5E, 0x0A5E}, {0x0A70, 0x0A75}, 
	{0x0A81, 0x0A83}, {0x0A85, 0x0A8D}, {0x0A8F, 0x0A91}, {0x0A93, 0x0AA8}, 
	{0x0AAA, 0x0AB0}, {0x0AB2, 0x0AB3}, {0x0AB5, 0x0AB9}, {0x0ABD, 0x0AC5}, 
	{0x0AC7, 0x0AC9}, {0x0ACB, 0x0ACC}, {0x0AD0, 0x0AD0}, {0x0AE0, 0x0AE3}, 
	{0x0AF9, 0x0AFC}, {0x0B01, 0x0B03}, {0x0B05, 0x0B0C}, {0x0B0F, 0x0B10}, 
	{0x0B13, 0x0B28}, {0x0B2A, 0x0B30}, {0x0B32, 0x0B33}, {0x0B35, 0x0B39}, 
	{0x0B3D, 0x0B44}, {0x0B47, 0x0B48}, {0x0B4B, 0x0B4C}, {0x0B56, 0x0B57}, 
	{0x0B5C, 0x0B5D}, {0x0B5F, 0x0B63}, {0x0B71, 0x0B71}, {0x0B82, 0x0B83}, 
	{0x0B85, 0x0B8A}, {0x0B8E, 0x0B90}, {0x0B92, 0x0B95}, {0x0B99, 0x0B9A}, 
	{0x0B9C, 0x0B9C}, {0x0B9E, 0x0B9F}, {0x0BA3, 0x0BA4}, {0x0BA8, 0x0BAA}, 
	{0x0BAE, 0x0BB9}, {0x0BBE, 0x0BC2}, {0x0BC6, 0x0BC8}, {0x0BCA, 0x0BCC}, 
	{0x0BD0, 0x0BD0}, {0x0BD7, 0x0BD7}, {0x0C00, 0x0C0C}, {0x0C0E, 0x0C10}, 
	{0x0C12, 0x0C28}, {0x0C2A, 0x0C39}, {0x0C3D, 0x0C44}, {0x0C46, 0x0C48}, 
	{0x0C4A, 0x0C4C}, {0x0C55, 0x0C56}, {0x0C58, 0x0C5A}, {0x0C5D, 0x0C5D}, 
	{0x0C60, 0x0C63}, {0x0C80, 0x0C83}, {0x0C85, 0x0C8C}, {0x0C8E, 0x0C90}, 
	{0x0C92, 0x0CA8}, {0x0CAA, 0x0CB3}, {0x0CB5, 0x0CB9}, {0x0CBD, 0x0CC4}, 
	{0x0CC6, 0x0CC8}, {0x0CCA, 0x0CCC}, {0x0CD5, 0x0CD6}, {0x0CDD, 0x0CDE}, 
	{0x0CE0, 0x0CE3}, {0x0CF1, 0x0CF3}, {0x0D00, 0x0D0C}, {0x0D0E, 0x0D10}, 
	{0x0D12, 0x0D3A}, {0x0D3D, 0x0D44}, {0x0D46, 0x0D48}, {0x0D4A, 0x0D4C}, 
	{0x0D4E, 0x0D4E}, {0x0D54, 0x0D57}, {0x0D5F, 0x0D63}, {0x0D7A, 0x0D7F}, 
	{0x0D81, 0x0D83}, {0x0D85, 0x0D96}, {0x0D9A, 0x0DB1}, {0x0DB3, 0x0DBB}, 
	{0x0DBD, 0x0DBD}, {0x0DC0, 0x0DC6}, {0x0DCF, 0x0DD4}, {0x0DD6, 0x0DD6}, 
	{0x0DD8, 0x0DDF}, {0x0DF2, 0x0DF3}, {0x0E01, 0x0E3A}, {0x0E40, 0x0E46}, 
	{0x0E4D, 0x0E4D}, {0x0E81, 0x0E82}, {0x0E84, 0x0E84}, {0x0E86, 0x0E8A}, 
	{0x0E8C, 0x0EA3}, {0x0EA5, 0x0EA5}, {0x0EA7, 0x0EB9}, {0x0EBB, 0x0EBD}, 
	{0x0EC0, 0x0EC4}, {0x0EC6, 0x0EC6}, {0x0ECD, 0x0ECD}, {0x0EDC, 0x0EDF}, 
	{0x0F00, 0x0F00}, {0x0F40, 0x0F47}, {0x0F49, 0x0F6C}, {0x0F71, 0x0F83}, 
	{0x0F88, 0x0F97}, {0x0F99, 0x0FBC}, {0x1000, 0x1036}, {0x1038, 0x1038}, 
	{0x103B, 0x103F}, {0x1050, 0x108F}, {0x109A, 0x109D}, {0x10A0, 0x10C5}, 
	{0x10C7, 0x10C7}, {0x10CD, 0x10CD}, {0x10D0, 0x10FA}, {0x10FC, 0x1248}, 
	{0x124A, 0x124D}, {0x1250, 0x1256}, {0x1258, 0x1258}, {0x125A, 0x125D}, 
	{0x1260, 0x1288}, {0x128A, 0x128D}, {0x1290, 0x12B0}, {0x12B2, 0x12B5}, 
	{0x12B8, 0x12BE}, {0x12C0, 0x12C0}, {0x12C2, 0x12C5}, {0x12C8, 0x12D6}, 
	{0x12D8, 0x1310}, {0x1312, 0x1315}, {0x1318, 0x135A}, {0x1380, 0x138F}, 
	{0x13A0, 0x13F5}, {0x13F8, 0x13FD}, {0x1401, 0x166C}, {0x166F, 0x167F}, 
	{0x1681, 0x169A}, {0x16A0, 0x16EA}, {0x16EE, 0x16F8}, {0x1700, 0x1713}, 
	{0x171F, 0x1733}, {0x1740, 0x1753}, {0x1760, 0x176C}, {0x176E, 0x1770}, 
	{0x1772, 0x1773}, {0x1780, 0x17B3}, {0x17B6, 0x17C8}, {0x17D7, 0x17D7}, 
	{0x17DC, 0x17DC}, {0x1820, 0x1878}, {0x1880, 0x18AA}, {0x18B0, 0x18F5}, 
	{0x1900, 0x191E}, {0x1920, 0x192B}, {0x1930, 0x1938}, {0x1950, 0x196D}, 
	{0x1970, 0x1974}, {0x1980, 0x19AB}, {0x19B0, 0x19C9}, {0x1A00, 0x1A1B}, 
	{0x1A20, 0x1A5E}, {0x1A61, 0x1A74}, {0x1AA7, 0x1AA7}, {0x1ABF, 0x1AC0}, 
	{0x1ACC, 0x1ACE}, {0x1B00, 0x1B33}, {0x1B35, 0x1B43}, {0x1B45, 0x1B4C}, 
	{0x1B80, 0x1BA9}, {0x1BAC, 0x1BAF}, {0x1BBA, 0x1BE5}, {0x1BE7, 0x1BF1}, 
	{0x1C00, 0x1C36}, {0x1C4D, 0x1C4F}, {0x1C5A, 0x1C7D}, {0x1C80, 0x1C88}, 
	{0x1C90, 0x1CBA}, {0x1CBD, 0x1CBF}, {0x1CE9, 0x1CEC}, {0x1CEE, 0x1CF3}, 
	{0x1CF5, 0x1CF6}, {0x1CFA, 0x1CFA}, {0x1D00, 0x1DBF}, {0x1DE7, 0x1DF4}, 
	{0x1E00, 0x1F15}, {0x1F18, 0x1F1D}, {0x1F20, 0x1F45}, {0x1F48, 0x1F4D}, 
	{0x1F50, 0x1F57}, {0x1F59, 0x1F59}, {0x1F5B, 0x1F5B}, {0x1F5D, 0x1F5D}, 
	{0x1F5F, 0x1F7D}, {0x1F80, 0x1FB4}, {0x1FB6, 0x1FBC}, {0x1FBE, 0x1FBE}, 
	{0x1FC2, 0x1FC4}, {0x1FC6, 0x1FCC}, {0x1FD0, 0x1FD3}, {0x1FD6, 0x1FDB}, 
	{0x1FE0, 0x1FEC}, {0x1FF2, 0x1FF4}, {0x1FF6, 0x1FFC}, {0x2071, 0x2071}, 
	{0x207F, 0x207F}, {0x2090, 0x209C}, {0x2102, 0x2102}, {0x2107, 0x2107}, 
	{0x210A, 0x2113}, {0x2115, 0x2115}, {0x2119, 0x211D}, {0x2124, 0x2124}, 
	{0x2126, 0x2126}, {0x2128, 0x2128}, {0x212A, 0x212D}, {0x212F, 0x2139}, 
	{0x213C, 0x213F}, {0x2145, 0x2149}, {0x214E, 0x214E}, {0x2160, 0x2188}, 
	{0x24B6, 0x24E9}, {0x2C00, 0x2CE4}, {0x2CEB, 0x2CEE}, {0x2CF2, 0x2CF3}, 
	{0x2D00, 0x2D25}, {0x2D27, 0x2D27}, {0x2D2D, 0x2D2D}, {0x2D30, 0x2D67}, 
	{0x2D6F, 0x2D6F}, {0x2D80, 0x2D96}, {0x2DA0, 0x2DA6}, {0x2DA8, 0x2DAE}, 
	{0x2DB0, 0x2DB6}, {0x2DB8, 0x2DBE}, {0x2DC0, 0x2DC6}, {0x2DC8, 0x2DCE}, 
	{0x2DD0, 0x2DD6}, {0x2DD8, 0x2DDE}, {0x2DE0, 0x2DFF}, {0x2E2F, 0x2E2F}, 
	{0x3005, 0x3007}, {0x3021, 0x3029}, {0x3031, 0x3035}, {0x3038, 0x303C}, 
	{0x3041, 0x3096}, {0x309D, 0x309F}, {0x30A1, 0x30FA}, {0x30FC, 0x30FF}, 
	{0x3105, 0x312F}, {0x3131, 0x318E}, {0x31A0, 0x31BF}, {0x31F0, 0x31FF}, 
	{0x3400, 0x4DBF}, {0x4E00, 0xA48C}, {0xA4D0, 0xA4FD}, {0xA500, 0xA60C}, 
	{0xA610, 0xA61F}, {0xA62A, 0xA62B}, {0xA640, 0xA66E}, {0xA674, 0xA67B}, 
	{0xA67F, 0xA6EF}, {0xA717, 0xA71F}, {0xA722, 0xA788}, {0xA78B, 0xA7CA}, 
	{0xA7D0, 0xA7D1}, {0xA7D3, 0xA7D3}, {0xA7D5, 0xA7D9}, {0xA7F2, 0xA805}, 
	{0xA807, 0xA827}, {0xA840, 0xA873}, {0xA880, 0xA8C3}, {0xA8C5, 0xA8C5}, 
	{0xA8F2, 0xA8F7}, {0xA8FB, 0xA8FB}, {0xA8FD, 0xA8FF}, {0xA90A, 0xA92A}, 
	{0xA930, 0xA952}, {0xA960, 0xA97C}, {0xA980, 0xA9B2}, {0xA9B4, 0xA9BF}, 
	{0xA9CF, 0xA9CF}, {0xA9E0, 0xA9EF}, {0xA9FA, 0xA9FE}, {0xAA00, 0xAA36}, 
	{0xAA40, 0xAA4D}, {0xAA60, 0xAA76}, {0xAA7A, 0xAABE}, {0xAAC0, 0xAAC0}, 
	{0xAAC2, 0xAAC2}, {0xAADB, 0xAADD}, {0xAAE0, 0xAAEF}, {0xAAF2, 0xAAF5}, 
	{0xAB01, 0xAB06}, {0xAB09, 0xAB0E}, {0xAB11, 0xAB16}, {0xAB20, 0xAB26}, 
	{0xAB28, 0xAB2E}, {0xAB30, 0xAB5A}, {0xAB5C, 0xAB69}, {0xAB70, 0xABEA}, 
	{0xAC00, 0xD7A3}, {0xD7B0, 0xD7C6}, {0xD7CB, 0xD7FB}, {0xF900, 0xFA6D}, 
	{0xFA70, 0xFAD9}, {0xFB00, 0xFB06}, {0xFB13, 0xFB17}, {0xFB1D, 0xFB28}, 
	{0xFB2A, 0xFB36}, {0xFB38, 0xFB3C}, {0xFB3E, 0xFB3E}, {0xFB40, 0xFB41}, 
	{0xFB43, 0xFB44}, {0xFB46, 0xFBB1}, {0xFBD3, 0xFD3D}, {0xFD50, 0xFD8F}, 
	{0xFD92, 0xFDC7}, {0xFDF0, 0xFDFB}, {0xFE70, 0xFE74}, {0xFE76, 0xFEFC}, 
	{0xFF21, 0xFF3A}, {0xFF41, 0xFF5A}, {0xFF66, 0xFFBE}, {0xFFC2, 0xFFC7}, 
	{0xFFCA, 0xFFCF}, {0xFFD2, 0xFFD7}, {0xFFDA, 0xFFDC}, {0x10000, 0x1000B}, 
	{0x1000D, 0x10026}, {0x10028, 0x1003A}, {0x1003C, 0x1003D}, {0x1003F, 0x1004D}, 
	{0x10050, 0x1005D}, {0x10080, 0x100FA}, {0x10140, 0x10174}, {0x10280, 0x1029C}, 
	{0x102A0, 0x102D0}, {0x10300, 0x1031F}, {0x1032D, 0x1034A}, {0x10350, 0x1037A}, 
	{0x10380, 0x1039D}, {0x103A0, 0x103C3}, {0x103C8, 0x103CF}, {0x103D1, 0x103D5}, 
	{0x10400, 0x1049D}, {0x104B0, 0x104D3}, {0x104D8, 0x104FB}, {0x10500, 0x10527}, 
	{0x10530, 0x10563}, {0x10570, 0x1057A}, {0x1057C, 0x1058A}, {0x1058C, 0x10592}, 
	{0x10594, 0x10595}, {0x10597, 0x105A1}, {0x105A3, 0x105B1}, {0x105B3, 0x105B9}, 
	{0x105BB, 0x105BC}, {0x10600, 0x10736}, {0x10740, 0x10755}, {0x10760, 0x10767}, 
	{0x10780, 0x10785}, {0x10787, 0x107B0}, {0x107B2, 0x107BA}, {0x10800, 0x10805}, 
	{0x10808, 0x10808}, {0x1080A, 0x10835}, {0x10837, 0x10838}, {0x1083C, 0x1083C}, 
	{0x1083F, 0x10855}, {0x10860, 0x10876}, {0x10880, 0x1089E}, {0x108E0, 0x108F2}, 
	{0x108F4, 0x108F5}, {0x10900, 0x10915}, {0x10920, 0x10939}, {0x10980, 0x109B7}, 
	{0x109BE, 0x109BF}, {0x10A00, 0x10A03}, {0x10A05, 0x10A06}, {0x10A0C, 0x10A13}, 
	{0x10A15, 0x10A17}, {0x10A19, 0x10A35}, {0x10A60, 0x10A7C}, {0x10A80, 0x10A9C}, 
	{0x10AC0, 0x10AC7}, {0x10AC9, 0x10AE4}, {0x10B00, 0x10B35}, {0x10B40, 0x10B55}, 
	{0x10B60, 0x10B72}, {0x10B80, 0x10B91}, {0x10C00, 0x10C48}, {0x10C80, 0x10CB2}, 
	{0x10CC0, 0x10CF2}, {0x10D00, 0x10D27}, {0x10E80, 0x10EA9}, {0x10EAB, 0x10EAC}, 
	{0x10EB0, 0x10EB1}, {0x10F00, 0x10F1C}, {0x10F27, 0x10F27}, {0x10F30, 0x10F45}, 
	{0x10F70, 0x10F81}, {0x10FB0, 0x10FC4}, {0x10FE0, 0x10FF6}, {0x11000, 0x11045}, 
	{0x11071, 0x11075}, {0x11080, 0x110B8}, {0x110C2, 0x110C2}, {0x110D0, 0x110E8}, 
	{0x11100, 0x11132}, {0x11144, 0x11147}, {0x11150, 0x11172}, {0x11176, 0x11176}, 
	{0x11180, 0x111BF}, {0x111C1, 0x111C4}, {0x111CE, 0x111CF}, {0x111DA, 0x111DA}, 
	{0x111DC, 0x111DC}, {0x11200, 0x11211}, {0x11213, 0x11234}, {0x11237, 0x11237}, 
	{0x1123E, 0x11241}, {0x11280, 0x11286}, {0x11288, 0x11288}, {0x1128A, 0x1128D}, 
	{0x1128F, 0x1129D}, {0x1129F, 0x112A8}, {0x112B0, 0x112E8}, {0x11300, 0x11303}, 
	{0x11305, 0x1130C}, {0x1130F, 0x11310}, {0x11313, 0x11328}, {0x1132A, 0x11330}, 
	{0x11332, 0x11333}, {0x11335, 0x11339}, {0x1133D, 0x11344}, {0x11347, 0x11348}, 
	{0x1134B, 0x1134C}, {0x11350, 0x11350}, {0x11357, 0x11357}, {0x1135D, 0x11363}, 
	{0x11400, 0x11441}, {0x11443, 0x11445}, {0x11447, 0x1144A}, {0x1145F, 0x11461}, 
	{0x11480, 0x114C1}, {0x114C4, 0x114C5}, {0x114C7, 0x114C7}, {0x11580, 0x115B5}, 
	{0x115B8, 0x115BE}, {0x115D8, 0x115DD}, {0x11600, 0x1163E}, {0x11640, 0x11640}, 
	{0x11644, 0x11644}, {0x11680, 0x116B5}, {0x116B8, 0x116B8}, {0x11700, 0x1171A}, 
	{0x1171D, 0x1172A}, {0x11740, 0x11746}, {0x11800, 0x11838}, {0x118A0, 0x118DF}, 
	{0x118FF, 0x11906}, {0x11909, 0x11909}, {0x1190C, 0x11913}, {0x11915, 0x11916}, 
	{0x11918, 0x11935}, {0x11937, 0x11938}, {0x1193B, 0x1193C}, {0x1193F, 0x11942}, 
	{0x119A0, 0x119A7}, {0x119AA, 0x119D7}, {0x119DA, 0x119DF}, {0x119E1, 0x119E1}, 
	{0x119E3, 0x119E4}, {0x11A00, 0x11A32}, {0x11A35, 0x11A3E}, {0x11A50, 0x11A97}, 
	{0x11A9D, 0x11A9D}, {0x11AB0, 0x11AF8}, {0x11C00, 0x11C08}, {0x11C0A, 0x11C36}, 
	{0x11C38, 0x11C3E}, {0x11C40, 0x11C40}, {0x11C72, 0x11C8F}, {0x11C92, 0x11CA7}, 
	{0x11CA9, 0x11CB6}, {0x11D00, 0x11D06}, {0x11D08, 0x11D09}, {0x11D0B, 0x11D36}, 
	{0x11D3A, 0x11D3A}, {0x11D3C, 0x11D3D}, {0x11D3F, 0x11D41}, {0x11D43, 0x11D43}, 
	{0x11D46, 0x11D47}, {0x11D60, 0x11D65}, {0x11D67, 0x11D68}, {0x11D6A, 0x11D8E}, 
	{0x11D90, 0x11D91}, {0x11D93, 0x11D96}, {0x11D98, 0x11D98}, {0x11EE0, 0x11EF6}, 
	{0x11F00, 0x11F10}, {0x11F12, 0x11F3A}, {0x11F3E, 0x11F40}, {0x11FB0, 0x11FB0}, 
	{0x12000, 0x12399}, {0x12400, 0x1246E}, {0x12480, 0x12543}, {0x12F90, 0x12FF0}, 
	{0x13000, 0x1342F}, {0x13441, 0x13446}, {0x14400, 0x14646}, {0x16800, 0x16A38}, 
	{0x16A40, 0x16A5E}, {0x16A70, 0x16ABE}, {0x16AD0, 0x16AED}, {0x16B00, 0x16B2F}, 
	{0x16B40, 0x16B43}, {0x16B63, 0x16B77}, {0x16B7D, 0x16B8F}, {0x16E40, 0x16E7F}, 
	{0x16F00, 0x16F4A}, {0x16F4F, 0x16F87}, {0x16F8F, 0x16F9F}, {0x16FE0, 0x16FE1}, 
	{0x16FE3, 0x16FE3}, {0x16FF0, 0x16FF1}, {0x17000, 0x187F7}, {0x18800, 0x18CD5}, 
	{0x18D00, 0x18D08}, {0x1AFF0, 0x1AFF3}, {0x1AFF5, 0x1AFFB}, {0x1AFFD, 0x1AFFE}, 
	{0x1B000, 0x1B122}, {0x1B132, 0x1B132}, {0x1B150, 0x1B152}, {0x1B155, 0x1B155}, 
	{0x1B164, 0x1B167}, {0x1B170, 0x1B2FB}, {0x1BC00, 0x1BC6A}, {0x1BC70, 0x1BC7C}, 
	{0x1BC80, 0x1BC88}, {0x1BC90, 0x1BC99}, {0x1BC9E, 0x1BC9E}, {0x1D400, 0x1D454}, 
	{0x1D456, 0x1D49C}, {0x1D49E, 0x1D49F}, {0x1D4A2, 0x1D4A2}, {0x1D4A5, 0x1D4A6}, 
	{0x1D4A9, 0x1D4AC}, {0x1D4AE, 0x1D4B9}, {0x1D4BB, 0x1D4BB}, {0x1D4BD, 0x1D4C3}, 
	{0x1D4C5, 0x1D505}, {0x1D507, 0x1D50A}, {0x1D50D, 0x1D514}, {0x1D516, 0x1D51C}, 
	{0x1D51E, 0x1D539}, {0x1D53B, 0x1D53E}, {0x1D540, 0x1D544}, {0x1D546, 0x1D546}, 
	{0x1D54A, 0x1D550}, {0x1D552, 0x1D6A5}, {0x1D6A8, 0x1D6C0}, {0x1D6C2, 0x1D6DA}, 
	{0x1D6DC, 0x1D6FA}, {0x1D6FC, 0x1D714}, {0x1D716, 0x1D734}, {0x1D736, 0x1D74E}, 
	{0x1D750, 0x1D76E}, {0x1D770, 0x1D788}, {0x1D78A, 0x1D7A8}, {0x1D7AA, 0x1D7C2}, 
	{0x1D7C4, 0x1D7CB}, {0x1DF00, 0x1DF1E}, {0x1DF25, 0x1DF2A}, {0x1E000, 0x1E006}, 
	{0x1E008, 0x1E018}, {0x1E01B, 0x1E021}, {0x1E023, 0x1E024}, {0x1E026, 0x1E02A}, 
	{0x1E030, 0x1E06D}, {0x1E08F, 0x1E08F}, {0x1E100, 0x1E12C}, {0x1E137, 0x1E13D}, 
	{0x1E14E, 0x1E14E}, {0x1E290, 0x1E2AD}, {0x1E2C0, 0x1E2EB}, {0x1E4D0, 0x1E4EB}, 
	{0x1E7E0, 0x1E7E6}, {0x1E7E8, 0x1E7EB}, {0x1E7ED, 0x1E7EE}, {0x1E7F0, 0x1E7FE}, 
	{0x1E800, 0x1E8C4}, {0x1E900, 0x1E943}, {0x1E947, 0x1E947}, {0x1E94B, 0x1E94B}, 
	{0x1EE00, 0x1EE03}, {0x1EE05, 0x1EE1F}, {0x1EE21, 0x1EE22}, {0x1EE24, 0x1EE24}, 
	{0x1EE27, 0x1EE27}, {0x1EE29, 0x1EE32}, {0x1EE34, 0x1EE37}, {0x1EE39, 0x1EE39}, 
	{0x1EE3B, 0x1EE3B}, {0x1EE42, 0x1EE42}, {0x1EE47, 0x1EE47}, {0x1EE49, 0x1EE49}, 
	{0x1EE4B, 0x1EE4B}, {0x1EE4D, 0x1EE4F}, {0x1EE51, 0x1EE52}, {0x1EE54, 0x1EE54}, 
	{0x1EE57, 0x1EE57}, {0x1EE59, 0x1EE59}, {0x1EE5B, 0x1EE5B}, {0x1EE5D, 0x1EE5D}, 
	{0x1EE5F, 0x1EE5F}, {0x1EE61, 0x1EE62}, {0x1EE64, 0x1EE64}, {0x1EE67, 0x1EE6A}, 
	{0x1EE6C, 0x1EE72}, {0x1EE74, 0x1EE77}, {0x1EE79, 0x1EE7C}, {0x1EE7E, 0x1EE7E}, 
	{0x1EE80, 0x1EE89}, {0x1EE8B, 0x1EE9B}, {0x1EEA1, 0x1EEA3}, {0x1EEA5, 0x1EEA9}, 
	{0x1EEAB, 0x1EEBB}, {0x1F130, 0x1F149}, {0x1F150, 0x1F169}, {0x1F170, 0x1F189}, 
	{0x20000, 0x2A6DF}, {0x2A700, 0x2B739}, {0x2B740, 0x2B81D}, {0x2B820, 0x2CEA1}, 
	{0x2CEB0, 0x2EBE0}, {0x2F800, 0x2FA1D}, {0x30000, 0x3134A}, {0x31350, 0x323AF}, 
};
static const guji_rune_range_t guji_prop_Anatolian_Hieroglyphs[] = {
	{0x14400, 0x14646}, 
};
static const guji_rune_range_t guji_prop_Arabic[] = {
	{0x0600, 0x0604}, {0x0606, 0x060B}, {0x060D, 0x061A}, {0x061C, 0x061E}, 
	{0x0620, 0x063F}, {0x0641, 0x064A}, {0x0656, 0x066F}, {0x0671, 0x06DC}, 
	{0x06DE, 0x06FF}, {0x0750, 0x077F}, {0x0870, 0x088E}, {0x0890, 0x0891}, 
	{0x0898, 0x08E1}, {0x08E3, 0x08FF}, {0xFB50, 0xFBC2}, {0xFBD3, 0xFD3D}, 
	{0xFD40, 0xFD8F}, {0xFD92, 0xFDC7}, {0xFDCF, 0xFDCF}, {0xFDF0, 0xFDFF}, 
	{0xFE70, 0xFE74}, {0xFE76, 0xFEFC}, {0x10E60, 0x10E7E}, {0x10EFD, 0x10EFF}, 
	{0x1EE00, 0x1EE03}, {0x1EE05, 0x1EE1F}, {0x1EE21, 0x1EE22}, {0x1EE24, 0x1EE24}, 
	{0x1EE27, 0x1EE27}, {0x1EE29, 0x1EE32}, {0x1EE34, 0x1EE37}, {0x1EE39, 0x1EE39}, 
	{0x1EE3B, 0x1EE3B}, {0x1EE42, 0x1EE42}, {0x1EE47, 0x1EE47}, {0x1EE49, 0x1EE49}, 
	{0x1EE4B, 0x1EE4B}, {0x1EE4D, 0x1EE4F}, {0x1EE51, 0x1EE52}, {0x1EE54, 0x1EE54}, 
	{0x1EE57, 0x1EE57}, {0x1EE59, 0x1EE59}, {0x1EE5B, 0x1EE5B}, {0x1EE5D, 0x1EE5D}, 
	{0x1EE5F, 0x1EE5F}, {0x1EE61, 0x1EE62}, {0x1EE64, 0x1EE64}, {0x1EE67, 0x1EE6A}, 
	{0x1EE6C, 0x1EE72}, {0x1EE74, 0x1EE77}, {0x1EE79, 0x1EE7C}, {0x1EE7E, 0x1EE7E}, 
	{0x1EE80, 0x1EE89}, {0x1EE8B, 0x1EE9B}, {0x1EEA1, 0x1EEA3}, {0x1EEA5, 0x1EEA9}, 
	{0x1EEAB, 0x1EEBB}, {0x1EEF0, 0x1EEF1}, 
};
static const guji_rune_range_t guji_prop_Armenian[] = {
	{0x0531, 0x0556}, {0x0559, 0x058A}, {0x058D, 0x058F}, {0xFB13, 0xFB17}, 
};
static const guji_rune_range_t guji_prop_Avestan[] = {
	{0x10B00, 0x10B35}, {0x10B39, 0x10B3F}, 
};
static const guji_rune_range_t guji_prop_Balinese[] = {
	{0x1B00, 0x1B4C}, {0x1B50, 0x1B7E}, 
};
static const guji_rune_range_t guji_prop_Bamum[] = {
	{0xA6A0, 0xA6F7}, {0x16800, 0x16A38}, 
};
static const guji_rune_range_t guji_prop_Bassa_Vah[] = {
	{0x16AD0, 0x16AED}, {0x16AF0, 0x16AF5}, 
};
static const guji_rune_range_t guji_prop_Batak[] = {
	{0x1BC0, 0x1BF3}, {0x1BFC, 0x1BFF}, 
};
static const guji_rune_range_t guji_prop_Bengali[] = {
	{0x0980, 0x0983}, {0x0985, 0x098C}, {0x098F, 0x0990}, {0x0993, 0x09A8}, 
	{0x09AA, 0x09B0}, {0x09B2, 0x09B2}, {0x09B6, 0x09B9}, {0x09BC, 0x09C4}, 
	{0x09C7, 0x09C8}, {0x09CB, 0x09CE}, {0x09D7, 0x09D7}, {0x09DC, 0x09DD}, 
	{0x09DF, 0x09E3}, {0x09E6, 0x09FE}, 
};
static const guji_rune_range_t guji_prop_Bhaiksuki[] = {
	{0x11C00, 0x11C08}, {0x11C0A, 0x11C36}, {0x11C38, 0x11C45}, {0x11C50, 0x11C6C}, 
};
static const guji_rune_range_t guji_prop_Bopomofo[] = {
	{0x02EA, 0x02EB}, {0x3105, 0x312F}, {0x31A0, 0x31BF}, 
};
static const guji_rune_range_t guji_prop_Brahmi[] = {
	{0x11000, 0x1104D}, {0x11052, 0x11075}, {0x1107F, 0x1107F}, 
};
static const guji_rune_range_t guji_prop_Braille[] = {
	{0x2800, 0x28FF}, 
};
static const guji_rune_range_t guji_prop_Buginese[] = {
	{0x1A00, 0x1A1B}, {0x1A1E, 0x1A1F}, 
};
static const guji_rune_range_t guji_prop_Buhid[] = {
	{0x1740, 0x1753}, 
};
static const guji_rune_range_t guji_prop_C[] = {
	{0x0000, 0x001F}, {0x007F, 0x009F}, {0x00AD, 0x00AD}, {0x0600, 0x0605}, 
	{0x061C, 0x061C}, {0x06DD, 0x06DD}, {0x070F, 0x070F}, {0x0890, 0x0891}, 
	{0x08E2, 0x08E2}, {0x180E, 0x180E}, {0x200B, 0x200F}, {0x202A, 0x202E}, 
	{0x2060, 0x2064}, {0x2066, 0x206F}, {0xD800, 0xF8FF}, {0xFEFF, 0xFEFF}, 
	{0xFFF9, 0xFFFB}, {0x110BD, 0x110BD}, {0x110CD, 0x110CD}, {0x13430, 0x1343F}, 
	{0x1BCA0, 0x1BCA3}, {0x1D173, 0x1D17A}, {0xE0001, 0xE0001}, {0xE0020, 0xE007F}, 
	{0xF0000, 0xFFFFD}, {0x100000, 0x10FFFD}, 
};
static const guji_rune_range_t guji_prop_Canadian_Aboriginal[] = {
	{0x1400, 0x167F}, {0x18B0, 0x18F5}, {0x11AB0, 0x11ABF}, 
};
static const guji_rune_range_t guji_prop_Carian[] = {
	{0x102A0, 0x102D0}, 
};
static const guji_rune_range_t guji_prop_Caucasian_Albanian[] = {
	{0x10530, 0x10563}, {0x1056F, 0x1056F}, 
};
static const guji_rune_range_t guji_prop_Cc[] = {
	{0x0000, 0x001F}, {0x007F, 0x009F}, 
};
static const guji_rune_range_t guji_prop_Cf[] = {
	{0x00AD, 0x00AD}, {0x0600, 0x0605}, {0x061C, 0x061C}, {0x06DD, 0x06DD}, 
	{0x070F, 0x070F}, {0x0890, 0x0891}, {0x08E2, 0x08E2}, {0x180E, 0x180E}, 
	{0x200B, 0x200F}, {0x202A, 0x202E}, {0x2060, 0x2064}, {0x2066, 0x206F}, 
	{0xFEFF, 0xFEFF}, {0xFFF9, 0xFFFB}, {0x110BD, 0x110BD}, {0x110CD, 0x110CD}, 
	{0x13430, 0x1343F}, {0x1BCA0, 0x1BCA3}, {0x1D173, 0x1D17A}, {0xE0001, 0xE0001}, 
	{0xE0020, 0xE007F}, 
};
static const guji_rune_range_t guji_prop_Chakma[] = {
	{0x11100, 0x11134}, {0x11136, 0x11147}, 
};
static const guji_rune_range_t guji_prop_Cham[] = {
	{0xAA00, 0xAA36}, {0xAA40, 0xAA4D}, {0xAA50, 0xAA59}, {0xAA5C, 0xAA5F}, 
};
static const guji_rune_range_t guji_prop_Cherokee[] = {
	{0x13A0, 0x13F5}, {0x13F8, 0x13FD}, {0xAB70, 0xABBF}, 
};
static const guji_rune_range_t guji_prop_Chorasmian[] = {
	{0x10FB0, 0x10FCB}, 
};
static const guji_rune_range_t guji_prop_Co[] = {
	{0xE000, 0xF8FF}, {0xF0000, 0xFFFFD}, {0x100000, 0x10FFFD}, 
};
static const guji_rune_range_t guji_prop_Common[] = {
	{0x0000, 0x0040}, {0x005B, 0x0060}, {0x007B, 0x00A9}, {0x00AB, 0x00B9}, 
	{0x00BB, 0x00BF}, {0x00D7, 0x00D7}, {0x00F7, 0x00F7}, {0x02B9, 0x02DF}, 
	{0x02E5, 0x02E9}, {0x02EC, 0x02FF}, {0x0374, 0x0374}, {0x037E, 0x037E}, 
	{0x0385, 0x0385}, {0x0387, 0x0387}, {0x0605, 0x0605}, {0x060C, 0x060C}, 
	{0x061B, 0x061B}, {0x061F, 0x061F}, {0x0640, 0x0640}, {0x06DD, 0x06DD}, 
	{0x08E2, 0x08E2}, {0x0964, 0x0965}, {0x0E3F, 0x0E3F}, {0x0FD5, 0x0FD8}, 
	{0x10FB, 0x10FB}, {0x16EB, 0x16ED}, {0x1735, 0x1736}, {0x1802, 0x1803}, 
	{0x1805, 0x1805}, {0x1CD3, 0x1CD3}, {0x1CE1, 0x1CE1}, {0x1CE9, 0x1CEC}, 
	{0x1CEE, 0x1CF3}, {0x1CF5, 0x1CF7}, {0x1CFA, 0x1CFA}, {0x2000, 0x200B}, 
	{0x200E, 0x2064}, {0x2066, 0x2070}, {0x2074, 0x207E}, {0x2080, 0x208E}, 
	{0x20A0, 0x20C0}, {0x2100, 0x2125}, {0x2127, 0x2129}, {0x212C, 0x2131}, 
	{0x2133, 0x214D}, {0x214F, 0x215F}, {0x2189, 0x218B}, {0x2190, 0x2426}, 
	{0x2440, 0x244A}, {0x2460, 0x27FF}, {0x2900, 0x2B73}, {0x2B76, 0x2B95}, 
	{0x2B97, 0x2BFF}, {0x2E00, 0x2E5D}, {0x2FF0, 0x2FFB}, {0x3000, 0x3004}, 
	{0x3006, 0x3006}, {0x3008, 0x3020}, {0x3030, 0x3037}, {0x303C, 0x303F}, 
	{0x309B, 0x309C}, {0x30A0, 0x30A0}, {0x30FB, 0x30FC}, {0x3190, 0x319F}, 
	{0x31C0, 0x31E3}, {0x3220, 0x325F}, {0x327F, 0x32CF}, {0x32FF, 0x32FF}, 
	{0x3358, 0x33FF}, {0x4DC0, 0x4DFF}, {0xA700, 0xA721}, {0xA788, 0xA78A}, 
	{0xA830, 0xA839}, {0xA92E, 0xA92E}, {0xA9CF, 0xA9CF}, {0xAB5B, 0xAB5B}, 
	{0xAB6A, 0xAB6B}, {0xFD3E, 0xFD3F}, {0xFE10, 0xFE19}, {0xFE30, 0xFE52}, 
	{0xFE54, 0xFE66}, {0xFE68, 0xFE6B}, {0xFEFF, 0xFEFF}, {0xFF01, 0xFF20}, 
	{0xFF3B, 0xFF40}, {0xFF5B, 0xFF65}, {0xFF70, 0xFF70}, {0xFF9E, 0xFF9F}, 
	{0xFFE0, 0xFFE6}, {0xFFE8, 0xFFEE}, {0xFFF9, 0xFFFD}, {0x10100, 0x10102}, 
	{0x10107, 0x10133}, {0x10137, 0x1013F}, {0x10190, 0x1019C}, {0x101D0, 0x101FC}, 
	{0x102E1, 0x102FB}, {0x1BCA0, 0x1BCA3}, {0x1CF50, 0x1CFC3}, {0x1D000, 0x1D0F5}, 
	{0x1D100, 0x1D126}, {0x1D129, 0x1D166}, {0x1D16A, 0x1D17A}, {0x1D183, 0x1D184}, 
	{0x1D18C, 0x1D1A9}, {0x1D1AE, 0x1D1EA}, {0x1D2C0, 0x1D2D3}, {0x1D2E0, 0x1D2F3}, 
	{0x1D300, 0x1D356}, {0x1D360, 0x1D378}, {0x1D400, 0x1D454}, {0x1D456, 0x1D49C}, 
	{0x1D49E, 0x1D49F}, {0x1D4A2, 0x1D4A2}, {0x1D4A5, 0x1D4A6}, {0x1D4A9, 0x1D4AC}, 
	{0x1D4AE, 0x1D4B9}, {0x1D4BB, 0x1D4BB}, {0x1D4BD, 0x1D4C3}, {0x1D4C5, 0x1D505}, 
	{0x1D507, 0x1D50A}, {0x1D50D, 0x1D514}, {0x1D516, 0x1D51C}, {0x1D51E, 0x1D539}, 
	{0x1D53B, 0x1D53E}, {0x1D540, 0x1D544}, {0x1D546, 0x1D546}, {0x1D54A, 0x1D550}, 
	{0x1D552, 0x1D6A5}, {0x1D6A8, 0x1D7CB}, {0x1D7CE, 0x1D7FF}, {0x1EC71, 0x1ECB4}, 
	{0x1ED01, 0x1ED3D}, {0x1F000, 0x1F02B}, {0x1F030, 0x1F093}, {0x1F0A0, 0x1F0AE}, 
	{0x1F0B1, 0x1F0BF}, {0x1F0C1, 0x1F0CF}, {0x1F0D1, 0x1F0F5}, {0x1F100, 0x1F1AD}, 
	{0x1F1E6, 0x1F1FF}, {0x1F201, 0x1F202}, {0x1F210, 0x1F23B}, {0x1F240, 0x1F248}, 
	{0x1F250, 0x1F251}, {0x1F260, 0x1F265}, {0x1F300, 0x1F6D7}, {0x1F6DC, 0x1F6EC}, 
	{0x1F6F0, 0x1F6FC}, {0x1F700, 0x1F776}, {0x1F77B, 0x1F7D9}, {0x1F7E0, 0x1F7EB}, 
	{0x1F7F0, 0x1F7F0}, {0x1F800, 0x1F80B}, {0x1F810, 0x1F847}, {0x1F850, 0x1F859}, 
	{0x1F860, 0x1F887}, {0x1F890, 0x1F8AD}, {0x1F8B0, 0x1F8B1}, {0x1F900, 0x1FA53}, 
	{0x1FA60, 0x1FA6D}, {0x1FA70, 0x1FA7C}, {0x1FA80, 0x1FA88}, {0x1FA90, 0x1FABD}, 
	{0x1FABF, 0x1FAC5}, {0x1FACE, 0x1FADB}, {0x1FAE0, 0x1FAE8}, {0x1FAF0, 0x1FAF8}, 
	{0x1FB00, 0x1FB92}, {0x1FB94, 0x1FBCA}, {0x1FBF0, 0x1FBF9}, {0xE0001, 0xE0001}, 
	{0xE0020, 0xE007F}, 
};
static const guji_rune_range_t guji_prop_Coptic[] = {
	{0x03E2, 0x03EF}, {0x2C80, 0x2CF3}, {0x2CF9, 0x2CFF}, 
};
static const guji_rune_range_t guji_prop_Cs[] = {
	{0xD800, 0xDFFF}, 
};
static const guji_rune_range_t guji_prop_Cuneiform[] = {
	{0x12000, 0x12399}, {0x12400, 0x1246E}, {0x12470, 0x12474}, {0x12480, 0x12543}, 
};
static const guji_rune_range_t guji_prop_Cypriot[] = {
	{0x10800, 0x10805}, {0x10808, 0x10808}, {0x1080A, 0x10835}, {0x10837, 0x10838}, 
	{0x1083C, 0x1083C}, {0x1083F, 0x1083F}, 
};
static const guji_rune_range_t guji_prop_Cypro_Minoan[] = {
	{0x12F90, 0x12FF2}, 
};
static const guji_rune_range_t guji_prop_Cyrillic[] = {
	{0x0400, 0x0484}, {0x0487, 0x052F}, {0x1C80, 0x1C88}, {0x1D2B, 0x1D2B}, 
	{0x1D78, 0x1D78}, {0x2DE0, 0x2DFF}, {0xA640, 0xA69F}, {0xFE2E, 0xFE2F}, 
	{0x1E030, 0x1E06D}, {0x1E08F, 0x1E08F}, 
};
static const guji_rune_range_t guji_prop_Deseret[] = {
	{0x10400, 0x1044F}, 
};
static const guji_rune_range_t guji_prop_Devanagari[] = {
	{0x0900, 0x0950}, {0x0955, 0x0963}, {0x0966, 0x097F}, {0xA8E0, 0xA8FF}, 
	{0x11B00, 0x11B09}, 
};
static const guji_rune_range_t guji_prop_Dives_Akuru[] = {
	{0x11900, 0x11906}, {0x11909, 0x11909}, {0x1190C, 0x11913}, {0x11915, 0x11916}, 
	{0x11918, 0x11935}, {0x11937, 0x11938}, {0x1193B, 0x11946}, {0x11950, 0x11959}, 
};
static const guji_rune_range_t guji_prop_Dogra[] = {
	{0x11800, 0x1183B}, 
};
static const guji_rune_range_t guji_prop_Duployan[] = {
	{0x1BC00, 0x1BC6A}, {0x1BC70, 0x1BC7C}, {0x1BC80, 0x1BC88}, {0x1BC90, 0x1BC99}, 
	{0x1BC9C, 0x1BC9F}, 
};
static const guji_rune_range_t guji_prop_Egyptian_Hieroglyphs[] = {
	{0x13000, 0x13455}, 
};
static const guji_rune_range_t guji_prop_Elbasan[] = {
	{0x10500, 0x10527}, 
};
static const guji_rune_range_t guji_prop_Elymaic[] = {
	{0x10FE0, 0x10FF6}, 
};
static const guji_rune_range_t guji_prop_Emoji[] = {
	{0x0023, 0x0023}, {0x002A, 0x002A}, {0x0030, 0x0039}, {0x00A9, 0x00A9}, 
	{0x00AE, 0x00AE}, {0x203C, 0x203C}, {0x2049, 0x2049}, {0x2122, 0x2122}, 
	{0x2139, 0x2139}, {0x2194, 0x2199}, {0x21A9, 0x21AA}, {0x231A, 0x231B}, 
	{0x2328, 0x2328}, {0x23CF, 0x23CF}, {0x23E9, 0x23F3}, {0x23F8, 0x23FA}, 
	{0x24C2, 0x24C2}, {0x25AA, 0x25AB}, {0x25B6, 0x25B6}, {0x25C0, 0x25C0}, 
	{0x25FB, 0x25FE}, {0x2600, 0x2604}, {0x260E, 0x260E}, {0x2611, 0x2611}, 
	{0x2614, 0x2615}, {0x2618, 0x2618}, {0x261D, 0x261D}, {0x2620, 0x2620}, 
	{0x2622, 0x2623}, {0x2626, 0x2626}, {0x262A, 0x262A}, {0x262E, 0x262F}, 
	{0x2638, 0x263A}, {0x2640, 0x2640}, {0x2642, 0x2642}, {0x2648, 0x2653}, 
	{0x265F, 0x2660}, {0x2663, 0x2663}, {0x2665, 0x2666}, {0x2668, 0x2668}, 
	{0x267B, 0x267B}, {0x267E, 0x267F}, {0x2692, 0x2697}, {0x2699, 0x2699}, 
	{0x269B, 0x269C}, {0x26A0, 0x26A1}, {0x26A7, 0x26A7}, {0x26AA, 0x26AB}, 
	{0x26B0, 0x26B1}, {0x26BD, 0x26BE}, {0x26C4, 0x26C5}, {0x26C8, 0x26C8}, 
	{0x26CE, 0x26CF}, {0x26D1, 0x26D1}, {0x26D3, 0x26D4}, {0x26E9, 0x26EA}, 
	{0x26F0, 0x26F5}, {0x26F7, 0x26FA}, {0x26FD, 0x26FD}, {0x2702, 0x2702}, 
	{0x2705, 0x2705}, {0x2708, 0x270D}, {0x270F, 0x270F}, {0x2712, 0x2712}, 
	{0x2714, 0x2714}, {0x2716, 0x2716}, {0x271D, 0x271D}, {0x2721, 0x2721}, 
	{0x2728, 0x2728}, {0x2733, 0x2734}, {0x2744, 0x2744}, {0x2747, 0x2747}, 
	{0x274C, 0x274C}, {0x274E, 0x274E}, {0x2753, 0x2755}, {0x2757, 0x2757}, 
	{0x2763, 0x2764}, {0x2795, 0x2797}, {0x27A1, 0x27A1}, {0x27B0, 0x27B0}, 
	{0x27BF, 0x27BF}, {0x2934, 0x2935}, {0x2B05, 0x2B07}, {0x2B1B, 0x2B1C}, 
	{0x2B50, 0x2B50}, {0x2B55, 0x2B55}, {0x3030, 0x3030}, {0x303D, 0x303D}, 
	{0x3297, 0x3297}, {0x3299, 0x3299}, {0x1F004, 0x1F004}, {0x1F0CF, 0x1F0CF}, 
	{0x1F170, 0x1F171}, {0x1F17E, 0x1F17F}, {0x1F18E, 0x1F18E}, {0x1F191, 0x1F19A}, 
	{0x1F1E6, 0x1F1FF}, {0x1F201, 0x1F202}, {0x1F21A, 0x1F21A}, {0x1F22F, 0x1F22F}, 
	{0x1F232, 0x1F23A}, {0x1F250, 0x1F251}, {0x1F300, 0x1F321}, {0x1F324, 0x1F393}, 
	{0x1F396, 0x1F397}, {0x1F399, 0x1F39B}, {0x1F39E, 0x1F3F0}, {0x1F3F3, 0x1F3F5}, 
	{0x1F3F7, 0x1F4FD}, {0x1F4FF, 0x1F53D}, {0x1F549, 0x1F54E}, {0x1F550, 0x1F567}, 
	{0x1F56F, 0x1F570}, {0x1F573, 0x1F57A}, {0x1F587, 0x1F587}, {0x1F58A, 0x1F58D}, 
	{0x1F590, 0x1F590}, {0x1F595, 0x1F596}, {0x1F5A4, 0x1F5A5}, {0x1F5A8, 0x1F5A8}, 
	{0x1F5B1, 0x1F5B2}, {0x1F5BC, 0x1F5BC}, {0x1F5C2, 0x1F5C4}, {0x1F5D1, 0x1F5D3}, 
	{0x1F5DC, 0x1F5DE}, {0x1F5E1, 0x1F5E1}, {0x1F5E3, 0x1F5E3}, {0x1F5E8, 0x1F5E8}, 
	{0x1F5EF, 0x1F5EF}, {0x1F5F3, 0x1F5F3}, {0x1F5FA, 0x1F64F}, {0x1F680, 0x1F6C5}, 
	{0x1F6CB, 0x1F6D2}, {0x1F6D5, 0x1F6D7}, {0x1F6DC, 0x1F6E5}, {0x1F6E9, 0x1F6E9}, 
	{0x1F6EB, 0x1F6EC}, {0x1F6F0, 0x1F6F0}, {0x1F6F3, 0x1F6FC}, {0x1F7E0, 0x1F7EB}, 
	{0x1F7F0, 0x1F7F0}, {0x1F90C, 0x1F93A}, {0x1F93C, 0x1F945}, {0x1F947, 0x1F9FF}, 
	{0x1FA70, 0x1FA7C}, {0x1FA80, 0x1FA88}, {0x1FA90, 0x1FABD}, {0x1FABF, 0x1FAC5}, 
	{0x1FACE, 0x1FADB}, {0x1FAE0, 0x1FAE8}, {0x1FAF0, 0x1FAF8}, 
};
static const guji_rune_range_t guji_prop_Ethiopic[] = {
	{0x1200, 0x1248}, {0x124A, 0x124D}, {0x1250, 0x1256}, {0x1258, 0x1258}, 
	{0x125A, 0x125D}, {0x1260, 0x1288}, {0x128A, 0x128D}, {0x1290, 0x12B0}, 
	{0x12B2, 0x12B5}, {0x12B8, 0x12BE}, {0x12C0, 0x12C0}, {0x12C2, 0x12C5}, 
	{0x12C8, 0x12D6}, {0x12D8, 0x1310}, {0x1312, 0x1315}, {0x1318, 0x135A}, 
	{0x135D, 0x137C}, {0x1380, 0x1399}, {0x2D80, 0x2D96}, {0x2DA0, 0x2DA6}, 
	{0x2DA8, 0x2DAE}, {0x2DB0, 0x2DB6}, {0x2DB8, 0x2DBE}, {0x2DC0, 0x2DC6}, 
	{0x2DC8, 0x2DCE}, {0x2DD0, 0x2DD6}, {0x2DD8, 0x2DDE}, {0xAB01, 0xAB06}, 
	{0xAB09, 0xAB0E}, {0xAB11, 0xAB16}, {0xAB20, 0xAB26}, {0xAB28, 0xAB2E}, 
	{0x1E7E0, 0x1E7E6}, {0x1E7E8, 0x1E7EB}, {0x1E7ED, 0x1E7EE}, {0x1E7F0, 0x1E7FE}, 
};
static const guji_rune_range_t guji_prop_Extended_Pictographic[] = {
	{0x00A9, 0x00A9}, {0x00AE, 0x00AE}, {0x203C, 0x203C}, {0x2049, 0x2049}, 
	{0x2122, 0x2122}, {0x2139, 0x2139}, {0x2194, 0x2199}, {0x21A9, 0x21AA}, 
	{0x231A, 0x231B}, {0x2328, 0x2328}, {0x2388, 0x2388}, {0x23CF, 0x23CF}, 
	{0x23E9, 0x23F3}, {0x23F8, 0x23FA}, {0x24C2, 0x24C2}, {0x25AA, 0x25AB}, 
	{0x25B6, 0x25B6}, {0x25C0, 0x25C0}, {0x25FB, 0x25FE}, {0x2600, 0x2605}, 
	{0x2607, 0x2612}, {0x2614, 0x2685}, {0x2690, 0x2705}, {0x2708, 0x2712}, 
	{0x2714, 0x2714}, {0x2716, 0x2716}, {0x271D, 0x271D}, {0x2721, 0x2721}, 
	{0x2728, 0x2728}, {0x2733, 0x2734}, {0x2744, 0x2744}, {0x2747, 0x2747}, 
	{0x274C, 0x274C}, {0x274E, 0x274E}, {0x2753, 0x2755}, {0x2757, 0x2757}, 
	{0x2763, 0x2767}, {0x2795, 0x2797}, {0x27A1, 0x27A1}, {0x27B0, 0x27B0}, 
	{0x27BF, 0x27BF}, {0x2934, 0x2935}, {0x2B05, 0x2B07}, {0x2B1B, 0x2B1C}, 
	{0x2B50, 0x2B50}, {0x2B55, 0x2B55}, {0x3030, 0x3030}, {0x303D, 0x303D}, 
	{0x3297, 0x3297}, {0x3299, 0x3299}, {0x1F000, 0x1F0FF}, {0x1F10D, 0x1F10F}, 
	{0x1F12F, 0x1F12F}, {0x1F16C, 0x1F171}, {0x1F17E, 0x1F17F}, {0x1F18E, 0x1F18E}, 
	{0x1F191, 0x1F19A}, {0x1F1AD, 0x1F1E5}, {0x1F201, 0x1F20F}, {0x1F21A, 0x1F21A}, 
	{0x1F22F, 0x1F22F}, {0x1F232, 0x1F23A}, {0x1F23C, 0x1F23F}, {0x1F249, 0x1F3FA}, 
	{0x1F400, 0x1F53D}, {0x1F546, 0x1F64F}, {0x1F680, 0x1F6FF}, {0x1F774, 0x1F77F}, 
	{0x1F7D5, 0x1F7FF}, {0x1F80C, 0x1F80F}, {0x1F848, 0x1F84F}, {0x1F85A, 0x1F85F}, 
	{0x1F888, 0x1F88F}, {0x1F8AE, 0x1F8FF}, {0x1F90C, 0x1F93A}, {0x1F93C, 0x1F945}, 
	{0x1F947, 0x1FAFF}, {0x1FC00, 0x1FFFD}, 
};
static const guji_rune_range_t guji_prop_Georgian[] = {
	{0x10A0, 0x10C5}, {0x10C7, 0x10C7}, {0x10CD, 0x10CD}, {0x10D0, 0x10FA}, 
	{0x10FC, 0x10FF}, {0x1C90, 0x1CBA}, {0x1CBD, 0x1CBF}, {0x2D00, 0x2D25}, 
	{0x2D27, 0x2D27}, {0x2D2D, 0x2D2D}, 
};
static const guji_rune_range_t guji_prop_Glagolitic[] = {
	{0x2C00, 0x2C5F}, {0x1E000, 0x1E006}, {0x1E008, 0x1E018}, {0x1E01B, 0x1E021}, 
	{0x1E023, 0x1E024}, {0x1E026, 0x1E02A}, 
};
static const guji_rune_range_t guji_prop_Gothic[] = {
	{0x10330, 0x1034A}, 
};
static const guji_rune_range_t guji_prop_Grantha[] = {
	{0x11300, 0x11303}, {0x11305, 0x1130C}, {0x1130F, 0x11310}, {0x11313, 0x11328}, 
	{0x1132A, 0x11330}, {0x11332, 0x11333}, {0x11335, 0x11339}, {0x1133C, 0x11344}, 
	{0x11347, 0x11348}, {0x1134B, 0x1134D}, {0x11350, 0x11350}, {0x11357, 0x11357}, 
	{0x1135D, 0x11363}, {0x11366, 0x1136C}, {0x11370, 0x11374}, 
};
static const guji_rune_range_t guji_prop_Greek[] = {
	{0x0370, 0x0373}, {0x0375, 0x0377}, {0x037A, 0x037D}, {0x037F, 0x037F}, 
	{0x0384, 0x0384}, {0x0386, 0x0386}, {0x0388, 0x038A}, {0x038C, 0x038C}, 
	{0x038E, 0x03A1}, {0x03A3, 0x03E1}, {0x03F0, 0x03FF}, {0x1D26, 0x1D2A}, 
	{0x1D5D, 0x1D61}, {0x1D66, 0x1D6A}, {0x1DBF, 0x1DBF}, {0x1F00, 0x1F15}, 
	{0x1F18, 0x1F1D}, {0x1F20, 0x1F45}, {0x1F48, 0x1F4D}, {0x1F50, 0x1F57}, 
	{0x1F59, 0x1F59}, {0x1F5B, 0x1F5B}, {0x1F5D, 0x1F5D}, {0x1F5F, 0x1F7D}, 
	{0x1F80, 0x1FB4}, {0x1FB6, 0x1FC4}, {0x1FC6, 0x1FD3}, {0x1FD6, 0x1FDB}, 
	{0x1FDD, 0x1FEF}, {0x1FF2, 0x1FF4}, {0x1FF6, 0x1FFE}, {0x2126, 0x2126}, 
	{0xAB65, 0xAB65}, {0x10140, 0x1018E}, {0x101A0, 0x101A0}, {0x1D200, 0x1D245}, 
};
static const guji_rune_range_t guji_prop_Gujarati[] = {
	{0x0A81, 0x0A83}, {0x0A85, 0x0A8D}, {0x0A8F, 0x0A91}, {0x0A93, 0x0AA8}, 
	{0x0AAA, 0x0AB0}, {0x0AB2, 0x0AB3}, {0x0AB5, 0x0AB9}, {0x0ABC, 0x0AC5}, 
	{0x0AC7, 0x0AC9}, {0x0ACB, 0x0ACD}, {0x0AD0, 0x0AD0}, {0x0AE0, 0x0AE3}, 
	{0x0AE6, 0x0AF1}, {0x0AF9, 0x0AFF}, 
};
static const guji_rune_range_t guji_prop_Gunjala_Gondi[] = {
	{0x11D60, 0x11D65}, {0x11D67, 0x11D68}, {0x11D6A, 0x11D8E}, {0x11D90, 0x11D91}, 
	{0x11D93, 0x11D98}, {0x11DA0, 0x11DA9}, 
};
static const guji_rune_range_t guji_prop_Gurmukhi[] = {
	{0x0A01, 0x0A03}, {0x0A05, 0x0A0A}, {0x0A0F, 0x0A10}, {0x0A13, 0x0A28}, 
	{0x0A2A, 0x0A30}, {0x0A32, 0x0A33}, {0x0A35, 0x0A36}, {0x0A38, 0x0A39}, 
	{0x0A3C, 0x0A3C}, {0x0A3E, 0x0A42}, {0x0A47, 0x0A48}, {0x0A4B, 0x0A4D}, 
	{0x0A51, 0x0A51}, {0x0A59, 0x0A5C}, {0x0A5E, 0x0A5E}, {0x0A66, 0x0A76}, 
};
static const guji_rune_range_t guji_prop_Han[] = {
	{0x2E80, 0x2E99}, {0x2E9B, 0x2EF3}, {0x2F00, 0x2FD5}, {0x3005, 0x3005}, 
	{0x3007, 0x3007}, {0x3021, 0x3029}, {0x3038, 0x303B}, {0x3400, 0x4DBF}, 
	{0x4E00, 0x9FFF}, {0xF900, 0xFA6D}, {0xFA70, 0xFAD9}, {0x16FE2, 0x16FE3}, 
	{0x16FF0, 0x16FF1}, {0x20000, 0x2A6DF}, {0x2A700, 0x2B739}, {0x2B740, 0x2B81D}, 
	{0x2B820, 0x2CEA1}, {0x2CEB0, 0x2EBE0}, {0x2F800, 0x2FA1D}, {0x30000, 0x3134A}, 
	{0x31350, 0x323AF}, 
};
static const guji_rune_range_t guji_prop_Hangul[] = {
	{0x1100, 0x11FF}, {0x302E, 0x302F}, {0x3131, 0x318E}, {0x3200, 0x321E}, 
	{0x3260, 0x327E}, {0xA960, 0xA97C}, {0xAC00, 0xD7A3}, {0xD7B0, 0xD7C6}, 
	{0xD7CB, 0xD7FB}, {0xFFA0, 0xFFBE}, {0xFFC2, 0xFFC7}, {0xFFCA, 0xFFCF}, 
	{0xFFD2, 0xFFD7}, {0xFFDA, 0xFFDC}, 
};
static const guji_rune_range_t guji_prop_Hanifi_Rohingya[] = {
	{0x10D00, 0x10D27}, {0x10D30, 0x10D39}, 
};
static const guji_rune_range_t guji_prop_Hanunoo[] = {
	{0x1720, 0x1734}, 
};
static const guji_rune_range_t guji_prop_Hatran[] = {
	{0x108E0, 0x108F2}, {0x108F4, 0x108F5}, {0x108FB, 0x108FF}, 
};
static const guji_rune_range_t guji_prop_Hebrew[] = {
	{0x0591, 0x05C7}, {0x05D0, 0x05EA}, {0x05EF, 0x05F4}, {0xFB1D, 0xFB36}, 
	{0xFB38, 0xFB3C}, {0xFB3E, 0xFB3E}, {0xFB40, 0xFB41}, {0xFB43, 0xFB44}, 
	{0xFB46, 0xFB4F}, 
};
static const guji_rune_range_t guji_prop_Hiragana[] = {
	{0x3041, 0x3096}, {0x309D, 0x309F}, {0x1B001, 0x1B11F}, {0x1B132, 0x1B132}, 
	{0x1B150, 0x1B152}, {0x1F200, 0x1F200}, 
};
static const guji_rune_range_t guji_prop_Imperial_Aramaic[] = {
	{0x10840, 0x10855}, {0x10857, 0x1085F}, 
};
static const guji_rune_range_t guji_prop_Inherited[] = {
	{0x0300, 0x036F}, {0x0485, 0x0486}, {0x064B, 0x0655}, {0x0670, 0x0670}, 
	{0x0951, 0x0954}, {0x1AB0, 0x1ACE}, {0x1CD0, 0x1CD2}, {0x1CD4, 0x1CE0}, 
	{0x1CE2, 0x1CE8}, {0x1CED, 0x1CED}, {0x1CF4, 0x1CF4}, {0x1CF8, 0x1CF9}, 
	{0x1DC0, 0x1DFF}, {0x200C, 0x200D}, {0x20D0, 0x20F0}, {0x302A, 0x302D}, 
	{0x3099, 0x309A}, {0xFE00, 0xFE0F}, {0xFE20, 0xFE2D}, {0x101FD, 0x101FD}, 
	{0x102E0, 0x102E0}, {0x1133B, 0x1133B}, {0x1CF00, 0x1CF2D}, {0x1CF30, 0x1CF46}, 
	{0x1D167, 0x1D169}, {0x1D17B, 0x1D182}, {0x1D185, 0x1D18B}, {0x1D1AA, 0x1D1AD}, 
	{0xE0100, 0xE01EF}, 
};
static const guji_rune_range_t guji_prop_Inscriptional_Pahlavi[] = {
	{0x10B60, 0x10B72}, {0x10B78, 0x10B7F}, 
};
static const guji_rune_range_t guji_prop_Inscriptional_Parthian[] = {
	{0x10B40, 0x10B55}, {0x10B58, 0x10B5F}, 
};
static const guji_rune_range_t guji_prop_Javanese[] = {
	{0xA980, 0xA9CD}, {0xA9D0, 0xA9D9}, {0xA9DE, 0xA9DF}, 
};
static const guji_rune_range_t guji_prop_Kaithi[] = {
	{0x11080, 0x110C2}, {0x110CD, 0x110CD}, 
};
static const guji_rune_range_t guji_prop_Kannada[] = {
	{0x0C80, 0x0C8C}, {0x0C8E, 0x0C90}, {0x0C92, 0x0CA8}, {0x0CAA, 0x0CB3}, 
	{0x0CB5, 0x0CB9}, {0x0CBC, 0x0CC4}, {0x0CC6, 0x0CC8}, {0x0CCA, 0x0CCD}, 
	{0x0CD5, 0x0CD6}, {0x0CDD, 0x0CDE}, {0x0CE0, 0x0CE3}, {0x0CE6, 0x0CEF}, 
	{0x0CF1, 0x0CF3}, 
};
static const guji_rune_range_t guji_prop_Katakana[] = {
	{0x30A1, 0x30FA}, {0x30FD, 0x30FF}, {0x31F0, 0x31FF}, {0x32D0, 0x32FE}, 
	{0x3300, 0x3357}, {0xFF66, 0xFF6F}, {0xFF71, 0xFF9D}, {0x1AFF0, 0x1AFF3}, 
	{0x1AFF5, 0x1AFFB}, {0x1AFFD, 0x1AFFE}, {0x1B000, 0x1B000}, {0x1B120, 0x1B122}, 
	{0x1B155, 0x1B155}, {0x1B164, 0x1B167}, 
};
static const guji_rune_range_t guji_prop_Kawi[] = {
	{0x11F00, 0x11F10}, {0x11F12, 0x11F3A}, {0x11F3E, 0x11F59}, 
};
static const guji_rune_range_t guji_prop_Kayah_Li[] = {
	{0xA900, 0xA92D}, {0xA92F, 0xA92F}, 
};
static const guji_rune_range_t guji_prop_Kharoshthi[] = {
	{0x10A00, 0x10A03}, {0x10A05, 0x10A06}, {0x10A0C, 0x10A13}, {0x10A15, 0x10A17}, 
	{0x10A19, 0x10A35}, {0x10A38, 0x10A3A}, {0x10A3F, 0x10A48}, {0x10A50, 0x10A58}, 
};
static const guji_rune_range_t guji_prop_Khitan_Small_Script[] = {
	{0x16FE4, 0x16FE4}, {0x18B00, 0x18CD5}, 
};
static const guji_rune_range_t guji_prop_Khmer[] = {
	{0x1780, 0x17DD}, {0x17E0, 0x17E9}, {0x17F0, 0x17F9}, {0x19E0, 0x19FF}, 
};
static const guji_rune_range_t guji_prop_Khojki[] = {
	{0x11200, 0x11211}, {0x11213, 0x11241}, 
};
static const guji_rune_range_t guji_prop_Khudawadi[] = {
	{0x112B0, 0x112EA}, {0x112F0, 0x112F9}, 
};
static const guji_rune_range_t guji_prop_L[] = {
	{0x0041, 0x005A}, {0x0061, 0x007A}, {0x00AA, 0x00AA}, {0x00B5, 0x00B5}, 
	{0x00BA, 0x00BA}, {0x00C0, 0x00D6}, {0x00D8, 0x00F6}, {0x00F8, 0x02C1}, 
	{0x02C6, 0x02D1}, {0x02E0, 0x02E4}, {0x02EC, 0x02EC}, {0x02EE, 0x02EE}, 
	{0x0370, 0x0374}, {0x0376, 0x0377}, {0x037A, 0x037D}, {0x037F, 0x037F}, 
	{0x0386, 0x0386}, {0x0388, 0x038A}, {0x038C, 0x038C}, {0x038E, 0x03A1}, 
	{0x03A3, 0x03F5}, {0x03F7, 0x0481}, {0x048A, 0x052F}, {0x0531, 0x0556}, 
	{0x0559, 0x0559}, {0x0560, 0x0588}, {0x05D0, 0x05EA}, {0x05EF, 0x05F2}, 
	{0x0620, 0x064A}, {0x066E, 0x066F}, {0x0671, 0x06D3}, {0x06D5, 0x06D5}, 
	{0x06E5, 0x06E6}, {0x06EE, 0x06EF}, {0x06FA, 0x06FC}, {0x06FF, 0x06FF}, 
	{0x0710, 0x0710}, {0x0712, 0x072F}, {0x074D, 0x07A5}, {0x07B1, 0x07B1}, 
	{0x07CA, 0x07EA}, {0x07F4, 0x07F5}, {0x07FA, 0x07FA}, {0x0800, 0x0815}, 
	{0x081A, 0x081A}, {0x0824, 0x0824}, {0x0828, 0x0828}, {0x0840, 0x0858}, 
	{0x0860, 0x086A}, {0x0870, 0x0887}, {0x0889, 0x088E}, {0x08A0, 0x08C9}, 
	{0x0904, 0x0939}, {0x093D, 0x093D}, {0x0950, 0x0950}, {0x0958, 0x0961}, 
	{0x0971, 0x0980}, {0x0985, 0x098C}, {0x098F, 0x0990}, {0x0993, 0x09A8}, 
	{0x09AA, 0x09B0}, {0x09B2, 0x09B2}, {0x09B6, 0x09B9}, {0x09BD, 0x09BD}, 
	{0x09CE, 0x09CE}, {0x09DC, 0x09DD}, {0x09DF, 0x09E1}, {0x09F0, 0x09F1}, 
	{0x09FC, 0x09FC}, {0x0A05, 0x0A0A}, {0x0A0F, 0x0A10}, {0x0A13, 0x0A28}, 
	{0x0A2A, 0x0A30}, {0x0A32, 0x0A33}, {0x0A35, 0x0A36}, {0x0A38, 0x0A39}, 
	{0x0A59, 0x0A5C}, {0x0A5E, 0x0A5E}, {0x0A72, 0x0A74}, {0x0A85, 0x0A8D}, 
	{0x0A8F, 0x0A91}, {0x0A93, 0x0AA8}, {0x0AAA, 0x0AB0}, {0x0AB2, 0x0AB3}, 
	{0x0AB5, 0x0AB9}, {0x0ABD, 0x0ABD}, {0x0AD0, 0x0AD0}, {0x0AE0, 0x0AE1}, 
	{0x0AF9, 0x0AF9}, {0x0B05, 0x0B0C}, {0x0B0F, 0x0B10}, {0x0B13, 0x0B28}, 
	{0x0B2A, 0x0B30}, {0x0B32, 0x0B33}, {0x0B35, 0x0B39}, {0x0B3D, 0x0B3D}, 
	{0x0B5C, 0x0B5D}, {0x0B5F, 0x0B61}, {0x0B71, 0x0B71}, {0x0B83, 0x0B83}, 
	{0x0B85, 0x0B8A}, {0x0B8E, 0x0B90}, {0x0B92, 0x0B95}, {0x0B99, 0x0B9A}, 
	{0x0B9C, 0x0B9C}, {0x0B9E, 0x0B9F}, {0x0BA3, 0x0BA4}, {0x0BA8, 0x0BAA}, 
	{0x0BAE, 0x0BB9}, {0x0BD0, 0x0BD0}, {0x0C05, 0x0C0C}, {0x0C0E, 0x0C10}, 
	{0x0C12, 0x0C28}, {0x0C2A, 0x0C39}, {0x0C3D, 0x0C3D}, {0x0C58, 0x0C5A}, 
	{0x0C5D, 0x0C5D}, {0x0C60, 0x0C61}, {0x0C80, 0x0C80}, {0x0C85, 0x0C8C}, 
	{0x0C8E, 0x0C90}, {0x0C92, 0x0CA8}, {0x0CAA, 0x0CB3}, {0x0CB5, 0x0CB9}, 
	{0x0CBD, 0x0CBD}, {0x0CDD, 0x0CDE}, {0x0CE0, 0x0CE1}, {0x0CF1, 0x0CF2}, 
	{0x0D04, 0x0D0C}, {0x0D0E, 0x0D10}, {0x0D12, 0x0D3A}, {0x0D3D, 0x0D3D}, 
	{0x0D4E, 0x0D4E}, {0x0D54, 0x0D56}, {0x0D5F, 0x0D61}, {0x0D7A, 0x0D7F}, 
	{0x0D85, 0x0D96}, {0x0D9A, 0x0DB1}, {0x0DB3, 0x0DBB}, {0x0DBD, 0x0DBD}, 
	{0x0DC0, 0x0DC6}, {0x0E01, 0x0E30}, {0x0E32, 0x0E33}, {0x0E40, 0x0E46}, 
	{0x0E81, 0x0E82}, {0x0E84, 0x0E84}, {0x0E86, 0x0E8A}, {0x0E8C, 0x0EA3}, 
	{0x0EA5, 0x0EA5}, {0x0EA7, 0x0EB0}, {0x0EB2, 0x0EB3}, {0x0EBD, 0x0EBD}, 
	{0x0EC0, 0x0EC4}, {0x0EC6, 0x0EC6}, {0x0EDC, 0x0EDF}, {0x0F00, 0x0F00}, 
	{0x0F40, 0x0F47}, {0x0F49, 0x0F6C}, {0x0F88, 0x0F8C}, {0x1000, 0x102A}, 
	{0x103F, 0x103F}, {0x1050, 0x1055}, {0x105A, 0x105D}, {0x1061, 0x1061}, 
	{0x1065, 0x1066}, {0x106E, 0x1070}, {0x1075, 0x1081}, {0x108E, 0x108E}, 
	{0x10A0, 0x10C5}, {0x10C7, 0x10C7}, {0x10CD, 0x10CD}, {0x10D0, 0x10FA}, 
	{0x10FC, 0x1248}, {0x124A, 0x124D}, {0x1250, 0x1256}, {0x1258, 0x1258}, 
	{0x125A, 0x125D}, {0x1260, 0x1288}, {0x128A, 0x128D}, {0x1290, 0x12B0}, 
	{0x12B2, 0x12B5}, {0x12B8, 0x12BE}, {0x12C0, 0x12C0}, {0x12C2, 0x12C5}, 
	{0x12C8, 0x12D6}, {0x12D8, 0x1310}, {0x1312, 0x1315}, {0x1318, 0x135A}, 
	{0x1380, 0x138F}, {0x13A0, 0x13F5}, {0x13F8, 0x13FD}, {0x1401, 0x166C}, 
	{0x166F, 0x167F}, {0x1681, 0x169A}, {0x16A0, 0x16EA}, {0x16F1, 0x16F8}, 
	{0x1700, 0x1711}, {0x171F, 0x1731}, {0x1740, 0x1751}, {0x1760, 0x176C}, 
	{0x176E, 0x1770}, {0x1780, 0x17B3}, {0x17D7, 0x17D7}, {0x17DC, 0x17DC}, 
	{0x1820, 0x1878}, {0x1880, 0x1884}, {0x1887, 0x18A8}, {0x18AA, 0x18AA}, 
	{0x18B0, 0x18F5}, {0x1900, 0x191E}, {0x1950, 0x196D}, {0x1970, 0x1974}, 
	{0x1980, 0x19AB}, {0x19B0, 0x19C9}, {0x1A00, 0x1A16}, {0x1A20, 0x1A54}, 
	{0x1AA7, 0x1AA7}, {0x1B05, 0x1B33}, {0x1B45, 0x1B4C}, {0x1B83, 0x1BA0}, 
	{0x1BAE, 0x1BAF}, {0x1BBA, 0x1BE5}, {0x1C00, 0x1C23}, {0x1C4D, 0x1C4F}, 
	{0x1C5A, 0x1C7D}, {0x1C80, 0x1C88}, {0x1C90, 0x1CBA}, {0x1CBD, 0x1CBF}, 
	{0x1CE9, 0x1CEC}, {0x1CEE, 0x1CF3}, {0x1CF5, 0x1CF6}, {0x1CFA, 0x1CFA}, 
	{0x1D00, 0x1DBF}, {0x1E00, 0x1F15}, {0x1F18, 0x1F1D}, {0x1F20, 0x1F45}, 
	{0x1F48, 0x1F4D}, {0x1F50, 0x1F57}, {0x1F59, 0x1F59}, {0x1F5B, 0x1F5B}, 
	{0x1F5D, 0x1F5D}, {0x1F5F, 0x1F7D}, {0x1F80, 0x1FB4}, {0x1FB6, 0x1FBC}, 
	{0x1FBE, 0x1FBE}, {0x1FC2, 0x1FC4}, {0x1FC6, 0x1FCC}, {0x1FD0, 0x1FD3}, 
	{0x1FD6, 0x1FDB}, {0x1FE0, 0x1FEC}, {0x1FF2, 0x1FF4}, {0x1FF6, 0x1FFC}, 
	{0x2071, 0x2071}, {0x207F, 0x207F}, {0x2090, 0x209C}, {0x2102, 0x2102}, 
	{0x2107, 0x2107}, {0x210A, 0x2113}, {0x2115, 0x2115}, {0x2119, 0x211D}, 
	{0x2124, 0x2124}, {0x2126, 0x2126}, {0x2128, 0x2128}, {0x212A, 0x212D}, 
	{0x212F, 0x2139}, {0x213C, 0x213F}, {0x2145, 0x2149}, {0x214E, 0x214E}, 
	{0x2183, 0x2184}, {0x2C00, 0x2CE4}, {0x2CEB, 0x2CEE}, {0x2CF2, 0x2CF3}, 
	{0x2D00, 0x2D25}, {0x2D27, 0x2D27}, {0x2D2D, 0x2D2D}, {0x2D30, 0x2D67}, 
	{0x2D6F, 0x2D6F}, {0x2D80, 0x2D96}, {0x2DA0, 0x2DA6}, {0x2DA8, 0x2DAE}, 
	{0x2DB0, 0x2DB6}, {0x2DB8, 0x2DBE}, {0x2DC0, 0x2DC6}, {0x2DC8, 0x2DCE}, 
	{0x2DD0, 0x2DD6}, {0x2DD8, 0x2DDE}, {0x2E2F, 0x2E2F}, {0x3005, 0x3006}, 
	{0x3031, 0x3035}, {0x303B, 0x303C}, {0x3041, 0x3096}, {0x309D, 0x309F}, 
	{0x30A1, 0x30FA}, {0x30FC, 0x30FF}, {0x3105, 0x312F}, {0x3131, 0x318E}, 
	{0x31A0, 0x31BF}, {0x31F0, 0x31FF}, {0x3400, 0x4DBF}, {0x4E00, 0xA48C}, 
	{0xA4D0, 0xA4FD}, {0xA500, 0xA60C}, {0xA610, 0xA61F}, {0xA62A, 0xA62B}, 
	{0xA640, 0xA66E}, {0xA67F, 0xA69D}, {0xA6A0, 0xA6E5}, {0xA717, 0xA71F}, 
	{0xA722, 0xA788}, {0xA78B, 0xA7CA}, {0xA7D0, 0xA7D1}, {0xA7D3, 0xA7D3}, 
	{0xA7D5, 0xA7D9}, {0xA7F2, 0xA801}, {0xA803, 0xA805}, {0xA807, 0xA80A}, 
	{0xA80C, 0xA822}, {0xA840, 0xA873}, {0xA882, 0xA8B3}, {0xA8F2, 0xA8F7}, 
	{0xA8FB, 0xA8FB}, {0xA8FD, 0xA8FE}, {0xA90A, 0xA925}, {0xA930, 0xA946}, 
	{0xA960, 0xA97C}, {0xA984, 0xA9B2}, {0xA9CF, 0xA9CF}, {0xA9E0, 0xA9E4}, 
	{0xA9E6, 0xA9EF}, {0xA9FA, 0xA9FE}, {0xAA00, 0xAA28}, {0xAA40, 0xAA42}, 
	{0xAA44, 0xAA4B}, {0xAA60, 0xAA76}, {0xAA7A, 0xAA7A}, {0xAA7E, 0xAAAF}, 
	{0xAAB1, 0xAAB1}, {0xAAB5, 0xAAB6}, {0xAAB9, 0xAABD}, {0xAAC0, 0xAAC0}, 
	{0xAAC2, 0xAAC2}, {0xAADB, 0xAADD}, {0xAAE0, 0xAAEA}, {0xAAF2, 0xAAF4}, 
	{0xAB01, 0xAB06}, {0xAB09, 0xAB0E}, {0xAB11, 0xAB16}, {0xAB20, 0xAB26}, 
	{0xAB28, 0xAB2E}, {0xAB30, 0xAB5A}, {0xAB5C, 0xAB69}, {0xAB70, 0xABE2}, 
	{0xAC00, 0xD7A3}, {0xD7B0, 0xD7C6}, {0xD7CB, 0xD7FB}, {0xF900, 0xFA6D}, 
	{0xFA70, 0xFAD9}, {0xFB00, 0xFB06}, {0xFB13, 0xFB17}, {0xFB1D, 0xFB1D}, 
	{0xFB1F, 0xFB28}, {0xFB2A, 0xFB36}, {0xFB38, 0xFB3C}, {0xFB3E, 0xFB3E}, 
	{0xFB40, 0xFB41}, {0xFB43, 0xFB44}, {0xFB46, 0xFBB1}, {0xFBD3, 0xFD3D}, 
	{0xFD50, 0xFD8F}, {0xFD92, 0xFDC7}, {0xFDF0, 0xFDFB}, {0xFE70, 0xFE74}, 
	{0xFE76, 0xFEFC}, {0xFF21, 0xFF3A}, {0xFF41, 0xFF5A}, {0xFF66, 0xFFBE}, 
	{0xFFC2, 0xFFC7}, {0xFFCA, 0xFFCF}, {0xFFD2, 0xFFD7}, {0xFFDA, 0xFFDC}, 
	{0x10000, 0x1000B}, {0x1000D, 0x10026}, {0x10028, 0x1003A}, {0x1003C, 0x1003D}, 
	{0x1003F, 0x1004D}, {0x10050, 0x1005D}, {0x10080, 0x100FA}, {0x10280, 0x1029C}, 
	{0x102A0, 0x102D0}, {0x10300, 0x1031F}, {0x1032D, 0x10340}, {0x10342, 0x10349}, 
	{0x10350, 0x10375}, {0x10380, 0x1039D}, {0x103A0, 0x103C3}, {0x103C8, 0x103CF}, 
	{0x10400, 0x1049D}, {0x104B0, 0x104D3}, {0x104D8, 0x104FB}, {0x10500, 0x10527}, 
	{0x10530, 0x10563}, {0x10570, 0x1057A}, {0x1057C, 0x1058A}, {0x1058C, 0x10592}, 
	{0x10594, 0x10595}, {0x10597, 0x105A1}, {0x105A3, 0x105B1}, {0x105B3, 0x105B9}, 
	{0x105BB, 0x105BC}, {0x10600, 0x10736}, {0x10740, 0x10755}, {0x10760, 0x10767}, 
	{0x10780, 0x10785}, {0x10787, 0x107B0}, {0x107B2, 0x107BA}, {0x10800, 0x10805}, 
	{0x10808, 0x10808}, {0x1080A, 0x10835}, {0x10837, 0x10838}, {0x1083C, 0x1083C}, 
	{0x1083F, 0x10855}, {0x10860, 0x10876}, {0x10880, 0x1089E}, {0x108E0, 0x108F2}, 
	{0x108F4, 0x108F5}, {0x10900, 0x10915}, {0x10920, 0x10939}, {0x10980, 0x109B7}, 
	{0x109BE, 0x109BF}, {0x10A00, 0x10A00}, {0x10A10, 0x10A13}, {0x10A15, 0x10A17}, 
	{0x10A19, 0x10A35}, {0x10A60, 0x10A7C}, {0x10A80, 0x10A9C}, {0x10AC0, 0x10AC7}, 
	{0x10AC9, 0x10AE4}, {0x10B00, 0x10B35}, {0x10B40, 0x10B55}, {0x10B60, 0x10B72}, 
	{0x10B80, 0x10B91}, {0x10C00, 0x10C48}, {0x10C80, 0x10CB2}, {0x10CC0, 0x10CF2}, 
	{0x10D00, 0x10D23}, {0x10E80, 0x10EA9}, {0x10EB0, 0x10EB1}, {0x10F00, 0x10F1C}, 
	{0x10F27, 0x10F27}, {0x10F30, 0x10F45}, {0x10F70, 0x10F81}, {0x10FB0, 0x10FC4}, 
	{0x10FE0, 0x10FF6}, {0x11003, 0x11037}, {0x11071, 0x11072}, {0x11075, 0x11075}, 
	{0x11083, 0x110AF}, {0x110D0, 0x110E8}, {0x11103, 0x11126}, {0x11144, 0x11144}, 
	{0x11147, 0x11147}, {0x11150, 0x11172}, {0x11176, 0x11176}, {0x11183, 0x111B2}, 
	{0x111C1, 0x111C4}, {0x111DA, 0x111DA}, {0x111DC, 0x111DC}, {0x11200, 0x11211}, 
	{0x11213, 0x1122B}, {0x1123F, 0x11240}, {0x11280, 0x11286}, {0x11288, 0x11288}, 
	{0x1128A, 0x1128D}, {0x1128F, 0x1129D}, {0x1129F, 0x112A8}, {0x112B0, 0x112DE}, 
	{0x11305, 0x1130C}, {0x1130F, 0x11310}, {0x11313, 0x11328}, {0x1132A, 0x11330}, 
	{0x11332, 0x11333}, {0x11335, 0x11339}, {0x1133D, 0x1133D}, {0x11350, 0x11350}, 
	{0x1135D, 0x11361}, {0x11400, 0x11434}, {0x11447, 0x1144A}, {0x1145F, 0x11461}, 
	{0x11480, 0x114AF}, {0x114C4, 0x114C5}, {0x114C7, 0x114C7}, {0x11580, 0x115AE}, 
	{0x115D8, 0x115DB}, {0x11600, 0x1162F}, {0x11644, 0x11644}, {0x11680, 0x116AA}, 
	{0x116B8, 0x116B8}, {0x11700, 0x1171A}, {0x11740, 0x11746}, {0x11800, 0x1182B}, 
	{0x118A0, 0x118DF}, {0x118FF, 0x11906}, {0x11909, 0x11909}, {0x1190C, 0x11913}, 
	{0x11915, 0x11916}, {0x11918, 0x1192F}, {0x1193F, 0x1193F}, {0x11941, 0x11941}, 
	{0x119A0, 0x119A7}, {0x119AA, 0x119D0}, {0x119E1, 0x119E1}, {0x119E3, 0x119E3}, 
	{0x11A00, 0x11A00}, {0x11A0B, 0x11A32}, {0x11A3A, 0x11A3A}, {0x11A50, 0x11A50}, 
	{0x11A5C, 0x11A89}, {0x11A9D, 0x11A9D}, {0x11AB0, 0x11AF8}, {0x11C00, 0x11C08}, 
	{0x11C0A, 0x11C2E}, {0x11C40, 0x11C40}, {0x11C72, 0x11C8F}, {0x11D00, 0x11D06}, 
	{0x11D08, 0x11D09}, {0x11D0B, 0x11D30}, {0x11D46, 0x11D46}, {0x11D60, 0x11D65}, 
	{0x11D67, 0x11D68}, {0x11D6A, 0x11D89}, {0x11D98, 0x11D98}, {0x11EE0, 0x11EF2}, 
	{0x11F02, 0x11F02}, {0x11F04, 0x11F10}, {0x11F12, 0x11F33}, {0x11FB0, 0x11FB0}, 
	{0x12000, 0x12399}, {0x12480, 0x12543}, {0x12F90, 0x12FF0}, {0x13000, 0x1342F}, 
	{0x13441, 0x13446}, {0x14400, 0x14646}, {0x16800, 0x16A38}, {0x16A40, 0x16A5E}, 
	{0x16A70, 0x16ABE}, {0x16AD0, 0x16AED}, {0x16B00, 0x16B2F}, {0x16B40, 0x16B43}, 
	{0x16B63, 0x16B77}, {0x16B7D, 0x16B8F}, {0x16E40, 0x16E7F}, {0x16F00, 0x16F4A}, 
	{0x16F50, 0x16F50}, {0x16F93, 0x16F9F}, {0x16FE0, 0x16FE1}, {0x16FE3, 0x16FE3}, 
	{0x17000, 0x187F7}, {0x18800, 0x18CD5}, {0x18D00, 0x18D08}, {0x1AFF0, 0x1AFF3}, 
	{0x1AFF5, 0x1AFFB}, {0x1AFFD, 0x1AFFE}, {0x1B000, 0x1B122}, {0x1B132, 0x1B132}, 
	{0x1B150, 0x1B152}, {0x1B155, 0x1B155}, {0x1B164, 0x1B167}, {0x1B170, 0x1B2FB}, 
	{0x1BC00, 0x1BC6A}, {0x1BC70, 0x1BC7C}, {0x1BC80, 0x1BC88}, {0x1BC90, 0x1BC99}, 
	{0x1D400, 0x1D454}, {0x1D456, 0x1D49C}, {0x1D49E, 0x1D49F}, {0x1D4A2, 0x1D4A2}, 
	{0x1D4A5, 0x1D4A6}, {0x1D4A9, 0x1D4AC}, {0x1D4AE, 0x1D4B9}, {0x1D4BB, 0x1D4BB}, 
	{0x1D4BD, 0x1D4C3}, {0x1D4C5, 0x1D505}, {0x1D507, 0x1D50A}, {0x1D50D, 0x1D514}, 
	{0x1D516, 0x1D51C}, {0x1D51E, 0x1D539}, {0x1D53B, 0x1D53E}, {0x1D540, 0x1D544}, 
	{0x1D546, 0x1D546}, {0x1D54A, 0x1D550}, {0x1D552, 0x1D6A5}, {0x1D6A8, 0x1D6C0}, 
	{0x1D6C2, 0x1D6DA}, {0x1D6DC, 0x1D6FA}, {0x1D6FC, 0x1D714}, {0x1D716, 0x1D734}, 
	{0x1D736, 0x1D74E}, {0x1D750, 0x1D76E}, {0x1D770, 0x1D788}, {0x1D78A, 0x1D7A8}, 
	{0x1D7AA, 0x1D7C2}, {0x1D7C4, 0x1D7CB}, {0x1DF00, 0x1DF1E}, {0x1DF25, 0x1DF2A}, 
	{0x1E030, 0x1E06D}, {0x1E100, 0x1E12C}, {0x1E137, 0x1E13D}, {0x1E14E, 0x1E14E}, 
	{0x1E290, 0x1E2AD}, {0x1E2C0, 0x1E2EB}, {0x1E4D0, 0x1E4EB}, {0x1E7E0, 0x1E7E6}, 
	{0x1E7E8, 0x1E7EB}, {0x1E7ED, 0x1E7EE}, {0x1E7F0, 0x1E7FE}, {0x1E800, 0x1E8C4}, 
	{0x1E900, 0x1E943}, {0x1E94B, 0x1E94B}, {0x1EE00, 0x1EE03}, {0x1EE05, 0x1EE1F}, 
	{0x1EE21, 0x1EE22}, {0x1EE24, 0x1EE24}, {0x1EE27, 0x1EE27}, {0x1EE29, 0x1EE32}, 
	{0x1EE34, 0x1EE37}, {0x1EE39, 0x1EE39}, {0x1EE3B, 0x1EE3B}, {0x1EE42, 0x1EE42}, 
	{0x1EE47, 0x1EE47}, {0x1EE49, 0x1EE49}, {0x1EE4B, 0x1EE4B}, {0x1EE4D, 0x1EE4F}, 
	{0x1EE51, 0x1EE52}, {0x1EE54, 0x1EE54}, {0x1EE57, 0x1EE57}, {0x1EE59, 0x1EE59}, 
	{0x1EE5B, 0x1EE5B}, {0x1EE5D, 0x1EE5D}, {0x1EE5F, 0x1EE5F}, {0x1EE61, 0x1EE62}, 
	{0x1EE64, 0x1EE64}, {0x1EE67, 0x1EE6A}, {0x1EE6C, 0x1EE72}, {0x1EE74, 0x1EE77}, 
	{0x1EE79, 0x1EE7C}, {0x1EE7E, 0x1EE7E}, {0x1EE80, 0x1EE89}, {0x1EE8B, 0x1EE9B}, 
	{0x1EEA1, 0x1EEA3}, {0x1EEA5, 0x1EEA9}, {0x1EEAB, 0x1EEBB}, {0x20000, 0x2A6DF}, 
	{0x2A700, 0x2B739}, {0x2B740, 0x2B81D}, {0x2B820, 0x2CEA1}, {0x2CEB0, 0x2EBE0}, 
	{0x2F800, 0x2FA1D}, {0x30000, 0x3134A}, {0x31350, 0x323AF}, 
};
static const guji_rune_range_t guji_prop_Lao[] = {
	{0x0E81, 0x0E82}, {0x0E84, 0x0E84}, {0x0E86, 0x0E8A}, {0x0E8C, 0x0EA3}, 
	{0x0EA5, 0x0EA5}, {0x0EA7, 0x0EBD}, {0x0EC0, 0x0EC4}, {0x0EC6, 0x0EC6}, 
	{0x0EC8, 0x0ECE}, {0x0ED0, 0x0ED9}, {0x0EDC, 0x0EDF}, 
};
static const guji_rune_range_t guji_prop_Latin[] = {
	{0x0041, 0x005A}, {0x0061, 0x007A}, {0x00AA, 0x00AA}, {0x00BA, 0x00BA}, 
	{0x00C0, 0x00D6}, {0x00D8, 0x00F6}, {0x00F8, 0x02B8}, {0x02E0, 0x02E4}, 
	{0x1D00, 0x1D25}, {0x1D2C, 0x1D5C}, {0x1D62, 0x1D65}, {0x1D6B, 0x1D77}, 
	{0x1D79, 0x1DBE}, {0x1E00, 0x1EFF}, {0x2071, 0x2071}, {0x207F, 0x207F}, 
	{0x2090, 0x209C}, {0x212A, 0x212B}, {0x2132, 0x2132}, {0x214E, 0x214E}, 
	{0x2160, 0x2188}, {0x2C60, 0x2C7F}, {0xA722, 0xA787}, {0xA78B, 0xA7CA}, 
	{0xA7D0, 0xA7D1}, {0xA7D3, 0xA7D3}, {0xA7D5, 0xA7D9}, {0xA7F2, 0xA7FF}, 
	{0xAB30, 0xAB5A}, {0xAB5C, 0xAB64}, {0xAB66, 0xAB69}, {0xFB00, 0xFB06}, 
	{0xFF21, 0xFF3A}, {0xFF41, 0xFF5A}, {0x10780, 0x10785}, {0x10787, 0x107B0}, 
	{0x107B2, 0x107BA}, {0x1DF00, 0x1DF1E}, {0x1DF25, 0x1DF2A}, 
};
static const guji_rune_range_t guji_prop_Lepcha[] = {
	{0x1C00, 0x1C37}, {0x1C3B, 0x1C49}, {0x1C4D, 0x1C4F}, 
};
static const guji_rune_range_t guji_prop_Limbu[] = {
	{0x1900, 0x191E}, {0x1920, 0x192B}, {0x1930, 0x193B}, {0x1940, 0x1940}, 
	{0x1944, 0x194F}, 
};
static const guji_rune_range_t guji_prop_Linear_A[] = {
	{0x10600, 0x10736}, {0x10740, 0x10755}, {0x10760, 0x10767}, 
};
static const guji_rune_range_t guji_prop_Linear_B[] = {
	{0x10000, 0x1000B}, {0x1000D, 0x10026}, {0x10028, 0x1003A}, {0x1003C, 0x1003D}, 
	{0x1003F, 0x1004D}, {0x10050, 0x1005D}, {0x10080, 0x100FA}, 
};
static const guji_rune_range_t guji_prop_Lisu[] = {
	{0xA4D0, 0xA4FF}, {0x11FB0, 0x11FB0}, 
};
static const guji_rune_range_t guji_prop_Ll[] = {
	{0x0061, 0x007A}, {0x00B5, 0x00B5}, {0x00DF, 0x00F6}, {0x00F8, 0x00FF}, 
	{0x0101, 0x0101}, {0x0103, 0x0103}, {0x0105, 0x0105}, {0x0107, 0x0107}, 
	{0x0109, 0x0109}, {0x010B, 0x010B}, {0x010D, 0x010D}, {0x010F, 0x010F}, 
	{0x0111, 0x0111}, {0x0113, 0x0113}, {0x0115, 0x0115}, {0x0117, 0x0117}, 
	{0x0119, 0x0119}, {0x011B, 0x011B}, {0x011D, 0x011D}, {0x011F, 0x011F}, 
	{0x0121, 0x0121}, {0x0123, 0x0123}, {0x0125, 0x0125}, {0x0127, 0x0127}, 
	{0x0129, 0x0129}, {0x012B, 0x012B}, {0x012D, 0x012D}, {0x012F, 0x012F}, 
	{0x0131, 0x0131}, {0x0133, 0x0133}, {0x0135, 0x0135}, {0x0137, 0x0138}, 
	{0x013A, 0x013A}, {0x013C, 0x013C}, {0x013E, 0x013E}, {0x0140, 0x0140}, 
	{0x0142, 0x0142}, {0x0144, 0x0144}, {0x0146, 0x0146}, {0x0148, 0x0149}, 
	{0x014B, 0x014B}, {0x014D, 0x014D}, {0x014F, 0x014F}, {0x0151, 0x0151}, 
	{0x0153, 0x0153}, {0x0155, 0x0155}, {0x0157, 0x0157}, {0x0159, 0x0159}, 
	{0x015B, 0x015B}, {0x015D, 0x015D}, {0x015F, 0x015F}, {0x0161, 0x0161}, 
	{0x0163, 0x0163}, {0x0165, 0x0165}, {0x0167, 0x0167}, {0x0169, 0x0169}, 
	{0x016B, 0x016B}, {0x016D, 0x016D}, {0x016F, 0x016F}, {0x0171, 0x0171}, 
	{0x0173, 0x0173}, {0x0175, 0x0175}, {0x0177, 0x0177}, {0x017A, 0x017A}, 
	{0x017C, 0x017C}, {0x017E, 0x0180}, {0x0183, 0x0183}, {0x0185, 0x0185}, 
	{0x0188, 0x0188}, {0x018C, 0x018D}, {0x0192, 0x0192}, {0x0195, 0x0195}, 
	{0x0199, 0x019B}, {0x019E, 0x019E}, {0x01A1, 0x01A1}, {0x01A3, 0x01A3}, 
	{0x01A5, 0x01A5}, {0x01A8, 0x01A8}, {0x01AA, 0x01AB}, {0x01AD, 0x01AD}, 
	{0x01B0, 0x01B0}, {0x01B4, 0x01B4}, {0x01B6, 0x01B6}, {0x01B9, 0x01BA}, 
	{0x01BD, 0x01BF}, {0x01C6, 0x01C6}, {0x01C9, 0x01C9}, {0x01CC, 0x01CC}, 
	{0x01CE, 0x01CE}, {0x01D0, 0x01D0}, {0x01D2, 0x01D2}, {0x01D4, 0x01D4}, 
	{0x01D6, 0x01D6}, {0x01D8, 0x01D8}, {0x01DA, 0x01DA}, {0x01DC, 0x01DD}, 
	{0x01DF, 0x01DF}, {0x01E1, 0x01E1}, {0x01E3, 0x01E3}, {0x01E5, 0x01E5}, 
	{0x01E7, 0x01E7}, {0x01E9, 0x01E9}, {0x01EB, 0x01EB}, {0x01ED, 0x01ED}, 
	{0x01EF, 0x01F0}, {0x01F3, 0x01F3}, {0x01F5, 0x01F5}, {0x01F9, 0x01F9}, 
	{0x01FB, 0x01FB}, {0x01FD, 0x01FD}, {0x01FF, 0x01FF}, {0x0201, 0x0201}, 
	{0x0203, 0x0203}, {0x0205, 0x0205}, {0x0207, 0x0207}, {0x0209, 0x0209}, 
	{0x020B, 0x020B}, {0x020D, 0x020D}, {0x020F, 0x020F}, {0x0211, 0x0211}, 
	{0x0213, 0x0213}, {0x0215, 0x0215}, {0x0217, 0x0217}, {0x0219, 0x0219}, 
	{0x021B, 0x021B}, {0x021D, 0x021D}, {0x021F, 0x021F}, {0x0221, 0x0221}, 
	{0x0223, 0x0223}, {0x0225, 0x0225}, {0x0227, 0x0227}, {0x0229, 0x0229}, 
	{0x022B, 0x022B}, {0x022D, 0x022D}, {0x022F, 0x022F}, {0x0231, 0x0231}, 
	{0x0233, 0x0239}, {0x023C, 0x023C}, {0x023F, 0x0240}, {0x0242, 0x0242}, 
	{0x0247, 0x0247}, {0x0249, 0x0249}, {0x024B, 0x024B}, {0x024D, 0x024D}, 
	{0x024F, 0x0293}, {0x0295, 0x02AF}, {0x0371, 0x0371}, {0x0373, 0x0373}, 
	{0x0377, 0x0377}, {0x037B, 0x037D}, {0x0390, 0x0390}, {0x03AC, 0x03CE}, 
	{0x03D0, 0x03D1}, {0x03D5, 0x03D7}, {0x03D9, 0x03D9}, {0x03DB, 0x03DB}, 
	{0x03DD, 0x03DD}, {0x03DF, 0x03DF}, {0x03E1, 0x03E1}, {0x03E3, 0x03E3}, 
	{0x03E5, 0x03E5}, {0x03E7, 0x03E7}, {0x03E9, 0x03E9}, {0x03EB, 0x03EB}, 
	{0x03ED, 0x03ED}, {0x03EF, 0x03F3}, {0x03F5, 0x03F5}, {0x03F8, 0x03F8}, 
	{0x03FB, 0x03FC}, {0x0430, 0x045F}, {0x0461, 0x0461}, {0x0463, 0x0463}, 
	{0x0465, 0x0465}, {0x0467, 0x0467}, {0x0469, 0x0469}, {0x046B, 0x046B}, 
	{0x046D, 0x046D}, {0x046F, 0x046F}, {0x0471, 0x0471}, {0x0473, 0x0473}, 
	{0x0475, 0x0475}, {0x0477, 0x0477}, {0x0479, 0x0479}, {0x047B, 0x047B}, 
	{0x047D, 0x047D}, {0x047F, 0x047F}, {0x0481, 0x0481}, {0x048B, 0x048B}, 
	{0x048D, 0x048D}, {0x048F, 0x048F}, {0x0491, 0x0491}, {0x0493, 0x0493}, 
	{0x0495, 0x0495}, {0x0497, 0x0497}, {0x0499, 0x0499}, {0x049B, 0x049B}, 
	{0x049D, 0x049D}, {0x049F, 0x049F}, {0x04A1, 0x04A1}, {0x04A3, 0x04A3}, 
	{0x04A5, 0x04A5}, {0x04A7, 0x04A7}, {0x04A9, 0x04A9}, {0x04AB, 0x04AB}, 
	{0x04AD, 0x04AD}, {0x04AF, 0x04AF}, {0x04B1, 0x04B1}, {0x04B3, 0x04B3}, 
	{0x04B5, 0x04B5}, {0x04B7, 0x04B7}, {0x04B9, 0x04B9}, {0x04BB, 0x04BB}, 
	{0x04BD, 0x04BD}, {0x04BF, 0x04BF}, {0x04C2, 0x04C2}, {0x04C4, 0x04C4}, 
	{0x04C6, 0x04C6}, {0x04C8, 0x04C8}, {0x04CA, 0x04CA}, {0x04CC, 0x04CC}, 
	{0x04CE, 0x04CF}, {0x04D1, 0x04D1}, {0x04D3, 0x04D3}, {0x04D5, 0x04D5}, 
	{0x04D7, 0x04D7}, {0x04D9, 0x04D9}, {0x04DB, 0x04DB}, {0x04DD, 0x04DD}, 
	{0x04DF, 0x04DF}, {0x04E1, 0x04E1}, {0x04E3, 0x04E3}, {0x04E5, 0x04E5}, 
	{0x04E7, 0x04E7}, {0x04E9, 0x04E9}, {0x04EB, 0x04EB}, {0x04ED, 0x04ED}, 
	{0x04EF, 0x04EF}, {0x04F1, 0x04F1}, {0x04F3, 0x04F3}, {0x04F5, 0x04F5}, 
	{0x04F7, 0x04F7}, {0x04F9, 0x04F9}, {0x04FB, 0x04FB}, {0x04FD, 0x04FD}, 
	{0x04FF, 0x04FF}, {0x0501, 0x0501}, {0x0503, 0x0503}, {0x0505, 0x0505}, 
	{0x0507, 0x0507}, {0x0509, 0x0509}, {0x050B, 0x050B}, {0x050D, 0x050D}, 
	{0x050F, 0x050F}, {0x0511, 0x0511}, {0x0513, 0x0513}, {0x0515, 0x0515}, 
	{0x0517, 0x0517}, {0x0519, 0x0519}, {0x051B, 0x051B}, {0x051D, 0x051D}, 
	{0x051F, 0x051F}, {0x0521, 0x0521}, {0x0523, 0x0523}, {0x0525, 0x0525}, 
	{0x0527, 0x0527}, {0x0529, 0x0529}, {0x052B, 0x052B}, {0x052D, 0x052D}, 
	{0x052F, 0x052F}, {0x0560, 0x0588}, {0x10D0, 0x10FA}, {0x10FD, 0x10FF}, 
	{0x13F8, 0x13FD}, {0x1C80, 0x1C88}, {0x1D00, 0x1D2B}, {0x1D6B, 0x1D77}, 
	{0x1D79, 0x1D9A}, {0x1E01, 0x1E01}, {0x1E03, 0x1E03}, {0x1E05, 0x1E05}, 
	{0x1E07, 0x1E07}, {0x1E09, 0x1E09}, {0x1E0B, 0x1E0B}, {0x1E0D, 0x1E0D}, 
	{0x1E0F, 0x1E0F}, {0x1E11, 0x1E11}, {0x1E13, 0x1E13}, {0x1E15, 0x1E15}, 
	{0x1E17, 0x1E17}, {0x1E19, 0x1E19}, {0x1E1B, 0x1E1B}, {0x1E1D, 0x1E1D}, 
	{0x1E1F, 0x1E1F}, {0x1E21, 0x1E21}, {0x1E23, 0x1E23}, {0x1E25, 0x1E25}, 
	{0x1E27, 0x1E27}, {0x1E29, 0x1E29}, {0x1E2B, 0x1E2B}, {0x1E2D, 0x1E2D}, 
	{0x1E2F, 0x1E2F}, {0x1E31, 0x1E31}, {0x1E33, 0x1E33}, {0x1E35, 0x1E35}, 
	{0x1E37, 0x1E37}, {0x1E39, 0x1E39}, {0x1E3B, 0x1E3B}, {0x1E3D, 0x1E3D}, 
	{0x1E3F, 0x1E3F}, {0x1E41, 0x1E41}, {0x1E43, 0x1E43}, {0x1E45, 0x1E45}, 
	{0x1E47, 0x1E47}, {0x1E49, 0x1E49}, {0x1E4B, 0x1E4B}, {0x1E4D, 0x1E4D}, 
	{0x1E4F, 0x1E4F}, {0x1E51, 0x1E51}, {0x1E53, 0x1E53}, {0x1E55, 0x1E55}, 
	{0x1E57, 0x1E57}, {0x1E59, 0x1E59}, {0x1E5B, 0x1E5B}, {0x1E5D, 0x1E5D}, 
	{0x1E5F, 0x1E5F}, {0x1E61, 0x1E61}, {0x1E63, 0x1E63}, {0x1E65, 0x1E65}, 
	{0x1E67, 0x1E67}, {0x1E69, 0x1E69}, {0x1E6B, 0x1E6B}, {0x1E6D, 0x1E6D}, 
	{0x1E6F, 0x1E6F}, {0x1E71, 0x1E71}, {0x1E73, 0x1E73}, {0x1E75, 0x1E75}, 
	{0x1E77, 0x1E77}, {0x1E79, 0x1E79}, {0x1E7B, 0x1E7B}, {0x1E7D, 0x1E7D}, 
	{0x1E7F, 0x1E7F}, {0x1E81, 0x1E81}, {0x1E83, 0x1E83}, {0x1E85, 0x1E85}, 
	{0x1E87, 0x1E87}, {0x1E89, 0x1E89}, {0x1E8B, 0x1E8B}, {0x1E8D, 0x1E8D}, 
	{0x1E8F, 0x1E8F}, {0x1E91, 0x1E91}, {0x1E93, 0x1E93}, {0x1E95, 0x1E9D}, 
	{0x1E9F, 0x1E9F}, {0x1EA1, 0x1EA1}, {0x1EA3, 0x1EA3}, {0x1EA5, 0x1EA5}, 
	{0x1EA7, 0x1EA7}, {0x1EA9, 0x1EA9}, {0x1EAB, 0x1EAB}, {0x1EAD, 0x1EAD}, 
	{0x1EAF, 0x1EAF}, {0x1EB1, 0x1EB1}, {0x1EB3, 0x1EB3}, {0x1EB5, 0x1EB5}, 
	{0x1EB7, 0x1EB7}, {0x1EB9, 0x1EB9}, {0x1EBB, 0x1EBB}, {0x1EBD, 0x1EBD}, 
	{0x1EBF, 0x1EBF}, {0x1EC1, 0x1EC1}, {0x1EC3, 0x1EC3}, {0x1EC5, 0x1EC5}, 
	{0x1EC7, 0x1EC7}, {0x1EC9, 0x1EC9}, {0x1ECB, 0x1ECB}, {0x1ECD, 0x1ECD}, 
	{0x1ECF, 0x1ECF}, {0x1ED1, 0x1ED1}, {0x1ED3, 0x1ED3}, {0x1ED5, 0x1ED5}, 
	{0x1ED7, 0x1ED7}, {0x1ED9, 0x1ED9}, {0x1EDB, 0x1EDB}, {0x1EDD, 0x1EDD}, 
	{0x1EDF, 0x1EDF}, {0x1EE1, 0x1EE1}, {0x1EE3, 0x1EE3}, {0x1EE5, 0x1EE5}, 
	{0x1EE7, 0x1EE7}, {0x1EE9, 0x1EE9}, {0x1EEB, 0x1EEB}, {0x1EED, 0x1EED}, 
	{0x1EEF, 0x1EEF}, {0x1EF1, 0x1EF1}, {0x1EF3, 0x1EF3}, {0x1EF5, 0x1EF5}, 
	{0x1EF7, 0x1EF7}, {0x1EF9, 0x1EF9}, {0x1EFB, 0x1EFB}, {0x1EFD, 0x1EFD}, 
	{0x1EFF, 0x1F07}, {0x1F10, 0x1F15}, {0x1F20, 0x1F27}, {0x1F30, 0x1F37}, 
	{0x1F40, 0x1F45}, {0x1F50, 0x1F57}, {0x1F60, 0x1F67}, {0x1F70, 0x1F7D}, 
	{0x1F80, 0x1F87}, {0x1F90, 0x1F97}, {0x1FA0, 0x1FA7}, {0x1FB0, 0x1FB4}, 
	{0x1FB6, 0x1FB7}, {0x1FBE, 0x1FBE}, {0x1FC2, 0x1FC4}, {0x1FC6, 0x1FC7}, 
	{0x1FD0, 0x1FD3}, {0x1FD6, 0x1FD7}, {0x1FE0, 0x1FE7}, {0x1FF2, 0x1FF4}, 
	{0x1FF6, 0x1FF7}, {0x210A, 0x210A}, {0x210E, 0x210F}, {0x2113, 0x2113}, 
	{0x212F, 0x212F}, {0x2134, 0x2134}, {0x2139, 0x2139}, {0x213C, 0x213D}, 
	{0x2146, 0x2149}, {0x214E, 0x214E}, {0x2184, 0x2184}, {0x2C30, 0x2C5F}, 
	{0x2C61, 0x2C61}, {0x2C65, 0x2C66}, {0x2C68, 0x2C68}, {0x2C6A, 0x2C6A}, 
	{0x2C6C, 0x2C6C}, {0x2C71, 0x2C71}, {0x2C73, 0x2C74}, {0x2C76, 0x2C7B}, 
	{0x2C81, 0x2C81}, {0x2C83, 0x2C83}, {0x2C85, 0x2C85}, {0x2C87, 0x2C87}, 
	{0x2C89, 0x2C89}, {0x2C8B, 0x2C8B}, {0x2C8D, 0x2C8D}, {0x2C8F, 0x2C8F}, 
	{0x2C91, 0x2C91}, {0x2C93, 0x2C93}, {0x2C95, 0x2C95}, {0x2C97, 0x2C97}, 
	{0x2C99, 0x2C99}, {0x2C9B, 0x2C9B}, {0x2C9D, 0x2C9D}, {0x2C9F, 0x2C9F}, 
	{0x2CA1, 0x2CA1}, {0x2CA3, 0x2CA3}, {0x2CA5, 0x2CA5}, {0x2CA7, 0x2CA7}, 
	{0x2CA9, 0x2CA9}, {0x2CAB, 0x2CAB}, {0x2CAD, 0x2CAD}, {0x2CAF, 0x2CAF}, 
	{0x2CB1, 0x2CB1}, {0x2CB3, 0x2CB3}, {0x2CB5, 0x2CB5}, {0x2CB7, 0x2CB7}, 
	{0x2CB9, 0x2CB9}, {0x2CBB, 0x2CBB}, {0x2CBD, 0x2CBD}, {0x2CBF, 0x2CBF}, 
	{0x2CC1, 0x2CC1}, {0x2CC3, 0x2CC3}, {0x2CC5, 0x2CC5}, {0x2CC7, 0x2CC7}, 
	{0x2CC9, 0x2CC9}, {0x2CCB, 0x2CCB}, {0x2CCD, 0x2CCD}, {0x2CCF, 0x2CCF}, 
	{0x2CD1, 0x2CD1}, {0x2CD3, 0x2CD3}, {0x2CD5, 0x2CD5}, {0x2CD7, 0x2CD7}, 
	{0x2CD9, 0x2CD9}, {0x2CDB, 0x2CDB}, {0x2CDD, 0x2CDD}, {0x2CDF, 0x2CDF}, 
	{0x2CE1, 0x2CE1}, {0x2CE3, 0x2CE4}, {0x2CEC, 0x2CEC}, {0x2CEE, 0x2CEE}, 
	{0x2CF3, 0x2CF3}, {0x2D00, 0x2D25}, {0x2D27, 0x2D27}, {0x2D2D, 0x2D2D}, 
	{0xA641, 0xA641}, {0xA643, 0xA643}, {0xA645, 0xA645}, {0xA647, 0xA647}, 
	{0xA649, 0xA649}, {0xA64B, 0xA64B}, {0xA64D, 0xA64D}, {0xA64F, 0xA64F}, 
	{0xA651, 0xA651}, {0xA653, 0xA653}, {0xA655, 0xA655}, {0xA657, 0xA657}, 
	{0xA659, 0xA659}, {0xA65B, 0xA65B}, {0xA65D, 0xA65D}, {0xA65F, 0xA65F}, 
	{0xA661, 0xA661}, {0xA663, 0xA663}, {0xA665, 0xA665}, {0xA667, 0xA667}, 
	{0xA669, 0xA669}, {0xA66B, 0xA66B}, {0xA66D, 0xA66D}, {0xA681, 0xA681}, 
	{0xA683, 0xA683}, {0xA685, 0xA685}, {0xA687, 0xA687}, {0xA689, 0xA689}, 
	{0xA68B, 0xA68B}, {0xA68D, 0xA68D}, {0xA68F, 0xA68F}, {0xA691, 0xA691}, 
	{0xA693, 0xA693}, {0xA695, 0xA695}, {0xA697, 0xA697}, {0xA699, 0xA699}, 
	{0xA69B, 0xA69B}, {0xA723, 0xA723}, {0xA725, 0xA725}, {0xA727, 0xA727}, 
	{0xA729, 0xA729}, {0xA72B, 0xA72B}, {0xA72D, 0xA72D}, {0xA72F, 0xA731}, 
	{0xA733, 0xA733}, {0xA735, 0xA735}, {0xA737, 0xA737}, {0xA739, 0xA739}, 
	{0xA73B, 0xA73B}, {0xA73D, 0xA73D}, {0xA73F, 0xA73F}, {0xA741, 0xA741}, 
	{0xA743, 0xA743}, {0xA745, 0xA745}, {0xA747, 0xA747}, {0xA749, 0xA749}, 
	{0xA74B, 0xA74B}, {0xA74D, 0xA74D}, {0xA74F, 0xA74F}, {0xA751, 0xA751}, 
	{0xA753, 0xA753}, {0xA755, 0xA755}, {0xA757, 0xA757}, {0xA759, 0xA759}, 
	{0xA75B, 0xA75B}, {0xA75D, 0xA75D}, {0xA75F, 0xA75F}, {0xA761, 0xA761}, 
	{0xA763, 0xA763}, {0xA765, 0xA765}, {0xA767, 0xA767}, {0xA769, 0xA769}, 
	{0xA76B, 0xA76B}, {0xA76D, 0xA76D}, {0xA76F, 0xA76F}, {0xA771, 0xA778}, 
	{0xA77A, 0xA77A}, {0xA77C, 0xA77C}, {0xA77F, 0xA77F}, {0xA781, 0xA781}, 
	{0xA783, 0xA783}, {0xA785, 0xA785}, {0xA787, 0xA787}, {0xA78C, 0xA78C}, 
	{0xA78E, 0xA78E}, {0xA791, 0xA791}, {0xA793, 0xA795}, {0xA797, 0xA797}, 
	{0xA799, 0xA799}, {0xA79B, 0xA79B}, {0xA79D, 0xA79D}, {0xA79F, 0xA79F}, 
	{0xA7A1, 0xA7A1}, {0xA7A3, 0xA7A3}, {0xA7A5, 0xA7A5}, {0xA7A7, 0xA7A7}, 
	{0xA7A9, 0xA7A9}, {0xA7AF, 0xA7AF}, {0xA7B5, 0xA7B5}, {0xA7B7, 0xA7B7}, 
	{0xA7B9, 0xA7B9}, {0xA7BB, 0xA7BB}, {0xA7BD, 0xA7BD}, {0xA7BF, 0xA7BF}, 
	{0xA7C1, 0xA7C1}, {0xA7C3, 0xA7C3}, {0xA7C8, 0xA7C8}, {0xA7CA, 0xA7CA}, 
	{0xA7D1, 0xA7D1}, {0xA7D3, 0xA7D3}, {0xA7D5, 0xA7D5}, {0xA7D7, 0xA7D7}, 
	{0xA7D9, 0xA7D9}, {0xA7F6, 0xA7F6}, {0xA7FA, 0xA7FA}, {0xAB30, 0xAB5A}, 
	{0xAB60, 0xAB68}, {0xAB70, 0xABBF}, {0xFB00, 0xFB06}, {0xFB13, 0xFB17}, 
	{0xFF41, 0xFF5A}, {0x10428, 0x1044F}, {0x104D8, 0x104FB}, {0x10597, 0x105A1}, 
	{0x105A3, 0x105B1}, {0x105B3, 0x105B9}, {0x105BB, 0x105BC}, {0x10CC0, 0x10CF2}, 
	{0x118C0, 0x118DF}, {0x16E60, 0x16E7F}, {0x1D41A, 0x1D433}, {0x1D44E, 0x1D454}, 
	{0x1D456, 0x1D467}, {0x1D482, 0x1D49B}, {0x1D4B6, 0x1D4B9}, {0x1D4BB, 0x1D4BB}, 
	{0x1D4BD, 0x1D4C3}, {0x1D4C5, 0x1D4CF}, {0x1D4EA, 0x1D503}, {0x1D51E, 0x1D537}, 
	{0x1D552, 0x1D56B}, {0x1D586, 0x1D59F}, {0x1D5BA, 0x1D5D3}, {0x1D5EE, 0x1D607}, 
	{0x1D622, 0x1D63B}, {0x1D656, 0x1D66F}, {0x1D68A, 0x1D6A5}, {0x1D6C2, 0x1D6DA}, 
	{0x1D6DC, 0x1D6E1}, {0x1D6FC, 0x1D714}, {0x1D716, 0x1D71B}, {0x1D736, 0x1D74E}, 
	{0x1D750, 0x1D755}, {0x1D770, 0x1D788}, {0x1D78A, 0x1D78F}, {0x1D7AA, 0x1D7C2}, 
	{0x1D7C4, 0x1D7C9}, {0x1D7CB, 0x1D7CB}, {0x1DF00, 0x1DF09}, {0x1DF0B, 0x1DF1E}, 
	{0x1DF25, 0x1DF2A}, {0x1E922, 0x1E943}, 
};
static const guji_rune_range_t guji_prop_Lm[] = {
	{0x02B0, 0x02C1}, {0x02C6, 0x02D1}, {0x02E0, 0x02E4}, {0x02EC, 0x02EC}, 
	{0x02EE, 0x02EE}, {0x0374, 0x0374}, {0x037A, 0x037A}, {0x0559, 0x0559}, 
	{0x0640, 0x0640}, {0x06E5, 0x06E6}, {0x07F4, 0x07F5}, {0x07FA, 0x07FA}, 
	{0x081A, 0x081A}, {0x0824, 0x0824}, {0x0828, 0x0828}, {0x08C9, 0x08C9}, 
	{0x0971, 0x0971}, {0x0E46, 0x0E46}, {0x0EC6, 0x0EC6}, {0x10FC, 0x10FC}, 
	{0x17D7, 0x17D7}, {0x1843, 0x1843}, {0x1AA7, 0x1AA7}, {0x1C78, 0x1C7D}, 
	{0x1D2C, 0x1D6A}, {0x1D78, 0x1D78}, {0x1D9B, 0x1DBF}, {0x2071, 0x2071}, 
	{0x207F, 0x207F}, {0x2090, 0x209C}, {0x2C7C, 0x2C7D}, {0x2D6F, 0x2D6F}, 
	{0x2E2F, 0x2E2F}, {0x3005, 0x3005}, {0x3031, 0x3035}, {0x303B, 0x303B}, 
	{0x309D, 0x309E}, {0x30FC, 0x30FE}, {0xA015, 0xA015}, {0xA4F8, 0xA4FD}, 
	{0xA60C, 0xA60C}, {0xA67F, 0xA67F}, {0xA69C, 0xA69D}, {0xA717, 0xA71F}, 
	{0xA770, 0xA770}, {0xA788, 0xA788}, {0xA7F2, 0xA7F4}, {0xA7F8, 0xA7F9}, 
	{0xA9CF, 0xA9CF}, {0xA9E6, 0xA9E6}, {0xAA70, 0xAA70}, {0xAADD, 0xAADD}, 
	{0xAAF3, 0xAAF4}, {0xAB5C, 0xAB5F}, {0xAB69, 0xAB69}, {0xFF70, 0xFF70}, 
	{0xFF9E, 0xFF9F}, {0x10780, 0x10785}, {0x10787, 0x107B0}, {0x107B2, 0x107BA}, 
	{0x16B40, 0x16B43}, {0x16F93, 0x16F9F}, {0x16FE0, 0x16FE1}, {0x16FE3, 0x16FE3}, 
	{0x1AFF0, 0x1AFF3}, {0x1AFF5, 0x1AFFB}, {0x1AFFD, 0x1AFFE}, {0x1E030, 0x1E06D}, 
	{0x1E137, 0x1E13D}, {0x1E4EB, 0x1E4EB}, {0x1E94B, 0x1E94B}, 
};
static const guji_rune_range_t guji_prop_Lo[] = {
	{0x00AA, 0x00AA}, {0x00BA, 0x00BA}, {0x01BB, 0x01BB}, {0x01C0, 0x01C3}, 
	{0x0294, 0x0294}, {0x05D0, 0x05EA}, {0x05EF, 0x05F2}, {0x0620, 0x063F}, 
	{0x0641, 0x064A}, {0x066E, 0x066F}, {0x0671, 0x06D3}, {0x06D5, 0x06D5}, 
	{0x06EE, 0x06EF}, {0x06FA, 0x06FC}, {0x06FF, 0x06FF}, {0x0710, 0x0710}, 
	{0x0712, 0x072F}, {0x074D, 0x07A5}, {0x07B1, 0x07B1}, {0x07CA, 0x07EA}, 
	{0x0800, 0x0815}, {0x0840, 0x0858}, {0x0860, 0x086A}, {0x0870, 0x0887}, 
	{0x0889, 0x088E}, {0x08A0, 0x08C8}, {0x0904, 0x0939}, {0x093D, 0x093D}, 
	{0x0950, 0x0950}, {0x0958, 0x0961}, {0x0972, 0x0980}, {0x0985, 0x098C}, 
	{0x098F, 0x0990}, {0x0993, 0x09A8}, {0x09AA, 0x09B0}, {0x09B2, 0x09B2}, 
	{0x09B6, 0x09B9}, {0x09BD, 0x09BD}, {0x09CE, 0x09CE}, {0x09DC, 0x09DD}, 
	{0x09DF, 0x09E1}, {0x09F0, 0x09F1}, {0x09FC, 0x09FC}, {0x0A05, 0x0A0A}, 
	{0x0A0F, 0x0A10}, {0x0A13, 0x0A28}, {0x0A2A, 0x0A30}, {0x0A32, 0x0A33}, 
	{0x0A35, 0x0A36}, {0x0A38, 0x0A39}, {0x0A59, 0x0A5C}, {0x0A5E, 0x0A5E}, 
	{0x0A72, 0x0A74}, {0x0A85, 0x0A8D}, {0x0A8F, 0x0A91}, {0x0A93, 0x0AA8}, 
	{0x0AAA, 0x0AB0}, {0x0AB2, 0x0AB3}, {0x0AB5, 0x0AB9}, {0x0ABD, 0x0ABD}, 
	{0x0AD0, 0x0AD0}, {0x0AE0, 0x0AE1}, {0x0AF9, 0x0AF9}, {0x0B05, 0x0B0C}, 
	{0x0B0F, 0x0B10}, {0x0B13, 0x0B28}, {0x0B2A, 0x0B30}, {0x0B32, 0x0B33}, 
	{0x0B35, 0x0B39}, {0x0B3D, 0x0B3D}, {0x0B5C, 0x0B5D}, {0x0B5F, 0x0B61}, 
	{0x0B71, 0x0B71}, {0x0B83, 0x0B83}, {0x0B85, 0x0B8A}, {0x0B8E, 0x0B90}, 
	{0x0B92, 0x0B95}, {0x0B99, 0x0B9A}, {0x0B9C, 0x0B9C}, {0x0B9E, 0x0B9F}, 
	{0x0BA3, 0x0BA4}, {0x0BA8, 0x0BAA}, {0x0BAE, 0x0BB9}, {0x0BD0, 0x0BD0}, 
	{0x0C05, 0x0C0C}, {0x0C0E, 0x0C10}, {0x0C12, 0x0C28}, {0x0C2A, 0x0C39}, 
	{0x0C3D, 0x0C3D}, {0x0C58, 0x0C5A}, {0x0C5D, 0x0C5D}, {0x0C60, 0x0C61}, 
	{0x0C80, 0x0C80}, {0x0C85, 0x0C8C}, {0x0C8E, 0x0C90}, {0x0C92, 0x0CA8}, 
	{0x0CAA, 0x0CB3}, {0x0CB5, 0x0CB9}, {0x0CBD, 0x0CBD}, {0x0CDD, 0x0CDE}, 
	{0x0CE0, 0x0CE1}, {0x0CF1, 0x0CF2}, {0x0D04, 0x0D0C}, {0x0D0E, 0x0D10}, 
	{0x0D12, 0x0D3A}, {0x0D3D, 0x0D3D}, {0x0D4E, 0x0D4E}, {0x0D54, 0x0D56}, 
	{0x0D5F, 0x0D61}, {0x0D7A, 0x0D7F}, {0x0D85, 0x0D96}, {0x0D9A, 0x0DB1}, 
	{0x0DB3, 0x0DBB}, {0x0DBD, 0x0DBD}, {0x0DC0, 0x0DC6}, {0x0E01, 0x0E30}, 
	{0x0E32, 0x0E33}, {0x0E40, 0x0E45}, {0x0E81, 0x0E82}, {0x0E84, 0x0E84}, 
	{0x0E86, 0x0E8A}, {0x0E8C, 0x0EA3}, {0x0EA5, 0x0EA5}, {0x0EA7, 0x0EB0}, 
	{0x0EB2, 0x0EB3}, {0x0EBD, 0x0EBD}, {0x0EC0, 0x0EC4}, {0x0EDC, 0x0EDF}, 
	{0x0F00, 0x0F00}, {0x0F40, 0x0F47}, {0x0F49, 0x0F6C}, {0x0F88, 0x0F8C}, 
	{0x1000, 0x102A}, {0x103F, 0x103F}, {0x1050, 0x1055}, {0x105A, 0x105D}, 
	{0x1061, 0x1061}, {0x1065, 0x1066}, {0x106E, 0x1070}, {0x1075, 0x1081}, 
	{0x108E, 0x108E}, {0x1100, 0x1248}, {0x124A, 0x124D}, {0x1250, 0x1256}, 
	{0x1258, 0x1258}, {0x125A, 0x125D}, {0x1260, 0x1288}, {0x128A, 0x128D}, 
	{0x1290, 0x12B0}, {0x12B2, 0x12B5}, {0x12B8, 0x12BE}, {0x12C0, 0x12C0}, 
	{0x12C2, 0x12C5}, {0x12C8, 0x12D6}, {0x12D8, 0x1310}, {0x1312, 0x1315}, 
	{0x1318, 0x135A}, {0x1380, 0x138F}, {0x1401, 0x166C}, {0x166F, 0x167F}, 
	{0x1681, 0x169A}, {0x16A0, 0x16EA}, {0x16F1, 0x16F8}, {0x1700, 0x1711}, 
	{0x171F, 0x1731}, {0x1740, 0x1751}, {0x1760, 0x176C}, {0x176E, 0x1770}, 
	{0x1780, 0x17B3}, {0x17DC, 0x17DC}, {0x1820, 0x1842}, {0x1844, 0x1878}, 
	{0x1880, 0x1884}, {0x1887, 0x18A8}, {0x18AA, 0x18AA}, {0x18B0, 0x18F5}, 
	{0x1900, 0x191E}, {0x1950, 0x196D}, {0x1970, 0x1974}, {0x1980, 0x19AB}, 
	{0x19B0, 0x19C9}, {0x1A00, 0x1A16}, {0x1A20, 0x1A54}, {0x1B05, 0x1B33}, 
	{0x1B45, 0x1B4C}, {0x1B83, 0x1BA0}, {0x1BAE, 0x1BAF}, {0x1BBA, 0x1BE5}, 
	{0x1C00, 0x1C23}, {0x1C4D, 0x1C4F}, {0x1C5A, 0x1C77}, {0x1CE9, 0x1CEC}, 
	{0x1CEE, 0x1CF3}, {0x1CF5, 0x1CF6}, {0x1CFA, 0x1CFA}, {0x2135, 0x2138}, 
	{0x2D30, 0x2D67}, {0x2D80, 0x2D96}, {0x2DA0, 0x2DA6}, {0x2DA8, 0x2DAE}, 
	{0x2DB0, 0x2DB6}, {0x2DB8, 0x2DBE}, {0x2DC0, 0x2DC6}, {0x2DC8, 0x2DCE}, 
	{0x2DD0, 0x2DD6}, {0x2DD8, 0x2DDE}, {0x3006, 0x3006}, {0x303C, 0x303C}, 
	{0x3041, 0x3096}, {0x309F, 0x309F}, {0x30A1, 0x30FA}, {0x30FF, 0x30FF}, 
	{0x3105, 0x312F}, {0x3131, 0x318E}, {0x31A0, 0x31BF}, {0x31F0, 0x31FF}, 
	{0x3400, 0x4DBF}, {0x4E00, 0xA014}, {0xA016, 0xA48C}, {0xA4D0, 0xA4F7}, 
	{0xA500, 0xA60B}, {0xA610, 0xA61F}, {0xA62A, 0xA62B}, {0xA66E, 0xA66E}, 
	{0xA6A0, 0xA6E5}, {0xA78F, 0xA78F}, {0xA7F7, 0xA7F7}, {0xA7FB, 0xA801}, 
	{0xA803, 0xA805}, {0xA807, 0xA80A}, {0xA80C, 0xA822}, {0xA840, 0xA873}, 
	{0xA882, 0xA8B3}, {0xA8F2, 0xA8F7}, {0xA8FB, 0xA8FB}, {0xA8FD, 0xA8FE}, 
	{0xA90A, 0xA925}, {0xA930, 0xA946}, {0xA960, 0xA97C}, {0xA984, 0xA9B2}, 
	{0xA9E0, 0xA9E4}, {0xA9E7, 0xA9EF}, {0xA9FA, 0xA9FE}, {0xAA00, 0xAA28}, 
	{0xAA40, 0xAA42}, {0xAA44, 0xAA4B}, {0xAA60, 0xAA6F}, {0xAA71, 0xAA76}, 
	{0xAA7A, 0xAA7A}, {0xAA7E, 0xAAAF}, {0xAAB1, 0xAAB1}, {0xAAB5, 0xAAB6}, 
	{0xAAB9, 0xAABD}, {0xAAC0, 0xAAC0}, {0xAAC2, 0xAAC2}, {0xAADB, 0xAADC}, 
	{0xAAE0, 0xAAEA}, {0xAAF2, 0xAAF2}, {0xAB01, 0xAB06}, {0xAB09, 0xAB0E}, 
	{0xAB11, 0xAB16}, {0xAB20, 0xAB26}, {0xAB28, 0xAB2E}, {0xABC0, 0xABE2}, 
	{0xAC00, 0xD7A3}, {0xD7B0, 0xD7C6}, {0xD7CB, 0xD7FB}, {0xF900, 0xFA6D}, 
	{0xFA70, 0xFAD9}, {0xFB1D, 0xFB1D}, {0xFB1F, 0xFB28}, {0xFB2A, 0xFB36}, 
	{0xFB38, 0xFB3C}, {0xFB3E, 0xFB3E}, {0xFB40, 0xFB41}, {0xFB43, 0xFB44}, 
	{0xFB46, 0xFBB1}, {0xFBD3, 0xFD3D}, {0xFD50, 0xFD8F}, {0xFD92, 0xFDC7}, 
	{0xFDF0, 0xFDFB}, {0xFE70, 0xFE74}, {0xFE76, 0xFEFC}, {0xFF66, 0xFF6F}, 
	{0xFF71, 0xFF9D}, {0xFFA0, 0xFFBE}, {0xFFC2, 0xFFC7}, {0xFFCA, 0xFFCF}, 
	{0xFFD2, 0xFFD7}, {0xFFDA, 0xFFDC}, {0x10000, 0x1000B}, {0x1000D, 0x10026}, 
	{0x10028, 0x1003A}, {0x1003C, 0x1003D}, {0x1003F, 0x1004D}, {0x10050, 0x1005D}, 
	{0x10080, 0x100FA}, {0x10280, 0x1029C}, {0x102A0, 0x102D0}, {0x10300, 0x1031F}, 
	{0x1032D, 0x10340}, {0x10342, 0x10349}, {0x10350, 0x10375}, {0x10380, 0x1039D}, 
	{0x103A0, 0x103C3}, {0x103C8, 0x103CF}, {0x10450, 0x1049D}, {0x10500, 0x10527}, 
	{0x10530, 0x10563}, {0x10600, 0x10736}, {0x10740, 0x10755}, {0x10760, 0x10767}, 
	{0x10800, 0x10805}, {0x10808, 0x10808}, {0x1080A, 0x10835}, {0x10837, 0x10838}, 
	{0x1083C, 0x1083C}, {0x1083F, 0x10855}, {0x10860, 0x10876}, {0x10880, 0x1089E}, 
	{0x108E0, 0x108F2}, {0x108F4, 0x108F5}, {0x10900, 0x10915}, {0x10920, 0x10939}, 
	{0x10980, 0x109B7}, {0x109BE, 0x109BF}, {0x10A00, 0x10A00}, {0x10A10, 0x10A13}, 
	{0x10A15, 0x10A17}, {0x10A19, 0x10A35}, {0x10A60, 0x10A7C}, {0x10A80, 0x10A9C}, 
	{0x10AC0, 0x10AC7}, {0x10AC9, 0x10AE4}, {0x10B00, 0x10B35}, {0x10B40, 0x10B55}, 
	{0x10B60, 0x10B72}, {0x10B80, 0x10B91}, {0x10C00, 0x10C48}, {0x10D00, 0x10D23}, 
	{0x10E80, 0x10EA9}, {0x10EB0, 0x10EB1}, {0x10F00, 0x10F1C}, {0x10F27, 0x10F27}, 
	{0x10F30, 0x10F45}, {0x10F70, 0x10F81}, {0x10FB0, 0x10FC4}, {0x10FE0, 0x10FF6}, 
	{0x11003, 0x11037}, {0x11071, 0x11072}, {0x11075, 0x11075}, {0x11083, 0x110AF}, 
	{0x110D0, 0x110E8}, {0x11103, 0x11126}, {0x11144, 0x11144}, {0x11147, 0x11147}, 
	{0x11150, 0x11172}, {0x11176, 0x11176}, {0x11183, 0x111B2}, {0x111C1, 0x111C4}, 
	{0x111DA, 0x111DA}, {0x111DC, 0x111DC}, {0x11200, 0x11211}, {0x11213, 0x1122B}, 
	{0x1123F, 0x11240}, {0x11280, 0x11286}, {0x11288, 0x11288}, {0x1128A, 0x1128D}, 
	{0x1128F, 0x1129D}, {0x1129F, 0x112A8}, {0x112B0, 0x112DE}, {0x11305, 0x1130C}, 
	{0x1130F, 0x11310}, {0x11313, 0x11328}, {0x1132A, 0x11330}, {0x11332, 0x11333}, 
	{0x11335, 0x11339}, {0x1133D, 0x1133D}, {0x11350, 0x11350}, {0x1135D, 0x11361}, 
	{0x11400, 0x11434}, {0x11447, 0x1144A}, {0x1145F, 0x11461}, {0x11480, 0x114AF}, 
	{0x114C4, 0x114C5}, {0x114C7, 0x114C7}, {0x11580, 0x115AE}, {0x115D8, 0x115DB}, 
	{0x11600, 0x1162F}, {0x11644, 0x11644}, {0x11680, 0x116AA}, {0x116B8, 0x116B8}, 
	{0x11700, 0x1171A}, {0x11740, 0x11746}, {0x11800, 0x1182B}, {0x118FF, 0x11906}, 
	{0x11909, 0x11909}, {0x1190C, 0x11913}, {0x11915, 0x11916}, {0x11918, 0x1192F}, 
	{0x1193F, 0x1193F}, {0x11941, 0x11941}, {0x119A0, 0x119A7}, {0x119AA, 0x119D0}, 
	{0x119E1, 0x119E1}, {0x119E3, 0x119E3}, {0x11A00, 0x11A00}, {0x11A0B, 0x11A32}, 
	{0x11A3A, 0x11A3A}, {0x11A50, 0x11A50}, {0x11A5C, 0x11A89}, {0x11A9D, 0x11A9D}, 
	{0x11AB0, 0x11AF8}, {0x11C00, 0x11C08}, {0x11C0A, 0x11C2E}, {0x11C40, 0x11C40}, 
	{0x11C72, 0x11C8F}, {0x11D00, 0x11D06}, {0x11D08, 0x11D09}, {0x11D0B, 0x11D30}, 
	{0x11D46, 0x11D46}, {0x11D60, 0x11D65}, {0x11D67, 0x11D68}, {0x11D6A, 0x11D89}, 
	{0x11D98, 0x11D98}, {0x11EE0, 0x11EF2}, {0x11F02, 0x11F02}, {0x11F04, 0x11F10}, 
	{0x11F12, 0x11F33}, {0x11FB0, 0x11FB0}, {0x12000, 0x12399}, {0x12480, 0x12543}, 
	{0x12F90, 0x12FF0}, {0x13000, 0x1342F}, {0x13441, 0x13446}, {0x14400, 0x14646}, 
	{0x16800, 0x16A38}, {0x16A40, 0x16A5E}, {0x16A70, 0x16ABE}, {0x16AD0, 0x16AED}, 
	{0x16B00, 0x16B2F}, {0x16B63, 0x16B77}, {0x16B7D, 0x16B8F}, {0x16F00, 0x16F4A}, 
	{0x16F50, 0x16F50}, {0x17000, 0x187F7}, {0x18800, 0x18CD5}, {0x18D00, 0x18D08}, 
	{0x1B000, 0x1B122}, {0x1B132, 0x1B132}, {0x1B150, 0x1B152}, {0x1B155, 0x1B155}, 
	{0x1B164, 0x1B167}, {0x1B170, 0x1B2FB}, {0x1BC00, 0x1BC6A}, {0x1BC70, 0x1BC7C}, 
	{0x1BC80, 0x1BC88}, {0x1BC90, 0x1BC99}, {0x1DF0A, 0x1DF0A}, {0x1E100, 0x1E12C}, 
	{0x1E14E, 0x1E14E}, {0x1E290, 0x1E2AD}, {0x1E2C0, 0x1E2EB}, {0x1E4D0, 0x1E4EA}, 
	{0x1E7E0, 0x1E7E6}, {0x1E7E8, 0x1E7EB}, {0x1E7ED, 0x1E7EE}, {0x1E7F0, 0x1E7FE}, 
	{0x1E800, 0x1E8C4}, {0x1EE00, 0x1EE03}, {0x1EE05, 0x1EE1F}, {0x1EE21, 0x1EE22}, 
	{0x1EE24, 0x1EE24}, {0x1EE27, 0x1EE27}, {0x1EE29, 0x1EE32}, {0x1EE34, 0x1EE37}, 
	{0x1EE39, 0x1EE39}, {0x1EE3B, 0x1EE3B}, {0x1EE42, 0x1EE42}, {0x1EE47, 0x1EE47}, 
	{0x1EE49, 0x1EE49}, {0x1EE4B, 0x1EE4B}, {0x1EE4D, 0x1EE4F}, {0x1EE51, 0x1EE52}, 
	{0x1EE54, 0x1EE54}, {0x1EE57, 0x1EE57}, {0x1EE59, 0x1EE59}, {0x1EE5B, 0x1EE5B}, 
	{0x1EE5D, 0x1EE5D}, {0x1EE5F, 0x1EE5F}, {0x1EE61, 0x1EE62}, {0x1EE64, 0x1EE64}, 
	{0x1EE67, 0x1EE6A}, {0x1EE6C, 0x1EE72}, {0x1EE74, 0x1EE77}, {0x1EE79, 0x1EE7C}, 
	{0x1EE7E, 0x1EE7E}, {0x1EE80, 0x1EE89}, {0x1EE8B, 0x1EE9B}, {0x1EEA1, 0x1EEA3}, 
	{0x1EEA5, 0x1EEA9}, {0x1EEAB, 0x1EEBB}, {0x20000, 0x2A6DF}, {0x2A700, 0x2B739}, 
	{0x2B740, 0x2B81D}, {0x2B820, 0x2CEA1}, {0x2CEB0, 0x2EBE0}, {0x2F800, 0x2FA1D}, 
	{0x30000, 0x3134A}, {0x31350, 0x323AF}, 
};
static const guji_rune_range_t guji_prop_Lowercase[] = {
	{0x0061, 0x007A}, {0x00AA, 0x00AA}, {0x00B5, 0x00B5}, {0x00BA, 0x00BA}, 
	{0x00DF, 0x00F6}, {0x00F8, 0x00FF}, {0x0101, 0x0101}, {0x0103, 0x0103}, 
	{0x0105, 0x0105}, {0x0107, 0x0107}, {0x0109, 0x0109}, {0x010B, 0x010B}, 
	{0x010D, 0x010D}, {0x010F, 0x010F}, {0x0111, 0x0111}, {0x0113, 0x0113}, 
	{0x0115, 0x0115}, {0x0117, 0x0117}, {0x0119, 0x0119}, {0x011B, 0x011B}, 
	{0x011D, 0x011D}, {0x011F, 0x011F}, {0x0121, 0x0121}, {0x0123, 0x0123}, 
	{0x0125, 0x0125}, {0x0127, 0x0127}, {0x0129, 0x0129}, {0x012B, 0x012B}, 
	{0x012D, 0x012D}, {0x012F, 0x012F}, {0x0131, 0x0131}, {0x0133, 0x0133}, 
	{0x0135, 0x0135}, {0x0137, 0x0138}, {0x013A, 0x013A}, {0x013C, 0x013C}, 
	{0x013E, 0x013E}, {0x0140, 0x0140}, {0x0142, 0x0142}, {0x0144, 0x0144}, 
	{0x0146, 0x0146}, {0x0148, 0x0149}, {0x014B, 0x014B}, {0x014D, 0x014D}, 
	{0x014F, 0x014F}, {0x0151, 0x0151}, {0x0153, 0x0153}, {0x0155, 0x0155}, 
	{0x0157, 0x0157}, {0x0159, 0x0159}, {0x015B, 0x015B}, {0x015D, 0x015D}, 
	{0x015F, 0x015F}, {0x0161, 0x0161}, {0x0163, 0x0163}, {0x0165, 0x0165}, 
	{0x0167, 0x0167}, {0x0169, 0x0169}, {0x016B, 0x016B}, {0x016D, 0x016D}, 
	{0x016F, 0x016F}, {0x0171, 0x0171}, {0x0173, 0x0173}, {0x0175, 0x0175}, 
	{0x0177, 0x0177}, {0x017A, 0x017A}, {0x017C, 0x017C}, {0x017E, 0x0180}, 
	{0x0183, 0x0183}, {0x0185, 0x0185}, {0x0188, 0x0188}, {0x018C, 0x018D}, 
	{0x0192, 0x0192}, {0x0195, 0x0195}, {0x0199, 0x019B}, {0x019E, 0x019E}, 
	{0x01A1, 0x01A1}, {0x01A3, 0x01A3}, {0x01A5, 0x01A5}, {0x01A8, 0x01A8}, 
	{0x01AA, 0x01AB}, {0x01AD, 0x01AD}, {0x01B0, 0x01B0}, {0x01B4, 0x01B4}, 
	{0x01B6, 0x01B6}, {0x01B9, 0x01BA}, {0x01BD, 0x01BF}, {0x01C6, 0x01C6}, 
	{0x01C9, 0x01C9}, {0x01CC, 0x01CC}, {0x01CE, 0x01CE}, {0x01D0, 0x01D0}, 
	{0x01D2, 0x01D2}, {0x01D4, 0x01D4}, {0x01D6, 0x01D6}, {0x01D8, 0x01D8}, 
	{0x01DA, 0x01DA}, {0x01DC, 0x01DD}, {0x01DF, 0x01DF}, {0x01E1, 0x01E1}, 
	{0x01E3, 0x01E3}, {0x01E5, 0x01E5}, {0x01E7, 0x01E7}, {0x01E9, 0x01E9}, 
	{0x01EB, 0x01EB}, {0x01ED, 0x01ED}, {0x01EF, 0x01F0}, {0x01F3, 0x01F3}, 
	{0x01F5, 0x01F5}, {0x01F9, 0x01F9}, {0x01FB, 0x01FB}, {0x01FD, 0x01FD}, 
	{0x01FF, 0x01FF}, {0x0201, 0x0201}, {0x0203, 0x0203}, {0x0205, 0x0205}, 
	{0x0207, 0x0207}, {0x0209, 0x0209}, {0x020B, 0x020B}, {0x020D, 0x020D}, 
	{0x020F, 0x020F}, {0x0211, 0x0211}, {0x0213, 0x0213}, {0x0215, 0x0215}, 
	{0x0217, 0x0217}, {0x0219, 0x0219}, {0x021B, 0x021B}, {0x021D, 0x021D}, 
	{0x021F, 0x021F}, {0x0221, 0x0221}, {0x0223, 0x0223}, {0x0225, 0x0225}, 
	{0x0227, 0x0227}, {0x0229, 0x0229}, {0x022B, 0x022B}, {0x022D, 0x022D}, 
	{0x022F, 0x022F}, {0x0231, 0x0231}, {0x0233, 0x0239}, {0x023C, 0x023C}, 
	{0x023F, 0x0240}, {0x0242, 0x0242}, {0x0247, 0x0247}, {0x0249, 0x0249}, 
	{0x024B, 0x024B}, {0x024D, 0x024D}, {0x024F, 0x0293}, {0x0295, 0x02B8}, 
	{0x02C0, 0x02C1}, {0x02E0, 0x02E4}, {0x0345, 0x0345}, {0x0371, 0x0371}, 
	{0x0373, 0x0373}, {0x0377, 0x0377}, {0x037A, 0x037D}, {0x0390, 0x0390}, 
	{0x03AC, 0x03CE}, {0x03D0, 0x03D1}, {0x03D5, 0x03D7}, {0x03D9, 0x03D9}, 
	{0x03DB, 0x03DB}, {0x03DD, 0x03DD}, {0x03DF, 0x03DF}, {0x03E1, 0x03E1}, 
	{0x03E3, 0x03E3}, {0x03E5, 0x03E5}, {0x03E7, 0x03E7}, {0x03E9, 0x03E9}, 
	{0x03EB, 0x03EB}, {0x03ED, 0x03ED}, {0x03EF, 0x03F3}, {0x03F5, 0x03F5}, 
	{0x03F8, 0x03F8}, {0x03FB, 0x03FC}, {0x0430, 0x045F}, {0x0461, 0x0461}, 
	{0x0463, 0x0463}, {0x0465, 0x0465}, {0x0467, 0x0467}, {0x0469, 0x0469}, 
	{0x046B, 0x046B}, {0x046D, 0x046D}, {0x046F, 0x046F}, {0x0471, 0x0471}, 
	{0x0473, 0x0473}, {0x0475, 0x0475}, {0x0477, 0x0477}, {0x0479, 0x0479}, 
	{0x047B, 0x047B}, {0x047D, 0x047D}, {0x047F, 0x047F}, {0x0481, 0x0481}, 
	{0x048B, 0x048B}, {0x048D, 0x048D}, {0x048F, 0x048F}, {0x0491, 0x0491}, 
	{0x0493, 0x0493}, {0x0495, 0x0495}, {0x0497, 0x0497}, {0x0499, 0x0499}, 
	{0x049B, 0x049B}, {0x049D, 0x049D}, {0x049F, 0x049F}, {0x04A1, 0x04A1}, 
	{0x04A3, 0x04A3}, {0x04A5, 0x04A5}, {0x04A7, 0x04A7}, {0x04A9, 0x04A9}, 
	{0x04AB, 0x04AB}, {0x04AD, 0x04AD}, {0x04AF, 0x04AF}, {0x04B1, 0x04B1}, 
	{0x04B3, 0x04B3}, {0x04B5, 0x04B5}, {0x04B7, 0x04B7}, {0x04B9, 0x04B9}, 
	{0x04BB, 0x04BB}, {0x04BD, 0x04BD}, {0x04BF, 0x04BF}, {0x04C2, 0x04C2}, 
	{0x04C4, 0x04C4}, {0x04C6, 0x04C6}, {0x04C8, 0x04C8}, {0x04CA, 0x04CA}, 
	{0x04CC, 0x04CC}, {0x04CE, 0x04CF}, {0x04D1, 0x04D1}, {0x04D3, 0x04D3}, 
	{0x04D5, 0x04D5}, {0x04D7, 0x04D7}, {0x04D9, 0x04D9}, {0x04DB, 0x04DB}, 
	{0x04DD, 0x04DD}, {0x04DF, 0x04DF}, {0x04E1, 0x04E1}, {0x04E3, 0x04E3}, 
	{0x04E5, 0x04E5}, {0x04E7, 0x04E7}, {0x04E9, 0x04E9}, {0x04EB, 0x04EB}, 
	{0x04ED, 0x04ED}, {0x04EF, 0x04EF}, {0x04F1, 0x04F1}, {0x04F3, 0x04F3}, 
	{0x04F5, 0x04F5}, {0x04F7, 0x04F7}, {0x04F9, 0x04F9}, {0x04FB, 0x04FB}, 
	{0x04FD, 0x04FD}, {0x04FF, 0x04FF}, {0x0501, 0x0501}, {0x0503, 0x0503}, 
	{0x0505, 0x0505}, {0x0507, 0x0507}, {0x0509, 0x0509}, {0x050B, 0x050B}, 
	{0x050D, 0x050D}, {0x050F, 0x050F}, {0x0511, 0x0511}, {0x0513, 0x0513}, 
	{0x0515, 0x0515}, {0x0517, 0x0517}, {0x0519, 0x0519}, {0x051B, 0x051B}, 
	{0x051D, 0x051D}, {0x051F, 0x051F}, {0x0521, 0x0521}, {0x0523, 0x0523}, 
	{0x0525, 0x0525}, {0x0527, 0x0527}, {0x0529, 0x0529}, {0x052B, 0x052B}, 
	{0x052D, 0x052D}, {0x052F, 0x052F}, {0x0560, 0x0588}, {0x10D0, 0x10FA}, 
	{0x10FC, 0x10FF}, {0x13F8, 0x13FD}, {0x1C80, 0x1C88}, {0x1D00, 0x1DBF}, 
	{0x1E01, 0x1E01}, {0x1E03, 0x1E03}, {0x1E05, 0x1E05}, {0x1E07, 0x1E07}, 
	{0x1E09, 0x1E09}, {0x1E0B, 0x1E0B}, {0x1E0D, 0x1E0D}, {0x1E0F, 0x1E0F}, 
	{0x1E11, 0x1E11}, {0x1E13, 0x1E13}, {0x1E15, 0x1E15}, {0x1E17, 0x1E17}, 
	{0x1E19, 0x1E19}, {0x1E1B, 0x1E1B}, {0x1E1D, 0x1E1D}, {0x1E1F, 0x1E1F}, 
	{0x1E21, 0x1E21}, {0x1E23, 0x1E23}, {0x1E25, 0x1E25}, {0x1E27, 0x1E27}, 
	{0x1E29, 0x1E29}, {0x1E2B, 0x1E2B}, {0x1E2D, 0x1E2D}, {0x1E2F, 0x1E2F}, 
	{0x1E31, 0x1E31}, {0x1E33, 0x1E33}, {0x1E35, 0x1E35}, {0x1E37, 0x1E37}, 
	{0x1E39, 0x1E39}, {0x1E3B, 0x1E3B}, {0x1E3D, 0x1E3D}, {0x1E3F, 0x1E3F}, 
	{0x1E41, 0x1E41}, {0x1E43, 0x1E43}, {0x1E45, 0x1E45}, {0x1E47, 0x1E47}, 
	{0x1E49, 0x1E49}, {0x1E4B, 0x1E4B}, {0x1E4D, 0x1E4D}, {0x1E4F, 0x1E4F}, 
	{0x1E51, 0x1E51}, {0x1E53, 0x1E53}, {0x1E55, 0x1E55}, {0x1E57, 0x1E57}, 
	{0x1E59, 0x1E59}, {0x1E5B, 0x1E5B}, {0x1E5D, 0x1E5D}, {0x1E5F, 0x1E5F}, 
	{0x1E61, 0x1E61}, {0x1E63, 0x1E63}, {0x1E65, 0x1E65}, {0x1E67, 0x1E67}, 
	{0x1E69, 0x1E69}, {0x1E6B, 0x1E6B}, {0x1E6D, 0x1E6D}, {0x1E6F, 0x1E6F}, 
	{0x1E71, 0x1E71}, {0x1E73, 0x1E73}, {0x1E75, 0x1E75}, {0x1E77, 0x1E77}, 
	{0x1E79, 0x1E79}, {0x1E7B, 0x1E7B}, {0x1E7D, 0x1E7D}, {0x1E7F, 0x1E7F}, 
	{0x1E81, 0x1E81}, {0x1E83, 0x1E83}, {0x1E85, 0x1E85}, {0x1E87, 0x1E87}, 
	{0x1E89, 0x1E89}, {0x1E8B, 0x1E8B}, {0x1E8D, 0x1E8D}, {0x1E8F, 0x1E8F}, 
	{0x1E91, 0x1E91}, {0x1E93, 0x1E93}, {0x1E95, 0x1E9D}, {0x1E9F, 0x1E9F}, 
	{0x1EA1, 0x1EA1}, {0x1EA3, 0x1EA3}, {0x1EA5, 0x1EA5}, {0x1EA7, 0x1EA7}, 
	{0x1EA9, 0x1EA9}, {0x1EAB, 0x1EAB}, {0x1EAD, 0x1EAD}, {0x1EAF, 0x1EAF}, 
	{0x1EB1, 0x1EB1}, {0x1EB3, 0x1EB3}, {0x1EB5, 0x1EB5}, {0x1EB7, 0x1EB7}, 
	{0x1EB9, 0x1EB9}, {0x1EBB, 0x1EBB}, {0x1EBD, 0x1EBD}, {0x1EBF, 0x1EBF}, 
	{0x1EC1, 0x1EC1}, {0x1EC3, 0x1EC3}, {0x1EC5, 0x1EC5}, {0x1EC7, 0x1EC7}, 
	{0x1EC9, 0x1EC9}, {0x1ECB, 0x1ECB}, {0x1ECD, 0x1ECD}, {0x1ECF, 0x1ECF}, 
	{0x1ED1, 0x1ED1}, {0x1ED3, 0x1ED3}, {0x1ED5, 0x1ED5}, {0x1ED7, 0x1ED7}, 
	{0x1ED9, 0x1ED9}, {0x1EDB, 0x1EDB}, {0x1EDD, 0x1EDD}, {0x1EDF, 0x1EDF}, 
	{0x1EE1, 0x1EE1}, {0x1EE3, 0x1EE3}, {0x1EE5, 0x1EE5}, {0x1EE7, 0x1EE7}, 
	{0x1EE9, 0x1EE9}, {0x1EEB, 0x1EEB}, {0x1EED, 0x1EED}, {0x1EEF, 0x1EEF}, 
	{0x1EF1, 0x1EF1}, {0x1EF3, 0x1EF3}, {0x1EF5, 0x1EF5}, {0x1EF7, 0x1EF7}, 
	{0x1EF9, 0x1EF9}, {0x1EFB, 0x1EFB}, {0x1EFD, 0x1EFD}, {0x1EFF, 0x1F07}, 
	{0x1F10, 0x1F15}, {0x1F20, 0x1F27}, {0x1F30, 0x1F37}, {0x1F40, 0x1F45}, 
	{0x1F50, 0x1F57}, {0x1F60, 0x1F67}, {0x1F70, 0x1F7D}, {0x1F80, 0x1F87}, 
	{0x1F90, 0x1F97}, {0x1FA0, 0x1FA7}, {0x1FB0, 0x1FB4}, {0x1FB6, 0x1FB7}, 
	{0x1FBE, 0x1FBE}, {0x1FC2, 0x1FC4}, {0x1FC6, 0x1FC7}, {0x1FD0, 0x1FD3}, 
	{0x1FD6, 0x1FD7}, {0x1FE0, 0x1FE7}, {0x1FF2, 0x1FF4}, {0x1FF6, 0x1FF7}, 
	{0x2071, 0x2071}, {0x207F, 0x207F}, {0x2090, 0x209C}, {0x210A, 0x210A}, 
	{0x210E, 0x210F}, {0x2113, 0x2113}, {0x212F, 0x212F}, {0x2134, 0x2134}, 
	{0x2139, 0x2139}, {0x213C, 0x213D}, {0x2146, 0x2149}, {0x214E, 0x214E}, 
	{0x2170, 0x217F}, {0x2184, 0x2184}, {0x24D0, 0x24E9}, {0x2C30, 0x2C5F}, 
	{0x2C61, 0x2C61}, {0x2C65, 0x2C66}, {0x2C68, 0x2C68}, {0x2C6A, 0x2C6A}, 
	{0x2C6C, 0x2C6C}, {0x2C71, 0x2C71}, {0x2C73, 0x2C74}, {0x2C76, 0x2C7D}, 
	{0x2C81, 0x2C81}, {0x2C83, 0x2C83}, {0x2C85, 0x2C85}, {0x2C87, 0x2C87}, 
	{0x2C89, 0x2C89}, {0x2C8B, 0x2C8B}, {0x2C8D, 0x2C8D}, {0x2C8F, 0x2C8F}, 
	{0x2C91, 0x2C91}, {0x2C93, 0x2C93}, {0x2C95, 0x2C95}, {0x2C97, 0x2C97}, 
	{0x2C99, 0x2C99}, {0x2C9B, 0x2C9B}, {0x2C9D, 0x2C9D}, {0x2C9F, 0x2C9F}, 
	{0x2CA1, 0x2CA1}, {0x2CA3, 0x2CA3}, {0x2CA5, 0x2CA5}, {0x2CA7, 0x2CA7}, 
	{0x2CA9, 0x2CA9}, {0x2CAB, 0x2CAB}, {0x2CAD, 0x2CAD}, {0x2CAF, 0x2CAF}, 
	{0x2CB1, 0x2CB1}, {0x2CB3, 0x2CB3}, {0x2CB5, 0x2CB5}, {0x2CB7, 0x2CB7}, 
	{0x2CB9, 0x2CB9}, {0x2CBB, 0x2CBB}, {0x2CBD, 0x2CBD}, {0x2CBF, 0x2CBF}, 
	{0x2CC1, 0x2CC1}, {0x2CC3, 0x2CC3}, {0x2CC5, 0x2CC5}, {0x2CC7, 0x2CC7}, 
	{0x2CC9, 0x2CC9}, {0x2CCB, 0x2CCB}, {0x2CCD, 0x2CCD}, {0x2CCF, 0x2CCF}, 
	{0x2CD1, 0x2CD1}, {0x2CD3, 0x2CD3}, {0x2CD5, 0x2CD5}, {0x2CD7, 0x2CD7}, 
	{0x2CD9, 0x2CD9}, {0x2CDB, 0x2CDB}, {0x2CDD, 0x2CDD}, {0x2CDF, 0x2CDF}, 
	{0x2CE1, 0x2CE1}, {0x2CE3, 0x2CE4}, {0x2CEC, 0x2CEC}, {0x2CEE, 0x2CEE}, 
	{0x2CF3, 0x2CF3}, {0x2D00, 0x2D25}, {0x2D27, 0x2D27}, {0x2D2D, 0x2D2D}, 
	{0xA641, 0xA641}, {0xA643, 0xA643}, {0xA645, 0xA645}, {0xA647, 0xA647}, 
	{0xA649, 0xA649}, {0xA64B, 0xA64B}, {0xA64D, 0xA64D}, {0xA64F, 0xA64F}, 
	{0xA651, 0xA651}, {0xA653, 0xA653}, {0xA655, 0xA655}, {0xA657, 0xA657}, 
	{0xA659, 0xA659}, {0xA65B, 0xA65B}, {0xA65D, 0xA65D}, {0xA65F, 0xA65F}, 
	{0xA661, 0xA661}, {0xA663, 0xA663}, {0xA665, 0xA665}, {0xA667, 0xA667}, 
	{0xA669, 0xA669}, {0xA66B, 0xA66B}, {0xA66D, 0xA66D}, {0xA681, 0xA681}, 
	{0xA683, 0xA683}, {0xA685, 0xA685}, {0xA687, 0xA687}, {0xA689, 0xA689}, 
	{0xA68B, 0xA68B}, {0xA68D, 0xA68D}, {0xA68F, 0xA68F}, {0xA691, 0xA691}, 
	{0xA693, 0xA693}, {0xA695, 0xA695}, {0xA697, 0xA697}, {0xA699, 0xA699}, 
	{0xA69B, 0xA69D}, {0xA723, 0xA723}, {0xA725, 0xA725}, {0xA727, 0xA727}, 
	{0xA729, 0xA729}, {0xA72B, 0xA72B}, {0xA72D, 0xA72D}, {0xA72F, 0xA731}, 
	{0xA733, 0xA733}, {0xA735, 0xA735}, {0xA737, 0xA737}, {0xA739, 0xA739}, 
	{0xA73B, 0xA73B}, {0xA73D, 0xA73D}, {0xA73F, 0xA73F}, {0xA741, 0xA741}, 
	{0xA743, 0xA743}, {0xA745, 0xA745}, {0xA747, 0xA747}, {0xA749, 0xA749}, 
	{0xA74B, 0xA74B}, {0xA74D, 0xA74D}, {0xA74F, 0xA74F}, {0xA751, 0xA751}, 
	{0xA753, 0xA753}, {0xA755, 0xA755}, {0xA757, 0xA757}, {0xA759, 0xA759}, 
	{0xA75B, 0xA75B}, {0xA75D, 0xA75D}, {0xA75F, 0xA75F}, {0xA761, 0xA761}, 
	{0xA763, 0xA763}, {0xA765, 0xA765}, {0xA767, 0xA767}, {0xA769, 0xA769}, 
	{0xA76B, 0xA76B}, {0xA76D, 0xA76D}, {0xA76F, 0xA778}, {0xA77A, 0xA77A}, 
	{0xA77C, 0xA77C}, {0xA77F, 0xA77F}, {0xA781, 0xA781}, {0xA783, 0xA783}, 
	{0xA785, 0xA785}, {0xA787, 0xA787}, {0xA78C, 0xA78C}, {0xA78E, 0xA78E}, 
	{0xA791, 0xA791}, {0xA793, 0xA795}, {0xA797, 0xA797}, {0xA799, 0xA799}, 
	{0xA79B, 0xA79B}, {0xA79D, 0xA79D}, {0xA79F, 0xA79F}, {0xA7A1, 0xA7A1}, 
	{0xA7A3, 0xA7A3}, {0xA7A5, 0xA7A5}, {0xA7A7, 0xA7A7}, {0xA7A9, 0xA7A9}, 
	{0xA7AF, 0xA7AF}, {0xA7B5, 0xA7B5}, {0xA7B7, 0xA7B7}, {0xA7B9, 0xA7B9}, 
	{0xA7BB, 0xA7BB}, {0xA7BD, 0xA7BD}, {0xA7BF, 0xA7BF}, {0xA7C1, 0xA7C1}, 
	{0xA7C3, 0xA7C3}, {0xA7C8, 0xA7C8}, {0xA7CA, 0xA7CA}, {0xA7D1, 0xA7D1}, 
	{0xA7D3, 0xA7D3}, {0xA7D5, 0xA7D5}, {0xA7D7, 0xA7D7}, {0xA7D9, 0xA7D9}, 
	{0xA7F2, 0xA7F4}, {0xA7F6, 0xA7F6}, {0xA7F8, 0xA7FA}, {0xAB30, 0xAB5A}, 
	{0xAB5C, 0xAB69}, {0xAB70, 0xABBF}, {0xFB00, 0xFB06}, {0xFB13, 0xFB17}, 
	{0xFF41, 0xFF5A}, {0x10428, 0x1044F}, {0x104D8, 0x104FB}, {0x10597, 0x105A1}, 
	{0x105A3, 0x105B1}, {0x105B3, 0x105B9}, {0x105BB, 0x105BC}, {0x10780, 0x10780}, 
	{0x10783, 0x10785}, {0x10787, 0x107B0}, {0x107B2, 0x107BA}, {0x10CC0, 0x10CF2}, 
	{0x118C0, 0x118DF}, {0x16E60, 0x16E7F}, {0x1D41A, 0x1D433}, {0x1D44E, 0x1D454}, 
	{0x1D456, 0x1D467}, {0x1D482, 0x1D49B}, {0x1D4B6, 0x1D4B9}, {0x1D4BB, 0x1D4BB}, 
	{0x1D4BD, 0x1D4C3}, {0x1D4C5, 0x1D4CF}, {0x1D4EA, 0x1D503}, {0x1D51E, 0x1D537}, 
	{0x1D552, 0x1D56B}, {0x1D586, 0x1D59F}, {0x1D5BA, 0x1D5D3}, {0x1D5EE, 0x1D607}, 
	{0x1D622, 0x1D63B}, {0x1D656, 0x1D66F}, {0x1D68A, 0x1D6A5}, {0x1D6C2, 0x1D6DA}, 
	{0x1D6DC, 0x1D6E1}, {0x1D6FC, 0x1D714}, {0x1D716, 0x1D71B}, {0x1D736, 0x1D74E}, 
	{0x1D750, 0x1D755}, {0x1D770, 0x1D788}, {0x1D78A, 0x1D78F}, {0x1D7AA, 0x1D7C2}, 
	{0x1D7C4, 0x1D7C9}, {0x1D7CB, 0x1D7CB}, {0x1DF00, 0x1DF09}, {0x1DF0B, 0x1DF1E}, 
	{0x1DF25, 0x1DF2A}, {0x1E030, 0x1E06D}, {0x1E922, 0x1E943}, 
};
static const guji_rune_range_t guji_prop_Lt[] = {
	{0x01C5, 0x01C5}, {0x01C8, 0x01C8}, {0x01CB, 0x01CB}, {0x01F2, 0x01F2}, 
	{0x1F88, 0x1F8F}, {0x1F98, 0x1F9F}, {0x1FA8, 0x1FAF}, {0x1FBC, 0x1FBC}, 
	{0x1FCC, 0x1FCC}, {0x1FFC, 0x1FFC}, 
};
static const guji_rune_range_t guji_prop_Lu[] = {
	{0x0041, 0x005A}, {0x00C0, 0x00D6}, {0x00D8, 0x00DE}, {0x0100, 0x0100}, 
	{0x0102, 0x0102}, {0x0104, 0x0104}, {0x0106, 0x0106}, {0x0108, 0x0108}, 
	{0x010A, 0x010A}, {0x010C, 0x010C}, {0x010E, 0x010E}, {0x0110, 0x0110}, 
	{0x0112, 0x0112}, {0x0114, 0x0114}, {0x0116, 0x0116}, {0x0118, 0x0118}, 
	{0x011A, 0x011A}, {0x011C, 0x011C}, {0x011E, 0x011E}, {0x0120, 0x0120}, 
	{0x0122, 0x0122}, {0x0124, 0x0124}, {0x0126, 0x0126}, {0x0128, 0x0128}, 
	{0x012A, 0x012A}, {0x012C, 0x012C}, {0x012E, 0x012E}, {0x0130, 0x0130}, 
	{0x0132, 0x0132}, {0x0134, 0x0134}, {0x0136, 0x0136}, {0x0139, 0x0139}, 
	{0x013B, 0x013B}, {0x013D, 0x013D}, {0x013F, 0x013F}, {0x0141, 0x0141}, 
	{0x0143, 0x0143}, {0x0145, 0x0145}, {0x0147, 0x0147}, {0x014A, 0x014A}, 
	{0x014C, 0x014C}, {0x014E, 0x014E}, {0x0150, 0x0150}, {0x0152, 0x0152}, 
	{0x0154, 0x0154}, {0x0156, 0x0156}, {0x0158, 0x0158}, {0x015A, 0x015A}, 
	{0x015C, 0x015C}, {0x015E, 0x015E}, {0x0160, 0x0160}, {0x0162, 0x0162}, 
	{0x0164, 0x0164}, {0x0166, 0x0166}, {0x0168, 0x0168}, {0x016A, 0x016A}, 
	{0x016C, 0x016C}, {0x016E, 0x016E}, {0x0170, 0x0170}, {0x0172, 0x0172}, 
	{0x0174, 0x0174}, {0x0176, 0x0176}, {0x0178, 0x0179}, {0x017B, 0x017B}, 
	{0x017D, 0x017D}, {0x0181, 0x0182}, {0x0184, 0x0184}, {0x0186, 0x0187}, 
	{0x0189, 0x018B}, {0x018E, 0x0191}, {0x0193, 0x0194}, {0x0196, 0x0198}, 
	{0x019C, 0x019D}, {0x019F, 0x01A0}, {0x01A2, 0x01A2}, {0x01A4, 0x01A4}, 
	{0x01A6, 0x01A7}, {0x01A9, 0x01A9}, {0x01AC, 0x01AC}, {0x01AE, 0x01AF}, 
	{0x01B1, 0x01B3}, {0x01B5, 0x01B5}, {0x01B7, 0x01B8}, {0x01BC, 0x01BC}, 
	{0x01C4, 0x01C4}, {0x01C7, 0x01C7}, {0x01CA, 0x01CA}, {0x01CD, 0x01CD}, 
	{0x01CF, 0x01CF}, {0x01D1, 0x01D1}, {0x01D3, 0x01D3}, {0x01D5, 0x01D5}, 
	{0x01D7, 0x01D7}, {0x01D9, 0x01D9}, {0x01DB, 0x01DB}, {0x01DE, 0x01DE}, 
	{0x01E0, 0x01E0}, {0x01E2, 0x01E2}, {0x01E4, 0x01E4}, {0x01E6, 0x01E6}, 
	{0x01E8, 0x01E8}, {0x01EA, 0x01EA}, {0x01EC, 0x01EC}, {0x01EE, 0x01EE}, 
	{0x01F1, 0x01F1}, {0x01F4, 0x01F4}, {0x01F6, 0x01F8}, {0x01FA, 0x01FA}, 
	{0x01FC, 0x01FC}, {0x01FE, 0x01FE}, {0x0200, 0x0200}, {0x0202, 0x0202}, 
	{0x0204, 0x0204}, {0x0206, 0x0206}, {0x0208, 0x0208}, {0x020A, 0x020A}, 
	{0x020C, 0x020C}, {0x020E, 0x020E}, {0x0210, 0x0210}, {0x0212, 0x0212}, 
	{0x0214, 0x0214}, {0x0216, 0x0216}, {0x0218, 0x0218}, {0x021A, 0x021A}, 
	{0x021C, 0x021C}, {0x021E, 0x021E}, {0x0220, 0x0220}, {0x0222, 0x0222}, 
	{0x0224, 0x0224}, {0x0226, 0x0226}, {0x0228, 0x0228}, {0x022A, 0x022A}, 
	{0x022C, 0x022C}, {0x022E, 0x022E}, {0x0230, 0x0230}, {0x0232, 0x0232}, 
	{0x023A, 0x023B}, {0x023D, 0x023E}, {0x0241, 0x0241}, {0x0243, 0x0246}, 
	{0x0248, 0x0248}, {0x024A, 0x024A}, {0x024C, 0x024C}, {0x024E, 0x024E}, 
	{0x0370, 0x0370}, {0x0372, 0x0372}, {0x0376, 0x0376}, {0x037F, 0x037F}, 
	{0x0386, 0x0386}, {0x0388, 0x038A}, {0x038C, 0x038C}, {0x038E, 0x038F}, 
	{0x0391, 0x03A1}, {0x03A3, 0x03AB}, {0x03CF, 0x03CF}, {0x03D2, 0x03D4}, 
	{0x03D8, 0x03D8}, {0x03DA, 0x03DA}, {0x03DC, 0x03DC}, {0x03DE, 0x03DE}, 
	{0x03E0, 0x03E0}, {0x03E2, 0x03E2}, {0x03E4, 0x03E4}, {0x03E6, 0x03E6}, 
	{0x03E8, 0x03E8}, {0x03EA, 0x03EA}, {0x03EC, 0x03EC}, {0x03EE, 0x03EE}, 
	{0x03F4, 0x03F4}, {0x03F7, 0x03F7}, {0x03F9, 0x03FA}, {0x03FD, 0x042F}, 
	{0x0460, 0x0460}, {0x0462, 0x0462}, {0x0464, 0x0464}, {0x0466, 0x0466}, 
	{0x0468, 0x0468}, {0x046A, 0x046A}, {0x046C, 0x046C}, {0x046E, 0x046E}, 
	{0x0470, 0x0470}, {0x0472, 0x0472}, {0x0474, 0x0474}, {0x0476, 0x0476}, 
	{0x0478, 0x0478}, {0x047A, 0x047A}, {0x047C, 0x047C}, {0x047E, 0x047E}, 
	{0x0480, 0x0480}, {0x048A, 0x048A}, {0x048C, 0x048C}, {0x048E, 0x048E}, 
	{0x0490, 0x0490}, {0x0492, 0x0492}, {0x0494, 0x0494}, {0x0496, 0x0496}, 
	{0x0498, 0x0498}, {0x049A, 0x049A}, {0x049C, 0x049C}, {0x049E, 0x049E}, 
	{0x04A0, 0x04A0}, {0x04A2, 0x04A2}, {0x04A4, 0x04A4}, {0x04A6, 0x04A6}, 
	{0x04A8, 0x04A8}, {0x04AA, 0x04AA}, {0x04AC, 0x04AC}, {0x04AE, 0x04AE}, 
	{0x04B0, 0x04B0}, {0x04B2, 0x04B2}, {0x04B4, 0x04B4}, {0x04B6, 0x04B6}, 
	{0x04B8, 0x04B8}, {0x04BA, 0x04BA}, {0x04BC, 0x04BC}, {0x04BE, 0x04BE}, 
	{0x04C0, 0x04C1}, {0x04C3, 0x04C3}, {0x04C5, 0x04C5}, {0x04C7, 0x04C7}, 
	{0x04C9, 0x04C9}, {0x04CB, 0x04CB}, {0x04CD, 0x04CD}, {0x04D0, 0x04D0}, 
	{0x04D2, 0x04D2}, {0x04D4, 0x04D4}, {0x04D6, 0x04D6}, {0x04D8, 0x04D8}, 
	{0x04DA, 0x04DA}, {0x04DC, 0x04DC}, {0x04DE, 0x04DE}, {0x04E0, 0x04E0}, 
	{0x04E2, 0x04E2}, {0x04E4, 0x04E4}, {0x04E6, 0x04E6}, {0x04E8, 0x04E8}, 
	{0x04EA, 0x04EA}, {0x04EC, 0x04EC}, {0x04EE, 0x04EE}, {0x04F0, 0x04F0}, 
	{0x04F2, 0x04F2}, {0x04F4, 0x04F4}, {0x04F6, 0x04F6}, {0x04F8, 0x04F8}, 
	{0x04FA, 0x04FA}, {0x04FC, 0x04FC}, {0x04FE, 0x04FE}, {0x0500, 0x0500}, 
	{0x0502, 0x0502}, {0x0504, 0x0504}, {0x0506, 0x0506}, {0x0508, 0x0508}, 
	{0x050A, 0x050A}, {0x050C, 0x050C}, {0x050E, 0x050E}, {0x0510, 0x0510}, 
	{0x0512, 0x0512}, {0x0514, 0x0514}, {0x0516, 0x0516}, {0x0518, 0x0518}, 
	{0x051A, 0x051A}, {0x051C, 0x051C}, {0x051E, 0x051E}, {0x0520, 0x0520}, 
	{0x0522, 0x0522}, {0x0524, 0x0524}, {0x0526, 0x0526}, {0x0528, 0x0528}, 
	{0x052A, 0x052A}, {0x052C, 0x052C}, {0x052E, 0x052E}, {0x0531, 0x0556}, 
	{0x10A0, 0x10C5}, {0x10C7, 0x10C7}, {0x10CD, 0x10CD}, {0x13A0, 0x13F5}, 
	{0x1C90, 0x1CBA}, {0x1CBD, 0x1CBF}, {0x1E00, 0x1E00}, {0x1E02, 0x1E02}, 
	{0x1E04, 0x1E04}, {0x1E06, 0x1E06}, {0x1E08, 0x1E08}, {0x1E0A, 0x1E0A}, 
	{0x1E0C, 0x1E0C}, {0x1E0E, 0x1E0E}, {0x1E10, 0x1E10}, {0x1E12, 0x1E12}, 
	{0x1E14, 0x1E14}, {0x1E16, 0x1E16}, {0x1E18, 0x1E18}, {0x1E1A, 0x1E1A}, 
	{0x1E1C, 0x1E1C}, {0x1E1E, 0x1E1E}, {0x1E20, 0x1E20}, {0x1E22, 0x1E22}, 
	{0x1E24, 0x1E24}, {0x1E26, 0x1E26}, {0x1E28, 0x1E28}, {0x1E2A, 0x1E2A}, 
	{0x1E2C, 0x1E2C}, {0x1E2E, 0x1E2E}, {0x1E30, 0x1E30}, {0x1E32, 0x1E32}, 
	{0x1E34, 0x1E34}, {0x1E36, 0x1E36}, {0x1E38, 0x1E38}, {0x1E3A, 0x1E3A}, 
	{0x1E3C, 0x1E3C}, {0x1E3E, 0x1E3E}, {0x1E40, 0x1E40}, {0x1E42, 0x1E42}, 
	{0x1E44, 0x1E44}, {0x1E46, 0x1E46}, {0x1E48, 0x1E48}, {0x1E4A, 0x1E4A}, 
	{0x1E4C, 0x1E4C}, {0x1E4E, 0x1E4E}, {0x1E50, 0x1E50}, {0x1E52, 0x1E52}, 
	{0x1E54, 0x1E54}, {0x1E56, 0x1E56}, {0x1E58, 0x1E58}, {0x1E5A, 0x1E5A}, 
	{0x1E5C, 0x1E5C}, {0x1E5E, 0x1E5E}, {0x1E60, 0x1E60}, {0x1E62, 0x1E62}, 
	{0x1E64, 0x1E64}, {0x1E66, 0x1E66}, {0x1E68, 0x1E68}, {0x1E6A, 0x1E6A}, 
	{0x1E6C, 0x1E6C}, {0x1E6E, 0x1E6E}, {0x1E70, 0x1E70}, {0x1E72, 0x1E72}, 
	{0x1E74, 0x1E74}, {0x1E76, 0x1E76}, {0x1E78, 0x1E78}, {0x1E7A, 0x1E7A}, 
	{0x1E7C, 0x1E7C}, {0x1E7E, 0x1E7E}, {0x1E80, 0x1E80}, {0x1E82, 0x1E82}, 
	{0x1E84, 0x1E84}, {0x1E86, 0x1E86}, {0x1E88, 0x1E88}, {0x1E8A, 0x1E8A}, 
	{0x1E8C, 0x1E8C}, {0x1E8E, 0x1E8E}, {0x1E90, 0x1E90}, {0x1E92, 0x1E92}, 
	{0x1E94, 0x1E94}, {0x1E9E, 0x1E9E}, {0x1EA0, 0x1EA0}, {0x1EA2, 0x1EA2}, 
	{0x1EA4, 0x1EA4}, {0x1EA6, 0x1EA6}, {0x1EA8, 0x1EA8}, {0x1EAA, 0x1EAA}, 
	{0x1EAC, 0x1EAC}, {0x1EAE, 0x1EAE}, {0x1EB0, 0x1EB0}, {0x1EB2, 0x1EB2}, 
	{0x1EB4, 0x1EB4}, {0x1EB6, 0x1EB6}, {0x1EB8, 0x1EB8}, {0x1EBA, 0x1EBA}, 
	{0x1EBC, 0x1EBC}, {0x1EBE, 0x1EBE}, {0x1EC0, 0x1EC0}, {0x1EC2, 0x1EC2}, 
	{0x1EC4, 0x1EC4}, {0x1EC6, 0x1EC6}, {0x1EC8, 0x1EC8}, {0x1ECA, 0x1ECA}, 
	{0x1ECC, 0x1ECC}, {0x1ECE, 0x1ECE}, {0x1ED0, 0x1ED0}, {0x1ED2, 0x1ED2}, 
	{0x1ED4, 0x1ED4}, {0x1ED6, 0x1ED6}, {0x1ED8, 0x1ED8}, {0x1EDA, 0x1EDA}, 
	{0x1EDC, 0x1EDC}, {0x1EDE, 0x1EDE}, {0x1EE0, 0x1EE0}, {0x1EE2, 0x1EE2}, 
	{0x1EE4, 0x1EE4}, {0x1EE6, 0x1EE6}, {0x1EE8, 0x1EE8}, {0x1EEA, 0x1EEA}, 
	{0x1EEC, 0x1EEC}, {0x1EEE, 0x1EEE}, {0x1EF0, 0x1EF0}, {0x1EF2, 0x1EF2}, 
	{0x1EF4, 0x1EF4}, {0x1EF6, 0x1EF6}, {0x1EF8, 0x1EF8}, {0x1EFA, 0x1EFA}, 
	{0x1EFC, 0x1EFC}, {0x1EFE, 0x1EFE}, {0x1F08, 0x1F0F}, {0x1F18, 0x1F1D}, 
	{0x1F28, 0x1F2F}, {0x1F38, 0x1F3F}, {0x1F48, 0x1F4D}, {0x1F59, 0x1F59}, 
	{0x1F5B, 0x1F5B}, {0x1F5D, 0x1F5D}, {0x1F5F, 0x1F5F}, {0x1F68, 0x1F6F}, 
	{0x1FB8, 0x1FBB}, {0x1FC8, 0x1FCB}, {0x1FD8, 0x1FDB}, {0x1FE8, 0x1FEC}, 
	{0x1FF8, 0x1FFB}, {0x2102, 0x2102}, {0x2107, 0x2107}, {0x210B, 0x210D}, 
	{0x2110, 0x2112}, {0x2115, 0x2115}, {0x2119, 0x211D}, {0x2124, 0x2124}, 
	{0x2126, 0x2126}, {0x2128, 0x2128}, {0x212A, 0x212D}, {0x2130, 0x2133}, 
	{0x213E, 0x213F}, {0x2145, 0x2145}, {0x2183, 0x2183}, {0x2C00, 0x2C2F}, 
	{0x2C60, 0x2C60}, {0x2C62, 0x2C64}, {0x2C67, 0x2C67}, {0x2C69, 0x2C69}, 
	{0x2C6B, 0x2C6B}, {0x2C6D, 0x2C70}, {0x2C72, 0x2C72}, {0x2C75, 0x2C75}, 
	{0x2C7E, 0x2C80}, {0x2C82, 0x2C82}, {0x2C84, 0x2C84}, {0x2C86, 0x2C86}, 
	{0x2C88, 0x2C88}, {0x2C8A, 0x2C8A}, {0x2C8C, 0x2C8C}, {0x2C8E, 0x2C8E}, 
	{0x2C90, 0x2C90}, {0x2C92, 0x2C92}, {0x2C94, 0x2C94}, {0x2C96, 0x2C96}, 
	{0x2C98, 0x2C98}, {0x2C9A, 0x2C9A}, {0x2C9C, 0x2C9C}, {0x2C9E, 0x2C9E}, 
	{0x2CA0, 0x2CA0}, {0x2CA2, 0x2CA2}, {0x2CA4, 0x2CA4}, {0x2CA6, 0x2CA6}, 
	{0x2CA8, 0x2CA8}, {0x2CAA, 0x2CAA}, {0x2CAC, 0x2CAC}, {0x2CAE, 0x2CAE}, 
	{0x2CB0, 0x2CB0}, {0x2CB2, 0x2CB2}, {0x2CB4, 0x2CB4}, {0x2CB6, 0x2CB6}, 
	{0x2CB8, 0x2CB8}, {0x2CBA, 0x2CBA}, {0x2CBC, 0x2CBC}, {0x2CBE, 0x2CBE}, 
	{0x2CC0, 0x2CC0}, {0x2CC2, 0x2CC2}, {0x2CC4, 0x2CC4}, {0x2CC6, 0x2CC6}, 
	{0x2CC8, 0x2CC8}, {0x2CCA, 0x2CCA}, {0x2CCC, 0x2CCC}, {0x2CCE, 0x2CCE}, 
	{0x2CD0, 0x2CD0}, {0x2CD2, 0x2CD2}, {0x2CD4, 0x2CD4}, {0x2CD6, 0x2CD6}, 
	{0x2CD8, 0x2CD8}, {0x2CDA, 0x2CDA}, {0x2CDC, 0x2CDC}, {0x2CDE, 0x2CDE}, 
	{0x2CE0, 0x2CE0}, {0x2CE2, 0x2CE2}, {0x2CEB, 0x2CEB}, {0x2CED, 0x2CED}, 
	{0x2CF2, 0x2CF2}, {0xA640, 0xA640}, {0xA642, 0xA642}, {0xA644, 0xA644}, 
	{0xA646, 0xA646}, {0xA648, 0xA648}, {0xA64A, 0xA64A}, {0xA64C, 0xA64C}, 
	{0xA64E, 0xA64E}, {0xA650, 0xA650}, {0xA652, 0xA652}, {0xA654, 0xA654}, 
	{0xA656, 0xA656}, {0xA658, 0xA658}, {0xA65A, 0xA65A}, {0xA65C, 0xA65C}, 
	{0xA65E, 0xA65E}, {0xA660, 0xA660}, {0xA662, 0xA662}, {0xA664, 0xA664}, 
	{0xA666, 0xA666}, {0xA668, 0xA668}, {0xA66A, 0xA66A}, {0xA66C, 0xA66C}, 
	{0xA680, 0xA680}, {0xA682, 0xA682}, {0xA684, 0xA684}, {0xA686, 0xA686}, 
	{0xA688, 0xA688}, {0xA68A, 0xA68A}, {0xA68C, 0xA68C}, {0xA68E, 0xA68E}, 
	{0xA690, 0xA690}, {0xA692, 0xA692}, {0xA694, 0xA694}, {0xA696, 0xA696}, 
	{0xA698, 0xA698}, {0xA69A, 0xA69A}, {0xA722, 0xA722}, {0xA724, 0xA724}, 
	{0xA726, 0xA726}, {0xA728, 0xA728}, {0xA72A, 0xA72A}, {0xA72C, 0xA72C}, 
	{0xA72E, 0xA72E}, {0xA732, 0xA732}, {0xA734, 0xA734}, {0xA736, 0xA736}, 
	{0xA738, 0xA738}, {0xA73A, 0xA73A}, {0xA73C, 0xA73C}, {0xA73E, 0xA73E}, 
	{0xA740, 0xA740}, {0xA742, 0xA742}, {0xA744, 0xA744}, {0xA746, 0xA746}, 
	{0xA748, 0xA748}, {0xA74A, 0xA74A}, {0xA74C, 0xA74C}, {0xA74E, 0xA74E}, 
	{0xA750, 0xA750}, {0xA752, 0xA752}, {0xA754, 0xA754}, {0xA756, 0xA756}, 
	{0xA758, 0xA758}, {0xA75A, 0xA75A}, {0xA75C, 0xA75C}, {0xA75E, 0xA75E}, 
	{0xA760, 0xA760}, {0xA762, 0xA762}, {0xA764, 0xA764}, {0xA766, 0xA766}, 
	{0xA768, 0xA768}, {0xA76A, 0xA76A}, {0xA76C, 0xA76C}, {0xA76E, 0xA76E}, 
	{0xA779, 0xA779}, {0xA77B, 0xA77B}, {0xA77D, 0xA77E}, {0xA780, 0xA780}, 
	{0xA782, 0xA782}, {0xA784, 0xA784}, {0xA786, 0xA786}, {0xA78B, 0xA78B}, 
	{0xA78D, 0xA78D}, {0xA790, 0xA790}, {0xA792, 0xA792}, {0xA796, 0xA796}, 
	{0xA798, 0xA798}, {0xA79A, 0xA79A}, {0xA79C, 0xA79C}, {0xA79E, 0xA79E}, 
	{0xA7A0, 0xA7A0}, {0xA7A2, 0xA7A2}, {0xA7A4, 0xA7A4}, {0xA7A6, 0xA7A6}, 
	{0xA7A8, 0xA7A8}, {0xA7AA, 0xA7AE}, {0xA7B0, 0xA7B4}, {0xA7B6, 0xA7B6}, 
	{0xA7B8, 0xA7B8}, {0xA7BA, 0xA7BA}, {0xA7BC, 0xA7BC}, {0xA7BE, 0xA7BE}, 
	{0xA7C0, 0xA7C0}, {0xA7C2, 0xA7C2}, {0xA7C4, 0xA7C7}, {0xA7C9, 0xA7C9}, 
	{0xA7D0, 0xA7D0}, {0xA7D6, 0xA7D6}, {0xA7D8, 0xA7D8}, {0xA7F5, 0xA7F5}, 
	{0xFF21, 0xFF3A}, {0x10400, 0x10427}, {0x104B0, 0x104D3}, {0x10570, 0x1057A}, 
	{0x1057C, 0x1058A}, {0x1058C, 0x10592}, {0x10594, 0x10595}, {0x10C80, 0x10CB2}, 
	{0x118A0, 0x118BF}, {0x16E40, 0x16E5F}, {0x1D400, 0x1D419}, {0x1D434, 0x1D44D}, 
	{0x1D468, 0x1D481}, {0x1D49C, 0x1D49C}, {0x1D49E, 0x1D49F}, {0x1D4A2, 0x1D4A2}, 
	{0x1D4A5, 0x1D4A6}, {0x1D4A9, 0x1D4AC}, {0x1D4AE, 0x1D4B5}, {0x1D4D0, 0x1D4E9}, 
	{0x1D504, 0x1D505}, {0x1D507, 0x1D50A}, {0x1D50D, 0x1D514}, {0x1D516, 0x1D51C}, 
	{0x1D538, 0x1D539}, {0x1D53B, 0x1D53E}, {0x1D540, 0x1D544}, {0x1D546, 0x1D546}, 
	{0x1D54A, 0x1D550}, {0x1D56C, 0x1D585}, {0x1D5A0, 0x1D5B9}, {0x1D5D4, 0x1D5ED}, 
	{0x1D608, 0x1D621}, {0x1D63C, 0x1D655}, {0x1D670, 0x1D689}, {0x1D6A8, 0x1D6C0}, 
	{0x1D6E2, 0x1D6FA}, {0x1D71C, 0x1D734}, {0x1D756, 0x1D76E}, {0x1D790, 0x1D7A8}, 
	{0x1D7CA, 0x1D7CA}, {0x1E900, 0x1E921}, 
};
static const guji_rune_range_t guji_prop_Lycian[] = {
	{0x10280, 0x1029C}, 
};
static const guji_rune_range_t guji_prop_Lydian[] = {
	{0x10920, 0x10939}, {0x1093F, 0x1093F}, 
};
static const guji_rune_range_t guji_prop_M[] = {
	{0x0300, 0x036F}, {0x0483, 0x0489}, {0x0591, 0x05BD}, {0x05BF, 0x05BF}, 
	{0x05C1, 0x05C2}, {0x05C4, 0x05C5}, {0x05C7, 0x05C7}, {0x0610, 0x061A}, 
	{0x064B, 0x065F}, {0x0670, 0x0670}, {0x06D6, 0x06DC}, {0x06DF, 0x06E4}, 
	{0x06E7, 0x06E8}, {0x06EA, 0x06ED}, {0x0711, 0x0711}, {0x0730, 0x074A}, 
	{0x07A6, 0x07B0}, {0x07EB, 0x07F3}, {0x07FD, 0x07FD}, {0x0816, 0x0819}, 
	{0x081B, 0x0823}, {0x0825, 0x0827}, {0x0829, 0x082D}, {0x0859, 0x085B}, 
	{0x0898, 0x089F}, {0x08CA, 0x08E1}, {0x08E3, 0x0903}, {0x093A, 0x093C}, 
	{0x093E, 0x094F}, {0x0951, 0x0957}, {0x0962, 0x0963}, {0x0981, 0x0983}, 
	{0x09BC, 0x09BC}, {0x09BE, 0x09C4}, {0x09C7, 0x09C8}, {0x09CB, 0x09CD}, 
	{0x09D7, 0x09D7}, {0x09E2, 0x09E3}, {0x09FE, 0x09FE}, {0x0A01, 0x0A03}, 
	{0x0A3C, 0x0A3C}, {0x0A3E, 0x0A42}, {0x0A47, 0x0A48}, {0x0A4B, 0x0A4D}, 
	{0x0A51, 0x0A51}, {0x0A70, 0x0A71}, {0x0A75, 0x0A75}, {0x0A81, 0x0A83}, 
	{0x0ABC, 0x0ABC}, {0x0ABE, 0x0AC5}, {0x0AC7, 0x0AC9}, {0x0ACB, 0x0ACD}, 
	{0x0AE2, 0x0AE3}, {0x0AFA, 0x0AFF}, {0x0B01, 0x0B03}, {0x0B3C, 0x0B3C}, 
	{0x0B3E, 0x0B44}, {0x0B47, 0x0B48}, {0x0B4B, 0x0B4D}, {0x0B55, 0x0B57}, 
	{0x0B62, 0x0B63}, {0x0B82, 0x0B82}, {0x0BBE, 0x0BC2}, {0x0BC6, 0x0BC8}, 
	{0x0BCA, 0x0BCD}, {0x0BD7, 0x0BD7}, {0x0C00, 0x0C04}, {0x0C3C, 0x0C3C}, 
	{0x0C3E, 0x0C44}, {0x0C46, 0x0C48}, {0x0C4A, 0x0C4D}, {0x0C55, 0x0C56}, 
	{0x0C62, 0x0C63}, {0x0C81, 0x0C83}, {0x0CBC, 0x0CBC}, {0x0CBE, 0x0CC4}, 
	{0x0CC6, 0x0CC8}, {0x0CCA, 0x0CCD}, {0x0CD5, 0x0CD6}, {0x0CE2, 0x0CE3}, 
	{0x0CF3, 0x0CF3}, {0x0D00, 0x0D03}, {0x0D3B, 0x0D3C}, {0x0D3E, 0x0D44}, 
	{0x0D46, 0x0D48}, {0x0D4A, 0x0D4D}, {0x0D57, 0x0D57}, {0x0D62, 0x0D63}, 
	{0x0D81, 0x0D83}, {0x0DCA, 0x0DCA}, {0x0DCF, 0x0DD4}, {0x0DD6, 0x0DD6}, 
	{0x0DD8, 0x0DDF}, {0x0DF2, 0x0DF3}, {0x0E31, 0x0E31}, {0x0E34, 0x0E3A}, 
	{0x0E47, 0x0E4E}, {0x0EB1, 0x0EB1}, {0x0EB4, 0x0EBC}, {0x0EC8, 0x0ECE}, 
	{0x0F18, 0x0F19}, {0x0F35, 0x0F35}, {0x0F37, 0x0F37}, {0x0F39, 0x0F39}, 
	{0x0F3E, 0x0F3F}, {0x0F71, 0x0F84}, {0x0F86, 0x0F87}, {0x0F8D, 0x0F97}, 
	{0x0F99, 0x0FBC}, {0x0FC6, 0x0FC6}, {0x102B, 0x103E}, {0x1056, 0x1059}, 
	{0x105E, 0x1060}, {0x1062, 0x1064}, {0x1067, 0x106D}, {0x1071, 0x1074}, 
	{0x1082, 0x108D}, {0x108F, 0x108F}, {0x109A, 0x109D}, {0x135D, 0x135F}, 
	{0x1712, 0x1715}, {0x1732, 0x1734}, {0x1752, 0x1753}, {0x1772, 0x1773}, 
	{0x17B4, 0x17D3}, {0x17DD, 0x17DD}, {0x180B, 0x180D}, {0x180F, 0x180F}, 
	{0x1885, 0x1886}, {0x18A9, 0x18A9}, {0x1920, 0x192B}, {0x1930, 0x193B}, 
	{0x1A17, 0x1A1B}, {0x1A55, 0x1A5E}, {0x1A60, 0x1A7C}, {0x1A7F, 0x1A7F}, 
	{0x1AB0, 0x1ACE}, {0x1B00, 0x1B04}, {0x1B34, 0x1B44}, {0x1B6B, 0x1B73}, 
	{0x1B80, 0x1B82}, {0x1BA1, 0x1BAD}, {0x1BE6, 0x1BF3}, {0x1C24, 0x1C37}, 
	{0x1CD0, 0x1CD2}, {0x1CD4, 0x1CE8}, {0x1CED, 0x1CED}, {0x1CF4, 0x1CF4}, 
	{0x1CF7, 0x1CF9}, {0x1DC0, 0x1DFF}, {0x20D0, 0x20F0}, {0x2CEF, 0x2CF1}, 
	{0x2D7F, 0x2D7F}, {0x2DE0, 0x2DFF}, {0x302A, 0x302F}, {0x3099, 0x309A}, 
	{0xA66F, 0xA672}, {0xA674, 0xA67D}, {0xA69E, 0xA69F}, {0xA6F0, 0xA6F1}, 
	{0xA802, 0xA802}, {0xA806, 0xA806}, {0xA80B, 0xA80B}, {0xA823, 0xA827}, 
	{0xA82C, 0xA82C}, {0xA880, 0xA881}, {0xA8B4, 0xA8C5}, {0xA8E0, 0xA8F1}, 
	{0xA8FF, 0xA8FF}, {0xA926, 0xA92D}, {0xA947, 0xA953}, {0xA980, 0xA983}, 
	{0xA9B3, 0xA9C0}, {0xA9E5, 0xA9E5}, {0xAA29, 0xAA36}, {0xAA43, 0xAA43}, 
	{0xAA4C, 0xAA4D}, {0xAA7B, 0xAA7D}, {0xAAB0, 0xAAB0}, {0xAAB2, 0xAAB4}, 
	{0xAAB7, 0xAAB8}, {0xAABE, 0xAABF}, {0xAAC1, 0xAAC1}, {0xAAEB, 0xAAEF}, 
	{0xAAF5, 0xAAF6}, {0xABE3, 0xABEA}, {0xABEC, 0xABED}, {0xFB1E, 0xFB1E}, 
	{0xFE00, 0xFE0F}, {0xFE20, 0xFE2F}, {0x101FD, 0x101FD}, {0x102E0, 0x102E0}, 
	{0x10376, 0x1037A}, {0x10A01, 0x10A03}, {0x10A05, 0x10A06}, {0x10A0C, 0x10A0F}, 
	{0x10A38, 0x10A3A}, {0x10A3F, 0x10A3F}, {0x10AE5, 0x10AE6}, {0x10D24, 0x10D27}, 
	{0x10EAB, 0x10EAC}, {0x10EFD, 0x10EFF}, {0x10F46, 0x10F50}, {0x10F82, 0x10F85}, 
	{0x11000, 0x11002}, {0x11038, 0x11046}, {0x11070, 0x11070}, {0x11073, 0x11074}, 
	{0x1107F, 0x11082}, {0x110B0, 0x110BA}, {0x110C2, 0x110C2}, {0x11100, 0x11102}, 
	{0x11127, 0x11134}, {0x11145, 0x11146}, {0x11173, 0x11173}, {0x11180, 0x11182}, 
	{0x111B3, 0x111C0}, {0x111C9, 0x111CC}, {0x111CE, 0x111CF}, {0x1122C, 0x11237}, 
	{0x1123E, 0x1123E}, {0x11241, 0x11241}, {0x112DF, 0x112EA}, {0x11300, 0x11303}, 
	{0x1133B, 0x1133C}, {0x1133E, 0x11344}, {0x11347, 0x11348}, {0x1134B, 0x1134D}, 
	{0x11357, 0x11357}, {0x11362, 0x11363}, {0x11366, 0x1136C}, {0x11370, 0x11374}, 
	{0x11435, 0x11446}, {0x1145E, 0x1145E}, {0x114B0, 0x114C3}, {0x115AF, 0x115B5}, 
	{0x115B8, 0x115C0}, {0x115DC, 0x115DD}, {0x11630, 0x11640}, {0x116AB, 0x116B7}, 
	{0x1171D, 0x1172B}, {0x1182C, 0x1183A}, {0x11930, 0x11935}, {0x11937, 0x11938}, 
	{0x1193B, 0x1193E}, {0x11940, 0x11940}, {0x11942, 0x11943}, {0x119D1, 0x119D7}, 
	{0x119DA, 0x119E0}, {0x119E4, 0x119E4}, {0x11A01, 0x11A0A}, {0x11A33, 0x11A39}, 
	{0x11A3B, 0x11A3E}, {0x11A47, 0x11A47}, {0x11A51, 0x11A5B}, {0x11A8A, 0x11A99}, 
	{0x11C2F, 0x11C36}, {0x11C38, 0x11C3F}, {0x11C92, 0x11CA7}, {0x11CA9, 0x11CB6}, 
	{0x11D31, 0x11D36}, {0x11D3A, 0x11D3A}, {0x11D3C, 0x11D3D}, {0x11D3F, 0x11D45}, 
	{0x11D47, 0x11D47}, {0x11D8A, 0x11D8E}, {0x11D90, 0x11D91}, {0x11D93, 0x11D97}, 
	{0x11EF3, 0x11EF6}, {0x11F00, 0x11F01}, {0x11F03, 0x11F03}, {0x11F34, 0x11F3A}, 
	{0x11F3E, 0x11F42}, {0x13440, 0x13440}, {0x13447, 0x13455}, {0x16AF0, 0x16AF4}, 
	{0x16B30, 0x16B36}, {0x16F4F, 0x16F4F}, {0x16F51, 0x16F87}, {0x16F8F, 0x16F92}, 
	{0x16FE4, 0x16FE4}, {0x16FF0, 0x16FF1}, {0x1BC9D, 0x1BC9E}, {0x1CF00, 0x1CF2D}, 
	{0x1CF30, 0x1CF46}, {0x1D165, 0x1D169}, {0x1D16D, 0x1D172}, {0x1D17B, 0x1D182}, 
	{0x1D185, 0x1D18B}, {0x1D1AA, 0x1D1AD}, {0x1D242, 0x1D244}, {0x1DA00, 0x1DA36}, 
	{0x1DA3B, 0x1DA6C}, {0x1DA75, 0x1DA75}, {0x1DA84, 0x1DA84}, {0x1DA9B, 0x1DA9F}, 
	{0x1DAA1, 0x1DAAF}, {0x1E000, 0x1E006}, {0x1E008, 0x1E018}, {0x1E01B, 0x1E021}, 
	{0x1E023, 0x1E024}, {0x1E026, 0x1E02A}, {0x1E08F, 0x1E08F}, {0x1E130, 0x1E136}, 
	{0x1E2AE, 0x1E2AE}, {0x1E2EC, 0x1E2EF}, {0x1E4EC, 0x1E4EF}, {0x1E8D0, 0x1E8D6}, 
	{0x1E944, 0x1E94A}, {0xE0100, 0xE01EF}, 
};
static const guji_rune_range_t guji_prop_Mahajani[] = {
	{0x11150, 0x11176}, 
};
static const guji_rune_range_t guji_prop_Makasar[] = {
	{0x11EE0, 0x11EF8}, 
};
static const guji_rune_range_t guji_prop_Malayalam[] = {
	{0x0D00, 0x0D0C}, {0x0D0E, 0x0D10}, {0x0D12, 0x0D44}, {0x0D46, 0x0D48}, 
	{0x0D4A, 0x0D4F}, {0x0D54, 0x0D63}, {0x0D66, 0x0D7F}, 
};
static const guji_rune_range_t guji_prop_Mandaic[] = {
	{0x0840, 0x085B}, {0x085E, 0x085E}, 
};
static const guji_rune_range_t guji_prop_Manichaean[] = {
	{0x10AC0, 0x10AE6}, {0x10AEB, 0x10AF6}, 
};
static const guji_rune_range_t guji_prop_Marchen[] = {
	{0x11C70, 0x11C8F}, {0x11C92, 0x11CA7}, {0x11CA9, 0x11CB6}, 
};
static const guji_rune_range_t guji_prop_Masaram_Gondi[] = {
	{0x11D00, 0x11D06}, {0x11D08, 0x11D09}, {0x11D0B, 0x11D36}, {0x11D3A, 0x11D3A}, 
	{0x11D3C, 0x11D3D}, {0x11D3F, 0x11D47}, {0x11D50, 0x11D59}, 
};
static const guji_rune_range_t guji_prop_Mc[] = {
	{0x0903, 0x0903}, {0x093B, 0x093B}, {0x093E, 0x0940}, {0x0949, 0x094C}, 
	{0x094E, 0x094F}, {0x0982, 0x0983}, {0x09BE, 0x09C0}, {0x09C7, 0x09C8}, 
	{0x09CB, 0x09CC}, {0x09D7, 0x09D7}, {0x0A03, 0x0A03}, {0x0A3E, 0x0A40}, 
	{0x0A83, 0x0A83}, {0x0ABE, 0x0AC0}, {0x0AC9, 0x0AC9}, {0x0ACB, 0x0ACC}, 
	{0x0B02, 0x0B03}, {0x0B3E, 0x0B3E}, {0x0B40, 0x0B40}, {0x0B47, 0x0B48}, 
	{0x0B4B, 0x0B4C}, {0x0B57, 0x0B57}, {0x0BBE, 0x0BBF}, {0x0BC1, 0x0BC2}, 
	{0x0BC6, 0x0BC8}, {0x0BCA, 0x0BCC}, {0x0BD7, 0x0BD7}, {0x0C01, 0x0C03}, 
	{0x0C41, 0x0C44}, {0x0C82, 0x0C83}, {0x0CBE, 0x0CBE}, {0x0CC0, 0x0CC4}, 
	{0x0CC7, 0x0CC8}, {0x0CCA, 0x0CCB}, {0x0CD5, 0x0CD6}, {0x0CF3, 0x0CF3}, 
	{0x0D02, 0x0D03}, {0x0D3E, 0x0D40}, {0x0D46, 0x0D48}, {0x0D4A, 0x0D4C}, 
	{0x0D57, 0x0D57}, {0x0D82, 0x0D83}, {0x0DCF, 0x0DD1}, {0x0DD8, 0x0DDF}, 
	{0x0DF2, 0x0DF3}, {0x0F3E, 0x0F3F}, {0x0F7F, 0x0F7F}, {0x102B, 0x102C}, 
	{0x1031, 0x1031}, {0x1038, 0x1038}, {0x103B, 0x103C}, {0x1056, 0x1057}, 
	{0x1062, 0x1064}, {0x1067, 0x106D}, {0x1083, 0x1084}, {0x1087, 0x108C}, 
	{0x108F, 0x108F}, {0x109A, 0x109C}, {0x1715, 0x1715}, {0x1734, 0x1734}, 
	{0x17B6, 0x17B6}, {0x17BE, 0x17C5}, {0x17C7, 0x17C8}, {0x1923, 0x1926}, 
	{0x1929, 0x192B}, {0x1930, 0x1931}, {0x1933, 0x1938}, {0x1A19, 0x1A1A}, 
	{0x1A55, 0x1A55}, {0x1A57, 0x1A57}, {0x1A61, 0x1A61}, {0x1A63, 0x1A64}, 
	{0x1A6D, 0x1A72}, {0x1B04, 0x1B04}, {0x1B35, 0x1B35}, {0x1B3B, 0x1B3B}, 
	{0x1B3D, 0x1B41}, {0x1B43, 0x1B44}, {0x1B82, 0x1B82}, {0x1BA1, 0x1BA1}, 
	{0x1BA6, 0x1BA7}, {0x1BAA, 0x1BAA}, {0x1BE7, 0x1BE7}, {0x1BEA, 0x1BEC}, 
	{0x1BEE, 0x1BEE}, {0x1BF2, 0x1BF3}, {0x1C24, 0x1C2B}, {0x1C34, 0x1C35}, 
	{0x1CE1, 0x1CE1}, {0x1CF7, 0x1CF7}, {0x302E, 0x302F}, {0xA823, 0xA824}, 
	{0xA827, 0xA827}, {0xA880, 0xA881}, {0xA8B4, 0xA8C3}, {0xA952, 0xA953}, 
	{0xA983, 0xA983}, {0xA9B4, 0xA9B5}, {0xA9BA, 0xA9BB}, {0xA9BE, 0xA9C0}, 
	{0xAA2F, 0xAA30}, {0xAA33, 0xAA34}, {0xAA4D, 0xAA4D}, {0xAA7B, 0xAA7B}, 
	{0xAA7D, 0xAA7D}, {0xAAEB, 0xAAEB}, {0xAAEE, 0xAAEF}, {0xAAF5, 0xAAF5}, 
	{0xABE3, 0xABE4}, {0xABE6, 0xABE7}, {0xABE9, 0xABEA}, {0xABEC, 0xABEC}, 
	{0x11000, 0x11000}, {0x11002, 0x11002}, {0x11082, 0x11082}, {0x110B0, 0x110B2}, 
	{0x110B7, 0x110B8}, {0x1112C, 0x1112C}, {0x11145, 0x11146}, {0x11182, 0x11182}, 
	{0x111B3, 0x111B5}, {0x111BF, 0x111C0}, {0x111CE, 0x111CE}, {0x1122C, 0x1122E}, 
	{0x11232, 0x11233}, {0x11235, 0x11235}, {0x112E0, 0x112E2}, {0x11302, 0x11303}, 
	{0x1133E, 0x1133F}, {0x11341, 0x11344}, {0x11347, 0x11348}, {0x1134B, 0x1134D}, 
	{0x11357, 0x11357}, {0x11362, 0x11363}, {0x11435, 0x11437}, {0x11440, 0x11441}, 
	{0x11445, 0x11445}, {0x114B0, 0x114B2}, {0x114B9, 0x114B9}, {0x114BB, 0x114BE}, 
	{0x114C1, 0x114C1}, {0x115AF, 0x115B1}, {0x115B8, 0x115BB}, {0x115BE, 0x115BE}, 
	{0x11630, 0x11632}, {0x1163B, 0x1163C}, {0x1163E, 0x1163E}, {0x116AC, 0x116AC}, 
	{0x116AE, 0x116AF}, {0x116B6, 0x116B6}, {0x11720, 0x11721}, {0x11726, 0x11726}, 
	{0x1182C, 0x1182E}, {0x11838, 0x11838}, {0x11930, 0x11935}, {0x11937, 0x11938}, 
	{0x1193D, 0x1193D}, {0x11940, 0x11940}, {0x11942, 0x11942}, {0x119D1, 0x119D3}, 
	{0x119DC, 0x119DF}, {0x119E4, 0x119E4}, {0x11A39, 0x11A39}, {0x11A57, 0x11A58}, 
	{0x11A97, 0x11A97}, {0x11C2F, 0x11C2F}, {0x11C3E, 0x11C3E}, {0x11CA9, 0x11CA9}, 
	{0x11CB1, 0x11CB1}, {0x11CB4, 0x11CB4}, {0x11D8A, 0x11D8E}, {0x11D93, 0x11D94}, 
	{0x11D96, 0x11D96}, {0x11EF5, 0x11EF6}, {0x11F03, 0x11F03}, {0x11F34, 0x11F35}, 
	{0x11F3E, 0x11F3F}, {0x11F41, 0x11F41}, {0x16F51, 0x16F87}, {0x16FF0, 0x16FF1}, 
	{0x1D165, 0x1D166}, {0x1D16D, 0x1D172}, 
};
static const guji_rune_range_t guji_prop_Me[] = {
	{0x0488, 0x0489}, {0x1ABE, 0x1ABE}, {0x20DD, 0x20E0}, {0x20E2, 0x20E4}, 
	{0xA670, 0xA672}, 
};
static const guji_rune_range_t guji_prop_Medefaidrin[] = {
	{0x16E40, 0x16E9A}, 
};
static const guji_rune_range_t guji_prop_Meetei_Mayek[] = {
	{0xAAE0, 0xAAF6}, {0xABC0, 0xABED}, {0xABF0, 0xABF9}, 
};
static const guji_rune_range_t guji_prop_Mende_Kikakui[] = {
	{0x1E800, 0x1E8C4}, {0x1E8C7, 0x1E8D6}, 
};
static const guji_rune_range_t guji_prop_Meroitic_Cursive[] = {
	{0x109A0, 0x109B7}, {0x109BC, 0x109CF}, {0x109D2, 0x109FF}, 
};
static const guji_rune_range_t guji_prop_Meroitic_Hieroglyphs[] = {
	{0x10980, 0x1099F}, 
};
static const guji_rune_range_t guji_prop_Miao[] = {
	{0x16F00, 0x16F4A}, {0x16F4F, 0x16F87}, {0x16F8F, 0x16F9F}, 
};
static const guji_rune_range_t guji_prop_Mn[] = {
	{0x0300, 0x036F}, {0x0483, 0x0487}, {0x0591, 0x05BD}, {0x05BF, 0x05BF}, 
	{0x05C1, 0x05C2}, {0x05C4, 0x05C5}, {0x05C7, 0x05C7}, {0x0610, 0x061A}, 
	{0x064B, 0x065F}, {0x0670, 0x0670}, {0x06D6, 0x06DC}, {0x06DF, 0x06E4}, 
	{0x06E7, 0x06E8}, {0x06EA, 0x06ED}, {0x0711, 0x0711}, {0x0730, 0x074A}, 
	{0x07A6, 0x07B0}, {0x07EB, 0x07F3}, {0x07FD, 0x07FD}, {0x0816, 0x0819}, 
	{0x081B, 0x0823}, {0x0825, 0x0827}, {0x0829, 0x082D}, {0x0859, 0x085B}, 
	{0x0898, 0x089F}, {0x08CA, 0x08E1}, {0x08E3, 0x0902}, {0x093A, 0x093A}, 
	{0x093C, 0x093C}, {0x0941, 0x0948}, {0x094D, 0x094D}, {0x0951, 0x0957}, 
	{0x0962, 0x0963}, {0x0981, 0x0981}, {0x09BC, 0x09BC}, {0x09C1, 0x09C4}, 
	{0x09CD, 0x09CD}, {0x09E2, 0x09E3}, {0x09FE, 0x09FE}, {0x0A01, 0x0A02}, 
	{0x0A3C, 0x0A3C}, {0x0A41, 0x0A42}, {0x0A47, 0x0A48}, {0x0A4B, 0x0A4D}, 
	{0x0A51, 0x0A51}, {0x0A70, 0x0A71}, {0x0A75, 0x0A75}, {0x0A81, 0x0A82}, 
	{0x0ABC, 0x0ABC}, {0x0AC1, 0x0AC5}, {0x0AC7, 0x0AC8}, {0x0ACD, 0x0ACD}, 
	{0x0AE2, 0x0AE3}, {0x0AFA, 0x0AFF}, {0x0B01, 0x0B01}, {0x0B3C, 0x0B3C}, 
	{0x0B3F, 0x0B3F}, {0x0B41, 0x0B44}, {0x0B4D, 0x0B4D}, {0x0B55, 0x0B56}, 
	{0x0B62, 0x0B63}, {0x0B82, 0x0B82}, {0x0BC0, 0x0BC0}, {0x0BCD, 0x0BCD}, 
	{0x0C00, 0x0C00}, {0x0C04, 0x0C04}, {0x0C3C, 0x0C3C}, {0x0C3E, 0x0C40}, 
	{0x0C46, 0x0C48}, {0x0C4A, 0x0C4D}, {0x0C55, 0x0C56}, {0x0C62, 0x0C63}, 
	{0x0C81, 0x0C81}, {0x0CBC, 0x0CBC}, {0x0CBF, 0x0CBF}, {0x0CC6, 0x0CC6}, 
	{0x0CCC, 0x0CCD}, {0x0CE2, 0x0CE3}, {0x0D00, 0x0D01}, {0x0D3B, 0x0D3C}, 
	{0x0D41, 0x0D44}, {0x0D4D, 0x0D4D}, {0x0D62, 0x0D63}, {0x0D81, 0x0D81}, 
	{0x0DCA, 0x0DCA}, {0x0DD2, 0x0DD4}, {0x0DD6, 0x0DD6}, {0x0E31, 0x0E31}, 
	{0x0E34, 0x0E3A}, {0x0E47, 0x0E4E}, {0x0EB1, 0x0EB1}, {0x0EB4, 0x0EBC}, 
	{0x0EC8, 0x0ECE}, {0x0F18, 0x0F19}, {0x0F35, 0x0F35}, {0x0F37, 0x0F37}, 
	{0x0F39, 0x0F39}, {0x0F71, 0x0F7E}, {0x0F80, 0x0F84}, {0x0F86, 0x0F87}, 
	{0x0F8D, 0x0F97}, {0x0F99, 0x0FBC}, {0x0FC6, 0x0FC6}, {0x102D, 0x1030}, 
	{0x1032, 0x1037}, {0x1039, 0x103A}, {0x103D, 0x103E}, {0x1058, 0x1059}, 
	{0x105E, 0x1060}, {0x1071, 0x1074}, {0x1082, 0x1082}, {0x1085, 0x1086}, 
	{0x108D, 0x108D}, {0x109D, 0x109D}, {0x135D, 0x135F}, {0x1712, 0x1714}, 
	{0x1732, 0x1733}, {0x1752, 0x1753}, {0x1772, 0x1773}, {0x17B4, 0x17B5}, 
	{0x17B7, 0x17BD}, {0x17C6, 0x17C6}, {0x17C9, 0x17D3}, {0x17DD, 0x17DD}, 
	{0x180B, 0x180D}, {0x180F, 0x180F}, {0x1885, 0x1886}, {0x18A9, 0x18A9}, 
	{0x1920, 0x1922}, {0x1927, 0x1928}, {0x1932, 0x1932}, {0x1939, 0x193B}, 
	{0x1A17, 0x1A18}, {0x1A1B, 0x1A1B}, {0x1A56, 0x1A56}, {0x1A58, 0x1A5E}, 
	{0x1A60, 0x1A60}, {0x1A62, 0x1A62}, {0x1A65, 0x1A6C}, {0x1A73, 0x1A7C}, 
	{0x1A7F, 0x1A7F}, {0x1AB0, 0x1ABD}, {0x1ABF, 0x1ACE}, {0x1B00, 0x1B03}, 
	{0x1B34, 0x1B34}, {0x1B36, 0x1B3A}, {0x1B3C, 0x1B3C}, {0x1B42, 0x1B42}, 
	{0x1B6B, 0x1B73}, {0x1B80, 0x1B81}, {0x1BA2, 0x1BA5}, {0x1BA8, 0x1BA9}, 
	{0x1BAB, 0x1BAD}, {0x1BE6, 0x1BE6}, {0x1BE8, 0x1BE9}, {0x1BED, 0x1BED}, 
	{0x1BEF, 0x1BF1}, {0x1C2C, 0x1C33}, {0x1C36, 0x1C37}, {0x1CD0, 0x1CD2}, 
	{0x1CD4, 0x1CE0}, {0x1CE2, 0x1CE8}, {0x1CED, 0x1CED}, {0x1CF4, 0x1CF4}, 
	{0x1CF8, 0x1CF9}, {0x1DC0, 0x1DFF}, {0x20D0, 0x20DC}, {0x20E1, 0x20E1}, 
	{0x20E5, 0x20F0}, {0x2CEF, 0x2CF1}, {0x2D7F, 0x2D7F}, {0x2DE0, 0x2DFF}, 
	{0x302A, 0x302D}, {0x3099, 0x309A}, {0xA66F, 0xA66F}, {0xA674, 0xA67D}, 
	{0xA69E, 0xA69F}, {0xA6F0, 0xA6F1}, {0xA802, 0xA802}, {0xA806, 0xA806}, 
	{0xA80B, 0xA80B}, {0xA825, 0xA826}, {0xA82C, 0xA82C}, {0xA8C4, 0xA8C5}, 
	{0xA8E0, 0xA8F1}, {0xA8FF, 0xA8FF}, {0xA926, 0xA92D}, {0xA947, 0xA951}, 
	{0xA980, 0xA982}, {0xA9B3, 0xA9B3}, {0xA9B6, 0xA9B9}, {0xA9BC, 0xA9BD}, 
	{0xA9E5, 0xA9E5}, {0xAA29, 0xAA2E}, {0xAA31, 0xAA32}, {0xAA35, 0xAA36}, 
	{0xAA43, 0xAA43}, {0xAA4C, 0xAA4C}, {0xAA7C, 0xAA7C}, {0xAAB0, 0xAAB0}, 
	{0xAAB2, 0xAAB4}, {0xAAB7, 0xAAB8}, {0xAABE, 0xAABF}, {0xAAC1, 0xAAC1}, 
	{0xAAEC, 0xAAED}, {0xAAF6, 0xAAF6}, {0xABE5, 0xABE5}, {0xABE8, 0xABE8}, 
	{0xABED, 0xABED}, {0xFB1E, 0xFB1E}, {0xFE00, 0xFE0F}, {0xFE20, 0xFE2F}, 
	{0x101FD, 0x101FD}, {0x102E0, 0x102E0}, {0x10376, 0x1037A}, {0x10A01, 0x10A03}, 
	{0x10A05, 0x10A06}, {0x10A0C, 0x10A0F}, {0x10A38, 0x10A3A}, {0x10A3F, 0x10A3F}, 
	{0x10AE5, 0x10AE6}, {0x10D24, 0x10D27}, {0x10EAB, 0x10EAC}, {0x10EFD, 0x10EFF}, 
	{0x10F46, 0x10F50}, {0x10F82, 0x10F85}, {0x11001, 0x11001}, {0x11038, 0x11046}, 
	{0x11070, 0x11070}, {0x11073, 0x11074}, {0x1107F, 0x11081}, {0x110B3, 0x110B6}, 
	{0x110B9, 0x110BA}, {0x110C2, 0x110C2}, {0x11100, 0x11102}, {0x11127, 0x1112B}, 
	{0x1112D, 0x11134}, {0x11173, 0x11173}, {0x11180, 0x11181}, {0x111B6, 0x111BE}, 
	{0x111C9, 0x111CC}, {0x111CF, 0x111CF}, {0x1122F, 0x11231}, {0x11234, 0x11234}, 
	{0x11236, 0x11237}, {0x1123E, 0x1123E}, {0x11241, 0x11241}, {0x112DF, 0x112DF}, 
	{0x112E3, 0x112EA}, {0x11300, 0x11301}, {0x1133B, 0x1133C}, {0x11340, 0x11340}, 
	{0x11366, 0x1136C}, {0x11370, 0x11374}, {0x11438, 0x1143F}, {0x11442, 0x11444}, 
	{0x11446, 0x11446}, {0x1145E, 0x1145E}, {0x114B3, 0x114B8}, {0x114BA, 0x114BA}, 
	{0x114BF, 0x114C0}, {0x114C2, 0x114C3}, {0x115B2, 0x115B5}, {0x115BC, 0x115BD}, 
	{0x115BF, 0x115C0}, {0x115DC, 0x115DD}, {0x11633, 0x1163A}, {0x1163D, 0x1163D}, 
	{0x1163F, 0x11640}, {0x116AB, 0x116AB}, {0x116AD, 0x116AD}, {0x116B0, 0x116B5}, 
	{0x116B7, 0x116B7}, {0x1171D, 0x1171F}, {0x11722, 0x11725}, {0x11727, 0x1172B}, 
	{0x1182F, 0x11837}, {0x11839, 0x1183A}, {0x1193B, 0x1193C}, {0x1193E, 0x1193E}, 
	{0x11943, 0x11943}, {0x119D4, 0x119D7}, {0x119DA, 0x119DB}, {0x119E0, 0x119E0}, 
	{0x11A01, 0x11A0A}, {0x11A33, 0x11A38}, {0x11A3B, 0x11A3E}, {0x11A47, 0x11A47}, 
	{0x11A51, 0x11A56}, {0x11A59, 0x11A5B}, {0x11A8A, 0x11A96}, {0x11A98, 0x11A99}, 
	{0x11C30, 0x11C36}, {0x11C38, 0x11C3D}, {0x11C3F, 0x11C3F}, {0x11C92, 0x11CA7}, 
	{0x11CAA, 0x11CB0}, {0x11CB2, 0x11CB3}, {0x11CB5, 0x11CB6}, {0x11D31, 0x11D36}, 
	{0x11D3A, 0x11D3A}, {0x11D3C, 0x11D3D}, {0x11D3F, 0x11D45}, {0x11D47, 0x11D47}, 
	{0x11D90, 0x11D91}, {0x11D95, 0x11D95}, {0x11D97, 0x11D97}, {0x11EF3, 0x11EF4}, 
	{0x11F00, 0x11F01}, {0x11F36, 0x11F3A}, {0x11F40, 0x11F40}, {0x11F42, 0x11F42}, 
	{0x13440, 0x13440}, {0x13447, 0x13455}, {0x16AF0, 0x16AF4}, {0x16B30, 0x16B36}, 
	{0x16F4F, 0x16F4F}, {0x16F8F, 0x16F92}, {0x16FE4, 0x16FE4}, {0x1BC9D, 0x1BC9E}, 
	{0x1CF00, 0x1CF2D}, {0x1CF30, 0x1CF46}, {0x1D167, 0x1D169}, {0x1D17B, 0x1D182}, 
	{0x1D185, 0x1D18B}, {0x1D1AA, 0x1D1AD}, {0x1D242, 0x1D244}, {0x1DA00, 0x1DA36}, 
	{0x1DA3B, 0x1DA6C}, {0x1DA75, 0x1DA75}, {0x1DA84, 0x1DA84}, {0x1DA9B, 0x1DA9F}, 
	{0x1DAA1, 0x1DAAF}, {0x1E000, 0x1E006}, {0x1E008, 0x1E018}, {0x1E01B, 0x1E021}, 
	{0x1E023, 0x1E024}, {0x1E026, 0x1E02A}, {0x1E08F, 0x1E08F}, {0x1E130, 0x1E136}, 
	{0x1E2AE, 0x1E2AE}, {0x1E2EC, 0x1E2EF}, {0x1E4EC, 0x1E4EF}, {0x1E8D0, 0x1E8D6}, 
	{0x1E944, 0x1E94A}, {0xE0100, 0xE01EF}, 
};
static const guji_rune_range_t guji_prop_Modi[] = {
	{0x11600, 0x11644}, {0x11650, 0x11659}, 
};
static const guji_rune_range_t guji_prop_Mongolian[] = {
	{0x1800, 0x1801}, {0x1804, 0x1804}, {0x1806, 0x1819}, {0x1820, 0x1878}, 
	{0x1880, 0x18AA}, {0x11660, 0x1166C}, 
};
static const guji_rune_range_t guji_prop_Mro[] = {
	{0x16A40, 0x16A5E}, {0x16A60, 0x16A69}, {0x16A6E, 0x16A6F}, 
};
static const guji_rune_range_t guji_prop_Multani[] = {
	{0x11280, 0x11286}, {0x11288, 0x11288}, {0x1128A, 0x1128D}, {0x1128F, 0x1129D}, 
	{0x1129F, 0x112A9}, 
};
static const guji_rune_range_t guji_prop_Myanmar[] = {
	{0x1000, 0x109F}, {0xA9E0, 0xA9FE}, {0xAA60, 0xAA7F}, 
};
static const guji_rune_range_t guji_prop_N[] = {
	{0x0030, 0x0039}, {0x00B2, 0x00B3}, {0x00B9, 0x00B9}, {0x00BC, 0x00BE}, 
	{0x0660, 0x0669}, {0x06F0, 0x06F9}, {0x07C0, 0x07C9}, {0x0966, 0x096F}, 
	{0x09E6, 0x09EF}, {0x09F4, 0x09F9}, {0x0A66, 0x0A6F}, {0x0AE6, 0x0AEF}, 
	{0x0B66, 0x0B6F}, {0x0B72, 0x0B77}, {0x0BE6, 0x0BF2}, {0x0C66, 0x0C6F}, 
	{0x0C78, 0x0C7E}, {0x0CE6, 0x0CEF}, {0x0D58, 0x0D5E}, {0x0D66, 0x0D78}, 
	{0x0DE6, 0x0DEF}, {0x0E50, 0x0E59}, {0x0ED0, 0x0ED9}, {0x0F20, 0x0F33}, 
	{0x1040, 0x1049}, {0x1090, 0x1099}, {0x1369, 0x137C}, {0x16EE, 0x16F0}, 
	{0x17E0, 0x17E9}, {0x17F0, 0x17F9}, {0x1810, 0x1819}, {0x1946, 0x194F}, 
	{0x19D0, 0x19DA}, {0x1A80, 0x1A89}, {0x1A90, 0x1A99}, {0x1B50, 0x1B59}, 
	{0x1BB0, 0x1BB9}, {0x1C40, 0x1C49}, {0x1C50, 0x1C59}, {0x2070, 0x2070}, 
	{0x2074, 0x2079}, {0x2080, 0x2089}, {0x2150, 0x2182}, {0x2185, 0x2189}, 
	{0x2460, 0x249B}, {0x24EA, 0x24FF}, {0x2776, 0x2793}, {0x2CFD, 0x2CFD}, 
	{0x3007, 0x3007}, {0x3021, 0x3029}, {0x3038, 0x303A}, {0x3192, 0x3195}, 
	{0x3220, 0x3229}, {0x3248, 0x324F}, {0x3251, 0x325F}, {0x3280, 0x3289}, 
	{0x32B1, 0x32BF}, {0xA620, 0xA629}, {0xA6E6, 0xA6EF}, {0xA830, 0xA835}, 
	{0xA8D0, 0xA8D9}, {0xA900, 0xA909}, {0xA9D0, 0xA9D9}, {0xA9F0, 0xA9F9}, 
	{0xAA50, 0xAA59}, {0xABF0, 0xABF9}, {0xFF10, 0xFF19}, {0x10107, 0x10133}, 
	{0x10140, 0x10178}, {0x1018A, 0x1018B}, {0x102E1, 0x102FB}, {0x10320, 0x10323}, 
	{0x10341, 0x10341}, {0x1034A, 0x1034A}, {0x103D1, 0x103D5}, {0x104A0, 0x104A9}, 
	{0x10858, 0x1085F}, {0x10879, 0x1087F}, {0x108A7, 0x108AF}, {0x108FB, 0x108FF}, 
	{0x10916, 0x1091B}, {0x109BC, 0x109BD}, {0x109C0, 0x109CF}, {0x109D2, 0x109FF}, 
	{0x10A40, 0x10A48}, {0x10A7D, 0x10A7E}, {0x10A9D, 0x10A9F}, {0x10AEB, 0x10AEF}, 
	{0x10B58, 0x10B5F}, {0x10B78, 0x10B7F}, {0x10BA9, 0x10BAF}, {0x10CFA, 0x10CFF}, 
	{0x10D30, 0x10D39}, {0x10E60, 0x10E7E}, {0x10F1D, 0x10F26}, {0x10F51, 0x10F54}, 
	{0x10FC5, 0x10FCB}, {0x11052, 0x1106F}, {0x110F0, 0x110F9}, {0x11136, 0x1113F}, 
	{0x111D0, 0x111D9}, {0x111E1, 0x111F4}, {0x112F0, 0x112F9}, {0x11450, 0x11459}, 
	{0x114D0, 0x114D9}, {0x11650, 0x11659}, {0x116C0, 0x116C9}, {0x11730, 0x1173B}, 
	{0x118E0, 0x118F2}, {0x11950, 0x11959}, {0x11C50, 0x11C6C}, {0x11D50, 0x11D59}, 
	{0x11DA0, 0x11DA9}, {0x11F50, 0x11F59}, {0x11FC0, 0x11FD4}, {0x12400, 0x1246E}, 
	{0x16A60, 0x16A69}, {0x16AC0, 0x16AC9}, {0x16B50, 0x16B59}, {0x16B5B, 0x16B61}, 
	{0x16E80, 0x16E96}, {0x1D2C0, 0x1D2D3}, {0x1D2E0, 0x1D2F3}, {0x1D360, 0x1D378}, 
	{0x1D7CE, 0x1D7FF}, {0x1E140, 0x1E149}, {0x1E2F0, 0x1E2F9}, {0x1E4F0, 0x1E4F9}, 
	{0x1E8C7, 0x1E8CF}, {0x1E950, 0x1E959}, {0x1EC71, 0x1ECAB}, {0x1ECAD, 0x1ECAF}, 
	{0x1ECB1, 0x1ECB4}, {0x1ED01, 0x1ED2D}, {0x1ED2F, 0x1ED3D}, {0x1F100, 0x1F10C}, 
	{0x1FBF0, 0x1FBF9}, 
};
static const guji_rune_range_t guji_prop_Nabataean[] = {
	{0x10880, 0x1089E}, {0x108A7, 0x108AF}, 
};
static const guji_rune_range_t guji_prop_Nag_Mundari[] = {
	{0x1E4D0, 0x1E4F9}, 
};
static const guji_rune_range_t guji_prop_Nandinagari[] = {
	{0x119A0, 0x119A7}, {0x119AA, 0x119D7}, {0x119DA, 0x119E4}, 
};
static const guji_rune_range_t guji_prop_Nd[] = {
	{0x0030, 0x0039}, {0x0660, 0x0669}, {0x06F0, 0x06F9}, {0x07C0, 0x07C9}, 
	{0x0966, 0x096F}, {0x09E6, 0x09EF}, {0x0A66, 0x0A6F}, {0x0AE6, 0x0AEF}, 
	{0x0B66, 0x0B6F}, {0x0BE6, 0x0BEF}, {0x0C66, 0x0C6F}, {0x0CE6, 0x0CEF}, 
	{0x0D66, 0x0D6F}, {0x0DE6, 0x0DEF}, {0x0E50, 0x0E59}, {0x0ED0, 0x0ED9}, 
	{0x0F20, 0x0F29}, {0x1040, 0x1049}, {0x1090, 0x1099}, {0x17E0, 0x17E9}, 
	{0x1810, 0x1819}, {0x1946, 0x194F}, {0x19D0, 0x19D9}, {0x1A80, 0x1A89}, 
	{0x1A90, 0x1A99}, {0x1B50, 0x1B59}, {0x1BB0, 0x1BB9}, {0x1C40, 0x1C49}, 
	{0x1C50, 0x1C59}, {0xA620, 0xA629}, {0xA8D0, 0xA8D9}, {0xA900, 0xA909}, 
	{0xA9D0, 0xA9D9}, {0xA9F0, 0xA9F9}, {0xAA50, 0xAA59}, {0xABF0, 0xABF9}, 
	{0xFF10, 0xFF19}, {0x104A0, 0x104A9}, {0x10D30, 0x10D39}, {0x11066, 0x1106F}, 
	{0x110F0, 0x110F9}, {0x11136, 0x1113F}, {0x111D0, 0x111D9}, {0x112F0, 0x112F9}, 
	{0x11450, 0x11459}, {0x114D0, 0x114D9}, {0x11650, 0x11659}, {0x116C0, 0x116C9}, 
	{0x11730, 0x11739}, {0x118E0, 0x118E9}, {0x11950, 0x11959}, {0x11C50, 0x11C59}, 
	{0x11D50, 0x11D59}, {0x11DA0, 0x11DA9}, {0x11F50, 0x11F59}, {0x16A60, 0x16A69}, 
	{0x16AC0, 0x16AC9}, {0x16B50, 0x16B59}, {0x1D7CE, 0x1D7FF}, {0x1E140, 0x1E149}, 
	{0x1E2F0, 0x1E2F9}, {0x1E4F0, 0x1E4F9}, {0x1E950, 0x1E959}, {0x1FBF0, 0x1FBF9}, 
};
static const guji_rune_range_t guji_prop_New_Tai_Lue[] = {
	{0x1980, 0x19AB}, {0x19B0, 0x19C9}, {0x19D0, 0x19DA}, {0x19DE, 0x19DF}, 
};
static const guji_rune_range_t guji_prop_Newa[] = {
	{0x11400, 0x1145B}, {0x1145D, 0x11461}, 
};
static const guji_rune_range_t guji_prop_Nko[] = {
	{0x07C0, 0x07FA}, {0x07FD, 0x07FF}, 
};
static const guji_rune_range_t guji_prop_Nl[] = {
	{0x16EE, 0x16F0}, {0x2160, 0x2182}, {0x2185, 0x2188}, {0x3007, 0x3007}, 
	{0x3021, 0x3029}, {0x3038, 0x303A}, {0xA6E6, 0xA6EF}, {0x10140, 0x10174}, 
	{0x10341, 0x10341}, {0x1034A, 0x1034A}, {0x103D1, 0x103D5}, {0x12400, 0x1246E}, 
};
static const guji_rune_range_t guji_prop_No[] = {
	{0x00B2, 0x00B3}, {0x00B9, 0x00B9}, {0x00BC, 0x00BE}, {0x09F4, 0x09F9}, 
	{0x0B72, 0x0B77}, {0x0BF0, 0x0BF2}, {0x0C78, 0x0C7E}, {0x0D58, 0x0D5E}, 
	{0x0D70, 0x0D78}, {0x0F2A, 0x0F33}, {0x1369, 0x137C}, {0x17F0, 0x17F9}, 
	{0x19DA, 0x19DA}, {0x2070, 0x2070}, {0x2074, 0x2079}, {0x2080, 0x2089}, 
	{0x2150, 0x215F}, {0x2189, 0x2189}, {0x2460, 0x249B}, {0x24EA, 0x24FF}, 
	{0x2776, 0x2793}, {0x2CFD, 0x2CFD}, {0x3192, 0x3195}, {0x3220, 0x3229}, 
	{0x3248, 0x324F}, {0x3251, 0x325F}, {0x3280, 0x3289}, {0x32B1, 0x32BF}, 
	{0xA830, 0xA835}, {0x10107, 0x10133}, {0x10175, 0x10178}, {0x1018A, 0x1018B}, 
	{0x102E1, 0x102FB}, {0x10320, 0x10323}, {0x10858, 0x1085F}, {0x10879, 0x1087F}, 
	{0x108A7, 0x108AF}, {0x108FB, 0x108FF}, {0x10916, 0x1091B}, {0x109BC, 0x109BD}, 
	{0x109C0, 0x109CF}, {0x109D2, 0x109FF}, {0x10A40, 0x10A48}, {0x10A7D, 0x10A7E}, 
	{0x10A9D, 0x10A9F}, {0x10AEB, 0x10AEF}, {0x10B58, 0x10B5F}, {0x10B78, 0x10B7F}, 
	{0x10BA9, 0x10BAF}, {0x10CFA, 0x10CFF}, {0x10E60, 0x10E7E}, {0x10F1D, 0x10F26}, 
	{0x10F51, 0x10F54}, {0x10FC5, 0x10FCB}, {0x11052, 0x11065}, {0x111E1, 0x111F4}, 
	{0x1173A, 0x1173B}, {0x118EA, 0x118F2}, {0x11C5A, 0x11C6C}, {0x11FC0, 0x11FD4}, 
	{0x16B5B, 0x16B61}, {0x16E80, 0x16E96}, {0x1D2C0, 0x1D2D3}, {0x1D2E0, 0x1D2F3}, 
	{0x1D360, 0x1D378}, {0x1E8C7, 0x1E8CF}, {0x1EC71, 0x1ECAB}, {0x1ECAD, 0x1ECAF}, 
	{0x1ECB1, 0x1ECB4}, {0x1ED01, 0x1ED2D}, {0x1ED2F, 0x1ED3D}, {0x1F100, 0x1F10C}, 
};
static const guji_rune_range_t guji_prop_Nushu[] = {
	{0x16FE1, 0x16FE1}, {0x1B170, 0x1B2FB}, 
};
static const guji_rune_range_t guji_prop_Nyiakeng_Puachue_Hmong[] = {
	{0x1E100, 0x1E12C}, {0x1E130, 0x1E13D}, {0x1E140, 0x1E149}, {0x1E14E, 0x1E14F}, 
};
static const guji_rune_range_t guji_prop_Ogham[] = {
	{0x1680, 0x169C}, 
};
static const guji_rune_range_t guji_prop_Ol_Chiki[] = {
	{0x1C50, 0x1C7F}, 
};
static const guji_rune_range_t guji_prop_Old_Hungarian[] = {
	{0x10C80, 0x10CB2}, {0x10CC0, 0x10CF2}, {0x10CFA, 0x10CFF}, 
};
static const guji_rune_range_t guji_prop_Old_Italic[] = {
	{0x10300, 0x10323}, {0x1032D, 0x1032F}, 
};
static const guji_rune_range_t guji_prop_Old_North_Arabian[] = {
	{0x10A80, 0x10A9F}, 
};
static const guji_rune_range_t guji_prop_Old_Permic[] = {
	{0x10350, 0x1037A}, 
};
static const guji_rune_range_t guji_prop_Old_Persian[] = {
	{0x103A0, 0x103C3}, {0x103C8, 0x103D5}, 
};
static const guji_rune_range_t guji_prop_Old_Sogdian[] = {
	{0x10F00, 0x10F27}, 
};
static const guji_rune_range_t guji_prop_Old_South_Arabian[] = {
	{0x10A60, 0x10A7F}, 
};
static const guji_rune_range_t guji_prop_Old_Turkic[] = {
	{0x10C00, 0x10C48}, 
};
static const guji_rune_range_t guji_prop_Old_Uyghur[] = {
	{0x10F70, 0x10F89}, 
};
static const guji_rune_range_t guji_prop_Oriya[] = {
	{0x0B01, 0x0B03}, {0x0B05, 0x0B0C}, {0x0B0F, 0x0B10}, {0x0B13, 0x0B28}, 
	{0x0B2A, 0x0B30}, {0x0B32, 0x0B33}, {0x0B35, 0x0B39}, {0x0B3C, 0x0B44}, 
	{0x0B47, 0x0B48}, {0x0B4B, 0x0B4D}, {0x0B55, 0x0B57}, {0x0B5C, 0x0B5D}, 
	{0x0B5F, 0x0B63}, {0x0B66, 0x0B77}, 
};
static const guji_rune_range_t guji_prop_Osage[] = {
	{0x104B0, 0x104D3}, {0x104D8, 0x104FB}, 
};
static const guji_rune_range_t guji_prop_Osmanya[] = {
	{0x10480, 0x1049D}, {0x104A0, 0x104A9}, 
};
static const guji_rune_range_t guji_prop_P[] = {
	{0x0021, 0x0023}, {0x0025, 0x002A}, {0x002C, 0x002F}, {0x003A, 0x003B}, 
	{0x003F, 0x0040}, {0x005B, 0x005D}, {0x005F, 0x005F}, {0x007B, 0x007B}, 
	{0x007D, 0x007D}, {0x00A1, 0x00A1}, {0x00A7, 0x00A7}, {0x00AB, 0x00AB}, 
	{0x00B6, 0x00B7}, {0x00BB, 0x00BB}, {0x00BF, 0x00BF}, {0x037E, 0x037E}, 
	{0x0387, 0x0387}, {0x055A, 0x055F}, {0x0589, 0x058A}, {0x05BE, 0x05BE}, 
	{0x05C0, 0x05C0}, {0x05C3, 0x05C3}, {0x05C6, 0x05C6}, {0x05F3, 0x05F4}, 
	{0x0609, 0x060A}, {0x060C, 0x060D}, {0x061B, 0x061B}, {0x061D, 0x061F}, 
	{0x066A, 0x066D}, {0x06D4, 0x06D4}, {0x0700, 0x070D}, {0x07F7, 0x07F9}, 
	{0x0830, 0x083E}, {0x085E, 0x085E}, {0x0964, 0x0965}, {0x0970, 0x0970}, 
	{0x09FD, 0x09FD}, {0x0A76, 0x0A76}, {0x0AF0, 0x0AF0}, {0x0C77, 0x0C77}, 
	{0x0C84, 0x0C84}, {0x0DF4, 0x0DF4}, {0x0E4F, 0x0E4F}, {0x0E5A, 0x0E5B}, 
	{0x0F04, 0x0F12}, {0x0F14, 0x0F14}, {0x0F3A, 0x0F3D}, {0x0F85, 0x0F85}, 
	{0x0FD0, 0x0FD4}, {0x0FD9, 0x0FDA}, {0x104A, 0x104F}, {0x10FB, 0x10FB}, 
	{0x1360, 0x1368}, {0x1400, 0x1400}, {0x166E, 0x166E}, {0x169B, 0x169C}, 
	{0x16EB, 0x16ED}, {0x1735, 0x1736}, {0x17D4, 0x17D6}, {0x17D8, 0x17DA}, 
	{0x1800, 0x180A}, {0x1944, 0x1945}, {0x1A1E, 0x1A1F}, {0x1AA0, 0x1AA6}, 
	{0x1AA8, 0x1AAD}, {0x1B5A, 0x1B60}, {0x1B7D, 0x1B7E}, {0x1BFC, 0x1BFF}, 
	{0x1C3B, 0x1C3F}, {0x1C7E, 0x1C7F}, {0x1CC0, 0x1CC7}, {0x1CD3, 0x1CD3}, 
	{0x2010, 0x2027}, {0x2030, 0x2043}, {0x2045, 0x2051}, {0x2053, 0x205E}, 
	{0x207D, 0x207E}, {0x208D, 0x208E}, {0x2308, 0x230B}, {0x2329, 0x232A}, 
	{0x2768, 0x2775}, {0x27C5, 0x27C6}, {0x27E6, 0x27EF}, {0x2983, 0x2998}, 
	{0x29D8, 0x29DB}, {0x29FC, 0x29FD}, {0x2CF9, 0x2CFC}, {0x2CFE, 0x2CFF}, 
	{0x2D70, 0x2D70}, {0x2E00, 0x2E2E}, {0x2E30, 0x2E4F}, {0x2E52, 0x2E5D}, 
	{0x3001, 0x3003}, {0x3008, 0x3011}, {0x3014, 0x301F}, {0x3030, 0x3030}, 
	{0x303D, 0x303D}, {0x30A0, 0x30A0}, {0x30FB, 0x30FB}, {0xA4FE, 0xA4FF}, 
	{0xA60D, 0xA60F}, {0xA673, 0xA673}, {0xA67E, 0xA67E}, {0xA6F2, 0xA6F7}, 
	{0xA874, 0xA877}, {0xA8CE, 0xA8CF}, {0xA8F8, 0xA8FA}, {0xA8FC, 0xA8FC}, 
	{0xA92E, 0xA92F}, {0xA95F, 0xA95F}, {0xA9C1, 0xA9CD}, {0xA9DE, 0xA9DF}, 
	{0xAA5C, 0xAA5F}, {0xAADE, 0xAADF}, {0xAAF0, 0xAAF1}, {0xABEB, 0xABEB}, 
	{0xFD3E, 0xFD3F}, {0xFE10, 0xFE19}, {0xFE30, 0xFE52}, {0xFE54, 0xFE61}, 
	{0xFE63, 0xFE63}, {0xFE68, 0xFE68}, {0xFE6A, 0xFE6B}, {0xFF01, 0xFF03}, 
	{0xFF05, 0xFF0A}, {0xFF0C, 0xFF0F}, {0xFF1A, 0xFF1B}, {0xFF1F, 0xFF20}, 
	{0xFF3B, 0xFF3D}, {0xFF3F, 0xFF3F}, {0xFF5B, 0xFF5B}, {0xFF5D, 0xFF5D}, 
	{0xFF5F, 0xFF65}, {0x10100, 0x10102}, {0x1039F, 0x1039F}, {0x103D0, 0x103D0}, 
	{0x1056F, 0x1056F}, {0x10857, 0x10857}, {0x1091F, 0x1091F}, {0x1093F, 0x1093F}, 
	{0x10A50, 0x10A58}, {0x10A7F, 0x10A7F}, {0x10AF0, 0x10AF6}, {0x10B39, 0x10B3F}, 
	{0x10B99, 0x10B9C}, {0x10EAD, 0x10EAD}, {0x10F55, 0x10F59}, {0x10F86, 0x10F89}, 
	{0x11047, 0x1104D}, {0x110BB, 0x110BC}, {0x110BE, 0x110C1}, {0x11140, 0x11143}, 
	{0x11174, 0x11175}, {0x111C5, 0x111C8}, {0x111CD, 0x111CD}, {0x111DB, 0x111DB}, 
	{0x111DD, 0x111DF}, {0x11238, 0x1123D}, {0x112A9, 0x112A9}, {0x1144B, 0x1144F}, 
	{0x1145A, 0x1145B}, {0x1145D, 0x1145D}, {0x114C6, 0x114C6}, {0x115C1, 0x115D7}, 
	{0x11641, 0x11643}, {0x11660, 0x1166C}, {0x116B9, 0x116B9}, {0x1173C, 0x1173E}, 
	{0x1183B, 0x1183B}, {0x11944, 0x11946}, {0x119E2, 0x119E2}, {0x11A3F, 0x11A46}, 
	{0x11A9A, 0x11A9C}, {0x11A9E, 0x11AA2}, {0x11B00, 0x11B09}, {0x11C41, 0x11C45}, 
	{0x11C70, 0x11C71}, {0x11EF7, 0x11EF8}, {0x11F43, 0x11F4F}, {0x11FFF, 0x11FFF}, 
	{0x12470, 0x12474}, {0x12FF1, 0x12FF2}, {0x16A6E, 0x16A6F}, {0x16AF5, 0x16AF5}, 
	{0x16B37, 0x16B3B}, {0x16B44, 0x16B44}, {0x16E97, 0x16E9A}, {0x16FE2, 0x16FE2}, 
	{0x1BC9F, 0x1BC9F}, {0x1DA87, 0x1DA8B}, {0x1E95E, 0x1E95F}, 
};
static const guji_rune_range_t guji_prop_Pahawh_Hmong[] = {
	{0x16B00, 0x16B45}, {0x16B50, 0x16B59}, {0x16B5B, 0x16B61}, {0x16B63, 0x16B77}, 
	{0x16B7D, 0x16B8F}, 
};
static const guji_rune_range_t guji_prop_Palmyrene[] = {
	{0x10860, 0x1087F}, 
};
static const guji_rune_range_t guji_prop_Pau_Cin_Hau[] = {
	{0x11AC0, 0x11AF8}, 
};
static const guji_rune_range_t guji_prop_Pc[] = {
	{0x005F, 0x005F}, {0x203F, 0x2040}, {0x2054, 0x2054}, {0xFE33, 0xFE34}, 
	{0xFE4D, 0xFE4F}, {0xFF3F, 0xFF3F}, 
};
static const guji_rune_range_t guji_prop_Pd[] = {
	{0x002D, 0x002D}, {0x058A, 0x058A}, {0x05BE, 0x05BE}, {0x1400, 0x1400}, 
	{0x1806, 0x1806}, {0x2010, 0x2015}, {0x2E17, 0x2E17}, {0x2E1A, 0x2E1A}, 
	{0x2E3A, 0x2E3B}, {0x2E40, 0x2E40}, {0x2E5D, 0x2E5D}, {0x301C, 0x301C}, 
	{0x3030, 0x3030}, {0x30A0, 0x30A0}, {0xFE31, 0xFE32}, {0xFE58, 0xFE58}, 
	{0xFE63, 0xFE63}, {0xFF0D, 0xFF0D}, {0x10EAD, 0x10EAD}, 
};
static const guji_rune_range_t guji_prop_Pe[] = {
	{0x0029, 0x0029}, {0x005D, 0x005D}, {0x007D, 0x007D}, {0x0F3B, 0x0F3B}, 
	{0x0F3D, 0x0F3D}, {0x169C, 0x169C}, {0x2046, 0x2046}, {0x207E, 0x207E}, 
	{0x208E, 0x208E}, {0x2309, 0x2309}, {0x230B, 0x230B}, {0x232A, 0x232A}, 
	{0x2769, 0x2769}, {0x276B, 0x276B}, {0x276D, 0x276D}, {0x276F, 0x276F}, 
	{0x2771, 0x2771}, {0x2773, 0x2773}, {0x2775, 0x2775}, {0x27C6, 0x27C6}, 
	{0x27E7, 0x27E7}, {0x27E9, 0x27E9}, {0x27EB, 0x27EB}, {0x27ED, 0x27ED}, 
	{0x27EF, 0x27EF}, {0x2984, 0x2984}, {0x2986, 0x2986}, {0x2988, 0x2988}, 
	{0x298A, 0x298A}, {0x298C, 0x298C}, {0x298E, 0x298E}, {0x2990, 0x2990}, 
	{0x2992, 0x2992}, {0x2994, 0x2994}, {0x2996, 0x2996}, {0x2998, 0x2998}, 
	{0x29D9, 0x29D9}, {0x29DB, 0x29DB}, {0x29FD, 0x29FD}, {0x2E23, 0x2E23}, 
	{0x2E25, 0x2E25}, {0x2E27, 0x2E27}, {0x2E29, 0x2E29}, {0x2E56, 0x2E56}, 
	{0x2E58, 0x2E58}, {0x2E5A, 0x2E5A}, {0x2E5C, 0x2E5C}, {0x3009, 0x3009}, 
	{0x300B, 0x300B}, {0x300D, 0x300D}, {0x300F, 0x300F}, {0x3011, 0x3011}, 
	{0x3015, 0x3015}, {0x3017, 0x3017}, {0x3019, 0x3019}, {0x301B, 0x301B}, 
	{0x301E, 0x301F}, {0xFD3E, 0xFD3E}, {0xFE18, 0xFE18}, {0xFE36, 0xFE36}, 
	{0xFE38, 0xFE38}, {0xFE3A, 0xFE3A}, {0xFE3C, 0xFE3C}, {0xFE3E, 0xFE3E}, 
	{0xFE40, 0xFE40}, {0xFE42, 0xFE42}, {0xFE44, 0xFE44}, {0xFE48, 0xFE48}, 
	{0xFE5A, 0xFE5A}, {0xFE5C, 0xFE5C}, {0xFE5E, 0xFE5E}, {0xFF09, 0xFF09}, 
	{0xFF3D, 0xFF3D}, {0xFF5D, 0xFF5D}, {0xFF60, 0xFF60}, {0xFF63, 0xFF63}, 
};
static const guji_rune_range_t guji_prop_Pf[] = {
	{0x00BB, 0x00BB}, {0x2019, 0x2019}, {0x201D, 0x201D}, {0x203A, 0x203A}, 
	{0x2E03, 0x2E03}, {0x2E05, 0x2E05}, {0x2E0A, 0x2E0A}, {0x2E0D, 0x2E0D}, 
	{0x2E1D, 0x2E1D}, {0x2E21, 0x2E21}, 
};
static const guji_rune_range_t guji_prop_Phags_Pa[] = {
	{0xA840, 0xA877}, 
};
static const guji_rune_range_t guji_prop_Phoenician[] = {
	{0x10900, 0x1091B}, {0x1091F, 0x1091F}, 
};
static const guji_rune_range_t guji_prop_Pi[] = {
	{0x00AB, 0x00AB}, {0x2018, 0x2018}, {0x201B, 0x201C}, {0x201F, 0x201F}, 
	{0x2039, 0x2039}, {0x2E02, 0x2E02}, {0x2E04, 0x2E04}, {0x2E09, 0x2E09}, 
	{0x2E0C, 0x2E0C}, {0x2E1C, 0x2E1C}, {0x2E20, 0x2E20}, 
};
static const guji_rune_range_t guji_prop_Po[] = {
	{0x0021, 0x0023}, {0x0025, 0x0027}, {0x002A, 0x002A}, {0x002C, 0x002C}, 
	{0x002E, 0x002F}, {0x003A, 0x003B}, {0x003F, 0x0040}, {0x005C, 0x005C}, 
	{0x00A1, 0x00A1}, {0x00A7, 0x00A7}, {0x00B6, 0x00B7}, {0x00BF, 0x00BF}, 
	{0x037E, 0x037E}, {0x0387, 0x0387}, {0x055A, 0x055F}, {0x0589, 0x0589}, 
	{0x05C0, 0x05C0}, {0x05C3, 0x05C3}, {0x05C6, 0x05C6}, {0x05F3, 0x05F4}, 
	{0x0609, 0x060A}, {0x060C, 0x060D}, {0x061B, 0x061B}, {0x061D, 0x061F}, 
	{0x066A, 0x066D}, {0x06D4, 0x06D4}, {0x0700, 0x070D}, {0x07F7, 0x07F9}, 
	{0x0830, 0x083E}, {0x085E, 0x085E}, {0x0964, 0x0965}, {0x0970, 0x0970}, 
	{0x09FD, 0x09FD}, {0x0A76, 0x0A76}, {0x0AF0, 0x0AF0}, {0x0C77, 0x0C77}, 
	{0x0C84, 0x0C84}, {0x0DF4, 0x0DF4}, {0x0E4F, 0x0E4F}, {0x0E5A, 0x0E5B}, 
	{0x0F04, 0x0F12}, {0x0F14, 0x0F14}, {0x0F85, 0x0F85}, {0x0FD0, 0x0FD4}, 
	{0x0FD9, 0x0FDA}, {0x104A, 0x104F}, {0x10FB, 0x10FB}, {0x1360, 0x1368}, 
	{0x166E, 0x166E}, {0x16EB, 0x16ED}, {0x1735, 0x1736}, {0x17D4, 0x17D6}, 
	{0x17D8, 0x17DA}, {0x1800, 0x1805}, {0x1807, 0x180A}, {0x1944, 0x1945}, 
	{0x1A1E, 0x1A1F}, {0x1AA0, 0x1AA6}, {0x1AA8, 0x1AAD}, {0x1B5A, 0x1B60}, 
	{0x1B7D, 0x1B7E}, {0x1BFC, 0x1BFF}, {0x1C3B, 0x1C3F}, {0x1C7E, 0x1C7F}, 
	{0x1CC0, 0x1CC7}, {0x1CD3, 0x1CD3}, {0x2016, 0x2017}, {0x2020, 0x2027}, 
	{0x2030, 0x2038}, {0x203B, 0x203E}, {0x2041, 0x2043}, {0x2047, 0x2051}, 
	{0x2053, 0x2053}, {0x2055, 0x205E}, {0x2CF9, 0x2CFC}, {0x2CFE, 0x2CFF}, 
	{0x2D70, 0x2D70}, {0x2E00, 0x2E01}, {0x2E06, 0x2E08}, {0x2E0B, 0x2E0B}, 
	{0x2E0E, 0x2E16}, {0x2E18, 0x2E19}, {0x2E1B, 0x2E1B}, {0x2E1E, 0x2E1F}, 
	{0x2E2A, 0x2E2E}, {0x2E30, 0x2E39}, {0x2E3C, 0x2E3F}, {0x2E41, 0x2E41}, 
	{0x2E43, 0x2E4F}, {0x2E52, 0x2E54}, {0x3001, 0x3003}, {0x303D, 0x303D}, 
	{0x30FB, 0x30FB}, {0xA4FE, 0xA4FF}, {0xA60D, 0xA60F}, {0xA673, 0xA673}, 
	{0xA67E, 0xA67E}, {0xA6F2, 0xA6F7}, {0xA874, 0xA877}, {0xA8CE, 0xA8CF}, 
	{0xA8F8, 0xA8FA}, {0xA8FC, 0xA8FC}, {0xA92E, 0xA92F}, {0xA95F, 0xA95F}, 
	{0xA9C1, 0xA9CD}, {0xA9DE, 0xA9DF}, {0xAA5C, 0xAA5F}, {0xAADE, 0xAADF}, 
	{0xAAF0, 0xAAF1}, {0xABEB, 0xABEB}, {0xFE10, 0xFE16}, {0xFE19, 0xFE19}, 
	{0xFE30, 0xFE30}, {0xFE45, 0xFE46}, {0xFE49, 0xFE4C}, {0xFE50, 0xFE52}, 
	{0xFE54, 0xFE57}, {0xFE5F, 0xFE61}, {0xFE68, 0xFE68}, {0xFE6A, 0xFE6B}, 
	{0xFF01, 0xFF03}, {0xFF05, 0xFF07}, {0xFF0A, 0xFF0A}, {0xFF0C, 0xFF0C}, 
	{0xFF0E, 0xFF0F}, {0xFF1A, 0xFF1B}, {0xFF1F, 0xFF20}, {0xFF3C, 0xFF3C}, 
	{0xFF61, 0xFF61}, {0xFF64, 0xFF65}, {0x10100, 0x10102}, {0x1039F, 0x1039F}, 
	{0x103D0, 0x103D0}, {0x1056F, 0x1056F}, {0x10857, 0x10857}, {0x1091F, 0x1091F}, 
	{0x1093F, 0x1093F}, {0x10A50, 0x10A58}, {0x10A7F, 0x10A7F}, {0x10AF0, 0x10AF6}, 
	{0x10B39, 0x10B3F}, {0x10B99, 0x10B9C}, {0x10F55, 0x10F59}, {0x10F86, 0x10F89}, 
	{0x11047, 0x1104D}, {0x110BB, 0x110BC}, {0x110BE, 0x110C1}, {0x11140, 0x11143}, 
	{0x11174, 0x11175}, {0x111C5, 0x111C8}, {0x111CD, 0x111CD}, {0x111DB, 0x111DB}, 
	{0x111DD, 0x111DF}, {0x11238, 0x1123D}, {0x112A9, 0x112A9}, {0x1144B, 0x1144F}, 
	{0x1145A, 0x1145B}, {0x1145D, 0x1145D}, {0x114C6, 0x114C6}, {0x115C1, 0x115D7}, 
	{0x11641, 0x11643}, {0x11660, 0x1166C}, {0x116B9, 0x116B9}, {0x1173C, 0x1173E}, 
	{0x1183B, 0x1183B}, {0x11944, 0x11946}, {0x119E2, 0x119E2}, {0x11A3F, 0x11A46}, 
	{0x11A9A, 0x11A9C}, {0x11A9E, 0x11AA2}, {0x11B00, 0x11B09}, {0x11C41, 0x11C45}, 
	{0x11C70, 0x11C71}, {0x11EF7, 0x11EF8}, {0x11F43, 0x11F4F}, {0x11FFF, 0x11FFF}, 
	{0x12470, 0x12474}, {0x12FF1, 0x12FF2}, {0x16A6E, 0x16A6F}, {0x16AF5, 0x16AF5}, 
	{0x16B37, 0x16B3B}, {0x16B44, 0x16B44}, {0x16E97, 0x16E9A}, {0x16FE2, 0x16FE2}, 
	{0x1BC9F, 0x1BC9F}, {0x1DA87, 0x1DA8B}, {0x1E95E, 0x1E95F}, 
};
static const guji_rune_range_t guji_prop_Ps[] = {
	{0x0028, 0x0028}, {0x005B, 0x005B}, {0x007B, 0x007B}, {0x0F3A, 0x0F3A}, 
	{0x0F3C, 0x0F3C}, {0x169B, 0x169B}, {0x201A, 0x201A}, {0x201E, 0x201E}, 
	{0x2045, 0x2045}, {0x207D, 0x207D}, {0x208D, 0x208D}, {0x2308, 0x2308}, 
	{0x230A, 0x230A}, {0x2329, 0x2329}, {0x2768, 0x2768}, {0x276A, 0x276A}, 
	{0x276C, 0x276C}, {0x276E, 0x276E}, {0x2770, 0x2770}, {0x2772, 0x2772}, 
	{0x2774, 0x2774}, {0x27C5, 0x27C5}, {0x27E6, 0x27E6}, {0x27E8, 0x27E8}, 
	{0x27EA, 0x27EA}, {0x27EC, 0x27EC}, {0x27EE, 0x27EE}, {0x2983, 0x2983}, 
	{0x2985, 0x2985}, {0x2987, 0x2987}, {0x2989, 0x2989}, {0x298B, 0x298B}, 
	{0x298D, 0x298D}, {0x298F, 0x298F}, {0x2991, 0x2991}, {0x2993, 0x2993}, 
	{0x2995, 0x2995}, {0x2997, 0x2997}, {0x29D8, 0x29D8}, {0x29DA, 0x29DA}, 
	{0x29FC, 0x29FC}, {0x2E22, 0x2E22}, {0x2E24, 0x2E24}, {0x2E26, 0x2E26}, 
	{0x2E28, 0x2E28}, {0x2E42, 0x2E42}, {0x2E55, 0x2E55}, {0x2E57, 0x2E57}, 
	{0x2E59, 0x2E59}, {0x2E5B, 0x2E5B}, {0x3008, 0x3008}, {0x300A, 0x300A}, 
	{0x300C, 0x300C}, {0x300E, 0x300E}, {0x3010, 0x3010}, {0x3014, 0x3014}, 
	{0x3016, 0x3016}, {0x3018, 0x3018}, {0x301A, 0x301A}, {0x301D, 0x301D}, 
	{0xFD3F, 0xFD3F}, {0xFE17, 0xFE17}, {0xFE35, 0xFE35}, {0xFE37, 0xFE37}, 
	{0xFE39, 0xFE39}, {0xFE3B, 0xFE3B}, {0xFE3D, 0xFE3D}, {0xFE3F, 0xFE3F}, 
	{0xFE41, 0xFE41}, {0xFE43, 0xFE43}, {0xFE47, 0xFE47}, {0xFE59, 0xFE59}, 
	{0xFE5B, 0xFE5B}, {0xFE5D, 0xFE5D}, {0xFF08, 0xFF08}, {0xFF3B, 0xFF3B}, 
	{0xFF5B, 0xFF5B}, {0xFF5F, 0xFF5F}, {0xFF62, 0xFF62}, 
};
static const guji_rune_range_t guji_prop_Psalter_Pahlavi[] = {
	{0x10B80, 0x10B91}, {0x10B99, 0x10B9C}, {0x10BA9, 0x10BAF}, 
};
static const guji_rune_range_t guji_prop_Rejang[] = {
	{0xA930, 0xA953}, {0xA95F, 0xA95F}, 
};
static const guji_rune_range_t guji_prop_Runic[] = {
	{0x16A0, 0x16EA}, {0x16EE, 0x16F8}, 
};
static const guji_rune_range_t guji_prop_S[] = {
	{0x0024, 0x0024}, {0x002B, 0x002B}, {0x003C, 0x003E}, {0x005E, 0x005E}, 
	{0x0060, 0x0060}, {0x007C, 0x007C}, {0x007E, 0x007E}, {0x00A2, 0x00A6}, 
	{0x00A8, 0x00A9}, {0x00AC, 0x00AC}, {0x00AE, 0x00B1}, {0x00B4, 0x00B4}, 
	{0x00B8, 0x00B8}, {0x00D7, 0x00D7}, {0x00F7, 0x00F7}, {0x02C2, 0x02C5}, 
	{0x02D2, 0x02DF}, {0x02E5, 0x02EB}, {0x02ED, 0x02ED}, {0x02EF, 0x02FF}, 
	{0x0375, 0x0375}, {0x0384, 0x0385}, {0x03F6, 0x03F6}, {0x0482, 0x0482}, 
	{0x058D, 0x058F}, {0x0606, 0x0608}, {0x060B, 0x060B}, {0x060E, 0x060F}, 
	{0x06DE, 0x06DE}, {0x06E9, 0x06E9}, {0x06FD, 0x06FE}, {0x07F6, 0x07F6}, 
	{0x07FE, 0x07FF}, {0x0888, 0x0888}, {0x09F2, 0x09F3}, {0x09FA, 0x09FB}, 
	{0x0AF1, 0x0AF1}, {0x0B70, 0x0B70}, {0x0BF3, 0x0BFA}, {0x0C7F, 0x0C7F}, 
	{0x0D4F, 0x0D4F}, {0x0D79, 0x0D79}, {0x0E3F, 0x0E3F}, {0x0F01, 0x0F03}, 
	{0x0F13, 0x0F13}, {0x0F15, 0x0F17}, {0x0F1A, 0x0F1F}, {0x0F34, 0x0F34}, 
	{0x0F36, 0x0F36}, {0x0F38, 0x0F38}, {0x0FBE, 0x0FC5}, {0x0FC7, 0x0FCC}, 
	{0x0FCE, 0x0FCF}, {0x0FD5, 0x0FD8}, {0x109E, 0x109F}, {0x1390, 0x1399}, 
	{0x166D, 0x166D}, {0x17DB, 0x17DB}, {0x1940, 0x1940}, {0x19DE, 0x19FF}, 
	{0x1B61, 0x1B6A}, {0x1B74, 0x1B7C}, {0x1FBD, 0x1FBD}, {0x1FBF, 0x1FC1}, 
	{0x1FCD, 0x1FCF}, {0x1FDD, 0x1FDF}, {0x1FED, 0x1FEF}, {0x1FFD, 0x1FFE}, 
	{0x2044, 0x2044}, {0x2052, 0x2052}, {0x207A, 0x207C}, {0x208A, 0x208C}, 
	{0x20A0, 0x20C0}, {0x2100, 0x2101}, {0x2103, 0x2106}, {0x2108, 0x2109}, 
	{0x2114, 0x2114}, {0x2116, 0x2118}, {0x211E, 0x2123}, {0x2125, 0x2125}, 
	{0x2127, 0x2127}, {0x2129, 0x2129}, {0x212E, 0x212E}, {0x213A, 0x213B}, 
	{0x2140, 0x2144}, {0x214A, 0x214D}, {0x214F, 0x214F}, {0x218A, 0x218B}, 
	{0x2190, 0x2307}, {0x230C, 0x2328}, {0x232B, 0x2426}, {0x2440, 0x244A}, 
	{0x249C, 0x24E9}, {0x2500, 0x2767}, {0x2794, 0x27C4}, {0x27C7, 0x27E5}, 
	{0x27F0, 0x2982}, {0x2999, 0x29D7}, {0x29DC, 0x29FB}, {0x29FE, 0x2B73}, 
	{0x2B76, 0x2B95}, {0x2B97, 0x2BFF}, {0x2CE5, 0x2CEA}, {0x2E50, 0x2E51}, 
	{0x2E80, 0x2E99}, {0x2E9B, 0x2EF3}, {0x2F00, 0x2FD5}, {0x2FF0, 0x2FFB}, 
	{0x3004, 0x3004}, {0x3012, 0x3013}, {0x3020, 0x3020}, {0x3036, 0x3037}, 
	{0x303E, 0x303F}, {0x309B, 0x309C}, {0x3190, 0x3191}, {0x3196, 0x319F}, 
	{0x31C0, 0x31E3}, {0x3200, 0x321E}, {0x322A, 0x3247}, {0x3250, 0x3250}, 
	{0x3260, 0x327F}, {0x328A, 0x32B0}, {0x32C0, 0x33FF}, {0x4DC0, 0x4DFF}, 
	{0xA490, 0xA4C6}, {0xA700, 0xA716}, {0xA720, 0xA721}, {0xA789, 0xA78A}, 
	{0xA828, 0xA82B}, {0xA836, 0xA839}, {0xAA77, 0xAA79}, {0xAB5B, 0xAB5B}, 
	{0xAB6A, 0xAB6B}, {0xFB29, 0xFB29}, {0xFBB2, 0xFBC2}, {0xFD40, 0xFD4F}, 
	{0xFDCF, 0xFDCF}, {0xFDFC, 0xFDFF}, {0xFE62, 0xFE62}, {0xFE64, 0xFE66}, 
	{0xFE69, 0xFE69}, {0xFF04, 0xFF04}, {0xFF0B, 0xFF0B}, {0xFF1C, 0xFF1E}, 
	{0xFF3E, 0xFF3E}, {0xFF40, 0xFF40}, {0xFF5C, 0xFF5C}, {0xFF5E, 0xFF5E}, 
	{0xFFE0, 0xFFE6}, {0xFFE8, 0xFFEE}, {0xFFFC, 0xFFFD}, {0x10137, 0x1013F}, 
	{0x10179, 0x10189}, {0x1018C, 0x1018E}, {0x10190, 0x1019C}, {0x101A0, 0x101A0}, 
	{0x101D0, 0x101FC}, {0x10877, 0x10878}, {0x10AC8, 0x10AC8}, {0x1173F, 0x1173F}, 
	{0x11FD5, 0x11FF1}, {0x16B3C, 0x16B3F}, {0x16B45, 0x16B45}, {0x1BC9C, 0x1BC9C}, 
	{0x1CF50, 0x1CFC3}, {0x1D000, 0x1D0F5}, {0x1D100, 0x1D126}, {0x1D129, 0x1D164}, 
	{0x1D16A, 0x1D16C}, {0x1D183, 0x1D184}, {0x1D18C, 0x1D1A9}, {0x1D1AE, 0x1D1EA}, 
	{0x1D200, 0x1D241}, {0x1D245, 0x1D245}, {0x1D300, 0x1D356}, {0x1D6C1, 0x1D6C1}, 
	{0x1D6DB, 0x1D6DB}, {0x1D6FB, 0x1D6FB}, {0x1D715, 0x1D715}, {0x1D735, 0x1D735}, 
	{0x1D74F, 0x1D74F}, {0x1D76F, 0x1D76F}, {0x1D789, 0x1D789}, {0x1D7A9, 0x1D7A9}, 
	{0x1D7C3, 0x1D7C3}, {0x1D800, 0x1D9FF}, {0x1DA37, 0x1DA3A}, {0x1DA6D, 0x1DA74}, 
	{0x1DA76, 0x1DA83}, {0x1DA85, 0x1DA86}, {0x1E14F, 0x1E14F}, {0x1E2FF, 0x1E2FF}, 
	{0x1ECAC, 0x1ECAC}, {0x1ECB0, 0x1ECB0}, {0x1ED2E, 0x1ED2E}, {0x1EEF0, 0x1EEF1}, 
	{0x1F000, 0x1F02B}, {0x1F030, 0x1F093}, {0x1F0A0, 0x1F0AE}, {0x1F0B1, 0x1F0BF}, 
	{0x1F0C1, 0x1F0CF}, {0x1F0D1, 0x1F0F5}, {0x1F10D, 0x1F1AD}, {0x1F1E6, 0x1F202}, 
	{0x1F210, 0x1F23B}, {0x1F240, 0x1F248}, {0x1F250, 0x1F251}, {0x1F260, 0x1F265}, 
	{0x1F300, 0x1F6D7}, {0x1F6DC, 0x1F6EC}, {0x1F6F0, 0x1F6FC}, {0x1F700, 0x1F776}, 
	{0x1F77B, 0x1F7D9}, {0x1F7E0, 0x1F7EB}, {0x1F7F0, 0x1F7F0}, {0x1F800, 0x1F80B}, 
	{0x1F810, 0x1F847}, {0x1F850, 0x1F859}, {0x1F860, 0x1F887}, {0x1F890, 0x1F8AD}, 
	{0x1F8B0, 0x1F8B1}, {0x1F900, 0x1FA53}, {0x1FA60, 0x1FA6D}, {0x1FA70, 0x1FA7C}, 
	{0x1FA80, 0x1FA88}, {0x1FA90, 0x1FABD}, {0x1FABF, 0x1FAC5}, {0x1FACE, 0x1FADB}, 
	{0x1FAE0, 0x1FAE8}, {0x1FAF0, 0x1FAF8}, {0x1FB00, 0x1FB92}, {0x1FB94, 0x1FBCA}, 
};
static const guji_rune_range_t guji_prop_Samaritan[] = {
	{0x0800, 0x082D}, {0x0830, 0x083E}, 
};
static const guji_rune_range_t guji_prop_Saurashtra[] = {
	{0xA880, 0xA8C5}, {0xA8CE, 0xA8D9}, 
};
static const guji_rune_range_t guji_prop_Sc[] = {
	{0x0024, 0x0024}, {0x00A2, 0x00A5}, {0x058F, 0x058F}, {0x060B, 0x060B}, 
	{0x07FE, 0x07FF}, {0x09F2, 0x09F3}, {0x09FB, 0x09FB}, {0x0AF1, 0x0AF1}, 
	{0x0BF9, 0x0BF9}, {0x0E3F, 0x0E3F}, {0x17DB, 0x17DB}, {0x20A0, 0x20C0}, 
	{0xA838, 0xA838}, {0xFDFC, 0xFDFC}, {0xFE69, 0xFE69}, {0xFF04, 0xFF04}, 
	{0xFFE0, 0xFFE1}, {0xFFE5, 0xFFE6}, {0x11FDD, 0x11FE0}, {0x1E2FF, 0x1E2FF}, 
	{0x1ECB0, 0x1ECB0}, 
};
static const guji_rune_range_t guji_prop_Sharada[] = {
	{0x11180, 0x111DF}, 
};
static const guji_rune_range_t guji_prop_Shavian[] = {
	{0x10450, 0x1047F}, 
};
static const guji_rune_range_t guji_prop_Siddham[] = {
	{0x11580, 0x115B5}, {0x115B8, 0x115DD}, 
};
static const guji_rune_range_t guji_prop_SignWriting[] = {
	{0x1D800, 0x1DA8B}, {0x1DA9B, 0x1DA9F}, {0x1DAA1, 0x1DAAF}, 
};
static const guji_rune_range_t guji_prop_Sinhala[] = {
	{0x0D81, 0x0D83}, {0x0D85, 0x0D96}, {0x0D9A, 0x0DB1}, {0x0DB3, 0x0DBB}, 
	{0x0DBD, 0x0DBD}, {0x0DC0, 0x0DC6}, {0x0DCA, 0x0DCA}, {0x0DCF, 0x0DD4}, 
	{0x0DD6, 0x0DD6}, {0x0DD8, 0x0DDF}, {0x0DE6, 0x0DEF}, {0x0DF2, 0x0DF4}, 
	{0x111E1, 0x111F4}, 
};
static const guji_rune_range_t guji_prop_Sk[] = {
	{0x005E, 0x005E}, {0x0060, 0x0060}, {0x00A8, 0x00A8}, {0x00AF, 0x00AF}, 
	{0x00B4, 0x00B4}, {0x00B8, 0x00B8}, {0x02C2, 0x02C5}, {0x02D2, 0x02DF}, 
	{0x02E5, 0x02EB}, {0x02ED, 0x02ED}, {0x02EF, 0x02FF}, {0x0375, 0x0375}, 
	{0x0384, 0x0385}, {0x0888, 0x0888}, {0x1FBD, 0x1FBD}, {0x1FBF, 0x1FC1}, 
	{0x1FCD, 0x1FCF}, {0x1FDD, 0x1FDF}, {0x1FED, 0x1FEF}, {0x1FFD, 0x1FFE}, 
	{0x309B, 0x309C}, {0xA700, 0xA716}, {0xA720, 0xA721}, {0xA789, 0xA78A}, 
	{0xAB5B, 0xAB5B}, {0xAB6A, 0xAB6B}, {0xFBB2, 0xFBC2}, {0xFF3E, 0xFF3E}, 
	{0xFF40, 0xFF40}, {0xFFE3, 0xFFE3}, {0x1F3FB, 0x1F3FF}, 
};
static const guji_rune_range_t guji_prop_Sm[] = {
	{0x002B, 0x002B}, {0x003C, 0x003E}, {0x007C, 0x007C}, {0x007E, 0x007E}, 
	{0x00AC, 0x00AC}, {0x00B1, 0x00B1}, {0x00D7, 0x00D7}, {0x00F7, 0x00F7}, 
	{0x03F6, 0x03F6}, {0x0606, 0x0608}, {0x2044, 0x2044}, {0x2052, 0x2052}, 
	{0x207A, 0x207C}, {0x208A, 0x208C}, {0x2118, 0x2118}, {0x2140, 0x2144}, 
	{0x214B, 0x214B}, {0x2190, 0x2194}, {0x219A, 0x219B}, {0x21A0, 0x21A0}, 
	{0x21A3, 0x21A3}, {0x21A6, 0x21A6}, {0x21AE, 0x21AE}, {0x21CE, 0x21CF}, 
	{0x21D2, 0x21D2}, {0x21D4, 0x21D4}, {0x21F4, 0x22FF}, {0x2320, 0x2321}, 
	{0x237C, 0x237C}, {0x239B, 0x23B3}, {0x23DC, 0x23E1}, {0x25B7, 0x25B7}, 
	{0x25C1, 0x25C1}, {0x25F8, 0x25FF}, {0x266F, 0x266F}, {0x27C0, 0x27C4}, 
	{0x27C7, 0x27E5}, {0x27F0, 0x27FF}, {0x2900, 0x2982}, {0x2999, 0x29D7}, 
	{0x29DC, 0x29FB}, {0x29FE, 0x2AFF}, {0x2B30, 0x2B44}, {0x2B47, 0x2B4C}, 
	{0xFB29, 0xFB29}, {0xFE62, 0xFE62}, {0xFE64, 0xFE66}, {0xFF0B, 0xFF0B}, 
	{0xFF1C, 0xFF1E}, {0xFF5C, 0xFF5C}, {0xFF5E, 0xFF5E}, {0xFFE2, 0xFFE2}, 
	{0xFFE9, 0xFFEC}, {0x1D6C1, 0x1D6C1}, {0x1D6DB, 0x1D6DB}, {0x1D6FB, 0x1D6FB}, 
	{0x1D715, 0x1D715}, {0x1D735, 0x1D735}, {0x1D74F, 0x1D74F}, {0x1D76F, 0x1D76F}, 
	{0x1D789, 0x1D789}, {0x1D7A9, 0x1D7A9}, {0x1D7C3, 0x1D7C3}, {0x1EEF0, 0x1EEF1}, 
};
static const guji_rune_range_t guji_prop_So[] = {
	{0x00A6, 0x00A6}, {0x00A9, 0x00A9}, {0x00AE, 0x00AE}, {0x00B0, 0x00B0}, 
	{0x0482, 0x0482}, {0x058D, 0x058E}, {0x060E, 0x060F}, {0x06DE, 0x06DE}, 
	{0x06E9, 0x06E9}, {0x06FD, 0x06FE}, {0x07F6, 0x07F6}, {0x09FA, 0x09FA}, 
	{0x0B70, 0x0B70}, {0x0BF3, 0x0BF8}, {0x0BFA, 0x0BFA}, {0x0C7F, 0x0C7F}, 
	{0x0D4F, 0x0D4F}, {0x0D79, 0x0D79}, {0x0F01, 0x0F03}, {0x0F13, 0x0F13}, 
	{0x0F15, 0x0F17}, {0x0F1A, 0x0F1F}, {0x0F34, 0x0F34}, {0x0F36, 0x0F36}, 
	{0x0F38, 0x0F38}, {0x0FBE, 0x0FC5}, {0x0FC7, 0x0FCC}, {0x0FCE, 0x0FCF}, 
	{0x0FD5, 0x0FD8}, {0x109E, 0x109F}, {0x1390, 0x1399}, {0x166D, 0x166D}, 
	{0x1940, 0x1940}, {0x19DE, 0x19FF}, {0x1B61, 0x1B6A}, {0x1B74, 0x1B7C}, 
	{0x2100, 0x2101}, {0x2103, 0x2106}, {0x2108, 0x2109}, {0x2114, 0x2114}, 
	{0x2116, 0x2117}, {0x211E, 0x2123}, {0x2125, 0x2125}, {0x2127, 0x2127}, 
	{0x2129, 0x2129}, {0x212E, 0x212E}, {0x213A, 0x213B}, {0x214A, 0x214A}, 
	{0x214C, 0x214D}, {0x214F, 0x214F}, {0x218A, 0x218B}, {0x2195, 0x2199}, 
	{0x219C, 0x219F}, {0x21A1, 0x21A2}, {0x21A4, 0x21A5}, {0x21A7, 0x21AD}, 
	{0x21AF, 0x21CD}, {0x21D0, 0x21D1}, {0x21D3, 0x21D3}, {0x21D5, 0x21F3}, 
	{0x2300, 0x2307}, {0x230C, 0x231F}, {0x2322, 0x2328}, {0x232B, 0x237B}, 
	{0x237D, 0x239A}, {0x23B4, 0x23DB}, {0x23E2, 0x2426}, {0x2440, 0x244A}, 
	{0x249C, 0x24E9}, {0x2500, 0x25B6}, {0x25B8, 0x25C0}, {0x25C2, 0x25F7}, 
	{0x2600, 0x266E}, {0x2670, 0x2767}, {0x2794, 0x27BF}, {0x2800, 0x28FF}, 
	{0x2B00, 0x2B2F}, {0x2B45, 0x2B46}, {0x2B4D, 0x2B73}, {0x2B76, 0x2B95}, 
	{0x2B97, 0x2BFF}, {0x2CE5, 0x2CEA}, {0x2E50, 0x2E51}, {0x2E80, 0x2E99}, 
	{0x2E9B, 0x2EF3}, {0x2F00, 0x2FD5}, {0x2FF0, 0x2FFB}, {0x3004, 0x3004}, 
	{0x3012, 0x3013}, {0x3020, 0x3020}, {0x3036, 0x3037}, {0x303E, 0x303F}, 
	{0x3190, 0x3191}, {0x3196, 0x319F}, {0x31C0, 0x31E3}, {0x3200, 0x321E}, 
	{0x322A, 0x3247}, {0x3250, 0x3250}, {0x3260, 0x327F}, {0x328A, 0x32B0}, 
	{0x32C0, 0x33FF}, {0x4DC0, 0x4DFF}, {0xA490, 0xA4C6}, {0xA828, 0xA82B}, 
	{0xA836, 0xA837}, {0xA839, 0xA839}, {0xAA77, 0xAA79}, {0xFD40, 0xFD4F}, 
	{0xFDCF, 0xFDCF}, {0xFDFD, 0xFDFF}, {0xFFE4, 0xFFE4}, {0xFFE8, 0xFFE8}, 
	{0xFFED, 0xFFEE}, {0xFFFC, 0xFFFD}, {0x10137, 0x1013F}, {0x10179, 0x10189}, 
	{0x1018C, 0x1018E}, {0x10190, 0x1019C}, {0x101A0, 0x101A0}, {0x101D0, 0x101FC}, 
	{0x10877, 0x10878}, {0x10AC8, 0x10AC8}, {0x1173F, 0x1173F}, {0x11FD5, 0x11FDC}, 
	{0x11FE1, 0x11FF1}, {0x16B3C, 0x16B3F}, {0x16B45, 0x16B45}, {0x1BC9C, 0x1BC9C}, 
	{0x1CF50, 0x1CFC3}, {0x1D000, 0x1D0F5}, {0x1D100, 0x1D126}, {0x1D129, 0x1D164}, 
	{0x1D16A, 0x1D16C}, {0x1D183, 0x1D184}, {0x1D18C, 0x1D1A9}, {0x1D1AE, 0x1D1EA}, 
	{0x1D200, 0x1D241}, {0x1D245, 0x1D245}, {0x1D300, 0x1D356}, {0x1D800, 0x1D9FF}, 
	{0x1DA37, 0x1DA3A}, {0x1DA6D, 0x1DA74}, {0x1DA76, 0x1DA83}, {0x1DA85, 0x1DA86}, 
	{0x1E14F, 0x1E14F}, {0x1ECAC, 0x1ECAC}, {0x1ED2E, 0x1ED2E}, {0x1F000, 0x1F02B}, 
	{0x1F030, 0x1F093}, {0x1F0A0, 0x1F0AE}, {0x1F0B1, 0x1F0BF}, {0x1F0C1, 0x1F0CF}, 
	{0x1F0D1, 0x1F0F5}, {0x1F10D, 0x1F1AD}, {0x1F1E6, 0x1F202}, {0x1F210, 0x1F23B}, 
	{0x1F240, 0x1F248}, {0x1F250, 0x1F251}, {0x1F260, 0x1F265}, {0x1F300, 0x1F3FA}, 
	{0x1F400, 0x1F6D7}, {0x1F6DC, 0x1F6EC}, {0x1F6F0, 0x1F6FC}, {0x1F700, 0x1F776}, 
	{0x1F77B, 0x1F7D9}, {0x1F7E0, 0x1F7EB}, {0x1F7F0, 0x1F7F0}, {0x1F800, 0x1F80B}, 
	{0x1F810, 0x1F847}, {0x1F850, 0x1F859}, {0x1F860, 0x1F887}, {0x1F890, 0x1F8AD}, 
	{0x1F8B0, 0x1F8B1}, {0x1F900, 0x1FA53}, {0x1FA60, 0x1FA6D}, {0x1FA70, 0x1FA7C}, 
	{0x1FA80, 0x1FA88}, {0x1FA90, 0x1FABD}, {0x1FABF, 0x1FAC5}, {0x1FACE, 0x1FADB}, 
	{0x1FAE0, 0x1FAE8}, {0x1FAF0, 0x1FAF8}, {0x1FB00, 0x1FB92}, {0x1FB94, 0x1FBCA}, 
};
static const guji_rune_range_t guji_prop_Sogdian[] = {
	{0x10F30, 0x10F59}, 
};
static const guji_rune_range_t guji_prop_Sora_Sompeng[] = {
	{0x110D0, 0x110E8}, {0x110F0, 0x110F9}, 
};
static const guji_rune_range_t guji_prop_Soyombo[] = {
	{0x11A50, 0x11AA2}, 
};
static const guji_rune_range_t guji_prop_Sundanese[] = {
	{0x1B80, 0x1BBF}, {0x1CC0, 0x1CC7}, 
};
static const guji_rune_range_t guji_prop_Syloti_Nagri[] = {
	{0xA800, 0xA82C}, 
};
static const guji_rune_range_t guji_prop_Syriac[] = {
	{0x0700, 0x070D}, {0x070F, 0x074A}, {0x074D, 0x074F}, {0x0860, 0x086A}, 
};
static const guji_rune_range_t guji_prop_Tagalog[] = {
	{0x1700, 0x1715}, {0x171F, 0x171F}, 
};
static const guji_rune_range_t guji_prop_Tagbanwa[] = {
	{0x1760, 0x176C}, {0x176E, 0x1770}, {0x1772, 0x1773}, 
};
static const guji_rune_range_t guji_prop_Tai_Le[] = {
	{0x1950, 0x196D}, {0x1970, 0x1974}, 
};
static const guji_rune_range_t guji_prop_Tai_Tham[] = {
	{0x1A20, 0x1A5E}, {0x1A60, 0x1A7C}, {0x1A7F, 0x1A89}, {0x1A90, 0x1A99}, 
	{0x1AA0, 0x1AAD}, 
};
static const guji_rune_range_t guji_prop_Tai_Viet[] = {
	{0xAA80, 0xAAC2}, {0xAADB, 0xAADF}, 
};
static const guji_rune_range_t guji_prop_Takri[] = {
	{0x11680, 0x116B9}, {0x116C0, 0x116C9}, 
};
static const guji_rune_range_t guji_prop_Tamil[] = {
	{0x0B82, 0x0B83}, {0x0B85, 0x0B8A}, {0x0B8E, 0x0B90}, {0x0B92, 0x0B95}, 
	{0x0B99, 0x0B9A}, {0x0B9C, 0x0B9C}, {0x0B9E, 0x0B9F}, {0x0BA3, 0x0BA4}, 
	{0x0BA8, 0x0BAA}, {0x0BAE, 0x0BB9}, {0x0BBE, 0x0BC2}, {0x0BC6, 0x0BC8}, 
	{0x0BCA, 0x0BCD}, {0x0BD0, 0x0BD0}, {0x0BD7, 0x0BD7}, {0x0BE6, 0x0BFA}, 
	{0x11FC0, 0x11FF1}, {0x11FFF, 0x11FFF}, 
};
static const guji_rune_range_t guji_prop_Tangsa[] = {
	{0x16A70, 0x16ABE}, {0x16AC0, 0x16AC9}, 
};
static const guji_rune_range_t guji_prop_Tangut[] = {
	{0x16FE0, 0x16FE0}, {0x17000, 0x187F7}, {0x18800, 0x18AFF}, {0x18D00, 0x18D08}, 
};
static const guji_rune_range_t guji_prop_Telugu[] = {
	{0x0C00, 0x0C0C}, {0x0C0E, 0x0C10}, {0x0C12, 0x0C28}, {0x0C2A, 0x0C39}, 
	{0x0C3C, 0x0C44}, {0x0C46, 0x0C48}, {0x0C4A, 0x0C4D}, {0x0C55, 0x0C56}, 
	{0x0C58, 0x0C5A}, {0x0C5D, 0x0C5D}, {0x0C60, 0x0C63}, {0x0C66, 0x0C6F}, 
	{0x0C77, 0x0C7F}, 
};
static const guji_rune_range_t guji_prop_Thaana[] = {
	{0x0780, 0x07B1}, 
};
static const guji_rune_range_t guji_prop_Thai[] = {
	{0x0E01, 0x0E3A}, {0x0E40, 0x0E5B}, 
};
static const guji_rune_range_t guji_prop_Tibetan[] = {
	{0x0F00, 0x0F47}, {0x0F49, 0x0F6C}, {0x0F71, 0x0F97}, {0x0F99, 0x0FBC}, 
	{0x0FBE, 0x0FCC}, {0x0FCE, 0x0FD4}, {0x0FD9, 0x0FDA}, 
};
static const guji_rune_range_t guji_prop_Tifinagh[] = {
	{0x2D30, 0x2D67}, {0x2D6F, 0x2D70}, {0x2D7F, 0x2D7F}, 
};
static const guji_rune_range_t guji_prop_Tirhuta[] = {
	{0x11480, 0x114C7}, {0x114D0, 0x114D9}, 
};
static const guji_rune_range_t guji_prop_Toto[] = {
	{0x1E290, 0x1E2AE}, 
};
static const guji_rune_range_t guji_prop_Ugaritic[] = {
	{0x10380, 0x1039D}, {0x1039F, 0x1039F}, 
};
static const guji_rune_range_t guji_prop_Uppercase[] = {
	{0x0041, 0x005A}, {0x00C0, 0x00D6}, {0x00D8, 0x00DE}, {0x0100, 0x0100}, 
	{0x0102, 0x0102}, {0x0104, 0x0104}, {0x0106, 0x0106}, {0x0108, 0x0108}, 
	{0x010A, 0x010A}, {0x010C, 0x010C}, {0x010E, 0x010E}, {0x0110, 0x0110}, 
	{0x0112, 0x0112}, {0x0114, 0x0114}, {0x0116, 0x0116}, {0x0118, 0x0118}, 
	{0x011A, 0x011A}, {0x011C, 0x011C}, {0x011E, 0x011E}, {0x0120, 0x0120}, 
	{0x0122, 0x0122}, {0x0124, 0x0124}, {0x0126, 0x0126}, {0x0128, 0x0128}, 
	{0x012A, 0x012A}, {0x012C, 0x012C}, {0x012E, 0x012E}, {0x0130, 0x0130}, 
	{0x0132, 0x0132}, {0x0134, 0x0134}, {0x0136, 0x0136}, {0x0139, 0x0139}, 
	{0x013B, 0x013B}, {0x013D, 0x013D}, {0x013F, 0x013F}, {0x0141, 0x0141}, 
	{0x0143, 0x0143}, {0x0145, 0x0145}, {0x0147, 0x0147}, {0x014A, 0x014A}, 
	{0x014C, 0x014C}, {0x014E, 0x014E}, {0x0150, 0x0150}, {0x0152, 0x0152}, 
	{0x0154, 0x0154}, {0x0156, 0x0156}, {0x0158, 0x0158}, {0x015A, 0x015A}, 
	{0x015C, 0x015C}, {0x015E, 0x015E}, {0x0160, 0x0160}, {0x0162, 0x0162}, 
	{0x0164, 0x0164}, {0x0166, 0x0166}, {0x0168, 0x0168}, {0x016A, 0x016A}, 
	{0x016C, 0x016C}, {0x016E, 0x016E}, {0x0170, 0x0170}, {0x0172, 0x0172}, 
	{0x0174, 0x0174}, {0x0176, 0x0176}, {0x0178, 0x0179}, {0x017B, 0x017B}, 
	{0x017D, 0x017D}, {0x0181, 0x0182}, {0x0184, 0x0184}, {0x0186, 0x0187}, 
	{0x0189, 0x018B}, {0x018E, 0x0191}, {0x0193, 0x0194}, {0x0196, 0x0198}, 
	{0x019C, 0x019D}, {0x019F, 0x01A0}, {0x01A2, 0x01A2}, {0x01A4, 0x01A4}, 
	{0x01A6, 0x01A7}, {0x01A9, 0x01A9}, {0x01AC, 0x01AC}, {0x01AE, 0x01AF}, 
	{0x01B1, 0x01B3}, {0x01B5, 0x01B5}, {0x01B7, 0x01B8}, {0x01BC, 0x01BC}, 
	{0x01C4, 0x01C4}, {0x01C7, 0x01C7}, {0x01CA, 0x01CA}, {0x01CD, 0x01CD}, 
	{0x01CF, 0x01CF}, {0x01D1, 0x01D1}, {0x01D3, 0x01D3}, {0x01D5, 0x01D5}, 
	{0x01D7, 0x01D7}, {0x01D9, 0x01D9}, {0x01DB, 0x01DB}, {0x01DE, 0x01DE}, 
	{0x01E0, 0x01E0}, {0x01E2, 0x01E2}, {0x01E4, 0x01E4}, {0x01E6, 0x01E6}, 
	{0x01E8, 0x01E8}, {0x01EA, 0x01EA}, {0x01EC, 0x01EC}, {0x01EE, 0x01EE}, 
	{0x01F1, 0x01F1}, {0x01F4, 0x01F4}, {0x01F6, 0x01F8}, {0x01FA, 0x01FA}, 
	{0x01FC, 0x01FC}, {0x01FE, 0x01FE}, {0x0200, 0x0200}, {0x0202, 0x0202}, 
	{0x0204, 0x0204}, {0x0206, 0x0206}, {0x0208, 0x0208}, {0x020A, 0x020A}, 
	{0x020C, 0x020C}, {0x020E, 0x020E}, {0x0210, 0x0210}, {0x0212, 0x0212}, 
	{0x0214, 0x0214}, {0x0216, 0x0216}, {0x0218, 0x0218}, {0x021A, 0x021A}, 
	{0x021C, 0x021C}, {0x021E, 0x021E}, {0x0220, 0x0220}, {0x0222, 0x0222}, 
	{0x0224, 0x0224}, {0x0226, 0x0226}, {0x0228, 0x0228}, {0x022A, 0x022A}, 
	{0x022C, 0x022C}, {0x022E, 0x022E}, {0x0230, 0x0230}, {0x0232, 0x0232}, 
	{0x023A, 0x023B}, {0x023D, 0x023E}, {0x0241, 0x0241}, {0x0243, 0x0246}, 
	{0x0248, 0x0248}, {0x024A, 0x024A}, {0x024C, 0x024C}, {0x024E, 0x024E}, 
	{0x0370, 0x0370}, {0x0372, 0x0372}, {0x0376, 0x0376}, {0x037F, 0x037F}, 
	{0x0386, 0x0386}, {0x0388, 0x038A}, {0x038C, 0x038C}, {0x038E, 0x038F}, 
	{0x0391, 0x03A1}, {0x03A3, 0x03AB}, {0x03CF, 0x03CF}, {0x03D2, 0x03D4}, 
	{0x03D8, 0x03D8}, {0x03DA, 0x03DA}, {0x03DC, 0x03DC}, {0x03DE, 0x03DE}, 
	{0x03E0, 0x03E0}, {0x03E2, 0x03E2}, {0x03E4, 0x03E4}, {0x03E6, 0x03E6}, 
	{0x03E8, 0x03E8}, {0x03EA, 0x03EA}, {0x03EC, 0x03EC}, {0x03EE, 0x03EE}, 
	{0x03F4, 0x03F4}, {0x03F7, 0x03F7}, {0x03F9, 0x03FA}, {0x03FD, 0x042F}, 
	{0x0460, 0x0460}, {0x0462, 0x0462}, {0x0464, 0x0464}, {0x0466, 0x0466}, 
	{0x0468, 0x0468}, {0x046A, 0x046A}, {0x046C, 0x046C}, {0x046E, 0x046E}, 
	{0x0470, 0x0470}, {0x0472, 0x0472}, {0x0474, 0x0474}, {0x0476, 0x0476}, 
	{0x0478, 0x0478}, {0x047A, 0x047A}, {0x047C, 0x047C}, {0x047E, 0x047E}, 
	{0x0480, 0x0480}, {0x048A, 0x048A}, {0x048C, 0x048C}, {0x048E, 0x048E}, 
	{0x0490, 0x0490}, {0x0492, 0x0492}, {0x0494, 0x0494}, {0x0496, 0x0496}, 
	{0x0498, 0x0498}, {0x049A, 0x049A}, {0x049C, 0x049C}, {0x049E, 0x049E}, 
	{0x04A0, 0x04A0}, {0x04A2, 0x04A2}, {0x04A4, 0x04A4}, {0x04A6, 0x04A6}, 
	{0x04A8, 0x04A8}, {0x04AA, 0x04AA}, {0x04AC, 0x04AC}, {0x04AE, 0x04AE}, 
	{0x04B0, 0x04B0}, {0x04B2, 0x04B2}, {0x04B4, 0x04B4}, {0x04B6, 0x04B6}, 
	{0x04B8, 0x04B8}, {0x04BA, 0x04BA}, {0x04BC, 0x04BC}, {0x04BE, 0x04BE}, 
	{0x04C0, 0x04C1}, {0x04C3, 0x04C3}, {0x04C5, 0x04C5}, {0x04C7, 0x04C7}, 
	{0x04C9, 0x04C9}, {0x04CB, 0x04CB}, {0x04CD, 0x04CD}, {0x04D0, 0x04D0}, 
	{0x04D2, 0x04D2}, {0x04D4, 0x04D4}, {0x04D6, 0x04D6}, {0x04D8, 0x04D8}, 
	{0x04DA, 0x04DA}, {0x04DC, 0x04DC}, {0x04DE, 0x04DE}, {0x04E0, 0x04E0}, 
	{0x04E2, 0x04E2}, {0x04E4, 0x04E4}, {0x04E6, 0x04E6}, {0x04E8, 0x04E8}, 
	{0x04EA, 0x04EA}, {0x04EC, 0x04EC}, {0x04EE, 0x04EE}, {0x04F0, 0x04F0}, 
	{0x04F2, 0x04F2}, {0x04F4, 0x04F4}, {0x04F6, 0x04F6}, {0x04F8, 0x04F8}, 
	{0x04FA, 0x04FA}, {0x04FC, 0x04FC}, {0x04FE, 0x04FE}, {0x0500, 0x0500}, 
	{0x0502, 0x0502}, {0x0504, 0x0504}, {0x0506, 0x0506}, {0x0508, 0x0508}, 
	{0x050A, 0x050A}, {0x050C, 0x050C}, {0x050E, 0x050E}, {0x0510, 0x0510}, 
	{0x0512, 0x0512}, {0x0514, 0x0514}, {0x0516, 0x0516}, {0x0518, 0x0518}, 
	{0x051A, 0x051A}, {0x051C, 0x051C}, {0x051E, 0x051E}, {0x0520, 0x0520}, 
	{0x0522, 0x0522}, {0x0524, 0x0524}, {0x0526, 0x0526}, {0x0528, 0x0528}, 
	{0x052A, 0x052A}, {0x052C, 0x052C}, {0x052E, 0x052E}, {0x0531, 0x0556}, 
	{0x10A0, 0x10C5}, {0x10C7, 0x10C7}, {0x10CD, 0x10CD}, {0x13A0, 0x13F5}, 
	{0x1C90, 0x1CBA}, {0x1CBD, 0x1CBF}, {0x1E00, 0x1E00}, {0x1E02, 0x1E02}, 
	{0x1E04, 0x1E04}, {0x1E06, 0x1E06}, {0x1E08, 0x1E08}, {0x1E0A, 0x1E0A}, 
	{0x1E0C, 0x1E0C}, {0x1E0E, 0x1E0E}, {0x1E10, 0x1E10}, {0x1E12, 0x1E12}, 
	{0x1E14, 0x1E14}, {0x1E16, 0x1E16}, {0x1E18, 0x1E18}, {0x1E1A, 0x1E1A}, 
	{0x1E1C, 0x1E1C}, {0x1E1E, 0x1E1E}, {0x1E20, 0x1E20}, {0x1E22, 0x1E22}, 
	{0x1E24, 0x1E24}, {0x1E26, 0x1E26}, {0x1E28, 0x1E28}, {0x1E2A, 0x1E2A}, 
	{0x1E2C, 0x1E2C}, {0x1E2E, 0x1E2E}, {0x1E30, 0x1E30}, {0x1E32, 0x1E32}, 
	{0x1E34, 0x1E34}, {0x1E36, 0x1E36}, {0x1E38, 0x1E38}, {0x1E3A, 0x1E3A}, 
	{0x1E3C, 0x1E3C}, {0x1E3E, 0x1E3E}, {0x1E40, 0x1E40}, {0x1E42, 0x1E42}, 
	{0x1E44, 0x1E44}, {0x1E46, 0x1E46}, {0x1E48, 0x1E48}, {0x1E4A, 0x1E4A}, 
	{0x1E4C, 0x1E4C}, {0x1E4E, 0x1E4E}, {0x1E50, 0x1E50}, {0x1E52, 0x1E52}, 
	{0x1E54, 0x1E54}, {0x1E56, 0x1E56}, {0x1E58, 0x1E58}, {0x1E5A, 0x1E5A}, 
	{0x1E5C, 0x1E5C}, {0x1E5E, 0x1E5E}, {0x1E60, 0x1E60}, {0x1E62, 0x1E62}, 
	{0x1E64, 0x1E64}, {0x1E66, 0x1E66}, {0x1E68, 0x1E68}, {0x1E6A, 0x1E6A}, 
	{0x1E6C, 0x1E6C}, {0x1E6E, 0x1E6E}, {0x1E70, 0x1E70}, {0x1E72, 0x1E72}, 
	{0x1E74, 0x1E74}, {0x1E76, 0x1E76}, {0x1E78, 0x1E78}, {0x1E7A, 0x1E7A}, 
	{0x1E7C, 0x1E7C}, {0x1E7E, 0x1E7E}, {0x1E80, 0x1E80}, {0x1E82, 0x1E82}, 
	{0x1E84, 0x1E84}, {0x1E86, 0x1E86}, {0x1E88, 0x1E88}, {0x1E8A, 0x1E8A}, 
	{0x1E8C, 0x1E8C}, {0x1E8E, 0x1E8E}, {0x1E90, 0x1E90}, {0x1E92, 0x1E92}, 
	{0x1E94, 0x1E94}, {0x1E9E, 0x1E9E}, {0x1EA0, 0x1EA0}, {0x1EA2, 0x1EA2}, 
	{0x1EA4, 0x1EA4}, {0x1EA6, 0x1EA6}, {0x1EA8, 0x1EA8}, {0x1EAA, 0x1EAA}, 
	{0x1EAC, 0x1EAC}, {0x1EAE, 0x1EAE}, {0x1EB0, 0x1EB0}, {0x1EB2, 0x1EB2}, 
	{0x1EB4, 0x1EB4}, {0x1EB6, 0x1EB6}, {0x1EB8, 0x1EB8}, {0x1EBA, 0x1EBA}, 
	{0x1EBC, 0x1EBC}, {0x1EBE, 0x1EBE}, {0x1EC0, 0x1EC0}, {0x1EC2, 0x1EC2}, 
	{0x1EC4, 0x1EC4}, {0x1EC6, 0x1EC6}, {0x1EC8, 0x1EC8}, {0x1ECA, 0x1ECA}, 
	{0x1ECC, 0x1ECC}, {0x1ECE, 0x1ECE}, {0x1ED0, 0x1ED0}, {0x1ED2, 0x1ED2}, 
	{0x1ED4, 0x1ED4}, {0x1ED6, 0x1ED6}, {0x1ED8, 0x1ED8}, {0x1EDA, 0x1EDA}, 
	{0x1EDC, 0x1EDC}, {0x1EDE, 0x1EDE}, {0x1EE0, 0x1EE0}, {0x1EE2, 0x1EE2}, 
	{0x1EE4, 0x1EE4}, {0x1EE6, 0x1EE6}, {0x1EE8, 0x1EE8}, {0x1EEA, 0x1EEA}, 
	{0x1EEC, 0x1EEC}, {0x1EEE, 0x1EEE}, {0x1EF0, 0x1EF0}, {0x1EF2, 0x1EF2}, 
	{0x1EF4, 0x1EF4}, {0x1EF6, 0x1EF6}, {0x1EF8, 0x1EF8}, {0x1EFA, 0x1EFA}, 
	{0x1EFC, 0x1EFC}, {0x1EFE, 0x1EFE}, {0x1F08, 0x1F0F}, {0x1F18, 0x1F1D}, 
	{0x1F28, 0x1F2F}, {0x1F38, 0x1F3F}, {0x1F48, 0x1F4D}, {0x1F59, 0x1F59}, 
	{0x1F5B, 0x1F5B}, {0x1F5D, 0x1F5D}, {0x1F5F, 0x1F5F}, {0x1F68, 0x1F6F}, 
	{0x1FB8, 0x1FBB}, {0x1FC8, 0x1FCB}, {0x1FD8, 0x1FDB}, {0x1FE8, 0x1FEC}, 
	{0x1FF8, 0x1FFB}, {0x2102, 0x2102}, {0x2107, 0x2107}, {0x210B, 0x210D}, 
	{0x2110, 0x2112}, {0x2115, 0x2115}, {0x2119, 0x211D}, {0x2124, 0x2124}, 
	{0x2126, 0x2126}, {0x2128, 0x2128}, {0x212A, 0x212D}, {0x2130, 0x2133}, 
	{0x213E, 0x213F}, {0x2145, 0x2145}, {0x2160, 0x216F}, {0x2183, 0x2183}, 
	{0x24B6, 0x24CF}, {0x2C00, 0x2C2F}, {0x2C60, 0x2C60}, {0x2C62, 0x2C64}, 
	{0x2C67, 0x2C67}, {0x2C69, 0x2C69}, {0x2C6B, 0x2C6B}, {0x2C6D, 0x2C70}, 
	{0x2C72, 0x2C72}, {0x2C75, 0x2C75}, {0x2C7E, 0x2C80}, {0x2C82, 0x2C82}, 
	{0x2C84, 0x2C84}, {0x2C86, 0x2C86}, {0x2C88, 0x2C88}, {0x2C8A, 0x2C8A}, 
	{0x2C8C, 0x2C8C}, {0x2C8E, 0x2C8E}, {0x2C90, 0x2C90}, {0x2C92, 0x2C92}, 
	{0x2C94, 0x2C94}, {0x2C96, 0x2C96}, {0x2C98, 0x2C98}, {0x2C9A, 0x2C9A}, 
	{0x2C9C, 0x2C9C}, {0x2C9E, 0x2C9E}, {0x2CA0, 0x2CA0}, {0x2CA2, 0x2CA2}, 
	{0x2CA4, 0x2CA4}, {0x2CA6, 0x2CA6}, {0x2CA8, 0x2CA8}, {0x2CAA, 0x2CAA}, 
	{0x2CAC, 0x2CAC}, {0x2CAE, 0x2CAE}, {0x2CB0, 0x2CB0}, {0x2CB2, 0x2CB2}, 
	{0x2CB4, 0x2CB4}, {0x2CB6, 0x2CB6}, {0x2CB8, 0x2CB8}, {0x2CBA, 0x2CBA}, 
	{0x2CBC, 0x2CBC}, {0x2CBE, 0x2CBE}, {0x2CC0, 0x2CC0}, {0x2CC2, 0x2CC2}, 
	{0x2CC4, 0x2CC4}, {0x2CC6, 0x2CC6}, {0x2CC8, 0x2CC8}, {0x2CCA, 0x2CCA}, 
	{0x2CCC, 0x2CCC}, {0x2CCE, 0x2CCE}, {0x2CD0, 0x2CD0}, {0x2CD2, 0x2CD2}, 
	{0x2CD4, 0x2CD4}, {0x2CD6, 0x2CD6}, {0x2CD8, 0x2CD8}, {0x2CDA, 0x2CDA}, 
	{0x2CDC, 0x2CDC}, {0x2CDE, 0x2CDE}, {0x2CE0, 0x2CE0}, {0x2CE2, 0x2CE2}, 
	{0x2CEB, 0x2CEB}, {0x2CED, 0x2CED}, {0x2CF2, 0x2CF2}, {0xA640, 0xA640}, 
	{0xA642, 0xA642}, {0xA644, 0xA644}, {0xA646, 0xA646}, {0xA648, 0xA648}, 
	{0xA64A, 0xA64A}, {0xA64C, 0xA64C}, {0xA64E, 0xA64E}, {0xA650, 0xA650}, 
	{0xA652, 0xA652}, {0xA654, 0xA654}, {0xA656, 0xA656}, {0xA658, 0xA658}, 
	{0xA65A, 0xA65A}, {0xA65C, 0xA65C}, {0xA65E, 0xA65E}, {0xA660, 0xA660}, 
	{0xA662, 0xA662}, {0xA664, 0xA664}, {0xA666, 0xA666}, {0xA668, 0xA668}, 
	{0xA66A, 0xA66A}, {0xA66C, 0xA66C}, {0xA680, 0xA680}, {0xA682, 0xA682}, 
	{0xA684, 0xA684}, {0xA686, 0xA686}, {0xA688, 0xA688}, {0xA68A, 0xA68A}, 
	{0xA68C, 0xA68C}, {0xA68E, 0xA68E}, {0xA690, 0xA690}, {0xA692, 0xA692}, 
	{0xA694, 0xA694}, {0xA696, 0xA696}, {0xA698, 0xA698}, {0xA69A, 0xA69A}, 
	{0xA722, 0xA722}, {0xA724, 0xA724}, {0xA726, 0xA726}, {0xA728, 0xA728}, 
	{0xA72A, 0xA72A}, {0xA72C, 0xA72C}, {0xA72E, 0xA72E}, {0xA732, 0xA732}, 
	{0xA734, 0xA734}, {0xA736, 0xA736}, {0xA738, 0xA738}, {0xA73A, 0xA73A}, 
	{0xA73C, 0xA73C}, {0xA73E, 0xA73E}, {0xA740, 0xA740}, {0xA742, 0xA742}, 
	{0xA744, 0xA744}, {0xA746, 0xA746}, {0xA748, 0xA748}, {0xA74A, 0xA74A}, 
	{0xA74C, 0xA74C}, {0xA74E, 0xA74E}, {0xA750, 0xA750}, {0xA752, 0xA752}, 
	{0xA754, 0xA754}, {0xA756, 0xA756}, {0xA758, 0xA758}, {0xA75A, 0xA75A}, 
	{0xA75C, 0xA75C}, {0xA75E, 0xA75E}, {0xA760, 0xA760}, {0xA762, 0xA762}, 
	{0xA764, 0xA764}, {0xA766, 0xA766}, {0xA768, 0xA768}, {0xA76A, 0xA76A}, 
	{0xA76C, 0xA76C}, {0xA76E, 0xA76E}, {0xA779, 0xA779}, {0xA77B, 0xA77B}, 
	{0xA77D, 0xA77E}, {0xA780, 0xA780}, {0xA782, 0xA782}, {0xA784, 0xA784}, 
	{0xA786, 0xA786}, {0xA78B, 0xA78B}, {0xA78D, 0xA78D}, {0xA790, 0xA790}, 
	{0xA792, 0xA792}, {0xA796, 0xA796}, {0xA798, 0xA798}, {0xA79A, 0xA79A}, 
	{0xA79C, 0xA79C}, {0xA79E, 0xA79E}, {0xA7A0, 0xA7A0}, {0xA7A2, 0xA7A2}, 
	{0xA7A4, 0xA7A4}, {0xA7A6, 0xA7A6}, {0xA7A8, 0xA7A8}, {0xA7AA, 0xA7AE}, 
	{0xA7B0, 0xA7B4}, {0xA7B6, 0xA7B6}, {0xA7B8, 0xA7B8}, {0xA7BA, 0xA7BA}, 
	{0xA7BC, 0xA7BC}, {0xA7BE, 0xA7BE}, {0xA7C0, 0xA7C0}, {0xA7C2, 0xA7C2}, 
	{0xA7C4, 0xA7C7}, {0xA7C9, 0xA7C9}, {0xA7D0, 0xA7D0}, {0xA7D6, 0xA7D6}, 
	{0xA7D8, 0xA7D8}, {0xA7F5, 0xA7F5}, {0xFF21, 0xFF3A}, {0x10400, 0x10427}, 
	{0x104B0, 0x104D3}, {0x10570, 0x1057A}, {0x1057C, 0x1058A}, {0x1058C, 0x10592}, 
	{0x10594, 0x10595}, {0x10C80, 0x10CB2}, {0x118A0, 0x118BF}, {0x16E40, 0x16E5F}, 
	{0x1D400, 0x1D419}, {0x1D434, 0x1D44D}, {0x1D468, 0x1D481}, {0x1D49C, 0x1D49C}, 
	{0x1D49E, 0x1D49F}, {0x1D4A2, 0x1D4A2}, {0x1D4A5, 0x1D4A6}, {0x1D4A9, 0x1D4AC}, 
	{0x1D4AE, 0x1D4B5}, {0x1D4D0, 0x1D4E9}, {0x1D504, 0x1D505}, {0x1D507, 0x1D50A}, 
	{0x1D50D, 0x1D514}, {0x1D516, 0x1D51C}, {0x1D538, 0x1D539}, {0x1D53B, 0x1D53E}, 
	{0x1D540, 0x1D544}, {0x1D546, 0x1D546}, {0x1D54A, 0x1D550}, {0x1D56C, 0x1D585}, 
	{0x1D5A0, 0x1D5B9}, {0x1D5D4, 0x1D5ED}, {0x1D608, 0x1D621}, {0x1D63C, 0x1D655}, 
	{0x1D670, 0x1D689}, {0x1D6A8, 0x1D6C0}, {0x1D6E2, 0x1D6FA}, {0x1D71C, 0x1D734}, 
	{0x1D756, 0x1D76E}, {0x1D790, 0x1D7A8}, {0x1D7CA, 0x1D7CA}, {0x1E900, 0x1E921}, 
	{0x1F130, 0x1F149}, {0x1F150, 0x1F169}, {0x1F170, 0x1F189}, 
};
static const guji_rune_range_t guji_prop_Vai[] = {
	{0xA500, 0xA62B}, 
};
static const guji_rune_range_t guji_prop_Vithkuqi[] = {
	{0x10570, 0x1057A}, {0x1057C, 0x1058A}, {0x1058C, 0x10592}, {0x10594, 0x10595}, 
	{0x10597, 0x105A1}, {0x105A3, 0x105B1}, {0x105B3, 0x105B9}, {0x105BB, 0x105BC}, 
};
static const guji_rune_range_t guji_prop_Wancho[] = {
	{0x1E2C0, 0x1E2F9}, {0x1E2FF, 0x1E2FF}, 
};
static const guji_rune_range_t guji_prop_Warang_Citi[] = {
	{0x118A0, 0x118F2}, {0x118FF, 0x118FF}, 
};
static const guji_rune_range_t guji_prop_White_Space[] = {
	{0x0009, 0x000D}, {0x0020, 0x0020}, {0x0085, 0x0085}, {0x00A0, 0x00A0}, 
	{0x1680, 0x1680}, {0x2000, 0x200A}, {0x2028, 0x2029}, {0x202F, 0x202F}, 
	{0x205F, 0x205F}, {0x3000, 0x3000}, 
};
static const guji_rune_range_t guji_prop_Yezidi[] = {
	{0x10E80, 0x10EA9}, {0x10EAB, 0x10EAD}, {0x10EB0, 0x10EB1}, 
};
static const guji_rune_range_t guji_prop_Yi[] = {
	{0xA000, 0xA48C}, {0xA490, 0xA4C6}, 
};
static const guji_rune_range_t guji_prop_Z[] = {
	{0x0020, 0x0020}, {0x00A0, 0x00A0}, {0x1680, 0x1680}, {0x2000, 0x200A}, 
	{0x2028, 0x2029}, {0x202F, 0x202F}, {0x205F, 0x205F}, {0x3000, 0x3000}, 
};
static const guji_rune_range_t guji_prop_Zanabazar_Square[] = {
	{0x11A00, 0x11A47}, 
};
static const guji_rune_range_t guji_prop_Zl[] = {
	{0x2028, 0x2028}, 
};
static const guji_rune_range_t guji_prop_Zp[] = {
	{0x2029, 0x2029}, 
};
static const guji_rune_range_t guji_prop_Zs[] = {
	{0x0020, 0x0020}, {0x00A0, 0x00A0}, {0x1680, 0x1680}, {0x2000, 0x200A}, 
	{0x202F, 0x202F}, {0x205F, 0x205F}, {0x3000, 0x3000}, 
};

static const guji_unicode_table_t guji_unicode_properties[] = {
	{"Adlam", guji_prop_Adlam, 3},
	{"Ahom", guji_prop_Ahom, 3},
	{"Alphabetic", guji_prop_Alphabetic, 732},
	{"Anatolian_Hieroglyphs", guji_prop_Anatolian_Hieroglyphs, 1},
	{"Arabic", guji_prop_Arabic, 58},
	{"Armenian", guji_prop_Armenian, 4},
	{"Avestan", guji_prop_Avestan, 2},
	{"Balinese", guji_prop_Balinese, 2},
	{"Bamum", guji_prop_Bamum, 2},
	{"Bassa_Vah", guji_prop_Bassa_Vah, 2},
	{"Batak", guji_prop_Batak, 2},
	{"Bengali", guji_prop_Bengali, 14},
	{"Bhaiksuki", guji_prop_Bhaiksuki, 4},
	{"Bopomofo", guji_prop_Bopomofo, 3},
	{"Brahmi", guji_prop_Brahmi, 3},
	{"Braille", guji_prop_Braille, 1},
	{"Buginese", guji_prop_Buginese, 2},
	{"Buhid", guji_prop_Buhid, 1},
	{"C", guji_prop_C, 26},
	{"Canadian_Aboriginal", guji_prop_Canadian_Aboriginal, 3},
	{"Carian", guji_prop_Carian, 1},
	{"Caucasian_Albanian", guji_prop_Caucasian_Albanian, 2},
	{"Cc", guji_prop_Cc, 2},
	{"Cf", guji_prop_Cf, 21},
	{"Chakma", guji_prop_Chakma, 2},
	{"Cham", guji_prop_Cham, 4},
	{"Cherokee", guji_prop_Cherokee, 3},
	{"Chorasmian", guji_prop_Chorasmian, 1},
	{"Co", guji_prop_Co, 3},
	{"Common", guji_prop_Common, 173},
	{"Coptic", guji_prop_Coptic, 3},
	{"Cs", guji_prop_Cs, 1},
	{"Cuneiform", guji_prop_Cuneiform, 4},
	{"Cypriot", guji_prop_Cypriot, 6},
	{"Cypro_Minoan", guji_prop_Cypro_Minoan, 1},
	{"Cyrillic", guji_prop_Cyrillic, 10},
	{"Deseret", guji_prop_Deseret, 1},
	{"Devanagari", guji_prop_Devanagari, 5},
	{"Dives_Akuru", guji_prop_Dives_Akuru, 8},
	{"Dogra", guji_prop_Dogra, 1},
	{"Duployan", guji_prop_Duployan, 5},
	{"Egyptian_Hieroglyphs", guji_prop_Egyptian_Hieroglyphs, 1},
	{"Elbasan", guji_prop_Elbasan, 1},
	{"Elymaic", guji_prop_Elymaic, 1},
	{"Emoji", guji_prop_Emoji, 151},
	{"Ethiopic", guji_prop_Ethiopic, 36},
	{"Extended_Pictographic", guji_prop_Extended_Pictographic, 78},
	{"Georgian", guji_prop_Georgian, 10},
	{"Glagolitic", guji_prop_Glagolitic, 6},
	{"Gothic", guji_prop_Gothic, 1},
	{"Grantha", guji_prop_Grantha, 15},
	{"Greek", guji_prop_Greek, 36},
	{"Gujarati", guji_prop_Gujarati, 14},
	{"Gunjala_Gondi", guji_prop_Gunjala_Gondi, 6},
	{"Gurmukhi", guji_prop_Gurmukhi, 16},
	{"Han", guji_prop_Han, 21},
	{"Hangul", guji_prop_Hangul, 14},
	{"Hanifi_Rohingya", guji_prop_Hanifi_Rohingya, 2},
	{"Hanunoo", guji_prop_Hanunoo, 1},
	{"Hatran", guji_prop_Hatran, 3},
	{"Hebrew", guji_prop_Hebrew, 9},
	{"Hiragana", guji_prop_Hiragana, 6},
	{"Imperial_Aramaic", guji_prop_Imperial_Aramaic, 2},
	{"Inherited", guji_prop_Inherited, 29},
	{"Inscriptional_Pahlavi", guji_prop_Inscriptional_Pahlavi, 2},
	{"Inscriptional_Parthian", guji_prop_Inscriptional_Parthian, 2},
	{"Javanese", guji_prop_Javanese, 3},
	{"Kaithi", guji_prop_Kaithi, 2},
	{"Kannada", guji_prop_Kannada, 13},
	{"Katakana", guji_prop_Katakana, 14},
	{"Kawi", guji_prop_Kawi, 3},
	{"Kayah_Li", guji_prop_Kayah_Li, 2},
	{"Kharoshthi", guji_prop_Kharoshthi, 8},
	{"Khitan_Small_Script", guji_prop_Khitan_Small_Script, 2},
	{"Khmer", guji_prop_Khmer, 4},
	{"Khojki", guji_prop_Khojki, 2},
	{"Khudawadi", guji_prop_Khudawadi, 2},
	{"L", guji_prop_L, 659},
	{"Lao", guji_prop_Lao, 11},
	{"Latin", guji_prop_Latin, 39},
	{"Lepcha", guji_prop_Lepcha, 3},
	{"Limbu", guji_prop_Limbu, 5},
	{"Linear_A", guji_prop_Linear_A, 3},
	{"Linear_B", guji_prop_Linear_B, 7},
	{"Lisu", guji_prop_Lisu, 2},
	{"Ll", guji_prop_Ll, 658},
	{"Lm", guji_prop_Lm, 71},
	{"Lo", guji_prop_Lo, 510},
	{"Lowercase", guji_prop_Lowercase, 671},
	{"Lt", guji_prop_Lt, 10},
	{"Lu", guji_prop_Lu, 646},
	{"Lycian", guji_prop_Lycian, 1},
	{"Lydian", guji_prop_Lydian, 2},
	{"M", guji_prop_M, 310},
	{"Mahajani", guji_prop_Mahajani, 1},
	{"Makasar", guji_prop_Makasar, 1},
	{"Malayalam", guji_prop_Malayalam, 7},
	{"Mandaic", guji_prop_Mandaic, 2},
	{"Manichaean", guji_prop_Manichaean, 2},
	{"Marchen", guji_prop_Marchen, 3},
	{"Masaram_Gondi", guji_prop_Masaram_Gondi, 7},
	{"Mc", guji_prop_Mc, 182},
	{"Me", guji_prop_Me, 5},
	{"Medefaidrin", guji_prop_Medefaidrin, 1},
	{"Meetei_Mayek", guji_prop_Meetei_Mayek, 3},
	{"Mende_Kikakui", guji_prop_Mende_Kikakui, 2},
	{"Meroitic_Cursive", guji_prop_Meroitic_Cursive, 3},
	{"Meroitic_Hieroglyphs", guji_prop_Meroitic_Hieroglyphs, 1},
	{"Miao", guji_prop_Miao, 3},
	{"Mn", guji_prop_Mn, 346},
	{"Modi", guji_prop_Modi, 2},
	{"Mongolian", guji_prop_Mongolian, 6},
	{"Mro", guji_prop_Mro, 3},
	{"Multani", guji_prop_Multani, 5},
	{"Myanmar", guji_prop_Myanmar, 3},
	{"N", guji_prop_N, 137},
	{"Nabataean", guji_prop_Nabataean, 2},
	{"Nag_Mundari", guji_prop_Nag_Mundari, 1},
	{"Nandinagari", guji_prop_Nandinagari, 3},
	{"Nd", guji_prop_Nd, 64},
	{"New_Tai_Lue", guji_prop_New_Tai_Lue, 4},
	{"Newa", guji_prop_Newa, 2},
	{"Nko", guji_prop_Nko, 2},
	{"Nl", guji_prop_Nl, 12},
	{"No", guji_prop_No, 72},
	{"Nushu", guji_prop_Nushu, 2},
	{"Nyiakeng_Puachue_Hmong", guji_prop_Nyiakeng_Puachue_Hmong, 4},
	{"Ogham", guji_prop_Ogham, 1},
	{"Ol_Chiki", guji_prop_Ol_Chiki, 1},
	{"Old_Hungarian", guji_prop_Old_Hungarian, 3},
	{"Old_Italic", guji_prop_Old_Italic, 2},
	{"Old_North_Arabian", guji_prop_Old_North_Arabian, 1},
	{"Old_Permic", guji_prop_Old_Permic, 1},
	{"Old_Persian", guji_prop_Old_Persian, 2},
	{"Old_Sogdian", guji_prop_Old_Sogdian, 1},
	{"Old_South_Arabian", guji_prop_Old_South_Arabian, 1},
	{"Old_Turkic", guji_prop_Old_Turkic, 1},
	{"Old_Uyghur", guji_prop_Old_Uyghur, 1},
	{"Oriya", guji_prop_Oriya, 14},
	{"Osage", guji_prop_Osage, 2},
	{"Osmanya", guji_prop_Osmanya, 2},
	{"P", guji_prop_P, 191},
	{"Pahawh_Hmong", guji_prop_Pahawh_Hmong, 5},
	{"Palmyrene", guji_prop_Palmyrene, 1},
	{"Pau_Cin_Hau", guji_prop_Pau_Cin_Hau, 1},
	{"Pc", guji_prop_Pc, 6},
	{"Pd", guji_prop_Pd, 19},
	{"Pe", guji_prop_Pe, 76},
	{"Pf", guji_prop_Pf, 10},
	{"Phags_Pa", guji_prop_Phags_Pa, 1},
	{"Phoenician", guji_prop_Phoenician, 2},
	{"Pi", guji_prop_Pi, 11},
	{"Po", guji_prop_Po, 187},
	{"Ps", guji_prop_Ps, 79},
	{"Psalter_Pahlavi", guji_prop_Psalter_Pahlavi, 3},
	{"Rejang", guji_prop_Rejang, 2},
	{"Runic", guji_prop_Runic, 2},
	{"S", guji_prop_S, 232},
	{"Samaritan", guji_prop_Samaritan, 2},
	{"Saurashtra", guji_prop_Saurashtra, 2},
	{"Sc", guji_prop_Sc, 21},
	{"Sharada", guji_prop_Sharada, 1},
	{"Shavian", guji_prop_Shavian, 1},
	{"Siddham", guji_prop_Siddham, 2},
	{"SignWriting", guji_prop_SignWriting, 3},
	{"Sinhala", guji_prop_Sinhala, 13},
	{"Sk", guji_prop_Sk, 31},
	{"Sm", guji_prop_Sm, 64},
	{"So", guji_prop_So, 184},
	{"Sogdian", guji_prop_Sogdian, 1},
	{"Sora_Sompeng", guji_prop_Sora_Sompeng, 2},
	{"Soyombo", guji_prop_Soyombo, 1},
	{"Sundanese", guji_prop_Sundanese, 2},
	{"Syloti_Nagri", guji_prop_Syloti_Nagri, 1},
	{"Syriac", guji_prop_Syriac, 4},
	{"Tagalog", guji_prop_Tagalog, 2},
	{"Tagbanwa", guji_prop_Tagbanwa, 3},
	{"Tai_Le", guji_prop_Tai_Le, 2},
	{"Tai_Tham", guji_prop_Tai_Tham, 5},
	{"Tai_Viet", guji_prop_Tai_Viet, 2},
	{"Takri", guji_prop_Takri, 2},
	{"Tamil", guji_prop_Tamil, 18},
	{"Tangsa", guji_prop_Tangsa, 2},
	{"Tangut", guji_prop_Tangut, 4},
	{"Telugu", guji_prop_Telugu, 13},
	{"Thaana", guji_prop_Thaana, 1},
	{"Thai", guji_prop_Thai, 2},
	{"Tibetan", guji_prop_Tibetan, 7},
	{"Tifinagh", guji_prop_Tifinagh, 3},
	{"Tirhuta", guji_prop_Tirhuta, 2},
	{"Toto", guji_prop_Toto, 1},
	{"Ugaritic", guji_prop_Ugaritic, 2},
	{"Uppercase", guji_prop_Uppercase, 651},
	{"Vai", guji_prop_Vai, 1},
	{"Vithkuqi", guji_prop_Vithkuqi, 8},
	{"Wancho", guji_prop_Wancho, 2},
	{"Warang_Citi", guji_prop_Warang_Citi, 2},
	{"White_Space", guji_prop_White_Space, 10},
	{"Yezidi", guji_prop_Yezidi, 3},
	{"Yi", guji_prop_Yi, 2},
	{"Z", guji_prop_Z, 8},
	{"Zanabazar_Square", guji_prop_Zanabazar_Square, 1},
	{"Zl", guji_prop_Zl, 1},
	{"Zp", guji_prop_Zp, 1},
	{"Zs", guji_prop_Zs, 7},
};
static const int32_t guji_unicode_property_count = 205;

/* Script names (canonical keys), for \p{Script=Name} scripts-only lookup. */
const char *const guji_unicode_script_names[] = {
	"Adlam", "Ahom", "Anatolian_Hieroglyphs", "Arabic", "Armenian", "Avestan", 
	"Balinese", "Bamum", "Bassa_Vah", "Batak", "Bengali", "Bhaiksuki", 
	"Bopomofo", "Brahmi", "Braille", "Buginese", "Buhid", "Canadian_Aboriginal", 
	"Carian", "Caucasian_Albanian", "Chakma", "Cham", "Cherokee", "Chorasmian", 
	"Common", "Coptic", "Cuneiform", "Cypriot", "Cypro_Minoan", "Cyrillic", 
	"Deseret", "Devanagari", "Dives_Akuru", "Dogra", "Duployan", "Egyptian_Hieroglyphs", 
	"Elbasan", "Elymaic", "Ethiopic", "Georgian", "Glagolitic", "Gothic", 
	"Grantha", "Greek", "Gujarati", "Gunjala_Gondi", "Gurmukhi", "Han", 
	"Hangul", "Hanifi_Rohingya", "Hanunoo", "Hatran", "Hebrew", "Hiragana", 
	"Imperial_Aramaic", "Inherited", "Inscriptional_Pahlavi", "Inscriptional_Parthian", "Javanese", "Kaithi", 
	"Kannada", "Katakana", "Kawi", "Kayah_Li", "Kharoshthi", "Khitan_Small_Script", 
	"Khmer", "Khojki", "Khudawadi", "Lao", "Latin", "Lepcha", 
	"Limbu", "Linear_A", "Linear_B", "Lisu", "Lycian", "Lydian", 
	"Mahajani", "Makasar", "Malayalam", "Mandaic", "Manichaean", "Marchen", 
	"Masaram_Gondi", "Medefaidrin", "Meetei_Mayek", "Mende_Kikakui", "Meroitic_Cursive", "Meroitic_Hieroglyphs", 
	"Miao", "Modi", "Mongolian", "Mro", "Multani", "Myanmar", 
	"Nabataean", "Nag_Mundari", "Nandinagari", "New_Tai_Lue", "Newa", "Nko", 
	"Nushu", "Nyiakeng_Puachue_Hmong", "Ogham", "Ol_Chiki", "Old_Hungarian", "Old_Italic", 
	"Old_North_Arabian", "Old_Permic", "Old_Persian", "Old_Sogdian", "Old_South_Arabian", "Old_Turkic", 
	"Old_Uyghur", "Oriya", "Osage", "Osmanya", "Pahawh_Hmong", "Palmyrene", 
	"Pau_Cin_Hau", "Phags_Pa", "Phoenician", "Psalter_Pahlavi", "Rejang", "Runic", 
	"Samaritan", "Saurashtra", "Sharada", "Shavian", "Siddham", "SignWriting", 
	"Sinhala", "Sogdian", "Sora_Sompeng", "Soyombo", "Sundanese", "Syloti_Nagri", 
	"Syriac", "Tagalog", "Tagbanwa", "Tai_Le", "Tai_Tham", "Tai_Viet", 
	"Takri", "Tamil", "Tangsa", "Tangut", "Telugu", "Thaana", 
	"Thai", "Tibetan", "Tifinagh", "Tirhuta", "Toto", "Ugaritic", 
	"Vai", "Vithkuqi", "Wancho", "Warang_Citi", "Yezidi", "Yi", 
	"Zanabazar_Square", 
};
const int32_t guji_unicode_script_name_count = 163;

const guji_rune_range_t guji_word_ranges[] = {
	{0x0030, 0x0039}, {0x0041, 0x005A}, {0x005F, 0x005F}, {0x0061, 0x007A}, 
	{0x00AA, 0x00AA}, {0x00B5, 0x00B5}, {0x00BA, 0x00BA}, {0x00C0, 0x00D6}, 
	{0x00D8, 0x00F6}, {0x00F8, 0x02C1}, {0x02C6, 0x02D1}, {0x02E0, 0x02E4}, 
	{0x02EC, 0x02EC}, {0x02EE, 0x02EE}, {0x0300, 0x0374}, {0x0376, 0x0377}, 
	{0x037A, 0x037D}, {0x037F, 0x037F}, {0x0386, 0x0386}, {0x0388, 0x038A}, 
	{0x038C, 0x038C}, {0x038E, 0x03A1}, {0x03A3, 0x03F5}, {0x03F7, 0x0481}, 
	{0x0483, 0x052F}, {0x0531, 0x0556}, {0x0559, 0x0559}, {0x0560, 0x0588}, 
	{0x0591, 0x05BD}, {0x05BF, 0x05BF}, {0x05C1, 0x05C2}, {0x05C4, 0x05C5}, 
	{0x05C7, 0x05C7}, {0x05D0, 0x05EA}, {0x05EF, 0x05F2}, {0x0610, 0x061A}, 
	{0x0620, 0x0669}, {0x066E, 0x06D3}, {0x06D5, 0x06DC}, {0x06DF, 0x06E8}, 
	{0x06EA, 0x06FC}, {0x06FF, 0x06FF}, {0x0710, 0x074A}, {0x074D, 0x07B1}, 
	{0x07C0, 0x07F5}, {0x07FA, 0x07FA}, {0x07FD, 0x07FD}, {0x0800, 0x082D}, 
	{0x0840, 0x085B}, {0x0860, 0x086A}, {0x0870, 0x0887}, {0x0889, 0x088E}, 
	{0x0898, 0x08E1}, {0x08E3, 0x0963}, {0x0966, 0x096F}, {0x0971, 0x0983}, 
	{0x0985, 0x098C}, {0x098F, 0x0990}, {0x0993, 0x09A8}, {0x09AA, 0x09B0}, 
	{0x09B2, 0x09B2}, {0x09B6, 0x09B9}, {0x09BC, 0x09C4}, {0x09C7, 0x09C8}, 
	{0x09CB, 0x09CE}, {0x09D7, 0x09D7}, {0x09DC, 0x09DD}, {0x09DF, 0x09E3}, 
	{0x09E6, 0x09F1}, {0x09FC, 0x09FC}, {0x09FE, 0x09FE}, {0x0A01, 0x0A03}, 
	{0x0A05, 0x0A0A}, {0x0A0F, 0x0A10}, {0x0A13, 0x0A28}, {0x0A2A, 0x0A30}, 
	{0x0A32, 0x0A33}, {0x0A35, 0x0A36}, {0x0A38, 0x0A39}, {0x0A3C, 0x0A3C}, 
	{0x0A3E, 0x0A42}, {0x0A47, 0x0A48}, {0x0A4B, 0x0A4D}, {0x0A51, 0x0A51}, 
	{0x0A59, 0x0A5C}, {0x0A5E, 0x0A5E}, {0x0A66, 0x0A75}, {0x0A81, 0x0A83}, 
	{0x0A85, 0x0A8D}, {0x0A8F, 0x0A91}, {0x0A93, 0x0AA8}, {0x0AAA, 0x0AB0}, 
	{0x0AB2, 0x0AB3}, {0x0AB5, 0x0AB9}, {0x0ABC, 0x0AC5}, {0x0AC7, 0x0AC9}, 
	{0x0ACB, 0x0ACD}, {0x0AD0, 0x0AD0}, {0x0AE0, 0x0AE3}, {0x0AE6, 0x0AEF}, 
	{0x0AF9, 0x0AFF}, {0x0B01, 0x0B03}, {0x0B05, 0x0B0C}, {0x0B0F, 0x0B10}, 
	{0x0B13, 0x0B28}, {0x0B2A, 0x0B30}, {0x0B32, 0x0B33}, {0x0B35, 0x0B39}, 
	{0x0B3C, 0x0B44}, {0x0B47, 0x0B48}, {0x0B4B, 0x0B4D}, {0x0B55, 0x0B57}, 
	{0x0B5C, 0x0B5D}, {0x0B5F, 0x0B63}, {0x0B66, 0x0B6F}, {0x0B71, 0x0B71}, 
	{0x0B82, 0x0B83}, {0x0B85, 0x0B8A}, {0x0B8E, 0x0B90}, {0x0B92, 0x0B95}, 
	{0x0B99, 0x0B9A}, {0x0B9C, 0x0B9C}, {0x0B9E, 0x0B9F}, {0x0BA3, 0x0BA4}, 
	{0x0BA8, 0x0BAA}, {0x0BAE, 0x0BB9}, {0x0BBE, 0x0BC2}, {0x0BC6, 0x0BC8}, 
	{0x0BCA, 0x0BCD}, {0x0BD0, 0x0BD0}, {0x0BD7, 0x0BD7}, {0x0BE6, 0x0BEF}, 
	{0x0C00, 0x0C0C}, {0x0C0E, 0x0C10}, {0x0C12, 0x0C28}, {0x0C2A, 0x0C39}, 
	{0x0C3C, 0x0C44}, {0x0C46, 0x0C48}, {0x0C4A, 0x0C4D}, {0x0C55, 0x0C56}, 
	{0x0C58, 0x0C5A}, {0x0C5D, 0x0C5D}, {0x0C60, 0x0C63}, {0x0C66, 0x0C6F}, 
	{0x0C80, 0x0C83}, {0x0C85, 0x0C8C}, {0x0C8E, 0x0C90}, {0x0C92, 0x0CA8}, 
	{0x0CAA, 0x0CB3}, {0x0CB5, 0x0CB9}, {0x0CBC, 0x0CC4}, {0x0CC6, 0x0CC8}, 
	{0x0CCA, 0x0CCD}, {0x0CD5, 0x0CD6}, {0x0CDD, 0x0CDE}, {0x0CE0, 0x0CE3}, 
	{0x0CE6, 0x0CEF}, {0x0CF1, 0x0CF3}, {0x0D00, 0x0D0C}, {0x0D0E, 0x0D10}, 
	{0x0D12, 0x0D44}, {0x0D46, 0x0D48}, {0x0D4A, 0x0D4E}, {0x0D54, 0x0D57}, 
	{0x0D5F, 0x0D63}, {0x0D66, 0x0D6F}, {0x0D7A, 0x0D7F}, {0x0D81, 0x0D83}, 
	{0x0D85, 0x0D96}, {0x0D9A, 0x0DB1}, {0x0DB3, 0x0DBB}, {0x0DBD, 0x0DBD}, 
	{0x0DC0, 0x0DC6}, {0x0DCA, 0x0DCA}, {0x0DCF, 0x0DD4}, {0x0DD6, 0x0DD6}, 
	{0x0DD8, 0x0DDF}, {0x0DE6, 0x0DEF}, {0x0DF2, 0x0DF3}, {0x0E01, 0x0E3A}, 
	{0x0E40, 0x0E4E}, {0x0E50, 0x0E59}, {0x0E81, 0x0E82}, {0x0E84, 0x0E84}, 
	{0x0E86, 0x0E8A}, {0x0E8C, 0x0EA3}, {0x0EA5, 0x0EA5}, {0x0EA7, 0x0EBD}, 
	{0x0EC0, 0x0EC4}, {0x0EC6, 0x0EC6}, {0x0EC8, 0x0ECE}, {0x0ED0, 0x0ED9}, 
	{0x0EDC, 0x0EDF}, {0x0F00, 0x0F00}, {0x0F18, 0x0F19}, {0x0F20, 0x0F29}, 
	{0x0F35, 0x0F35}, {0x0F37, 0x0F37}, {0x0F39, 0x0F39}, {0x0F3E, 0x0F47}, 
	{0x0F49, 0x0F6C}, {0x0F71, 0x0F84}, {0x0F86, 0x0F97}, {0x0F99, 0x0FBC}, 
	{0x0FC6, 0x0FC6}, {0x1000, 0x1049}, {0x1050, 0x109D}, {0x10A0, 0x10C5}, 
	{0x10C7, 0x10C7}, {0x10CD, 0x10CD}, {0x10D0, 0x10FA}, {0x10FC, 0x1248}, 
	{0x124A, 0x124D}, {0x1250, 0x1256}, {0x1258, 0x1258}, {0x125A, 0x125D}, 
	{0x1260, 0x1288}, {0x128A, 0x128D}, {0x1290, 0x12B0}, {0x12B2, 0x12B5}, 
	{0x12B8, 0x12BE}, {0x12C0, 0x12C0}, {0x12C2, 0x12C5}, {0x12C8, 0x12D6}, 
	{0x12D8, 0x1310}, {0x1312, 0x1315}, {0x1318, 0x135A}, {0x135D, 0x135F}, 
	{0x1380, 0x138F}, {0x13A0, 0x13F5}, {0x13F8, 0x13FD}, {0x1401, 0x166C}, 
	{0x166F, 0x167F}, {0x1681, 0x169A}, {0x16A0, 0x16EA}, {0x16EE, 0x16F8}, 
	{0x1700, 0x1715}, {0x171F, 0x1734}, {0x1740, 0x1753}, {0x1760, 0x176C}, 
	{0x176E, 0x1770}, {0x1772, 0x1773}, {0x1780, 0x17D3}, {0x17D7, 0x17D7}, 
	{0x17DC, 0x17DD}, {0x17E0, 0x17E9}, {0x180B, 0x180D}, {0x180F, 0x1819}, 
	{0x1820, 0x1878}, {0x1880, 0x18AA}, {0x18B0, 0x18F5}, {0x1900, 0x191E}, 
	{0x1920, 0x192B}, {0x1930, 0x193B}, {0x1946, 0x196D}, {0x1970, 0x1974}, 
	{0x1980, 0x19AB}, {0x19B0, 0x19C9}, {0x19D0, 0x19D9}, {0x1A00, 0x1A1B}, 
	{0x1A20, 0x1A5E}, {0x1A60, 0x1A7C}, {0x1A7F, 0x1A89}, {0x1A90, 0x1A99}, 
	{0x1AA7, 0x1AA7}, {0x1AB0, 0x1ACE}, {0x1B00, 0x1B4C}, {0x1B50, 0x1B59}, 
	{0x1B6B, 0x1B73}, {0x1B80, 0x1BF3}, {0x1C00, 0x1C37}, {0x1C40, 0x1C49}, 
	{0x1C4D, 0x1C7D}, {0x1C80, 0x1C88}, {0x1C90, 0x1CBA}, {0x1CBD, 0x1CBF}, 
	{0x1CD0, 0x1CD2}, {0x1CD4, 0x1CFA}, {0x1D00, 0x1F15}, {0x1F18, 0x1F1D}, 
	{0x1F20, 0x1F45}, {0x1F48, 0x1F4D}, {0x1F50, 0x1F57}, {0x1F59, 0x1F59}, 
	{0x1F5B, 0x1F5B}, {0x1F5D, 0x1F5D}, {0x1F5F, 0x1F7D}, {0x1F80, 0x1FB4}, 
	{0x1FB6, 0x1FBC}, {0x1FBE, 0x1FBE}, {0x1FC2, 0x1FC4}, {0x1FC6, 0x1FCC}, 
	{0x1FD0, 0x1FD3}, {0x1FD6, 0x1FDB}, {0x1FE0, 0x1FEC}, {0x1FF2, 0x1FF4}, 
	{0x1FF6, 0x1FFC}, {0x203F, 0x2040}, {0x2054, 0x2054}, {0x2071, 0x2071}, 
	{0x207F, 0x207F}, {0x2090, 0x209C}, {0x20D0, 0x20F0}, {0x2102, 0x2102}, 
	{0x2107, 0x2107}, {0x210A, 0x2113}, {0x2115, 0x2115}, {0x2119, 0x211D}, 
	{0x2124, 0x2124}, {0x2126, 0x2126}, {0x2128, 0x2128}, {0x212A, 0x212D}, 
	{0x212F, 0x2139}, {0x213C, 0x213F}, {0x2145, 0x2149}, {0x214E, 0x214E}, 
	{0x2160, 0x2188}, {0x24B6, 0x24E9}, {0x2C00, 0x2CE4}, {0x2CEB, 0x2CF3}, 
	{0x2D00, 0x2D25}, {0x2D27, 0x2D27}, {0x2D2D, 0x2D2D}, {0x2D30, 0x2D67}, 
	{0x2D6F, 0x2D6F}, {0x2D7F, 0x2D96}, {0x2DA0, 0x2DA6}, {0x2DA8, 0x2DAE}, 
	{0x2DB0, 0x2DB6}, {0x2DB8, 0x2DBE}, {0x2DC0, 0x2DC6}, {0x2DC8, 0x2DCE}, 
	{0x2DD0, 0x2DD6}, {0x2DD8, 0x2DDE}, {0x2DE0, 0x2DFF}, {0x2E2F, 0x2E2F}, 
	{0x3005, 0x3007}, {0x3021, 0x302F}, {0x3031, 0x3035}, {0x3038, 0x303C}, 
	{0x3041, 0x3096}, {0x3099, 0x309A}, {0x309D, 0x309F}, {0x30A1, 0x30FA}, 
	{0x30FC, 0x30FF}, {0x3105, 0x312F}, {0x3131, 0x318E}, {0x31A0, 0x31BF}, 
	{0x31F0, 0x31FF}, {0x3400, 0x4DBF}, {0x4E00, 0xA48C}, {0xA4D0, 0xA4FD}, 
	{0xA500, 0xA60C}, {0xA610, 0xA62B}, {0xA640, 0xA672}, {0xA674, 0xA67D}, 
	{0xA67F, 0xA6F1}, {0xA717, 0xA71F}, {0xA722, 0xA788}, {0xA78B, 0xA7CA}, 
	{0xA7D0, 0xA7D1}, {0xA7D3, 0xA7D3}, {0xA7D5, 0xA7D9}, {0xA7F2, 0xA827}, 
	{0xA82C, 0xA82C}, {0xA840, 0xA873}, {0xA880, 0xA8C5}, {0xA8D0, 0xA8D9}, 
	{0xA8E0, 0xA8F7}, {0xA8FB, 0xA8FB}, {0xA8FD, 0xA92D}, {0xA930, 0xA953}, 
	{0xA960, 0xA97C}, {0xA980, 0xA9C0}, {0xA9CF, 0xA9D9}, {0xA9E0, 0xA9FE}, 
	{0xAA00, 0xAA36}, {0xAA40, 0xAA4D}, {0xAA50, 0xAA59}, {0xAA60, 0xAA76}, 
	{0xAA7A, 0xAAC2}, {0xAADB, 0xAADD}, {0xAAE0, 0xAAEF}, {0xAAF2, 0xAAF6}, 
	{0xAB01, 0xAB06}, {0xAB09, 0xAB0E}, {0xAB11, 0xAB16}, {0xAB20, 0xAB26}, 
	{0xAB28, 0xAB2E}, {0xAB30, 0xAB5A}, {0xAB5C, 0xAB69}, {0xAB70, 0xABEA}, 
	{0xABEC, 0xABED}, {0xABF0, 0xABF9}, {0xAC00, 0xD7A3}, {0xD7B0, 0xD7C6}, 
	{0xD7CB, 0xD7FB}, {0xF900, 0xFA6D}, {0xFA70, 0xFAD9}, {0xFB00, 0xFB06}, 
	{0xFB13, 0xFB17}, {0xFB1D, 0xFB28}, {0xFB2A, 0xFB36}, {0xFB38, 0xFB3C}, 
	{0xFB3E, 0xFB3E}, {0xFB40, 0xFB41}, {0xFB43, 0xFB44}, {0xFB46, 0xFBB1}, 
	{0xFBD3, 0xFD3D}, {0xFD50, 0xFD8F}, {0xFD92, 0xFDC7}, {0xFDF0, 0xFDFB}, 
	{0xFE00, 0xFE0F}, {0xFE20, 0xFE2F}, {0xFE33, 0xFE34}, {0xFE4D, 0xFE4F}, 
	{0xFE70, 0xFE74}, {0xFE76, 0xFEFC}, {0xFF10, 0xFF19}, {0xFF21, 0xFF3A}, 
	{0xFF3F, 0xFF3F}, {0xFF41, 0xFF5A}, {0xFF66, 0xFFBE}, {0xFFC2, 0xFFC7}, 
	{0xFFCA, 0xFFCF}, {0xFFD2, 0xFFD7}, {0xFFDA, 0xFFDC}, {0x10000, 0x1000B}, 
	{0x1000D, 0x10026}, {0x10028, 0x1003A}, {0x1003C, 0x1003D}, {0x1003F, 0x1004D}, 
	{0x10050, 0x1005D}, {0x10080, 0x100FA}, {0x10140, 0x10174}, {0x101FD, 0x101FD}, 
	{0x10280, 0x1029C}, {0x102A0, 0x102D0}, {0x102E0, 0x102E0}, {0x10300, 0x1031F}, 
	{0x1032D, 0x1034A}, {0x10350, 0x1037A}, {0x10380, 0x1039D}, {0x103A0, 0x103C3}, 
	{0x103C8, 0x103CF}, {0x103D1, 0x103D5}, {0x10400, 0x1049D}, {0x104A0, 0x104A9}, 
	{0x104B0, 0x104D3}, {0x104D8, 0x104FB}, {0x10500, 0x10527}, {0x10530, 0x10563}, 
	{0x10570, 0x1057A}, {0x1057C, 0x1058A}, {0x1058C, 0x10592}, {0x10594, 0x10595}, 
	{0x10597, 0x105A1}, {0x105A3, 0x105B1}, {0x105B3, 0x105B9}, {0x105BB, 0x105BC}, 
	{0x10600, 0x10736}, {0x10740, 0x10755}, {0x10760, 0x10767}, {0x10780, 0x10785}, 
	{0x10787, 0x107B0}, {0x107B2, 0x107BA}, {0x10800, 0x10805}, {0x10808, 0x10808}, 
	{0x1080A, 0x10835}, {0x10837, 0x10838}, {0x1083C, 0x1083C}, {0x1083F, 0x10855}, 
	{0x10860, 0x10876}, {0x10880, 0x1089E}, {0x108E0, 0x108F2}, {0x108F4, 0x108F5}, 
	{0x10900, 0x10915}, {0x10920, 0x10939}, {0x10980, 0x109B7}, {0x109BE, 0x109BF}, 
	{0x10A00, 0x10A03}, {0x10A05, 0x10A06}, {0x10A0C, 0x10A13}, {0x10A15, 0x10A17}, 
	{0x10A19, 0x10A35}, {0x10A38, 0x10A3A}, {0x10A3F, 0x10A3F}, {0x10A60, 0x10A7C}, 
	{0x10A80, 0x10A9C}, {0x10AC0, 0x10AC7}, {0x10AC9, 0x10AE6}, {0x10B00, 0x10B35}, 
	{0x10B40, 0x10B55}, {0x10B60, 0x10B72}, {0x10B80, 0x10B91}, {0x10C00, 0x10C48}, 
	{0x10C80, 0x10CB2}, {0x10CC0, 0x10CF2}, {0x10D00, 0x10D27}, {0x10D30, 0x10D39}, 
	{0x10E80, 0x10EA9}, {0x10EAB, 0x10EAC}, {0x10EB0, 0x10EB1}, {0x10EFD, 0x10F1C}, 
	{0x10F27, 0x10F27}, {0x10F30, 0x10F50}, {0x10F70, 0x10F85}, {0x10FB0, 0x10FC4}, 
	{0x10FE0, 0x10FF6}, {0x11000, 0x11046}, {0x11066, 0x11075}, {0x1107F, 0x110BA}, 
	{0x110C2, 0x110C2}, {0x110D0, 0x110E8}, {0x110F0, 0x110F9}, {0x11100, 0x11134}, 
	{0x11136, 0x1113F}, {0x11144, 0x11147}, {0x11150, 0x11173}, {0x11176, 0x11176}, 
	{0x11180, 0x111C4}, {0x111C9, 0x111CC}, {0x111CE, 0x111DA}, {0x111DC, 0x111DC}, 
	{0x11200, 0x11211}, {0x11213, 0x11237}, {0x1123E, 0x11241}, {0x11280, 0x11286}, 
	{0x11288, 0x11288}, {0x1128A, 0x1128D}, {0x1128F, 0x1129D}, {0x1129F, 0x112A8}, 
	{0x112B0, 0x112EA}, {0x112F0, 0x112F9}, {0x11300, 0x11303}, {0x11305, 0x1130C}, 
	{0x1130F, 0x11310}, {0x11313, 0x11328}, {0x1132A, 0x11330}, {0x11332, 0x11333}, 
	{0x11335, 0x11339}, {0x1133B, 0x11344}, {0x11347, 0x11348}, {0x1134B, 0x1134D}, 
	{0x11350, 0x11350}, {0x11357, 0x11357}, {0x1135D, 0x11363}, {0x11366, 0x1136C}, 
	{0x11370, 0x11374}, {0x11400, 0x1144A}, {0x11450, 0x11459}, {0x1145E, 0x11461}, 
	{0x11480, 0x114C5}, {0x114C7, 0x114C7}, {0x114D0, 0x114D9}, {0x11580, 0x115B5}, 
	{0x115B8, 0x115C0}, {0x115D8, 0x115DD}, {0x11600, 0x11640}, {0x11644, 0x11644}, 
	{0x11650, 0x11659}, {0x11680, 0x116B8}, {0x116C0, 0x116C9}, {0x11700, 0x1171A}, 
	{0x1171D, 0x1172B}, {0x11730, 0x11739}, {0x11740, 0x11746}, {0x11800, 0x1183A}, 
	{0x118A0, 0x118E9}, {0x118FF, 0x11906}, {0x11909, 0x11909}, {0x1190C, 0x11913}, 
	{0x11915, 0x11916}, {0x11918, 0x11935}, {0x11937, 0x11938}, {0x1193B, 0x11943}, 
	{0x11950, 0x11959}, {0x119A0, 0x119A7}, {0x119AA, 0x119D7}, {0x119DA, 0x119E1}, 
	{0x119E3, 0x119E4}, {0x11A00, 0x11A3E}, {0x11A47, 0x11A47}, {0x11A50, 0x11A99}, 
	{0x11A9D, 0x11A9D}, {0x11AB0, 0x11AF8}, {0x11C00, 0x11C08}, {0x11C0A, 0x11C36}, 
	{0x11C38, 0x11C40}, {0x11C50, 0x11C59}, {0x11C72, 0x11C8F}, {0x11C92, 0x11CA7}, 
	{0x11CA9, 0x11CB6}, {0x11D00, 0x11D06}, {0x11D08, 0x11D09}, {0x11D0B, 0x11D36}, 
	{0x11D3A, 0x11D3A}, {0x11D3C, 0x11D3D}, {0x11D3F, 0x11D47}, {0x11D50, 0x11D59}, 
	{0x11D60, 0x11D65}, {0x11D67, 0x11D68}, {0x11D6A, 0x11D8E}, {0x11D90, 0x11D91}, 
	{0x11D93, 0x11D98}, {0x11DA0, 0x11DA9}, {0x11EE0, 0x11EF6}, {0x11F00, 0x11F10}, 
	{0x11F12, 0x11F3A}, {0x11F3E, 0x11F42}, {0x11F50, 0x11F59}, {0x11FB0, 0x11FB0}, 
	{0x12000, 0x12399}, {0x12400, 0x1246E}, {0x12480, 0x12543}, {0x12F90, 0x12FF0}, 
	{0x13000, 0x1342F}, {0x13440, 0x13455}, {0x14400, 0x14646}, {0x16800, 0x16A38}, 
	{0x16A40, 0x16A5E}, {0x16A60, 0x16A69}, {0x16A70, 0x16ABE}, {0x16AC0, 0x16AC9}, 
	{0x16AD0, 0x16AED}, {0x16AF0, 0x16AF4}, {0x16B00, 0x16B36}, {0x16B40, 0x16B43}, 
	{0x16B50, 0x16B59}, {0x16B63, 0x16B77}, {0x16B7D, 0x16B8F}, {0x16E40, 0x16E7F}, 
	{0x16F00, 0x16F4A}, {0x16F4F, 0x16F87}, {0x16F8F, 0x16F9F}, {0x16FE0, 0x16FE1}, 
	{0x16FE3, 0x16FE4}, {0x16FF0, 0x16FF1}, {0x17000, 0x187F7}, {0x18800, 0x18CD5}, 
	{0x18D00, 0x18D08}, {0x1AFF0, 0x1AFF3}, {0x1AFF5, 0x1AFFB}, {0x1AFFD, 0x1AFFE}, 
	{0x1B000, 0x1B122}, {0x1B132, 0x1B132}, {0x1B150, 0x1B152}, {0x1B155, 0x1B155}, 
	{0x1B164, 0x1B167}, {0x1B170, 0x1B2FB}, {0x1BC00, 0x1BC6A}, {0x1BC70, 0x1BC7C}, 
	{0x1BC80, 0x1BC88}, {0x1BC90, 0x1BC99}, {0x1BC9D, 0x1BC9E}, {0x1CF00, 0x1CF2D}, 
	{0x1CF30, 0x1CF46}, {0x1D165, 0x1D169}, {0x1D16D, 0x1D172}, {0x1D17B, 0x1D182}, 
	{0x1D185, 0x1D18B}, {0x1D1AA, 0x1D1AD}, {0x1D242, 0x1D244}, {0x1D400, 0x1D454}, 
	{0x1D456, 0x1D49C}, {0x1D49E, 0x1D49F}, {0x1D4A2, 0x1D4A2}, {0x1D4A5, 0x1D4A6}, 
	{0x1D4A9, 0x1D4AC}, {0x1D4AE, 0x1D4B9}, {0x1D4BB, 0x1D4BB}, {0x1D4BD, 0x1D4C3}, 
	{0x1D4C5, 0x1D505}, {0x1D507, 0x1D50A}, {0x1D50D, 0x1D514}, {0x1D516, 0x1D51C}, 
	{0x1D51E, 0x1D539}, {0x1D53B, 0x1D53E}, {0x1D540, 0x1D544}, {0x1D546, 0x1D546}, 
	{0x1D54A, 0x1D550}, {0x1D552, 0x1D6A5}, {0x1D6A8, 0x1D6C0}, {0x1D6C2, 0x1D6DA}, 
	{0x1D6DC, 0x1D6FA}, {0x1D6FC, 0x1D714}, {0x1D716, 0x1D734}, {0x1D736, 0x1D74E}, 
	{0x1D750, 0x1D76E}, {0x1D770, 0x1D788}, {0x1D78A, 0x1D7A8}, {0x1D7AA, 0x1D7C2}, 
	{0x1D7C4, 0x1D7CB}, {0x1D7CE, 0x1D7FF}, {0x1DA00, 0x1DA36}, {0x1DA3B, 0x1DA6C}, 
	{0x1DA75, 0x1DA75}, {0x1DA84, 0x1DA84}, {0x1DA9B, 0x1DA9F}, {0x1DAA1, 0x1DAAF}, 
	{0x1DF00, 0x1DF1E}, {0x1DF25, 0x1DF2A}, {0x1E000, 0x1E006}, {0x1E008, 0x1E018}, 
	{0x1E01B, 0x1E021}, {0x1E023, 0x1E024}, {0x1E026, 0x1E02A}, {0x1E030, 0x1E06D}, 
	{0x1E08F, 0x1E08F}, {0x1E100, 0x1E12C}, {0x1E130, 0x1E13D}, {0x1E140, 0x1E149}, 
	{0x1E14E, 0x1E14E}, {0x1E290, 0x1E2AE}, {0x1E2C0, 0x1E2F9}, {0x1E4D0, 0x1E4F9}, 
	{0x1E7E0, 0x1E7E6}, {0x1E7E8, 0x1E7EB}, {0x1E7ED, 0x1E7EE}, {0x1E7F0, 0x1E7FE}, 
	{0x1E800, 0x1E8C4}, {0x1E8D0, 0x1E8D6}, {0x1E900, 0x1E94B}, {0x1E950, 0x1E959}, 
	{0x1EE00, 0x1EE03}, {0x1EE05, 0x1EE1F}, {0x1EE21, 0x1EE22}, {0x1EE24, 0x1EE24}, 
	{0x1EE27, 0x1EE27}, {0x1EE29, 0x1EE32}, {0x1EE34, 0x1EE37}, {0x1EE39, 0x1EE39}, 
	{0x1EE3B, 0x1EE3B}, {0x1EE42, 0x1EE42}, {0x1EE47, 0x1EE47}, {0x1EE49, 0x1EE49}, 
	{0x1EE4B, 0x1EE4B}, {0x1EE4D, 0x1EE4F}, {0x1EE51, 0x1EE52}, {0x1EE54, 0x1EE54}, 
	{0x1EE57, 0x1EE57}, {0x1EE59, 0x1EE59}, {0x1EE5B, 0x1EE5B}, {0x1EE5D, 0x1EE5D}, 
	{0x1EE5F, 0x1EE5F}, {0x1EE61, 0x1EE62}, {0x1EE64, 0x1EE64}, {0x1EE67, 0x1EE6A}, 
	{0x1EE6C, 0x1EE72}, {0x1EE74, 0x1EE77}, {0x1EE79, 0x1EE7C}, {0x1EE7E, 0x1EE7E}, 
	{0x1EE80, 0x1EE89}, {0x1EE8B, 0x1EE9B}, {0x1EEA1, 0x1EEA3}, {0x1EEA5, 0x1EEA9}, 
	{0x1EEAB, 0x1EEBB}, {0x1F130, 0x1F149}, {0x1F150, 0x1F169}, {0x1F170, 0x1F189}, 
	{0x1FBF0, 0x1FBF9}, {0x20000, 0x2A6DF}, {0x2A700, 0x2B739}, {0x2B740, 0x2B81D}, 
	{0x2B820, 0x2CEA1}, {0x2CEB0, 0x2EBE0}, {0x2F800, 0x2FA1D}, {0x30000, 0x3134A}, 
	{0x31350, 0x323AF}, {0xE0100, 0xE01EF}, 
};
const int32_t guji_word_range_count = 770;

static const guji_fold_pair_t guji_fold_pairs[] = {
	{0x0041, 0x0061}, {0x0042, 0x0062}, {0x0043, 0x0063}, {0x0044, 0x0064}, 
	{0x0045, 0x0065}, {0x0046, 0x0066}, {0x0047, 0x0067}, {0x0048, 0x0068}, 
	{0x0049, 0x0069}, {0x004A, 0x006A}, {0x004B, 0x006B}, {0x004C, 0x006C}, 
	{0x004D, 0x006D}, {0x004E, 0x006E}, {0x004F, 0x006F}, {0x0050, 0x0070}, 
	{0x0051, 0x0071}, {0x0052, 0x0072}, {0x0053, 0x0073}, {0x0054, 0x0074}, 
	{0x0055, 0x0075}, {0x0056, 0x0076}, {0x0057, 0x0077}, {0x0058, 0x0078}, 
	{0x0059, 0x0079}, {0x005A, 0x007A}, {0x0061, 0x0041}, {0x0062, 0x0042}, 
	{0x0063, 0x0043}, {0x0064, 0x0044}, {0x0065, 0x0045}, {0x0066, 0x0046}, 
	{0x0067, 0x0047}, {0x0068, 0x0048}, {0x0069, 0x0049}, {0x006A, 0x004A}, 
	{0x006B, 0x212A}, {0x006C, 0x004C}, {0x006D, 0x004D}, {0x006E, 0x004E}, 
	{0x006F, 0x004F}, {0x0070, 0x0050}, {0x0071, 0x0051}, {0x0072, 0x0052}, 
	{0x0073, 0x017F}, {0x0074, 0x0054}, {0x0075, 0x0055}, {0x0076, 0x0056}, 
	{0x0077, 0x0057}, {0x0078, 0x0058}, {0x0079, 0x0059}, {0x007A, 0x005A}, 
	{0x00B5, 0x039C}, {0x00C0, 0x00E0}, {0x00C1, 0x00E1}, {0x00C2, 0x00E2}, 
	{0x00C3, 0x00E3}, {0x00C4, 0x00E4}, {0x00C5, 0x00E5}, {0x00C6, 0x00E6}, 
	{0x00C7, 0x00E7}, {0x00C8, 0x00E8}, {0x00C9, 0x00E9}, {0x00CA, 0x00EA}, 
	{0x00CB, 0x00EB}, {0x00CC, 0x00EC}, {0x00CD, 0x00ED}, {0x00CE, 0x00EE}, 
	{0x00CF, 0x00EF}, {0x00D0, 0x00F0}, {0x00D1, 0x00F1}, {0x00D2, 0x00F2}, 
	{0x00D3, 0x00F3}, {0x00D4, 0x00F4}, {0x00D5, 0x00F5}, {0x00D6, 0x00F6}, 
	{0x00D8, 0x00F8}, {0x00D9, 0x00F9}, {0x00DA, 0x00FA}, {0x00DB, 0x00FB}, 
	{0x00DC, 0x00FC}, {0x00DD, 0x00FD}, {0x00DE, 0x00FE}, {0x00DF, 0x1E9E}, 
	{0x00E0, 0x00C0}, {0x00E1, 0x00C1}, {0x00E2, 0x00C2}, {0x00E3, 0x00C3}, 
	{0x00E4, 0x00C4}, {0x00E5, 0x212B}, {0x00E6, 0x00C6}, {0x00E7, 0x00C7}, 
	{0x00E8, 0x00C8}, {0x00E9, 0x00C9}, {0x00EA, 0x00CA}, {0x00EB, 0x00CB}, 
	{0x00EC, 0x00CC}, {0x00ED, 0x00CD}, {0x00EE, 0x00CE}, {0x00EF, 0x00CF}, 
	{0x00F0, 0x00D0}, {0x00F1, 0x00D1}, {0x00F2, 0x00D2}, {0x00F3, 0x00D3}, 
	{0x00F4, 0x00D4}, {0x00F5, 0x00D5}, {0x00F6, 0x00D6}, {0x00F8, 0x00D8}, 
	{0x00F9, 0x00D9}, {0x00FA, 0x00DA}, {0x00FB, 0x00DB}, {0x00FC, 0x00DC}, 
	{0x00FD, 0x00DD}, {0x00FE, 0x00DE}, {0x00FF, 0x0178}, {0x0100, 0x0101}, 
	{0x0101, 0x0100}, {0x0102, 0x0103}, {0x0103, 0x0102}, {0x0104, 0x0105}, 
	{0x0105, 0x0104}, {0x0106, 0x0107}, {0x0107, 0x0106}, {0x0108, 0x0109}, 
	{0x0109, 0x0108}, {0x010A, 0x010B}, {0x010B, 0x010A}, {0x010C, 0x010D}, 
	{0x010D, 0x010C}, {0x010E, 0x010F}, {0x010F, 0x010E}, {0x0110, 0x0111}, 
	{0x0111, 0x0110}, {0x0112, 0x0113}, {0x0113, 0x0112}, {0x0114, 0x0115}, 
	{0x0115, 0x0114}, {0x0116, 0x0117}, {0x0117, 0x0116}, {0x0118, 0x0119}, 
	{0x0119, 0x0118}, {0x011A, 0x011B}, {0x011B, 0x011A}, {0x011C, 0x011D}, 
	{0x011D, 0x011C}, {0x011E, 0x011F}, {0x011F, 0x011E}, {0x0120, 0x0121}, 
	{0x0121, 0x0120}, {0x0122, 0x0123}, {0x0123, 0x0122}, {0x0124, 0x0125}, 
	{0x0125, 0x0124}, {0x0126, 0x0127}, {0x0127, 0x0126}, {0x0128, 0x0129}, 
	{0x0129, 0x0128}, {0x012A, 0x012B}, {0x012B, 0x012A}, {0x012C, 0x012D}, 
	{0x012D, 0x012C}, {0x012E, 0x012F}, {0x012F, 0x012E}, {0x0132, 0x0133}, 
	{0x0133, 0x0132}, {0x0134, 0x0135}, {0x0135, 0x0134}, {0x0136, 0x0137}, 
	{0x0137, 0x0136}, {0x0139, 0x013A}, {0x013A, 0x0139}, {0x013B, 0x013C}, 
	{0x013C, 0x013B}, {0x013D, 0x013E}, {0x013E, 0x013D}, {0x013F, 0x0140}, 
	{0x0140, 0x013F}, {0x0141, 0x0142}, {0x0142, 0x0141}, {0x0143, 0x0144}, 
	{0x0144, 0x0143}, {0x0145, 0x0146}, {0x0146, 0x0145}, {0x0147, 0x0148}, 
	{0x0148, 0x0147}, {0x014A, 0x014B}, {0x014B, 0x014A}, {0x014C, 0x014D}, 
	{0x014D, 0x014C}, {0x014E, 0x014F}, {0x014F, 0x014E}, {0x0150, 0x0151}, 
	{0x0151, 0x0150}, {0x0152, 0x0153}, {0x0153, 0x0152}, {0x0154, 0x0155}, 
	{0x0155, 0x0154}, {0x0156, 0x0157}, {0x0157, 0x0156}, {0x0158, 0x0159}, 
	{0x0159, 0x0158}, {0x015A, 0x015B}, {0x015B, 0x015A}, {0x015C, 0x015D}, 
	{0x015D, 0x015C}, {0x015E, 0x015F}, {0x015F, 0x015E}, {0x0160, 0x0161}, 
	{0x0161, 0x0160}, {0x0162, 0x0163}, {0x0163, 0x0162}, {0x0164, 0x0165}, 
	{0x0165, 0x0164}, {0x0166, 0x0167}, {0x0167, 0x0166}, {0x0168, 0x0169}, 
	{0x0169, 0x0168}, {0x016A, 0x016B}, {0x016B, 0x016A}, {0x016C, 0x016D}, 
	{0x016D, 0x016C}, {0x016E, 0x016F}, {0x016F, 0x016E}, {0x0170, 0x0171}, 
	{0x0171, 0x0170}, {0x0172, 0x0173}, {0x0173, 0x0172}, {0x0174, 0x0175}, 
	{0x0175, 0x0174}, {0x0176, 0x0177}, {0x0177, 0x0176}, {0x0178, 0x00FF}, 
	{0x0179, 0x017A}, {0x017A, 0x0179}, {0x017B, 0x017C}, {0x017C, 0x017B}, 
	{0x017D, 0x017E}, {0x017E, 0x017D}, {0x017F, 0x0053}, {0x0180, 0x0243}, 
	{0x0181, 0x0253}, {0x0182, 0x0183}, {0x0183, 0x0182}, {0x0184, 0x0185}, 
	{0x0185, 0x0184}, {0x0186, 0x0254}, {0x0187, 0x0188}, {0x0188, 0x0187}, 
	{0x0189, 0x0256}, {0x018A, 0x0257}, {0x018B, 0x018C}, {0x018C, 0x018B}, 
	{0x018E, 0x01DD}, {0x018F, 0x0259}, {0x0190, 0x025B}, {0x0191, 0x0192}, 
	{0x0192, 0x0191}, {0x0193, 0x0260}, {0x0194, 0x0263}, {0x0195, 0x01F6}, 
	{0x0196, 0x0269}, {0x0197, 0x0268}, {0x0198, 0x0199}, {0x0199, 0x0198}, 
	{0x019A, 0x023D}, {0x019C, 0x026F}, {0x019D, 0x0272}, {0x019E, 0x0220}, 
	{0x019F, 0x0275}, {0x01A0, 0x01A1}, {0x01A1, 0x01A0}, {0x01A2, 0x01A3}, 
	{0x01A3, 0x01A2}, {0x01A4, 0x01A5}, {0x01A5, 0x01A4}, {0x01A6, 0x0280}, 
	{0x01A7, 0x01A8}, {0x01A8, 0x01A7}, {0x01A9, 0x0283}, {0x01AC, 0x01AD}, 
	{0x01AD, 0x01AC}, {0x01AE, 0x0288}, {0x01AF, 0x01B0}, {0x01B0, 0x01AF}, 
	{0x01B1, 0x028A}, {0x01B2, 0x028B}, {0x01B3, 0x01B4}, {0x01B4, 0x01B3}, 
	{0x01B5, 0x01B6}, {0x01B6, 0x01B5}, {0x01B7, 0x0292}, {0x01B8, 0x01B9}, 
	{0x01B9, 0x01B8}, {0x01BC, 0x01BD}, {0x01BD, 0x01BC}, {0x01BF, 0x01F7}, 
	{0x01C4, 0x01C5}, {0x01C5, 0x01C6}, {0x01C6, 0x01C4}, {0x01C7, 0x01C8}, 
	{0x01C8, 0x01C9}, {0x01C9, 0x01C7}, {0x01CA, 0x01CB}, {0x01CB, 0x01CC}, 
	{0x01CC, 0x01CA}, {0x01CD, 0x01CE}, {0x01CE, 0x01CD}, {0x01CF, 0x01D0}, 
	{0x01D0, 0x01CF}, {0x01D1, 0x01D2}, {0x01D2, 0x01D1}, {0x01D3, 0x01D4}, 
	{0x01D4, 0x01D3}, {0x01D5, 0x01D6}, {0x01D6, 0x01D5}, {0x01D7, 0x01D8}, 
	{0x01D8, 0x01D7}, {0x01D9, 0x01DA}, {0x01DA, 0x01D9}, {0x01DB, 0x01DC}, 
	{0x01DC, 0x01DB}, {0x01DD, 0x018E}, {0x01DE, 0x01DF}, {0x01DF, 0x01DE}, 
	{0x01E0, 0x01E1}, {0x01E1, 0x01E0}, {0x01E2, 0x01E3}, {0x01E3, 0x01E2}, 
	{0x01E4, 0x01E5}, {0x01E5, 0x01E4}, {0x01E6, 0x01E7}, {0x01E7, 0x01E6}, 
	{0x01E8, 0x01E9}, {0x01E9, 0x01E8}, {0x01EA, 0x01EB}, {0x01EB, 0x01EA}, 
	{0x01EC, 0x01ED}, {0x01ED, 0x01EC}, {0x01EE, 0x01EF}, {0x01EF, 0x01EE}, 
	{0x01F1, 0x01F2}, {0x01F2, 0x01F3}, {0x01F3, 0x01F1}, {0x01F4, 0x01F5}, 
	{0x01F5, 0x01F4}, {0x01F6, 0x0195}, {0x01F7, 0x01BF}, {0x01F8, 0x01F9}, 
	{0x01F9, 0x01F8}, {0x01FA, 0x01FB}, {0x01FB, 0x01FA}, {0x01FC, 0x01FD}, 
	{0x01FD, 0x01FC}, {0x01FE, 0x01FF}, {0x01FF, 0x01FE}, {0x0200, 0x0201}, 
	{0x0201, 0x0200}, {0x0202, 0x0203}, {0x0203, 0x0202}, {0x0204, 0x0205}, 
	{0x0205, 0x0204}, {0x0206, 0x0207}, {0x0207, 0x0206}, {0x0208, 0x0209}, 
	{0x0209, 0x0208}, {0x020A, 0x020B}, {0x020B, 0x020A}, {0x020C, 0x020D}, 
	{0x020D, 0x020C}, {0x020E, 0x020F}, {0x020F, 0x020E}, {0x0210, 0x0211}, 
	{0x0211, 0x0210}, {0x0212, 0x0213}, {0x0213, 0x0212}, {0x0214, 0x0215}, 
	{0x0215, 0x0214}, {0x0216, 0x0217}, {0x0217, 0x0216}, {0x0218, 0x0219}, 
	{0x0219, 0x0218}, {0x021A, 0x021B}, {0x021B, 0x021A}, {0x021C, 0x021D}, 
	{0x021D, 0x021C}, {0x021E, 0x021F}, {0x021F, 0x021E}, {0x0220, 0x019E}, 
	{0x0222, 0x0223}, {0x0223, 0x0222}, {0x0224, 0x0225}, {0x0225, 0x0224}, 
	{0x0226, 0x0227}, {0x0227, 0x0226}, {0x0228, 0x0229}, {0x0229, 0x0228}, 
	{0x022A, 0x022B}, {0x022B, 0x022A}, {0x022C, 0x022D}, {0x022D, 0x022C}, 
	{0x022E, 0x022F}, {0x022F, 0x022E}, {0x0230, 0x0231}, {0x0231, 0x0230}, 
	{0x0232, 0x0233}, {0x0233, 0x0232}, {0x023A, 0x2C65}, {0x023B, 0x023C}, 
	{0x023C, 0x023B}, {0x023D, 0x019A}, {0x023E, 0x2C66}, {0x023F, 0x2C7E}, 
	{0x0240, 0x2C7F}, {0x0241, 0x0242}, {0x0242, 0x0241}, {0x0243, 0x0180}, 
	{0x0244, 0x0289}, {0x0245, 0x028C}, {0x0246, 0x0247}, {0x0247, 0x0246}, 
	{0x0248, 0x0249}, {0x0249, 0x0248}, {0x024A, 0x024B}, {0x024B, 0x024A}, 
	{0x024C, 0x024D}, {0x024D, 0x024C}, {0x024E, 0x024F}, {0x024F, 0x024E}, 
	{0x0250, 0x2C6F}, {0x0251, 0x2C6D}, {0x0252, 0x2C70}, {0x0253, 0x0181}, 
	{0x0254, 0x0186}, {0x0256, 0x0189}, {0x0257, 0x018A}, {0x0259, 0x018F}, 
	{0x025B, 0x0190}, {0x025C, 0xA7AB}, {0x0260, 0x0193}, {0x0261, 0xA7AC}, 
	{0x0263, 0x0194}, {0x0265, 0xA78D}, {0x0266, 0xA7AA}, {0x0268, 0x0197}, 
	{0x0269, 0x0196}, {0x026A, 0xA7AE}, {0x026B, 0x2C62}, {0x026C, 0xA7AD}, 
	{0x026F, 0x019C}, {0x0271, 0x2C6E}, {0x0272, 0x019D}, {0x0275, 0x019F}, 
	{0x027D, 0x2C64}, {0x0280, 0x01A6}, {0x0282, 0xA7C5}, {0x0283, 0x01A9}, 
	{0x0287, 0xA7B1}, {0x0288, 0x01AE}, {0x0289, 0x0244}, {0x028A, 0x01B1}, 
	{0x028B, 0x01B2}, {0x028C, 0x0245}, {0x0292, 0x01B7}, {0x029D, 0xA7B2}, 
	{0x029E, 0xA7B0}, {0x0345, 0x0399}, {0x0370, 0x0371}, {0x0371, 0x0370}, 
	{0x0372, 0x0373}, {0x0373, 0x0372}, {0x0376, 0x0377}, {0x0377, 0x0376}, 
	{0x037B, 0x03FD}, {0x037C, 0x03FE}, {0x037D, 0x03FF}, {0x037F, 0x03F3}, 
	{0x0386, 0x03AC}, {0x0388, 0x03AD}, {0x0389, 0x03AE}, {0x038A, 0x03AF}, 
	{0x038C, 0x03CC}, {0x038E, 0x03CD}, {0x038F, 0x03CE}, {0x0391, 0x03B1}, 
	{0x0392, 0x03B2}, {0x0393, 0x03B3}, {0x0394, 0x03B4}, {0x0395, 0x03B5}, 
	{0x0396, 0x03B6}, {0x0397, 0x03B7}, {0x0398, 0x03B8}, {0x0399, 0x03B9}, 
	{0x039A, 0x03BA}, {0x039B, 0x03BB}, {0x039C, 0x03BC}, {0x039D, 0x03BD}, 
	{0x039E, 0x03BE}, {0x039F, 0x03BF}, {0x03A0, 0x03C0}, {0x03A1, 0x03C1}, 
	{0x03A3, 0x03C2}, {0x03A4, 0x03C4}, {0x03A5, 0x03C5}, {0x03A6, 0x03C6}, 
	{0x03A7, 0x03C7}, {0x03A8, 0x03C8}, {0x03A9, 0x03C9}, {0x03AA, 0x03CA}, 
	{0x03AB, 0x03CB}, {0x03AC, 0x0386}, {0x03AD, 0x0388}, {0x03AE, 0x0389}, 
	{0x03AF, 0x038A}, {0x03B1, 0x0391}, {0x03B2, 0x03D0}, {0x03B3, 0x0393}, 
	{0x03B4, 0x0394}, {0x03B5, 0x03F5}, {0x03B6, 0x0396}, {0x03B7, 0x0397}, 
	{0x03B8, 0x03D1}, {0x03B9, 0x1FBE}, {0x03BA, 0x03F0}, {0x03BB, 0x039B}, 
	{0x03BC, 0x00B5}, {0x03BD, 0x039D}, {0x03BE, 0x039E}, {0x03BF, 0x039F}, 
	{0x03C0, 0x03D6}, {0x03C1, 0x03F1}, {0x03C2, 0x03C3}, {0x03C3, 0x03A3}, 
	{0x03C4, 0x03A4}, {0x03C5, 0x03A5}, {0x03C6, 0x03D5}, {0x03C7, 0x03A7}, 
	{0x03C8, 0x03A8}, {0x03C9, 0x2126}, {0x03CA, 0x03AA}, {0x03CB, 0x03AB}, 
	{0x03CC, 0x038C}, {0x03CD, 0x038E}, {0x03CE, 0x038F}, {0x03CF, 0x03D7}, 
	{0x03D0, 0x0392}, {0x03D1, 0x03F4}, {0x03D5, 0x03A6}, {0x03D6, 0x03A0}, 
	{0x03D7, 0x03CF}, {0x03D8, 0x03D9}, {0x03D9, 0x03D8}, {0x03DA, 0x03DB}, 
	{0x03DB, 0x03DA}, {0x03DC, 0x03DD}, {0x03DD, 0x03DC}, {0x03DE, 0x03DF}, 
	{0x03DF, 0x03DE}, {0x03E0, 0x03E1}, {0x03E1, 0x03E0}, {0x03E2, 0x03E3}, 
	{0x03E3, 0x03E2}, {0x03E4, 0x03E5}, {0x03E5, 0x03E4}, {0x03E6, 0x03E7}, 
	{0x03E7, 0x03E6}, {0x03E8, 0x03E9}, {0x03E9, 0x03E8}, {0x03EA, 0x03EB}, 
	{0x03EB, 0x03EA}, {0x03EC, 0x03ED}, {0x03ED, 0x03EC}, {0x03EE, 0x03EF}, 
	{0x03EF, 0x03EE}, {0x03F0, 0x039A}, {0x03F1, 0x03A1}, {0x03F2, 0x03F9}, 
	{0x03F3, 0x037F}, {0x03F4, 0x0398}, {0x03F5, 0x0395}, {0x03F7, 0x03F8}, 
	{0x03F8, 0x03F7}, {0x03F9, 0x03F2}, {0x03FA, 0x03FB}, {0x03FB, 0x03FA}, 
	{0x03FD, 0x037B}, {0x03FE, 0x037C}, {0x03FF, 0x037D}, {0x0400, 0x0450}, 
	{0x0401, 0x0451}, {0x0402, 0x0452}, {0x0403, 0x0453}, {0x0404, 0x0454}, 
	{0x0405, 0x0455}, {0x0406, 0x0456}, {0x0407, 0x0457}, {0x0408, 0x0458}, 
	{0x0409, 0x0459}, {0x040A, 0x045A}, {0x040B, 0x045B}, {0x040C, 0x045C}, 
	{0x040D, 0x045D}, {0x040E, 0x045E}, {0x040F, 0x045F}, {0x0410, 0x0430}, 
	{0x0411, 0x0431}, {0x0412, 0x0432}, {0x0413, 0x0433}, {0x0414, 0x0434}, 
	{0x0415, 0x0435}, {0x0416, 0x0436}, {0x0417, 0x0437}, {0x0418, 0x0438}, 
	{0x0419, 0x0439}, {0x041A, 0x043A}, {0x041B, 0x043B}, {0x041C, 0x043C}, 
	{0x041D, 0x043D}, {0x041E, 0x043E}, {0x041F, 0x043F}, {0x0420, 0x0440}, 
	{0x0421, 0x0441}, {0x0422, 0x0442}, {0x0423, 0x0443}, {0x0424, 0x0444}, 
	{0x0425, 0x0445}, {0x0426, 0x0446}, {0x0427, 0x0447}, {0x0428, 0x0448}, 
	{0x0429, 0x0449}, {0x042A, 0x044A}, {0x042B, 0x044B}, {0x042C, 0x044C}, 
	{0x042D, 0x044D}, {0x042E, 0x044E}, {0x042F, 0x044F}, {0x0430, 0x0410}, 
	{0x0431, 0x0411}, {0x0432, 0x1C80}, {0x0433, 0x0413}, {0x0434, 0x1C81}, 
	{0x0435, 0x0415}, {0x0436, 0x0416}, {0x0437, 0x0417}, {0x0438, 0x0418}, 
	{0x0439, 0x0419}, {0x043A, 0x041A}, {0x043B, 0x041B}, {0x043C, 0x041C}, 
	{0x043D, 0x041D}, {0x043E, 0x1C82}, {0x043F, 0x041F}, {0x0440, 0x0420}, 
	{0x0441, 0x1C83}, {0x0442, 0x1C84}, {0x0443, 0x0423}, {0x0444, 0x0424}, 
	{0x0445, 0x0425}, {0x0446, 0x0426}, {0x0447, 0x0427}, {0x0448, 0x0428}, 
	{0x0449, 0x0429}, {0x044A, 0x1C86}, {0x044B, 0x042B}, {0x044C, 0x042C}, 
	{0x044D, 0x042D}, {0x044E, 0x042E}, {0x044F, 0x042F}, {0x0450, 0x0400}, 
	{0x0451, 0x0401}, {0x0452, 0x0402}, {0x0453, 0x0403}, {0x0454, 0x0404}, 
	{0x0455, 0x0405}, {0x0456, 0x0406}, {0x0457, 0x0407}, {0x0458, 0x0408}, 
	{0x0459, 0x0409}, {0x045A, 0x040A}, {0x045B, 0x040B}, {0x045C, 0x040C}, 
	{0x045D, 0x040D}, {0x045E, 0x040E}, {0x045F, 0x040F}, {0x0460, 0x0461}, 
	{0x0461, 0x0460}, {0x0462, 0x0463}, {0x0463, 0x1C87}, {0x0464, 0x0465}, 
	{0x0465, 0x0464}, {0x0466, 0x0467}, {0x0467, 0x0466}, {0x0468, 0x0469}, 
	{0x0469, 0x0468}, {0x046A, 0x046B}, {0x046B, 0x046A}, {0x046C, 0x046D}, 
	{0x046D, 0x046C}, {0x046E, 0x046F}, {0x046F, 0x046E}, {0x0470, 0x0471}, 
	{0x0471, 0x0470}, {0x0472, 0x0473}, {0x0473, 0x0472}, {0x0474, 0x0475}, 
	{0x0475, 0x0474}, {0x0476, 0x0477}, {0x0477, 0x0476}, {0x0478, 0x0479}, 
	{0x0479, 0x0478}, {0x047A, 0x047B}, {0x047B, 0x047A}, {0x047C, 0x047D}, 
	{0x047D, 0x047C}, {0x047E, 0x047F}, {0x047F, 0x047E}, {0x0480, 0x0481}, 
	{0x0481, 0x0480}, {0x048A, 0x048B}, {0x048B, 0x048A}, {0x048C, 0x048D}, 
	{0x048D, 0x048C}, {0x048E, 0x048F}, {0x048F, 0x048E}, {0x0490, 0x0491}, 
	{0x0491, 0x0490}, {0x0492, 0x0493}, {0x0493, 0x0492}, {0x0494, 0x0495}, 
	{0x0495, 0x0494}, {0x0496, 0x0497}, {0x0497, 0x0496}, {0x0498, 0x0499}, 
	{0x0499, 0x0498}, {0x049A, 0x049B}, {0x049B, 0x049A}, {0x049C, 0x049D}, 
	{0x049D, 0x049C}, {0x049E, 0x049F}, {0x049F, 0x049E}, {0x04A0, 0x04A1}, 
	{0x04A1, 0x04A0}, {0x04A2, 0x04A3}, {0x04A3, 0x04A2}, {0x04A4, 0x04A5}, 
	{0x04A5, 0x04A4}, {0x04A6, 0x04A7}, {0x04A7, 0x04A6}, {0x04A8, 0x04A9}, 
	{0x04A9, 0x04A8}, {0x04AA, 0x04AB}, {0x04AB, 0x04AA}, {0x04AC, 0x04AD}, 
	{0x04AD, 0x04AC}, {0x04AE, 0x04AF}, {0x04AF, 0x04AE}, {0x04B0, 0x04B1}, 
	{0x04B1, 0x04B0}, {0x04B2, 0x04B3}, {0x04B3, 0x04B2}, {0x04B4, 0x04B5}, 
	{0x04B5, 0x04B4}, {0x04B6, 0x04B7}, {0x04B7, 0x04B6}, {0x04B8, 0x04B9}, 
	{0x04B9, 0x04B8}, {0x04BA, 0x04BB}, {0x04BB, 0x04BA}, {0x04BC, 0x04BD}, 
	{0x04BD, 0x04BC}, {0x04BE, 0x04BF}, {0x04BF, 0x04BE}, {0x04C0, 0x04CF}, 
	{0x04C1, 0x04C2}, {0x04C2, 0x04C1}, {0x04C3, 0x04C4}, {0x04C4, 0x04C3}, 
	{0x04C5, 0x04C6}, {0x04C6, 0x04C5}, {0x04C7, 0x04C8}, {0x04C8, 0x04C7}, 
	{0x04C9, 0x04CA}, {0x04CA, 0x04C9}, {0x04CB, 0x04CC}, {0x04CC, 0x04CB}, 
	{0x04CD, 0x04CE}, {0x04CE, 0x04CD}, {0x04CF, 0x04C0}, {0x04D0, 0x04D1}, 
	{0x04D1, 0x04D0}, {0x04D2, 0x04D3}, {0x04D3, 0x04D2}, {0x04D4, 0x04D5}, 
	{0x04D5, 0x04D4}, {0x04D6, 0x04D7}, {0x04D7, 0x04D6}, {0x04D8, 0x04D9}, 
	{0x04D9, 0x04D8}, {0x04DA, 0x04DB}, {0x04DB, 0x04DA}, {0x04DC, 0x04DD}, 
	{0x04DD, 0x04DC}, {0x04DE, 0x04DF}, {0x04DF, 0x04DE}, {0x04E0, 0x04E1}, 
	{0x04E1, 0x04E0}, {0x04E2, 0x04E3}, {0x04E3, 0x04E2}, {0x04E4, 0x04E5}, 
	{0x04E5, 0x04E4}, {0x04E6, 0x04E7}, {0x04E7, 0x04E6}, {0x04E8, 0x04E9}, 
	{0x04E9, 0x04E8}, {0x04EA, 0x04EB}, {0x04EB, 0x04EA}, {0x04EC, 0x04ED}, 
	{0x04ED, 0x04EC}, {0x04EE, 0x04EF}, {0x04EF, 0x04EE}, {0x04F0, 0x04F1}, 
	{0x04F1, 0x04F0}, {0x04F2, 0x04F3}, {0x04F3, 0x04F2}, {0x04F4, 0x04F5}, 
	{0x04F5, 0x04F4}, {0x04F6, 0x04F7}, {0x04F7, 0x04F6}, {0x04F8, 0x04F9}, 
	{0x04F9, 0x04F8}, {0x04FA, 0x04FB}, {0x04FB, 0x04FA}, {0x04FC, 0x04FD}, 
	{0x04FD, 0x04FC}, {0x04FE, 0x04FF}, {0x04FF, 0x04FE}, {0x0500, 0x0501}, 
	{0x0501, 0x0500}, {0x0502, 0x0503}, {0x0503, 0x0502}, {0x0504, 0x0505}, 
	{0x0505, 0x0504}, {0x0506, 0x0507}, {0x0507, 0x0506}, {0x0508, 0x0509}, 
	{0x0509, 0x0508}, {0x050A, 0x050B}, {0x050B, 0x050A}, {0x050C, 0x050D}, 
	{0x050D, 0x050C}, {0x050E, 0x050F}, {0x050F, 0x050E}, {0x0510, 0x0511}, 
	{0x0511, 0x0510}, {0x0512, 0x0513}, {0x0513, 0x0512}, {0x0514, 0x0515}, 
	{0x0515, 0x0514}, {0x0516, 0x0517}, {0x0517, 0x0516}, {0x0518, 0x0519}, 
	{0x0519, 0x0518}, {0x051A, 0x051B}, {0x051B, 0x051A}, {0x051C, 0x051D}, 
	{0x051D, 0x051C}, {0x051E, 0x051F}, {0x051F, 0x051E}, {0x0520, 0x0521}, 
	{0x0521, 0x0520}, {0x0522, 0x0523}, {0x0523, 0x0522}, {0x0524, 0x0525}, 
	{0x0525, 0x0524}, {0x0526, 0x0527}, {0x0527, 0x0526}, {0x0528, 0x0529}, 
	{0x0529, 0x0528}, {0x052A, 0x052B}, {0x052B, 0x052A}, {0x052C, 0x052D}, 
	{0x052D, 0x052C}, {0x052E, 0x052F}, {0x052F, 0x052E}, {0x0531, 0x0561}, 
	{0x0532, 0x0562}, {0x0533, 0x0563}, {0x0534, 0x0564}, {0x0535, 0x0565}, 
	{0x0536, 0x0566}, {0x0537, 0x0567}, {0x0538, 0x0568}, {0x0539, 0x0569}, 
	{0x053A, 0x056A}, {0x053B, 0x056B}, {0x053C, 0x056C}, {0x053D, 0x056D}, 
	{0x053E, 0x056E}, {0x053F, 0x056F}, {0x0540, 0x0570}, {0x0541, 0x0571}, 
	{0x0542, 0x0572}, {0x0543, 0x0573}, {0x0544, 0x0574}, {0x0545, 0x0575}, 
	{0x0546, 0x0576}, {0x0547, 0x0577}, {0x0548, 0x0578}, {0x0549, 0x0579}, 
	{0x054A, 0x057A}, {0x054B, 0x057B}, {0x054C, 0x057C}, {0x054D, 0x057D}, 
	{0x054E, 0x057E}, {0x054F, 0x057F}, {0x0550, 0x0580}, {0x0551, 0x0581}, 
	{0x0552, 0x0582}, {0x0553, 0x0583}, {0x0554, 0x0584}, {0x0555, 0x0585}, 
	{0x0556, 0x0586}, {0x0561, 0x0531}, {0x0562, 0x0532}, {0x0563, 0x0533}, 
	{0x0564, 0x0534}, {0x0565, 0x0535}, {0x0566, 0x0536}, {0x0567, 0x0537}, 
	{0x0568, 0x0538}, {0x0569, 0x0539}, {0x056A, 0x053A}, {0x056B, 0x053B}, 
	{0x056C, 0x053C}, {0x056D, 0x053D}, {0x056E, 0x053E}, {0x056F, 0x053F}, 
	{0x0570, 0x0540}, {0x0571, 0x0541}, {0x0572, 0x0542}, {0x0573, 0x0543}, 
	{0x0574, 0x0544}, {0x0575, 0x0545}, {0x0576, 0x0546}, {0x0577, 0x0547}, 
	{0x0578, 0x0548}, {0x0579, 0x0549}, {0x057A, 0x054A}, {0x057B, 0x054B}, 
	{0x057C, 0x054C}, {0x057D, 0x054D}, {0x057E, 0x054E}, {0x057F, 0x054F}, 
	{0x0580, 0x0550}, {0x0581, 0x0551}, {0x0582, 0x0552}, {0x0583, 0x0553}, 
	{0x0584, 0x0554}, {0x0585, 0x0555}, {0x0586, 0x0556}, {0x10A0, 0x2D00}, 
	{0x10A1, 0x2D01}, {0x10A2, 0x2D02}, {0x10A3, 0x2D03}, {0x10A4, 0x2D04}, 
	{0x10A5, 0x2D05}, {0x10A6, 0x2D06}, {0x10A7, 0x2D07}, {0x10A8, 0x2D08}, 
	{0x10A9, 0x2D09}, {0x10AA, 0x2D0A}, {0x10AB, 0x2D0B}, {0x10AC, 0x2D0C}, 
	{0x10AD, 0x2D0D}, {0x10AE, 0x2D0E}, {0x10AF, 0x2D0F}, {0x10B0, 0x2D10}, 
	{0x10B1, 0x2D11}, {0x10B2, 0x2D12}, {0x10B3, 0x2D13}, {0x10B4, 0x2D14}, 
	{0x10B5, 0x2D15}, {0x10B6, 0x2D16}, {0x10B7, 0x2D17}, {0x10B8, 0x2D18}, 
	{0x10B9, 0x2D19}, {0x10BA, 0x2D1A}, {0x10BB, 0x2D1B}, {0x10BC, 0x2D1C}, 
	{0x10BD, 0x2D1D}, {0x10BE, 0x2D1E}, {0x10BF, 0x2D1F}, {0x10C0, 0x2D20}, 
	{0x10C1, 0x2D21}, {0x10C2, 0x2D22}, {0x10C3, 0x2D23}, {0x10C4, 0x2D24}, 
	{0x10C5, 0x2D25}, {0x10C7, 0x2D27}, {0x10CD, 0x2D2D}, {0x10D0, 0x1C90}, 
	{0x10D1, 0x1C91}, {0x10D2, 0x1C92}, {0x10D3, 0x1C93}, {0x10D4, 0x1C94}, 
	{0x10D5, 0x1C95}, {0x10D6, 0x1C96}, {0x10D7, 0x1C97}, {0x10D8, 0x1C98}, 
	{0x10D9, 0x1C99}, {0x10DA, 0x1C9A}, {0x10DB, 0x1C9B}, {0x10DC, 0x1C9C}, 
	{0x10DD, 0x1C9D}, {0x10DE, 0x1C9E}, {0x10DF, 0x1C9F}, {0x10E0, 0x1CA0}, 
	{0x10E1, 0x1CA1}, {0x10E2, 0x1CA2}, {0x10E3, 0x1CA3}, {0x10E4, 0x1CA4}, 
	{0x10E5, 0x1CA5}, {0x10E6, 0x1CA6}, {0x10E7, 0x1CA7}, {0x10E8, 0x1CA8}, 
	{0x10E9, 0x1CA9}, {0x10EA, 0x1CAA}, {0x10EB, 0x1CAB}, {0x10EC, 0x1CAC}, 
	{0x10ED, 0x1CAD}, {0x10EE, 0x1CAE}, {0x10EF, 0x1CAF}, {0x10F0, 0x1CB0}, 
	{0x10F1, 0x1CB1}, {0x10F2, 0x1CB2}, {0x10F3, 0x1CB3}, {0x10F4, 0x1CB4}, 
	{0x10F5, 0x1CB5}, {0x10F6, 0x1CB6}, {0x10F7, 0x1CB7}, {0x10F8, 0x1CB8}, 
	{0x10F9, 0x1CB9}, {0x10FA, 0x1CBA}, {0x10FD, 0x1CBD}, {0x10FE, 0x1CBE}, 
	{0x10FF, 0x1CBF}, {0x13A0, 0xAB70}, {0x13A1, 0xAB71}, {0x13A2, 0xAB72}, 
	{0x13A3, 0xAB73}, {0x13A4, 0xAB74}, {0x13A5, 0xAB75}, {0x13A6, 0xAB76}, 
	{0x13A7, 0xAB77}, {0x13A8, 0xAB78}, {0x13A9, 0xAB79}, {0x13AA, 0xAB7A}, 
	{0x13AB, 0xAB7B}, {0x13AC, 0xAB7C}, {0x13AD, 0xAB7D}, {0x13AE, 0xAB7E}, 
	{0x13AF, 0xAB7F}, {0x13B0, 0xAB80}, {0x13B1, 0xAB81}, {0x13B2, 0xAB82}, 
	{0x13B3, 0xAB83}, {0x13B4, 0xAB84}, {0x13B5, 0xAB85}, {0x13B6, 0xAB86}, 
	{0x13B7, 0xAB87}, {0x13B8, 0xAB88}, {0x13B9, 0xAB89}, {0x13BA, 0xAB8A}, 
	{0x13BB, 0xAB8B}, {0x13BC, 0xAB8C}, {0x13BD, 0xAB8D}, {0x13BE, 0xAB8E}, 
	{0x13BF, 0xAB8F}, {0x13C0, 0xAB90}, {0x13C1, 0xAB91}, {0x13C2, 0xAB92}, 
	{0x13C3, 0xAB93}, {0x13C4, 0xAB94}, {0x13C5, 0xAB95}, {0x13C6, 0xAB96}, 
	{0x13C7, 0xAB97}, {0x13C8, 0xAB98}, {0x13C9, 0xAB99}, {0x13CA, 0xAB9A}, 
	{0x13CB, 0xAB9B}, {0x13CC, 0xAB9C}, {0x13CD, 0xAB9D}, {0x13CE, 0xAB9E}, 
	{0x13CF, 0xAB9F}, {0x13D0, 0xABA0}, {0x13D1, 0xABA1}, {0x13D2, 0xABA2}, 
	{0x13D3, 0xABA3}, {0x13D4, 0xABA4}, {0x13D5, 0xABA5}, {0x13D6, 0xABA6}, 
	{0x13D7, 0xABA7}, {0x13D8, 0xABA8}, {0x13D9, 0xABA9}, {0x13DA, 0xABAA}, 
	{0x13DB, 0xABAB}, {0x13DC, 0xABAC}, {0x13DD, 0xABAD}, {0x13DE, 0xABAE}, 
	{0x13DF, 0xABAF}, {0x13E0, 0xABB0}, {0x13E1, 0xABB1}, {0x13E2, 0xABB2}, 
	{0x13E3, 0xABB3}, {0x13E4, 0xABB4}, {0x13E5, 0xABB5}, {0x13E6, 0xABB6}, 
	{0x13E7, 0xABB7}, {0x13E8, 0xABB8}, {0x13E9, 0xABB9}, {0x13EA, 0xABBA}, 
	{0x13EB, 0xABBB}, {0x13EC, 0xABBC}, {0x13ED, 0xABBD}, {0x13EE, 0xABBE}, 
	{0x13EF, 0xABBF}, {0x13F0, 0x13F8}, {0x13F1, 0x13F9}, {0x13F2, 0x13FA}, 
	{0x13F3, 0x13FB}, {0x13F4, 0x13FC}, {0x13F5, 0x13FD}, {0x13F8, 0x13F0}, 
	{0x13F9, 0x13F1}, {0x13FA, 0x13F2}, {0x13FB, 0x13F3}, {0x13FC, 0x13F4}, 
	{0x13FD, 0x13F5}, {0x1C80, 0x0412}, {0x1C81, 0x0414}, {0x1C82, 0x041E}, 
	{0x1C83, 0x0421}, {0x1C84, 0x1C85}, {0x1C85, 0x0422}, {0x1C86, 0x042A}, 
	{0x1C87, 0x0462}, {0x1C88, 0xA64A}, {0x1C90, 0x10D0}, {0x1C91, 0x10D1}, 
	{0x1C92, 0x10D2}, {0x1C93, 0x10D3}, {0x1C94, 0x10D4}, {0x1C95, 0x10D5}, 
	{0x1C96, 0x10D6}, {0x1C97, 0x10D7}, {0x1C98, 0x10D8}, {0x1C99, 0x10D9}, 
	{0x1C9A, 0x10DA}, {0x1C9B, 0x10DB}, {0x1C9C, 0x10DC}, {0x1C9D, 0x10DD}, 
	{0x1C9E, 0x10DE}, {0x1C9F, 0x10DF}, {0x1CA0, 0x10E0}, {0x1CA1, 0x10E1}, 
	{0x1CA2, 0x10E2}, {0x1CA3, 0x10E3}, {0x1CA4, 0x10E4}, {0x1CA5, 0x10E5}, 
	{0x1CA6, 0x10E6}, {0x1CA7, 0x10E7}, {0x1CA8, 0x10E8}, {0x1CA9, 0x10E9}, 
	{0x1CAA, 0x10EA}, {0x1CAB, 0x10EB}, {0x1CAC, 0x10EC}, {0x1CAD, 0x10ED}, 
	{0x1CAE, 0x10EE}, {0x1CAF, 0x10EF}, {0x1CB0, 0x10F0}, {0x1CB1, 0x10F1}, 
	{0x1CB2, 0x10F2}, {0x1CB3, 0x10F3}, {0x1CB4, 0x10F4}, {0x1CB5, 0x10F5}, 
	{0x1CB6, 0x10F6}, {0x1CB7, 0x10F7}, {0x1CB8, 0x10F8}, {0x1CB9, 0x10F9}, 
	{0x1CBA, 0x10FA}, {0x1CBD, 0x10FD}, {0x1CBE, 0x10FE}, {0x1CBF, 0x10FF}, 
	{0x1D79, 0xA77D}, {0x1D7D, 0x2C63}, {0x1D8E, 0xA7C6}, {0x1E00, 0x1E01}, 
	{0x1E01, 0x1E00}, {0x1E02, 0x1E03}, {0x1E03, 0x1E02}, {0x1E04, 0x1E05}, 
	{0x1E05, 0x1E04}, {0x1E06, 0x1E07}, {0x1E07, 0x1E06}, {0x1E08, 0x1E09}, 
	{0x1E09, 0x1E08}, {0x1E0A, 0x1E0B}, {0x1E0B, 0x1E0A}, {0x1E0C, 0x1E0D}, 
	{0x1E0D, 0x1E0C}, {0x1E0E, 0x1E0F}, {0x1E0F, 0x1E0E}, {0x1E10, 0x1E11}, 
	{0x1E11, 0x1E10}, {0x1E12, 0x1E13}, {0x1E13, 0x1E12}, {0x1E14, 0x1E15}, 
	{0x1E15, 0x1E14}, {0x1E16, 0x1E17}, {0x1E17, 0x1E16}, {0x1E18, 0x1E19}, 
	{0x1E19, 0x1E18}, {0x1E1A, 0x1E1B}, {0x1E1B, 0x1E1A}, {0x1E1C, 0x1E1D}, 
	{0x1E1D, 0x1E1C}, {0x1E1E, 0x1E1F}, {0x1E1F, 0x1E1E}, {0x1E20, 0x1E21}, 
	{0x1E21, 0x1E20}, {0x1E22, 0x1E23}, {0x1E23, 0x1E22}, {0x1E24, 0x1E25}, 
	{0x1E25, 0x1E24}, {0x1E26, 0x1E27}, {0x1E27, 0x1E26}, {0x1E28, 0x1E29}, 
	{0x1E29, 0x1E28}, {0x1E2A, 0x1E2B}, {0x1E2B, 0x1E2A}, {0x1E2C, 0x1E2D}, 
	{0x1E2D, 0x1E2C}, {0x1E2E, 0x1E2F}, {0x1E2F, 0x1E2E}, {0x1E30, 0x1E31}, 
	{0x1E31, 0x1E30}, {0x1E32, 0x1E33}, {0x1E33, 0x1E32}, {0x1E34, 0x1E35}, 
	{0x1E35, 0x1E34}, {0x1E36, 0x1E37}, {0x1E37, 0x1E36}, {0x1E38, 0x1E39}, 
	{0x1E39, 0x1E38}, {0x1E3A, 0x1E3B}, {0x1E3B, 0x1E3A}, {0x1E3C, 0x1E3D}, 
	{0x1E3D, 0x1E3C}, {0x1E3E, 0x1E3F}, {0x1E3F, 0x1E3E}, {0x1E40, 0x1E41}, 
	{0x1E41, 0x1E40}, {0x1E42, 0x1E43}, {0x1E43, 0x1E42}, {0x1E44, 0x1E45}, 
	{0x1E45, 0x1E44}, {0x1E46, 0x1E47}, {0x1E47, 0x1E46}, {0x1E48, 0x1E49}, 
	{0x1E49, 0x1E48}, {0x1E4A, 0x1E4B}, {0x1E4B, 0x1E4A}, {0x1E4C, 0x1E4D}, 
	{0x1E4D, 0x1E4C}, {0x1E4E, 0x1E4F}, {0x1E4F, 0x1E4E}, {0x1E50, 0x1E51}, 
	{0x1E51, 0x1E50}, {0x1E52, 0x1E53}, {0x1E53, 0x1E52}, {0x1E54, 0x1E55}, 
	{0x1E55, 0x1E54}, {0x1E56, 0x1E57}, {0x1E57, 0x1E56}, {0x1E58, 0x1E59}, 
	{0x1E59, 0x1E58}, {0x1E5A, 0x1E5B}, {0x1E5B, 0x1E5A}, {0x1E5C, 0x1E5D}, 
	{0x1E5D, 0x1E5C}, {0x1E5E, 0x1E5F}, {0x1E5F, 0x1E5E}, {0x1E60, 0x1E61}, 
	{0x1E61, 0x1E9B}, {0x1E62, 0x1E63}, {0x1E63, 0x1E62}, {0x1E64, 0x1E65}, 
	{0x1E65, 0x1E64}, {0x1E66, 0x1E67}, {0x1E67, 0x1E66}, {0x1E68, 0x1E69}, 
	{0x1E69, 0x1E68}, {0x1E6A, 0x1E6B}, {0x1E6B, 0x1E6A}, {0x1E6C, 0x1E6D}, 
	{0x1E6D, 0x1E6C}, {0x1E6E, 0x1E6F}, {0x1E6F, 0x1E6E}, {0x1E70, 0x1E71}, 
	{0x1E71, 0x1E70}, {0x1E72, 0x1E73}, {0x1E73, 0x1E72}, {0x1E74, 0x1E75}, 
	{0x1E75, 0x1E74}, {0x1E76, 0x1E77}, {0x1E77, 0x1E76}, {0x1E78, 0x1E79}, 
	{0x1E79, 0x1E78}, {0x1E7A, 0x1E7B}, {0x1E7B, 0x1E7A}, {0x1E7C, 0x1E7D}, 
	{0x1E7D, 0x1E7C}, {0x1E7E, 0x1E7F}, {0x1E7F, 0x1E7E}, {0x1E80, 0x1E81}, 
	{0x1E81, 0x1E80}, {0x1E82, 0x1E83}, {0x1E83, 0x1E82}, {0x1E84, 0x1E85}, 
	{0x1E85, 0x1E84}, {0x1E86, 0x1E87}, {0x1E87, 0x1E86}, {0x1E88, 0x1E89}, 
	{0x1E89, 0x1E88}, {0x1E8A, 0x1E8B}, {0x1E8B, 0x1E8A}, {0x1E8C, 0x1E8D}, 
	{0x1E8D, 0x1E8C}, {0x1E8E, 0x1E8F}, {0x1E8F, 0x1E8E}, {0x1E90, 0x1E91}, 
	{0x1E91, 0x1E90}, {0x1E92, 0x1E93}, {0x1E93, 0x1E92}, {0x1E94, 0x1E95}, 
	{0x1E95, 0x1E94}, {0x1E9B, 0x1E60}, {0x1E9E, 0x00DF}, {0x1EA0, 0x1EA1}, 
	{0x1EA1, 0x1EA0}, {0x1EA2, 0x1EA3}, {0x1EA3, 0x1EA2}, {0x1EA4, 0x1EA5}, 
	{0x1EA5, 0x1EA4}, {0x1EA6, 0x1EA7}, {0x1EA7, 0x1EA6}, {0x1EA8, 0x1EA9}, 
	{0x1EA9, 0x1EA8}, {0x1EAA, 0x1EAB}, {0x1EAB, 0x1EAA}, {0x1EAC, 0x1EAD}, 
	{0x1EAD, 0x1EAC}, {0x1EAE, 0x1EAF}, {0x1EAF, 0x1EAE}, {0x1EB0, 0x1EB1}, 
	{0x1EB1, 0x1EB0}, {0x1EB2, 0x1EB3}, {0x1EB3, 0x1EB2}, {0x1EB4, 0x1EB5}, 
	{0x1EB5, 0x1EB4}, {0x1EB6, 0x1EB7}, {0x1EB7, 0x1EB6}, {0x1EB8, 0x1EB9}, 
	{0x1EB9, 0x1EB8}, {0x1EBA, 0x1EBB}, {0x1EBB, 0x1EBA}, {0x1EBC, 0x1EBD}, 
	{0x1EBD, 0x1EBC}, {0x1EBE, 0x1EBF}, {0x1EBF, 0x1EBE}, {0x1EC0, 0x1EC1}, 
	{0x1EC1, 0x1EC0}, {0x1EC2, 0x1EC3}, {0x1EC3, 0x1EC2}, {0x1EC4, 0x1EC5}, 
	{0x1EC5, 0x1EC4}, {0x1EC6, 0x1EC7}, {0x1EC7, 0x1EC6}, {0x1EC8, 0x1EC9}, 
	{0x1EC9, 0x1EC8}, {0x1ECA, 0x1ECB}, {0x1ECB, 0x1ECA}, {0x1ECC, 0x1ECD}, 
	{0x1ECD, 0x1ECC}, {0x1ECE, 0x1ECF}, {0x1ECF, 0x1ECE}, {0x1ED0, 0x1ED1}, 
	{0x1ED1, 0x1ED0}, {0x1ED2, 0x1ED3}, {0x1ED3, 0x1ED2}, {0x1ED4, 0x1ED5}, 
	{0x1ED5, 0x1ED4}, {0x1ED6, 0x1ED7}, {0x1ED7, 0x1ED6}, {0x1ED8, 0x1ED9}, 
	{0x1ED9, 0x1ED8}, {0x1EDA, 0x1EDB}, {0x1EDB, 0x1EDA}, {0x1EDC, 0x1EDD}, 
	{0x1EDD, 0x1EDC}, {0x1EDE, 0x1EDF}, {0x1EDF, 0x1EDE}, {0x1EE0, 0x1EE1}, 
	{0x1EE1, 0x1EE0}, {0x1EE2, 0x1EE3}, {0x1EE3, 0x1EE2}, {0x1EE4, 0x1EE5}, 
	{0x1EE5, 0x1EE4}, {0x1EE6, 0x1EE7}, {0x1EE7, 0x1EE6}, {0x1EE8, 0x1EE9}, 
	{0x1EE9, 0x1EE8}, {0x1EEA, 0x1EEB}, {0x1EEB, 0x1EEA}, {0x1EEC, 0x1EED}, 
	{0x1EED, 0x1EEC}, {0x1EEE, 0x1EEF}, {0x1EEF, 0x1EEE}, {0x1EF0, 0x1EF1}, 
	{0x1EF1, 0x1EF0}, {0x1EF2, 0x1EF3}, {0x1EF3, 0x1EF2}, {0x1EF4, 0x1EF5}, 
	{0x1EF5, 0x1EF4}, {0x1EF6, 0x1EF7}, {0x1EF7, 0x1EF6}, {0x1EF8, 0x1EF9}, 
	{0x1EF9, 0x1EF8}, {0x1EFA, 0x1EFB}, {0x1EFB, 0x1EFA}, {0x1EFC, 0x1EFD}, 
	{0x1EFD, 0x1EFC}, {0x1EFE, 0x1EFF}, {0x1EFF, 0x1EFE}, {0x1F00, 0x1F08}, 
	{0x1F01, 0x1F09}, {0x1F02, 0x1F0A}, {0x1F03, 0x1F0B}, {0x1F04, 0x1F0C}, 
	{0x1F05, 0x1F0D}, {0x1F06, 0x1F0E}, {0x1F07, 0x1F0F}, {0x1F08, 0x1F00}, 
	{0x1F09, 0x1F01}, {0x1F0A, 0x1F02}, {0x1F0B, 0x1F03}, {0x1F0C, 0x1F04}, 
	{0x1F0D, 0x1F05}, {0x1F0E, 0x1F06}, {0x1F0F, 0x1F07}, {0x1F10, 0x1F18}, 
	{0x1F11, 0x1F19}, {0x1F12, 0x1F1A}, {0x1F13, 0x1F1B}, {0x1F14, 0x1F1C}, 
	{0x1F15, 0x1F1D}, {0x1F18, 0x1F10}, {0x1F19, 0x1F11}, {0x1F1A, 0x1F12}, 
	{0x1F1B, 0x1F13}, {0x1F1C, 0x1F14}, {0x1F1D, 0x1F15}, {0x1F20, 0x1F28}, 
	{0x1F21, 0x1F29}, {0x1F22, 0x1F2A}, {0x1F23, 0x1F2B}, {0x1F24, 0x1F2C}, 
	{0x1F25, 0x1F2D}, {0x1F26, 0x1F2E}, {0x1F27, 0x1F2F}, {0x1F28, 0x1F20}, 
	{0x1F29, 0x1F21}, {0x1F2A, 0x1F22}, {0x1F2B, 0x1F23}, {0x1F2C, 0x1F24}, 
	{0x1F2D, 0x1F25}, {0x1F2E, 0x1F26}, {0x1F2F, 0x1F27}, {0x1F30, 0x1F38}, 
	{0x1F31, 0x1F39}, {0x1F32, 0x1F3A}, {0x1F33, 0x1F3B}, {0x1F34, 0x1F3C}, 
	{0x1F35, 0x1F3D}, {0x1F36, 0x1F3E}, {0x1F37, 0x1F3F}, {0x1F38, 0x1F30}, 
	{0x1F39, 0x1F31}, {0x1F3A, 0x1F32}, {0x1F3B, 0x1F33}, {0x1F3C, 0x1F34}, 
	{0x1F3D, 0x1F35}, {0x1F3E, 0x1F36}, {0x1F3F, 0x1F37}, {0x1F40, 0x1F48}, 
	{0x1F41, 0x1F49}, {0x1F42, 0x1F4A}, {0x1F43, 0x1F4B}, {0x1F44, 0x1F4C}, 
	{0x1F45, 0x1F4D}, {0x1F48, 0x1F40}, {0x1F49, 0x1F41}, {0x1F4A, 0x1F42}, 
	{0x1F4B, 0x1F43}, {0x1F4C, 0x1F44}, {0x1F4D, 0x1F45}, {0x1F51, 0x1F59}, 
	{0x1F53, 0x1F5B}, {0x1F55, 0x1F5D}, {0x1F57, 0x1F5F}, {0x1F59, 0x1F51}, 
	{0x1F5B, 0x1F53}, {0x1F5D, 0x1F55}, {0x1F5F, 0x1F57}, {0x1F60, 0x1F68}, 
	{0x1F61, 0x1F69}, {0x1F62, 0x1F6A}, {0x1F63, 0x1F6B}, {0x1F64, 0x1F6C}, 
	{0x1F65, 0x1F6D}, {0x1F66, 0x1F6E}, {0x1F67, 0x1F6F}, {0x1F68, 0x1F60}, 
	{0x1F69, 0x1F61}, {0x1F6A, 0x1F62}, {0x1F6B, 0x1F63}, {0x1F6C, 0x1F64}, 
	{0x1F6D, 0x1F65}, {0x1F6E, 0x1F66}, {0x1F6F, 0x1F67}, {0x1F70, 0x1FBA}, 
	{0x1F71, 0x1FBB}, {0x1F72, 0x1FC8}, {0x1F73, 0x1FC9}, {0x1F74, 0x1FCA}, 
	{0x1F75, 0x1FCB}, {0x1F76, 0x1FDA}, {0x1F77, 0x1FDB}, {0x1F78, 0x1FF8}, 
	{0x1F79, 0x1FF9}, {0x1F7A, 0x1FEA}, {0x1F7B, 0x1FEB}, {0x1F7C, 0x1FFA}, 
	{0x1F7D, 0x1FFB}, {0x1F80, 0x1F88}, {0x1F81, 0x1F89}, {0x1F82, 0x1F8A}, 
	{0x1F83, 0x1F8B}, {0x1F84, 0x1F8C}, {0x1F85, 0x1F8D}, {0x1F86, 0x1F8E}, 
	{0x1F87, 0x1F8F}, {0x1F88, 0x1F80}, {0x1F89, 0x1F81}, {0x1F8A, 0x1F82}, 
	{0x1F8B, 0x1F83}, {0x1F8C, 0x1F84}, {0x1F8D, 0x1F85}, {0x1F8E, 0x1F86}, 
	{0x1F8F, 0x1F87}, {0x1F90, 0x1F98}, {0x1F91, 0x1F99}, {0x1F92, 0x1F9A}, 
	{0x1F93, 0x1F9B}, {0x1F94, 0x1F9C}, {0x1F95, 0x1F9D}, {0x1F96, 0x1F9E}, 
	{0x1F97, 0x1F9F}, {0x1F98, 0x1F90}, {0x1F99, 0x1F91}, {0x1F9A, 0x1F92}, 
	{0x1F9B, 0x1F93}, {0x1F9C, 0x1F94}, {0x1F9D, 0x1F95}, {0x1F9E, 0x1F96}, 
	{0x1F9F, 0x1F97}, {0x1FA0, 0x1FA8}, {0x1FA1, 0x1FA9}, {0x1FA2, 0x1FAA}, 
	{0x1FA3, 0x1FAB}, {0x1FA4, 0x1FAC}, {0x1FA5, 0x1FAD}, {0x1FA6, 0x1FAE}, 
	{0x1FA7, 0x1FAF}, {0x1FA8, 0x1FA0}, {0x1FA9, 0x1FA1}, {0x1FAA, 0x1FA2}, 
	{0x1FAB, 0x1FA3}, {0x1FAC, 0x1FA4}, {0x1FAD, 0x1FA5}, {0x1FAE, 0x1FA6}, 
	{0x1FAF, 0x1FA7}, {0x1FB0, 0x1FB8}, {0x1FB1, 0x1FB9}, {0x1FB3, 0x1FBC}, 
	{0x1FB8, 0x1FB0}, {0x1FB9, 0x1FB1}, {0x1FBA, 0x1F70}, {0x1FBB, 0x1F71}, 
	{0x1FBC, 0x1FB3}, {0x1FBE, 0x0345}, {0x1FC3, 0x1FCC}, {0x1FC8, 0x1F72}, 
	{0x1FC9, 0x1F73}, {0x1FCA, 0x1F74}, {0x1FCB, 0x1F75}, {0x1FCC, 0x1FC3}, 
	{0x1FD0, 0x1FD8}, {0x1FD1, 0x1FD9}, {0x1FD8, 0x1FD0}, {0x1FD9, 0x1FD1}, 
	{0x1FDA, 0x1F76}, {0x1FDB, 0x1F77}, {0x1FE0, 0x1FE8}, {0x1FE1, 0x1FE9}, 
	{0x1FE5, 0x1FEC}, {0x1FE8, 0x1FE0}, {0x1FE9, 0x1FE1}, {0x1FEA, 0x1F7A}, 
	{0x1FEB, 0x1F7B}, {0x1FEC, 0x1FE5}, {0x1FF3, 0x1FFC}, {0x1FF8, 0x1F78}, 
	{0x1FF9, 0x1F79}, {0x1FFA, 0x1F7C}, {0x1FFB, 0x1F7D}, {0x1FFC, 0x1FF3}, 
	{0x2126, 0x03A9}, {0x212A, 0x004B}, {0x212B, 0x00C5}, {0x2132, 0x214E}, 
	{0x214E, 0x2132}, {0x2160, 0x2170}, {0x2161, 0x2171}, {0x2162, 0x2172}, 
	{0x2163, 0x2173}, {0x2164, 0x2174}, {0x2165, 0x2175}, {0x2166, 0x2176}, 
	{0x2167, 0x2177}, {0x2168, 0x2178}, {0x2169, 0x2179}, {0x216A, 0x217A}, 
	{0x216B, 0x217B}, {0x216C, 0x217C}, {0x216D, 0x217D}, {0x216E, 0x217E}, 
	{0x216F, 0x217F}, {0x2170, 0x2160}, {0x2171, 0x2161}, {0x2172, 0x2162}, 
	{0x2173, 0x2163}, {0x2174, 0x2164}, {0x2175, 0x2165}, {0x2176, 0x2166}, 
	{0x2177, 0x2167}, {0x2178, 0x2168}, {0x2179, 0x2169}, {0x217A, 0x216A}, 
	{0x217B, 0x216B}, {0x217C, 0x216C}, {0x217D, 0x216D}, {0x217E, 0x216E}, 
	{0x217F, 0x216F}, {0x2183, 0x2184}, {0x2184, 0x2183}, {0x24B6, 0x24D0}, 
	{0x24B7, 0x24D1}, {0x24B8, 0x24D2}, {0x24B9, 0x24D3}, {0x24BA, 0x24D4}, 
	{0x24BB, 0x24D5}, {0x24BC, 0x24D6}, {0x24BD, 0x24D7}, {0x24BE, 0x24D8}, 
	{0x24BF, 0x24D9}, {0x24C0, 0x24DA}, {0x24C1, 0x24DB}, {0x24C2, 0x24DC}, 
	{0x24C3, 0x24DD}, {0x24C4, 0x24DE}, {0x24C5, 0x24DF}, {0x24C6, 0x24E0}, 
	{0x24C7, 0x24E1}, {0x24C8, 0x24E2}, {0x24C9, 0x24E3}, {0x24CA, 0x24E4}, 
	{0x24CB, 0x24E5}, {0x24CC, 0x24E6}, {0x24CD, 0x24E7}, {0x24CE, 0x24E8}, 
	{0x24CF, 0x24E9}, {0x24D0, 0x24B6}, {0x24D1, 0x24B7}, {0x24D2, 0x24B8}, 
	{0x24D3, 0x24B9}, {0x24D4, 0x24BA}, {0x24D5, 0x24BB}, {0x24D6, 0x24BC}, 
	{0x24D7, 0x24BD}, {0x24D8, 0x24BE}, {0x24D9, 0x24BF}, {0x24DA, 0x24C0}, 
	{0x24DB, 0x24C1}, {0x24DC, 0x24C2}, {0x24DD, 0x24C3}, {0x24DE, 0x24C4}, 
	{0x24DF, 0x24C5}, {0x24E0, 0x24C6}, {0x24E1, 0x24C7}, {0x24E2, 0x24C8}, 
	{0x24E3, 0x24C9}, {0x24E4, 0x24CA}, {0x24E5, 0x24CB}, {0x24E6, 0x24CC}, 
	{0x24E7, 0x24CD}, {0x24E8, 0x24CE}, {0x24E9, 0x24CF}, {0x2C00, 0x2C30}, 
	{0x2C01, 0x2C31}, {0x2C02, 0x2C32}, {0x2C03, 0x2C33}, {0x2C04, 0x2C34}, 
	{0x2C05, 0x2C35}, {0x2C06, 0x2C36}, {0x2C07, 0x2C37}, {0x2C08, 0x2C38}, 
	{0x2C09, 0x2C39}, {0x2C0A, 0x2C3A}, {0x2C0B, 0x2C3B}, {0x2C0C, 0x2C3C}, 
	{0x2C0D, 0x2C3D}, {0x2C0E, 0x2C3E}, {0x2C0F, 0x2C3F}, {0x2C10, 0x2C40}, 
	{0x2C11, 0x2C41}, {0x2C12, 0x2C42}, {0x2C13, 0x2C43}, {0x2C14, 0x2C44}, 
	{0x2C15, 0x2C45}, {0x2C16, 0x2C46}, {0x2C17, 0x2C47}, {0x2C18, 0x2C48}, 
	{0x2C19, 0x2C49}, {0x2C1A, 0x2C4A}, {0x2C1B, 0x2C4B}, {0x2C1C, 0x2C4C}, 
	{0x2C1D, 0x2C4D}, {0x2C1E, 0x2C4E}, {0x2C1F, 0x2C4F}, {0x2C20, 0x2C50}, 
	{0x2C21, 0x2C51}, {0x2C22, 0x2C52}, {0x2C23, 0x2C53}, {0x2C24, 0x2C54}, 
	{0x2C25, 0x2C55}, {0x2C26, 0x2C56}, {0x2C27, 0x2C57}, {0x2C28, 0x2C58}, 
	{0x2C29, 0x2C59}, {0x2C2A, 0x2C5A}, {0x2C2B, 0x2C5B}, {0x2C2C, 0x2C5C}, 
	{0x2C2D, 0x2C5D}, {0x2C2E, 0x2C5E}, {0x2C2F, 0x2C5F}, {0x2C30, 0x2C00}, 
	{0x2C31, 0x2C01}, {0x2C32, 0x2C02}, {0x2C33, 0x2C03}, {0x2C34, 0x2C04}, 
	{0x2C35, 0x2C05}, {0x2C36, 0x2C06}, {0x2C37, 0x2C07}, {0x2C38, 0x2C08}, 
	{0x2C39, 0x2C09}, {0x2C3A, 0x2C0A}, {0x2C3B, 0x2C0B}, {0x2C3C, 0x2C0C}, 
	{0x2C3D, 0x2C0D}, {0x2C3E, 0x2C0E}, {0x2C3F, 0x2C0F}, {0x2C40, 0x2C10}, 
	{0x2C41, 0x2C11}, {0x2C42, 0x2C12}, {0x2C43, 0x2C13}, {0x2C44, 0x2C14}, 
	{0x2C45, 0x2C15}, {0x2C46, 0x2C16}, {0x2C47, 0x2C17}, {0x2C48, 0x2C18}, 
	{0x2C49, 0x2C19}, {0x2C4A, 0x2C1A}, {0x2C4B, 0x2C1B}, {0x2C4C, 0x2C1C}, 
	{0x2C4D, 0x2C1D}, {0x2C4E, 0x2C1E}, {0x2C4F, 0x2C1F}, {0x2C50, 0x2C20}, 
	{0x2C51, 0x2C21}, {0x2C52, 0x2C22}, {0x2C53, 0x2C23}, {0x2C54, 0x2C24}, 
	{0x2C55, 0x2C25}, {0x2C56, 0x2C26}, {0x2C57, 0x2C27}, {0x2C58, 0x2C28}, 
	{0x2C59, 0x2C29}, {0x2C5A, 0x2C2A}, {0x2C5B, 0x2C2B}, {0x2C5C, 0x2C2C}, 
	{0x2C5D, 0x2C2D}, {0x2C5E, 0x2C2E}, {0x2C5F, 0x2C2F}, {0x2C60, 0x2C61}, 
	{0x2C61, 0x2C60}, {0x2C62, 0x026B}, {0x2C63, 0x1D7D}, {0x2C64, 0x027D}, 
	{0x2C65, 0x023A}, {0x2C66, 0x023E}, {0x2C67, 0x2C68}, {0x2C68, 0x2C67}, 
	{0x2C69, 0x2C6A}, {0x2C6A, 0x2C69}, {0x2C6B, 0x2C6C}, {0x2C6C, 0x2C6B}, 
	{0x2C6D, 0x0251}, {0x2C6E, 0x0271}, {0x2C6F, 0x0250}, {0x2C70, 0x0252}, 
	{0x2C72, 0x2C73}, {0x2C73, 0x2C72}, {0x2C75, 0x2C76}, {0x2C76, 0x2C75}, 
	{0x2C7E, 0x023F}, {0x2C7F, 0x0240}, {0x2C80, 0x2C81}, {0x2C81, 0x2C80}, 
	{0x2C82, 0x2C83}, {0x2C83, 0x2C82}, {0x2C84, 0x2C85}, {0x2C85, 0x2C84}, 
	{0x2C86, 0x2C87}, {0x2C87, 0x2C86}, {0x2C88, 0x2C89}, {0x2C89, 0x2C88}, 
	{0x2C8A, 0x2C8B}, {0x2C8B, 0x2C8A}, {0x2C8C, 0x2C8D}, {0x2C8D, 0x2C8C}, 
	{0x2C8E, 0x2C8F}, {0x2C8F, 0x2C8E}, {0x2C90, 0x2C91}, {0x2C91, 0x2C90}, 
	{0x2C92, 0x2C93}, {0x2C93, 0x2C92}, {0x2C94, 0x2C95}, {0x2C95, 0x2C94}, 
	{0x2C96, 0x2C97}, {0x2C97, 0x2C96}, {0x2C98, 0x2C99}, {0x2C99, 0x2C98}, 
	{0x2C9A, 0x2C9B}, {0x2C9B, 0x2C9A}, {0x2C9C, 0x2C9D}, {0x2C9D, 0x2C9C}, 
	{0x2C9E, 0x2C9F}, {0x2C9F, 0x2C9E}, {0x2CA0, 0x2CA1}, {0x2CA1, 0x2CA0}, 
	{0x2CA2, 0x2CA3}, {0x2CA3, 0x2CA2}, {0x2CA4, 0x2CA5}, {0x2CA5, 0x2CA4}, 
	{0x2CA6, 0x2CA7}, {0x2CA7, 0x2CA6}, {0x2CA8, 0x2CA9}, {0x2CA9, 0x2CA8}, 
	{0x2CAA, 0x2CAB}, {0x2CAB, 0x2CAA}, {0x2CAC, 0x2CAD}, {0x2CAD, 0x2CAC}, 
	{0x2CAE, 0x2CAF}, {0x2CAF, 0x2CAE}, {0x2CB0, 0x2CB1}, {0x2CB1, 0x2CB0}, 
	{0x2CB2, 0x2CB3}, {0x2CB3, 0x2CB2}, {0x2CB4, 0x2CB5}, {0x2CB5, 0x2CB4}, 
	{0x2CB6, 0x2CB7}, {0x2CB7, 0x2CB6}, {0x2CB8, 0x2CB9}, {0x2CB9, 0x2CB8}, 
	{0x2CBA, 0x2CBB}, {0x2CBB, 0x2CBA}, {0x2CBC, 0x2CBD}, {0x2CBD, 0x2CBC}, 
	{0x2CBE, 0x2CBF}, {0x2CBF, 0x2CBE}, {0x2CC0, 0x2CC1}, {0x2CC1, 0x2CC0}, 
	{0x2CC2, 0x2CC3}, {0x2CC3, 0x2CC2}, {0x2CC4, 0x2CC5}, {0x2CC5, 0x2CC4}, 
	{0x2CC6, 0x2CC7}, {0x2CC7, 0x2CC6}, {0x2CC8, 0x2CC9}, {0x2CC9, 0x2CC8}, 
	{0x2CCA, 0x2CCB}, {0x2CCB, 0x2CCA}, {0x2CCC, 0x2CCD}, {0x2CCD, 0x2CCC}, 
	{0x2CCE, 0x2CCF}, {0x2CCF, 0x2CCE}, {0x2CD0, 0x2CD1}, {0x2CD1, 0x2CD0}, 
	{0x2CD2, 0x2CD3}, {0x2CD3, 0x2CD2}, {0x2CD4, 0x2CD5}, {0x2CD5, 0x2CD4}, 
	{0x2CD6, 0x2CD7}, {0x2CD7, 0x2CD6}, {0x2CD8, 0x2CD9}, {0x2CD9, 0x2CD8}, 
	{0x2CDA, 0x2CDB}, {0x2CDB, 0x2CDA}, {0x2CDC, 0x2CDD}, {0x2CDD, 0x2CDC}, 
	{0x2CDE, 0x2CDF}, {0x2CDF, 0x2CDE}, {0x2CE0, 0x2CE1}, {0x2CE1, 0x2CE0}, 
	{0x2CE2, 0x2CE3}, {0x2CE3, 0x2CE2}, {0x2CEB, 0x2CEC}, {0x2CEC, 0x2CEB}, 
	{0x2CED, 0x2CEE}, {0x2CEE, 0x2CED}, {0x2CF2, 0x2CF3}, {0x2CF3, 0x2CF2}, 
	{0x2D00, 0x10A0}, {0x2D01, 0x10A1}, {0x2D02, 0x10A2}, {0x2D03, 0x10A3}, 
	{0x2D04, 0x10A4}, {0x2D05, 0x10A5}, {0x2D06, 0x10A6}, {0x2D07, 0x10A7}, 
	{0x2D08, 0x10A8}, {0x2D09, 0x10A9}, {0x2D0A, 0x10AA}, {0x2D0B, 0x10AB}, 
	{0x2D0C, 0x10AC}, {0x2D0D, 0x10AD}, {0x2D0E, 0x10AE}, {0x2D0F, 0x10AF}, 
	{0x2D10, 0x10B0}, {0x2D11, 0x10B1}, {0x2D12, 0x10B2}, {0x2D13, 0x10B3}, 
	{0x2D14, 0x10B4}, {0x2D15, 0x10B5}, {0x2D16, 0x10B6}, {0x2D17, 0x10B7}, 
	{0x2D18, 0x10B8}, {0x2D19, 0x10B9}, {0x2D1A, 0x10BA}, {0x2D1B, 0x10BB}, 
	{0x2D1C, 0x10BC}, {0x2D1D, 0x10BD}, {0x2D1E, 0x10BE}, {0x2D1F, 0x10BF}, 
	{0x2D20, 0x10C0}, {0x2D21, 0x10C1}, {0x2D22, 0x10C2}, {0x2D23, 0x10C3}, 
	{0x2D24, 0x10C4}, {0x2D25, 0x10C5}, {0x2D27, 0x10C7}, {0x2D2D, 0x10CD}, 
	{0xA640, 0xA641}, {0xA641, 0xA640}, {0xA642, 0xA643}, {0xA643, 0xA642}, 
	{0xA644, 0xA645}, {0xA645, 0xA644}, {0xA646, 0xA647}, {0xA647, 0xA646}, 
	{0xA648, 0xA649}, {0xA649, 0xA648}, {0xA64A, 0xA64B}, {0xA64B, 0x1C88}, 
	{0xA64C, 0xA64D}, {0xA64D, 0xA64C}, {0xA64E, 0xA64F}, {0xA64F, 0xA64E}, 
	{0xA650, 0xA651}, {0xA651, 0xA650}, {0xA652, 0xA653}, {0xA653, 0xA652}, 
	{0xA654, 0xA655}, {0xA655, 0xA654}, {0xA656, 0xA657}, {0xA657, 0xA656}, 
	{0xA658, 0xA659}, {0xA659, 0xA658}, {0xA65A, 0xA65B}, {0xA65B, 0xA65A}, 
	{0xA65C, 0xA65D}, {0xA65D, 0xA65C}, {0xA65E, 0xA65F}, {0xA65F, 0xA65E}, 
	{0xA660, 0xA661}, {0xA661, 0xA660}, {0xA662, 0xA663}, {0xA663, 0xA662}, 
	{0xA664, 0xA665}, {0xA665, 0xA664}, {0xA666, 0xA667}, {0xA667, 0xA666}, 
	{0xA668, 0xA669}, {0xA669, 0xA668}, {0xA66A, 0xA66B}, {0xA66B, 0xA66A}, 
	{0xA66C, 0xA66D}, {0xA66D, 0xA66C}, {0xA680, 0xA681}, {0xA681, 0xA680}, 
	{0xA682, 0xA683}, {0xA683, 0xA682}, {0xA684, 0xA685}, {0xA685, 0xA684}, 
	{0xA686, 0xA687}, {0xA687, 0xA686}, {0xA688, 0xA689}, {0xA689, 0xA688}, 
	{0xA68A, 0xA68B}, {0xA68B, 0xA68A}, {0xA68C, 0xA68D}, {0xA68D, 0xA68C}, 
	{0xA68E, 0xA68F}, {0xA68F, 0xA68E}, {0xA690, 0xA691}, {0xA691, 0xA690}, 
	{0xA692, 0xA693}, {0xA693, 0xA692}, {0xA694, 0xA695}, {0xA695, 0xA694}, 
	{0xA696, 0xA697}, {0xA697, 0xA696}, {0xA698, 0xA699}, {0xA699, 0xA698}, 
	{0xA69A, 0xA69B}, {0xA69B, 0xA69A}, {0xA722, 0xA723}, {0xA723, 0xA722}, 
	{0xA724, 0xA725}, {0xA725, 0xA724}, {0xA726, 0xA727}, {0xA727, 0xA726}, 
	{0xA728, 0xA729}, {0xA729, 0xA728}, {0xA72A, 0xA72B}, {0xA72B, 0xA72A}, 
	{0xA72C, 0xA72D}, {0xA72D, 0xA72C}, {0xA72E, 0xA72F}, {0xA72F, 0xA72E}, 
	{0xA732, 0xA733}, {0xA733, 0xA732}, {0xA734, 0xA735}, {0xA735, 0xA734}, 
	{0xA736, 0xA737}, {0xA737, 0xA736}, {0xA738, 0xA739}, {0xA739, 0xA738}, 
	{0xA73A, 0xA73B}, {0xA73B, 0xA73A}, {0xA73C, 0xA73D}, {0xA73D, 0xA73C}, 
	{0xA73E, 0xA73F}, {0xA73F, 0xA73E}, {0xA740, 0xA741}, {0xA741, 0xA740}, 
	{0xA742, 0xA743}, {0xA743, 0xA742}, {0xA744, 0xA745}, {0xA745, 0xA744}, 
	{0xA746, 0xA747}, {0xA747, 0xA746}, {0xA748, 0xA749}, {0xA749, 0xA748}, 
	{0xA74A, 0xA74B}, {0xA74B, 0xA74A}, {0xA74C, 0xA74D}, {0xA74D, 0xA74C}, 
	{0xA74E, 0xA74F}, {0xA74F, 0xA74E}, {0xA750, 0xA751}, {0xA751, 0xA750}, 
	{0xA752, 0xA753}, {0xA753, 0xA752}, {0xA754, 0xA755}, {0xA755, 0xA754}, 
	{0xA756, 0xA757}, {0xA757, 0xA756}, {0xA758, 0xA759}, {0xA759, 0xA758}, 
	{0xA75A, 0xA75B}, {0xA75B, 0xA75A}, {0xA75C, 0xA75D}, {0xA75D, 0xA75C}, 
	{0xA75E, 0xA75F}, {0xA75F, 0xA75E}, {0xA760, 0xA761}, {0xA761, 0xA760}, 
	{0xA762, 0xA763}, {0xA763, 0xA762}, {0xA764, 0xA765}, {0xA765, 0xA764}, 
	{0xA766, 0xA767}, {0xA767, 0xA766}, {0xA768, 0xA769}, {0xA769, 0xA768}, 
	{0xA76A, 0xA76B}, {0xA76B, 0xA76A}, {0xA76C, 0xA76D}, {0xA76D, 0xA76C}, 
	{0xA76E, 0xA76F}, {0xA76F, 0xA76E}, {0xA779, 0xA77A}, {0xA77A, 0xA779}, 
	{0xA77B, 0xA77C}, {0xA77C, 0xA77B}, {0xA77D, 0x1D79}, {0xA77E, 0xA77F}, 
	{0xA77F, 0xA77E}, {0xA780, 0xA781}, {0xA781, 0xA780}, {0xA782, 0xA783}, 
	{0xA783, 0xA782}, {0xA784, 0xA785}, {0xA785, 0xA784}, {0xA786, 0xA787}, 
	{0xA787, 0xA786}, {0xA78B, 0xA78C}, {0xA78C, 0xA78B}, {0xA78D, 0x0265}, 
	{0xA790, 0xA791}, {0xA791, 0xA790}, {0xA792, 0xA793}, {0xA793, 0xA792}, 
	{0xA794, 0xA7C4}, {0xA796, 0xA797}, {0xA797, 0xA796}, {0xA798, 0xA799}, 
	{0xA799, 0xA798}, {0xA79A, 0xA79B}, {0xA79B, 0xA79A}, {0xA79C, 0xA79D}, 
	{0xA79D, 0xA79C}, {0xA79E, 0xA79F}, {0xA79F, 0xA79E}, {0xA7A0, 0xA7A1}, 
	{0xA7A1, 0xA7A0}, {0xA7A2, 0xA7A3}, {0xA7A3, 0xA7A2}, {0xA7A4, 0xA7A5}, 
	{0xA7A5, 0xA7A4}, {0xA7A6, 0xA7A7}, {0xA7A7, 0xA7A6}, {0xA7A8, 0xA7A9}, 
	{0xA7A9, 0xA7A8}, {0xA7AA, 0x0266}, {0xA7AB, 0x025C}, {0xA7AC, 0x0261}, 
	{0xA7AD, 0x026C}, {0xA7AE, 0x026A}, {0xA7B0, 0x029E}, {0xA7B1, 0x0287}, 
	{0xA7B2, 0x029D}, {0xA7B3, 0xAB53}, {0xA7B4, 0xA7B5}, {0xA7B5, 0xA7B4}, 
	{0xA7B6, 0xA7B7}, {0xA7B7, 0xA7B6}, {0xA7B8, 0xA7B9}, {0xA7B9, 0xA7B8}, 
	{0xA7BA, 0xA7BB}, {0xA7BB, 0xA7BA}, {0xA7BC, 0xA7BD}, {0xA7BD, 0xA7BC}, 
	{0xA7BE, 0xA7BF}, {0xA7BF, 0xA7BE}, {0xA7C0, 0xA7C1}, {0xA7C1, 0xA7C0}, 
	{0xA7C2, 0xA7C3}, {0xA7C3, 0xA7C2}, {0xA7C4, 0xA794}, {0xA7C5, 0x0282}, 
	{0xA7C6, 0x1D8E}, {0xA7C7, 0xA7C8}, {0xA7C8, 0xA7C7}, {0xA7C9, 0xA7CA}, 
	{0xA7CA, 0xA7C9}, {0xA7D0, 0xA7D1}, {0xA7D1, 0xA7D0}, {0xA7D6, 0xA7D7}, 
	{0xA7D7, 0xA7D6}, {0xA7D8, 0xA7D9}, {0xA7D9, 0xA7D8}, {0xA7F5, 0xA7F6}, 
	{0xA7F6, 0xA7F5}, {0xAB53, 0xA7B3}, {0xAB70, 0x13A0}, {0xAB71, 0x13A1}, 
	{0xAB72, 0x13A2}, {0xAB73, 0x13A3}, {0xAB74, 0x13A4}, {0xAB75, 0x13A5}, 
	{0xAB76, 0x13A6}, {0xAB77, 0x13A7}, {0xAB78, 0x13A8}, {0xAB79, 0x13A9}, 
	{0xAB7A, 0x13AA}, {0xAB7B, 0x13AB}, {0xAB7C, 0x13AC}, {0xAB7D, 0x13AD}, 
	{0xAB7E, 0x13AE}, {0xAB7F, 0x13AF}, {0xAB80, 0x13B0}, {0xAB81, 0x13B1}, 
	{0xAB82, 0x13B2}, {0xAB83, 0x13B3}, {0xAB84, 0x13B4}, {0xAB85, 0x13B5}, 
	{0xAB86, 0x13B6}, {0xAB87, 0x13B7}, {0xAB88, 0x13B8}, {0xAB89, 0x13B9}, 
	{0xAB8A, 0x13BA}, {0xAB8B, 0x13BB}, {0xAB8C, 0x13BC}, {0xAB8D, 0x13BD}, 
	{0xAB8E, 0x13BE}, {0xAB8F, 0x13BF}, {0xAB90, 0x13C0}, {0xAB91, 0x13C1}, 
	{0xAB92, 0x13C2}, {0xAB93, 0x13C3}, {0xAB94, 0x13C4}, {0xAB95, 0x13C5}, 
	{0xAB96, 0x13C6}, {0xAB97, 0x13C7}, {0xAB98, 0x13C8}, {0xAB99, 0x13C9}, 
	{0xAB9A, 0x13CA}, {0xAB9B, 0x13CB}, {0xAB9C, 0x13CC}, {0xAB9D, 0x13CD}, 
	{0xAB9E, 0x13CE}, {0xAB9F, 0x13CF}, {0xABA0, 0x13D0}, {0xABA1, 0x13D1}, 
	{0xABA2, 0x13D2}, {0xABA3, 0x13D3}, {0xABA4, 0x13D4}, {0xABA5, 0x13D5}, 
	{0xABA6, 0x13D6}, {0xABA7, 0x13D7}, {0xABA8, 0x13D8}, {0xABA9, 0x13D9}, 
	{0xABAA, 0x13DA}, {0xABAB, 0x13DB}, {0xABAC, 0x13DC}, {0xABAD, 0x13DD}, 
	{0xABAE, 0x13DE}, {0xABAF, 0x13DF}, {0xABB0, 0x13E0}, {0xABB1, 0x13E1}, 
	{0xABB2, 0x13E2}, {0xABB3, 0x13E3}, {0xABB4, 0x13E4}, {0xABB5, 0x13E5}, 
	{0xABB6, 0x13E6}, {0xABB7, 0x13E7}, {0xABB8, 0x13E8}, {0xABB9, 0x13E9}, 
	{0xABBA, 0x13EA}, {0xABBB, 0x13EB}, {0xABBC, 0x13EC}, {0xABBD, 0x13ED}, 
	{0xABBE, 0x13EE}, {0xABBF, 0x13EF}, {0xFF21, 0xFF41}, {0xFF22, 0xFF42}, 
	{0xFF23, 0xFF43}, {0xFF24, 0xFF44}, {0xFF25, 0xFF45}, {0xFF26, 0xFF46}, 
	{0xFF27, 0xFF47}, {0xFF28, 0xFF48}, {0xFF29, 0xFF49}, {0xFF2A, 0xFF4A}, 
	{0xFF2B, 0xFF4B}, {0xFF2C, 0xFF4C}, {0xFF2D, 0xFF4D}, {0xFF2E, 0xFF4E}, 
	{0xFF2F, 0xFF4F}, {0xFF30, 0xFF50}, {0xFF31, 0xFF51}, {0xFF32, 0xFF52}, 
	{0xFF33, 0xFF53}, {0xFF34, 0xFF54}, {0xFF35, 0xFF55}, {0xFF36, 0xFF56}, 
	{0xFF37, 0xFF57}, {0xFF38, 0xFF58}, {0xFF39, 0xFF59}, {0xFF3A, 0xFF5A}, 
	{0xFF41, 0xFF21}, {0xFF42, 0xFF22}, {0xFF43, 0xFF23}, {0xFF44, 0xFF24}, 
	{0xFF45, 0xFF25}, {0xFF46, 0xFF26}, {0xFF47, 0xFF27}, {0xFF48, 0xFF28}, 
	{0xFF49, 0xFF29}, {0xFF4A, 0xFF2A}, {0xFF4B, 0xFF2B}, {0xFF4C, 0xFF2C}, 
	{0xFF4D, 0xFF2D}, {0xFF4E, 0xFF2E}, {0xFF4F, 0xFF2F}, {0xFF50, 0xFF30}, 
	{0xFF51, 0xFF31}, {0xFF52, 0xFF32}, {0xFF53, 0xFF33}, {0xFF54, 0xFF34}, 
	{0xFF55, 0xFF35}, {0xFF56, 0xFF36}, {0xFF57, 0xFF37}, {0xFF58, 0xFF38}, 
	{0xFF59, 0xFF39}, {0xFF5A, 0xFF3A}, {0x10400, 0x10428}, {0x10401, 0x10429}, 
	{0x10402, 0x1042A}, {0x10403, 0x1042B}, {0x10404, 0x1042C}, {0x10405, 0x1042D}, 
	{0x10406, 0x1042E}, {0x10407, 0x1042F}, {0x10408, 0x10430}, {0x10409, 0x10431}, 
	{0x1040A, 0x10432}, {0x1040B, 0x10433}, {0x1040C, 0x10434}, {0x1040D, 0x10435}, 
	{0x1040E, 0x10436}, {0x1040F, 0x10437}, {0x10410, 0x10438}, {0x10411, 0x10439}, 
	{0x10412, 0x1043A}, {0x10413, 0x1043B}, {0x10414, 0x1043C}, {0x10415, 0x1043D}, 
	{0x10416, 0x1043E}, {0x10417, 0x1043F}, {0x10418, 0x10440}, {0x10419, 0x10441}, 
	{0x1041A, 0x10442}, {0x1041B, 0x10443}, {0x1041C, 0x10444}, {0x1041D, 0x10445}, 
	{0x1041E, 0x10446}, {0x1041F, 0x10447}, {0x10420, 0x10448}, {0x10421, 0x10449}, 
	{0x10422, 0x1044A}, {0x10423, 0x1044B}, {0x10424, 0x1044C}, {0x10425, 0x1044D}, 
	{0x10426, 0x1044E}, {0x10427, 0x1044F}, {0x10428, 0x10400}, {0x10429, 0x10401}, 
	{0x1042A, 0x10402}, {0x1042B, 0x10403}, {0x1042C, 0x10404}, {0x1042D, 0x10405}, 
	{0x1042E, 0x10406}, {0x1042F, 0x10407}, {0x10430, 0x10408}, {0x10431, 0x10409}, 
	{0x10432, 0x1040A}, {0x10433, 0x1040B}, {0x10434, 0x1040C}, {0x10435, 0x1040D}, 
	{0x10436, 0x1040E}, {0x10437, 0x1040F}, {0x10438, 0x10410}, {0x10439, 0x10411}, 
	{0x1043A, 0x10412}, {0x1043B, 0x10413}, {0x1043C, 0x10414}, {0x1043D, 0x10415}, 
	{0x1043E, 0x10416}, {0x1043F, 0x10417}, {0x10440, 0x10418}, {0x10441, 0x10419}, 
	{0x10442, 0x1041A}, {0x10443, 0x1041B}, {0x10444, 0x1041C}, {0x10445, 0x1041D}, 
	{0x10446, 0x1041E}, {0x10447, 0x1041F}, {0x10448, 0x10420}, {0x10449, 0x10421}, 
	{0x1044A, 0x10422}, {0x1044B, 0x10423}, {0x1044C, 0x10424}, {0x1044D, 0x10425}, 
	{0x1044E, 0x10426}, {0x1044F, 0x10427}, {0x104B0, 0x104D8}, {0x104B1, 0x104D9}, 
	{0x104B2, 0x104DA}, {0x104B3, 0x104DB}, {0x104B4, 0x104DC}, {0x104B5, 0x104DD}, 
	{0x104B6, 0x104DE}, {0x104B7, 0x104DF}, {0x104B8, 0x104E0}, {0x104B9, 0x104E1}, 
	{0x104BA, 0x104E2}, {0x104BB, 0x104E3}, {0x104BC, 0x104E4}, {0x104BD, 0x104E5}, 
	{0x104BE, 0x104E6}, {0x104BF, 0x104E7}, {0x104C0, 0x104E8}, {0x104C1, 0x104E9}, 
	{0x104C2, 0x104EA}, {0x104C3, 0x104EB}, {0x104C4, 0x104EC}, {0x104C5, 0x104ED}, 
	{0x104C6, 0x104EE}, {0x104C7, 0x104EF}, {0x104C8, 0x104F0}, {0x104C9, 0x104F1}, 
	{0x104CA, 0x104F2}, {0x104CB, 0x104F3}, {0x104CC, 0x104F4}, {0x104CD, 0x104F5}, 
	{0x104CE, 0x104F6}, {0x104CF, 0x104F7}, {0x104D0, 0x104F8}, {0x104D1, 0x104F9}, 
	{0x104D2, 0x104FA}, {0x104D3, 0x104FB}, {0x104D8, 0x104B0}, {0x104D9, 0x104B1}, 
	{0x104DA, 0x104B2}, {0x104DB, 0x104B3}, {0x104DC, 0x104B4}, {0x104DD, 0x104B5}, 
	{0x104DE, 0x104B6}, {0x104DF, 0x104B7}, {0x104E0, 0x104B8}, {0x104E1, 0x104B9}, 
	{0x104E2, 0x104BA}, {0x104E3, 0x104BB}, {0x104E4, 0x104BC}, {0x104E5, 0x104BD}, 
	{0x104E6, 0x104BE}, {0x104E7, 0x104BF}, {0x104E8, 0x104C0}, {0x104E9, 0x104C1}, 
	{0x104EA, 0x104C2}, {0x104EB, 0x104C3}, {0x104EC, 0x104C4}, {0x104ED, 0x104C5}, 
	{0x104EE, 0x104C6}, {0x104EF, 0x104C7}, {0x104F0, 0x104C8}, {0x104F1, 0x104C9}, 
	{0x104F2, 0x104CA}, {0x104F3, 0x104CB}, {0x104F4, 0x104CC}, {0x104F5, 0x104CD}, 
	{0x104F6, 0x104CE}, {0x104F7, 0x104CF}, {0x104F8, 0x104D0}, {0x104F9, 0x104D1}, 
	{0x104FA, 0x104D2}, {0x104FB, 0x104D3}, {0x10570, 0x10597}, {0x10571, 0x10598}, 
	{0x10572, 0x10599}, {0x10573, 0x1059A}, {0x10574, 0x1059B}, {0x10575, 0x1059C}, 
	{0x10576, 0x1059D}, {0x10577, 0x1059E}, {0x10578, 0x1059F}, {0x10579, 0x105A0}, 
	{0x1057A, 0x105A1}, {0x1057C, 0x105A3}, {0x1057D, 0x105A4}, {0x1057E, 0x105A5}, 
	{0x1057F, 0x105A6}, {0x10580, 0x105A7}, {0x10581, 0x105A8}, {0x10582, 0x105A9}, 
	{0x10583, 0x105AA}, {0x10584, 0x105AB}, {0x10585, 0x105AC}, {0x10586, 0x105AD}, 
	{0x10587, 0x105AE}, {0x10588, 0x105AF}, {0x10589, 0x105B0}, {0x1058A, 0x105B1}, 
	{0x1058C, 0x105B3}, {0x1058D, 0x105B4}, {0x1058E, 0x105B5}, {0x1058F, 0x105B6}, 
	{0x10590, 0x105B7}, {0x10591, 0x105B8}, {0x10592, 0x105B9}, {0x10594, 0x105BB}, 
	{0x10595, 0x105BC}, {0x10597, 0x10570}, {0x10598, 0x10571}, {0x10599, 0x10572}, 
	{0x1059A, 0x10573}, {0x1059B, 0x10574}, {0x1059C, 0x10575}, {0x1059D, 0x10576}, 
	{0x1059E, 0x10577}, {0x1059F, 0x10578}, {0x105A0, 0x10579}, {0x105A1, 0x1057A}, 
	{0x105A3, 0x1057C}, {0x105A4, 0x1057D}, {0x105A5, 0x1057E}, {0x105A6, 0x1057F}, 
	{0x105A7, 0x10580}, {0x105A8, 0x10581}, {0x105A9, 0x10582}, {0x105AA, 0x10583}, 
	{0x105AB, 0x10584}, {0x105AC, 0x10585}, {0x105AD, 0x10586}, {0x105AE, 0x10587}, 
	{0x105AF, 0x10588}, {0x105B0, 0x10589}, {0x105B1, 0x1058A}, {0x105B3, 0x1058C}, 
	{0x105B4, 0x1058D}, {0x105B5, 0x1058E}, {0x105B6, 0x1058F}, {0x105B7, 0x10590}, 
	{0x105B8, 0x10591}, {0x105B9, 0x10592}, {0x105BB, 0x10594}, {0x105BC, 0x10595}, 
	{0x10C80, 0x10CC0}, {0x10C81, 0x10CC1}, {0x10C82, 0x10CC2}, {0x10C83, 0x10CC3}, 
	{0x10C84, 0x10CC4}, {0x10C85, 0x10CC5}, {0x10C86, 0x10CC6}, {0x10C87, 0x10CC7}, 
	{0x10C88, 0x10CC8}, {0x10C89, 0x10CC9}, {0x10C8A, 0x10CCA}, {0x10C8B, 0x10CCB}, 
	{0x10C8C, 0x10CCC}, {0x10C8D, 0x10CCD}, {0x10C8E, 0x10CCE}, {0x10C8F, 0x10CCF}, 
	{0x10C90, 0x10CD0}, {0x10C91, 0x10CD1}, {0x10C92, 0x10CD2}, {0x10C93, 0x10CD3}, 
	{0x10C94, 0x10CD4}, {0x10C95, 0x10CD5}, {0x10C96, 0x10CD6}, {0x10C97, 0x10CD7}, 
	{0x10C98, 0x10CD8}, {0x10C99, 0x10CD9}, {0x10C9A, 0x10CDA}, {0x10C9B, 0x10CDB}, 
	{0x10C9C, 0x10CDC}, {0x10C9D, 0x10CDD}, {0x10C9E, 0x10CDE}, {0x10C9F, 0x10CDF}, 
	{0x10CA0, 0x10CE0}, {0x10CA1, 0x10CE1}, {0x10CA2, 0x10CE2}, {0x10CA3, 0x10CE3}, 
	{0x10CA4, 0x10CE4}, {0x10CA5, 0x10CE5}, {0x10CA6, 0x10CE6}, {0x10CA7, 0x10CE7}, 
	{0x10CA8, 0x10CE8}, {0x10CA9, 0x10CE9}, {0x10CAA, 0x10CEA}, {0x10CAB, 0x10CEB}, 
	{0x10CAC, 0x10CEC}, {0x10CAD, 0x10CED}, {0x10CAE, 0x10CEE}, {0x10CAF, 0x10CEF}, 
	{0x10CB0, 0x10CF0}, {0x10CB1, 0x10CF1}, {0x10CB2, 0x10CF2}, {0x10CC0, 0x10C80}, 
	{0x10CC1, 0x10C81}, {0x10CC2, 0x10C82}, {0x10CC3, 0x10C83}, {0x10CC4, 0x10C84}, 
	{0x10CC5, 0x10C85}, {0x10CC6, 0x10C86}, {0x10CC7, 0x10C87}, {0x10CC8, 0x10C88}, 
	{0x10CC9, 0x10C89}, {0x10CCA, 0x10C8A}, {0x10CCB, 0x10C8B}, {0x10CCC, 0x10C8C}, 
	{0x10CCD, 0x10C8D}, {0x10CCE, 0x10C8E}, {0x10CCF, 0x10C8F}, {0x10CD0, 0x10C90}, 
	{0x10CD1, 0x10C91}, {0x10CD2, 0x10C92}, {0x10CD3, 0x10C93}, {0x10CD4, 0x10C94}, 
	{0x10CD5, 0x10C95}, {0x10CD6, 0x10C96}, {0x10CD7, 0x10C97}, {0x10CD8, 0x10C98}, 
	{0x10CD9, 0x10C99}, {0x10CDA, 0x10C9A}, {0x10CDB, 0x10C9B}, {0x10CDC, 0x10C9C}, 
	{0x10CDD, 0x10C9D}, {0x10CDE, 0x10C9E}, {0x10CDF, 0x10C9F}, {0x10CE0, 0x10CA0}, 
	{0x10CE1, 0x10CA1}, {0x10CE2, 0x10CA2}, {0x10CE3, 0x10CA3}, {0x10CE4, 0x10CA4}, 
	{0x10CE5, 0x10CA5}, {0x10CE6, 0x10CA6}, {0x10CE7, 0x10CA7}, {0x10CE8, 0x10CA8}, 
	{0x10CE9, 0x10CA9}, {0x10CEA, 0x10CAA}, {0x10CEB, 0x10CAB}, {0x10CEC, 0x10CAC}, 
	{0x10CED, 0x10CAD}, {0x10CEE, 0x10CAE}, {0x10CEF, 0x10CAF}, {0x10CF0, 0x10CB0}, 
	{0x10CF1, 0x10CB1}, {0x10CF2, 0x10CB2}, {0x118A0, 0x118C0}, {0x118A1, 0x118C1}, 
	{0x118A2, 0x118C2}, {0x118A3, 0x118C3}, {0x118A4, 0x118C4}, {0x118A5, 0x118C5}, 
	{0x118A6, 0x118C6}, {0x118A7, 0x118C7}, {0x118A8, 0x118C8}, {0x118A9, 0x118C9}, 
	{0x118AA, 0x118CA}, {0x118AB, 0x118CB}, {0x118AC, 0x118CC}, {0x118AD, 0x118CD}, 
	{0x118AE, 0x118CE}, {0x118AF, 0x118CF}, {0x118B0, 0x118D0}, {0x118B1, 0x118D1}, 
	{0x118B2, 0x118D2}, {0x118B3, 0x118D3}, {0x118B4, 0x118D4}, {0x118B5, 0x118D5}, 
	{0x118B6, 0x118D6}, {0x118B7, 0x118D7}, {0x118B8, 0x118D8}, {0x118B9, 0x118D9}, 
	{0x118BA, 0x118DA}, {0x118BB, 0x118DB}, {0x118BC, 0x118DC}, {0x118BD, 0x118DD}, 
	{0x118BE, 0x118DE}, {0x118BF, 0x118DF}, {0x118C0, 0x118A0}, {0x118C1, 0x118A1}, 
	{0x118C2, 0x118A2}, {0x118C3, 0x118A3}, {0x118C4, 0x118A4}, {0x118C5, 0x118A5}, 
	{0x118C6, 0x118A6}, {0x118C7, 0x118A7}, {0x118C8, 0x118A8}, {0x118C9, 0x118A9}, 
	{0x118CA, 0x118AA}, {0x118CB, 0x118AB}, {0x118CC, 0x118AC}, {0x118CD, 0x118AD}, 
	{0x118CE, 0x118AE}, {0x118CF, 0x118AF}, {0x118D0, 0x118B0}, {0x118D1, 0x118B1}, 
	{0x118D2, 0x118B2}, {0x118D3, 0x118B3}, {0x118D4, 0x118B4}, {0x118D5, 0x118B5}, 
	{0x118D6, 0x118B6}, {0x118D7, 0x118B7}, {0x118D8, 0x118B8}, {0x118D9, 0x118B9}, 
	{0x118DA, 0x118BA}, {0x118DB, 0x118BB}, {0x118DC, 0x118BC}, {0x118DD, 0x118BD}, 
	{0x118DE, 0x118BE}, {0x118DF, 0x118BF}, {0x16E40, 0x16E60}, {0x16E41, 0x16E61}, 
	{0x16E42, 0x16E62}, {0x16E43, 0x16E63}, {0x16E44, 0x16E64}, {0x16E45, 0x16E65}, 
	{0x16E46, 0x16E66}, {0x16E47, 0x16E67}, {0x16E48, 0x16E68}, {0x16E49, 0x16E69}, 
	{0x16E4A, 0x16E6A}, {0x16E4B, 0x16E6B}, {0x16E4C, 0x16E6C}, {0x16E4D, 0x16E6D}, 
	{0x16E4E, 0x16E6E}, {0x16E4F, 0x16E6F}, {0x16E50, 0x16E70}, {0x16E51, 0x16E71}, 
	{0x16E52, 0x16E72}, {0x16E53, 0x16E73}, {0x16E54, 0x16E74}, {0x16E55, 0x16E75}, 
	{0x16E56, 0x16E76}, {0x16E57, 0x16E77}, {0x16E58, 0x16E78}, {0x16E59, 0x16E79}, 
	{0x16E5A, 0x16E7A}, {0x16E5B, 0x16E7B}, {0x16E5C, 0x16E7C}, {0x16E5D, 0x16E7D}, 
	{0x16E5E, 0x16E7E}, {0x16E5F, 0x16E7F}, {0x16E60, 0x16E40}, {0x16E61, 0x16E41}, 
	{0x16E62, 0x16E42}, {0x16E63, 0x16E43}, {0x16E64, 0x16E44}, {0x16E65, 0x16E45}, 
	{0x16E66, 0x16E46}, {0x16E67, 0x16E47}, {0x16E68, 0x16E48}, {0x16E69, 0x16E49}, 
	{0x16E6A, 0x16E4A}, {0x16E6B, 0x16E4B}, {0x16E6C, 0x16E4C}, {0x16E6D, 0x16E4D}, 
	{0x16E6E, 0x16E4E}, {0x16E6F, 0x16E4F}, {0x16E70, 0x16E50}, {0x16E71, 0x16E51}, 
	{0x16E72, 0x16E52}, {0x16E73, 0x16E53}, {0x16E74, 0x16E54}, {0x16E75, 0x16E55}, 
	{0x16E76, 0x16E56}, {0x16E77, 0x16E57}, {0x16E78, 0x16E58}, {0x16E79, 0x16E59}, 
	{0x16E7A, 0x16E5A}, {0x16E7B, 0x16E5B}, {0x16E7C, 0x16E5C}, {0x16E7D, 0x16E5D}, 
	{0x16E7E, 0x16E5E}, {0x16E7F, 0x16E5F}, {0x1E900, 0x1E922}, {0x1E901, 0x1E923}, 
	{0x1E902, 0x1E924}, {0x1E903, 0x1E925}, {0x1E904, 0x1E926}, {0x1E905, 0x1E927}, 
	{0x1E906, 0x1E928}, {0x1E907, 0x1E929}, {0x1E908, 0x1E92A}, {0x1E909, 0x1E92B}, 
	{0x1E90A, 0x1E92C}, {0x1E90B, 0x1E92D}, {0x1E90C, 0x1E92E}, {0x1E90D, 0x1E92F}, 
	{0x1E90E, 0x1E930}, {0x1E90F, 0x1E931}, {0x1E910, 0x1E932}, {0x1E911, 0x1E933}, 
	{0x1E912, 0x1E934}, {0x1E913, 0x1E935}, {0x1E914, 0x1E936}, {0x1E915, 0x1E937}, 
	{0x1E916, 0x1E938}, {0x1E917, 0x1E939}, {0x1E918, 0x1E93A}, {0x1E919, 0x1E93B}, 
	{0x1E91A, 0x1E93C}, {0x1E91B, 0x1E93D}, {0x1E91C, 0x1E93E}, {0x1E91D, 0x1E93F}, 
	{0x1E91E, 0x1E940}, {0x1E91F, 0x1E941}, {0x1E920, 0x1E942}, {0x1E921, 0x1E943}, 
	{0x1E922, 0x1E900}, {0x1E923, 0x1E901}, {0x1E924, 0x1E902}, {0x1E925, 0x1E903}, 
	{0x1E926, 0x1E904}, {0x1E927, 0x1E905}, {0x1E928, 0x1E906}, {0x1E929, 0x1E907}, 
	{0x1E92A, 0x1E908}, {0x1E92B, 0x1E909}, {0x1E92C, 0x1E90A}, {0x1E92D, 0x1E90B}, 
	{0x1E92E, 0x1E90C}, {0x1E92F, 0x1E90D}, {0x1E930, 0x1E90E}, {0x1E931, 0x1E90F}, 
	{0x1E932, 0x1E910}, {0x1E933, 0x1E911}, {0x1E934, 0x1E912}, {0x1E935, 0x1E913}, 
	{0x1E936, 0x1E914}, {0x1E937, 0x1E915}, {0x1E938, 0x1E916}, {0x1E939, 0x1E917}, 
	{0x1E93A, 0x1E918}, {0x1E93B, 0x1E919}, {0x1E93C, 0x1E91A}, {0x1E93D, 0x1E91B}, 
	{0x1E93E, 0x1E91C}, {0x1E93F, 0x1E91D}, {0x1E940, 0x1E91E}, {0x1E941, 0x1E91F}, 
	{0x1E942, 0x1E920}, {0x1E943, 0x1E921}, 
};
static const int32_t guji_fold_pair_count = 2878;

static const guji_gcb_range_t guji_gcb_ranges[] = {
	{0x0000, 0x0009, 3}, {0x000A, 0x000A, 2}, {0x000B, 0x000C, 3}, {0x000D, 0x000D, 1}, 
	{0x000E, 0x001F, 3}, {0x007F, 0x009F, 3}, {0x00AD, 0x00AD, 3}, {0x0300, 0x036F, 4}, 
	{0x0483, 0x0489, 4}, {0x0591, 0x05BD, 4}, {0x05BF, 0x05BF, 4}, {0x05C1, 0x05C2, 4}, 
	{0x05C4, 0x05C5, 4}, {0x05C7, 0x05C7, 4}, {0x0600, 0x0605, 7}, {0x0610, 0x061A, 4}, 
	{0x061C, 0x061C, 3}, {0x064B, 0x065F, 4}, {0x0670, 0x0670, 4}, {0x06D6, 0x06DC, 4}, 
	{0x06DD, 0x06DD, 7}, {0x06DF, 0x06E4, 4}, {0x06E7, 0x06E8, 4}, {0x06EA, 0x06ED, 4}, 
	{0x070F, 0x070F, 7}, {0x0711, 0x0711, 4}, {0x0730, 0x074A, 4}, {0x07A6, 0x07B0, 4}, 
	{0x07EB, 0x07F3, 4}, {0x07FD, 0x07FD, 4}, {0x0816, 0x0819, 4}, {0x081B, 0x0823, 4}, 
	{0x0825, 0x0827, 4}, {0x0829, 0x082D, 4}, {0x0859, 0x085B, 4}, {0x0890, 0x0891, 7}, 
	{0x0898, 0x089F, 4}, {0x08CA, 0x08E1, 4}, {0x08E2, 0x08E2, 7}, {0x08E3, 0x0902, 4}, 
	{0x0903, 0x0903, 8}, {0x093A, 0x093A, 4}, {0x093B, 0x093B, 8}, {0x093C, 0x093C, 4}, 
	{0x093E, 0x0940, 8}, {0x0941, 0x0948, 4}, {0x0949, 0x094C, 8}, {0x094D, 0x094D, 4}, 
	{0x094E, 0x094F, 8}, {0x0951, 0x0957, 4}, {0x0962, 0x0963, 4}, {0x0981, 0x0981, 4}, 
	{0x0982, 0x0983, 8}, {0x09BC, 0x09BC, 4}, {0x09BE, 0x09BE, 4}, {0x09BF, 0x09C0, 8}, 
	{0x09C1, 0x09C4, 4}, {0x09C7, 0x09C8, 8}, {0x09CB, 0x09CC, 8}, {0x09CD, 0x09CD, 4}, 
	{0x09D7, 0x09D7, 4}, {0x09E2, 0x09E3, 4}, {0x09FE, 0x09FE, 4}, {0x0A01, 0x0A02, 4}, 
	{0x0A03, 0x0A03, 8}, {0x0A3C, 0x0A3C, 4}, {0x0A3E, 0x0A40, 8}, {0x0A41, 0x0A42, 4}, 
	{0x0A47, 0x0A48, 4}, {0x0A4B, 0x0A4D, 4}, {0x0A51, 0x0A51, 4}, {0x0A70, 0x0A71, 4}, 
	{0x0A75, 0x0A75, 4}, {0x0A81, 0x0A82, 4}, {0x0A83, 0x0A83, 8}, {0x0ABC, 0x0ABC, 4}, 
	{0x0ABE, 0x0AC0, 8}, {0x0AC1, 0x0AC5, 4}, {0x0AC7, 0x0AC8, 4}, {0x0AC9, 0x0AC9, 8}, 
	{0x0ACB, 0x0ACC, 8}, {0x0ACD, 0x0ACD, 4}, {0x0AE2, 0x0AE3, 4}, {0x0AFA, 0x0AFF, 4}, 
	{0x0B01, 0x0B01, 4}, {0x0B02, 0x0B03, 8}, {0x0B3C, 0x0B3C, 4}, {0x0B3E, 0x0B3F, 4}, 
	{0x0B40, 0x0B40, 8}, {0x0B41, 0x0B44, 4}, {0x0B47, 0x0B48, 8}, {0x0B4B, 0x0B4C, 8}, 
	{0x0B4D, 0x0B4D, 4}, {0x0B55, 0x0B57, 4}, {0x0B62, 0x0B63, 4}, {0x0B82, 0x0B82, 4}, 
	{0x0BBE, 0x0BBE, 4}, {0x0BBF, 0x0BBF, 8}, {0x0BC0, 0x0BC0, 4}, {0x0BC1, 0x0BC2, 8}, 
	{0x0BC6, 0x0BC8, 8}, {0x0BCA, 0x0BCC, 8}, {0x0BCD, 0x0BCD, 4}, {0x0BD7, 0x0BD7, 4}, 
	{0x0C00, 0x0C00, 4}, {0x0C01, 0x0C03, 8}, {0x0C04, 0x0C04, 4}, {0x0C3C, 0x0C3C, 4}, 
	{0x0C3E, 0x0C40, 4}, {0x0C41, 0x0C44, 8}, {0x0C46, 0x0C48, 4}, {0x0C4A, 0x0C4D, 4}, 
	{0x0C55, 0x0C56, 4}, {0x0C62, 0x0C63, 4}, {0x0C81, 0x0C81, 4}, {0x0C82, 0x0C83, 8}, 
	{0x0CBC, 0x0CBC, 4}, {0x0CBE, 0x0CBE, 8}, {0x0CBF, 0x0CBF, 4}, {0x0CC0, 0x0CC1, 8}, 
	{0x0CC2, 0x0CC2, 4}, {0x0CC3, 0x0CC4, 8}, {0x0CC6, 0x0CC6, 4}, {0x0CC7, 0x0CC8, 8}, 
	{0x0CCA, 0x0CCB, 8}, {0x0CCC, 0x0CCD, 4}, {0x0CD5, 0x0CD6, 4}, {0x0CE2, 0x0CE3, 4}, 
	{0x0CF3, 0x0CF3, 8}, {0x0D00, 0x0D01, 4}, {0x0D02, 0x0D03, 8}, {0x0D3B, 0x0D3C, 4}, 
	{0x0D3E, 0x0D3E, 4}, {0x0D3F, 0x0D40, 8}, {0x0D41, 0x0D44, 4}, {0x0D46, 0x0D48, 8}, 
	{0x0D4A, 0x0D4C, 8}, {0x0D4D, 0x0D4D, 4}, {0x0D4E, 0x0D4E, 7}, {0x0D57, 0x0D57, 4}, 
	{0x0D62, 0x0D63, 4}, {0x0D81, 0x0D81, 4}, {0x0D82, 0x0D83, 8}, {0x0DCA, 0x0DCA, 4}, 
	{0x0DCF, 0x0DCF, 4}, {0x0DD0, 0x0DD1, 8}, {0x0DD2, 0x0DD4, 4}, {0x0DD6, 0x0DD6, 4}, 
	{0x0DD8, 0x0DDE, 8}, {0x0DDF, 0x0DDF, 4}, {0x0DF2, 0x0DF3, 8}, {0x0E31, 0x0E31, 4}, 
	{0x0E33, 0x0E33, 8}, {0x0E34, 0x0E3A, 4}, {0x0E47, 0x0E4E, 4}, {0x0EB1, 0x0EB1, 4}, 
	{0x0EB3, 0x0EB3, 8}, {0x0EB4, 0x0EBC, 4}, {0x0EC8, 0x0ECE, 4}, {0x0F18, 0x0F19, 4}, 
	{0x0F35, 0x0F35, 4}, {0x0F37, 0x0F37, 4}, {0x0F39, 0x0F39, 4}, {0x0F3E, 0x0F3F, 8}, 
	{0x0F71, 0x0F7E, 4}, {0x0F7F, 0x0F7F, 8}, {0x0F80, 0x0F84, 4}, {0x0F86, 0x0F87, 4}, 
	{0x0F8D, 0x0F97, 4}, {0x0F99, 0x0FBC, 4}, {0x0FC6, 0x0FC6, 4}, {0x102D, 0x1030, 4}, 
	{0x1031, 0x1031, 8}, {0x1032, 0x1037, 4}, {0x1039, 0x103A, 4}, {0x103B, 0x103C, 8}, 
	{0x103D, 0x103E, 4}, {0x1056, 0x1057, 8}, {0x1058, 0x1059, 4}, {0x105E, 0x1060, 4}, 
	{0x1071, 0x1074, 4}, {0x1082, 0x1082, 4}, {0x1084, 0x1084, 8}, {0x1085, 0x1086, 4}, 
	{0x108D, 0x108D, 4}, {0x109D, 0x109D, 4}, {0x1100, 0x115F, 9}, {0x1160, 0x11A7, 10}, 
	{0x11A8, 0x11FF, 11}, {0x135D, 0x135F, 4}, {0x1712, 0x1714, 4}, {0x1715, 0x1715, 8}, 
	{0x1732, 0x1733, 4}, {0x1734, 0x1734, 8}, {0x1752, 0x1753, 4}, {0x1772, 0x1773, 4}, 
	{0x17B4, 0x17B5, 4}, {0x17B6, 0x17B6, 8}, {0x17B7, 0x17BD, 4}, {0x17BE, 0x17C5, 8}, 
	{0x17C6, 0x17C6, 4}, {0x17C7, 0x17C8, 8}, {0x17C9, 0x17D3, 4}, {0x17DD, 0x17DD, 4}, 
	{0x180B, 0x180D, 4}, {0x180E, 0x180E, 3}, {0x180F, 0x180F, 4}, {0x1885, 0x1886, 4}, 
	{0x18A9, 0x18A9, 4}, {0x1920, 0x1922, 4}, {0x1923, 0x1926, 8}, {0x1927, 0x1928, 4}, 
	{0x1929, 0x192B, 8}, {0x1930, 0x1931, 8}, {0x1932, 0x1932, 4}, {0x1933, 0x1938, 8}, 
	{0x1939, 0x193B, 4}, {0x1A17, 0x1A18, 4}, {0x1A19, 0x1A1A, 8}, {0x1A1B, 0x1A1B, 4}, 
	{0x1A55, 0x1A55, 8}, {0x1A56, 0x1A56, 4}, {0x1A57, 0x1A57, 8}, {0x1A58, 0x1A5E, 4}, 
	{0x1A60, 0x1A60, 4}, {0x1A62, 0x1A62, 4}, {0x1A65, 0x1A6C, 4}, {0x1A6D, 0x1A72, 8}, 
	{0x1A73, 0x1A7C, 4}, {0x1A7F, 0x1A7F, 4}, {0x1AB0, 0x1ACE, 4}, {0x1B00, 0x1B03, 4}, 
	{0x1B04, 0x1B04, 8}, {0x1B34, 0x1B3A, 4}, {0x1B3B, 0x1B3B, 8}, {0x1B3C, 0x1B3C, 4}, 
	{0x1B3D, 0x1B41, 8}, {0x1B42, 0x1B42, 4}, {0x1B43, 0x1B44, 8}, {0x1B6B, 0x1B73, 4}, 
	{0x1B80, 0x1B81, 4}, {0x1B82, 0x1B82, 8}, {0x1BA1, 0x1BA1, 8}, {0x1BA2, 0x1BA5, 4}, 
	{0x1BA6, 0x1BA7, 8}, {0x1BA8, 0x1BA9, 4}, {0x1BAA, 0x1BAA, 8}, {0x1BAB, 0x1BAD, 4}, 
	{0x1BE6, 0x1BE6, 4}, {0x1BE7, 0x1BE7, 8}, {0x1BE8, 0x1BE9, 4}, {0x1BEA, 0x1BEC, 8}, 
	{0x1BED, 0x1BED, 4}, {0x1BEE, 0x1BEE, 8}, {0x1BEF, 0x1BF1, 4}, {0x1BF2, 0x1BF3, 8}, 
	{0x1C24, 0x1C2B, 8}, {0x1C2C, 0x1C33, 4}, {0x1C34, 0x1C35, 8}, {0x1C36, 0x1C37, 4}, 
	{0x1CD0, 0x1CD2, 4}, {0x1CD4, 0x1CE0, 4}, {0x1CE1, 0x1CE1, 8}, {0x1CE2, 0x1CE8, 4}, 
	{0x1CED, 0x1CED, 4}, {0x1CF4, 0x1CF4, 4}, {0x1CF7, 0x1CF7, 8}, {0x1CF8, 0x1CF9, 4}, 
	{0x1DC0, 0x1DFF, 4}, {0x200B, 0x200B, 3}, {0x200C, 0x200C, 4}, {0x200D, 0x200D, 5}, 
	{0x200E, 0x200F, 3}, {0x2028, 0x202E, 3}, {0x2060, 0x206F, 3}, {0x20D0, 0x20F0, 4}, 
	{0x2CEF, 0x2CF1, 4}, {0x2D7F, 0x2D7F, 4}, {0x2DE0, 0x2DFF, 4}, {0x302A, 0x302F, 4}, 
	{0x3099, 0x309A, 4}, {0xA66F, 0xA672, 4}, {0xA674, 0xA67D, 4}, {0xA69E, 0xA69F, 4}, 
	{0xA6F0, 0xA6F1, 4}, {0xA802, 0xA802, 4}, {0xA806, 0xA806, 4}, {0xA80B, 0xA80B, 4}, 
	{0xA823, 0xA824, 8}, {0xA825, 0xA826, 4}, {0xA827, 0xA827, 8}, {0xA82C, 0xA82C, 4}, 
	{0xA880, 0xA881, 8}, {0xA8B4, 0xA8C3, 8}, {0xA8C4, 0xA8C5, 4}, {0xA8E0, 0xA8F1, 4}, 
	{0xA8FF, 0xA8FF, 4}, {0xA926, 0xA92D, 4}, {0xA947, 0xA951, 4}, {0xA952, 0xA953, 8}, 
	{0xA960, 0xA97C, 9}, {0xA980, 0xA982, 4}, {0xA983, 0xA983, 8}, {0xA9B3, 0xA9B3, 4}, 
	{0xA9B4, 0xA9B5, 8}, {0xA9B6, 0xA9B9, 4}, {0xA9BA, 0xA9BB, 8}, {0xA9BC, 0xA9BD, 4}, 
	{0xA9BE, 0xA9C0, 8}, {0xA9E5, 0xA9E5, 4}, {0xAA29, 0xAA2E, 4}, {0xAA2F, 0xAA30, 8}, 
	{0xAA31, 0xAA32, 4}, {0xAA33, 0xAA34, 8}, {0xAA35, 0xAA36, 4}, {0xAA43, 0xAA43, 4}, 
	{0xAA4C, 0xAA4C, 4}, {0xAA4D, 0xAA4D, 8}, {0xAA7C, 0xAA7C, 4}, {0xAAB0, 0xAAB0, 4}, 
	{0xAAB2, 0xAAB4, 4}, {0xAAB7, 0xAAB8, 4}, {0xAABE, 0xAABF, 4}, {0xAAC1, 0xAAC1, 4}, 
	{0xAAEB, 0xAAEB, 8}, {0xAAEC, 0xAAED, 4}, {0xAAEE, 0xAAEF, 8}, {0xAAF5, 0xAAF5, 8}, 
	{0xAAF6, 0xAAF6, 4}, {0xABE3, 0xABE4, 8}, {0xABE5, 0xABE5, 4}, {0xABE6, 0xABE7, 8}, 
	{0xABE8, 0xABE8, 4}, {0xABE9, 0xABEA, 8}, {0xABEC, 0xABEC, 8}, {0xABED, 0xABED, 4}, 
	{0xAC00, 0xAC00, 12}, {0xAC01, 0xAC1B, 13}, {0xAC1C, 0xAC1C, 12}, {0xAC1D, 0xAC37, 13}, 
	{0xAC38, 0xAC38, 12}, {0xAC39, 0xAC53, 13}, {0xAC54, 0xAC54, 12}, {0xAC55, 0xAC6F, 13}, 
	{0xAC70, 0xAC70, 12}, {0xAC71, 0xAC8B, 13}, {0xAC8C, 0xAC8C, 12}, {0xAC8D, 0xACA7, 13}, 
	{0xACA8, 0xACA8, 12}, {0xACA9, 0xACC3, 13}, {0xACC4, 0xACC4, 12}, {0xACC5, 0xACDF, 13}, 
	{0xACE0, 0xACE0, 12}, {0xACE1, 0xACFB, 13}, {0xACFC, 0xACFC, 12}, {0xACFD, 0xAD17, 13}, 
	{0xAD18, 0xAD18, 12}, {0xAD19, 0xAD33, 13}, {0xAD34, 0xAD34, 12}, {0xAD35, 0xAD4F, 13}, 
	{0xAD50, 0xAD50, 12}, {0xAD51, 0xAD6B, 13}, {0xAD6C, 0xAD6C, 12}, {0xAD6D, 0xAD87, 13}, 
	{0xAD88, 0xAD88, 12}, {0xAD89, 0xADA3, 13}, {0xADA4, 0xADA4, 12}, {0xADA5, 0xADBF, 13}, 
	{0xADC0, 0xADC0, 12}, {0xADC1, 0xADDB, 13}, {0xADDC, 0xADDC, 12}, {0xADDD, 0xADF7, 13}, 
	{0xADF8, 0xADF8, 12}, {0xADF9, 0xAE13, 13}, {0xAE14, 0xAE14, 12}, {0xAE15, 0xAE2F, 13}, 
	{0xAE30, 0xAE30, 12}, {0xAE31, 0xAE4B, 13}, {0xAE4C, 0xAE4C, 12}, {0xAE4D, 0xAE67, 13}, 
	{0xAE68, 0xAE68, 12}, {0xAE69, 0xAE83, 13}, {0xAE84, 0xAE84, 12}, {0xAE85, 0xAE9F, 13}, 
	{0xAEA0, 0xAEA0, 12}, {0xAEA1, 0xAEBB, 13}, {0xAEBC, 0xAEBC, 12}, {0xAEBD, 0xAED7, 13}, 
	{0xAED8, 0xAED8, 12}, {0xAED9, 0xAEF3, 13}, {0xAEF4, 0xAEF4, 12}, {0xAEF5, 0xAF0F, 13}, 
	{0xAF10, 0xAF10, 12}, {0xAF11, 0xAF2B, 13}, {0xAF2C, 0xAF2C, 12}, {0xAF2D, 0xAF47, 13}, 
	{0xAF48, 0xAF48, 12}, {0xAF49, 0xAF63, 13}, {0xAF64, 0xAF64, 12}, {0xAF65, 0xAF7F, 13}, 
	{0xAF80, 0xAF80, 12}, {0xAF81, 0xAF9B, 13}, {0xAF9C, 0xAF9C, 12}, {0xAF9D, 0xAFB7, 13}, 
	{0xAFB8, 0xAFB8, 12}, {0xAFB9, 0xAFD3, 13}, {0xAFD4, 0xAFD4, 12}, {0xAFD5, 0xAFEF, 13}, 
	{0xAFF0, 0xAFF0, 12}, {0xAFF1, 0xB00B, 13}, {0xB00C, 0xB00C, 12}, {0xB00D, 0xB027, 13}, 
	{0xB028, 0xB028, 12}, {0xB029, 0xB043, 13}, {0xB044, 0xB044, 12}, {0xB045, 0xB05F, 13}, 
	{0xB060, 0xB060, 12}, {0xB061, 0xB07B, 13}, {0xB07C, 0xB07C, 12}, {0xB07D, 0xB097, 13}, 
	{0xB098, 0xB098, 12}, {0xB099, 0xB0B3, 13}, {0xB0B4, 0xB0B4, 12}, {0xB0B5, 0xB0CF, 13}, 
	{0xB0D0, 0xB0D0, 12}, {0xB0D1, 0xB0EB, 13}, {0xB0EC, 0xB0EC, 12}, {0xB0ED, 0xB107, 13}, 
	{0xB108, 0xB108, 12}, {0xB109, 0xB123, 13}, {0xB124, 0xB124, 12}, {0xB125, 0xB13F, 13}, 
	{0xB140, 0xB140, 12}, {0xB141, 0xB15B, 13}, {0xB15C, 0xB15C, 12}, {0xB15D, 0xB177, 13}, 
	{0xB178, 0xB178, 12}, {0xB179, 0xB193, 13}, {0xB194, 0xB194, 12}, {0xB195, 0xB1AF, 13}, 
	{0xB1B0, 0xB1B0, 12}, {0xB1B1, 0xB1CB, 13}, {0xB1CC, 0xB1CC, 12}, {0xB1CD, 0xB1E7, 13}, 
	{0xB1E8, 0xB1E8, 12}, {0xB1E9, 0xB203, 13}, {0xB204, 0xB204, 12}, {0xB205, 0xB21F, 13}, 
	{0xB220, 0xB220, 12}, {0xB221, 0xB23B, 13}, {0xB23C, 0xB23C, 12}, {0xB23D, 0xB257, 13}, 
	{0xB258, 0xB258, 12}, {0xB259, 0xB273, 13}, {0xB274, 0xB274, 12}, {0xB275, 0xB28F, 13}, 
	{0xB290, 0xB290, 12}, {0xB291, 0xB2AB, 13}, {0xB2AC, 0xB2AC, 12}, {0xB2AD, 0xB2C7, 13}, 
	{0xB2C8, 0xB2C8, 12}, {0xB2C9, 0xB2E3, 13}, {0xB2E4, 0xB2E4, 12}, {0xB2E5, 0xB2FF, 13}, 
	{0xB300, 0xB300, 12}, {0xB301, 0xB31B, 13}, {0xB31C, 0xB31C, 12}, {0xB31D, 0xB337, 13}, 
	{0xB338, 0xB338, 12}, {0xB339, 0xB353, 13}, {0xB354, 0xB354, 12}, {0xB355, 0xB36F, 13}, 
	{0xB370, 0xB370, 12}, {0xB371, 0xB38B, 13}, {0xB38C, 0xB38C, 12}, {0xB38D, 0xB3A7, 13}, 
	{0xB3A8, 0xB3A8, 12}, {0xB3A9, 0xB3C3, 13}, {0xB3C4, 0xB3C4, 12}, {0xB3C5, 0xB3DF, 13}, 
	{0xB3E0, 0xB3E0, 12}, {0xB3E1, 0xB3FB, 13}, {0xB3FC, 0xB3FC, 12}, {0xB3FD, 0xB417, 13}, 
	{0xB418, 0xB418, 12}, {0xB419, 0xB433, 13}, {0xB434, 0xB434, 12}, {0xB435, 0xB44F, 13}, 
	{0xB450, 0xB450, 12}, {0xB451, 0xB46B, 13}, {0xB46C, 0xB46C, 12}, {0xB46D, 0xB487, 13}, 
	{0xB488, 0xB488, 12}, {0xB489, 0xB4A3, 13}, {0xB4A4, 0xB4A4, 12}, {0xB4A5, 0xB4BF, 13}, 
	{0xB4C0, 0xB4C0, 12}, {0xB4C1, 0xB4DB, 13}, {0xB4DC, 0xB4DC, 12}, {0xB4DD, 0xB4F7, 13}, 
	{0xB4F8, 0xB4F8, 12}, {0xB4F9, 0xB513, 13}, {0xB514, 0xB514, 12}, {0xB515, 0xB52F, 13}, 
	{0xB530, 0xB530, 12}, {0xB531, 0xB54B, 13}, {0xB54C, 0xB54C, 12}, {0xB54D, 0xB567, 13}, 
	{0xB568, 0xB568, 12}, {0xB569, 0xB583, 13}, {0xB584, 0xB584, 12}, {0xB585, 0xB59F, 13}, 
	{0xB5A0, 0xB5A0, 12}, {0xB5A1, 0xB5BB, 13}, {0xB5BC, 0xB5BC, 12}, {0xB5BD, 0xB5D7, 13}, 
	{0xB5D8, 0xB5D8, 12}, {0xB5D9, 0xB5F3, 13}, {0xB5F4, 0xB5F4, 12}, {0xB5F5, 0xB60F, 13}, 
	{0xB610, 0xB610, 12}, {0xB611, 0xB62B, 13}, {0xB62C, 0xB62C, 12}, {0xB62D, 0xB647, 13}, 
	{0xB648, 0xB648, 12}, {0xB649, 0xB663, 13}, {0xB664, 0xB664, 12}, {0xB665, 0xB67F, 13}, 
	{0xB680, 0xB680, 12}, {0xB681, 0xB69B, 13}, {0xB69C, 0xB69C, 12}, {0xB69D, 0xB6B7, 13}, 
	{0xB6B8, 0xB6B8, 12}, {0xB6B9, 0xB6D3, 13}, {0xB6D4, 0xB6D4, 12}, {0xB6D5, 0xB6EF, 13}, 
	{0xB6F0, 0xB6F0, 12}, {0xB6F1, 0xB70B, 13}, {0xB70C, 0xB70C, 12}, {0xB70D, 0xB727, 13}, 
	{0xB728, 0xB728, 12}, {0xB729, 0xB743, 13}, {0xB744, 0xB744, 12}, {0xB745, 0xB75F, 13}, 
	{0xB760, 0xB760, 12}, {0xB761, 0xB77B, 13}, {0xB77C, 0xB77C, 12}, {0xB77D, 0xB797, 13}, 
	{0xB798, 0xB798, 12}, {0xB799, 0xB7B3, 13}, {0xB7B4, 0xB7B4, 12}, {0xB7B5, 0xB7CF, 13}, 
	{0xB7D0, 0xB7D0, 12}, {0xB7D1, 0xB7EB, 13}, {0xB7EC, 0xB7EC, 12}, {0xB7ED, 0xB807, 13}, 
	{0xB808, 0xB808, 12}, {0xB809, 0xB823, 13}, {0xB824, 0xB824, 12}, {0xB825, 0xB83F, 13}, 
	{0xB840, 0xB840, 12}, {0xB841, 0xB85B, 13}, {0xB85C, 0xB85C, 12}, {0xB85D, 0xB877, 13}, 
	{0xB878, 0xB878, 12}, {0xB879, 0xB893, 13}, {0xB894, 0xB894, 12}, {0xB895, 0xB8AF, 13}, 
	{0xB8B0, 0xB8B0, 12}, {0xB8B1, 0xB8CB, 13}, {0xB8CC, 0xB8CC, 12}, {0xB8CD, 0xB8E7, 13}, 
	{0xB8E8, 0xB8E8, 12}, {0xB8E9, 0xB903, 13}, {0xB904, 0xB904, 12}, {0xB905, 0xB91F, 13}, 
	{0xB920, 0xB920, 12}, {0xB921, 0xB93B, 13}, {0xB93C, 0xB93C, 12}, {0xB93D, 0xB957, 13}, 
	{0xB958, 0xB958, 12}, {0xB959, 0xB973, 13}, {0xB974, 0xB974, 12}, {0xB975, 0xB98F, 13}, 
	{0xB990, 0xB990, 12}, {0xB991, 0xB9AB, 13}, {0xB9AC, 0xB9AC, 12}, {0xB9AD, 0xB9C7, 13}, 
	{0xB9C8, 0xB9C8, 12}, {0xB9C9, 0xB9E3, 13}, {0xB9E4, 0xB9E4, 12}, {0xB9E5, 0xB9FF, 13}, 
	{0xBA00, 0xBA00, 12}, {0xBA01, 0xBA1B, 13}, {0xBA1C, 0xBA1C, 12}, {0xBA1D, 0xBA37, 13}, 
	{0xBA38, 0xBA38, 12}, {0xBA39, 0xBA53, 13}, {0xBA54, 0xBA54, 12}, {0xBA55, 0xBA6F, 13}, 
	{0xBA70, 0xBA70, 12}, {0xBA71, 0xBA8B, 13}, {0xBA8C, 0xBA8C, 12}, {0xBA8D, 0xBAA7, 13}, 
	{0xBAA8, 0xBAA8, 12}, {0xBAA9, 0xBAC3, 13}, {0xBAC4, 0xBAC4, 12}, {0xBAC5, 0xBADF, 13}, 
	{0xBAE0, 0xBAE0, 12}, {0xBAE1, 0xBAFB, 13}, {0xBAFC, 0xBAFC, 12}, {0xBAFD, 0xBB17, 13}, 
	{0xBB18, 0xBB18, 12}, {0xBB19, 0xBB33, 13}, {0xBB34, 0xBB34, 12}, {0xBB35, 0xBB4F, 13}, 
	{0xBB50, 0xBB50, 12}, {0xBB51, 0xBB6B, 13}, {0xBB6C, 0xBB6C, 12}, {0xBB6D, 0xBB87, 13}, 
	{0xBB88, 0xBB88, 12}, {0xBB89, 0xBBA3, 13}, {0xBBA4, 0xBBA4, 12}, {0xBBA5, 0xBBBF, 13}, 
	{0xBBC0, 0xBBC0, 12}, {0xBBC1, 0xBBDB, 13}, {0xBBDC, 0xBBDC, 12}, {0xBBDD, 0xBBF7, 13}, 
	{0xBBF8, 0xBBF8, 12}, {0xBBF9, 0xBC13, 13}, {0xBC14, 0xBC14, 12}, {0xBC15, 0xBC2F, 13}, 
	{0xBC30, 0xBC30, 12}, {0xBC31, 0xBC4B, 13}, {0xBC4C, 0xBC4C, 12}, {0xBC4D, 0xBC67, 13}, 
	{0xBC68, 0xBC68, 12}, {0xBC69, 0xBC83, 13}, {0xBC84, 0xBC84, 12}, {0xBC85, 0xBC9F, 13}, 
	{0xBCA0, 0xBCA0, 12}, {0xBCA1, 0xBCBB, 13}, {0xBCBC, 0xBCBC, 12}, {0xBCBD, 0xBCD7, 13}, 
	{0xBCD8, 0xBCD8, 12}, {0xBCD9, 0xBCF3, 13}, {0xBCF4, 0xBCF4, 12}, {0xBCF5, 0xBD0F, 13}, 
	{0xBD10, 0xBD10, 12}, {0xBD11, 0xBD2B, 13}, {0xBD2C, 0xBD2C, 12}, {0xBD2D, 0xBD47, 13}, 
	{0xBD48, 0xBD48, 12}, {0xBD49, 0xBD63, 13}, {0xBD64, 0xBD64, 12}, {0xBD65, 0xBD7F, 13}, 
	{0xBD80, 0xBD80, 12}, {0xBD81, 0xBD9B, 13}, {0xBD9C, 0xBD9C, 12}, {0xBD9D, 0xBDB7, 13}, 
	{0xBDB8, 0xBDB8, 12}, {0xBDB9, 0xBDD3, 13}, {0xBDD4, 0xBDD4, 12}, {0xBDD5, 0xBDEF, 13}, 
	{0xBDF0, 0xBDF0, 12}, {0xBDF1, 0xBE0B, 13}, {0xBE0C, 0xBE0C, 12}, {0xBE0D, 0xBE27, 13}, 
	{0xBE28, 0xBE28, 12}, {0xBE29, 0xBE43, 13}, {0xBE44, 0xBE44, 12}, {0xBE45, 0xBE5F, 13}, 
	{0xBE60, 0xBE60, 12}, {0xBE61, 0xBE7B, 13}, {0xBE7C, 0xBE7C, 12}, {0xBE7D, 0xBE97, 13}, 
	{0xBE98, 0xBE98, 12}, {0xBE99, 0xBEB3, 13}, {0xBEB4, 0xBEB4, 12}, {0xBEB5, 0xBECF, 13}, 
	{0xBED0, 0xBED0, 12}, {0xBED1, 0xBEEB, 13}, {0xBEEC, 0xBEEC, 12}, {0xBEED, 0xBF07, 13}, 
	{0xBF08, 0xBF08, 12}, {0xBF09, 0xBF23, 13}, {0xBF24, 0xBF24, 12}, {0xBF25, 0xBF3F, 13}, 
	{0xBF40, 0xBF40, 12}, {0xBF41, 0xBF5B, 13}, {0xBF5C, 0xBF5C, 12}, {0xBF5D, 0xBF77, 13}, 
	{0xBF78, 0xBF78, 12}, {0xBF79, 0xBF93, 13}, {0xBF94, 0xBF94, 12}, {0xBF95, 0xBFAF, 13}, 
	{0xBFB0, 0xBFB0, 12}, {0xBFB1, 0xBFCB, 13}, {0xBFCC, 0xBFCC, 12}, {0xBFCD, 0xBFE7, 13}, 
	{0xBFE8, 0xBFE8, 12}, {0xBFE9, 0xC003, 13}, {0xC004, 0xC004, 12}, {0xC005, 0xC01F, 13}, 
	{0xC020, 0xC020, 12}, {0xC021, 0xC03B, 13}, {0xC03C, 0xC03C, 12}, {0xC03D, 0xC057, 13}, 
	{0xC058, 0xC058, 12}, {0xC059, 0xC073, 13}, {0xC074, 0xC074, 12}, {0xC075, 0xC08F, 13}, 
	{0xC090, 0xC090, 12}, {0xC091, 0xC0AB, 13}, {0xC0AC, 0xC0AC, 12}, {0xC0AD, 0xC0C7, 13}, 
	{0xC0C8, 0xC0C8, 12}, {0xC0C9, 0xC0E3, 13}, {0xC0E4, 0xC0E4, 12}, {0xC0E5, 0xC0FF, 13}, 
	{0xC100, 0xC100, 12}, {0xC101, 0xC11B, 13}, {0xC11C, 0xC11C, 12}, {0xC11D, 0xC137, 13}, 
	{0xC138, 0xC138, 12}, {0xC139, 0xC153, 13}, {0xC154, 0xC154, 12}, {0xC155, 0xC16F, 13}, 
	{0xC170, 0xC170, 12}, {0xC171, 0xC18B, 13}, {0xC18C, 0xC18C, 12}, {0xC18D, 0xC1A7, 13}, 
	{0xC1A8, 0xC1A8, 12}, {0xC1A9, 0xC1C3, 13}, {0xC1C4, 0xC1C4, 12}, {0xC1C5, 0xC1DF, 13}, 
	{0xC1E0, 0xC1E0, 12}, {0xC1E1, 0xC1FB, 13}, {0xC1FC, 0xC1FC, 12}, {0xC1FD, 0xC217, 13}, 
	{0xC218, 0xC218, 12}, {0xC219, 0xC233, 13}, {0xC234, 0xC234, 12}, {0xC235, 0xC24F, 13}, 
	{0xC250, 0xC250, 12}, {0xC251, 0xC26B, 13}, {0xC26C, 0xC26C, 12}, {0xC26D, 0xC287, 13}, 
	{0xC288, 0xC288, 12}, {0xC289, 0xC2A3, 13}, {0xC2A4, 0xC2A4, 12}, {0xC2A5, 0xC2BF, 13}, 
	{0xC2C0, 0xC2C0, 12}, {0xC2C1, 0xC2DB, 13}, {0xC2DC, 0xC2DC, 12}, {0xC2DD, 0xC2F7, 13}, 
	{0xC2F8, 0xC2F8, 12}, {0xC2F9, 0xC313, 13}, {0xC314, 0xC314, 12}, {0xC315, 0xC32F, 13}, 
	{0xC330, 0xC330, 12}, {0xC331, 0xC34B, 13}, {0xC34C, 0xC34C, 12}, {0xC34D, 0xC367, 13}, 
	{0xC368, 0xC368, 12}, {0xC369, 0xC383, 13}, {0xC384, 0xC384, 12}, {0xC385, 0xC39F, 13}, 
	{0xC3A0, 0xC3A0, 12}, {0xC3A1, 0xC3BB, 13}, {0xC3BC, 0xC3BC, 12}, {0xC3BD, 0xC3D7, 13}, 
	{0xC3D8, 0xC3D8, 12}, {0xC3D9, 0xC3F3, 13}, {0xC3F4, 0xC3F4, 12}, {0xC3F5, 0xC40F, 13}, 
	{0xC410, 0xC410, 12}, {0xC411, 0xC42B, 13}, {0xC42C, 0xC42C, 12}, {0xC42D, 0xC447, 13}, 
	{0xC448, 0xC448, 12}, {0xC449, 0xC463, 13}, {0xC464, 0xC464, 12}, {0xC465, 0xC47F, 13}, 
	{0xC480, 0xC480, 12}, {0xC481, 0xC49B, 13}, {0xC49C, 0xC49C, 12}, {0xC49D, 0xC4B7, 13}, 
	{0xC4B8, 0xC4B8, 12}, {0xC4B9, 0xC4D3, 13}, {0xC4D4, 0xC4D4, 12}, {0xC4D5, 0xC4EF, 13}, 
	{0xC4F0, 0xC4F0, 12}, {0xC4F1, 0xC50B, 13}, {0xC50C, 0xC50C, 12}, {0xC50D, 0xC527, 13}, 
	{0xC528, 0xC528, 12}, {0xC529, 0xC543, 13}, {0xC544, 0xC544, 12}, {0xC545, 0xC55F, 13}, 
	{0xC560, 0xC560, 12}, {0xC561, 0xC57B, 13}, {0xC57C, 0xC57C, 12}, {0xC57D, 0xC597, 13}, 
	{0xC598, 0xC598, 12}, {0xC599, 0xC5B3, 13}, {0xC5B4, 0xC5B4, 12}, {0xC5B5, 0xC5CF, 13}, 
	{0xC5D0, 0xC5D0, 12}, {0xC5D1, 0xC5EB, 13}, {0xC5EC, 0xC5EC, 12}, {0xC5ED, 0xC607, 13}, 
	{0xC608, 0xC608, 12}, {0xC609, 0xC623, 13}, {0xC624, 0xC624, 12}, {0xC625, 0xC63F, 13}, 
	{0xC640, 0xC640, 12}, {0xC641, 0xC65B, 13}, {0xC65C, 0xC65C, 12}, {0xC65D, 0xC677, 13}, 
	{0xC678, 0xC678, 12}, {0xC679, 0xC693, 13}, {0xC694, 0xC694, 12}, {0xC695, 0xC6AF, 13}, 
	{0xC6B0, 0xC6B0, 12}, {0xC6B1, 0xC6CB, 13}, {0xC6CC, 0xC6CC, 12}, {0xC6CD, 0xC6E7, 13}, 
	{0xC6E8, 0xC6E8, 12}, {0xC6E9, 0xC703, 13}, {0xC704, 0xC704, 12}, {0xC705, 0xC71F, 13}, 
	{0xC720, 0xC720, 12}, {0xC721, 0xC73B, 13}, {0xC73C, 0xC73C, 12}, {0xC73D, 0xC757, 13}, 
	{0xC758, 0xC758, 12}, {0xC759, 0xC773, 13}, {0xC774, 0xC774, 12}, {0xC775, 0xC78F, 13}, 
	{0xC790, 0xC790, 12}, {0xC791, 0xC7AB, 13}, {0xC7AC, 0xC7AC, 12}, {0xC7AD, 0xC7C7, 13}, 
	{0xC7C8, 0xC7C8, 12}, {0xC7C9, 0xC7E3, 13}, {0xC7E4, 0xC7E4, 12}, {0xC7E5, 0xC7FF, 13}, 
	{0xC800, 0xC800, 12}, {0xC801, 0xC81B, 13}, {0xC81C, 0xC81C, 12}, {0xC81D, 0xC837, 13}, 
	{0xC838, 0xC838, 12}, {0xC839, 0xC853, 13}, {0xC854, 0xC854, 12}, {0xC855, 0xC86F, 13}, 
	{0xC870, 0xC870, 12}, {0xC871, 0xC88B, 13}, {0xC88C, 0xC88C, 12}, {0xC88D, 0xC8A7, 13}, 
	{0xC8A8, 0xC8A8, 12}, {0xC8A9, 0xC8C3, 13}, {0xC8C4, 0xC8C4, 12}, {0xC8C5, 0xC8DF, 13}, 
	{0xC8E0, 0xC8E0, 12}, {0xC8E1, 0xC8FB, 13}, {0xC8FC, 0xC8FC, 12}, {0xC8FD, 0xC917, 13}, 
	{0xC918, 0xC918, 12}, {0xC919, 0xC933, 13}, {0xC934, 0xC934, 12}, {0xC935, 0xC94F, 13}, 
	{0xC950, 0xC950, 12}, {0xC951, 0xC96B, 13}, {0xC96C, 0xC96C, 12}, {0xC96D, 0xC987, 13}, 
	{0xC988, 0xC988, 12}, {0xC989, 0xC9A3, 13}, {0xC9A4, 0xC9A4, 12}, {0xC9A5, 0xC9BF, 13}, 
	{0xC9C0, 0xC9C0, 12}, {0xC9C1, 0xC9DB, 13}, {0xC9DC, 0xC9DC, 12}, {0xC9DD, 0xC9F7, 13}, 
	{0xC9F8, 0xC9F8, 12}, {0xC9F9, 0xCA13, 13}, {0xCA14, 0xCA14, 12}, {0xCA15, 0xCA2F, 13}, 
	{0xCA30, 0xCA30, 12}, {0xCA31, 0xCA4B, 13}, {0xCA4C, 0xCA4C, 12}, {0xCA4D, 0xCA67, 13}, 
	{0xCA68, 0xCA68, 12}, {0xCA69, 0xCA83, 13}, {0xCA84, 0xCA84, 12}, {0xCA85, 0xCA9F, 13}, 
	{0xCAA0, 0xCAA0, 12}, {0xCAA1, 0xCABB, 13}, {0xCABC, 0xCABC, 12}, {0xCABD, 0xCAD7, 13}, 
	{0xCAD8, 0xCAD8, 12}, {0xCAD9, 0xCAF3, 13}, {0xCAF4, 0xCAF4, 12}, {0xCAF5, 0xCB0F, 13}, 
	{0xCB10, 0xCB10, 12}, {0xCB11, 0xCB2B, 13}, {0xCB2C, 0xCB2C, 12}, {0xCB2D, 0xCB47, 13}, 
	{0xCB48, 0xCB48, 12}, {0xCB49, 0xCB63, 13}, {0xCB64, 0xCB64, 12}, {0xCB65, 0xCB7F, 13}, 
	{0xCB80, 0xCB80, 12}, {0xCB81, 0xCB9B, 13}, {0xCB9C, 0xCB9C, 12}, {0xCB9D, 0xCBB7, 13}, 
	{0xCBB8, 0xCBB8, 12}, {0xCBB9, 0xCBD3, 13}, {0xCBD4, 0xCBD4, 12}, {0xCBD5, 0xCBEF, 13}, 
	{0xCBF0, 0xCBF0, 12}, {0xCBF1, 0xCC0B, 13}, {0xCC0C, 0xCC0C, 12}, {0xCC0D, 0xCC27, 13}, 
	{0xCC28, 0xCC28, 12}, {0xCC29, 0xCC43, 13}, {0xCC44, 0xCC44, 12}, {0xCC45, 0xCC5F, 13}, 
	{0xCC60, 0xCC60, 12}, {0xCC61, 0xCC7B, 13}, {0xCC7C, 0xCC7C, 12}, {0xCC7D, 0xCC97, 13}, 
	{0xCC98, 0xCC98, 12}, {0xCC99, 0xCCB3, 13}, {0xCCB4, 0xCCB4, 12}, {0xCCB5, 0xCCCF, 13}, 
	{0xCCD0, 0xCCD0, 12}, {0xCCD1, 0xCCEB, 13}, {0xCCEC, 0xCCEC, 12}, {0xCCED, 0xCD07, 13}, 
	{0xCD08, 0xCD08, 12}, {0xCD09, 0xCD23, 13}, {0xCD24, 0xCD24, 12}, {0xCD25, 0xCD3F, 13}, 
	{0xCD40, 0xCD40, 12}, {0xCD41, 0xCD5B, 13}, {0xCD5C, 0xCD5C, 12}, {0xCD5D, 0xCD77, 13}, 
	{0xCD78, 0xCD78, 12}, {0xCD79, 0xCD93, 13}, {0xCD94, 0xCD94, 12}, {0xCD95, 0xCDAF, 13}, 
	{0xCDB0, 0xCDB0, 12}, {0xCDB1, 0xCDCB, 13}, {0xCDCC, 0xCDCC, 12}, {0xCDCD, 0xCDE7, 13}, 
	{0xCDE8, 0xCDE8, 12}, {0xCDE9, 0xCE03, 13}, {0xCE04, 0xCE04, 12}, {0xCE05, 0xCE1F, 13}, 
	{0xCE20, 0xCE20, 12}, {0xCE21, 0xCE3B, 13}, {0xCE3C, 0xCE3C, 12}, {0xCE3D, 0xCE57, 13}, 
	{0xCE58, 0xCE58, 12}, {0xCE59, 0xCE73, 13}, {0xCE74, 0xCE74, 12}, {0xCE75, 0xCE8F, 13}, 
	{0xCE90, 0xCE90, 12}, {0xCE91, 0xCEAB, 13}, {0xCEAC, 0xCEAC, 12}, {0xCEAD, 0xCEC7, 13}, 
	{0xCEC8, 0xCEC8, 12}, {0xCEC9, 0xCEE3, 13}, {0xCEE4, 0xCEE4, 12}, {0xCEE5, 0xCEFF, 13}, 
	{0xCF00, 0xCF00, 12}, {0xCF01, 0xCF1B, 13}, {0xCF1C, 0xCF1C, 12}, {0xCF1D, 0xCF37, 13}, 
	{0xCF38, 0xCF38, 12}, {0xCF39, 0xCF53, 13}, {0xCF54, 0xCF54, 12}, {0xCF55, 0xCF6F, 13}, 
	{0xCF70, 0xCF70, 12}, {0xCF71, 0xCF8B, 13}, {0xCF8C, 0xCF8C, 12}, {0xCF8D, 0xCFA7, 13}, 
	{0xCFA8, 0xCFA8, 12}, {0xCFA9, 0xCFC3, 13}, {0xCFC4, 0xCFC4, 12}, {0xCFC5, 0xCFDF, 13}, 
	{0xCFE0, 0xCFE0, 12}, {0xCFE1, 0xCFFB, 13}, {0xCFFC, 0xCFFC, 12}, {0xCFFD, 0xD017, 13}, 
	{0xD018, 0xD018, 12}, {0xD019, 0xD033, 13}, {0xD034, 0xD034, 12}, {0xD035, 0xD04F, 13}, 
	{0xD050, 0xD050, 12}, {0xD051, 0xD06B, 13}, {0xD06C, 0xD06C, 12}, {0xD06D, 0xD087, 13}, 
	{0xD088, 0xD088, 12}, {0xD089, 0xD0A3, 13}, {0xD0A4, 0xD0A4, 12}, {0xD0A5, 0xD0BF, 13}, 
	{0xD0C0, 0xD0C0, 12}, {0xD0C1, 0xD0DB, 13}, {0xD0DC, 0xD0DC, 12}, {0xD0DD, 0xD0F7, 13}, 
	{0xD0F8, 0xD0F8, 12}, {0xD0F9, 0xD113, 13}, {0xD114, 0xD114, 12}, {0xD115, 0xD12F, 13}, 
	{0xD130, 0xD130, 12}, {0xD131, 0xD14B, 13}, {0xD14C, 0xD14C, 12}, {0xD14D, 0xD167, 13}, 
	{0xD168, 0xD168, 12}, {0xD169, 0xD183, 13}, {0xD184, 0xD184, 12}, {0xD185, 0xD19F, 13}, 
	{0xD1A0, 0xD1A0, 12}, {0xD1A1, 0xD1BB, 13}, {0xD1BC, 0xD1BC, 12}, {0xD1BD, 0xD1D7, 13}, 
	{0xD1D8, 0xD1D8, 12}, {0xD1D9, 0xD1F3, 13}, {0xD1F4, 0xD1F4, 12}, {0xD1F5, 0xD20F, 13}, 
	{0xD210, 0xD210, 12}, {0xD211, 0xD22B, 13}, {0xD22C, 0xD22C, 12}, {0xD22D, 0xD247, 13}, 
	{0xD248, 0xD248, 12}, {0xD249, 0xD263, 13}, {0xD264, 0xD264, 12}, {0xD265, 0xD27F, 13}, 
	{0xD280, 0xD280, 12}, {0xD281, 0xD29B, 13}, {0xD29C, 0xD29C, 12}, {0xD29D, 0xD2B7, 13}, 
	{0xD2B8, 0xD2B8, 12}, {0xD2B9, 0xD2D3, 13}, {0xD2D4, 0xD2D4, 12}, {0xD2D5, 0xD2EF, 13}, 
	{0xD2F0, 0xD2F0, 12}, {0xD2F1, 0xD30B, 13}, {0xD30C, 0xD30C, 12}, {0xD30D, 0xD327, 13}, 
	{0xD328, 0xD328, 12}, {0xD329, 0xD343, 13}, {0xD344, 0xD344, 12}, {0xD345, 0xD35F, 13}, 
	{0xD360, 0xD360, 12}, {0xD361, 0xD37B, 13}, {0xD37C, 0xD37C, 12}, {0xD37D, 0xD397, 13}, 
	{0xD398, 0xD398, 12}, {0xD399, 0xD3B3, 13}, {0xD3B4, 0xD3B4, 12}, {0xD3B5, 0xD3CF, 13}, 
	{0xD3D0, 0xD3D0, 12}, {0xD3D1, 0xD3EB, 13}, {0xD3EC, 0xD3EC, 12}, {0xD3ED, 0xD407, 13}, 
	{0xD408, 0xD408, 12}, {0xD409, 0xD423, 13}, {0xD424, 0xD424, 12}, {0xD425, 0xD43F, 13}, 
	{0xD440, 0xD440, 12}, {0xD441, 0xD45B, 13}, {0xD45C, 0xD45C, 12}, {0xD45D, 0xD477, 13}, 
	{0xD478, 0xD478, 12}, {0xD479, 0xD493, 13}, {0xD494, 0xD494, 12}, {0xD495, 0xD4AF, 13}, 
	{0xD4B0, 0xD4B0, 12}, {0xD4B1, 0xD4CB, 13}, {0xD4CC, 0xD4CC, 12}, {0xD4CD, 0xD4E7, 13}, 
	{0xD4E8, 0xD4E8, 12}, {0xD4E9, 0xD503, 13}, {0xD504, 0xD504, 12}, {0xD505, 0xD51F, 13}, 
	{0xD520, 0xD520, 12}, {0xD521, 0xD53B, 13}, {0xD53C, 0xD53C, 12}, {0xD53D, 0xD557, 13}, 
	{0xD558, 0xD558, 12}, {0xD559, 0xD573, 13}, {0xD574, 0xD574, 12}, {0xD575, 0xD58F, 13}, 
	{0xD590, 0xD590, 12}, {0xD591, 0xD5AB, 13}, {0xD5AC, 0xD5AC, 12}, {0xD5AD, 0xD5C7, 13}, 
	{0xD5C8, 0xD5C8, 12}, {0xD5C9, 0xD5E3, 13}, {0xD5E4, 0xD5E4, 12}, {0xD5E5, 0xD5FF, 13}, 
	{0xD600, 0xD600, 12}, {0xD601, 0xD61B, 13}, {0xD61C, 0xD61C, 12}, {0xD61D, 0xD637, 13}, 
	{0xD638, 0xD638, 12}, {0xD639, 0xD653, 13}, {0xD654, 0xD654, 12}, {0xD655, 0xD66F, 13}, 
	{0xD670, 0xD670, 12}, {0xD671, 0xD68B, 13}, {0xD68C, 0xD68C, 12}, {0xD68D, 0xD6A7, 13}, 
	{0xD6A8, 0xD6A8, 12}, {0xD6A9, 0xD6C3, 13}, {0xD6C4, 0xD6C4, 12}, {0xD6C5, 0xD6DF, 13}, 
	{0xD6E0, 0xD6E0, 12}, {0xD6E1, 0xD6FB, 13}, {0xD6FC, 0xD6FC, 12}, {0xD6FD, 0xD717, 13}, 
	{0xD718, 0xD718, 12}, {0xD719, 0xD733, 13}, {0xD734, 0xD734, 12}, {0xD735, 0xD74F, 13}, 
	{0xD750, 0xD750, 12}, {0xD751, 0xD76B, 13}, {0xD76C, 0xD76C, 12}, {0xD76D, 0xD787, 13}, 
	{0xD788, 0xD788, 12}, {0xD789, 0xD7A3, 13}, {0xD7B0, 0xD7C6, 10}, {0xD7CB, 0xD7FB, 11}, 
	{0xFB1E, 0xFB1E, 4}, {0xFE00, 0xFE0F, 4}, {0xFE20, 0xFE2F, 4}, {0xFEFF, 0xFEFF, 3}, 
	{0xFF9E, 0xFF9F, 4}, {0xFFF0, 0xFFFB, 3}, {0x101FD, 0x101FD, 4}, {0x102E0, 0x102E0, 4}, 
	{0x10376, 0x1037A, 4}, {0x10A01, 0x10A03, 4}, {0x10A05, 0x10A06, 4}, {0x10A0C, 0x10A0F, 4}, 
	{0x10A38, 0x10A3A, 4}, {0x10A3F, 0x10A3F, 4}, {0x10AE5, 0x10AE6, 4}, {0x10D24, 0x10D27, 4}, 
	{0x10EAB, 0x10EAC, 4}, {0x10EFD, 0x10EFF, 4}, {0x10F46, 0x10F50, 4}, {0x10F82, 0x10F85, 4}, 
	{0x11000, 0x11000, 8}, {0x11001, 0x11001, 4}, {0x11002, 0x11002, 8}, {0x11038, 0x11046, 4}, 
	{0x11070, 0x11070, 4}, {0x11073, 0x11074, 4}, {0x1107F, 0x11081, 4}, {0x11082, 0x11082, 8}, 
	{0x110B0, 0x110B2, 8}, {0x110B3, 0x110B6, 4}, {0x110B7, 0x110B8, 8}, {0x110B9, 0x110BA, 4}, 
	{0x110BD, 0x110BD, 7}, {0x110C2, 0x110C2, 4}, {0x110CD, 0x110CD, 7}, {0x11100, 0x11102, 4}, 
	{0x11127, 0x1112B, 4}, {0x1112C, 0x1112C, 8}, {0x1112D, 0x11134, 4}, {0x11145, 0x11146, 8}, 
	{0x11173, 0x11173, 4}, {0x11180, 0x11181, 4}, {0x11182, 0x11182, 8}, {0x111B3, 0x111B5, 8}, 
	{0x111B6, 0x111BE, 4}, {0x111BF, 0x111C0, 8}, {0x111C2, 0x111C3, 7}, {0x111C9, 0x111CC, 4}, 
	{0x111CE, 0x111CE, 8}, {0x111CF, 0x111CF, 4}, {0x1122C, 0x1122E, 8}, {0x1122F, 0x11231, 4}, 
	{0x11232, 0x11233, 8}, {0x11234, 0x11234, 4}, {0x11235, 0x11235, 8}, {0x11236, 0x11237, 4}, 
	{0x1123E, 0x1123E, 4}, {0x11241, 0x11241, 4}, {0x112DF, 0x112DF, 4}, {0x112E0, 0x112E2, 8}, 
	{0x112E3, 0x112EA, 4}, {0x11300, 0x11301, 4}, {0x11302, 0x11303, 8}, {0x1133B, 0x1133C, 4}, 
	{0x1133E, 0x1133E, 4}, {0x1133F, 0x1133F, 8}, {0x11340, 0x11340, 4}, {0x11341, 0x11344, 8}, 
	{0x11347, 0x11348, 8}, {0x1134B, 0x1134D, 8}, {0x11357, 0x11357, 4}, {0x11362, 0x11363, 8}, 
	{0x11366, 0x1136C, 4}, {0x11370, 0x11374, 4}, {0x11435, 0x11437, 8}, {0x11438, 0x1143F, 4}, 
	{0x11440, 0x11441, 8}, {0x11442, 0x11444, 4}, {0x11445, 0x11445, 8}, {0x11446, 0x11446, 4}, 
	{0x1145E, 0x1145E, 4}, {0x114B0, 0x114B0, 4}, {0x114B1, 0x114B2, 8}, {0x114B3, 0x114B8, 4}, 
	{0x114B9, 0x114B9, 8}, {0x114BA, 0x114BA, 4}, {0x114BB, 0x114BC, 8}, {0x114BD, 0x114BD, 4}, 
	{0x114BE, 0x114BE, 8}, {0x114BF, 0x114C0, 4}, {0x114C1, 0x114C1, 8}, {0x114C2, 0x114C3, 4}, 
	{0x115AF, 0x115AF, 4}, {0x115B0, 0x115B1, 8}, {0x115B2, 0x115B5, 4}, {0x115B8, 0x115BB, 8}, 
	{0x115BC, 0x115BD, 4}, {0x115BE, 0x115BE, 8}, {0x115BF, 0x115C0, 4}, {0x115DC, 0x115DD, 4}, 
	{0x11630, 0x11632, 8}, {0x11633, 0x1163A, 4}, {0x1163B, 0x1163C, 8}, {0x1163D, 0x1163D, 4}, 
	{0x1163E, 0x1163E, 8}, {0x1163F, 0x11640, 4}, {0x116AB, 0x116AB, 4}, {0x116AC, 0x116AC, 8}, 
	{0x116AD, 0x116AD, 4}, {0x116AE, 0x116AF, 8}, {0x116B0, 0x116B5, 4}, {0x116B6, 0x116B6, 8}, 
	{0x116B7, 0x116B7, 4}, {0x1171D, 0x1171F, 4}, {0x11722, 0x11725, 4}, {0x11726, 0x11726, 8}, 
	{0x11727, 0x1172B, 4}, {0x1182C, 0x1182E, 8}, {0x1182F, 0x11837, 4}, {0x11838, 0x11838, 8}, 
	{0x11839, 0x1183A, 4}, {0x11930, 0x11930, 4}, {0x11931, 0x11935, 8}, {0x11937, 0x11938, 8}, 
	{0x1193B, 0x1193C, 4}, {0x1193D, 0x1193D, 8}, {0x1193E, 0x1193E, 4}, {0x1193F, 0x1193F, 7}, 
	{0x11940, 0x11940, 8}, {0x11941, 0x11941, 7}, {0x11942, 0x11942, 8}, {0x11943, 0x11943, 4}, 
	{0x119D1, 0x119D3, 8}, {0x119D4, 0x119D7, 4}, {0x119DA, 0x119DB, 4}, {0x119DC, 0x119DF, 8}, 
	{0x119E0, 0x119E0, 4}, {0x119E4, 0x119E4, 8}, {0x11A01, 0x11A0A, 4}, {0x11A33, 0x11A38, 4}, 
	{0x11A39, 0x11A39, 8}, {0x11A3A, 0x11A3A, 7}, {0x11A3B, 0x11A3E, 4}, {0x11A47, 0x11A47, 4}, 
	{0x11A51, 0x11A56, 4}, {0x11A57, 0x11A58, 8}, {0x11A59, 0x11A5B, 4}, {0x11A84, 0x11A89, 7}, 
	{0x11A8A, 0x11A96, 4}, {0x11A97, 0x11A97, 8}, {0x11A98, 0x11A99, 4}, {0x11C2F, 0x11C2F, 8}, 
	{0x11C30, 0x11C36, 4}, {0x11C38, 0x11C3D, 4}, {0x11C3E, 0x11C3E, 8}, {0x11C3F, 0x11C3F, 4}, 
	{0x11C92, 0x11CA7, 4}, {0x11CA9, 0x11CA9, 8}, {0x11CAA, 0x11CB0, 4}, {0x11CB1, 0x11CB1, 8}, 
	{0x11CB2, 0x11CB3, 4}, {0x11CB4, 0x11CB4, 8}, {0x11CB5, 0x11CB6, 4}, {0x11D31, 0x11D36, 4}, 
	{0x11D3A, 0x11D3A, 4}, {0x11D3C, 0x11D3D, 4}, {0x11D3F, 0x11D45, 4}, {0x11D46, 0x11D46, 7}, 
	{0x11D47, 0x11D47, 4}, {0x11D8A, 0x11D8E, 8}, {0x11D90, 0x11D91, 4}, {0x11D93, 0x11D94, 8}, 
	{0x11D95, 0x11D95, 4}, {0x11D96, 0x11D96, 8}, {0x11D97, 0x11D97, 4}, {0x11EF3, 0x11EF4, 4}, 
	{0x11EF5, 0x11EF6, 8}, {0x11F00, 0x11F01, 4}, {0x11F02, 0x11F02, 7}, {0x11F03, 0x11F03, 8}, 
	{0x11F34, 0x11F35, 8}, {0x11F36, 0x11F3A, 4}, {0x11F3E, 0x11F3F, 8}, {0x11F40, 0x11F40, 4}, 
	{0x11F41, 0x11F41, 8}, {0x11F42, 0x11F42, 4}, {0x13430, 0x1343F, 3}, {0x13440, 0x13440, 4}, 
	{0x13447, 0x13455, 4}, {0x16AF0, 0x16AF4, 4}, {0x16B30, 0x16B36, 4}, {0x16F4F, 0x16F4F, 4}, 
	{0x16F51, 0x16F87, 8}, {0x16F8F, 0x16F92, 4}, {0x16FE4, 0x16FE4, 4}, {0x16FF0, 0x16FF1, 8}, 
	{0x1BC9D, 0x1BC9E, 4}, {0x1BCA0, 0x1BCA3, 3}, {0x1CF00, 0x1CF2D, 4}, {0x1CF30, 0x1CF46, 4}, 
	{0x1D165, 0x1D165, 4}, {0x1D166, 0x1D166, 8}, {0x1D167, 0x1D169, 4}, {0x1D16D, 0x1D16D, 8}, 
	{0x1D16E, 0x1D172, 4}, {0x1D173, 0x1D17A, 3}, {0x1D17B, 0x1D182, 4}, {0x1D185, 0x1D18B, 4}, 
	{0x1D1AA, 0x1D1AD, 4}, {0x1D242, 0x1D244, 4}, {0x1DA00, 0x1DA36, 4}, {0x1DA3B, 0x1DA6C, 4}, 
	{0x1DA75, 0x1DA75, 4}, {0x1DA84, 0x1DA84, 4}, {0x1DA9B, 0x1DA9F, 4}, {0x1DAA1, 0x1DAAF, 4}, 
	{0x1E000, 0x1E006, 4}, {0x1E008, 0x1E018, 4}, {0x1E01B, 0x1E021, 4}, {0x1E023, 0x1E024, 4}, 
	{0x1E026, 0x1E02A, 4}, {0x1E08F, 0x1E08F, 4}, {0x1E130, 0x1E136, 4}, {0x1E2AE, 0x1E2AE, 4}, 
	{0x1E2EC, 0x1E2EF, 4}, {0x1E4EC, 0x1E4EF, 4}, {0x1E8D0, 0x1E8D6, 4}, {0x1E944, 0x1E94A, 4}, 
	{0x1F1E6, 0x1F1FF, 6}, {0x1F3FB, 0x1F3FF, 4}, {0xE0000, 0xE001F, 3}, {0xE0020, 0xE007F, 4}, 
	{0xE0080, 0xE00FF, 3}, {0xE0100, 0xE01EF, 4}, {0xE01F0, 0xE0FFF, 3}, 
};
static const int32_t guji_gcb_range_count = 1371;

const char *const guji_rgi_emoji_sequences[] = {
	"\360\237\221\250\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\250\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\250\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\250\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\250\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\247\221\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\276",
	"\360\237\247\221\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\277",
	"\360\237\247\221\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\276",
	"\360\237\247\221\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\277",
	"\360\237\247\221\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\276",
	"\360\237\247\221\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\277",
	"\360\237\247\221\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\277",
	"\360\237\247\221\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\247\221\360\237\217\276",
	"\360\237\221\250\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250",
	"\360\237\221\250\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\250\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\250\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\250\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\250\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\250",
	"\360\237\221\251\342\200\215\342\235\244\357\270\217\342\200\215\360\237\222\213\342\200\215\360\237\221\251",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\247\221\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\276",
	"\360\237\247\221\360\237\217\273\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\277",
	"\360\237\247\221\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\276",
	"\360\237\247\221\360\237\217\274\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\277",
	"\360\237\247\221\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\276",
	"\360\237\247\221\360\237\217\275\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\277",
	"\360\237\247\221\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\276\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\277",
	"\360\237\247\221\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\277\342\200\215\342\235\244\357\270\217\342\200\215\360\237\247\221\360\237\217\276",
	"\360\237\217\264\363\240\201\247\363\240\201\242\363\240\201\245\363\240\201\256\363\240\201\247\363\240\201\277",
	"\360\237\217\264\363\240\201\247\363\240\201\242\363\240\201\263\363\240\201\243\363\240\201\264\363\240\201\277",
	"\360\237\217\264\363\240\201\247\363\240\201\242\363\240\201\267\363\240\201\254\363\240\201\263\363\240\201\277",
	"\360\237\221\250\342\200\215\360\237\221\250\342\200\215\360\237\221\246\342\200\215\360\237\221\246",
	"\360\237\221\250\342\200\215\360\237\221\250\342\200\215\360\237\221\247\342\200\215\360\237\221\246",
	"\360\237\221\250\342\200\215\360\237\221\250\342\200\215\360\237\221\247\342\200\215\360\237\221\247",
	"\360\237\221\250\342\200\215\360\237\221\251\342\200\215\360\237\221\246\342\200\215\360\237\221\246",
	"\360\237\221\250\342\200\215\360\237\221\251\342\200\215\360\237\221\247\342\200\215\360\237\221\246",
	"\360\237\221\250\342\200\215\360\237\221\251\342\200\215\360\237\221\247\342\200\215\360\237\221\247",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\342\200\215\360\237\221\251\342\200\215\360\237\221\246\342\200\215\360\237\221\246",
	"\360\237\221\251\342\200\215\360\237\221\251\342\200\215\360\237\221\247\342\200\215\360\237\221\246",
	"\360\237\221\251\342\200\215\360\237\221\251\342\200\215\360\237\221\247\342\200\215\360\237\221\247",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\277",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\273",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\274",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\275",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\221\250\360\237\217\276",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\221\251\360\237\217\276",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\276",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\277",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\276",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\277",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\276",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\277",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\276",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\277",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\276",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\244\235\342\200\215\360\237\247\221\360\237\217\277",
	"\360\237\221\250\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250",
	"\360\237\221\251\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\250",
	"\360\237\221\251\342\200\215\342\235\244\357\270\217\342\200\215\360\237\221\251",
	"\342\233\271\357\270\217\342\200\215\342\231\200\357\270\217",
	"\342\233\271\357\270\217\342\200\215\342\231\202\357\270\217",
	"\342\233\271\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\342\233\271\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\342\233\271\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\342\233\271\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\342\233\271\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\342\233\271\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\342\233\271\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\342\233\271\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\342\233\271\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\342\233\271\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\217\203\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\217\203\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\217\203\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\217\203\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\217\203\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\217\203\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\217\203\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\217\203\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\217\203\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\217\203\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\217\204\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\217\204\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\217\204\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\217\204\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\217\204\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\217\204\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\217\204\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\217\204\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\217\204\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\217\204\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\217\212\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\217\212\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\217\212\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\217\212\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\217\212\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\217\212\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\217\212\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\217\212\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\217\212\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\217\212\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\217\213\357\270\217\342\200\215\342\231\200\357\270\217",
	"\360\237\217\213\357\270\217\342\200\215\342\231\202\357\270\217",
	"\360\237\217\213\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\217\213\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\217\213\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\217\213\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\217\213\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\217\213\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\217\213\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\217\213\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\217\213\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\217\213\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\217\214\357\270\217\342\200\215\342\231\200\357\270\217",
	"\360\237\217\214\357\270\217\342\200\215\342\231\202\357\270\217",
	"\360\237\217\214\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\217\214\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\217\214\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\217\214\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\217\214\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\217\214\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\217\214\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\217\214\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\217\214\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\217\214\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\217\263\357\270\217\342\200\215\342\232\247\357\270\217",
	"\360\237\221\201\357\270\217\342\200\215\360\237\227\250\357\270\217",
	"\360\237\221\250\342\200\215\360\237\221\246\342\200\215\360\237\221\246",
	"\360\237\221\250\342\200\215\360\237\221\247\342\200\215\360\237\221\246",
	"\360\237\221\250\342\200\215\360\237\221\247\342\200\215\360\237\221\247",
	"\360\237\221\250\342\200\215\360\237\221\250\342\200\215\360\237\221\246",
	"\360\237\221\250\342\200\215\360\237\221\250\342\200\215\360\237\221\247",
	"\360\237\221\250\342\200\215\360\237\221\251\342\200\215\360\237\221\246",
	"\360\237\221\250\342\200\215\360\237\221\251\342\200\215\360\237\221\247",
	"\360\237\221\250\360\237\217\273\342\200\215\342\232\225\357\270\217",
	"\360\237\221\250\360\237\217\273\342\200\215\342\232\226\357\270\217",
	"\360\237\221\250\360\237\217\273\342\200\215\342\234\210\357\270\217",
	"\360\237\221\250\360\237\217\274\342\200\215\342\232\225\357\270\217",
	"\360\237\221\250\360\237\217\274\342\200\215\342\232\226\357\270\217",
	"\360\237\221\250\360\237\217\274\342\200\215\342\234\210\357\270\217",
	"\360\237\221\250\360\237\217\275\342\200\215\342\232\225\357\270\217",
	"\360\237\221\250\360\237\217\275\342\200\215\342\232\226\357\270\217",
	"\360\237\221\250\360\237\217\275\342\200\215\342\234\210\357\270\217",
	"\360\237\221\250\360\237\217\276\342\200\215\342\232\225\357\270\217",
	"\360\237\221\250\360\237\217\276\342\200\215\342\232\226\357\270\217",
	"\360\237\221\250\360\237\217\276\342\200\215\342\234\210\357\270\217",
	"\360\237\221\250\360\237\217\277\342\200\215\342\232\225\357\270\217",
	"\360\237\221\250\360\237\217\277\342\200\215\342\232\226\357\270\217",
	"\360\237\221\250\360\237\217\277\342\200\215\342\234\210\357\270\217",
	"\360\237\221\251\342\200\215\360\237\221\246\342\200\215\360\237\221\246",
	"\360\237\221\251\342\200\215\360\237\221\247\342\200\215\360\237\221\246",
	"\360\237\221\251\342\200\215\360\237\221\247\342\200\215\360\237\221\247",
	"\360\237\221\251\342\200\215\360\237\221\251\342\200\215\360\237\221\246",
	"\360\237\221\251\342\200\215\360\237\221\251\342\200\215\360\237\221\247",
	"\360\237\221\251\360\237\217\273\342\200\215\342\232\225\357\270\217",
	"\360\237\221\251\360\237\217\273\342\200\215\342\232\226\357\270\217",
	"\360\237\221\251\360\237\217\273\342\200\215\342\234\210\357\270\217",
	"\360\237\221\251\360\237\217\274\342\200\215\342\232\225\357\270\217",
	"\360\237\221\251\360\237\217\274\342\200\215\342\232\226\357\270\217",
	"\360\237\221\251\360\237\217\274\342\200\215\342\234\210\357\270\217",
	"\360\237\221\251\360\237\217\275\342\200\215\342\232\225\357\270\217",
	"\360\237\221\251\360\237\217\275\342\200\215\342\232\226\357\270\217",
	"\360\237\221\251\360\237\217\275\342\200\215\342\234\210\357\270\217",
	"\360\237\221\251\360\237\217\276\342\200\215\342\232\225\357\270\217",
	"\360\237\221\251\360\237\217\276\342\200\215\342\232\226\357\270\217",
	"\360\237\221\251\360\237\217\276\342\200\215\342\234\210\357\270\217",
	"\360\237\221\251\360\237\217\277\342\200\215\342\232\225\357\270\217",
	"\360\237\221\251\360\237\217\277\342\200\215\342\232\226\357\270\217",
	"\360\237\221\251\360\237\217\277\342\200\215\342\234\210\357\270\217",
	"\360\237\221\256\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\221\256\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\221\256\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\221\256\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\221\256\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\221\256\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\221\256\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\221\256\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\221\256\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\221\256\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\221\260\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\221\260\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\221\260\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\221\260\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\221\260\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\221\260\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\221\260\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\221\260\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\221\260\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\221\260\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\221\261\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\221\261\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\221\261\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\221\261\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\221\261\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\221\261\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\221\261\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\221\261\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\221\261\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\221\261\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\221\263\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\221\263\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\221\263\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\221\263\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\221\263\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\221\263\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\221\263\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\221\263\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\221\263\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\221\263\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\221\267\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\221\267\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\221\267\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\221\267\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\221\267\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\221\267\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\221\267\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\221\267\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\221\267\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\221\267\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\222\201\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\222\201\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\222\201\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\222\201\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\222\201\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\222\201\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\222\201\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\222\201\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\222\201\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\222\201\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\222\202\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\222\202\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\222\202\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\222\202\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\222\202\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\222\202\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\222\202\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\222\202\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\222\202\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\222\202\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\222\206\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\222\206\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\222\206\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\222\206\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\222\206\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\222\206\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\222\206\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\222\206\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\222\206\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\222\206\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\222\207\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\222\207\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\222\207\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\222\207\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\222\207\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\222\207\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\222\207\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\222\207\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\222\207\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\222\207\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\225\265\357\270\217\342\200\215\342\231\200\357\270\217",
	"\360\237\225\265\357\270\217\342\200\215\342\231\202\357\270\217",
	"\360\237\225\265\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\225\265\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\225\265\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\225\265\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\225\265\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\225\265\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\225\265\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\225\265\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\225\265\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\225\265\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\231\205\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\231\205\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\231\205\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\231\205\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\231\205\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\231\205\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\231\205\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\231\205\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\231\205\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\231\205\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\231\206\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\231\206\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\231\206\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\231\206\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\231\206\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\231\206\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\231\206\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\231\206\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\231\206\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\231\206\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\231\207\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\231\207\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\231\207\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\231\207\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\231\207\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\231\207\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\231\207\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\231\207\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\231\207\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\231\207\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\231\213\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\231\213\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\231\213\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\231\213\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\231\213\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\231\213\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\231\213\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\231\213\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\231\213\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\231\213\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\231\215\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\231\215\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\231\215\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\231\215\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\231\215\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\231\215\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\231\215\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\231\215\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\231\215\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\231\215\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\231\216\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\231\216\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\231\216\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\231\216\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\231\216\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\231\216\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\231\216\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\231\216\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\231\216\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\231\216\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\232\243\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\232\243\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\232\243\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\232\243\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\232\243\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\232\243\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\232\243\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\232\243\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\232\243\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\232\243\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\232\264\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\232\264\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\232\264\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\232\264\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\232\264\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\232\264\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\232\264\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\232\264\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\232\264\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\232\264\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\232\265\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\232\265\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\232\265\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\232\265\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\232\265\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\232\265\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\232\265\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\232\265\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\232\265\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\232\265\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\232\266\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\232\266\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\232\266\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\232\266\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\232\266\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\232\266\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\232\266\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\232\266\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\232\266\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\232\266\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\244\246\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\244\246\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\244\246\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\244\246\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\244\246\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\244\246\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\244\246\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\244\246\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\244\246\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\244\246\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\244\265\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\244\265\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\244\265\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\244\265\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\244\265\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\244\265\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\244\265\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\244\265\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\244\265\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\244\265\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\244\267\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\244\267\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\244\267\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\244\267\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\244\267\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\244\267\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\244\267\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\244\267\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\244\267\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\244\267\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\244\270\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\244\270\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\244\270\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\244\270\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\244\270\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\244\270\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\244\270\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\244\270\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\244\270\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\244\270\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\244\271\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\244\271\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\244\271\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\244\271\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\244\271\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\244\271\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\244\271\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\244\271\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\244\271\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\244\271\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\244\275\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\244\275\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\244\275\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\244\275\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\244\275\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\244\275\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\244\275\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\244\275\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\244\275\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\244\275\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\244\276\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\244\276\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\244\276\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\244\276\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\244\276\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\244\276\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\244\276\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\244\276\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\244\276\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\244\276\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\246\270\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\246\270\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\246\270\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\246\270\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\246\270\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\246\270\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\246\270\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\246\270\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\246\270\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\246\270\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\246\271\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\246\271\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\246\271\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\246\271\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\246\271\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\246\271\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\246\271\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\246\271\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\246\271\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\246\271\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\247\215\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\247\215\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\247\215\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\247\215\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\247\215\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\247\215\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\247\215\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\247\215\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\247\215\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\247\215\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\247\216\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\247\216\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\247\216\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\247\216\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\247\216\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\247\216\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\247\216\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\247\216\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\247\216\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\247\216\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\247\217\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\247\217\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\247\217\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\247\217\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\247\217\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\247\217\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\247\217\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\247\217\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\247\217\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\247\217\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\247\221\342\200\215\360\237\244\235\342\200\215\360\237\247\221",
	"\360\237\247\221\360\237\217\273\342\200\215\342\232\225\357\270\217",
	"\360\237\247\221\360\237\217\273\342\200\215\342\232\226\357\270\217",
	"\360\237\247\221\360\237\217\273\342\200\215\342\234\210\357\270\217",
	"\360\237\247\221\360\237\217\274\342\200\215\342\232\225\357\270\217",
	"\360\237\247\221\360\237\217\274\342\200\215\342\232\226\357\270\217",
	"\360\237\247\221\360\237\217\274\342\200\215\342\234\210\357\270\217",
	"\360\237\247\221\360\237\217\275\342\200\215\342\232\225\357\270\217",
	"\360\237\247\221\360\237\217\275\342\200\215\342\232\226\357\270\217",
	"\360\237\247\221\360\237\217\275\342\200\215\342\234\210\357\270\217",
	"\360\237\247\221\360\237\217\276\342\200\215\342\232\225\357\270\217",
	"\360\237\247\221\360\237\217\276\342\200\215\342\232\226\357\270\217",
	"\360\237\247\221\360\237\217\276\342\200\215\342\234\210\357\270\217",
	"\360\237\247\221\360\237\217\277\342\200\215\342\232\225\357\270\217",
	"\360\237\247\221\360\237\217\277\342\200\215\342\232\226\357\270\217",
	"\360\237\247\221\360\237\217\277\342\200\215\342\234\210\357\270\217",
	"\360\237\247\224\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\247\224\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\247\224\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\247\224\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\247\224\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\247\224\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\247\224\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\247\224\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\247\224\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\247\224\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\247\226\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\247\226\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\247\226\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\247\226\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\247\226\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\247\226\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\247\226\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\247\226\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\247\226\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\247\226\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\247\227\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\247\227\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\247\227\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\247\227\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\247\227\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\247\227\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\247\227\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\247\227\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\247\227\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\247\227\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\247\230\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\247\230\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\247\230\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\247\230\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\247\230\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\247\230\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\247\230\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\247\230\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\247\230\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\247\230\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\247\231\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\247\231\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\247\231\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\247\231\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\247\231\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\247\231\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\247\231\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\247\231\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\247\231\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\247\231\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\247\232\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\247\232\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\247\232\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\247\232\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\247\232\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\247\232\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\247\232\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\247\232\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\247\232\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\247\232\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\247\233\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\247\233\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\247\233\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\247\233\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\247\233\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\247\233\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\247\233\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\247\233\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\247\233\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\247\233\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\247\234\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\247\234\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\247\234\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\247\234\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\247\234\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\247\234\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\247\234\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\247\234\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\247\234\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\247\234\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\247\235\360\237\217\273\342\200\215\342\231\200\357\270\217",
	"\360\237\247\235\360\237\217\273\342\200\215\342\231\202\357\270\217",
	"\360\237\247\235\360\237\217\274\342\200\215\342\231\200\357\270\217",
	"\360\237\247\235\360\237\217\274\342\200\215\342\231\202\357\270\217",
	"\360\237\247\235\360\237\217\275\342\200\215\342\231\200\357\270\217",
	"\360\237\247\235\360\237\217\275\342\200\215\342\231\202\357\270\217",
	"\360\237\247\235\360\237\217\276\342\200\215\342\231\200\357\270\217",
	"\360\237\247\235\360\237\217\276\342\200\215\342\231\202\357\270\217",
	"\360\237\247\235\360\237\217\277\342\200\215\342\231\200\357\270\217",
	"\360\237\247\235\360\237\217\277\342\200\215\342\231\202\357\270\217",
	"\360\237\253\261\360\237\217\273\342\200\215\360\237\253\262\360\237\217\274",
	"\360\237\253\261\360\237\217\273\342\200\215\360\237\253\262\360\237\217\275",
	"\360\237\253\261\360\237\217\273\342\200\215\360\237\253\262\360\237\217\276",
	"\360\237\253\261\360\237\217\273\342\200\215\360\237\253\262\360\237\217\277",
	"\360\237\253\261\360\237\217\274\342\200\215\360\237\253\262\360\237\217\273",
	"\360\237\253\261\360\237\217\274\342\200\215\360\237\253\262\360\237\217\275",
	"\360\237\253\261\360\237\217\274\342\200\215\360\237\253\262\360\237\217\276",
	"\360\237\253\261\360\237\217\274\342\200\215\360\237\253\262\360\237\217\277",
	"\360\237\253\261\360\237\217\275\342\200\215\360\237\253\262\360\237\217\273",
	"\360\237\253\261\360\237\217\275\342\200\215\360\237\253\262\360\237\217\274",
	"\360\237\253\261\360\237\217\275\342\200\215\360\237\253\262\360\237\217\276",
	"\360\237\253\261\360\237\217\275\342\200\215\360\237\253\262\360\237\217\277",
	"\360\237\253\261\360\237\217\276\342\200\215\360\237\253\262\360\237\217\273",
	"\360\237\253\261\360\237\217\276\342\200\215\360\237\253\262\360\237\217\274",
	"\360\237\253\261\360\237\217\276\342\200\215\360\237\253\262\360\237\217\275",
	"\360\237\253\261\360\237\217\276\342\200\215\360\237\253\262\360\237\217\277",
	"\360\237\253\261\360\237\217\277\342\200\215\360\237\253\262\360\237\217\273",
	"\360\237\253\261\360\237\217\277\342\200\215\360\237\253\262\360\237\217\274",
	"\360\237\253\261\360\237\217\277\342\200\215\360\237\253\262\360\237\217\275",
	"\360\237\253\261\360\237\217\277\342\200\215\360\237\253\262\360\237\217\276",
	"\342\235\244\357\270\217\342\200\215\360\237\224\245",
	"\342\235\244\357\270\217\342\200\215\360\237\251\271",
	"\360\237\217\203\342\200\215\342\231\200\357\270\217",
	"\360\237\217\203\342\200\215\342\231\202\357\270\217",
	"\360\237\217\204\342\200\215\342\231\200\357\270\217",
	"\360\237\217\204\342\200\215\342\231\202\357\270\217",
	"\360\237\217\212\342\200\215\342\231\200\357\270\217",
	"\360\237\217\212\342\200\215\342\231\202\357\270\217",
	"\360\237\217\263\357\270\217\342\200\215\360\237\214\210",
	"\360\237\217\264\342\200\215\342\230\240\357\270\217",
	"\360\237\220\273\342\200\215\342\235\204\357\270\217",
	"\360\237\221\250\342\200\215\342\232\225\357\270\217",
	"\360\237\221\250\342\200\215\342\232\226\357\270\217",
	"\360\237\221\250\342\200\215\342\234\210\357\270\217",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\214\276",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\215\263",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\215\274",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\216\223",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\216\244",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\216\250",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\217\253",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\217\255",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\222\273",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\222\274",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\224\247",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\224\254",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\232\200",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\232\222",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\246\257",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\246\260",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\246\261",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\246\262",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\246\263",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\246\274",
	"\360\237\221\250\360\237\217\273\342\200\215\360\237\246\275",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\214\276",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\215\263",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\215\274",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\216\223",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\216\244",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\216\250",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\217\253",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\217\255",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\222\273",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\222\274",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\224\247",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\224\254",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\232\200",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\232\222",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\246\257",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\246\260",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\246\261",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\246\262",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\246\263",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\246\274",
	"\360\237\221\250\360\237\217\274\342\200\215\360\237\246\275",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\214\276",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\215\263",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\215\274",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\216\223",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\216\244",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\216\250",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\217\253",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\217\255",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\222\273",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\222\274",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\224\247",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\224\254",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\232\200",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\232\222",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\246\257",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\246\260",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\246\261",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\246\262",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\246\263",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\246\274",
	"\360\237\221\250\360\237\217\275\342\200\215\360\237\246\275",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\214\276",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\215\263",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\215\274",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\216\223",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\216\244",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\216\250",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\217\253",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\217\255",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\222\273",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\222\274",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\224\247",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\224\254",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\232\200",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\232\222",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\246\257",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\246\260",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\246\261",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\246\262",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\246\263",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\246\274",
	"\360\237\221\250\360\237\217\276\342\200\215\360\237\246\275",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\214\276",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\215\263",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\215\274",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\216\223",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\216\244",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\216\250",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\217\253",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\217\255",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\222\273",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\222\274",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\224\247",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\224\254",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\232\200",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\232\222",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\246\257",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\246\260",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\246\261",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\246\262",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\246\263",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\246\274",
	"\360\237\221\250\360\237\217\277\342\200\215\360\237\246\275",
	"\360\237\221\251\342\200\215\342\232\225\357\270\217",
	"\360\237\221\251\342\200\215\342\232\226\357\270\217",
	"\360\237\221\251\342\200\215\342\234\210\357\270\217",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\214\276",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\215\263",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\215\274",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\216\223",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\216\244",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\216\250",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\217\253",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\217\255",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\222\273",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\222\274",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\224\247",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\224\254",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\232\200",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\232\222",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\246\257",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\246\260",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\246\261",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\246\262",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\246\263",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\246\274",
	"\360\237\221\251\360\237\217\273\342\200\215\360\237\246\275",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\214\276",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\215\263",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\215\274",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\216\223",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\216\244",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\216\250",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\217\253",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\217\255",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\222\273",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\222\274",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\224\247",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\224\254",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\232\200",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\232\222",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\246\257",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\246\260",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\246\261",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\246\262",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\246\263",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\246\274",
	"\360\237\221\251\360\237\217\274\342\200\215\360\237\246\275",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\214\276",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\215\263",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\215\274",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\216\223",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\216\244",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\216\250",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\217\253",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\217\255",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\222\273",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\222\274",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\224\247",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\224\254",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\232\200",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\232\222",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\246\257",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\246\260",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\246\261",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\246\262",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\246\263",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\246\274",
	"\360\237\221\251\360\237\217\275\342\200\215\360\237\246\275",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\214\276",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\215\263",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\215\274",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\216\223",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\216\244",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\216\250",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\217\253",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\217\255",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\222\273",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\222\274",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\224\247",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\224\254",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\232\200",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\232\222",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\246\257",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\246\260",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\246\261",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\246\262",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\246\263",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\246\274",
	"\360\237\221\251\360\237\217\276\342\200\215\360\237\246\275",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\214\276",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\215\263",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\215\274",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\216\223",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\216\244",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\216\250",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\217\253",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\217\255",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\222\273",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\222\274",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\224\247",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\224\254",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\232\200",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\232\222",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\246\257",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\246\260",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\246\261",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\246\262",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\246\263",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\246\274",
	"\360\237\221\251\360\237\217\277\342\200\215\360\237\246\275",
	"\360\237\221\256\342\200\215\342\231\200\357\270\217",
	"\360\237\221\256\342\200\215\342\231\202\357\270\217",
	"\360\237\221\257\342\200\215\342\231\200\357\270\217",
	"\360\237\221\257\342\200\215\342\231\202\357\270\217",
	"\360\237\221\260\342\200\215\342\231\200\357\270\217",
	"\360\237\221\260\342\200\215\342\231\202\357\270\217",
	"\360\237\221\261\342\200\215\342\231\200\357\270\217",
	"\360\237\221\261\342\200\215\342\231\202\357\270\217",
	"\360\237\221\263\342\200\215\342\231\200\357\270\217",
	"\360\237\221\263\342\200\215\342\231\202\357\270\217",
	"\360\237\221\267\342\200\215\342\231\200\357\270\217",
	"\360\237\221\267\342\200\215\342\231\202\357\270\217",
	"\360\237\222\201\342\200\215\342\231\200\357\270\217",
	"\360\237\222\201\342\200\215\342\231\202\357\270\217",
	"\360\237\222\202\342\200\215\342\231\200\357\270\217",
	"\360\237\222\202\342\200\215\342\231\202\357\270\217",
	"\360\237\222\206\342\200\215\342\231\200\357\270\217",
	"\360\237\222\206\342\200\215\342\231\202\357\270\217",
	"\360\237\222\207\342\200\215\342\231\200\357\270\217",
	"\360\237\222\207\342\200\215\342\231\202\357\270\217",
	"\360\237\230\266\342\200\215\360\237\214\253\357\270\217",
	"\360\237\231\205\342\200\215\342\231\200\357\270\217",
	"\360\237\231\205\342\200\215\342\231\202\357\270\217",
	"\360\237\231\206\342\200\215\342\231\200\357\270\217",
	"\360\237\231\206\342\200\215\342\231\202\357\270\217",
	"\360\237\231\207\342\200\215\342\231\200\357\270\217",
	"\360\237\231\207\342\200\215\342\231\202\357\270\217",
	"\360\237\231\213\342\200\215\342\231\200\357\270\217",
	"\360\237\231\213\342\200\215\342\231\202\357\270\217",
	"\360\237\231\215\342\200\215\342\231\200\357\270\217",
	"\360\237\231\215\342\200\215\342\231\202\357\270\217",
	"\360\237\231\216\342\200\215\342\231\200\357\270\217",
	"\360\237\231\216\342\200\215\342\231\202\357\270\217",
	"\360\237\232\243\342\200\215\342\231\200\357\270\217",
	"\360\237\232\243\342\200\215\342\231\202\357\270\217",
	"\360\237\232\264\342\200\215\342\231\200\357\270\217",
	"\360\237\232\264\342\200\215\342\231\202\357\270\217",
	"\360\237\232\265\342\200\215\342\231\200\357\270\217",
	"\360\237\232\265\342\200\215\342\231\202\357\270\217",
	"\360\237\232\266\342\200\215\342\231\200\357\270\217",
	"\360\237\232\266\342\200\215\342\231\202\357\270\217",
	"\360\237\244\246\342\200\215\342\231\200\357\270\217",
	"\360\237\244\246\342\200\215\342\231\202\357\270\217",
	"\360\237\244\265\342\200\215\342\231\200\357\270\217",
	"\360\237\244\265\342\200\215\342\231\202\357\270\217",
	"\360\237\244\267\342\200\215\342\231\200\357\270\217",
	"\360\237\244\267\342\200\215\342\231\202\357\270\217",
	"\360\237\244\270\342\200\215\342\231\200\357\270\217",
	"\360\237\244\270\342\200\215\342\231\202\357\270\217",
	"\360\237\244\271\342\200\215\342\231\200\357\270\217",
	"\360\237\244\271\342\200\215\342\231\202\357\270\217",
	"\360\237\244\274\342\200\215\342\231\200\357\270\217",
	"\360\237\244\274\342\200\215\342\231\202\357\270\217",
	"\360\237\244\275\342\200\215\342\231\200\357\270\217",
	"\360\237\244\275\342\200\215\342\231\202\357\270\217",
	"\360\237\244\276\342\200\215\342\231\200\357\270\217",
	"\360\237\244\276\342\200\215\342\231\202\357\270\217",
	"\360\237\246\270\342\200\215\342\231\200\357\270\217",
	"\360\237\246\270\342\200\215\342\231\202\357\270\217",
	"\360\237\246\271\342\200\215\342\231\200\357\270\217",
	"\360\237\246\271\342\200\215\342\231\202\357\270\217",
	"\360\237\247\215\342\200\215\342\231\200\357\270\217",
	"\360\237\247\215\342\200\215\342\231\202\357\270\217",
	"\360\237\247\216\342\200\215\342\231\200\357\270\217",
	"\360\237\247\216\342\200\215\342\231\202\357\270\217",
	"\360\237\247\217\342\200\215\342\231\200\357\270\217",
	"\360\237\247\217\342\200\215\342\231\202\357\270\217",
	"\360\237\247\221\342\200\215\342\232\225\357\270\217",
	"\360\237\247\221\342\200\215\342\232\226\357\270\217",
	"\360\237\247\221\342\200\215\342\234\210\357\270\217",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\214\276",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\215\263",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\215\274",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\216\204",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\216\223",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\216\244",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\216\250",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\217\253",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\217\255",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\222\273",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\222\274",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\224\247",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\224\254",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\232\200",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\232\222",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\246\257",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\246\260",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\246\261",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\246\262",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\246\263",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\246\274",
	"\360\237\247\221\360\237\217\273\342\200\215\360\237\246\275",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\214\276",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\215\263",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\215\274",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\216\204",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\216\223",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\216\244",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\216\250",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\217\253",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\217\255",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\222\273",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\222\274",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\224\247",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\224\254",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\232\200",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\232\222",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\246\257",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\246\260",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\246\261",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\246\262",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\246\263",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\246\274",
	"\360\237\247\221\360\237\217\274\342\200\215\360\237\246\275",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\214\276",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\215\263",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\215\274",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\216\204",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\216\223",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\216\244",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\216\250",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\217\253",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\217\255",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\222\273",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\222\274",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\224\247",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\224\254",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\232\200",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\232\222",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\246\257",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\246\260",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\246\261",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\246\262",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\246\263",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\246\274",
	"\360\237\247\221\360\237\217\275\342\200\215\360\237\246\275",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\214\276",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\215\263",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\215\274",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\216\204",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\216\223",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\216\244",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\216\250",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\217\253",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\217\255",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\222\273",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\222\274",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\224\247",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\224\254",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\232\200",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\232\222",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\246\257",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\246\260",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\246\261",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\246\262",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\246\263",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\246\274",
	"\360\237\247\221\360\237\217\276\342\200\215\360\237\246\275",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\214\276",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\215\263",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\215\274",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\216\204",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\216\223",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\216\244",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\216\250",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\217\253",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\217\255",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\222\273",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\222\274",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\224\247",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\224\254",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\232\200",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\232\222",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\246\257",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\246\260",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\246\261",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\246\262",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\246\263",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\246\274",
	"\360\237\247\221\360\237\217\277\342\200\215\360\237\246\275",
	"\360\237\247\224\342\200\215\342\231\200\357\270\217",
	"\360\237\247\224\342\200\215\342\231\202\357\270\217",
	"\360\237\247\226\342\200\215\342\231\200\357\270\217",
	"\360\237\247\226\342\200\215\342\231\202\357\270\217",
	"\360\237\247\227\342\200\215\342\231\200\357\270\217",
	"\360\237\247\227\342\200\215\342\231\202\357\270\217",
	"\360\237\247\230\342\200\215\342\231\200\357\270\217",
	"\360\237\247\230\342\200\215\342\231\202\357\270\217",
	"\360\237\247\231\342\200\215\342\231\200\357\270\217",
	"\360\237\247\231\342\200\215\342\231\202\357\270\217",
	"\360\237\247\232\342\200\215\342\231\200\357\270\217",
	"\360\237\247\232\342\200\215\342\231\202\357\270\217",
	"\360\237\247\233\342\200\215\342\231\200\357\270\217",
	"\360\237\247\233\342\200\215\342\231\202\357\270\217",
	"\360\237\247\234\342\200\215\342\231\200\357\270\217",
	"\360\237\247\234\342\200\215\342\231\202\357\270\217",
	"\360\237\247\235\342\200\215\342\231\200\357\270\217",
	"\360\237\247\235\342\200\215\342\231\202\357\270\217",
	"\360\237\247\236\342\200\215\342\231\200\357\270\217",
	"\360\237\247\236\342\200\215\342\231\202\357\270\217",
	"\360\237\247\237\342\200\215\342\231\200\357\270\217",
	"\360\237\247\237\342\200\215\342\231\202\357\270\217",
	"\043\357\270\217\342\203\243",
	"\052\357\270\217\342\203\243",
	"\060\357\270\217\342\203\243",
	"\061\357\270\217\342\203\243",
	"\062\357\270\217\342\203\243",
	"\063\357\270\217\342\203\243",
	"\064\357\270\217\342\203\243",
	"\065\357\270\217\342\203\243",
	"\066\357\270\217\342\203\243",
	"\067\357\270\217\342\203\243",
	"\070\357\270\217\342\203\243",
	"\071\357\270\217\342\203\243",
	"\360\237\220\210\342\200\215\342\254\233",
	"\360\237\220\225\342\200\215\360\237\246\272",
	"\360\237\220\246\342\200\215\342\254\233",
	"\360\237\221\250\342\200\215\360\237\214\276",
	"\360\237\221\250\342\200\215\360\237\215\263",
	"\360\237\221\250\342\200\215\360\237\215\274",
	"\360\237\221\250\342\200\215\360\237\216\223",
	"\360\237\221\250\342\200\215\360\237\216\244",
	"\360\237\221\250\342\200\215\360\237\216\250",
	"\360\237\221\250\342\200\215\360\237\217\253",
	"\360\237\221\250\342\200\215\360\237\217\255",
	"\360\237\221\250\342\200\215\360\237\221\246",
	"\360\237\221\250\342\200\215\360\237\221\247",
	"\360\237\221\250\342\200\215\360\237\222\273",
	"\360\237\221\250\342\200\215\360\237\222\274",
	"\360\237\221\250\342\200\215\360\237\224\247",
	"\360\237\221\250\342\200\215\360\237\224\254",
	"\360\237\221\250\342\200\215\360\237\232\200",
	"\360\237\221\250\342\200\215\360\237\232\222",
	"\360\237\221\250\342\200\215\360\237\246\257",
	"\360\237\221\250\342\200\215\360\237\246\260",
	"\360\237\221\250\342\200\215\360\237\246\261",
	"\360\237\221\250\342\200\215\360\237\246\262",
	"\360\237\221\250\342\200\215\360\237\246\263",
	"\360\237\221\250\342\200\215\360\237\246\274",
	"\360\237\221\250\342\200\215\360\237\246\275",
	"\360\237\221\251\342\200\215\360\237\214\276",
	"\360\237\221\251\342\200\215\360\237\215\263",
	"\360\237\221\251\342\200\215\360\237\215\274",
	"\360\237\221\251\342\200\215\360\237\216\223",
	"\360\237\221\251\342\200\215\360\237\216\244",
	"\360\237\221\251\342\200\215\360\237\216\250",
	"\360\237\221\251\342\200\215\360\237\217\253",
	"\360\237\221\251\342\200\215\360\237\217\255",
	"\360\237\221\251\342\200\215\360\237\221\246",
	"\360\237\221\251\342\200\215\360\237\221\247",
	"\360\237\221\251\342\200\215\360\237\222\273",
	"\360\237\221\251\342\200\215\360\237\222\274",
	"\360\237\221\251\342\200\215\360\237\224\247",
	"\360\237\221\251\342\200\215\360\237\224\254",
	"\360\237\221\251\342\200\215\360\237\232\200",
	"\360\237\221\251\342\200\215\360\237\232\222",
	"\360\237\221\251\342\200\215\360\237\246\257",
	"\360\237\221\251\342\200\215\360\237\246\260",
	"\360\237\221\251\342\200\215\360\237\246\261",
	"\360\237\221\251\342\200\215\360\237\246\262",
	"\360\237\221\251\342\200\215\360\237\246\263",
	"\360\237\221\251\342\200\215\360\237\246\274",
	"\360\237\221\251\342\200\215\360\237\246\275",
	"\360\237\230\256\342\200\215\360\237\222\250",
	"\360\237\230\265\342\200\215\360\237\222\253",
	"\360\237\247\221\342\200\215\360\237\214\276",
	"\360\237\247\221\342\200\215\360\237\215\263",
	"\360\237\247\221\342\200\215\360\237\215\274",
	"\360\237\247\221\342\200\215\360\237\216\204",
	"\360\237\247\221\342\200\215\360\237\216\223",
	"\360\237\247\221\342\200\215\360\237\216\244",
	"\360\237\247\221\342\200\215\360\237\216\250",
	"\360\237\247\221\342\200\215\360\237\217\253",
	"\360\237\247\221\342\200\215\360\237\217\255",
	"\360\237\247\221\342\200\215\360\237\222\273",
	"\360\237\247\221\342\200\215\360\237\222\274",
	"\360\237\247\221\342\200\215\360\237\224\247",
	"\360\237\247\221\342\200\215\360\237\224\254",
	"\360\237\247\221\342\200\215\360\237\232\200",
	"\360\237\247\221\342\200\215\360\237\232\222",
	"\360\237\247\221\342\200\215\360\237\246\257",
	"\360\237\247\221\342\200\215\360\237\246\260",
	"\360\237\247\221\342\200\215\360\237\246\261",
	"\360\237\247\221\342\200\215\360\237\246\262",
	"\360\237\247\221\342\200\215\360\237\246\263",
	"\360\237\247\221\342\200\215\360\237\246\274",
	"\360\237\247\221\342\200\215\360\237\246\275",
	"\302\251\357\270\217",
	"\302\256\357\270\217",
	"\342\200\274\357\270\217",
	"\342\201\211\357\270\217",
	"\342\204\242\357\270\217",
	"\342\204\271\357\270\217",
	"\342\206\224\357\270\217",
	"\342\206\225\357\270\217",
	"\342\206\226\357\270\217",
	"\342\206\227\357\270\217",
	"\342\206\230\357\270\217",
	"\342\206\231\357\270\217",
	"\342\206\251\357\270\217",
	"\342\206\252\357\270\217",
	"\342\214\250\357\270\217",
	"\342\217\217\357\270\217",
	"\342\217\255\357\270\217",
	"\342\217\256\357\270\217",
	"\342\217\257\357\270\217",
	"\342\217\261\357\270\217",
	"\342\217\262\357\270\217",
	"\342\217\270\357\270\217",
	"\342\217\271\357\270\217",
	"\342\217\272\357\270\217",
	"\342\223\202\357\270\217",
	"\342\226\252\357\270\217",
	"\342\226\253\357\270\217",
	"\342\226\266\357\270\217",
	"\342\227\200\357\270\217",
	"\342\227\273\357\270\217",
	"\342\227\274\357\270\217",
	"\342\230\200\357\270\217",
	"\342\230\201\357\270\217",
	"\342\230\202\357\270\217",
	"\342\230\203\357\270\217",
	"\342\230\204\357\270\217",
	"\342\230\216\357\270\217",
	"\342\230\221\357\270\217",
	"\342\230\230\357\270\217",
	"\342\230\235\357\270\217",
	"\342\230\235\360\237\217\273",
	"\342\230\235\360\237\217\274",
	"\342\230\235\360\237\217\275",
	"\342\230\235\360\237\217\276",
	"\342\230\235\360\237\217\277",
	"\342\230\240\357\270\217",
	"\342\230\242\357\270\217",
	"\342\230\243\357\270\217",
	"\342\230\246\357\270\217",
	"\342\230\252\357\270\217",
	"\342\230\256\357\270\217",
	"\342\230\257\357\270\217",
	"\342\230\270\357\270\217",
	"\342\230\271\357\270\217",
	"\342\230\272\357\270\217",
	"\342\231\200\357\270\217",
	"\342\231\202\357\270\217",
	"\342\231\237\357\270\217",
	"\342\231\240\357\270\217",
	"\342\231\243\357\270\217",
	"\342\231\245\357\270\217",
	"\342\231\246\357\270\217",
	"\342\231\250\357\270\217",
	"\342\231\273\357\270\217",
	"\342\231\276\357\270\217",
	"\342\232\222\357\270\217",
	"\342\232\224\357\270\217",
	"\342\232\225\357\270\217",
	"\342\232\226\357\270\217",
	"\342\232\227\357\270\217",
	"\342\232\231\357\270\217",
	"\342\232\233\357\270\217",
	"\342\232\234\357\270\217",
	"\342\232\240\357\270\217",
	"\342\232\247\357\270\217",
	"\342\232\260\357\270\217",
	"\342\232\261\357\270\217",
	"\342\233\210\357\270\217",
	"\342\233\217\357\270\217",
	"\342\233\221\357\270\217",
	"\342\233\223\357\270\217",
	"\342\233\251\357\270\217",
	"\342\233\260\357\270\217",
	"\342\233\261\357\270\217",
	"\342\233\264\357\270\217",
	"\342\233\267\357\270\217",
	"\342\233\270\357\270\217",
	"\342\233\271\357\270\217",
	"\342\233\271\360\237\217\273",
	"\342\233\271\360\237\217\274",
	"\342\233\271\360\237\217\275",
	"\342\233\271\360\237\217\276",
	"\342\233\271\360\237\217\277",
	"\342\234\202\357\270\217",
	"\342\234\210\357\270\217",
	"\342\234\211\357\270\217",
	"\342\234\212\360\237\217\273",
	"\342\234\212\360\237\217\274",
	"\342\234\212\360\237\217\275",
	"\342\234\212\360\237\217\276",
	"\342\234\212\360\237\217\277",
	"\342\234\213\360\237\217\273",
	"\342\234\213\360\237\217\274",
	"\342\234\213\360\237\217\275",
	"\342\234\213\360\237\217\276",
	"\342\234\213\360\237\217\277",
	"\342\234\214\357\270\217",
	"\342\234\214\360\237\217\273",
	"\342\234\214\360\237\217\274",
	"\342\234\214\360\237\217\275",
	"\342\234\214\360\237\217\276",
	"\342\234\214\360\237\217\277",
	"\342\234\215\357\270\217",
	"\342\234\215\360\237\217\273",
	"\342\234\215\360\237\217\274",
	"\342\234\215\360\237\217\275",
	"\342\234\215\360\237\217\276",
	"\342\234\215\360\237\217\277",
	"\342\234\217\357\270\217",
	"\342\234\222\357\270\217",
	"\342\234\224\357\270\217",
	"\342\234\226\357\270\217",
	"\342\234\235\357\270\217",
	"\342\234\241\357\270\217",
	"\342\234\263\357\270\217",
	"\342\234\264\357\270\217",
	"\342\235\204\357\270\217",
	"\342\235\207\357\270\217",
	"\342\235\243\357\270\217",
	"\342\235\244\357\270\217",
	"\342\236\241\357\270\217",
	"\342\244\264\357\270\217",
	"\342\244\265\357\270\217",
	"\342\254\205\357\270\217",
	"\342\254\206\357\270\217",
	"\342\254\207\357\270\217",
	"\343\200\260\357\270\217",
	"\343\200\275\357\270\217",
	"\343\212\227\357\270\217",
	"\343\212\231\357\270\217",
	"\360\237\205\260\357\270\217",
	"\360\237\205\261\357\270\217",
	"\360\237\205\276\357\270\217",
	"\360\237\205\277\357\270\217",
	"\360\237\207\246\360\237\207\250",
	"\360\237\207\246\360\237\207\251",
	"\360\237\207\246\360\237\207\252",
	"\360\237\207\246\360\237\207\253",
	"\360\237\207\246\360\237\207\254",
	"\360\237\207\246\360\237\207\256",
	"\360\237\207\246\360\237\207\261",
	"\360\237\207\246\360\237\207\262",
	"\360\237\207\246\360\237\207\264",
	"\360\237\207\246\360\237\207\266",
	"\360\237\207\246\360\237\207\267",
	"\360\237\207\246\360\237\207\270",
	"\360\237\207\246\360\237\207\271",
	"\360\237\207\246\360\237\207\272",
	"\360\237\207\246\360\237\207\274",
	"\360\237\207\246\360\237\207\275",
	"\360\237\207\246\360\237\207\277",
	"\360\237\207\247\360\237\207\246",
	"\360\237\207\247\360\237\207\247",
	"\360\237\207\247\360\237\207\251",
	"\360\237\207\247\360\237\207\252",
	"\360\237\207\247\360\237\207\253",
	"\360\237\207\247\360\237\207\254",
	"\360\237\207\247\360\237\207\255",
	"\360\237\207\247\360\237\207\256",
	"\360\237\207\247\360\237\207\257",
	"\360\237\207\247\360\237\207\261",
	"\360\237\207\247\360\237\207\262",
	"\360\237\207\247\360\237\207\263",
	"\360\237\207\247\360\237\207\264",
	"\360\237\207\247\360\237\207\266",
	"\360\237\207\247\360\237\207\267",
	"\360\237\207\247\360\237\207\270",
	"\360\237\207\247\360\237\207\271",
	"\360\237\207\247\360\237\207\273",
	"\360\237\207\247\360\237\207\274",
	"\360\237\207\247\360\237\207\276",
	"\360\237\207\247\360\237\207\277",
	"\360\237\207\250\360\237\207\246",
	"\360\237\207\250\360\237\207\250",
	"\360\237\207\250\360\237\207\251",
	"\360\237\207\250\360\237\207\253",
	"\360\237\207\250\360\237\207\254",
	"\360\237\207\250\360\237\207\255",
	"\360\237\207\250\360\237\207\256",
	"\360\237\207\250\360\237\207\260",
	"\360\237\207\250\360\237\207\261",
	"\360\237\207\250\360\237\207\262",
	"\360\237\207\250\360\237\207\263",
	"\360\237\207\250\360\237\207\264",
	"\360\237\207\250\360\237\207\265",
	"\360\237\207\250\360\237\207\267",
	"\360\237\207\250\360\237\207\272",
	"\360\237\207\250\360\237\207\273",
	"\360\237\207\250\360\237\207\274",
	"\360\237\207\250\360\237\207\275",
	"\360\237\207\250\360\237\207\276",
	"\360\237\207\250\360\237\207\277",
	"\360\237\207\251\360\237\207\252",
	"\360\237\207\251\360\237\207\254",
	"\360\237\207\251\360\237\207\257",
	"\360\237\207\251\360\237\207\260",
	"\360\237\207\251\360\237\207\262",
	"\360\237\207\251\360\237\207\264",
	"\360\237\207\251\360\237\207\277",
	"\360\237\207\252\360\237\207\246",
	"\360\237\207\252\360\237\207\250",
	"\360\237\207\252\360\237\207\252",
	"\360\237\207\252\360\237\207\254",
	"\360\237\207\252\360\237\207\255",
	"\360\237\207\252\360\237\207\267",
	"\360\237\207\252\360\237\207\270",
	"\360\237\207\252\360\237\207\271",
	"\360\237\207\252\360\237\207\272",
	"\360\237\207\253\360\237\207\256",
	"\360\237\207\253\360\237\207\257",
	"\360\237\207\253\360\237\207\260",
	"\360\237\207\253\360\237\207\262",
	"\360\237\207\253\360\237\207\264",
	"\360\237\207\253\360\237\207\267",
	"\360\237\207\254\360\237\207\246",
	"\360\237\207\254\360\237\207\247",
	"\360\237\207\254\360\237\207\251",
	"\360\237\207\254\360\237\207\252",
	"\360\237\207\254\360\237\207\253",
	"\360\237\207\254\360\237\207\254",
	"\360\237\207\254\360\237\207\255",
	"\360\237\207\254\360\237\207\256",
	"\360\237\207\254\360\237\207\261",
	"\360\237\207\254\360\237\207\262",
	"\360\237\207\254\360\237\207\263",
	"\360\237\207\254\360\237\207\265",
	"\360\237\207\254\360\237\207\266",
	"\360\237\207\254\360\237\207\267",
	"\360\237\207\254\360\237\207\270",
	"\360\237\207\254\360\237\207\271",
	"\360\237\207\254\360\237\207\272",
	"\360\237\207\254\360\237\207\274",
	"\360\237\207\254\360\237\207\276",
	"\360\237\207\255\360\237\207\260",
	"\360\237\207\255\360\237\207\262",
	"\360\237\207\255\360\237\207\263",
	"\360\237\207\255\360\237\207\267",
	"\360\237\207\255\360\237\207\271",
	"\360\237\207\255\360\237\207\272",
	"\360\237\207\256\360\237\207\250",
	"\360\237\207\256\360\237\207\251",
	"\360\237\207\256\360\237\207\252",
	"\360\237\207\256\360\237\207\261",
	"\360\237\207\256\360\237\207\262",
	"\360\237\207\256\360\237\207\263",
	"\360\237\207\256\360\237\207\264",
	"\360\237\207\256\360\237\207\266",
	"\360\237\207\256\360\237\207\267",
	"\360\237\207\256\360\237\207\270",
	"\360\237\207\256\360\237\207\271",
	"\360\237\207\257\360\237\207\252",
	"\360\237\207\257\360\237\207\262",
	"\360\237\207\257\360\237\207\264",
	"\360\237\207\257\360\237\207\265",
	"\360\237\207\260\360\237\207\252",
	"\360\237\207\260\360\237\207\254",
	"\360\237\207\260\360\237\207\255",
	"\360\237\207\260\360\237\207\256",
	"\360\237\207\260\360\237\207\262",
	"\360\237\207\260\360\237\207\263",
	"\360\237\207\260\360\237\207\265",
	"\360\237\207\260\360\237\207\267",
	"\360\237\207\260\360\237\207\274",
	"\360\237\207\260\360\237\207\276",
	"\360\237\207\260\360\237\207\277",
	"\360\237\207\261\360\237\207\246",
	"\360\237\207\261\360\237\207\247",
	"\360\237\207\261\360\237\207\250",
	"\360\237\207\261\360\237\207\256",
	"\360\237\207\261\360\237\207\260",
	"\360\237\207\261\360\237\207\267",
	"\360\237\207\261\360\237\207\270",
	"\360\237\207\261\360\237\207\271",
	"\360\237\207\261\360\237\207\272",
	"\360\237\207\261\360\237\207\273",
	"\360\237\207\261\360\237\207\276",
	"\360\237\207\262\360\237\207\246",
	"\360\237\207\262\360\237\207\250",
	"\360\237\207\262\360\237\207\251",
	"\360\237\207\262\360\237\207\252",
	"\360\237\207\262\360\237\207\253",
	"\360\237\207\262\360\237\207\254",
	"\360\237\207\262\360\237\207\255",
	"\360\237\207\262\360\237\207\260",
	"\360\237\207\262\360\237\207\261",
	"\360\237\207\262\360\237\207\262",
	"\360\237\207\262\360\237\207\263",
	"\360\237\207\262\360\237\207\264",
	"\360\237\207\262\360\237\207\265",
	"\360\237\207\262\360\237\207\266",
	"\360\237\207\262\360\237\207\267",
	"\360\237\207\262\360\237\207\270",
	"\360\237\207\262\360\237\207\271",
	"\360\237\207\262\360\237\207\272",
	"\360\237\207\262\360\237\207\273",
	"\360\237\207\262\360\237\207\274",
	"\360\237\207\262\360\237\207\275",
	"\360\237\207\262\360\237\207\276",
	"\360\237\207\262\360\237\207\277",
	"\360\237\207\263\360\237\207\246",
	"\360\237\207\263\360\237\207\250",
	"\360\237\207\263\360\237\207\252",
	"\360\237\207\263\360\237\207\253",
	"\360\237\207\263\360\237\207\254",
	"\360\237\207\263\360\237\207\256",
	"\360\237\207\263\360\237\207\261",
	"\360\237\207\263\360\237\207\264",
	"\360\237\207\263\360\237\207\265",
	"\360\237\207\263\360\237\207\267",
	"\360\237\207\263\360\237\207\272",
	"\360\237\207\263\360\237\207\277",
	"\360\237\207\264\360\237\207\262",
	"\360\237\207\265\360\237\207\246",
	"\360\237\207\265\360\237\207\252",
	"\360\237\207\265\360\237\207\253",
	"\360\237\207\265\360\237\207\254",
	"\360\237\207\265\360\237\207\255",
	"\360\237\207\265\360\237\207\260",
	"\360\237\207\265\360\237\207\261",
	"\360\237\207\265\360\237\207\262",
	"\360\237\207\265\360\237\207\263",
	"\360\237\207\265\360\237\207\267",
	"\360\237\207\265\360\237\207\270",
	"\360\237\207\265\360\237\207\271",
	"\360\237\207\265\360\237\207\274",
	"\360\237\207\265\360\237\207\276",
	"\360\237\207\266\360\237\207\246",
	"\360\237\207\267\360\237\207\252",
	"\360\237\207\267\360\237\207\264",
	"\360\237\207\267\360\237\207\270",
	"\360\237\207\267\360\237\207\272",
	"\360\237\207\267\360\237\207\274",
	"\360\237\207\270\360\237\207\246",
	"\360\237\207\270\360\237\207\247",
	"\360\237\207\270\360\237\207\250",
	"\360\237\207\270\360\237\207\251",
	"\360\237\207\270\360\237\207\252",
	"\360\237\207\270\360\237\207\254",
	"\360\237\207\270\360\237\207\255",
	"\360\237\207\270\360\237\207\256",
	"\360\237\207\270\360\237\207\257",
	"\360\237\207\270\360\237\207\260",
	"\360\237\207\270\360\237\207\261",
	"\360\237\207\270\360\237\207\262",
	"\360\237\207\270\360\237\207\263",
	"\360\237\207\270\360\237\207\264",
	"\360\237\207\270\360\237\207\267",
	"\360\237\207\270\360\237\207\270",
	"\360\237\207\270\360\237\207\271",
	"\360\237\207\270\360\237\207\273",
	"\360\237\207\270\360\237\207\275",
	"\360\237\207\270\360\237\207\276",
	"\360\237\207\270\360\237\207\277",
	"\360\237\207\271\360\237\207\246",
	"\360\237\207\271\360\237\207\250",
	"\360\237\207\271\360\237\207\251",
	"\360\237\207\271\360\237\207\253",
	"\360\237\207\271\360\237\207\254",
	"\360\237\207\271\360\237\207\255",
	"\360\237\207\271\360\237\207\257",
	"\360\237\207\271\360\237\207\260",
	"\360\237\207\271\360\237\207\261",
	"\360\237\207\271\360\237\207\262",
	"\360\237\207\271\360\237\207\263",
	"\360\237\207\271\360\237\207\264",
	"\360\237\207\271\360\237\207\267",
	"\360\237\207\271\360\237\207\271",
	"\360\237\207\271\360\237\207\273",
	"\360\237\207\271\360\237\207\274",
	"\360\237\207\271\360\237\207\277",
	"\360\237\207\272\360\237\207\246",
	"\360\237\207\272\360\237\207\254",
	"\360\237\207\272\360\237\207\262",
	"\360\237\207\272\360\237\207\263",
	"\360\237\207\272\360\237\207\270",
	"\360\237\207\272\360\237\207\276",
	"\360\237\207\272\360\237\207\277",
	"\360\237\207\273\360\237\207\246",
	"\360\237\207\273\360\237\207\250",
	"\360\237\207\273\360\237\207\252",
	"\360\237\207\273\360\237\207\254",
	"\360\237\207\273\360\237\207\256",
	"\360\237\207\273\360\237\207\263",
	"\360\237\207\273\360\237\207\272",
	"\360\237\207\274\360\237\207\253",
	"\360\237\207\274\360\237\207\270",
	"\360\237\207\275\360\237\207\260",
	"\360\237\207\276\360\237\207\252",
	"\360\237\207\276\360\237\207\271",
	"\360\237\207\277\360\237\207\246",
	"\360\237\207\277\360\237\207\262",
	"\360\237\207\277\360\237\207\274",
	"\360\237\210\202\357\270\217",
	"\360\237\210\267\357\270\217",
	"\360\237\214\241\357\270\217",
	"\360\237\214\244\357\270\217",
	"\360\237\214\245\357\270\217",
	"\360\237\214\246\357\270\217",
	"\360\237\214\247\357\270\217",
	"\360\237\214\250\357\270\217",
	"\360\237\214\251\357\270\217",
	"\360\237\214\252\357\270\217",
	"\360\237\214\253\357\270\217",
	"\360\237\214\254\357\270\217",
	"\360\237\214\266\357\270\217",
	"\360\237\215\275\357\270\217",
	"\360\237\216\205\360\237\217\273",
	"\360\237\216\205\360\237\217\274",
	"\360\237\216\205\360\237\217\275",
	"\360\237\216\205\360\237\217\276",
	"\360\237\216\205\360\237\217\277",
	"\360\237\216\226\357\270\217",
	"\360\237\216\227\357\270\217",
	"\360\237\216\231\357\270\217",
	"\360\237\216\232\357\270\217",
	"\360\237\216\233\357\270\217",
	"\360\237\216\236\357\270\217",
	"\360\237\216\237\357\270\217",
	"\360\237\217\202\360\237\217\273",
	"\360\237\217\202\360\237\217\274",
	"\360\237\217\202\360\237\217\275",
	"\360\237\217\202\360\237\217\276",
	"\360\237\217\202\360\237\217\277",
	"\360\237\217\203\360\237\217\273",
	"\360\237\217\203\360\237\217\274",
	"\360\237\217\203\360\237\217\275",
	"\360\237\217\203\360\237\217\276",
	"\360\237\217\203\360\237\217\277",
	"\360\237\217\204\360\237\217\273",
	"\360\237\217\204\360\237\217\274",
	"\360\237\217\204\360\237\217\275",
	"\360\237\217\204\360\237\217\276",
	"\360\237\217\204\360\237\217\277",
	"\360\237\217\207\360\237\217\273",
	"\360\237\217\207\360\237\217\274",
	"\360\237\217\207\360\237\217\275",
	"\360\237\217\207\360\237\217\276",
	"\360\237\217\207\360\237\217\277",
	"\360\237\217\212\360\237\217\273",
	"\360\237\217\212\360\237\217\274",
	"\360\237\217\212\360\237\217\275",
	"\360\237\217\212\360\237\217\276",
	"\360\237\217\212\360\237\217\277",
	"\360\237\217\213\357\270\217",
	"\360\237\217\213\360\237\217\273",
	"\360\237\217\213\360\237\217\274",
	"\360\237\217\213\360\237\217\275",
	"\360\237\217\213\360\237\217\276",
	"\360\237\217\213\360\237\217\277",
	"\360\237\217\214\357\270\217",
	"\360\237\217\214\360\237\217\273",
	"\360\237\217\214\360\237\217\274",
	"\360\237\217\214\360\237\217\275",
	"\360\237\217\214\360\237\217\276",
	"\360\237\217\214\360\237\217\277",
	"\360\237\217\215\357\270\217",
	"\360\237\217\216\357\270\217",
	"\360\237\217\224\357\270\217",
	"\360\237\217\225\357\270\217",
	"\360\237\217\226\357\270\217",
	"\360\237\217\227\357\270\217",
	"\360\237\217\230\357\270\217",
	"\360\237\217\231\357\270\217",
	"\360\237\217\232\357\270\217",
	"\360\237\217\233\357\270\217",
	"\360\237\217\234\357\270\217",
	"\360\237\217\235\357\270\217",
	"\360\237\217\236\357\270\217",
	"\360\237\217\237\357\270\217",
	"\360\237\217\263\357\270\217",
	"\360\237\217\265\357\270\217",
	"\360\237\217\267\357\270\217",
	"\360\237\220\277\357\270\217",
	"\360\237\221\201\357\270\217",
	"\360\237\221\202\360\237\217\273",
	"\360\237\221\202\360\237\217\274",
	"\360\237\221\202\360\237\217\275",
	"\360\237\221\202\360\237\217\276",
	"\360\237\221\202\360\237\217\277",
	"\360\237\221\203\360\237\217\273",
	"\360\237\221\203\360\237\217\274",
	"\360\237\221\203\360\237\217\275",
	"\360\237\221\203\360\237\217\276",
	"\360\237\221\203\360\237\217\277",
	"\360\237\221\206\360\237\217\273",
	"\360\237\221\206\360\237\217\274",
	"\360\237\221\206\360\237\217\275",
	"\360\237\221\206\360\237\217\276",
	"\360\237\221\206\360\237\217\277",
	"\360\237\221\207\360\237\217\273",
	"\360\237\221\207\360\237\217\274",
	"\360\237\221\207\360\237\217\275",
	"\360\237\221\207\360\237\217\276",
	"\360\237\221\207\360\237\217\277",
	"\360\237\221\210\360\237\217\273",
	"\360\237\221\210\360\237\217\274",
	"\360\237\221\210\360\237\217\275",
	"\360\237\221\210\360\237\217\276",
	"\360\237\221\210\360\237\217\277",
	"\360\237\221\211\360\237\217\273",
	"\360\237\221\211\360\237\217\274",
	"\360\237\221\211\360\237\217\275",
	"\360\237\221\211\360\237\217\276",
	"\360\237\221\211\360\237\217\277",
	"\360\237\221\212\360\237\217\273",
	"\360\237\221\212\360\237\217\274",
	"\360\237\221\212\360\237\217\275",
	"\360\237\221\212\360\237\217\276",
	"\360\237\221\212\360\237\217\277",
	"\360\237\221\213\360\237\217\273",
	"\360\237\221\213\360\237\217\274",
	"\360\237\221\213\360\237\217\275",
	"\360\237\221\213\360\237\217\276",
	"\360\237\221\213\360\237\217\277",
	"\360\237\221\214\360\237\217\273",
	"\360\237\221\214\360\237\217\274",
	"\360\237\221\214\360\237\217\275",
	"\360\237\221\214\360\237\217\276",
	"\360\237\221\214\360\237\217\277",
	"\360\237\221\215\360\237\217\273",
	"\360\237\221\215\360\237\217\274",
	"\360\237\221\215\360\237\217\275",
	"\360\237\221\215\360\237\217\276",
	"\360\237\221\215\360\237\217\277",
	"\360\237\221\216\360\237\217\273",
	"\360\237\221\216\360\237\217\274",
	"\360\237\221\216\360\237\217\275",
	"\360\237\221\216\360\237\217\276",
	"\360\237\221\216\360\237\217\277",
	"\360\237\221\217\360\237\217\273",
	"\360\237\221\217\360\237\217\274",
	"\360\237\221\217\360\237\217\275",
	"\360\237\221\217\360\237\217\276",
	"\360\237\221\217\360\237\217\277",
	"\360\237\221\220\360\237\217\273",
	"\360\237\221\220\360\237\217\274",
	"\360\237\221\220\360\237\217\275",
	"\360\237\221\220\360\237\217\276",
	"\360\237\221\220\360\237\217\277",
	"\360\237\221\246\360\237\217\273",
	"\360\237\221\246\360\237\217\274",
	"\360\237\221\246\360\237\217\275",
	"\360\237\221\246\360\237\217\276",
	"\360\237\221\246\360\237\217\277",
	"\360\237\221\247\360\237\217\273",
	"\360\237\221\247\360\237\217\274",
	"\360\237\221\247\360\237\217\275",
	"\360\237\221\247\360\237\217\276",
	"\360\237\221\247\360\237\217\277",
	"\360\237\221\250\360\237\217\273",
	"\360\237\221\250\360\237\217\274",
	"\360\237\221\250\360\237\217\275",
	"\360\237\221\250\360\237\217\276",
	"\360\237\221\250\360\237\217\277",
	"\360\237\221\251\360\237\217\273",
	"\360\237\221\251\360\237\217\274",
	"\360\237\221\251\360\237\217\275",
	"\360\237\221\251\360\237\217\276",
	"\360\237\221\251\360\237\217\277",
	"\360\237\221\253\360\237\217\273",
	"\360\237\221\253\360\237\217\274",
	"\360\237\221\253\360\237\217\275",
	"\360\237\221\253\360\237\217\276",
	"\360\237\221\253\360\237\217\277",
	"\360\237\221\254\360\237\217\273",
	"\360\237\221\254\360\237\217\274",
	"\360\237\221\254\360\237\217\275",
	"\360\237\221\254\360\237\217\276",
	"\360\237\221\254\360\237\217\277",
	"\360\237\221\255\360\237\217\273",
	"\360\237\221\255\360\237\217\274",
	"\360\237\221\255\360\237\217\275",
	"\360\237\221\255\360\237\217\276",
	"\360\237\221\255\360\237\217\277",
	"\360\237\221\256\360\237\217\273",
	"\360\237\221\256\360\237\217\274",
	"\360\237\221\256\360\237\217\275",
	"\360\237\221\256\360\237\217\276",
	"\360\237\221\256\360\237\217\277",
	"\360\237\221\260\360\237\217\273",
	"\360\237\221\260\360\237\217\274",
	"\360\237\221\260\360\237\217\275",
	"\360\237\221\260\360\237\217\276",
	"\360\237\221\260\360\237\217\277",
	"\360\237\221\261\360\237\217\273",
	"\360\237\221\261\360\237\217\274",
	"\360\237\221\261\360\237\217\275",
	"\360\237\221\261\360\237\217\276",
	"\360\237\221\261\360\237\217\277",
	"\360\237\221\262\360\237\217\273",
	"\360\237\221\262\360\237\217\274",
	"\360\237\221\262\360\237\217\275",
	"\360\237\221\262\360\237\217\276",
	"\360\237\221\262\360\237\217\277",
	"\360\237\221\263\360\237\217\273",
	"\360\237\221\263\360\237\217\274",
	"\360\237\221\263\360\237\217\275",
	"\360\237\221\263\360\237\217\276",
	"\360\237\221\263\360\237\217\277",
	"\360\237\221\264\360\237\217\273",
	"\360\237\221\264\360\237\217\274",
	"\360\237\221\264\360\237\217\275",
	"\360\237\221\264\360\237\217\276",
	"\360\237\221\264\360\237\217\277",
	"\360\237\221\265\360\237\217\273",
	"\360\237\221\265\360\237\217\274",
	"\360\237\221\265\360\237\217\275",
	"\360\237\221\265\360\237\217\276",
	"\360\237\221\265\360\237\217\277",
	"\360\237\221\266\360\237\217\273",
	"\360\237\221\266\360\237\217\274",
	"\360\237\221\266\360\237\217\275",
	"\360\237\221\266\360\237\217\276",
	"\360\237\221\266\360\237\217\277",
	"\360\237\221\267\360\237\217\273",
	"\360\237\221\267\360\237\217\274",
	"\360\237\221\267\360\237\217\275",
	"\360\237\221\267\360\237\217\276",
	"\360\237\221\267\360\237\217\277",
	"\360\237\221\270\360\237\217\273",
	"\360\237\221\270\360\237\217\274",
	"\360\237\221\270\360\237\217\275",
	"\360\237\221\270\360\237\217\276",
	"\360\237\221\270\360\237\217\277",
	"\360\237\221\274\360\237\217\273",
	"\360\237\221\274\360\237\217\274",
	"\360\237\221\274\360\237\217\275",
	"\360\237\221\274\360\237\217\276",
	"\360\237\221\274\360\237\217\277",
	"\360\237\222\201\360\237\217\273",
	"\360\237\222\201\360\237\217\274",
	"\360\237\222\201\360\237\217\275",
	"\360\237\222\201\360\237\217\276",
	"\360\237\222\201\360\237\217\277",
	"\360\237\222\202\360\237\217\273",
	"\360\237\222\202\360\237\217\274",
	"\360\237\222\202\360\237\217\275",
	"\360\237\222\202\360\237\217\276",
	"\360\237\222\202\360\237\217\277",
	"\360\237\222\203\360\237\217\273",
	"\360\237\222\203\360\237\217\274",
	"\360\237\222\203\360\237\217\275",
	"\360\237\222\203\360\237\217\276",
	"\360\237\222\203\360\237\217\277",
	"\360\237\222\205\360\237\217\273",
	"\360\237\222\205\360\237\217\274",
	"\360\237\222\205\360\237\217\275",
	"\360\237\222\205\360\237\217\276",
	"\360\237\222\205\360\237\217\277",
	"\360\237\222\206\360\237\217\273",
	"\360\237\222\206\360\237\217\274",
	"\360\237\222\206\360\237\217\275",
	"\360\237\222\206\360\237\217\276",
	"\360\237\222\206\360\237\217\277",
	"\360\237\222\207\360\237\217\273",
	"\360\237\222\207\360\237\217\274",
	"\360\237\222\207\360\237\217\275",
	"\360\237\222\207\360\237\217\276",
	"\360\237\222\207\360\237\217\277",
	"\360\237\222\217\360\237\217\273",
	"\360\237\222\217\360\237\217\274",
	"\360\237\222\217\360\237\217\275",
	"\360\237\222\217\360\237\217\276",
	"\360\237\222\217\360\237\217\277",
	"\360\237\222\221\360\237\217\273",
	"\360\237\222\221\360\237\217\274",
	"\360\237\222\221\360\237\217\275",
	"\360\237\222\221\360\237\217\276",
	"\360\237\222\221\360\237\217\277",
	"\360\237\222\252\360\237\217\273",
	"\360\237\222\252\360\237\217\274",
	"\360\237\222\252\360\237\217\275",
	"\360\237\222\252\360\237\217\276",
	"\360\237\222\252\360\237\217\277",
	"\360\237\223\275\357\270\217",
	"\360\237\225\211\357\270\217",
	"\360\237\225\212\357\270\217",
	"\360\237\225\257\357\270\217",
	"\360\237\225\260\357\270\217",
	"\360\237\225\263\357\270\217",
	"\360\237\225\264\357\270\217",
	"\360\237\225\264\360\237\217\273",
	"\360\237\225\264\360\237\217\274",
	"\360\237\225\264\360\237\217\275",
	"\360\237\225\264\360\237\217\276",
	"\360\237\225\264\360\237\217\277",
	"\360\237\225\265\357\270\217",
	"\360\237\225\265\360\237\217\273",
	"\360\237\225\265\360\237\217\274",
	"\360\237\225\265\360\237\217\275",
	"\360\237\225\265\360\237\217\276",
	"\360\237\225\265\360\237\217\277",
	"\360\237\225\266\357\270\217",
	"\360\237\225\267\357\270\217",
	"\360\237\225\270\357\270\217",
	"\360\237\225\271\357\270\217",
	"\360\237\225\272\360\237\217\273",
	"\360\237\225\272\360\237\217\274",
	"\360\237\225\272\360\237\217\275",
	"\360\237\225\272\360\237\217\276",
	"\360\237\225\272\360\237\217\277",
	"\360\237\226\207\357\270\217",
	"\360\237\226\212\357\270\217",
	"\360\237\226\213\357\270\217",
	"\360\237\226\214\357\270\217",
	"\360\237\226\215\357\270\217",
	"\360\237\226\220\357\270\217",
	"\360\237\226\220\360\237\217\273",
	"\360\237\226\220\360\237\217\274",
	"\360\237\226\220\360\237\217\275",
	"\360\237\226\220\360\237\217\276",
	"\360\237\226\220\360\237\217\277",
	"\360\237\226\225\360\237\217\273",
	"\360\237\226\225\360\237\217\274",
	"\360\237\226\225\360\237\217\275",
	"\360\237\226\225\360\237\217\276",
	"\360\237\226\225\360\237\217\277",
	"\360\237\226\226\360\237\217\273",
	"\360\237\226\226\360\237\217\274",
	"\360\237\226\226\360\237\217\275",
	"\360\237\226\226\360\237\217\276",
	"\360\237\226\226\360\237\217\277",
	"\360\237\226\245\357\270\217",
	"\360\237\226\250\357\270\217",
	"\360\237\226\261\357\270\217",
	"\360\237\226\262\357\270\217",
	"\360\237\226\274\357\270\217",
	"\360\237\227\202\357\270\217",
	"\360\237\227\203\357\270\217",
	"\360\237\227\204\357\270\217",
	"\360\237\227\221\357\270\217",
	"\360\237\227\222\357\270\217",
	"\360\237\227\223\357\270\217",
	"\360\237\227\234\357\270\217",
	"\360\237\227\235\357\270\217",
	"\360\237\227\236\357\270\217",
	"\360\237\227\241\357\270\217",
	"\360\237\227\243\357\270\217",
	"\360\237\227\250\357\270\217",
	"\360\237\227\257\357\270\217",
	"\360\237\227\263\357\270\217",
	"\360\237\227\272\357\270\217",
	"\360\237\231\205\360\237\217\273",
	"\360\237\231\205\360\237\217\274",
	"\360\237\231\205\360\237\217\275",
	"\360\237\231\205\360\237\217\276",
	"\360\237\231\205\360\237\217\277",
	"\360\237\231\206\360\237\217\273",
	"\360\237\231\206\360\237\217\274",
	"\360\237\231\206\360\237\217\275",
	"\360\237\231\206\360\237\217\276",
	"\360\237\231\206\360\237\217\277",
	"\360\237\231\207\360\237\217\273",
	"\360\237\231\207\360\237\217\274",
	"\360\237\231\207\360\237\217\275",
	"\360\237\231\207\360\237\217\276",
	"\360\237\231\207\360\237\217\277",
	"\360\237\231\213\360\237\217\273",
	"\360\237\231\213\360\237\217\274",
	"\360\237\231\213\360\237\217\275",
	"\360\237\231\213\360\237\217\276",
	"\360\237\231\213\360\237\217\277",
	"\360\237\231\214\360\237\217\273",
	"\360\237\231\214\360\237\217\274",
	"\360\237\231\214\360\237\217\275",
	"\360\237\231\214\360\237\217\276",
	"\360\237\231\214\360\237\217\277",
	"\360\237\231\215\360\237\217\273",
	"\360\237\231\215\360\237\217\274",
	"\360\237\231\215\360\237\217\275",
	"\360\237\231\215\360\237\217\276",
	"\360\237\231\215\360\237\217\277",
	"\360\237\231\216\360\237\217\273",
	"\360\237\231\216\360\237\217\274",
	"\360\237\231\216\360\237\217\275",
	"\360\237\231\216\360\237\217\276",
	"\360\237\231\216\360\237\217\277",
	"\360\237\231\217\360\237\217\273",
	"\360\237\231\217\360\237\217\274",
	"\360\237\231\217\360\237\217\275",
	"\360\237\231\217\360\237\217\276",
	"\360\237\231\217\360\237\217\277",
	"\360\237\232\243\360\237\217\273",
	"\360\237\232\243\360\237\217\274",
	"\360\237\232\243\360\237\217\275",
	"\360\237\232\243\360\237\217\276",
	"\360\237\232\243\360\237\217\277",
	"\360\237\232\264\360\237\217\273",
	"\360\237\232\264\360\237\217\274",
	"\360\237\232\264\360\237\217\275",
	"\360\237\232\264\360\237\217\276",
	"\360\237\232\264\360\237\217\277",
	"\360\237\232\265\360\237\217\273",
	"\360\237\232\265\360\237\217\274",
	"\360\237\232\265\360\237\217\275",
	"\360\237\232\265\360\237\217\276",
	"\360\237\232\265\360\237\217\277",
	"\360\237\232\266\360\237\217\273",
	"\360\237\232\266\360\237\217\274",
	"\360\237\232\266\360\237\217\275",
	"\360\237\232\266\360\237\217\276",
	"\360\237\232\266\360\237\217\277",
	"\360\237\233\200\360\237\217\273",
	"\360\237\233\200\360\237\217\274",
	"\360\237\233\200\360\237\217\275",
	"\360\237\233\200\360\237\217\276",
	"\360\237\233\200\360\237\217\277",
	"\360\237\233\213\357\270\217",
	"\360\237\233\214\360\237\217\273",
	"\360\237\233\214\360\237\217\274",
	"\360\237\233\214\360\237\217\275",
	"\360\237\233\214\360\237\217\276",
	"\360\237\233\214\360\237\217\277",
	"\360\237\233\215\357\270\217",
	"\360\237\233\216\357\270\217",
	"\360\237\233\217\357\270\217",
	"\360\237\233\240\357\270\217",
	"\360\237\233\241\357\270\217",
	"\360\237\233\242\357\270\217",
	"\360\237\233\243\357\270\217",
	"\360\237\233\244\357\270\217",
	"\360\237\233\245\357\270\217",
	"\360\237\233\251\357\270\217",
	"\360\237\233\260\357\270\217",
	"\360\237\233\263\357\270\217",
	"\360\237\244\214\360\237\217\273",
	"\360\237\244\214\360\237\217\274",
	"\360\237\244\214\360\237\217\275",
	"\360\237\244\214\360\237\217\276",
	"\360\237\244\214\360\237\217\277",
	"\360\237\244\217\360\237\217\273",
	"\360\237\244\217\360\237\217\274",
	"\360\237\244\217\360\237\217\275",
	"\360\237\244\217\360\237\217\276",
	"\360\237\244\217\360\237\217\277",
	"\360\237\244\230\360\237\217\273",
	"\360\237\244\230\360\237\217\274",
	"\360\237\244\230\360\237\217\275",
	"\360\237\244\230\360\237\217\276",
	"\360\237\244\230\360\237\217\277",
	"\360\237\244\231\360\237\217\273",
	"\360\237\244\231\360\237\217\274",
	"\360\237\244\231\360\237\217\275",
	"\360\237\244\231\360\237\217\276",
	"\360\237\244\231\360\237\217\277",
	"\360\237\244\232\360\237\217\273",
	"\360\237\244\232\360\237\217\274",
	"\360\237\244\232\360\237\217\275",
	"\360\237\244\232\360\237\217\276",
	"\360\237\244\232\360\237\217\277",
	"\360\237\244\233\360\237\217\273",
	"\360\237\244\233\360\237\217\274",
	"\360\237\244\233\360\237\217\275",
	"\360\237\244\233\360\237\217\276",
	"\360\237\244\233\360\237\217\277",
	"\360\237\244\234\360\237\217\273",
	"\360\237\244\234\360\237\217\274",
	"\360\237\244\234\360\237\217\275",
	"\360\237\244\234\360\237\217\276",
	"\360\237\244\234\360\237\217\277",
	"\360\237\244\235\360\237\217\273",
	"\360\237\244\235\360\237\217\274",
	"\360\237\244\235\360\237\217\275",
	"\360\237\244\235\360\237\217\276",
	"\360\237\244\235\360\237\217\277",
	"\360\237\244\236\360\237\217\273",
	"\360\237\244\236\360\237\217\274",
	"\360\237\244\236\360\237\217\275",
	"\360\237\244\236\360\237\217\276",
	"\360\237\244\236\360\237\217\277",
	"\360\237\244\237\360\237\217\273",
	"\360\237\244\237\360\237\217\274",
	"\360\237\244\237\360\237\217\275",
	"\360\237\244\237\360\237\217\276",
	"\360\237\244\237\360\237\217\277",
	"\360\237\244\246\360\237\217\273",
	"\360\237\244\246\360\237\217\274",
	"\360\237\244\246\360\237\217\275",
	"\360\237\244\246\360\237\217\276",
	"\360\237\244\246\360\237\217\277",
	"\360\237\244\260\360\237\217\273",
	"\360\237\244\260\360\237\217\274",
	"\360\237\244\260\360\237\217\275",
	"\360\237\244\260\360\237\217\276",
	"\360\237\244\260\360\237\217\277",
	"\360\237\244\261\360\237\217\273",
	"\360\237\244\261\360\237\217\274",
	"\360\237\244\261\360\237\217\275",
	"\360\237\244\261\360\237\217\276",
	"\360\237\244\261\360\237\217\277",
	"\360\237\244\262\360\237\217\273",
	"\360\237\244\262\360\237\217\274",
	"\360\237\244\262\360\237\217\275",
	"\360\237\244\262\360\237\217\276",
	"\360\237\244\262\360\237\217\277",
	"\360\237\244\263\360\237\217\273",
	"\360\237\244\263\360\237\217\274",
	"\360\237\244\263\360\237\217\275",
	"\360\237\244\263\360\237\217\276",
	"\360\237\244\263\360\237\217\277",
	"\360\237\244\264\360\237\217\273",
	"\360\237\244\264\360\237\217\274",
	"\360\237\244\264\360\237\217\275",
	"\360\237\244\264\360\237\217\276",
	"\360\237\244\264\360\237\217\277",
	"\360\237\244\265\360\237\217\273",
	"\360\237\244\265\360\237\217\274",
	"\360\237\244\265\360\237\217\275",
	"\360\237\244\265\360\237\217\276",
	"\360\237\244\265\360\237\217\277",
	"\360\237\244\266\360\237\217\273",
	"\360\237\244\266\360\237\217\274",
	"\360\237\244\266\360\237\217\275",
	"\360\237\244\266\360\237\217\276",
	"\360\237\244\266\360\237\217\277",
	"\360\237\244\267\360\237\217\273",
	"\360\237\244\267\360\237\217\274",
	"\360\237\244\267\360\237\217\275",
	"\360\237\244\267\360\237\217\276",
	"\360\237\244\267\360\237\217\277",
	"\360\237\244\270\360\237\217\273",
	"\360\237\244\270\360\237\217\274",
	"\360\237\244\270\360\237\217\275",
	"\360\237\244\270\360\237\217\276",
	"\360\237\244\270\360\237\217\277",
	"\360\237\244\271\360\237\217\273",
	"\360\237\244\271\360\237\217\274",
	"\360\237\244\271\360\237\217\275",
	"\360\237\244\271\360\237\217\276",
	"\360\237\244\271\360\237\217\277",
	"\360\237\244\275\360\237\217\273",
	"\360\237\244\275\360\237\217\274",
	"\360\237\244\275\360\237\217\275",
	"\360\237\244\275\360\237\217\276",
	"\360\237\244\275\360\237\217\277",
	"\360\237\244\276\360\237\217\273",
	"\360\237\244\276\360\237\217\274",
	"\360\237\244\276\360\237\217\275",
	"\360\237\244\276\360\237\217\276",
	"\360\237\244\276\360\237\217\277",
	"\360\237\245\267\360\237\217\273",
	"\360\237\245\267\360\237\217\274",
	"\360\237\245\267\360\237\217\275",
	"\360\237\245\267\360\237\217\276",
	"\360\237\245\267\360\237\217\277",
	"\360\237\246\265\360\237\217\273",
	"\360\237\246\265\360\237\217\274",
	"\360\237\246\265\360\237\217\275",
	"\360\237\246\265\360\237\217\276",
	"\360\237\246\265\360\237\217\277",
	"\360\237\246\266\360\237\217\273",
	"\360\237\246\266\360\237\217\274",
	"\360\237\246\266\360\237\217\275",
	"\360\237\246\266\360\237\217\276",
	"\360\237\246\266\360\237\217\277",
	"\360\237\246\270\360\237\217\273",
	"\360\237\246\270\360\237\217\274",
	"\360\237\246\270\360\237\217\275",
	"\360\237\246\270\360\237\217\276",
	"\360\237\246\270\360\237\217\277",
	"\360\237\246\271\360\237\217\273",
	"\360\237\246\271\360\237\217\274",
	"\360\237\246\271\360\237\217\275",
	"\360\237\246\271\360\237\217\276",
	"\360\237\246\271\360\237\217\277",
	"\360\237\246\273\360\237\217\273",
	"\360\237\246\273\360\237\217\274",
	"\360\237\246\273\360\237\217\275",
	"\360\237\246\273\360\237\217\276",
	"\360\237\246\273\360\237\217\277",
	"\360\237\247\215\360\237\217\273",
	"\360\237\247\215\360\237\217\274",
	"\360\237\247\215\360\237\217\275",
	"\360\237\247\215\360\237\217\276",
	"\360\237\247\215\360\237\217\277",
	"\360\237\247\216\360\237\217\273",
	"\360\237\247\216\360\237\217\274",
	"\360\237\247\216\360\237\217\275",
	"\360\237\247\216\360\237\217\276",
	"\360\237\247\216\360\237\217\277",
	"\360\237\247\217\360\237\217\273",
	"\360\237\247\217\360\237\217\274",
	"\360\237\247\217\360\237\217\275",
	"\360\237\247\217\360\237\217\276",
	"\360\237\247\217\360\237\217\277",
	"\360\237\247\221\360\237\217\273",
	"\360\237\247\221\360\237\217\274",
	"\360\237\247\221\360\237\217\275",
	"\360\237\247\221\360\237\217\276",
	"\360\237\247\221\360\237\217\277",
	"\360\237\247\222\360\237\217\273",
	"\360\237\247\222\360\237\217\274",
	"\360\237\247\222\360\237\217\275",
	"\360\237\247\222\360\237\217\276",
	"\360\237\247\222\360\237\217\277",
	"\360\237\247\223\360\237\217\273",
	"\360\237\247\223\360\237\217\274",
	"\360\237\247\223\360\237\217\275",
	"\360\237\247\223\360\237\217\276",
	"\360\237\247\223\360\237\217\277",
	"\360\237\247\224\360\237\217\273",
	"\360\237\247\224\360\237\217\274",
	"\360\237\247\224\360\237\217\275",
	"\360\237\247\224\360\237\217\276",
	"\360\237\247\224\360\237\217\277",
	"\360\237\247\225\360\237\217\273",
	"\360\237\247\225\360\237\217\274",
	"\360\237\247\225\360\237\217\275",
	"\360\237\247\225\360\237\217\276",
	"\360\237\247\225\360\237\217\277",
	"\360\237\247\226\360\237\217\273",
	"\360\237\247\226\360\237\217\274",
	"\360\237\247\226\360\237\217\275",
	"\360\237\247\226\360\237\217\276",
	"\360\237\247\226\360\237\217\277",
	"\360\237\247\227\360\237\217\273",
	"\360\237\247\227\360\237\217\274",
	"\360\237\247\227\360\237\217\275",
	"\360\237\247\227\360\237\217\276",
	"\360\237\247\227\360\237\217\277",
	"\360\237\247\230\360\237\217\273",
	"\360\237\247\230\360\237\217\274",
	"\360\237\247\230\360\237\217\275",
	"\360\237\247\230\360\237\217\276",
	"\360\237\247\230\360\237\217\277",
	"\360\237\247\231\360\237\217\273",
	"\360\237\247\231\360\237\217\274",
	"\360\237\247\231\360\237\217\275",
	"\360\237\247\231\360\237\217\276",
	"\360\237\247\231\360\237\217\277",
	"\360\237\247\232\360\237\217\273",
	"\360\237\247\232\360\237\217\274",
	"\360\237\247\232\360\237\217\275",
	"\360\237\247\232\360\237\217\276",
	"\360\237\247\232\360\237\217\277",
	"\360\237\247\233\360\237\217\273",
	"\360\237\247\233\360\237\217\274",
	"\360\237\247\233\360\237\217\275",
	"\360\237\247\233\360\237\217\276",
	"\360\237\247\233\360\237\217\277",
	"\360\237\247\234\360\237\217\273",
	"\360\237\247\234\360\237\217\274",
	"\360\237\247\234\360\237\217\275",
	"\360\237\247\234\360\237\217\276",
	"\360\237\247\234\360\237\217\277",
	"\360\237\247\235\360\237\217\273",
	"\360\237\247\235\360\237\217\274",
	"\360\237\247\235\360\237\217\275",
	"\360\237\247\235\360\237\217\276",
	"\360\237\247\235\360\237\217\277",
	"\360\237\253\203\360\237\217\273",
	"\360\237\253\203\360\237\217\274",
	"\360\237\253\203\360\237\217\275",
	"\360\237\253\203\360\237\217\276",
	"\360\237\253\203\360\237\217\277",
	"\360\237\253\204\360\237\217\273",
	"\360\237\253\204\360\237\217\274",
	"\360\237\253\204\360\237\217\275",
	"\360\237\253\204\360\237\217\276",
	"\360\237\253\204\360\237\217\277",
	"\360\237\253\205\360\237\217\273",
	"\360\237\253\205\360\237\217\274",
	"\360\237\253\205\360\237\217\275",
	"\360\237\253\205\360\237\217\276",
	"\360\237\253\205\360\237\217\277",
	"\360\237\253\260\360\237\217\273",
	"\360\237\253\260\360\237\217\274",
	"\360\237\253\260\360\237\217\275",
	"\360\237\253\260\360\237\217\276",
	"\360\237\253\260\360\237\217\277",
	"\360\237\253\261\360\237\217\273",
	"\360\237\253\261\360\237\217\274",
	"\360\237\253\261\360\237\217\275",
	"\360\237\253\261\360\237\217\276",
	"\360\237\253\261\360\237\217\277",
	"\360\237\253\262\360\237\217\273",
	"\360\237\253\262\360\237\217\274",
	"\360\237\253\262\360\237\217\275",
	"\360\237\253\262\360\237\217\276",
	"\360\237\253\262\360\237\217\277",
	"\360\237\253\263\360\237\217\273",
	"\360\237\253\263\360\237\217\274",
	"\360\237\253\263\360\237\217\275",
	"\360\237\253\263\360\237\217\276",
	"\360\237\253\263\360\237\217\277",
	"\360\237\253\264\360\237\217\273",
	"\360\237\253\264\360\237\217\274",
	"\360\237\253\264\360\237\217\275",
	"\360\237\253\264\360\237\217\276",
	"\360\237\253\264\360\237\217\277",
	"\360\237\253\265\360\237\217\273",
	"\360\237\253\265\360\237\217\274",
	"\360\237\253\265\360\237\217\275",
	"\360\237\253\265\360\237\217\276",
	"\360\237\253\265\360\237\217\277",
	"\360\237\253\266\360\237\217\273",
	"\360\237\253\266\360\237\217\274",
	"\360\237\253\266\360\237\217\275",
	"\360\237\253\266\360\237\217\276",
	"\360\237\253\266\360\237\217\277",
	"\360\237\253\267\360\237\217\273",
	"\360\237\253\267\360\237\217\274",
	"\360\237\253\267\360\237\217\275",
	"\360\237\253\267\360\237\217\276",
	"\360\237\253\267\360\237\217\277",
	"\360\237\253\270\360\237\217\273",
	"\360\237\253\270\360\237\217\274",
	"\360\237\253\270\360\237\217\275",
	"\360\237\253\270\360\237\217\276",
	"\360\237\253\270\360\237\217\277",
	"\342\214\232",
	"\342\214\233",
	"\342\217\251",
	"\342\217\252",
	"\342\217\253",
	"\342\217\254",
	"\342\217\260",
	"\342\217\263",
	"\342\227\275",
	"\342\227\276",
	"\342\230\224",
	"\342\230\225",
	"\342\231\210",
	"\342\231\211",
	"\342\231\212",
	"\342\231\213",
	"\342\231\214",
	"\342\231\215",
	"\342\231\216",
	"\342\231\217",
	"\342\231\220",
	"\342\231\221",
	"\342\231\222",
	"\342\231\223",
	"\342\231\277",
	"\342\232\223",
	"\342\232\241",
	"\342\232\252",
	"\342\232\253",
	"\342\232\275",
	"\342\232\276",
	"\342\233\204",
	"\342\233\205",
	"\342\233\216",
	"\342\233\224",
	"\342\233\252",
	"\342\233\262",
	"\342\233\263",
	"\342\233\265",
	"\342\233\272",
	"\342\233\275",
	"\342\234\205",
	"\342\234\212",
	"\342\234\213",
	"\342\234\250",
	"\342\235\214",
	"\342\235\216",
	"\342\235\223",
	"\342\235\224",
	"\342\235\225",
	"\342\235\227",
	"\342\236\225",
	"\342\236\226",
	"\342\236\227",
	"\342\236\260",
	"\342\236\277",
	"\342\254\233",
	"\342\254\234",
	"\342\255\220",
	"\342\255\225",
	"\360\237\200\204",
	"\360\237\203\217",
	"\360\237\206\216",
	"\360\237\206\221",
	"\360\237\206\222",
	"\360\237\206\223",
	"\360\237\206\224",
	"\360\237\206\225",
	"\360\237\206\226",
	"\360\237\206\227",
	"\360\237\206\230",
	"\360\237\206\231",
	"\360\237\206\232",
	"\360\237\210\201",
	"\360\237\210\232",
	"\360\237\210\257",
	"\360\237\210\262",
	"\360\237\210\263",
	"\360\237\210\264",
	"\360\237\210\265",
	"\360\237\210\266",
	"\360\237\210\270",
	"\360\237\210\271",
	"\360\237\210\272",
	"\360\237\211\220",
	"\360\237\211\221",
	"\360\237\214\200",
	"\360\237\214\201",
	"\360\237\214\202",
	"\360\237\214\203",
	"\360\237\214\204",
	"\360\237\214\205",
	"\360\237\214\206",
	"\360\237\214\207",
	"\360\237\214\210",
	"\360\237\214\211",
	"\360\237\214\212",
	"\360\237\214\213",
	"\360\237\214\214",
	"\360\237\214\215",
	"\360\237\214\216",
	"\360\237\214\217",
	"\360\237\214\220",
	"\360\237\214\221",
	"\360\237\214\222",
	"\360\237\214\223",
	"\360\237\214\224",
	"\360\237\214\225",
	"\360\237\214\226",
	"\360\237\214\227",
	"\360\237\214\230",
	"\360\237\214\231",
	"\360\237\214\232",
	"\360\237\214\233",
	"\360\237\214\234",
	"\360\237\214\235",
	"\360\237\214\236",
	"\360\237\214\237",
	"\360\237\214\240",
	"\360\237\214\255",
	"\360\237\214\256",
	"\360\237\214\257",
	"\360\237\214\260",
	"\360\237\214\261",
	"\360\237\214\262",
	"\360\237\214\263",
	"\360\237\214\264",
	"\360\237\214\265",
	"\360\237\214\267",
	"\360\237\214\270",
	"\360\237\214\271",
	"\360\237\214\272",
	"\360\237\214\273",
	"\360\237\214\274",
	"\360\237\214\275",
	"\360\237\214\276",
	"\360\237\214\277",
	"\360\237\215\200",
	"\360\237\215\201",
	"\360\237\215\202",
	"\360\237\215\203",
	"\360\237\215\204",
	"\360\237\215\205",
	"\360\237\215\206",
	"\360\237\215\207",
	"\360\237\215\210",
	"\360\237\215\211",
	"\360\237\215\212",
	"\360\237\215\213",
	"\360\237\215\214",
	"\360\237\215\215",
	"\360\237\215\216",
	"\360\237\215\217",
	"\360\237\215\220",
	"\360\237\215\221",
	"\360\237\215\222",
	"\360\237\215\223",
	"\360\237\215\224",
	"\360\237\215\225",
	"\360\237\215\226",
	"\360\237\215\227",
	"\360\237\215\230",
	"\360\237\215\231",
	"\360\237\215\232",
	"\360\237\215\233",
	"\360\237\215\234",
	"\360\237\215\235",
	"\360\237\215\236",
	"\360\237\215\237",
	"\360\237\215\240",
	"\360\237\215\241",
	"\360\237\215\242",
	"\360\237\215\243",
	"\360\237\215\244",
	"\360\237\215\245",
	"\360\237\215\246",
	"\360\237\215\247",
	"\360\237\215\250",
	"\360\237\215\251",
	"\360\237\215\252",
	"\360\237\215\253",
	"\360\237\215\254",
	"\360\237\215\255",
	"\360\237\215\256",
	"\360\237\215\257",
	"\360\237\215\260",
	"\360\237\215\261",
	"\360\237\215\262",
	"\360\237\215\263",
	"\360\237\215\264",
	"\360\237\215\265",
	"\360\237\215\266",
	"\360\237\215\267",
	"\360\237\215\270",
	"\360\237\215\271",
	"\360\237\215\272",
	"\360\237\215\273",
	"\360\237\215\274",
	"\360\237\215\276",
	"\360\237\215\277",
	"\360\237\216\200",
	"\360\237\216\201",
	"\360\237\216\202",
	"\360\237\216\203",
	"\360\237\216\204",
	"\360\237\216\205",
	"\360\237\216\206",
	"\360\237\216\207",
	"\360\237\216\210",
	"\360\237\216\211",
	"\360\237\216\212",
	"\360\237\216\213",
	"\360\237\216\214",
	"\360\237\216\215",
	"\360\237\216\216",
	"\360\237\216\217",
	"\360\237\216\220",
	"\360\237\216\221",
	"\360\237\216\222",
	"\360\237\216\223",
	"\360\237\216\240",
	"\360\237\216\241",
	"\360\237\216\242",
	"\360\237\216\243",
	"\360\237\216\244",
	"\360\237\216\245",
	"\360\237\216\246",
	"\360\237\216\247",
	"\360\237\216\250",
	"\360\237\216\251",
	"\360\237\216\252",
	"\360\237\216\253",
	"\360\237\216\254",
	"\360\237\216\255",
	"\360\237\216\256",
	"\360\237\216\257",
	"\360\237\216\260",
	"\360\237\216\261",
	"\360\237\216\262",
	"\360\237\216\263",
	"\360\237\216\264",
	"\360\237\216\265",
	"\360\237\216\266",
	"\360\237\216\267",
	"\360\237\216\270",
	"\360\237\216\271",
	"\360\237\216\272",
	"\360\237\216\273",
	"\360\237\216\274",
	"\360\237\216\275",
	"\360\237\216\276",
	"\360\237\216\277",
	"\360\237\217\200",
	"\360\237\217\201",
	"\360\237\217\202",
	"\360\237\217\203",
	"\360\237\217\204",
	"\360\237\217\205",
	"\360\237\217\206",
	"\360\237\217\207",
	"\360\237\217\210",
	"\360\237\217\211",
	"\360\237\217\212",
	"\360\237\217\217",
	"\360\237\217\220",
	"\360\237\217\221",
	"\360\237\217\222",
	"\360\237\217\223",
	"\360\237\217\240",
	"\360\237\217\241",
	"\360\237\217\242",
	"\360\237\217\243",
	"\360\237\217\244",
	"\360\237\217\245",
	"\360\237\217\246",
	"\360\237\217\247",
	"\360\237\217\250",
	"\360\237\217\251",
	"\360\237\217\252",
	"\360\237\217\253",
	"\360\237\217\254",
	"\360\237\217\255",
	"\360\237\217\256",
	"\360\237\217\257",
	"\360\237\217\260",
	"\360\237\217\264",
	"\360\237\217\270",
	"\360\237\217\271",
	"\360\237\217\272",
	"\360\237\217\273",
	"\360\237\217\274",
	"\360\237\217\275",
	"\360\237\217\276",
	"\360\237\217\277",
	"\360\237\220\200",
	"\360\237\220\201",
	"\360\237\220\202",
	"\360\237\220\203",
	"\360\237\220\204",
	"\360\237\220\205",
	"\360\237\220\206",
	"\360\237\220\207",
	"\360\237\220\210",
	"\360\237\220\211",
	"\360\237\220\212",
	"\360\237\220\213",
	"\360\237\220\214",
	"\360\237\220\215",
	"\360\237\220\216",
	"\360\237\220\217",
	"\360\237\220\220",
	"\360\237\220\221",
	"\360\237\220\222",
	"\360\237\220\223",
	"\360\237\220\224",
	"\360\237\220\225",
	"\360\237\220\226",
	"\360\237\220\227",
	"\360\237\220\230",
	"\360\237\220\231",
	"\360\237\220\232",
	"\360\237\220\233",
	"\360\237\220\234",
	"\360\237\220\235",
	"\360\237\220\236",
	"\360\237\220\237",
	"\360\237\220\240",
	"\360\237\220\241",
	"\360\237\220\242",
	"\360\237\220\243",
	"\360\237\220\244",
	"\360\237\220\245",
	"\360\237\220\246",
	"\360\237\220\247",
	"\360\237\220\250",
	"\360\237\220\251",
	"\360\237\220\252",
	"\360\237\220\253",
	"\360\237\220\254",
	"\360\237\220\255",
	"\360\237\220\256",
	"\360\237\220\257",
	"\360\237\220\260",
	"\360\237\220\261",
	"\360\237\220\262",
	"\360\237\220\263",
	"\360\237\220\264",
	"\360\237\220\265",
	"\360\237\220\266",
	"\360\237\220\267",
	"\360\237\220\270",
	"\360\237\220\271",
	"\360\237\220\272",
	"\360\237\220\273",
	"\360\237\220\274",
	"\360\237\220\275",
	"\360\237\220\276",
	"\360\237\221\200",
	"\360\237\221\202",
	"\360\237\221\203",
	"\360\237\221\204",
	"\360\237\221\205",
	"\360\237\221\206",
	"\360\237\221\207",
	"\360\237\221\210",
	"\360\237\221\211",
	"\360\237\221\212",
	"\360\237\221\213",
	"\360\237\221\214",
	"\360\237\221\215",
	"\360\237\221\216",
	"\360\237\221\217",
	"\360\237\221\220",
	"\360\237\221\221",
	"\360\237\221\222",
	"\360\237\221\223",
	"\360\237\221\224",
	"\360\237\221\225",
	"\360\237\221\226",
	"\360\237\221\227",
	"\360\237\221\230",
	"\360\237\221\231",
	"\360\237\221\232",
	"\360\237\221\233",
	"\360\237\221\234",
	"\360\237\221\235",
	"\360\237\221\236",
	"\360\237\221\237",
	"\360\237\221\240",
	"\360\237\221\241",
	"\360\237\221\242",
	"\360\237\221\243",
	"\360\237\221\244",
	"\360\237\221\245",
	"\360\237\221\246",
	"\360\237\221\247",
	"\360\237\221\250",
	"\360\237\221\251",
	"\360\237\221\252",
	"\360\237\221\253",
	"\360\237\221\254",
	"\360\237\221\255",
	"\360\237\221\256",
	"\360\237\221\257",
	"\360\237\221\260",
	"\360\237\221\261",
	"\360\237\221\262",
	"\360\237\221\263",
	"\360\237\221\264",
	"\360\237\221\265",
	"\360\237\221\266",
	"\360\237\221\267",
	"\360\237\221\270",
	"\360\237\221\271",
	"\360\237\221\272",
	"\360\237\221\273",
	"\360\237\221\274",
	"\360\237\221\275",
	"\360\237\221\276",
	"\360\237\221\277",
	"\360\237\222\200",
	"\360\237\222\201",
	"\360\237\222\202",
	"\360\237\222\203",
	"\360\237\222\204",
	"\360\237\222\205",
	"\360\237\222\206",
	"\360\237\222\207",
	"\360\237\222\210",
	"\360\237\222\211",
	"\360\237\222\212",
	"\360\237\222\213",
	"\360\237\222\214",
	"\360\237\222\215",
	"\360\237\222\216",
	"\360\237\222\217",
	"\360\237\222\220",
	"\360\237\222\221",
	"\360\237\222\222",
	"\360\237\222\223",
	"\360\237\222\224",
	"\360\237\222\225",
	"\360\237\222\226",
	"\360\237\222\227",
	"\360\237\222\230",
	"\360\237\222\231",
	"\360\237\222\232",
	"\360\237\222\233",
	"\360\237\222\234",
	"\360\237\222\235",
	"\360\237\222\236",
	"\360\237\222\237",
	"\360\237\222\240",
	"\360\237\222\241",
	"\360\237\222\242",
	"\360\237\222\243",
	"\360\237\222\244",
	"\360\237\222\245",
	"\360\237\222\246",
	"\360\237\222\247",
	"\360\237\222\250",
	"\360\237\222\251",
	"\360\237\222\252",
	"\360\237\222\253",
	"\360\237\222\254",
	"\360\237\222\255",
	"\360\237\222\256",
	"\360\237\222\257",
	"\360\237\222\260",
	"\360\237\222\261",
	"\360\237\222\262",
	"\360\237\222\263",
	"\360\237\222\264",
	"\360\237\222\265",
	"\360\237\222\266",
	"\360\237\222\267",
	"\360\237\222\270",
	"\360\237\222\271",
	"\360\237\222\272",
	"\360\237\222\273",
	"\360\237\222\274",
	"\360\237\222\275",
	"\360\237\222\276",
	"\360\237\222\277",
	"\360\237\223\200",
	"\360\237\223\201",
	"\360\237\223\202",
	"\360\237\223\203",
	"\360\237\223\204",
	"\360\237\223\205",
	"\360\237\223\206",
	"\360\237\223\207",
	"\360\237\223\210",
	"\360\237\223\211",
	"\360\237\223\212",
	"\360\237\223\213",
	"\360\237\223\214",
	"\360\237\223\215",
	"\360\237\223\216",
	"\360\237\223\217",
	"\360\237\223\220",
	"\360\237\223\221",
	"\360\237\223\222",
	"\360\237\223\223",
	"\360\237\223\224",
	"\360\237\223\225",
	"\360\237\223\226",
	"\360\237\223\227",
	"\360\237\223\230",
	"\360\237\223\231",
	"\360\237\223\232",
	"\360\237\223\233",
	"\360\237\223\234",
	"\360\237\223\235",
	"\360\237\223\236",
	"\360\237\223\237",
	"\360\237\223\240",
	"\360\237\223\241",
	"\360\237\223\242",
	"\360\237\223\243",
	"\360\237\223\244",
	"\360\237\223\245",
	"\360\237\223\246",
	"\360\237\223\247",
	"\360\237\223\250",
	"\360\237\223\251",
	"\360\237\223\252",
	"\360\237\223\253",
	"\360\237\223\254",
	"\360\237\223\255",
	"\360\237\223\256",
	"\360\237\223\257",
	"\360\237\223\260",
	"\360\237\223\261",
	"\360\237\223\262",
	"\360\237\223\263",
	"\360\237\223\264",
	"\360\237\223\265",
	"\360\237\223\266",
	"\360\237\223\267",
	"\360\237\223\270",
	"\360\237\223\271",
	"\360\237\223\272",
	"\360\237\223\273",
	"\360\237\223\274",
	"\360\237\223\277",
	"\360\237\224\200",
	"\360\237\224\201",
	"\360\237\224\202",
	"\360\237\224\203",
	"\360\237\224\204",
	"\360\237\224\205",
	"\360\237\224\206",
	"\360\237\224\207",
	"\360\237\224\210",
	"\360\237\224\211",
	"\360\237\224\212",
	"\360\237\224\213",
	"\360\237\224\214",
	"\360\237\224\215",
	"\360\237\224\216",
	"\360\237\224\217",
	"\360\237\224\220",
	"\360\237\224\221",
	"\360\237\224\222",
	"\360\237\224\223",
	"\360\237\224\224",
	"\360\237\224\225",
	"\360\237\224\226",
	"\360\237\224\227",
	"\360\237\224\230",
	"\360\237\224\231",
	"\360\237\224\232",
	"\360\237\224\233",
	"\360\237\224\234",
	"\360\237\224\235",
	"\360\237\224\236",
	"\360\237\224\237",
	"\360\237\224\240",
	"\360\237\224\241",
	"\360\237\224\242",
	"\360\237\224\243",
	"\360\237\224\244",
	"\360\237\224\245",
	"\360\237\224\246",
	"\360\237\224\247",
	"\360\237\224\250",
	"\360\237\224\251",
	"\360\237\224\252",
	"\360\237\224\253",
	"\360\237\224\254",
	"\360\237\224\255",
	"\360\237\224\256",
	"\360\237\224\257",
	"\360\237\224\260",
	"\360\237\224\261",
	"\360\237\224\262",
	"\360\237\224\263",
	"\360\237\224\264",
	"\360\237\224\265",
	"\360\237\224\266",
	"\360\237\224\267",
	"\360\237\224\270",
	"\360\237\224\271",
	"\360\237\224\272",
	"\360\237\224\273",
	"\360\237\224\274",
	"\360\237\224\275",
	"\360\237\225\213",
	"\360\237\225\214",
	"\360\237\225\215",
	"\360\237\225\216",
	"\360\237\225\220",
	"\360\237\225\221",
	"\360\237\225\222",
	"\360\237\225\223",
	"\360\237\225\224",
	"\360\237\225\225",
	"\360\237\225\226",
	"\360\237\225\227",
	"\360\237\225\230",
	"\360\237\225\231",
	"\360\237\225\232",
	"\360\237\225\233",
	"\360\237\225\234",
	"\360\237\225\235",
	"\360\237\225\236",
	"\360\237\225\237",
	"\360\237\225\240",
	"\360\237\225\241",
	"\360\237\225\242",
	"\360\237\225\243",
	"\360\237\225\244",
	"\360\237\225\245",
	"\360\237\225\246",
	"\360\237\225\247",
	"\360\237\225\272",
	"\360\237\226\225",
	"\360\237\226\226",
	"\360\237\226\244",
	"\360\237\227\273",
	"\360\237\227\274",
	"\360\237\227\275",
	"\360\237\227\276",
	"\360\237\227\277",
	"\360\237\230\200",
	"\360\237\230\201",
	"\360\237\230\202",
	"\360\237\230\203",
	"\360\237\230\204",
	"\360\237\230\205",
	"\360\237\230\206",
	"\360\237\230\207",
	"\360\237\230\210",
	"\360\237\230\211",
	"\360\237\230\212",
	"\360\237\230\213",
	"\360\237\230\214",
	"\360\237\230\215",
	"\360\237\230\216",
	"\360\237\230\217",
	"\360\237\230\220",
	"\360\237\230\221",
	"\360\237\230\222",
	"\360\237\230\223",
	"\360\237\230\224",
	"\360\237\230\225",
	"\360\237\230\226",
	"\360\237\230\227",
	"\360\237\230\230",
	"\360\237\230\231",
	"\360\237\230\232",
	"\360\237\230\233",
	"\360\237\230\234",
	"\360\237\230\235",
	"\360\237\230\236",
	"\360\237\230\237",
	"\360\237\230\240",
	"\360\237\230\241",
	"\360\237\230\242",
	"\360\237\230\243",
	"\360\237\230\244",
	"\360\237\230\245",
	"\360\237\230\246",
	"\360\237\230\247",
	"\360\237\230\250",
	"\360\237\230\251",
	"\360\237\230\252",
	"\360\237\230\253",
	"\360\237\230\254",
	"\360\237\230\255",
	"\360\237\230\256",
	"\360\237\230\257",
	"\360\237\230\260",
	"\360\237\230\261",
	"\360\237\230\262",
	"\360\237\230\263",
	"\360\237\230\264",
	"\360\237\230\265",
	"\360\237\230\266",
	"\360\237\230\267",
	"\360\237\230\270",
	"\360\237\230\271",
	"\360\237\230\272",
	"\360\237\230\273",
	"\360\237\230\274",
	"\360\237\230\275",
	"\360\237\230\276",
	"\360\237\230\277",
	"\360\237\231\200",
	"\360\237\231\201",
	"\360\237\231\202",
	"\360\237\231\203",
	"\360\237\231\204",
	"\360\237\231\205",
	"\360\237\231\206",
	"\360\237\231\207",
	"\360\237\231\210",
	"\360\237\231\211",
	"\360\237\231\212",
	"\360\237\231\213",
	"\360\237\231\214",
	"\360\237\231\215",
	"\360\237\231\216",
	"\360\237\231\217",
	"\360\237\232\200",
	"\360\237\232\201",
	"\360\237\232\202",
	"\360\237\232\203",
	"\360\237\232\204",
	"\360\237\232\205",
	"\360\237\232\206",
	"\360\237\232\207",
	"\360\237\232\210",
	"\360\237\232\211",
	"\360\237\232\212",
	"\360\237\232\213",
	"\360\237\232\214",
	"\360\237\232\215",
	"\360\237\232\216",
	"\360\237\232\217",
	"\360\237\232\220",
	"\360\237\232\221",
	"\360\237\232\222",
	"\360\237\232\223",
	"\360\237\232\224",
	"\360\237\232\225",
	"\360\237\232\226",
	"\360\237\232\227",
	"\360\237\232\230",
	"\360\237\232\231",
	"\360\237\232\232",
	"\360\237\232\233",
	"\360\237\232\234",
	"\360\237\232\235",
	"\360\237\232\236",
	"\360\237\232\237",
	"\360\237\232\240",
	"\360\237\232\241",
	"\360\237\232\242",
	"\360\237\232\243",
	"\360\237\232\244",
	"\360\237\232\245",
	"\360\237\232\246",
	"\360\237\232\247",
	"\360\237\232\250",
	"\360\237\232\251",
	"\360\237\232\252",
	"\360\237\232\253",
	"\360\237\232\254",
	"\360\237\232\255",
	"\360\237\232\256",
	"\360\237\232\257",
	"\360\237\232\260",
	"\360\237\232\261",
	"\360\237\232\262",
	"\360\237\232\263",
	"\360\237\232\264",
	"\360\237\232\265",
	"\360\237\232\266",
	"\360\237\232\267",
	"\360\237\232\270",
	"\360\237\232\271",
	"\360\237\232\272",
	"\360\237\232\273",
	"\360\237\232\274",
	"\360\237\232\275",
	"\360\237\232\276",
	"\360\237\232\277",
	"\360\237\233\200",
	"\360\237\233\201",
	"\360\237\233\202",
	"\360\237\233\203",
	"\360\237\233\204",
	"\360\237\233\205",
	"\360\237\233\214",
	"\360\237\233\220",
	"\360\237\233\221",
	"\360\237\233\222",
	"\360\237\233\225",
	"\360\237\233\226",
	"\360\237\233\227",
	"\360\237\233\234",
	"\360\237\233\235",
	"\360\237\233\236",
	"\360\237\233\237",
	"\360\237\233\253",
	"\360\237\233\254",
	"\360\237\233\264",
	"\360\237\233\265",
	"\360\237\233\266",
	"\360\237\233\267",
	"\360\237\233\270",
	"\360\237\233\271",
	"\360\237\233\272",
	"\360\237\233\273",
	"\360\237\233\274",
	"\360\237\237\240",
	"\360\237\237\241",
	"\360\237\237\242",
	"\360\237\237\243",
	"\360\237\237\244",
	"\360\237\237\245",
	"\360\237\237\246",
	"\360\237\237\247",
	"\360\237\237\250",
	"\360\237\237\251",
	"\360\237\237\252",
	"\360\237\237\253",
	"\360\237\237\260",
	"\360\237\244\214",
	"\360\237\244\215",
	"\360\237\244\216",
	"\360\237\244\217",
	"\360\237\244\220",
	"\360\237\244\221",
	"\360\237\244\222",
	"\360\237\244\223",
	"\360\237\244\224",
	"\360\237\244\225",
	"\360\237\244\226",
	"\360\237\244\227",
	"\360\237\244\230",
	"\360\237\244\231",
	"\360\237\244\232",
	"\360\237\244\233",
	"\360\237\244\234",
	"\360\237\244\235",
	"\360\237\244\236",
	"\360\237\244\237",
	"\360\237\244\240",
	"\360\237\244\241",
	"\360\237\244\242",
	"\360\237\244\243",
	"\360\237\244\244",
	"\360\237\244\245",
	"\360\237\244\246",
	"\360\237\244\247",
	"\360\237\244\250",
	"\360\237\244\251",
	"\360\237\244\252",
	"\360\237\244\253",
	"\360\237\244\254",
	"\360\237\244\255",
	"\360\237\244\256",
	"\360\237\244\257",
	"\360\237\244\260",
	"\360\237\244\261",
	"\360\237\244\262",
	"\360\237\244\263",
	"\360\237\244\264",
	"\360\237\244\265",
	"\360\237\244\266",
	"\360\237\244\267",
	"\360\237\244\270",
	"\360\237\244\271",
	"\360\237\244\272",
	"\360\237\244\274",
	"\360\237\244\275",
	"\360\237\244\276",
	"\360\237\244\277",
	"\360\237\245\200",
	"\360\237\245\201",
	"\360\237\245\202",
	"\360\237\245\203",
	"\360\237\245\204",
	"\360\237\245\205",
	"\360\237\245\207",
	"\360\237\245\210",
	"\360\237\245\211",
	"\360\237\245\212",
	"\360\237\245\213",
	"\360\237\245\214",
	"\360\237\245\215",
	"\360\237\245\216",
	"\360\237\245\217",
	"\360\237\245\220",
	"\360\237\245\221",
	"\360\237\245\222",
	"\360\237\245\223",
	"\360\237\245\224",
	"\360\237\245\225",
	"\360\237\245\226",
	"\360\237\245\227",
	"\360\237\245\230",
	"\360\237\245\231",
	"\360\237\245\232",
	"\360\237\245\233",
	"\360\237\245\234",
	"\360\237\245\235",
	"\360\237\245\236",
	"\360\237\245\237",
	"\360\237\245\240",
	"\360\237\245\241",
	"\360\237\245\242",
	"\360\237\245\243",
	"\360\237\245\244",
	"\360\237\245\245",
	"\360\237\245\246",
	"\360\237\245\247",
	"\360\237\245\250",
	"\360\237\245\251",
	"\360\237\245\252",
	"\360\237\245\253",
	"\360\237\245\254",
	"\360\237\245\255",
	"\360\237\245\256",
	"\360\237\245\257",
	"\360\237\245\260",
	"\360\237\245\261",
	"\360\237\245\262",
	"\360\237\245\263",
	"\360\237\245\264",
	"\360\237\245\265",
	"\360\237\245\266",
	"\360\237\245\267",
	"\360\237\245\270",
	"\360\237\245\271",
	"\360\237\245\272",
	"\360\237\245\273",
	"\360\237\245\274",
	"\360\237\245\275",
	"\360\237\245\276",
	"\360\237\245\277",
	"\360\237\246\200",
	"\360\237\246\201",
	"\360\237\246\202",
	"\360\237\246\203",
	"\360\237\246\204",
	"\360\237\246\205",
	"\360\237\246\206",
	"\360\237\246\207",
	"\360\237\246\210",
	"\360\237\246\211",
	"\360\237\246\212",
	"\360\237\246\213",
	"\360\237\246\214",
	"\360\237\246\215",
	"\360\237\246\216",
	"\360\237\246\217",
	"\360\237\246\220",
	"\360\237\246\221",
	"\360\237\246\222",
	"\360\237\246\223",
	"\360\237\246\224",
	"\360\237\246\225",
	"\360\237\246\226",
	"\360\237\246\227",
	"\360\237\246\230",
	"\360\237\246\231",
	"\360\237\246\232",
	"\360\237\246\233",
	"\360\237\246\234",
	"\360\237\246\235",
	"\360\237\246\236",
	"\360\237\246\237",
	"\360\237\246\240",
	"\360\237\246\241",
	"\360\237\246\242",
	"\360\237\246\243",
	"\360\237\246\244",
	"\360\237\246\245",
	"\360\237\246\246",
	"\360\237\246\247",
	"\360\237\246\250",
	"\360\237\246\251",
	"\360\237\246\252",
	"\360\237\246\253",
	"\360\237\246\254",
	"\360\237\246\255",
	"\360\237\246\256",
	"\360\237\246\257",
	"\360\237\246\260",
	"\360\237\246\261",
	"\360\237\246\262",
	"\360\237\246\263",
	"\360\237\246\264",
	"\360\237\246\265",
	"\360\237\246\266",
	"\360\237\246\267",
	"\360\237\246\270",
	"\360\237\246\271",
	"\360\237\246\272",
	"\360\237\246\273",
	"\360\237\246\274",
	"\360\237\246\275",
	"\360\237\246\276",
	"\360\237\246\277",
	"\360\237\247\200",
	"\360\237\247\201",
	"\360\237\247\202",
	"\360\237\247\203",
	"\360\237\247\204",
	"\360\237\247\205",
	"\360\237\247\206",
	"\360\237\247\207",
	"\360\237\247\210",
	"\360\237\247\211",
	"\360\237\247\212",
	"\360\237\247\213",
	"\360\237\247\214",
	"\360\237\247\215",
	"\360\237\247\216",
	"\360\237\247\217",
	"\360\237\247\220",
	"\360\237\247\221",
	"\360\237\247\222",
	"\360\237\247\223",
	"\360\237\247\224",
	"\360\237\247\225",
	"\360\237\247\226",
	"\360\237\247\227",
	"\360\237\247\230",
	"\360\237\247\231",
	"\360\237\247\232",
	"\360\237\247\233",
	"\360\237\247\234",
	"\360\237\247\235",
	"\360\237\247\236",
	"\360\237\247\237",
	"\360\237\247\240",
	"\360\237\247\241",
	"\360\237\247\242",
	"\360\237\247\243",
	"\360\237\247\244",
	"\360\237\247\245",
	"\360\237\247\246",
	"\360\237\247\247",
	"\360\237\247\250",
	"\360\237\247\251",
	"\360\237\247\252",
	"\360\237\247\253",
	"\360\237\247\254",
	"\360\237\247\255",
	"\360\237\247\256",
	"\360\237\247\257",
	"\360\237\247\260",
	"\360\237\247\261",
	"\360\237\247\262",
	"\360\237\247\263",
	"\360\237\247\264",
	"\360\237\247\265",
	"\360\237\247\266",
	"\360\237\247\267",
	"\360\237\247\270",
	"\360\237\247\271",
	"\360\237\247\272",
	"\360\237\247\273",
	"\360\237\247\274",
	"\360\237\247\275",
	"\360\237\247\276",
	"\360\237\247\277",
	"\360\237\251\260",
	"\360\237\251\261",
	"\360\237\251\262",
	"\360\237\251\263",
	"\360\237\251\264",
	"\360\237\251\265",
	"\360\237\251\266",
	"\360\237\251\267",
	"\360\237\251\270",
	"\360\237\251\271",
	"\360\237\251\272",
	"\360\237\251\273",
	"\360\237\251\274",
	"\360\237\252\200",
	"\360\237\252\201",
	"\360\237\252\202",
	"\360\237\252\203",
	"\360\237\252\204",
	"\360\237\252\205",
	"\360\237\252\206",
	"\360\237\252\207",
	"\360\237\252\210",
	"\360\237\252\220",
	"\360\237\252\221",
	"\360\237\252\222",
	"\360\237\252\223",
	"\360\237\252\224",
	"\360\237\252\225",
	"\360\237\252\226",
	"\360\237\252\227",
	"\360\237\252\230",
	"\360\237\252\231",
	"\360\237\252\232",
	"\360\237\252\233",
	"\360\237\252\234",
	"\360\237\252\235",
	"\360\237\252\236",
	"\360\237\252\237",
	"\360\237\252\240",
	"\360\237\252\241",
	"\360\237\252\242",
	"\360\237\252\243",
	"\360\237\252\244",
	"\360\237\252\245",
	"\360\237\252\246",
	"\360\237\252\247",
	"\360\237\252\250",
	"\360\237\252\251",
	"\360\237\252\252",
	"\360\237\252\253",
	"\360\237\252\254",
	"\360\237\252\255",
	"\360\237\252\256",
	"\360\237\252\257",
	"\360\237\252\260",
	"\360\237\252\261",
	"\360\237\252\262",
	"\360\237\252\263",
	"\360\237\252\264",
	"\360\237\252\265",
	"\360\237\252\266",
	"\360\237\252\267",
	"\360\237\252\270",
	"\360\237\252\271",
	"\360\237\252\272",
	"\360\237\252\273",
	"\360\237\252\274",
	"\360\237\252\275",
	"\360\237\252\277",
	"\360\237\253\200",
	"\360\237\253\201",
	"\360\237\253\202",
	"\360\237\253\203",
	"\360\237\253\204",
	"\360\237\253\205",
	"\360\237\253\216",
	"\360\237\253\217",
	"\360\237\253\220",
	"\360\237\253\221",
	"\360\237\253\222",
	"\360\237\253\223",
	"\360\237\253\224",
	"\360\237\253\225",
	"\360\237\253\226",
	"\360\237\253\227",
	"\360\237\253\230",
	"\360\237\253\231",
	"\360\237\253\232",
	"\360\237\253\233",
	"\360\237\253\240",
	"\360\237\253\241",
	"\360\237\253\242",
	"\360\237\253\243",
	"\360\237\253\244",
	"\360\237\253\245",
	"\360\237\253\246",
	"\360\237\253\247",
	"\360\237\253\250",
	"\360\237\253\260",
	"\360\237\253\261",
	"\360\237\253\262",
	"\360\237\253\263",
	"\360\237\253\264",
	"\360\237\253\265",
	"\360\237\253\266",
	"\360\237\253\267",
	"\360\237\253\270",
};
const int32_t guji_rgi_emoji_lengths[] = {
	35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 
	35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 
	35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 
	35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 
	35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 
	35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 27, 
	28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 
	28, 28, 28, 28, 28, 28, 28, 28, 28, 27, 27, 28, 28, 28, 28, 28, 
	28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 
	28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 
	28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 
	28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 
	28, 28, 28, 28, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 
	26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 25, 25, 
	25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 
	26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 
	26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 
	26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 
	26, 26, 20, 20, 20, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 
	16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 16, 
	16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 16, 16, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 16, 17, 18, 18, 18, 18, 18, 18, 18, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 
	18, 18, 18, 18, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 16, 16, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 18, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 
	17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 19, 
	19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 
	19, 19, 19, 13, 13, 13, 13, 13, 13, 13, 13, 14, 13, 13, 13, 13, 
	13, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 13, 13, 13, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 
	13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 13, 13, 13, 13, 13, 
	13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 
	13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 
	13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 
	15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 13, 13, 13, 13, 13, 13, 
	13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 
	7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 10, 11, 10, 11, 
	11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 
	11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 
	11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 
	11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 
	11, 11, 11, 11, 11, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 
	6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 
	6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 
	7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 
	6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 
	6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 
	7, 7, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 
	7, 7, 7, 7, 7, 6, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 
	6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 
	6, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 7, 7, 
	7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 
	7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 7, 8, 8, 8, 8, 8, 
	7, 8, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 
	7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 7, 8, 8, 
	8, 8, 8, 7, 7, 7, 7, 8, 8, 8, 8, 8, 7, 7, 7, 7, 
	7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 
	7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 7, 8, 8, 8, 8, 8, 7, 7, 7, 7, 
	7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
	8, 8, 8, 8, 8, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 
	3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 
	3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 
	3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 
	3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
	4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 
};
const int32_t guji_rgi_emoji_count = 3664;

int guji_rune_in_ranges(int32_t r, const guji_rune_range_t *ranges, int32_t count) {
	int32_t lo = 0, hi = count - 1;
	while (lo <= hi) {
		int32_t mid = lo + (hi - lo) / 2;
		if (r < ranges[mid].lo) {
			hi = mid - 1;
		} else if (r > ranges[mid].hi) {
			lo = mid + 1;
		} else {
			return 1;
		}
	}
	return 0;
}

/* guji_unicode_property resolves a canonical property name (a general
   category, script, or curated binary property — the parser's canonical
   keys) to its range table, or NULL if unknown. */
const guji_unicode_table_t *guji_unicode_property(const char *name) {
	int32_t lo = 0, hi = guji_unicode_property_count - 1;
	while (lo <= hi) {
		int32_t mid = lo + (hi - lo) / 2;
		int c = strcmp(name, guji_unicode_properties[mid].name);
		if (c < 0) {
			hi = mid - 1;
		} else if (c > 0) {
			lo = mid + 1;
		} else {
			return &guji_unicode_properties[mid];
		}
	}
	return NULL;
}

/* guji_is_word_rune is the Unicode-aware \w / \b membership test (section
   13.5): [\p{Alphabetic}\p{M}\p{Nd}\p{Pc}]. */
int guji_is_word_rune(int32_t r) {
	return guji_rune_in_ranges(r, guji_word_ranges, guji_word_range_count);
}

/* guji_simple_fold is Go's unicode.SimpleFold: the next scalar in the simple
   case-folding orbit, or r itself when r folds only to itself. */
int32_t guji_simple_fold(int32_t r) {
	int32_t lo = 0, hi = guji_fold_pair_count - 1;
	while (lo <= hi) {
		int32_t mid = lo + (hi - lo) / 2;
		if (r < guji_fold_pairs[mid].from) {
			hi = mid - 1;
		} else if (r > guji_fold_pairs[mid].from) {
			lo = mid + 1;
		} else {
			return guji_fold_pairs[mid].to;
		}
	}
	return r;
}

/* guji_grapheme_cbreak returns the scalar's Grapheme_Cluster_Break class
   (GUJI_GCB_*), GUJI_GCB_OTHER for unassigned scalars. */
int guji_grapheme_cbreak(int32_t r) {
	int32_t lo = 0, hi = guji_gcb_range_count - 1;
	while (lo <= hi) {
		int32_t mid = lo + (hi - lo) / 2;
		if (r < guji_gcb_ranges[mid].lo) {
			hi = mid - 1;
		} else if (r > guji_gcb_ranges[mid].hi) {
			lo = mid + 1;
		} else {
			return (int)guji_gcb_ranges[mid].cls;
		}
	}
	return GUJI_GCB_OTHER;
}


/* Guji regex VM runtime. The VM consumes compiled Program IR; the parser and
   compiler below produce that IR from pattern text. */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

enum {
	GUJI_RE_OP_CHAR = 0,
	GUJI_RE_OP_CLASS = 1,
	GUJI_RE_OP_ANY = 2,
	GUJI_RE_OP_ANYNL = 3,
	GUJI_RE_OP_GRAPHEME_X = 4,
	GUJI_RE_OP_RGI_EMOJI = 5,
	GUJI_RE_OP_SPLIT = 6,
	GUJI_RE_OP_JMP = 7,
	GUJI_RE_OP_SAVE = 8,
	GUJI_RE_OP_ASSERT_BOT = 9,
	GUJI_RE_OP_ASSERT_EOT = 10,
	GUJI_RE_OP_ASSERT_BOL = 11,
	GUJI_RE_OP_ASSERT_EOL = 12,
	GUJI_RE_OP_ASSERT_EOT_ABS = 13,
	GUJI_RE_OP_WORD_B = 14,
	GUJI_RE_OP_NWORD_B = 15,
	GUJI_RE_OP_BACKREF = 16,
	GUJI_RE_OP_LOOK_START = 17,
	GUJI_RE_OP_LOOK_END = 18,
	GUJI_RE_OP_CUT_MARK = 19,
	GUJI_RE_OP_CUT = 20,
	GUJI_RE_OP_MATCH = 21,
};

enum {
	GUJI_RE_LOOK_AHEAD_POS = 0,
	GUJI_RE_LOOK_AHEAD_NEG = 1,
	GUJI_RE_LOOK_BEHIND_POS = 2,
	GUJI_RE_LOOK_BEHIND_NEG = 3,
};

typedef struct { int32_t lo; int32_t hi; } guji_regex_range_t;
typedef struct { int32_t negated; const guji_regex_range_t *ranges; int32_t range_count; } guji_regex_class_t;
typedef struct {
	int32_t op;
	int32_t rune;
	int32_t cls;
	int32_t out;
	int32_t out1;
	int32_t slot;
	int32_t fold;
	int32_t ascii;
} guji_regex_inst_t;
typedef struct {
	int32_t kind;
	int32_t minw;
	int32_t maxw;
	int32_t after_pc;
} guji_regex_look_t;

typedef struct guji_regex_program guji_regex_program_t;
struct guji_regex_program {
	int32_t version;
	const guji_regex_inst_t *insts;
	int32_t inst_count;
	const guji_regex_class_t *classes;
	int32_t class_count;
	int32_t num_cap;
	/* Engine captures include private groups retained for splice-local
	   backreferences. Public captures are the ordered slots exposed through
	   Match and replacement templates. */
	int32_t public_num_cap;
	const int32_t *public_cap_indexes;
	const char *const *cap_names;
	const guji_regex_look_t *looks;
	int32_t look_count;
	const guji_regex_program_t *const *subprogs;
	int32_t subprog_count;
};

typedef struct {
	int32_t matched;
	int32_t span_count;
	int32_t spans[64][2];
} guji_regex_match_t;

typedef struct {
	int32_t pc;
	int32_t pos;
	int32_t *caps;
	int32_t *seen_pc;
	int32_t *seen_pos;
	int32_t seen_len;
	int32_t seen_cap;
	int32_t *cuts;
	int32_t cuts_len;
	int32_t cuts_cap;
} guji_regex_state_t;

static void *guji_regex_xmalloc(size_t n) {
	void *p = malloc(n ? n : 1);
	if (!p) {
		abort();
	}
	return p;
}

static int32_t *guji_regex_clone_i32(const int32_t *in, int32_t n) {
	if (n <= 0) {
		return NULL;
	}
	int32_t *out = (int32_t *)guji_regex_xmalloc(sizeof(int32_t) * (size_t)n);
	memcpy(out, in, sizeof(int32_t) * (size_t)n);
	return out;
}

static void guji_regex_state_free(guji_regex_state_t *st) {
	free(st->caps);
	free(st->seen_pc);
	free(st->seen_pos);
	free(st->cuts);
	memset(st, 0, sizeof(*st));
}

static guji_regex_state_t guji_regex_state_clone(const guji_regex_state_t *st, int32_t cap_slots) {
	guji_regex_state_t out = *st;
	out.caps = guji_regex_clone_i32(st->caps, cap_slots);
	out.seen_pc = guji_regex_clone_i32(st->seen_pc, st->seen_len);
	out.seen_pos = guji_regex_clone_i32(st->seen_pos, st->seen_len);
	out.seen_cap = st->seen_len;
	out.cuts = guji_regex_clone_i32(st->cuts, st->cuts_len);
	out.cuts_cap = st->cuts_len;
	return out;
}

static int guji_regex_seen_has(guji_regex_state_t *st, int32_t pc, int32_t pos) {
	for (int32_t i = 0; i < st->seen_len; i++) {
		if (st->seen_pc[i] == pc && st->seen_pos[i] == pos) {
			return 1;
		}
	}
	return 0;
}

static void guji_regex_seen_add(guji_regex_state_t *st, int32_t pc, int32_t pos) {
	if (st->seen_len == st->seen_cap) {
		int32_t ncap = st->seen_cap ? st->seen_cap * 2 : 8;
		st->seen_pc = (int32_t *)realloc(st->seen_pc, sizeof(int32_t) * (size_t)ncap);
		st->seen_pos = (int32_t *)realloc(st->seen_pos, sizeof(int32_t) * (size_t)ncap);
		if (!st->seen_pc || !st->seen_pos) {
			abort();
		}
		st->seen_cap = ncap;
	}
	st->seen_pc[st->seen_len] = pc;
	st->seen_pos[st->seen_len] = pos;
	st->seen_len++;
}

static void guji_regex_cut_push(guji_regex_state_t *st, int32_t watermark) {
	if (st->cuts_len == st->cuts_cap) {
		int32_t ncap = st->cuts_cap ? st->cuts_cap * 2 : 4;
		st->cuts = (int32_t *)realloc(st->cuts, sizeof(int32_t) * (size_t)ncap);
		if (!st->cuts) {
			abort();
		}
		st->cuts_cap = ncap;
	}
	st->cuts[st->cuts_len++] = watermark;
}

/* GUJI_RX_RUNE_ERROR is the Unicode replacement scalar (U+FFFD) that Go's
   utf8.DecodeRuneInString yields for every malformed byte sequence. The
   interpreter's regex VM decodes through that exact function, so the native
   decoder must mirror it byte-for-byte: invalid lead bytes, truncated tails,
   overlong forms, surrogate-range and out-of-range encodings all decode to
   U+FFFD and advance exactly one byte. Before this, a lone 0xFF decoded to the
   raw codepoint U+00FF ('ÿ', a \w word character) and native `~~ /\w/` matched
   invalid UTF-8 the interpreter rejected (D5). */
#define GUJI_RX_RUNE_ERROR 0xFFFD

/* guji_rx_utf8_first mirrors Go's unicode/utf8 `first` table: it maps each
   possible lead byte to a packed descriptor. 0xF0 = ASCII (size 1), 0xF1 =
   invalid lead (size 1, decode to U+FFFD); any other value v encodes the
   sequence size in (v & 7) and the accept-range selector for the first
   continuation byte in (v >> 4). */
static const unsigned char guji_rx_utf8_first[256] = {
	/* 0x00-0x7F: ASCII */
	0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0,
	0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0,
	0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0,
	0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0,
	0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0,
	0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0,
	0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0,
	0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0,
	/* 0x80-0xBF: continuation bytes — invalid as lead */
	0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1,
	0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1,
	0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1,
	0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1,
	/* 0xC0-0xC1: overlong 2-byte leads — invalid */
	0xF1, 0xF1,
	/* 0xC2-0xDF: valid 2-byte leads (size 2, accept 0) */
	0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
	0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
	/* 0xE0: size 3, accept 1 (second byte 0xA0-0xBF) */
	0x13,
	/* 0xE1-0xEC: size 3, accept 0 */
	0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0x03, 0x03,
	/* 0xED: size 3, accept 2 (second byte 0x80-0x9F, excludes surrogates) */
	0x23,
	/* 0xEE-0xEF: size 3, accept 0 */
	0x03, 0x03,
	/* 0xF0: size 4, accept 3 (second byte 0x90-0xBF) */
	0x34,
	/* 0xF1-0xF3: size 4, accept 0 */
	0x04, 0x04, 0x04,
	/* 0xF4: size 4, accept 4 (second byte 0x80-0x8F) */
	0x44,
	/* 0xF5-0xFF: invalid leads (out of range) */
	0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1, 0xF1,
};

static int guji_regex_read_rune(const char *s, int32_t len, int32_t pos, int32_t *r, int32_t *next) {
	if (pos < 0 || pos >= len) {
		return 0;
	}
	unsigned char s0 = (unsigned char)s[pos];
	unsigned char x = guji_rx_utf8_first[s0];
	if (x >= 0xF0) {
		/* 0xF0 = ASCII (decode the byte itself); 0xF1 = invalid lead (U+FFFD). */
		*r = (x == 0xF1) ? GUJI_RX_RUNE_ERROR : (int32_t)s0;
		*next = pos + 1;
		return 1;
	}
	int32_t sz = (int32_t)(x & 7);
	unsigned char acc_lo, acc_hi;
	switch (x >> 4) {
	case 1:
		acc_lo = 0xA0;
		acc_hi = 0xBF;
		break;
	case 2:
		acc_lo = 0x80;
		acc_hi = 0x9F;
		break;
	case 3:
		acc_lo = 0x90;
		acc_hi = 0xBF;
		break;
	case 4:
		acc_lo = 0x80;
		acc_hi = 0x8F;
		break;
	default:
		acc_lo = 0x80;
		acc_hi = 0xBF;
		break;
	}
	if (len - pos < sz) {
		*r = GUJI_RX_RUNE_ERROR;
		*next = pos + 1;
		return 1;
	}
	unsigned char s1 = (unsigned char)s[pos + 1];
	if (s1 < acc_lo || s1 > acc_hi) {
		*r = GUJI_RX_RUNE_ERROR;
		*next = pos + 1;
		return 1;
	}
	if (sz <= 2) {
		*r = ((int32_t)(s0 & 0x1F) << 6) | (int32_t)(s1 & 0x3F);
		*next = pos + 2;
		return 1;
	}
	unsigned char s2 = (unsigned char)s[pos + 2];
	if (s2 < 0x80 || s2 > 0xBF) {
		*r = GUJI_RX_RUNE_ERROR;
		*next = pos + 1;
		return 1;
	}
	if (sz <= 3) {
		*r = ((int32_t)(s0 & 0x0F) << 12) | ((int32_t)(s1 & 0x3F) << 6) | (int32_t)(s2 & 0x3F);
		*next = pos + 3;
		return 1;
	}
	unsigned char s3 = (unsigned char)s[pos + 3];
	if (s3 < 0x80 || s3 > 0xBF) {
		*r = GUJI_RX_RUNE_ERROR;
		*next = pos + 1;
		return 1;
	}
	*r = ((int32_t)(s0 & 0x07) << 18) | ((int32_t)(s1 & 0x3F) << 12) | ((int32_t)(s2 & 0x3F) << 6) | (int32_t)(s3 & 0x3F);
	*next = pos + 4;
	return 1;
}

static int guji_regex_is_rune_start(unsigned char c) {
	return (c & 0xC0) != 0x80;
}

static int32_t guji_regex_clamp_start(const char *s, int32_t len, int32_t start) {
	(void)s;
	if (start <= 0) {
		return 0;
	}
	if (start >= len) {
		return len;
	}
	while (start < len && !guji_regex_is_rune_start((unsigned char)s[start])) {
		start++;
	}
	return start;
}

static int32_t guji_regex_next_start(const char *s, int32_t len, int32_t pos) {
	int32_t r = 0, next = pos;
	if (pos >= len) {
		return len;
	}
	if (!guji_regex_read_rune(s, len, pos, &r, &next)) {
		return len;
	}
	return next;
}

static int32_t guji_regex_prev_rune_start(const char *s, int32_t pos) {
	if (pos <= 0) {
		return -1;
	}
	pos--;
	while (pos > 0 && !guji_regex_is_rune_start((unsigned char)s[pos])) {
		pos--;
	}
	return pos;
}

static int32_t guji_regex_walk_back_scalars(const char *s, int32_t pos, int32_t w) {
	for (int32_t i = 0; i < w && pos > 0; i++) {
		pos = guji_regex_prev_rune_start(s, pos);
	}
	return pos < 0 ? 0 : pos;
}

static int guji_regex_class_match(const guji_regex_class_t *cls, int32_t r) {
	int in = 0;
	for (int32_t i = 0; i < cls->range_count; i++) {
		if (r >= cls->ranges[i].lo && r <= cls->ranges[i].hi) {
			in = 1;
			break;
		}
	}
	return cls->negated ? !in : in;
}

static int guji_regex_word_at(const char *s, int32_t len, int32_t pos, int ascii) {
	int32_t r = 0, next = 0;
	if (pos < 0 || pos >= len || !guji_regex_read_rune(s, len, pos, &r, &next)) {
		return 0;
	}
	if (r < 0x80 || ascii) {
		return (r >= '0' && r <= '9') || (r >= 'A' && r <= 'Z') || (r >= 'a' && r <= 'z') || r == '_';
	}
	return guji_is_word_rune(r);
}

static int guji_regex_same_fold(int32_t a, int32_t b) {
	for (int32_t r = a;;) {
		if (r == b) {
			return 1;
		}
		r = guji_simple_fold(r);
		if (r == a) {
			return 0;
		}
	}
}

static int guji_regex_backref(const char *s, int32_t len, int32_t pos, const int32_t *caps, int32_t slot, int fold, int32_t *next_out) {
	if (slot < 0) {
		return 0;
	}
	int32_t start = caps[slot];
	int32_t end = caps[slot + 1];
	if (start < 0 || end < start || end > len) {
		return 0;
	}
	if (!fold) {
		int32_t n = end - start;
		if (len - pos < n || memcmp(s + pos, s + start, (size_t)n) != 0) {
			return 0;
		}
		*next_out = pos + n;
		return 1;
	}
	int32_t ref = start;
	int32_t cur = pos;
	while (ref < end) {
		int32_t want = 0, want_next = 0, got = 0, got_next = 0;
		if (!guji_regex_read_rune(s, len, ref, &want, &want_next) || !guji_regex_read_rune(s, len, cur, &got, &got_next) || !guji_regex_same_fold(got, want)) {
			return 0;
		}
		ref = want_next;
		cur = got_next;
	}
	*next_out = cur;
	return 1;
}

static int guji_regex_is_ext_pict(int32_t r) {
	const guji_unicode_table_t *tab = guji_unicode_property("Extended_Pictographic");
	if (!tab) {
		return 0;
	}
	for (int32_t i = 0; i < tab->count; i++) {
		if (r >= tab->ranges[i].lo && r <= tab->ranges[i].hi) {
			return 1;
		}
	}
	return 0;
}

typedef struct {
	int32_t prev;
	int32_t ri_run;
	int32_t pict_extend;
	int32_t pict_zwj;
} guji_regex_gstate_t;

static void guji_regex_gstate_accept(guji_regex_gstate_t *st, int32_t cat, int pict) {
	st->prev = cat;
	st->ri_run = (cat == GUJI_GCB_REGIONAL_INDICATOR) ? st->ri_run + 1 : 0;
	if (pict) {
		st->pict_extend = 1;
		st->pict_zwj = 0;
	} else if (st->pict_extend && cat == GUJI_GCB_EXTEND) {
		/* stay in Extend* */
	} else if (st->pict_extend && cat == GUJI_GCB_ZWJ) {
		st->pict_extend = 0;
		st->pict_zwj = 1;
	} else {
		st->pict_extend = 0;
		st->pict_zwj = 0;
	}
}

static int guji_regex_gbreak_before(guji_regex_gstate_t *st, int32_t cat, int pict) {
	int32_t p = st->prev;
	if (p == GUJI_GCB_CR && cat == GUJI_GCB_LF) return 0;
	if (p == GUJI_GCB_CONTROL || p == GUJI_GCB_CR || p == GUJI_GCB_LF) return 1;
	if (cat == GUJI_GCB_CONTROL || cat == GUJI_GCB_CR || cat == GUJI_GCB_LF) return 1;
	if (p == GUJI_GCB_L && (cat == GUJI_GCB_L || cat == GUJI_GCB_V || cat == GUJI_GCB_LV || cat == GUJI_GCB_LVT)) return 0;
	if ((p == GUJI_GCB_LV || p == GUJI_GCB_V) && (cat == GUJI_GCB_V || cat == GUJI_GCB_T)) return 0;
	if ((p == GUJI_GCB_LVT || p == GUJI_GCB_T) && cat == GUJI_GCB_T) return 0;
	if (cat == GUJI_GCB_EXTEND || cat == GUJI_GCB_ZWJ) return 0;
	if (cat == GUJI_GCB_SPACINGMARK) return 0;
	if (p == GUJI_GCB_PREPEND) return 0;
	if (st->pict_zwj && pict) return 0;
	if (p == GUJI_GCB_REGIONAL_INDICATOR && cat == GUJI_GCB_REGIONAL_INDICATOR && st->ri_run % 2 == 1) return 0;
	return 1;
}

static int32_t guji_regex_grapheme_end(const char *s, int32_t len, int32_t start) {
	int32_t r = 0, pos = start;
	if (!guji_regex_read_rune(s, len, start, &r, &pos)) {
		return start;
	}
	guji_regex_gstate_t st;
	memset(&st, 0, sizeof(st));
	guji_regex_gstate_accept(&st, guji_grapheme_cbreak(r), guji_regex_is_ext_pict(r));
	while (pos < len) {
		int32_t r2 = 0, next = 0;
		if (!guji_regex_read_rune(s, len, pos, &r2, &next)) {
			break;
		}
		int32_t cat = guji_grapheme_cbreak(r2);
		int pict = guji_regex_is_ext_pict(r2);
		if (guji_regex_gbreak_before(&st, cat, pict)) {
			break;
		}
		guji_regex_gstate_accept(&st, cat, pict);
		pos = next;
	}
	return pos;
}

static int guji_regex_rgi_emoji(const char *s, int32_t len, int32_t pos, int32_t *end_out) {
	for (int32_t i = 0; i < guji_rgi_emoji_count; i++) {
		int32_t n = guji_rgi_emoji_lengths[i];
		if (pos + n <= len && memcmp(s + pos, guji_rgi_emoji_sequences[i], (size_t)n) == 0) {
			*end_out = pos + n;
			return 1;
		}
	}
	return 0;
}

static int guji_regex_pop(guji_regex_state_t **stack, int32_t *len, guji_regex_state_t *out) {
	if (*len <= 0) {
		return 0;
	}
	*out = (*stack)[--(*len)];
	return 1;
}

static void guji_regex_push(guji_regex_state_t **stack, int32_t *len, int32_t *cap, guji_regex_state_t st) {
	if (*len == *cap) {
		int32_t ncap = *cap ? *cap * 2 : 8;
		*stack = (guji_regex_state_t *)realloc(*stack, sizeof(guji_regex_state_t) * (size_t)ncap);
		if (!*stack) {
			abort();
		}
		*cap = ncap;
	}
	(*stack)[(*len)++] = st;
}

static int guji_regex_backtrack(guji_regex_state_t **stack, int32_t *stack_len, guji_regex_state_t *st) {
	guji_regex_state_free(st);
	return guji_regex_pop(stack, stack_len, st);
}

static guji_regex_match_t guji_regex_match_at_caps(const guji_regex_program_t *prog, const char *s, int32_t len, int32_t start, int32_t anchor_end, const int32_t *inherit_caps, int32_t inherit_len) {
	guji_regex_match_t no;
	memset(&no, 0, sizeof(no));
	if (!prog || !prog->insts || prog->inst_count <= 0 || prog->num_cap + 1 > 64) {
		return no;
	}

	int32_t cap_slots = (prog->num_cap + 1) * 2;
	guji_regex_state_t st;
	memset(&st, 0, sizeof(st));
	st.pc = 0;
	st.pos = start;
	st.caps = (int32_t *)guji_regex_xmalloc(sizeof(int32_t) * (size_t)cap_slots);
	for (int32_t i = 0; i < cap_slots; i++) st.caps[i] = -1;
	if (inherit_caps) {
		int32_t n = inherit_len < cap_slots ? inherit_len : cap_slots;
		memcpy(st.caps, inherit_caps, sizeof(int32_t) * (size_t)n);
	}
	st.caps[0] = start;

	guji_regex_state_t *stack = NULL;
	int32_t stack_len = 0, stack_cap = 0;

	for (;;) {
		if (st.pc < 0 || st.pc >= prog->inst_count || guji_regex_seen_has(&st, st.pc, st.pos)) {
			if (!guji_regex_backtrack(&stack, &stack_len, &st)) {
				free(stack);
				return no;
			}
			continue;
		}
		guji_regex_seen_add(&st, st.pc, st.pos);
		guji_regex_inst_t inst = prog->insts[st.pc];
		int32_t r = 0, next = 0;
		switch (inst.op) {
		case GUJI_RE_OP_CHAR:
			if (!guji_regex_read_rune(s, len, st.pos, &r, &next) || r != inst.rune) {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.pos = next; st.pc++; break;
		case GUJI_RE_OP_CLASS:
			if (!guji_regex_read_rune(s, len, st.pos, &r, &next) || inst.cls < 0 || inst.cls >= prog->class_count || !guji_regex_class_match(&prog->classes[inst.cls], r)) {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.pos = next; st.pc++; break;
		case GUJI_RE_OP_ANY:
			if (!guji_regex_read_rune(s, len, st.pos, &r, &next) || r == '\n') {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.pos = next; st.pc++; break;
		case GUJI_RE_OP_ANYNL:
			if (!guji_regex_read_rune(s, len, st.pos, &r, &next)) {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.pos = next; st.pc++; break;
		case GUJI_RE_OP_GRAPHEME_X:
			if (st.pos >= len) {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.pos = guji_regex_grapheme_end(s, len, st.pos); st.pc++; break;
		case GUJI_RE_OP_RGI_EMOJI:
			if (!guji_regex_rgi_emoji(s, len, st.pos, &next)) {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.pos = next; st.pc++; break;
		case GUJI_RE_OP_SPLIT:
			guji_regex_push(&stack, &stack_len, &stack_cap, guji_regex_state_clone(&st, cap_slots));
			stack[stack_len - 1].pc = inst.out1;
			st.pc = inst.out;
			break;
		case GUJI_RE_OP_JMP:
			st.pc = inst.out; break;
		case GUJI_RE_OP_SAVE:
			if (inst.slot >= 0 && inst.slot < cap_slots) st.caps[inst.slot] = st.pos;
			st.pc++; break;
		case GUJI_RE_OP_BACKREF:
			if (inst.slot < 0 || inst.slot + 1 >= cap_slots || !guji_regex_backref(s, len, st.pos, st.caps, inst.slot, inst.fold, &next)) {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.pos = next; st.pc++; break;
		case GUJI_RE_OP_ASSERT_BOT:
			if (st.pos != 0) {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.pc++; break;
		case GUJI_RE_OP_ASSERT_EOT:
			if (st.pos != len) {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.pc++; break;
		case GUJI_RE_OP_ASSERT_BOL:
			if (st.pos != 0 && s[st.pos - 1] != '\n') {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.pc++; break;
		case GUJI_RE_OP_ASSERT_EOL:
			if (st.pos != len && s[st.pos] != '\n') {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.pc++; break;
		case GUJI_RE_OP_ASSERT_EOT_ABS:
			if (!(st.pos == len || (st.pos + 1 == len && s[st.pos] == '\n'))) {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.pc++; break;
		case GUJI_RE_OP_WORD_B:
		case GUJI_RE_OP_NWORD_B: {
			int boundary = guji_regex_word_at(s, len, guji_regex_prev_rune_start(s, st.pos), inst.ascii) != guji_regex_word_at(s, len, st.pos, inst.ascii);
			if ((inst.op == GUJI_RE_OP_WORD_B && !boundary) || (inst.op == GUJI_RE_OP_NWORD_B && boundary)) {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.pc++; break;
		}
		case GUJI_RE_OP_CUT_MARK:
			guji_regex_cut_push(&st, stack_len);
			st.pc++; break;
		case GUJI_RE_OP_CUT:
			if (st.cuts_len > 0) {
				int32_t w = st.cuts[--st.cuts_len];
				while (stack_len > w) guji_regex_state_free(&stack[--stack_len]);
			}
			st.pc++; break;
		case GUJI_RE_OP_LOOK_START: {
			if (inst.cls < 0 || inst.cls >= prog->look_count || inst.cls >= prog->subprog_count) {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			guji_regex_look_t li = prog->looks[inst.cls];
			const guji_regex_program_t *sub = prog->subprogs[inst.cls];
			int32_t saved_pos = st.pos;
			int32_t *saved_caps = guji_regex_clone_i32(st.caps, cap_slots);
			guji_regex_match_t m;
			int found = 0;
			if (li.kind == GUJI_RE_LOOK_AHEAD_POS || li.kind == GUJI_RE_LOOK_AHEAD_NEG) {
				m = guji_regex_match_at_caps(sub, s, len, st.pos, -1, st.caps, cap_slots);
				found = m.matched;
			} else {
				for (int32_t w = li.minw; w <= li.maxw; w++) {
					int32_t start_pos = guji_regex_walk_back_scalars(s, saved_pos, w);
					m = guji_regex_match_at_caps(sub, s, len, start_pos, saved_pos, st.caps, cap_slots);
					if (m.matched) { found = 1; break; }
				}
			}
			int positive = li.kind == GUJI_RE_LOOK_AHEAD_POS || li.kind == GUJI_RE_LOOK_BEHIND_POS;
			if ((positive && found) || (!positive && !found)) {
				st.pos = saved_pos;
				if (positive) {
					for (int32_t g = 1; g < m.span_count && g * 2 + 1 < cap_slots; g++) {
						st.caps[g * 2] = m.spans[g][0];
						st.caps[g * 2 + 1] = m.spans[g][1];
					}
				} else {
					memcpy(st.caps, saved_caps, sizeof(int32_t) * (size_t)cap_slots);
				}
				st.pc = li.after_pc;
				free(saved_caps);
			} else {
				st.pos = saved_pos;
				memcpy(st.caps, saved_caps, sizeof(int32_t) * (size_t)cap_slots);
				free(saved_caps);
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
			}
			break;
		}
		case GUJI_RE_OP_LOOK_END:
			st.pc++; break;
		case GUJI_RE_OP_MATCH: {
			if (anchor_end >= 0 && st.pos != anchor_end) {
				if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
				break;
			}
			st.caps[1] = st.pos;
			guji_regex_match_t out;
			memset(&out, 0, sizeof(out));
			out.matched = 1;
			out.span_count = prog->num_cap + 1;
			for (int32_t i = 0; i < out.span_count; i++) {
				out.spans[i][0] = st.caps[i * 2];
				out.spans[i][1] = st.caps[i * 2 + 1];
			}
			guji_regex_state_free(&st);
			for (int32_t i = 0; i < stack_len; i++) guji_regex_state_free(&stack[i]);
			free(stack);
			return out;
		}
		default:
			if (!guji_regex_backtrack(&stack, &stack_len, &st)) { free(stack); return no; }
			break;
		}
	}
}

static guji_regex_match_t guji_regex_find(const guji_regex_program_t *prog, const char *s, int32_t start) {
	int32_t len = (int32_t)GUJI_HDR(s)->count;
	start = guji_regex_clamp_start(s, len, start);
	for (int32_t pos = start; pos <= len; pos = guji_regex_next_start(s, len, pos)) {
		guji_regex_match_t m = guji_regex_match_at_caps(prog, s, len, pos, -1, NULL, 0);
		if (m.matched) {
			return m;
		}
		if (pos == len) {
			break;
		}
	}
	guji_regex_match_t no;
	memset(&no, 0, sizeof(no));
	return no;
}

static guji_regex_match_t guji_regex_find_anchored(const guji_regex_program_t *prog, const char *s, int32_t start) {
	int32_t len = (int32_t)GUJI_HDR(s)->count;
	start = guji_regex_clamp_start(s, len, start);
	return guji_regex_match_at_caps(prog, s, len, start, -1, NULL, 0);
}


/* Guji regex parser + compiler. This layer turns a pattern string into the
   Program IR the VM executes;
   it must be concatenated AFTER guji_regex.c (struct + guji_regex_read_rune)
   and guji_unicode_tables.c.

   X6c-1 covers the table-free RE2 core: literals + rune escapes, '.', the
   ^ $ \A \z \b \B anchors, character classes ([...] ranges, negation, POSIX
   [[:name:]]), concatenation, alternation, greedy/lazy/counted quantifiers,
   capturing / non-capturing (?:) / named (?<n>) / (?P<n>) groups, and atomic
   groups (?>) with possessive desugaring. X6c-2a adds Unicode-aware \d \w \s
   with (?a) ASCII mode. X6c-2b adds \p{...} / \P{...} Unicode properties
   (loose-name resolution against guji_unicode_properties, Script=/sc= against
   the scripts-only index) and (?i) case-fold expansion of literals and classes
   via guji_simple_fold, with the combined (?ai...) flag machinery. X6c-3a adds
   backreferences (\1, \k<name>). X6c-3b adds lookaround ((?=)(?!)(?<=)(?<!),
   with bounded-width lookbehind checks and OpLookStart/OpLookEnd sub-program
   emission). X6c-3c adds \X graphemes and \p{RGI_Emoji}. Raw <{ }> splice
   markers are rejected by the string-pattern entry point because evaluating
   guji expressions is host/codegen-owned; X6d-2b-ii-b adds
   guji_regex_compile_spliced(parts), the host-provided parts port of Go's
   ParseSpliced, for spliced regex literals. Where Go's compiler has an observable
   quirk (POSIX [[:^name:]] negation is ignored by classForClass), this port
   mirrors it for parity. */

/* ---------- AST ---------- */

enum {
	GUJI_REC_EMPTY = 0,
	GUJI_REC_LITERAL,
	GUJI_REC_ANY,
	GUJI_REC_ANCHOR,
	GUJI_REC_CLASS,
	GUJI_REC_CONCAT,
	GUJI_REC_ALTERNATE,
	GUJI_REC_QUANTIFIER,
	GUJI_REC_BACKREF,
	GUJI_REC_GROUP,
	GUJI_REC_ATOMIC,
	GUJI_REC_LOOKAROUND,
	GUJI_REC_GRAPHEME,
	GUJI_REC_RGI_EMOJI,
	GUJI_REC_SPLICE,
};

/* Stable internal ordering for regex shorthand classes. */
enum {
	GUJI_REC_SH_DIGIT = 0,
	GUJI_REC_SH_NOT_DIGIT,
	GUJI_REC_SH_WORD,
	GUJI_REC_SH_NOT_WORD,
	GUJI_REC_SH_SPACE,
	GUJI_REC_SH_NOT_SPACE,
};

/* Stable internal ordering for regex anchors. */
enum {
	GUJI_REC_ANCHOR_BEGIN_LINE = 0,
	GUJI_REC_ANCHOR_END_LINE,
	GUJI_REC_ANCHOR_BEGIN_TEXT,
	GUJI_REC_ANCHOR_END_TEXT,
	GUJI_REC_ANCHOR_END_TEXT_ABS,
	GUJI_REC_ANCHOR_WORD_BOUNDARY,
	GUJI_REC_ANCHOR_NON_WORD_BOUNDARY,
};

/* Regex parser flags are resolved into the tree at parse time. */
typedef struct {
	int fold;
	int multiline;
	int dot_all;
	int ascii;
	int verbose;
} guji_rec_flags_t;

typedef struct guji_rec_node guji_rec_node_t;
struct guji_rec_node {
	int kind;
	/* literal */
	int32_t rune;
	int fold;
	/* any */
	int dot_all;
	/* anchor */
	int anchor_kind;
	int multiline;
	int ascii;
	/* class */
	int cls_negated;
	int cls_fold;
	int cls_raw;
	guji_regex_range_t *cls_ranges;
	int32_t cls_range_count;
	/* concat / alternate */
	guji_rec_node_t **subs;
	int32_t sub_count;
	/* quantifier */
	guji_rec_node_t *sub;
	int qmin;
	int qmax;
	int greedy;
	/* backref */
	int backref_index;
	/* group */
	int cap;
	int index;
	/* lookaround (kind mirrors guji_regex.c GUJI_RE_LOOK_*; minw/maxw set for
	   lookbehind only, 0 for lookahead). The body is in `sub`. */
	int look_kind;
	int look_minw;
	int look_maxw;
	/* splice: the independently parsed atom is in `sub`; index stores its local
	   capture count until guji_rec_finish rebases those private slots */
};

/* ---------- parser ---------- */

#define GUJI_REC_EOF (-1)
#define GUJI_REC_MSG_CAP 160

typedef struct {
	int32_t *src;
	int32_t len;
	int32_t pos;
	int32_t num_cap;
	int32_t *public_cap_indexes;
	int32_t public_cap_count;
	int32_t public_cap_cap;
	/* Reserved 0H... names are accepted only for compiler-materialized Regex
	   values. Plain user source always leaves this disabled. */
	int allow_hidden_names;
	/* capture names, ASCII only (isNameChar); kept for duplicate detection */
	int32_t **names;
	int32_t *name_lens;
	int32_t *name_indexes;
	int32_t name_count;
	int32_t name_cap;
	/* error state */
	int err;
	char msg[GUJI_REC_MSG_CAP];
	int32_t err_pos;
	/* inline flag groups mutate enclosing flags; parseConcat polls these fields */
	guji_rec_flags_t flags;
	int inline_flag_applied;
	/* host-provided splice parts (guji_regex_compile_spliced): marker rune
	   0xE000+i in src resolves to splices[i], an independently parsed atom with
	   private capture slots. NULL for plain compiles,
	   so private-use runes stay ordinary literals like Go's CompileString. */
	guji_rec_node_t **splices;
	int32_t splice_count;
	/* arena: every AST node + node-owned array tracked for teardown */
	void **allocs;
	int32_t alloc_count;
	int32_t alloc_cap;
} guji_rec_parser_t;

static void *guji_rec_track(guji_rec_parser_t *p, void *ptr) {
	if (!ptr) {
		return NULL;
	}
	if (p->alloc_count == p->alloc_cap) {
		int32_t nc = p->alloc_cap ? p->alloc_cap * 2 : 16;
		void **na = (void **)realloc(p->allocs, sizeof(void *) * (size_t)nc);
		if (!na) {
			abort();
		}
		p->allocs = na;
		p->alloc_cap = nc;
	}
	p->allocs[p->alloc_count++] = ptr;
	return ptr;
}

static void guji_rec_set_error(guji_rec_parser_t *p, int32_t pos, const char *msg) {
	if (p->err) {
		return; /* keep the first error, like Go's early returns */
	}
	p->err = 1;
	p->err_pos = pos;
	size_t i = 0;
	for (; msg[i] != '\0' && i < GUJI_REC_MSG_CAP - 1; i++) {
		p->msg[i] = msg[i];
	}
	p->msg[i] = '\0';
}

static int32_t guji_rec_peek(guji_rec_parser_t *p) {
	return p->pos >= p->len ? GUJI_REC_EOF : p->src[p->pos];
}

static int32_t guji_rec_at(guji_rec_parser_t *p, int32_t off) {
	int32_t i = p->pos + off;
	if (i < 0 || i >= p->len) {
		return GUJI_REC_EOF;
	}
	return p->src[i];
}

/* Skip ignored whitespace and #...\n comments when the verbose flag (?x) is in
   effect. Used outside bracket expressions and escape sequences only. */
static void guji_rec_skip_verbose(guji_rec_parser_t *p, guji_rec_flags_t fl) {
	if (!fl.verbose) {
		return;
	}
	while (p->pos < p->len) {
		int32_t c = p->src[p->pos];
		switch (c) {
		case ' ':
		case '\t':
		case '\n':
		case '\r':
		case '\f':
		case '\v':
			p->pos++;
			break;
		case '#':
			while (p->pos < p->len && p->src[p->pos] != '\n') {
				p->pos++;
			}
			break;
		default:
			return;
		}
	}
}

static guji_rec_node_t *guji_rec_new(guji_rec_parser_t *p, int kind) {
	guji_rec_node_t *n = (guji_rec_node_t *)calloc(1, sizeof(*n));
	if (!n) {
		abort();
	}
	n->kind = kind;
	guji_rec_track(p, n);
	return n;
}

static int guji_rec_is_name_char(int32_t c) {
	return c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9');
}

/* Names beginning 0H are reserved for private captures in a materialized
   Regex-valued splice. User capture names cannot begin with a digit. */
static int guji_rec_is_hidden_name(
		const guji_rec_parser_t *p, int32_t start, int32_t end) {
	return end - start >= 3 && p->src[start] == '0' && p->src[start + 1] == 'H';
}

static void guji_rec_add_public_cap(guji_rec_parser_t *p, int32_t index) {
	if (p->public_cap_count == p->public_cap_cap) {
		int32_t nc = p->public_cap_cap ? p->public_cap_cap * 2 : 8;
		int32_t *ni = (int32_t *)realloc(
			p->public_cap_indexes, sizeof(int32_t) * (size_t)nc);
		if (!ni) {
			abort();
		}
		p->public_cap_indexes = ni;
		p->public_cap_cap = nc;
	}
	p->public_cap_indexes[p->public_cap_count++] = index;
}

static int guji_rec_is_hex(int32_t c) {
	return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
}

static int32_t guji_rec_hex_val(int32_t c) {
	if (c >= '0' && c <= '9') {
		return c - '0';
	}
	if (c >= 'a' && c <= 'f') {
		return c - 'a' + 10;
	}
	return c - 'A' + 10;
}

/* forward declarations */
static guji_rec_node_t *guji_rec_parse_alternate(guji_rec_parser_t *p, guji_rec_flags_t fl);
static guji_rec_node_t *guji_rec_parse_concat(guji_rec_parser_t *p, guji_rec_flags_t *fl);
static guji_rec_node_t *guji_rec_parse_named_backref(guji_rec_parser_t *p, guji_rec_flags_t fl, int32_t bs);

static int guji_rec_quantifiable(const guji_rec_node_t *n) {
	return n->kind != GUJI_REC_ANCHOR;
}

/* scanCountedRepeat: returns consumed rune count (>=0) on success, -1 on
   failure, writing lo/hi (hi == -1 for an open upper bound). */
static int32_t guji_rec_scan_counted(guji_rec_parser_t *p, int32_t *lo_out, int32_t *hi_out) {
	if (guji_rec_peek(p) != '{') {
		return -1;
	}
	int32_t i = p->pos + 1;
	int32_t start = i;
	int32_t lo = 0;
	while (i < p->len && p->src[i] >= '0' && p->src[i] <= '9') {
		lo = lo * 10 + (p->src[i] - '0');
		i++;
	}
	if (i == start) {
		return -1;
	}
	int32_t hi = lo;
	if (i < p->len && p->src[i] == ',') {
		i++;
		int32_t hstart = i;
		hi = 0;
		while (i < p->len && p->src[i] >= '0' && p->src[i] <= '9') {
			hi = hi * 10 + (p->src[i] - '0');
			i++;
		}
		if (i == hstart) {
			hi = -1; /* {n,} unbounded */
		}
	}
	if (i >= p->len || p->src[i] != '}') {
		return -1;
	}
	*lo_out = lo;
	*hi_out = hi;
	return (i + 1) - p->pos;
}

/* parseRuneEscape: backslash already consumed; bs is its position. */
static int32_t guji_rec_parse_rune_escape(guji_rec_parser_t *p, int32_t bs) {
	int32_t c = guji_rec_peek(p);
	switch (c) {
	case 'n':
		p->pos++;
		return '\n';
	case 'r':
		p->pos++;
		return '\r';
	case 't':
		p->pos++;
		return '\t';
	case 'f':
		p->pos++;
		return '\f';
	case 'v':
		p->pos++;
		return '\v';
	case 'a':
		p->pos++;
		return '\a';
	case '0':
		p->pos++;
		return 0;
	case 'x': {
		int32_t xpos = p->pos;
		p->pos++; /* consume 'x' */
		if (guji_rec_peek(p) == '{') {
			p->pos++; /* consume '{' */
			int32_t start = p->pos;
			int64_t v = 0;
			while (guji_rec_peek(p) != '}') {
				int32_t h = guji_rec_peek(p);
				if (!guji_rec_is_hex(h)) {
					guji_rec_set_error(p, p->pos, "invalid hexadecimal escape");
					return 0;
				}
				v = v * 16 + guji_rec_hex_val(h);
				if (v > 0x10FFFF) {
					v = 0x110000; /* clamp: still > MaxRune so we report below */
				}
				p->pos++;
			}
			if (p->pos == start) {
				guji_rec_set_error(p, start, "invalid hexadecimal escape");
				return 0;
			}
			p->pos++; /* consume '}' */
			if (v > 0x10FFFF) {
				guji_rec_set_error(p, start, "invalid hexadecimal escape");
				return 0;
			}
			return (int32_t)v;
		}
		/* exactly two hex digits */
		if (!guji_rec_is_hex(guji_rec_at(p, 0)) || !guji_rec_is_hex(guji_rec_at(p, 1))) {
			guji_rec_set_error(p, xpos, "invalid hexadecimal escape");
			return 0;
		}
		int32_t v = guji_rec_hex_val(p->src[p->pos]) * 16 + guji_rec_hex_val(p->src[p->pos + 1]);
		p->pos += 2;
		return v;
	}
	default:
		if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) {
			char buf[64];
			snprintf(buf, sizeof(buf), "invalid escape sequence \\%c", (char)c);
			guji_rec_set_error(p, bs, buf);
			return 0;
		}
		p->pos++;
		return c;
	}
}

/* posixRanges appends the scalar ranges of a POSIX class to buf (the caller
   owns growth). Mirrors compile.go posixRanges. Returns the new count, or -1
   for an unknown name. */
static int guji_rec_name_eq(const int32_t *src, int32_t start, int32_t end, const char *lit) {
	int32_t n = end - start;
	int32_t i;
	for (i = 0; i < n; i++) {
		if (lit[i] == '\0' || src[start + i] != (int32_t)lit[i]) {
			return 0;
		}
	}
	return lit[i] == '\0';
}

/* ---------- class range buffer ---------- */

typedef struct {
	guji_regex_range_t *data;
	int32_t count;
	int32_t cap;
} guji_rec_ranges_t;

static void guji_rec_ranges_push(guji_rec_ranges_t *r, int32_t lo, int32_t hi) {
	if (r->count == r->cap) {
		int32_t nc = r->cap ? r->cap * 2 : 8;
		guji_regex_range_t *nd = (guji_regex_range_t *)realloc(r->data, sizeof(*nd) * (size_t)nc);
		if (!nd) {
			abort();
		}
		r->data = nd;
		r->cap = nc;
	}
	r->data[r->count].lo = lo;
	r->data[r->count].hi = hi;
	r->count++;
}

static void guji_rec_ranges_append_table(guji_rec_ranges_t *out, const guji_unicode_table_t *tab) {
	if (!tab) {
		return;
	}
	for (int32_t i = 0; i < tab->count; i++) {
		guji_rec_ranges_push(out, tab->ranges[i].lo, tab->ranges[i].hi);
	}
}

static void guji_rec_ranges_append_word(guji_rec_ranges_t *out) {
	for (int32_t i = 0; i < guji_word_range_count; i++) {
		guji_rec_ranges_push(out, guji_word_ranges[i].lo, guji_word_ranges[i].hi);
	}
}

static void guji_rec_ranges_append_complement(guji_rec_ranges_t *out, const guji_rec_ranges_t *base) {
	int32_t next = 0;
	for (int32_t i = 0; i < base->count; i++) {
		int32_t lo = base->data[i].lo;
		int32_t hi = base->data[i].hi;
		if (lo > next) {
			guji_rec_ranges_push(out, next, lo - 1);
		}
		if (hi + 1 > next) {
			next = hi + 1;
		}
	}
	if (next <= GUJI_MAX_RUNE) {
		guji_rec_ranges_push(out, next, GUJI_MAX_RUNE);
	}
}

static int guji_rec_shorthand_kind(int32_t c) {
	switch (c) {
	case 'd':
		return GUJI_REC_SH_DIGIT;
	case 'D':
		return GUJI_REC_SH_NOT_DIGIT;
	case 'w':
		return GUJI_REC_SH_WORD;
	case 'W':
		return GUJI_REC_SH_NOT_WORD;
	case 's':
		return GUJI_REC_SH_SPACE;
	case 'S':
		return GUJI_REC_SH_NOT_SPACE;
	default:
		return -1;
	}
}

static int guji_rec_shorthand_negated(int kind) {
	return kind == GUJI_REC_SH_NOT_DIGIT || kind == GUJI_REC_SH_NOT_WORD || kind == GUJI_REC_SH_NOT_SPACE;
}

static void guji_rec_append_shorthand_base(guji_rec_ranges_t *out, int kind, int ascii) {
	if (ascii) {
		switch (kind) {
		case GUJI_REC_SH_DIGIT:
		case GUJI_REC_SH_NOT_DIGIT:
			guji_rec_ranges_push(out, '0', '9');
			return;
		case GUJI_REC_SH_WORD:
		case GUJI_REC_SH_NOT_WORD:
			guji_rec_ranges_push(out, '0', '9');
			guji_rec_ranges_push(out, 'A', 'Z');
			guji_rec_ranges_push(out, '_', '_');
			guji_rec_ranges_push(out, 'a', 'z');
			return;
		case GUJI_REC_SH_SPACE:
		case GUJI_REC_SH_NOT_SPACE:
			guji_rec_ranges_push(out, '\t', '\t');
			guji_rec_ranges_push(out, '\n', '\n');
			guji_rec_ranges_push(out, '\v', '\v');
			guji_rec_ranges_push(out, '\f', '\f');
			guji_rec_ranges_push(out, '\r', '\r');
			guji_rec_ranges_push(out, ' ', ' ');
			return;
		}
	}
	switch (kind) {
	case GUJI_REC_SH_DIGIT:
	case GUJI_REC_SH_NOT_DIGIT:
		guji_rec_ranges_append_table(out, guji_unicode_property("Nd"));
		return;
	case GUJI_REC_SH_WORD:
	case GUJI_REC_SH_NOT_WORD:
		guji_rec_ranges_append_word(out);
		return;
	case GUJI_REC_SH_SPACE:
	case GUJI_REC_SH_NOT_SPACE:
		guji_rec_ranges_append_table(out, guji_unicode_property("White_Space"));
		return;
	}
}

static void guji_rec_append_class_shorthand(guji_rec_ranges_t *out, int kind, int ascii) {
	guji_rec_ranges_t base = {0};
	guji_rec_append_shorthand_base(&base, kind, ascii);
	if (guji_rec_shorthand_negated(kind)) {
		guji_rec_ranges_append_complement(out, &base);
	} else {
		for (int32_t i = 0; i < base.count; i++) {
			guji_rec_ranges_push(out, base.data[i].lo, base.data[i].hi);
		}
	}
	free(base.data);
}

/* ---------- Unicode property resolution (\p{...}) ---------- */

/* guji_rec_loose_name_eq compares the rune span [start,end) against a
   canonical ASCII property name with Unicode loose matching: spaces,
   underscores, and hyphens are insignificant and letters compare
   case-insensitively. The two non-ASCII scalars whose Unicode lowercase forms
   land in ASCII are special-cased so, for example, \p{LATİN} resolves. */
static int guji_rec_loose_name_eq(const int32_t *src, int32_t start, int32_t end, const char *name) {
	int32_t i = start;
	const char *q = name;
	for (;;) {
		while (i < end && (src[i] == ' ' || src[i] == '_' || src[i] == '-')) {
			i++;
		}
		while (*q == ' ' || *q == '_' || *q == '-') {
			q++;
		}
		if (i >= end) {
			return *q == '\0';
		}
		if (*q == '\0') {
			return 0;
		}
		int32_t c = src[i];
		if (c >= 'A' && c <= 'Z') {
			c += 'a' - 'A';
		} else if (c == 0x130) {
			c = 'i'; /* LATIN CAPITAL LETTER I WITH DOT ABOVE */
		} else if (c == 0x212A) {
			c = 'k'; /* KELVIN SIGN */
		}
		int32_t d = (unsigned char)*q;
		if (d >= 'A' && d <= 'Z') {
			d += 'a' - 'A';
		}
		if (c != d) {
			return 0;
		}
		i++;
		q++;
	}
}

/* guji_rec_msg_append_rune UTF-8-encodes r into buf (capped, NUL space kept),
   so error messages can quote the raw property name like Go's %q does for
   printable runes. */
static void guji_rec_msg_append_rune(char *buf, size_t cap, size_t *off, int32_t r) {
	unsigned char tmp[4];
	int n;
	if (r < 0x80) {
		tmp[0] = (unsigned char)r;
		n = 1;
	} else if (r < 0x800) {
		tmp[0] = (unsigned char)(0xC0 | (r >> 6));
		tmp[1] = (unsigned char)(0x80 | (r & 0x3F));
		n = 2;
	} else if (r < 0x10000) {
		tmp[0] = (unsigned char)(0xE0 | (r >> 12));
		tmp[1] = (unsigned char)(0x80 | ((r >> 6) & 0x3F));
		tmp[2] = (unsigned char)(0x80 | (r & 0x3F));
		n = 3;
	} else {
		tmp[0] = (unsigned char)(0xF0 | (r >> 18));
		tmp[1] = (unsigned char)(0x80 | ((r >> 12) & 0x3F));
		tmp[2] = (unsigned char)(0x80 | ((r >> 6) & 0x3F));
		tmp[3] = (unsigned char)(0x80 | (r & 0x3F));
		n = 4;
	}
	for (int i = 0; i < n && *off < cap - 1; i++) {
		buf[(*off)++] = (char)tmp[i];
	}
}

static void guji_rec_unknown_property(guji_rec_parser_t *p, int32_t bs, int32_t start, int32_t end) {
	char buf[GUJI_REC_MSG_CAP];
	size_t off = 0;
	const char *prefix = "unknown Unicode property \"";
	for (; *prefix != '\0' && off < sizeof(buf) - 1; prefix++) {
		buf[off++] = *prefix;
	}
	for (int32_t i = start; i < end; i++) {
		guji_rec_msg_append_rune(buf, sizeof(buf), &off, p->src[i]);
	}
	if (off < sizeof(buf) - 1) {
		buf[off++] = '"';
	}
	buf[off] = '\0';
	guji_rec_set_error(p, bs, buf);
}

/* guji_rec_resolve_property resolves the rune span [start,end) of a \p{...}
   body. A Script=/sc= prefix resolves against scripts only; a bare name
   resolves against the full property table (categories, scripts, and binary
   properties). The normalized keys are collision-free, so a flat first-match
   scan is deterministic. Returns the table; NULL with *is_rgi set for the
   RGI_Emoji string property; NULL with an error recorded otherwise. */
static const guji_unicode_table_t *guji_rec_resolve_property(guji_rec_parser_t *p, int32_t bs, int32_t start, int32_t end, int *is_rgi) {
	*is_rgi = 0;
	int32_t eq = -1;
	for (int32_t i = start; i < end; i++) {
		if (p->src[i] == '=') {
			eq = i;
			break;
		}
	}
	if (eq >= 0) {
		if (guji_rec_loose_name_eq(p->src, start, eq, "script") || guji_rec_loose_name_eq(p->src, start, eq, "sc")) {
			for (int32_t i = 0; i < guji_unicode_script_name_count; i++) {
				if (guji_rec_loose_name_eq(p->src, eq + 1, end, guji_unicode_script_names[i])) {
					return guji_unicode_property(guji_unicode_script_names[i]);
				}
			}
		}
		guji_rec_unknown_property(p, bs, start, end);
		return NULL;
	}
	if (guji_rec_loose_name_eq(p->src, start, end, "RGI_Emoji")) {
		*is_rgi = 1;
		return NULL;
	}
	for (int32_t i = 0; i < guji_unicode_property_count; i++) {
		if (guji_rec_loose_name_eq(p->src, start, end, guji_unicode_properties[i].name)) {
			return &guji_unicode_properties[i];
		}
	}
	guji_rec_unknown_property(p, bs, start, end);
	return NULL;
}

/* guji_rec_parse_unicode_property parses \p{Name} / \P{Name}: the leading p/P
   is at the current position and the backslash position is bs. It includes the
   RGI_Emoji negation error. On success it returns the table, or NULL with
   *is_rgi set (positive RGI_Emoji; in a bracket class it contributes no
   scalars). NULL with *is_rgi == 0 means an error was recorded. */
static const guji_unicode_table_t *guji_rec_parse_unicode_property(guji_rec_parser_t *p, int32_t bs, int negated, int *is_rgi) {
	*is_rgi = 0;
	p->pos++; /* consume p/P */
	if (guji_rec_peek(p) != '{') {
		guji_rec_set_error(p, bs, "invalid Unicode property syntax");
		return NULL;
	}
	p->pos++; /* consume '{' */
	int32_t start = p->pos;
	for (;;) {
		int32_t c = guji_rec_peek(p);
		if (c == '}') {
			break;
		}
		if (c == GUJI_REC_EOF || c == '\n') {
			guji_rec_set_error(p, bs, "missing closing } in Unicode property");
			return NULL;
		}
		p->pos++;
	}
	int32_t end = p->pos;
	p->pos++; /* consume '}' */
	if (end == start) {
		guji_rec_set_error(p, bs, "empty Unicode property");
		return NULL;
	}
	const guji_unicode_table_t *tab = guji_rec_resolve_property(p, bs, start, end, is_rgi);
	if (*is_rgi && negated) {
		*is_rgi = 0;
		guji_rec_set_error(p, bs, "cannot negate string property \\p{RGI_Emoji}");
		return NULL;
	}
	return tab;
}

/* parsePosixClass: opening '[' is at the current pos. Appends ranges. */
static void guji_rec_parse_posix(guji_rec_parser_t *p, int32_t open, guji_rec_ranges_t *out) {
	p->pos += 2; /* consume "[:" */
	if (guji_rec_peek(p) == '^') {
		p->pos++; /* Go's classForClass ignores POSIX negation; we mirror it */
	}
	int32_t start = p->pos;
	while (guji_rec_peek(p) != ':') {
		int32_t c = guji_rec_peek(p);
		if (c == GUJI_REC_EOF || c == ']') {
			guji_rec_set_error(p, open, "invalid POSIX character class");
			return;
		}
		p->pos++;
	}
	int32_t end = p->pos;
	p->pos++; /* consume ':' */
	if (guji_rec_peek(p) != ']') {
		guji_rec_set_error(p, open, "invalid POSIX character class");
		return;
	}
	p->pos++; /* consume ']' */

	if (guji_rec_name_eq(p->src, start, end, "ascii")) {
		guji_rec_ranges_push(out, 0, 127);
	} else if (guji_rec_name_eq(p->src, start, end, "digit")) {
		guji_rec_ranges_push(out, '0', '9');
	} else if (guji_rec_name_eq(p->src, start, end, "upper")) {
		guji_rec_ranges_push(out, 'A', 'Z');
	} else if (guji_rec_name_eq(p->src, start, end, "lower")) {
		guji_rec_ranges_push(out, 'a', 'z');
	} else if (guji_rec_name_eq(p->src, start, end, "alpha")) {
		guji_rec_ranges_push(out, 'A', 'Z');
		guji_rec_ranges_push(out, 'a', 'z');
	} else if (guji_rec_name_eq(p->src, start, end, "alnum")) {
		guji_rec_ranges_push(out, '0', '9');
		guji_rec_ranges_push(out, 'A', 'Z');
		guji_rec_ranges_push(out, 'a', 'z');
	} else if (guji_rec_name_eq(p->src, start, end, "word")) {
		guji_rec_ranges_push(out, '0', '9');
		guji_rec_ranges_push(out, 'A', 'Z');
		guji_rec_ranges_push(out, 'a', 'z');
		guji_rec_ranges_push(out, '_', '_');
	} else if (guji_rec_name_eq(p->src, start, end, "space")) {
		guji_rec_ranges_push(out, '\t', '\t');
		guji_rec_ranges_push(out, '\n', '\n');
		guji_rec_ranges_push(out, '\f', '\f');
		guji_rec_ranges_push(out, '\r', '\r');
		guji_rec_ranges_push(out, ' ', ' ');
	} else if (guji_rec_name_eq(p->src, start, end, "blank")) {
		guji_rec_ranges_push(out, '\t', '\t');
		guji_rec_ranges_push(out, ' ', ' ');
	} else if (guji_rec_name_eq(p->src, start, end, "punct")) {
		guji_rec_ranges_push(out, '!', '/');
		guji_rec_ranges_push(out, ':', '@');
		guji_rec_ranges_push(out, '[', '`');
		guji_rec_ranges_push(out, '{', '~');
	} else if (guji_rec_name_eq(p->src, start, end, "xdigit")) {
		guji_rec_ranges_push(out, '0', '9');
		guji_rec_ranges_push(out, 'A', 'F');
		guji_rec_ranges_push(out, 'a', 'f');
	} else if (guji_rec_name_eq(p->src, start, end, "cntrl")) {
		guji_rec_ranges_push(out, 0, 31);
		guji_rec_ranges_push(out, 127, 127);
	} else if (guji_rec_name_eq(p->src, start, end, "graph")) {
		guji_rec_ranges_push(out, 33, 126);
	} else if (guji_rec_name_eq(p->src, start, end, "print")) {
		guji_rec_ranges_push(out, 32, 126);
	} else {
		guji_rec_set_error(p, start, "unknown POSIX class");
	}
}

/* classMember reads one bracket member: a single scalar (returns single=1).
   Shorthand escapes inside a class are handled by parseClass before this helper
   because they contribute ranges rather than a single scalar. */
static int32_t guji_rec_class_member(guji_rec_parser_t *p, guji_rec_flags_t fl, int *single) {
	*single = 1;
	if (guji_rec_peek(p) == '\\') {
		int32_t bs = p->pos;
		p->pos++; /* consume '\' */
		int32_t c = guji_rec_peek(p);
		switch (c) {
		case 'd':
		case 'D':
		case 'w':
		case 'W':
		case 's':
		case 'S':
			guji_rec_set_error(p, bs, "invalid character class range");
			return 0;
		case 'p':
		case 'P': {
			/* Reachable only as a range endpoint ([a-\p{L}]): parse the
			   property (surfacing its own syntax errors first, like Go's
			   classEscape) and report non-single so the caller emits
			   "invalid character class range". */
			int is_rgi = 0;
			(void)guji_rec_parse_unicode_property(p, bs, c == 'P', &is_rgi);
			if (p->err) {
				return 0;
			}
			*single = 0;
			return 0;
		}
		case 'b':
			p->pos++; /* \b inside a class is a backspace */
			return '\b';
		default:
			return guji_rec_parse_rune_escape(p, bs);
		}
	}
	int32_t c = guji_rec_peek(p);
	p->pos++;
	(void)fl;
	return c;
}

/* parseClass parses a [...] bracket expression. */
static guji_rec_node_t *guji_rec_parse_class(guji_rec_parser_t *p, guji_rec_flags_t fl) {
	int32_t open = p->pos;
	p->pos++; /* consume '[' */
	guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_CLASS);
	if (guji_rec_peek(p) == '^') {
		n->cls_negated = 1;
		p->pos++;
	}
	n->cls_fold = fl.fold;
	guji_rec_ranges_t ranges = {0};
	int first = 1; /* a ']' immediately after '[' (or '[^') is a literal */
	for (;;) {
		int32_t c = guji_rec_peek(p);
		if (c == GUJI_REC_EOF) {
			free(ranges.data);
			guji_rec_set_error(p, open, "missing closing ]");
			return NULL;
		}
		if (c == ']' && !first) {
			p->pos++;
			n->cls_ranges = (guji_regex_range_t *)guji_rec_track(p, ranges.data);
			n->cls_range_count = ranges.count;
			return n;
		}
		first = 0;

		if (c == '[' && guji_rec_at(p, 1) == ':') {
			guji_rec_parse_posix(p, open, &ranges);
			if (p->err) {
				free(ranges.data);
				return NULL;
			}
			continue;
		}
		if (c == '\\') {
			int kind = guji_rec_shorthand_kind(guji_rec_at(p, 1));
			if (kind >= 0) {
				p->pos += 2;
				guji_rec_append_class_shorthand(&ranges, kind, fl.ascii);
				continue;
			}
			int32_t pc = guji_rec_at(p, 1);
			if (pc == 'p' || pc == 'P') {
				int32_t bs = p->pos;
				int negated = pc == 'P';
				p->pos++; /* consume '\' */
				int is_rgi = 0;
				const guji_unicode_table_t *tab = guji_rec_parse_unicode_property(p, bs, negated, &is_rgi);
				if (p->err) {
					free(ranges.data);
					return NULL;
				}
				if (is_rgi) {
					continue; /* string property: no scalars, like Go's classForClass */
				}
				if (negated) {
					/* [\P{Name}] contributes the complement of the base set. */
					guji_rec_ranges_t base = {0};
					guji_rec_ranges_append_table(&base, tab);
					guji_rec_ranges_append_complement(&ranges, &base);
					free(base.data);
				} else {
					guji_rec_ranges_append_table(&ranges, tab);
				}
				continue;
			}
		}

		int single = 0;
		int32_t lo = guji_rec_class_member(p, fl, &single);
		if (p->err) {
			free(ranges.data);
			return NULL;
		}
		if (!single) {
			/* class_member only returns single members in this slice */
			free(ranges.data);
			guji_rec_set_error(p, open, "invalid character class");
			return NULL;
		}
		if (guji_rec_peek(p) == '-' && guji_rec_at(p, 1) != ']' && guji_rec_at(p, 1) != GUJI_REC_EOF) {
			p->pos++; /* consume '-' */
			int single2 = 0;
			int32_t hi = guji_rec_class_member(p, fl, &single2);
			if (p->err) {
				free(ranges.data);
				return NULL;
			}
			if (!single2 || hi < lo) {
				free(ranges.data);
				guji_rec_set_error(p, open, "invalid character class range");
				return NULL;
			}
			guji_rec_ranges_push(&ranges, lo, hi);
			continue;
		}
		guji_rec_ranges_push(&ranges, lo, lo);
	}
}

/* parseEscape parses a backslash escape outside a bracket expression. */
static guji_rec_node_t *guji_rec_parse_escape(guji_rec_parser_t *p, guji_rec_flags_t fl) {
	int32_t bs = p->pos;
	p->pos++; /* consume '\' */
	int32_t c = guji_rec_peek(p);
	if (c == GUJI_REC_EOF) {
		guji_rec_set_error(p, bs, "trailing backslash");
		return NULL;
	}
	switch (c) {
	case 'd':
	case 'D':
	case 'w':
	case 'W':
	case 's':
	case 'S': {
		p->pos++;
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_CLASS);
		guji_rec_ranges_t ranges = {0};
		int kind = guji_rec_shorthand_kind(c);
		guji_rec_append_shorthand_base(&ranges, kind, fl.ascii);
		n->cls_negated = guji_rec_shorthand_negated(kind);
		n->cls_raw = 1;
		n->cls_ranges = (guji_regex_range_t *)guji_rec_track(p, ranges.data);
		n->cls_range_count = ranges.count;
		return n;
	}
	case 'b': {
		p->pos++;
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_ANCHOR);
		n->anchor_kind = GUJI_REC_ANCHOR_WORD_BOUNDARY;
		n->ascii = fl.ascii;
		return n;
	}
	case 'B': {
		p->pos++;
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_ANCHOR);
		n->anchor_kind = GUJI_REC_ANCHOR_NON_WORD_BOUNDARY;
		n->ascii = fl.ascii;
		return n;
	}
	case 'A': {
		p->pos++;
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_ANCHOR);
		n->anchor_kind = GUJI_REC_ANCHOR_BEGIN_TEXT;
		return n;
	}
	case 'z': {
		p->pos++;
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_ANCHOR);
		n->anchor_kind = GUJI_REC_ANCHOR_END_TEXT;
		return n;
	}
	case 'Z': {
		p->pos++;
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_ANCHOR);
		n->anchor_kind = GUJI_REC_ANCHOR_END_TEXT_ABS;
		return n;
	}
	case 'X': {
		p->pos++;
		return guji_rec_new(p, GUJI_REC_GRAPHEME);
	}
	case 'k':
		return guji_rec_parse_named_backref(p, fl, bs);
	case 'p':
	case 'P': {
		int negated = c == 'P';
		int is_rgi = 0;
		const guji_unicode_table_t *tab = guji_rec_parse_unicode_property(p, bs, negated, &is_rgi);
		if (is_rgi) {
			return guji_rec_new(p, GUJI_REC_RGI_EMOJI);
		}
		if (!tab) {
			return NULL; /* error already recorded */
		}
		/* Like Go's classForUnicodeProperty: the table ranges ARE the class,
		   verbatim (already sorted+merged); negation is the class flag. */
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_CLASS);
		guji_rec_ranges_t ranges = {0};
		guji_rec_ranges_append_table(&ranges, tab);
		n->cls_negated = negated;
		n->cls_raw = 1;
		n->cls_ranges = (guji_regex_range_t *)guji_rec_track(p, ranges.data);
		n->cls_range_count = ranges.count;
		return n;
	}
	case '1':
	case '2':
	case '3':
	case '4':
	case '5':
	case '6':
	case '7':
		case '8':
		case '9': {
			p->pos++;
			int32_t public_idx = c - '0';
			if (public_idx > p->public_cap_count) {
				guji_rec_set_error(p, bs, "invalid backreference");
				return NULL;
			}
			guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_BACKREF);
			n->backref_index = p->public_cap_indexes[public_idx - 1];
			n->fold = fl.fold;
			return n;
		}
	default: {
		int32_t r = guji_rec_parse_rune_escape(p, bs);
		if (p->err) {
			return NULL;
		}
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_LITERAL);
		n->rune = r;
		n->fold = fl.fold;
		return n;
	}
	}
}

/* validateName checks and records a capture name, returning 0 on error. */
static int guji_rec_record_name(guji_rec_parser_t *p, int32_t open, int32_t start, int32_t end, int32_t index) {
	int32_t n = end - start;
	if (n == 0) {
		guji_rec_set_error(p, open, "empty capture name");
		return 0;
	}
	if (p->src[start] >= '0' && p->src[start] <= '9'
			&& !(p->allow_hidden_names
				&& guji_rec_is_hidden_name(p, start, end))) {
		guji_rec_set_error(p, start, "capture name must not start with a digit");
		return 0;
	}
	for (int32_t i = 0; i < p->name_count; i++) {
		if (p->name_lens[i] == n) {
			int32_t j = 0;
			for (; j < n; j++) {
				if (p->names[i][j] != p->src[start + j]) {
					break;
				}
			}
			if (j == n) {
				char buf[GUJI_REC_MSG_CAP];
				int off = snprintf(buf, sizeof(buf), "duplicate capture name \"");
				for (int32_t k = 0; k < n && off < (int)sizeof(buf) - 2; k++) {
					buf[off++] = (char)p->src[start + k];
				}
				buf[off++] = '"';
				buf[off] = '\0';
				guji_rec_set_error(p, open, buf);
				return 0;
			}
		}
	}
	if (p->name_count == p->name_cap) {
		int32_t nc = p->name_cap ? p->name_cap * 2 : 8;
		p->names = (int32_t **)realloc(p->names, sizeof(int32_t *) * (size_t)nc);
		p->name_lens = (int32_t *)realloc(p->name_lens, sizeof(int32_t) * (size_t)nc);
		p->name_indexes = (int32_t *)realloc(p->name_indexes, sizeof(int32_t) * (size_t)nc);
		if (!p->names || !p->name_lens || !p->name_indexes) {
			abort();
		}
		p->name_cap = nc;
	}
	int32_t *copy = (int32_t *)malloc(sizeof(int32_t) * (size_t)(n > 0 ? n : 1));
	if (!copy) {
		abort();
	}
	memcpy(copy, &p->src[start], sizeof(int32_t) * (size_t)n);
	p->names[p->name_count] = copy;
	p->name_lens[p->name_count] = n;
	p->name_indexes[p->name_count] = index;
	p->name_count++;
	return 1;
}

static int32_t guji_rec_find_name(guji_rec_parser_t *p, int32_t start, int32_t end) {
	int32_t n = end - start;
	for (int32_t i = 0; i < p->name_count; i++) {
		if (p->name_lens[i] != n) {
			continue;
		}
		int32_t j = 0;
		for (; j < n; j++) {
			if (p->names[i][j] != p->src[start + j]) {
				break;
			}
		}
		if (j == n) {
			return p->name_indexes[i];
		}
	}
	return -1;
}

static void guji_rec_set_unknown_name_error(guji_rec_parser_t *p, int32_t pos, int32_t start, int32_t end) {
	char buf[GUJI_REC_MSG_CAP];
	int off = snprintf(buf, sizeof(buf), "unknown capture name \"");
	for (int32_t k = start; k < end && off < (int)sizeof(buf) - 2; k++) {
		buf[off++] = (char)p->src[k];
	}
	buf[off++] = '"';
	buf[off] = '\0';
	guji_rec_set_error(p, pos, buf);
}

static guji_rec_node_t *guji_rec_parse_named_backref(guji_rec_parser_t *p, guji_rec_flags_t fl, int32_t bs) {
	p->pos++; /* consume 'k' */
	if (guji_rec_peek(p) != '<') {
		guji_rec_set_error(p, bs, "invalid named backreference syntax");
		return NULL;
	}
	p->pos++; /* consume '<' */
	int32_t start = p->pos;
	while (guji_rec_peek(p) != '>') {
		int32_t c = guji_rec_peek(p);
		if (c == GUJI_REC_EOF || c == ')') {
			guji_rec_set_error(p, bs, "missing closing > in named backreference");
			return NULL;
		}
		if (!guji_rec_is_name_char(c)) {
			guji_rec_set_error(p, p->pos, "invalid character in capture name");
			return NULL;
		}
		p->pos++;
	}
	int32_t end = p->pos;
	p->pos++; /* consume '>' */
	if (end == start) {
		guji_rec_set_error(p, bs, "empty capture name");
		return NULL;
	}
	int32_t idx = guji_rec_find_name(p, start, end);
	if (idx < 0) {
		guji_rec_set_unknown_name_error(p, bs, start, end);
		return NULL;
	}
	guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_BACKREF);
	n->backref_index = idx;
	n->fold = fl.fold;
	return n;
}

/* parseNamedGroup parses (?<name>...) — the '<' is at the current pos. */
static guji_rec_node_t *guji_rec_parse_named_group(guji_rec_parser_t *p, guji_rec_flags_t fl, int32_t open) {
	p->pos++; /* consume '<' */
	int32_t start = p->pos;
	for (;;) {
		int32_t c = guji_rec_peek(p);
		if (c == '>') {
			break;
		}
		if (c == GUJI_REC_EOF || c == ')') {
			guji_rec_set_error(p, open, "missing closing > in named group");
			return NULL;
		}
		if (!guji_rec_is_name_char(c)) {
			guji_rec_set_error(p, p->pos, "invalid character in capture name");
			return NULL;
		}
		p->pos++;
	}
	int32_t end = p->pos;
	p->pos++; /* consume '>' */
	guji_rec_skip_verbose(p, fl);
	int hidden = p->allow_hidden_names
		&& guji_rec_is_hidden_name(p, start, end);
	if (!guji_rec_record_name(p, open, start, end, p->num_cap + 1)) {
		return NULL;
	}
	p->num_cap++;
	int idx = p->num_cap;
	if (!hidden) {
		guji_rec_add_public_cap(p, idx);
	}
	guji_rec_node_t *body = guji_rec_parse_alternate(p, fl);
	if (p->err) {
		return NULL;
	}
	if (guji_rec_peek(p) != ')') {
		guji_rec_set_error(p, open, "missing closing )");
		return NULL;
	}
	p->pos++;
	guji_rec_node_t *g = guji_rec_new(p, GUJI_REC_GROUP);
	g->sub = body;
	g->cap = hidden ? 2 : 1;
	g->index = idx;
	return g;
}

/* parseFlagGroup parses (?flags) inline settings and (?flags:...) scoped groups.
   a/m/s are resolved into the AST in this slice; i expansion and x/U are
   rejected with stable diagnostics. */
static guji_rec_node_t *guji_rec_parse_flag_group(guji_rec_parser_t *p, guji_rec_flags_t fl, int32_t open) {
	guji_rec_flags_t newFl = fl;
	int neg = 0;
	int sawFlag = 0;
	for (;;) {
		guji_rec_skip_verbose(p, newFl);
		int32_t c = guji_rec_peek(p);
		switch (c) {
		case 'a':
			newFl.ascii = !neg;
			sawFlag = 1;
			break;
		case 'i':
			newFl.fold = !neg;
			sawFlag = 1;
			break;
		case 'm':
			newFl.multiline = !neg;
			sawFlag = 1;
			break;
		case 's':
			newFl.dot_all = !neg;
			sawFlag = 1;
			break;
		case 'x':
			newFl.verbose = !neg;
			sawFlag = 1;
			break;
		case 'U':
			guji_rec_set_error(p, p->pos, "the (?U) flag is not supported in v0");
			return NULL;
		case '-':
			if (neg) {
				guji_rec_set_error(p, p->pos, "invalid flag group");
				return NULL;
			}
			neg = 1;
			sawFlag = 0; /* a '-' must be followed by at least one flag */
			break;
		case ':':
			p->pos++;
			guji_rec_skip_verbose(p, newFl);
			{
				guji_rec_node_t *body = guji_rec_parse_alternate(p, newFl);
				if (p->err) {
					return NULL;
				}
				if (guji_rec_peek(p) != ')') {
					guji_rec_set_error(p, open, "missing closing )");
					return NULL;
				}
				p->pos++;
				guji_rec_node_t *g = guji_rec_new(p, GUJI_REC_GROUP);
				g->sub = body;
				g->cap = 0;
				return g;
			}
		case ')':
			if (neg && !sawFlag) {
				guji_rec_set_error(p, p->pos, "invalid flag group");
				return NULL;
			}
			p->pos++;
			/* Inline setting applies to the rest of the enclosing group.
			   parseConcat polls p->inline_flag_applied to update its fl. */
			p->flags = newFl;
			p->inline_flag_applied = 1;
			return guji_rec_new(p, GUJI_REC_EMPTY);
		case GUJI_REC_EOF:
			guji_rec_set_error(p, open, "missing closing )");
			return NULL;
		default:
			guji_rec_set_error(p, p->pos, "invalid flag in group");
			return NULL;
		}
		p->pos++;
	}
}

/* parseGroupSpecial dispatches the construct after a leading "(?". */
/* Return a sub-pattern's minimum and maximum scalar width, with bounded=0 for
   unbounded patterns (Max==-1 quantifiers and backreferences). Used for the
   bounded-lookbehind check. */
static void guji_rec_ast_width(const guji_rec_node_t *n, int *min, int *max, int *bounded) {
	switch (n->kind) {
	case GUJI_REC_EMPTY:
	case GUJI_REC_ANCHOR:
		*min = 0;
		*max = 0;
		*bounded = 1;
		return;
	case GUJI_REC_LITERAL:
	case GUJI_REC_ANY:
	case GUJI_REC_CLASS:
		*min = 1;
		*max = 1;
		*bounded = 1;
		return;
	case GUJI_REC_GRAPHEME:
	case GUJI_REC_RGI_EMOJI:
		*min = 1;
		*max = -1;
		*bounded = 0;
		return;
	case GUJI_REC_BACKREF:
		*min = 0;
		*max = 0;
		*bounded = 0;
		return;
	case GUJI_REC_CONCAT: {
		int mn = 0, mx = 0, bd = 1;
		for (int32_t i = 0; i < n->sub_count; i++) {
			int smin, smax, sb;
			guji_rec_ast_width(n->subs[i], &smin, &smax, &sb);
			if (!sb) {
				bd = 0;
			}
			mn += smin;
			if (bd) {
				if (smax < 0) {
					bd = 0;
					mx = -1;
				} else {
					mx += smax;
				}
			}
		}
		*min = mn;
		*max = mx;
		*bounded = bd;
		return;
	}
	case GUJI_REC_ALTERNATE: {
		if (n->sub_count == 0) {
			*min = 0;
			*max = 0;
			*bounded = 1;
			return;
		}
		int mn, mx, bd;
		guji_rec_ast_width(n->subs[0], &mn, &mx, &bd);
		for (int32_t i = 1; i < n->sub_count; i++) {
			int smin, smax, sb;
			guji_rec_ast_width(n->subs[i], &smin, &smax, &sb);
			if (smin < mn) {
				mn = smin;
			}
			if (!sb) {
				bd = 0;
			}
			if (bd) {
				if (smax < 0) {
					bd = 0;
					mx = -1;
				} else if (smax > mx) {
					mx = smax;
				}
			}
		}
		*min = mn;
		*max = mx;
		*bounded = bd;
		return;
	}
	case GUJI_REC_QUANTIFIER: {
		int smin, smax, sb;
		guji_rec_ast_width(n->sub, &smin, &smax, &sb);
		if (!sb) {
			*bounded = 0;
			if (n->qmax == -1) {
				*min = n->qmin * smin;
				*max = -1;
			} else {
				*min = n->qmin * smin;
				*max = n->qmax * smax;
			}
			return;
		}
		*min = n->qmin * smin;
		if (n->qmax == -1) {
			*max = -1;
			*bounded = 0;
			return;
		}
		*max = n->qmax * smax;
		*bounded = 1;
		return;
	}
	case GUJI_REC_GROUP:
	case GUJI_REC_ATOMIC:
	case GUJI_REC_LOOKAROUND:
	case GUJI_REC_SPLICE:
		guji_rec_ast_width(n->sub, min, max, bounded);
		return;
	default:
		*min = 0;
		*max = 0;
		*bounded = 0;
		return;
	}
}

static guji_rec_node_t *guji_rec_parse_group_special(guji_rec_parser_t *p, guji_rec_flags_t fl, int32_t open) {
	guji_rec_skip_verbose(p, fl);
	int32_t c = guji_rec_peek(p);
	if (c == ':') {
		p->pos++;
		guji_rec_skip_verbose(p, fl);
		guji_rec_node_t *body = guji_rec_parse_alternate(p, fl);
		if (p->err) {
			return NULL;
		}
		if (guji_rec_peek(p) != ')') {
			guji_rec_set_error(p, open, "missing closing )");
			return NULL;
		}
		p->pos++;
		guji_rec_node_t *g = guji_rec_new(p, GUJI_REC_GROUP);
		g->sub = body;
		g->cap = 0;
		return g;
	}
	if (c == '>') {
		p->pos++;
		guji_rec_skip_verbose(p, fl);
		guji_rec_node_t *body = guji_rec_parse_alternate(p, fl);
		if (p->err) {
			return NULL;
		}
		if (guji_rec_peek(p) != ')') {
			guji_rec_set_error(p, open, "missing closing )");
			return NULL;
		}
		p->pos++;
		guji_rec_node_t *a = guji_rec_new(p, GUJI_REC_ATOMIC);
		a->sub = body;
		return a;
	}
	if (c == '=' || c == '!') {
		p->pos++; /* consume '=' or '!' */
		guji_rec_skip_verbose(p, fl);
		int kind = (c == '!') ? GUJI_RE_LOOK_AHEAD_NEG : GUJI_RE_LOOK_AHEAD_POS;
		guji_rec_node_t *body = guji_rec_parse_alternate(p, fl);
		if (p->err) {
			return NULL;
		}
		if (guji_rec_peek(p) != ')') {
			guji_rec_set_error(p, open, "missing closing )");
			return NULL;
		}
		p->pos++;
		guji_rec_node_t *la = guji_rec_new(p, GUJI_REC_LOOKAROUND);
		la->sub = body;
		la->look_kind = kind;
		la->look_minw = 0;
		la->look_maxw = 0;
		return la;
	}
	if (c == '<') {
		int32_t next = guji_rec_at(p, 1);
		if (next == '=' || next == '!') {
			p->pos += 2; /* consume '<=' or '<!' */
			guji_rec_skip_verbose(p, fl);
			int kind = (next == '!') ? GUJI_RE_LOOK_BEHIND_NEG : GUJI_RE_LOOK_BEHIND_POS;
			guji_rec_node_t *body = guji_rec_parse_alternate(p, fl);
			if (p->err) {
				return NULL;
			}
			if (guji_rec_peek(p) != ')') {
				guji_rec_set_error(p, open, "missing closing )");
				return NULL;
			}
			p->pos++;
			int minw, maxw, bounded;
			guji_rec_ast_width(body, &minw, &maxw, &bounded);
			if (!bounded) {
				guji_rec_set_error(p, open, "lookbehind requires bounded width");
				return NULL;
			}
			guji_rec_node_t *la = guji_rec_new(p, GUJI_REC_LOOKAROUND);
			la->sub = body;
			la->look_kind = kind;
			la->look_minw = minw;
			la->look_maxw = maxw;
			return la;
		}
		return guji_rec_parse_named_group(p, fl, open);
	}
	if (c == 'P') {
		if (guji_rec_at(p, 1) != '<') {
			guji_rec_set_error(p, open, "invalid named group syntax");
			return NULL;
		}
		p->pos++; /* consume 'P', leaving '<' for parseNamedGroup */
		return guji_rec_parse_named_group(p, fl, open);
	}
	if (c == 'a' || c == 'i' || c == 'm' || c == 's' || c == 'x' || c == 'U' || c == '-') {
		return guji_rec_parse_flag_group(p, fl, open);
	}
	guji_rec_set_error(p, open, "invalid group syntax");
	return NULL;
}

/* parseGroup parses a '(' ... ')' construct. */
static guji_rec_node_t *guji_rec_parse_group(guji_rec_parser_t *p, guji_rec_flags_t fl) {
	int32_t open = p->pos;
	p->pos++; /* consume '(' */
	guji_rec_skip_verbose(p, fl);
	if (guji_rec_peek(p) == '?') {
		p->pos++; /* consume '?' */
		return guji_rec_parse_group_special(p, fl, open);
	}
	p->num_cap++;
	int idx = p->num_cap;
	guji_rec_add_public_cap(p, idx);
	guji_rec_node_t *body = guji_rec_parse_alternate(p, fl);
	if (p->err) {
		return NULL;
	}
	if (guji_rec_peek(p) != ')') {
		guji_rec_set_error(p, open, "missing closing )");
		return NULL;
	}
	p->pos++;
	guji_rec_node_t *g = guji_rec_new(p, GUJI_REC_GROUP);
	g->sub = body;
	g->cap = 1;
	g->index = idx;
	return g;
}

/* parseAtom parses a single (un-quantified) atom. */
static guji_rec_node_t *guji_rec_parse_atom(guji_rec_parser_t *p, guji_rec_flags_t fl) {
	guji_rec_skip_verbose(p, fl);
	int32_t c = guji_rec_peek(p);
	switch (c) {
	case '(':
		return guji_rec_parse_group(p, fl);
	case '[':
		return guji_rec_parse_class(p, fl);
	case '.': {
		p->pos++;
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_ANY);
		n->dot_all = fl.dot_all;
		return n;
	}
	case '^': {
		p->pos++;
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_ANCHOR);
		n->anchor_kind = GUJI_REC_ANCHOR_BEGIN_LINE;
		n->multiline = fl.multiline;
		return n;
	}
	case '$': {
		p->pos++;
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_ANCHOR);
		n->anchor_kind = GUJI_REC_ANCHOR_END_LINE;
		n->multiline = fl.multiline;
		return n;
	}
	case '\\':
		return guji_rec_parse_escape(p, fl);
	case '*':
	case '+':
	case '?':
		guji_rec_set_error(p, p->pos, "missing argument to repetition operator");
		return NULL;
	case '{': {
		int32_t lo, hi;
		if (guji_rec_scan_counted(p, &lo, &hi) >= 0) {
			guji_rec_set_error(p, p->pos, "missing argument to repetition operator");
			return NULL;
		}
		p->pos++;
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_LITERAL);
		n->rune = '{';
		n->fold = fl.fold;
		return n;
	}
	case '<': {
		if (guji_rec_at(p, 1) == '{') {
			guji_rec_set_error(p, p->pos, "regex splicing requires host-provided parts");
			return NULL;
		}
		p->pos++;
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_LITERAL);
		n->rune = '<';
		n->fold = fl.fold;
		return n;
	}
	case ')':
		guji_rec_set_error(p, p->pos, "unexpected )");
		return NULL;
	default: {
		if (p->splices && c >= 0xE000 && c < 0xE000 + p->splice_count) {
			p->pos++;
			return p->splices[c - 0xE000];
		}
		p->pos++;
		guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_LITERAL);
		n->rune = c;
		n->fold = fl.fold;
		return n;
	}
	}
}

/* maybeQuantifier applies a trailing *, +, ?, or {n,m} to sub. */
static guji_rec_node_t *guji_rec_maybe_quantifier(guji_rec_parser_t *p, guji_rec_node_t *sub, guji_rec_flags_t fl) {
	guji_rec_skip_verbose(p, fl);
	int32_t min, max;
	int32_t op_pos = p->pos;
	int32_t c = guji_rec_peek(p);
	switch (c) {
	case '*':
		min = 0;
		max = -1;
		p->pos++;
		break;
	case '+':
		min = 1;
		max = -1;
		p->pos++;
		break;
	case '?':
		min = 0;
		max = 1;
		p->pos++;
		break;
	case '{': {
		int32_t lo, hi;
		int32_t consumed = guji_rec_scan_counted(p, &lo, &hi);
		if (consumed < 0) {
			return sub; /* a '{' that is not a valid {n,m} is a literal */
		}
		p->pos += consumed;
		min = lo;
		max = hi;
		break;
	}
	default:
		return sub;
	}
	if (!guji_rec_quantifiable(sub)) {
		guji_rec_set_error(p, op_pos, "missing argument to repetition operator");
		return NULL;
	}
	if (max != -1 && max < min) {
		guji_rec_set_error(p, op_pos, "invalid repetition count");
		return NULL;
	}
	int greedy = 1;
	int possessive = 0;
	guji_rec_skip_verbose(p, fl);
	switch (guji_rec_peek(p)) {
	case '?':
		greedy = 0;
		p->pos++;
		break;
	case '+':
		possessive = 1;
		p->pos++;
		break;
	}
	/* reject stacked quantifiers (a**, a*{2}, ...) */
	guji_rec_skip_verbose(p, fl);
	switch (guji_rec_peek(p)) {
	case '*':
	case '+':
	case '?':
		guji_rec_set_error(p, p->pos, "bad repetition operator");
		return NULL;
	case '{': {
		int32_t lo, hi;
		if (guji_rec_scan_counted(p, &lo, &hi) >= 0) {
			guji_rec_set_error(p, p->pos, "bad repetition operator");
			return NULL;
		}
		break;
	}
	}
	guji_rec_node_t *q = guji_rec_new(p, GUJI_REC_QUANTIFIER);
	q->sub = sub;
	q->qmin = min;
	q->qmax = max;
	q->greedy = greedy;
	if (possessive) {
		guji_rec_node_t *a = guji_rec_new(p, GUJI_REC_ATOMIC);
		a->sub = q;
		return a;
	}
	return q;
}

static guji_rec_node_t *guji_rec_parse_concat(guji_rec_parser_t *p, guji_rec_flags_t *fl) {
	guji_rec_node_t **subs = NULL;
	int32_t count = 0;
	int32_t cap = 0;
	for (;;) {
		guji_rec_skip_verbose(p, *fl);
		int32_t c = guji_rec_peek(p);
		if (c == GUJI_REC_EOF || c == '|' || c == ')') {
			break;
		}
		guji_rec_node_t *n = guji_rec_parse_atom(p, *fl);
		if (p->err) {
			free(subs);
			return NULL;
		}
		if (p->inline_flag_applied) {
			*fl = p->flags;
			p->inline_flag_applied = 0;
			continue;
		}
		n = guji_rec_maybe_quantifier(p, n, *fl);
		if (p->err) {
			free(subs);
			return NULL;
		}
		if (count == cap) {
			cap = cap ? cap * 2 : 4;
			guji_rec_node_t **ns = (guji_rec_node_t **)realloc(subs, sizeof(*ns) * (size_t)cap);
			if (!ns) {
				abort();
			}
			subs = ns;
		}
		subs[count++] = n;
	}
	if (count == 0) {
		free(subs);
		return guji_rec_new(p, GUJI_REC_EMPTY);
	}
	if (count == 1) {
		guji_rec_node_t *only = subs[0];
		free(subs);
		return only;
	}
	guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_CONCAT);
	n->subs = (guji_rec_node_t **)guji_rec_track(p, subs);
	n->sub_count = count;
	return n;
}

static guji_rec_node_t *guji_rec_parse_alternate(guji_rec_parser_t *p, guji_rec_flags_t fl) {
	guji_rec_flags_t cur = fl;
	guji_rec_skip_verbose(p, cur);
	guji_rec_node_t *first = guji_rec_parse_concat(p, &cur);
	if (p->err) {
		return NULL;
	}
	guji_rec_skip_verbose(p, cur);
	if (guji_rec_peek(p) != '|') {
		return first;
	}
	guji_rec_node_t **subs = NULL;
	int32_t count = 0;
	int32_t cap = 0;
	cap = 4;
	subs = (guji_rec_node_t **)malloc(sizeof(*subs) * (size_t)cap);
	if (!subs) {
		abort();
	}
	subs[count++] = first;
	for (;;) {
		guji_rec_skip_verbose(p, cur);
		if (guji_rec_peek(p) != '|') {
			break;
		}
		p->pos++; /* consume '|' */
		guji_rec_node_t *next = guji_rec_parse_concat(p, &cur);
		if (p->err) {
			free(subs);
			return NULL;
		}
		if (count == cap) {
			cap *= 2;
			guji_rec_node_t **ns = (guji_rec_node_t **)realloc(subs, sizeof(*ns) * (size_t)cap);
			if (!ns) {
				abort();
			}
			subs = ns;
		}
		subs[count++] = next;
	}
	guji_rec_node_t *n = guji_rec_new(p, GUJI_REC_ALTERNATE);
	n->subs = (guji_rec_node_t **)guji_rec_track(p, subs);
	n->sub_count = count;
	return n;
}

/* ---------- compiler ---------- */

typedef struct {
	guji_regex_inst_t *insts;
	int32_t inst_count;
	int32_t inst_cap;
	guji_regex_class_t *classes;
	int32_t class_count;
	int32_t class_cap;
	int32_t num_cap;
	guji_regex_look_t *looks;
	int32_t look_count;
	int32_t look_cap;
	guji_regex_program_t **subprogs;
	int32_t subprog_count;
	int32_t subprog_cap;
} guji_rec_builder_t;

static guji_regex_inst_t guji_rec_inst(int op) {
	guji_regex_inst_t i;
	i.op = op;
	i.rune = 0;
	i.cls = 0;
	i.out = 0;
	i.out1 = 0;
	i.slot = 0;
	i.fold = 0;
	i.ascii = 0;
	return i;
}

static int32_t guji_rec_emit(guji_rec_builder_t *b, guji_regex_inst_t inst) {
	if (b->inst_count == b->inst_cap) {
		int32_t nc = b->inst_cap ? b->inst_cap * 2 : 16;
		guji_regex_inst_t *na = (guji_regex_inst_t *)realloc(b->insts, sizeof(*na) * (size_t)nc);
		if (!na) {
			abort();
		}
		b->insts = na;
		b->inst_cap = nc;
	}
	int32_t idx = b->inst_count;
	b->insts[b->inst_count++] = inst;
	return idx;
}

static int guji_rec_range_cmp(const void *a, const void *b) {
	const guji_regex_range_t *ra = (const guji_regex_range_t *)a;
	const guji_regex_range_t *rb = (const guji_regex_range_t *)b;
	if (ra->lo < rb->lo) {
		return -1;
	}
	if (ra->lo > rb->lo) {
		return 1;
	}
	return 0;
}

/* guji_rec_merge_ranges sorts + coalesces ranges into a fresh heap array
   (== Go's runesToRanges output for the same scalar set). */
static guji_regex_range_t *guji_rec_merge_ranges(const guji_regex_range_t *in, int32_t in_count, int32_t *out_count) {
	*out_count = 0;
	if (in_count <= 0) {
		return NULL;
	}
	guji_regex_range_t *tmp = (guji_regex_range_t *)malloc(sizeof(*tmp) * (size_t)in_count);
	if (!tmp) {
		abort();
	}
	memcpy(tmp, in, sizeof(*tmp) * (size_t)in_count);
	qsort(tmp, (size_t)in_count, sizeof(*tmp), guji_rec_range_cmp);
	guji_regex_range_t *merged = (guji_regex_range_t *)malloc(sizeof(*merged) * (size_t)in_count);
	if (!merged) {
		abort();
	}
	merged[0] = tmp[0];
	int32_t merged_count = 1;
	for (int32_t i = 1; i < in_count; i++) {
		guji_regex_range_t *last = &merged[merged_count - 1];
		if (tmp[i].lo <= last->hi + 1) {
			if (tmp[i].hi > last->hi) {
				last->hi = tmp[i].hi;
			}
			continue;
		}
		merged[merged_count++] = tmp[i];
	}
	free(tmp);
	*out_count = merged_count;
	return merged;
}

/* guji_rec_add_class sorts + coalesces ranges (== Go's runesToRanges output for
   non-folded classes) and appends a class table, returning its index. */
static int32_t guji_rec_add_class(guji_rec_builder_t *b, int negated, const guji_regex_range_t *in, int32_t in_count) {
	int32_t merged_count = 0;
	guji_regex_range_t *merged = guji_rec_merge_ranges(in, in_count, &merged_count);
	if (b->class_count == b->class_cap) {
		int32_t nc = b->class_cap ? b->class_cap * 2 : 8;
		guji_regex_class_t *na = (guji_regex_class_t *)realloc(b->classes, sizeof(*na) * (size_t)nc);
		if (!na) {
			abort();
		}
		b->classes = na;
		b->class_cap = nc;
	}
	int32_t idx = b->class_count;
	b->classes[idx].negated = negated;
	b->classes[idx].ranges = merged;
	b->classes[idx].range_count = merged_count;
	b->class_count++;
	return idx;
}

/* guji_rec_fold_orbit_push appends every scalar in r's simple case-folding
   orbit other than r itself, as singleton ranges (compile.go foldRunes). */
static void guji_rec_fold_orbit_push(guji_rec_ranges_t *out, int32_t r) {
	for (int32_t f = guji_simple_fold(r); f != r; f = guji_simple_fold(f)) {
		guji_rec_ranges_push(out, f, f);
	}
}

/* guji_rec_add_class_fold is the (?i) class path: close the scalar set under
   simple case folding, then sort+coalesce. Merging first keeps the orbit walk
   per unique scalar, matching Go's rune-set semantics. */
static int32_t guji_rec_add_class_fold(guji_rec_builder_t *b, int negated, const guji_regex_range_t *in, int32_t in_count) {
	int32_t base_count = 0;
	guji_regex_range_t *base = guji_rec_merge_ranges(in, in_count, &base_count);
	guji_rec_ranges_t buf = {0};
	for (int32_t i = 0; i < base_count; i++) {
		guji_rec_ranges_push(&buf, base[i].lo, base[i].hi);
		for (int32_t r = base[i].lo; r <= base[i].hi; r++) {
			guji_rec_fold_orbit_push(&buf, r);
		}
	}
	free(base);
	int32_t idx = guji_rec_add_class(b, negated, buf.data, buf.count);
	free(buf.data);
	return idx;
}

static int32_t guji_rec_add_class_raw(guji_rec_builder_t *b, int negated, const guji_regex_range_t *in, int32_t in_count) {
	guji_regex_range_t *copy = NULL;
	if (in_count > 0) {
		copy = (guji_regex_range_t *)malloc(sizeof(*copy) * (size_t)in_count);
		if (!copy) {
			abort();
		}
		memcpy(copy, in, sizeof(*copy) * (size_t)in_count);
	}
	if (b->class_count == b->class_cap) {
		int32_t nc = b->class_cap ? b->class_cap * 2 : 8;
		guji_regex_class_t *na = (guji_regex_class_t *)realloc(b->classes, sizeof(*na) * (size_t)nc);
		if (!na) {
			abort();
		}
		b->classes = na;
		b->class_cap = nc;
	}
	int32_t idx = b->class_count;
	b->classes[idx].negated = negated;
	b->classes[idx].ranges = copy;
	b->classes[idx].range_count = in_count;
	b->class_count++;
	return idx;
}

static void guji_rec_compile(guji_rec_builder_t *b, const guji_rec_node_t *n);

static void guji_rec_compile_alternate(guji_rec_builder_t *b, const guji_rec_node_t *n) {
	if (n->sub_count == 0) {
		return;
	}
	if (n->sub_count == 1) {
		guji_rec_compile(b, n->subs[0]);
		return;
	}
	int32_t nalt = n->sub_count;
	int32_t *splits = (int32_t *)malloc(sizeof(int32_t) * (size_t)(nalt - 1));
	int32_t *ends = (int32_t *)malloc(sizeof(int32_t) * (size_t)(nalt - 1));
	if (!splits || !ends) {
		abort();
	}
	int32_t ends_count = 0;
	for (int32_t i = 0; i < nalt - 1; i++) {
		splits[i] = guji_rec_emit(b, guji_rec_inst(GUJI_RE_OP_SPLIT));
	}
	for (int32_t i = 0; i < nalt; i++) {
		if (i < nalt - 1) {
			b->insts[splits[i]].out = b->inst_count;
		}
		guji_rec_compile(b, n->subs[i]);
		if (i < nalt - 1) {
			ends[ends_count++] = guji_rec_emit(b, guji_rec_inst(GUJI_RE_OP_JMP));
			b->insts[splits[i]].out1 = b->inst_count;
		}
	}
	int32_t after = b->inst_count;
	for (int32_t i = 0; i < ends_count; i++) {
		b->insts[ends[i]].out = after;
	}
	free(splits);
	free(ends);
}

static void guji_rec_compile_star(guji_rec_builder_t *b, const guji_rec_node_t *sub, int greedy) {
	int32_t split = guji_rec_emit(b, guji_rec_inst(GUJI_RE_OP_SPLIT));
	int32_t body_start = b->inst_count;
	guji_rec_compile(b, sub);
	guji_regex_inst_t jmp = guji_rec_inst(GUJI_RE_OP_JMP);
	jmp.out = split;
	guji_rec_emit(b, jmp);
	int32_t after = b->inst_count;
	if (greedy) {
		b->insts[split].out = body_start;
		b->insts[split].out1 = after;
	} else {
		b->insts[split].out = after;
		b->insts[split].out1 = body_start;
	}
}

static void guji_rec_compile_plus(guji_rec_builder_t *b, const guji_rec_node_t *sub, int greedy) {
	int32_t body_start = b->inst_count;
	guji_rec_compile(b, sub);
	int32_t split = guji_rec_emit(b, guji_rec_inst(GUJI_RE_OP_SPLIT));
	int32_t after = b->inst_count;
	if (greedy) {
		b->insts[split].out = body_start;
		b->insts[split].out1 = after;
	} else {
		b->insts[split].out = after;
		b->insts[split].out1 = body_start;
	}
}

static void guji_rec_compile_quest(guji_rec_builder_t *b, const guji_rec_node_t *sub, int greedy) {
	int32_t split = guji_rec_emit(b, guji_rec_inst(GUJI_RE_OP_SPLIT));
	guji_rec_compile(b, sub);
	int32_t after = b->inst_count;
	if (greedy) {
		b->insts[split].out = split + 1;
		b->insts[split].out1 = after;
	} else {
		b->insts[split].out = after;
		b->insts[split].out1 = split + 1;
	}
}

static void guji_rec_compile_quantifier(guji_rec_builder_t *b, const guji_rec_node_t *n) {
	if (n->qmin == 0 && n->qmax == -1) {
		guji_rec_compile_star(b, n->sub, n->greedy);
	} else if (n->qmin == 1 && n->qmax == -1) {
		guji_rec_compile_plus(b, n->sub, n->greedy);
	} else if (n->qmin == 0 && n->qmax == 1) {
		guji_rec_compile_quest(b, n->sub, n->greedy);
	} else {
		for (int i = 0; i < n->qmin; i++) {
			guji_rec_compile(b, n->sub);
		}
		if (n->qmax == -1) {
			guji_rec_compile_star(b, n->sub, n->greedy);
		} else {
			for (int i = n->qmin; i < n->qmax; i++) {
				guji_rec_compile_quest(b, n->sub, n->greedy);
			}
		}
	}
}

/* guji_rec_builder_to_program transfers ownership of a builder's arrays into a
   freshly heap-allocated program (the standalone program or a lookaround
   sub-program). The caller frees it with guji_regex_program_free. */
static guji_regex_program_t *guji_rec_builder_to_program(guji_rec_builder_t *b) {
	guji_regex_program_t *prog = (guji_regex_program_t *)malloc(sizeof(*prog));
	if (!prog) {
		abort();
	}
	prog->version = 1;
	prog->insts = b->insts;
	prog->inst_count = b->inst_count;
	prog->classes = b->classes;
	prog->class_count = b->class_count;
	prog->num_cap = b->num_cap;
	prog->public_num_cap = 0;
	prog->public_cap_indexes = NULL;
	prog->cap_names = NULL;
	prog->looks = b->looks;
	prog->look_count = b->look_count;
	prog->subprogs = (const guji_regex_program_t *const *)b->subprogs;
	prog->subprog_count = b->subprog_count;
	return prog;
}

/* guji_rec_compile_lookaround mirrors compile.go compileLookaround: the body is
   compiled into its OWN sub-program (sharing num_cap so backrefs inside the
   lookaround resolve against the parent captures) ending in OpMatch; a LookInfo
   records the kind/width/after-PC; then OpLookStart (cls = look index) and
   OpLookEnd are emitted into the parent. AfterPC points just past OpLookEnd. */
static void guji_rec_compile_lookaround(guji_rec_builder_t *b, const guji_rec_node_t *n) {
	guji_rec_builder_t sub;
	memset(&sub, 0, sizeof(sub));
	sub.num_cap = b->num_cap;
	guji_rec_compile(&sub, n->sub);
	guji_rec_emit(&sub, guji_rec_inst(GUJI_RE_OP_MATCH));
	guji_regex_program_t *subprog = guji_rec_builder_to_program(&sub);

	int32_t idx = b->look_count;
	if (b->look_count == b->look_cap) {
		int32_t nc = b->look_cap ? b->look_cap * 2 : 4;
		guji_regex_look_t *nl = (guji_regex_look_t *)realloc(b->looks, sizeof(*nl) * (size_t)nc);
		if (!nl) {
			abort();
		}
		b->looks = nl;
		b->look_cap = nc;
	}
	b->looks[idx].kind = n->look_kind;
	b->looks[idx].minw = n->look_minw;
	b->looks[idx].maxw = n->look_maxw;
	b->looks[idx].after_pc = b->inst_count + 2; /* past OpLookStart + OpLookEnd */
	b->look_count++;

	if (b->subprog_count == b->subprog_cap) {
		int32_t nc = b->subprog_cap ? b->subprog_cap * 2 : 4;
		guji_regex_program_t **ns = (guji_regex_program_t **)realloc(b->subprogs, sizeof(*ns) * (size_t)nc);
		if (!ns) {
			abort();
		}
		b->subprogs = ns;
		b->subprog_cap = nc;
	}
	b->subprogs[b->subprog_count++] = subprog;

	guji_regex_inst_t ls = guji_rec_inst(GUJI_RE_OP_LOOK_START);
	ls.cls = idx;
	guji_rec_emit(b, ls);
	guji_rec_emit(b, guji_rec_inst(GUJI_RE_OP_LOOK_END));
}

static void guji_rec_compile(guji_rec_builder_t *b, const guji_rec_node_t *n) {
	switch (n->kind) {
	case GUJI_REC_EMPTY:
		break;
	case GUJI_REC_LITERAL: {
		if (n->fold) {
			/* compile.go classForFoldedLiteral: the literal becomes a class
			   holding its full simple-fold orbit. */
			guji_rec_ranges_t buf = {0};
			guji_rec_ranges_push(&buf, n->rune, n->rune);
			guji_rec_fold_orbit_push(&buf, n->rune);
			int32_t idx = guji_rec_add_class(b, 0, buf.data, buf.count);
			free(buf.data);
			guji_regex_inst_t i = guji_rec_inst(GUJI_RE_OP_CLASS);
			i.cls = idx;
			guji_rec_emit(b, i);
			break;
		}
		guji_regex_inst_t i = guji_rec_inst(GUJI_RE_OP_CHAR);
		i.rune = n->rune;
		guji_rec_emit(b, i);
		break;
	}
	case GUJI_REC_ANY:
		guji_rec_emit(b, guji_rec_inst(n->dot_all ? GUJI_RE_OP_ANYNL : GUJI_RE_OP_ANY));
		break;
	case GUJI_REC_ANCHOR: {
		int op;
		switch (n->anchor_kind) {
		case GUJI_REC_ANCHOR_BEGIN_LINE:
			op = n->multiline ? GUJI_RE_OP_ASSERT_BOL : GUJI_RE_OP_ASSERT_BOT;
			break;
		case GUJI_REC_ANCHOR_END_LINE:
			op = n->multiline ? GUJI_RE_OP_ASSERT_EOL : GUJI_RE_OP_ASSERT_EOT;
			break;
		case GUJI_REC_ANCHOR_BEGIN_TEXT:
			op = GUJI_RE_OP_ASSERT_BOT;
			break;
		case GUJI_REC_ANCHOR_END_TEXT:
			op = GUJI_RE_OP_ASSERT_EOT;
			break;
		case GUJI_REC_ANCHOR_END_TEXT_ABS:
			op = GUJI_RE_OP_ASSERT_EOT_ABS;
			break;
		case GUJI_REC_ANCHOR_WORD_BOUNDARY: {
			guji_regex_inst_t i = guji_rec_inst(GUJI_RE_OP_WORD_B);
			i.ascii = n->ascii;
			guji_rec_emit(b, i);
			return;
		}
		case GUJI_REC_ANCHOR_NON_WORD_BOUNDARY: {
			guji_regex_inst_t i = guji_rec_inst(GUJI_RE_OP_NWORD_B);
			i.ascii = n->ascii;
			guji_rec_emit(b, i);
			return;
		}
		default:
			return;
		}
		guji_rec_emit(b, guji_rec_inst(op));
		break;
	}
	case GUJI_REC_CLASS: {
		int32_t idx;
		if (n->cls_raw) {
			idx = guji_rec_add_class_raw(b, n->cls_negated, n->cls_ranges, n->cls_range_count);
		} else if (n->cls_fold) {
			idx = guji_rec_add_class_fold(b, n->cls_negated, n->cls_ranges, n->cls_range_count);
		} else {
			idx = guji_rec_add_class(b, n->cls_negated, n->cls_ranges, n->cls_range_count);
		}
		guji_regex_inst_t i = guji_rec_inst(GUJI_RE_OP_CLASS);
		i.cls = idx;
		guji_rec_emit(b, i);
		break;
	}
	case GUJI_REC_CONCAT:
		for (int32_t i = 0; i < n->sub_count; i++) {
			guji_rec_compile(b, n->subs[i]);
		}
		break;
	case GUJI_REC_ALTERNATE:
		guji_rec_compile_alternate(b, n);
		break;
	case GUJI_REC_QUANTIFIER:
		guji_rec_compile_quantifier(b, n);
		break;
	case GUJI_REC_BACKREF: {
		guji_regex_inst_t i = guji_rec_inst(GUJI_RE_OP_BACKREF);
		i.slot = n->backref_index * 2;
		i.fold = n->fold;
		guji_rec_emit(b, i);
		break;
	}
	case GUJI_REC_GROUP:
		if (n->cap) {
			int32_t start_slot = n->index * 2;
			guji_regex_inst_t s = guji_rec_inst(GUJI_RE_OP_SAVE);
			s.slot = start_slot;
			guji_rec_emit(b, s);
			guji_rec_compile(b, n->sub);
			guji_regex_inst_t e = guji_rec_inst(GUJI_RE_OP_SAVE);
			e.slot = start_slot + 1;
			guji_rec_emit(b, e);
		} else {
			guji_rec_compile(b, n->sub);
		}
		break;
	case GUJI_REC_ATOMIC:
		guji_rec_emit(b, guji_rec_inst(GUJI_RE_OP_CUT_MARK));
		guji_rec_compile(b, n->sub);
		guji_rec_emit(b, guji_rec_inst(GUJI_RE_OP_CUT));
		break;
	case GUJI_REC_LOOKAROUND:
		guji_rec_compile_lookaround(b, n);
		break;
	case GUJI_REC_GRAPHEME:
		guji_rec_emit(b, guji_rec_inst(GUJI_RE_OP_GRAPHEME_X));
		break;
	case GUJI_REC_RGI_EMOJI:
		guji_rec_emit(b, guji_rec_inst(GUJI_RE_OP_RGI_EMOJI));
		break;
	case GUJI_REC_SPLICE:
		guji_rec_compile(b, n->sub);
		break;
	default:
		break;
	}
}

/* ---------- public API ---------- */

typedef struct {
	int ok;
	int32_t pos;
	char msg[GUJI_REC_MSG_CAP];
	guji_regex_program_t *prog;
} guji_regex_compile_result_t;

void guji_regex_program_free(guji_regex_program_t *prog) {
	if (!prog) {
		return;
	}
	for (int32_t i = 0; i < prog->subprog_count; i++) {
		guji_regex_program_free((guji_regex_program_t *)prog->subprogs[i]);
	}
	for (int32_t i = 0; i < prog->class_count; i++) {
		free((void *)prog->classes[i].ranges);
	}
	free((void *)prog->classes);
	free((void *)prog->insts);
	free((void *)prog->looks);
	free((void *)prog->subprogs);
	free((void *)prog->public_cap_indexes);
	if (prog->cap_names != NULL) {
		for (int32_t i = 0; i < prog->num_cap; i++) {
			free((void *)prog->cap_names[i]);
		}
		free((void *)prog->cap_names);
	}
	free(prog);
}

static void guji_rec_parser_teardown(guji_rec_parser_t *p) {
	for (int32_t i = 0; i < p->alloc_count; i++) {
		free(p->allocs[i]);
	}
	free(p->allocs);
	for (int32_t i = 0; i < p->name_count; i++) {
		free(p->names[i]);
	}
	free(p->names);
	free(p->name_lens);
	free(p->name_indexes);
	free(p->public_cap_indexes);
	free(p->src);
}

/* guji_rec_decode_runes appends the UTF-8 string's runes to dst (which must
   have capacity for at least strlen(s) more entries), returning the new
   length. Positions then match Go's []rune offsets exactly. */
static int32_t guji_rec_decode_runes(const char *s, int32_t *dst, int32_t len) {
	int32_t blen = (int32_t)strlen(s);
	int32_t bp = 0;
	while (bp < blen) {
		int32_t r, next;
		if (!guji_regex_read_rune(s, blen, bp, &r, &next)) {
			break;
		}
		dst[len++] = r;
		bp = next;
	}
	return len;
}

/* guji_rec_error_result copies the parser's error state into a result and
   tears the parser down. */
static guji_regex_compile_result_t guji_rec_error_result(guji_rec_parser_t *p) {
	guji_regex_compile_result_t res;
	res.ok = 0;
	res.pos = p->err_pos;
	size_t i = 0;
	for (; p->msg[i] != '\0' && i < GUJI_REC_MSG_CAP - 1; i++) {
		res.msg[i] = p->msg[i];
	}
	res.msg[i] = '\0';
	res.prog = NULL;
	guji_rec_parser_teardown(p);
	return res;
}

static void guji_rec_hide_spliced_captures(guji_rec_node_t *n, int32_t offset);

/* guji_rec_finish parses the parser's assembled rune source and compiles the
   tree into a Program, consuming (tearing down) the parser either way. */
static guji_regex_compile_result_t guji_rec_finish(guji_rec_parser_t *p) {
	guji_rec_node_t *root = guji_rec_parse_alternate(p, p->flags);
	if (!p->err && p->pos < p->len) {
		guji_rec_set_error(p, p->pos, "unexpected )");
	}
	if (p->err) {
		return guji_rec_error_result(p);
	}

	/* Host captures were numbered without the independently parsed splice
	   captures. Put every splice's private slots after that stable public prefix. */
	int32_t hidden_offset = p->num_cap;
	for (int32_t i = 0; i < p->splice_count; i++) {
		guji_rec_node_t *splice = p->splices[i];
		guji_rec_hide_spliced_captures(splice->sub, hidden_offset);
		hidden_offset += splice->index;
	}
	p->num_cap = hidden_offset;

	guji_rec_builder_t b;
	memset(&b, 0, sizeof(b));
	b.num_cap = p->num_cap; /* shared by lookaround sub-programs before compile */
	guji_rec_compile(&b, root);
	guji_rec_emit(&b, guji_rec_inst(GUJI_RE_OP_MATCH));

	guji_regex_program_t *prog = guji_rec_builder_to_program(&b);
	prog->public_num_cap = p->public_cap_count;
	prog->public_cap_indexes = p->public_cap_indexes;
	p->public_cap_indexes = NULL;
	p->public_cap_count = 0;
	p->public_cap_cap = 0;
	if (p->num_cap > 0) {
		char **cap_names = (char **)calloc((size_t)p->num_cap, sizeof(char *));
		if (!cap_names) {
			abort();
		}
		for (int32_t i = 0; i < p->name_count; i++) {
			int32_t slot = p->name_indexes[i] - 1;
			int32_t len = p->name_lens[i];
			if (slot < 0 || slot >= p->num_cap) {
				abort();
			}
			cap_names[slot] = (char *)malloc((size_t)len + 1);
			if (!cap_names[slot]) {
				abort();
			}
			for (int32_t j = 0; j < len; j++) {
				cap_names[slot][j] = (char)p->names[i][j];
			}
			cap_names[slot][len] = '\0';
		}
		prog->cap_names = (const char *const *)cap_names;
	}

	guji_rec_parser_teardown(p);

	guji_regex_compile_result_t res;
	res.ok = 1;
	res.pos = 0;
	res.msg[0] = '\0';
	res.prog = prog;
	return res;
}

static guji_regex_compile_result_t guji_regex_compile_mode(
		const char *pattern, int allow_hidden_names) {
	int32_t *src = (int32_t *)malloc(sizeof(int32_t) * (strlen(pattern) + 1));
	if (!src) {
		abort();
	}
	int32_t rlen = guji_rec_decode_runes(pattern, src, 0);

	guji_rec_parser_t p;
	memset(&p, 0, sizeof(p));
	p.src = src;
	p.len = rlen;
	p.allow_hidden_names = allow_hidden_names;
	return guji_rec_finish(&p);
}

guji_regex_compile_result_t guji_regex_compile(const char *pattern) {
	return guji_regex_compile_mode(pattern, 0);
}

/* Compiler-generated first-class Regex values may contain reserved private
   capture names. Keeping this entry point separate prevents raw user patterns
   from forging the private-capture representation. */
static guji_regex_compile_result_t guji_regex_compile_internal(
		const char *pattern) {
	return guji_regex_compile_mode(pattern, 1);
}

/* ---------- spliced compilation (host-provided parts, X6d-2b-ii-b) ----------

   A regex literal with <{ expr }> splices is assembled by the compiler into
   parts after
	   evaluating each splice expression. A part is either host regex text
	   (pattern == NULL) or a spliced regex pattern (pattern != NULL), which is
	   parsed fresh, keeps private captures for its own backreferences, and is
	   inserted as ONE noncapturing atom. Str-valued
   splices are escaped by the caller (guji_regex_escape_literal) and passed as
   text using the literal-escape contract.

   A spliced part is re-parsed from its pattern string. Compiler-materialized
   first-class values carry the private provenance bit, which is the sole
   authority for accepting their reserved hidden-capture names. */

typedef struct {
	const char *text;    /* host regex source; used when pattern == NULL */
	const char *pattern; /* Regex value; its captures become private here */
} guji_regex_part_t;

static int guji_regex_value_is_private(const char* pattern) {
	return pattern != NULL
		&& GUJI_HDR(pattern)->kind == GUJI_KIND_STR
		&& (GUJI_HDR(pattern)->flags & GUJI_REGEX_PRIVATE) != 0;
}

/* A splice keeps its own capture slots so its backreferences remain meaningful,
   but those slots are private to the splice. Rebase every local slot above the
   host-visible captures and mark groups private; public Match indexing is carried
   separately by program->public_cap_indexes. */
static void guji_rec_hide_spliced_captures(guji_rec_node_t *n, int32_t offset) {
	switch (n->kind) {
	case GUJI_REC_CONCAT:
	case GUJI_REC_ALTERNATE:
		for (int32_t i = 0; i < n->sub_count; i++) {
			guji_rec_hide_spliced_captures(n->subs[i], offset);
		}
		return;
	case GUJI_REC_GROUP:
		if (n->cap) {
			n->cap = 2;
			n->index += offset;
		}
		guji_rec_hide_spliced_captures(n->sub, offset);
		return;
	case GUJI_REC_QUANTIFIER:
	case GUJI_REC_ATOMIC:
	case GUJI_REC_LOOKAROUND:
	case GUJI_REC_SPLICE:
		guji_rec_hide_spliced_captures(n->sub, offset);
		return;
	case GUJI_REC_BACKREF:
		n->backref_index += offset;
		return;
	default:
		return;
	}
}

/* guji_rec_parser_absorb moves the sub-parse's AST arena into the host parser
   (the spliced nodes must outlive the sub-parse) and frees everything else
   the sub-parser owns. */
static void guji_rec_parser_absorb(guji_rec_parser_t *host, guji_rec_parser_t *sub) {
	for (int32_t i = 0; i < sub->alloc_count; i++) {
		guji_rec_track(host, sub->allocs[i]);
	}
	free(sub->allocs);
	sub->allocs = NULL;
	sub->alloc_count = 0;
	sub->alloc_cap = 0;
	guji_rec_parser_teardown(sub);
}

guji_regex_compile_result_t guji_regex_compile_spliced(const guji_regex_part_t *parts, int32_t part_count) {
	/* Assembled source capacity: every text byte is at most one rune, every
	   spliced part contributes exactly one marker rune. */
	size_t cap = 1;
	int32_t splice_total = 0;
	for (int32_t i = 0; i < part_count; i++) {
		if (parts[i].pattern != NULL) {
			splice_total++;
			cap++;
		} else {
			cap += strlen(parts[i].text);
		}
	}
	int32_t *src = (int32_t *)malloc(sizeof(int32_t) * cap);
	guji_rec_node_t **splices = NULL;
	if (splice_total > 0) {
		splices = (guji_rec_node_t **)malloc(sizeof(guji_rec_node_t *) * (size_t)splice_total);
	}
	if (!src || (splice_total > 0 && !splices)) {
		abort();
	}

	guji_rec_parser_t p;
	memset(&p, 0, sizeof(p));
	p.splices = splices;

	int32_t rlen = 0;
	int32_t splice_count = 0;
	for (int32_t i = 0; i < part_count; i++) {
		if (parts[i].pattern == NULL) {
			rlen = guji_rec_decode_runes(parts[i].text, src, rlen);
			continue;
		}
		/* Parse the spliced Regex value with independent capture numbering and
		   flags. It may already be a compiler-materialized value with reserved
		   private captures, so this parser alone enables hidden-name provenance. */
		int32_t *ssrc = (int32_t *)malloc(sizeof(int32_t) * (strlen(parts[i].pattern) + 1));
		if (!ssrc) {
			abort();
		}
		guji_rec_parser_t sp;
		memset(&sp, 0, sizeof(sp));
		sp.src = ssrc;
		sp.len = guji_rec_decode_runes(parts[i].pattern, ssrc, 0);
		sp.allow_hidden_names =
			guji_regex_value_is_private(parts[i].pattern);

		guji_rec_node_t *sroot = guji_rec_parse_alternate(&sp, sp.flags);
		if (!sp.err && sp.pos < sp.len) {
			guji_rec_set_error(&sp, sp.pos, "unexpected )");
		}
		if (sp.err) {
			/* Unreachable through guji code: Regex.compile or materialization
			   validated the spliced value before it reached this API. */
			p.src = src;
			p.len = rlen;
			guji_rec_parser_teardown(&p);
			free(splices);
			guji_regex_compile_result_t res = guji_rec_error_result(&sp);
			return res;
		}

		guji_rec_node_t *atom = guji_rec_new(&sp, GUJI_REC_SPLICE);
		atom->sub = sroot;
		atom->index = sp.num_cap;
		guji_rec_parser_absorb(&p, &sp);

		splices[splice_count] = atom;
		src[rlen++] = 0xE000 + splice_count;
		splice_count++;
	}
	p.splice_count = splice_count;
	p.src = src;
	p.len = rlen;

	guji_regex_compile_result_t res = guji_rec_finish(&p);
	free(splices);
	return res;
}



static guji_match_t* guji_match_from_regex_match(
		const char* base, guji_regex_match_t rm, int nsubs, const char** names,
		const int32_t* cap_indexes) {
	if (!rm.matched) {
		return NULL;
	}
	guji_match_t* m = (guji_match_t*)guji_alloc(GUJI_KIND_MATCH, 0, sizeof(guji_match_t));
	m->group_names = NULL;
	int len = rm.spans[0][1] - rm.spans[0][0];
	char* text = guji_str_alloc((size_t)len);
	memcpy(text, base + rm.spans[0][0], (size_t)len);
	text[len] = '\0';
	m->text = text;
	m->group_count = nsubs;
	m->groups = (const char**)guji_alloc(GUJI_KIND_ARR_STR, nsubs, sizeof(const char*) * (size_t)(nsubs > 0 ? nsubs : 1));
	for (int i = 0; i < nsubs; i++) {
		int span_index = cap_indexes != NULL ? cap_indexes[i] : i + 1;
		if (span_index >= rm.span_count || rm.spans[span_index][0] < 0) {
			m->groups[i] = NULL;
			continue;
		}
		len = rm.spans[span_index][1] - rm.spans[span_index][0];
		char* g = guji_str_alloc((size_t)len);
		memcpy(g, base + rm.spans[span_index][0], (size_t)len);
		g[len] = '\0';
		m->groups[i] = g;
	}
	if (names != NULL && nsubs > 0) {
		m->group_names = (const char**)guji_alloc(GUJI_KIND_ARR_PTR, nsubs, sizeof(const char*) * (size_t)nsubs);
		for (int i = 0; i < nsubs; i++) {
			m->group_names[i] = names[i] != NULL ? guji_str_from_c(names[i]) : NULL;
		}
	}
	return m;
}

/* guji_match_copy returns a fresh rc==1 deep copy of a Match graph, detached
   from any shared refcount. §17 copy-on-send (RFC-003 §7.3) uses it so an
   Option[Match] sent over a channel never shares a count with the sender's
   per-task heap: text and every capture-group Str are independently copied, the
   groups array is a fresh ARR_STR, and every present capture name is copied
   into an owned counted Str. */
static guji_match_t* guji_match_copy(guji_match_t* src) {
	if (src == NULL) {
		return NULL;
	}
	guji_match_t* m = (guji_match_t*)guji_alloc(GUJI_KIND_MATCH, 0, sizeof(guji_match_t));
	m->text = guji_str_copy(src->text);
	m->group_count = src->group_count;
	int n = src->group_count;
	m->groups = (const char**)guji_alloc(GUJI_KIND_ARR_STR, n, sizeof(const char*) * (size_t)(n > 0 ? n : 1));
	for (int i = 0; i < n; i++) {
		m->groups[i] = (src->groups[i] != NULL) ? guji_str_copy(src->groups[i]) : NULL;
	}
	m->group_names = NULL;
	if (src->group_names != NULL && n > 0) {
		m->group_names = (const char**)guji_alloc(GUJI_KIND_ARR_PTR, n, sizeof(const char*) * (size_t)n);
		for (int i = 0; i < n; i++) {
			m->group_names[i] = src->group_names[i] != NULL ? guji_str_copy(src->group_names[i]) : NULL;
		}
	}
	return m;
}

static void guji_regex_panic_compile(
		const guji_regex_compile_result_t* cr) {
	char msg[GUJI_REC_MSG_CAP + 24];
	snprintf(msg, sizeof(msg), "invalid regex: %s",
		(cr && cr->msg[0]) ? cr->msg : "compile failed");
	guji_panic(msg);
}

static guji_match_t* guji_regex_match_pattern_engine(const char* pattern, const char* subject, int nsubs, const char** names) {
	guji_regex_compile_result_t cr = guji_regex_compile(pattern);
	if (!cr.ok) {
		guji_regex_panic_compile(&cr);
		return NULL;
	}
	guji_regex_match_t rm = guji_regex_find(cr.prog, subject, 0);
	guji_match_t* out = guji_match_from_regex_match(
		subject, rm, nsubs, names, cr.prog->public_cap_indexes);
	guji_regex_program_free(cr.prog);
	return out;
}

static const char* guji_regex_compile_error_message(const guji_regex_compile_result_t* cr) {
	const char* msg = (cr && cr->msg[0]) ? cr->msg : "invalid regex";
	size_t n = strlen(msg);
	char* out = guji_str_alloc(n);
	memcpy(out, msg, n + 1);
	return out;
}

/* guji_regex_compile_fail reports a RUNTIME regex-compilation failure the same
   way the interpreter oracle does: a located, classified
   "<line>:<col>: runtime error: invalid regex: <msg>" on stderr, then exit 1.
   Spliced match/replace lowerings can fail at runtime if a dynamic part cannot
   be compiled; a bare guji_panic ("panic: <msg>") would diverge from the
   interpreter's located runtime error. loc is the regex literal's "line:col". */
static void guji_regex_compile_fail(const char* loc, const guji_regex_compile_result_t* cr) {
	const char* msg = (cr && cr->msg[0]) ? cr->msg : "compile failed";
	fprintf(stderr, "%s: runtime error: invalid regex: %s\n", loc, msg);
	fflush(NULL);
	_exit(1);
}

typedef struct {
	const char* name;
	size_t name_len;
	int32_t index;
} guji_regex_splice_name_t;

static int guji_regex_value_scope(const guji_disp_buf* out, const char* pattern) {
	for (int scope = 0;; scope++) {
		char prefix[40];
		snprintf(prefix, sizeof(prefix), "0H%d_", scope);
		if ((out->p == NULL || strstr(out->p, prefix) == NULL)
				&& strstr(pattern, prefix) == NULL) {
			return scope;
		}
	}
}

static void guji_regex_value_put_hidden_name(
		guji_disp_buf* out, int scope, int32_t index) {
	char name[64];
	snprintf(name, sizeof(name), "0H%d_%d", scope, index);
	guji_disp_puts(out, name);
}

typedef struct {
	int matched;
	size_t next;
	int scoped;
	int verbose;
} guji_regex_splice_flag_info_t;

static int guji_regex_splice_verbose_space(unsigned char c) {
	return c == ' ' || c == '\t' || c == '\n' || c == '\r'
		|| c == '\f' || c == '\v';
}

static size_t guji_regex_splice_comment_end(
		const char* pattern, size_t i) {
	while (pattern[i] != '\0' && pattern[i] != '\n') {
		i++;
	}
	if (pattern[i] == '\n') {
		i++;
	}
	return i;
}

/* Recognize a noncapturing/flag group header beginning at `i`. Besides (?:),
   this tracks x/-x for both inline and scoped flag groups. The input Regex was
   already validated, so malformed headers simply fall back to ordinary special
   group scanning. */
static guji_regex_splice_flag_info_t guji_regex_splice_flag_info(
		const char* pattern, size_t i, int current_verbose) {
	guji_regex_splice_flag_info_t no = {0, 0, 0, current_verbose};
	if (pattern[i] != '(' || pattern[i + 1] != '?') {
		return no;
	}
	size_t j = i + 2;
	int verbose = current_verbose;
	int neg = 0;
	for (;;) {
		unsigned char c = (unsigned char)pattern[j];
		if (verbose && guji_regex_splice_verbose_space(c)) {
			j++;
			continue;
		}
		if (verbose && c == '#') {
			j = guji_regex_splice_comment_end(pattern, j);
			continue;
		}
		switch (c) {
		case 'x':
			verbose = !neg;
			j++;
			continue;
		case 'a':
		case 'i':
		case 'm':
		case 's':
			j++;
			continue;
		case '-':
			neg = 1;
			j++;
			continue;
		case ':': {
			guji_regex_splice_flag_info_t yes = {1, j + 1, 1, verbose};
			return yes;
		}
		case ')': {
			guji_regex_splice_flag_info_t yes = {1, j + 1, 0, verbose};
			return yes;
		}
		default:
			return no;
		}
	}
}

static void guji_regex_splice_mode_push(
		int** modes, int32_t* count, int32_t* cap, int verbose) {
	if (*count == *cap) {
		int32_t nc = *cap ? *cap * 2 : 8;
		int* nm = (int*)realloc(*modes, sizeof(int) * (size_t)nc);
		if (!nm) {
			abort();
		}
		*modes = nm;
		*cap = nc;
	}
	(*modes)[(*count)++] = verbose;
}

/* Append a Regex-valued splice while retaining private capture slots for its
   own backreferences. Reserved 0H... names make those slots distinguishable
   from host captures; each materialization chooses a collision-free scope. */
static void guji_regex_value_append_demoted(
		guji_disp_buf* out, const char* pattern, int scope) {
	int in_class = 0;
	int class_phase = 0; /* 0=start, 1=after leading ^, 2=ordinary member */
	int32_t capture_count = 0;
	int32_t public_capture_count = 0;
	int32_t public_hidden[10] = {0};
	guji_regex_splice_name_t* names = NULL;
	int32_t name_count = 0;
	int32_t name_cap = 0;
	int verbose = 0;
	int* modes = NULL;
	int32_t mode_count = 0;
	int32_t mode_cap = 0;
	for (size_t i = 0; pattern[i] != '\0';) {
		unsigned char c = (unsigned char)pattern[i];
		if (c == '\\') {
			unsigned char next = (unsigned char)pattern[i + 1];
			if (!in_class && next >= '1' && next <= '9') {
				int32_t public_index = next - '0';
				if (public_index <= public_capture_count
						&& public_hidden[public_index] > 0) {
					guji_disp_puts(out, "\\k<");
					guji_regex_value_put_hidden_name(
						out, scope, public_hidden[public_index]);
					guji_disp_puts(out, ">");
					i += 2;
					continue;
				}
			}
			if (!in_class && next == 'k' && pattern[i + 2] == '<') {
				const char* name = pattern + i + 3;
				const char* close = strchr(name, '>');
				if (close != NULL) {
					size_t len = (size_t)(close - name);
					int32_t found = -1;
					for (int32_t j = 0; j < name_count && found < 0; j++) {
						if (names[j].name_len == len
								&& strncmp(names[j].name, name, len) == 0) {
							found = names[j].index;
						}
					}
					if (found > 0) {
						guji_disp_puts(out, "\\k<");
						guji_regex_value_put_hidden_name(out, scope, found);
						guji_disp_puts(out, ">");
						i = (size_t)(close - pattern) + 1;
						continue;
					}
				}
			}
			guji_disp_putn(out, pattern + i, next != '\0' ? 2 : 1);
			i += next != '\0' ? 2 : 1;
			if (in_class) {
				class_phase = 2;
			}
			continue;
		}
		if (in_class) {
			guji_disp_putn(out, pattern + i, 1);
			if (c == ']' && class_phase == 2) {
				in_class = 0;
			} else if (class_phase == 0 && c == '^') {
				class_phase = 1;
			} else {
				class_phase = 2;
			}
			i++;
			continue;
		}
		if (verbose && c == '#') {
			size_t end = guji_regex_splice_comment_end(pattern, i);
			guji_disp_putn(out, pattern + i, end - i);
			i = end;
			continue;
		}
		if (c == '[') {
			guji_disp_putn(out, pattern + i, 1);
			in_class = 1;
			class_phase = 0;
			i++;
			continue;
		}
		if (c == '(' && pattern[i + 1] != '?') {
			guji_regex_splice_mode_push(
				&modes, &mode_count, &mode_cap, verbose);
			capture_count++;
			public_capture_count++;
			if (public_capture_count < 10) {
				public_hidden[public_capture_count] = capture_count;
			}
			guji_disp_puts(out, "(?<");
			guji_regex_value_put_hidden_name(out, scope, capture_count);
			guji_disp_puts(out, ">");
			i++;
			continue;
		}
		if (c == '(' && pattern[i + 1] == '?') {
			guji_regex_splice_flag_info_t flags =
				guji_regex_splice_flag_info(pattern, i, verbose);
			if (flags.matched) {
				guji_disp_putn(out, pattern + i, flags.next - i);
				if (flags.scoped) {
					guji_regex_splice_mode_push(
						&modes, &mode_count, &mode_cap, verbose);
				}
				verbose = flags.verbose;
				i = flags.next;
				continue;
			}
			guji_regex_splice_mode_push(
				&modes, &mode_count, &mode_cap, verbose);
			size_t name_start = 0;
			if (pattern[i + 2] == '<'
					&& pattern[i + 3] != '=' && pattern[i + 3] != '!') {
				name_start = i + 3;
			} else if (pattern[i + 2] == 'P' && pattern[i + 3] == '<') {
				name_start = i + 4;
			}
			if (name_start != 0) {
				const char* close = strchr(pattern + name_start, '>');
				if (close != NULL) {
					int hidden_source = close - (pattern + name_start) >= 2
						&& pattern[name_start] == '0'
						&& pattern[name_start + 1] == 'H';
					capture_count++;
					if (!hidden_source) {
						public_capture_count++;
						if (public_capture_count < 10) {
							public_hidden[public_capture_count] = capture_count;
						}
					}
					if (name_count == name_cap) {
						int32_t nc = name_cap ? name_cap * 2 : 8;
						guji_regex_splice_name_t* nn =
							(guji_regex_splice_name_t*)realloc(
								names, sizeof(*names) * (size_t)nc);
						if (!nn) {
							abort();
						}
						names = nn;
						name_cap = nc;
					}
					names[name_count].name = pattern + name_start;
					names[name_count].name_len =
						(size_t)(close - (pattern + name_start));
					names[name_count].index = capture_count;
					name_count++;
					guji_disp_puts(out, "(?<");
					guji_regex_value_put_hidden_name(out, scope, capture_count);
					guji_disp_puts(out, ">");
					i = (size_t)(close - pattern) + 1;
					continue;
				}
			}
		}
		if (c == ')') {
			guji_disp_putn(out, pattern + i, 1);
			i++;
			verbose = mode_count > 0 ? modes[--mode_count] : 0;
			continue;
		}
		guji_disp_putn(out, pattern + i, 1);
		i++;
	}
	free(names);
	free(modes);
}

/* Materialize the canonical first-class Regex representation for a spliced
   literal. String parts have already been escaped by codegen. Regex parts keep
   private capture slots and are wrapped as one noncapturing atom, matching D.
   The assembled source is validated before returning an owned counted Str. */
static const char* guji_regex_value_from_parts(
		const char* loc, const guji_regex_part_t* parts, int32_t part_count) {
	guji_disp_buf out = {0, 0, 0};
	for (int32_t i = 0; i < part_count; i++) {
		if (parts[i].pattern == NULL) {
			guji_disp_puts(&out, parts[i].text);
		} else {
			guji_regex_compile_result_t part_cr =
				guji_regex_value_is_private(parts[i].pattern)
					? guji_regex_compile_internal(parts[i].pattern)
					: guji_regex_compile(parts[i].pattern);
			if (!part_cr.ok) {
				free(out.p);
				guji_regex_compile_fail(loc, &part_cr);
			}
			guji_regex_program_free(part_cr.prog);
			int scope = guji_regex_value_scope(&out, parts[i].pattern);
			guji_disp_puts(&out, "(?:");
			guji_regex_value_append_demoted(&out, parts[i].pattern, scope);
			guji_disp_puts(&out, ")");
		}
	}
	const char* assembled = out.p != NULL ? out.p : "";
	guji_regex_compile_result_t cr = guji_regex_compile_internal(assembled);
	if (!cr.ok) {
		free(out.p);
		guji_regex_compile_fail(loc, &cr);
	}
	guji_regex_program_free(cr.prog);
	const char* value = guji_disp_finish(&out);
	GUJI_HDR(value)->flags |= GUJI_REGEX_PRIVATE;
	return value;
}

static guji_match_t* guji_regex_match_parts_engine(const char* loc, const guji_regex_part_t* parts, int32_t part_count, const char* subject, int nsubs, const char** names) {
	guji_regex_compile_result_t cr = guji_regex_compile_spliced(parts, part_count);
	if (!cr.ok) {
		guji_regex_compile_fail(loc, &cr);
		return NULL;
	}
	guji_regex_match_t rm = guji_regex_find(cr.prog, subject, 0);
	guji_match_t* out = guji_match_from_regex_match(
		subject, rm, nsubs, names, cr.prog->public_cap_indexes);
	guji_regex_program_free(cr.prog);
	return out;
}

static guji_match_t* guji_regex_match_value_engine(const char* pattern, const char* subject) {
	guji_regex_compile_result_t cr = guji_regex_value_is_private(pattern)
		? guji_regex_compile_internal(pattern)
		: guji_regex_compile(pattern);
	if (!cr.ok) {
		guji_regex_panic_compile(&cr);
		return NULL;
	}
	int nsubs = cr.prog->public_num_cap;
	const char **names = NULL;
	if (nsubs > 0) {
		names = (const char **)malloc(sizeof(const char *) * (size_t)nsubs);
		if (!names) {
			abort();
		}
		for (int i = 0; i < nsubs; i++) {
			int32_t cap_index = cr.prog->public_cap_indexes[i];
			names[i] = cr.prog->cap_names != NULL
				? cr.prog->cap_names[cap_index - 1] : NULL;
		}
	}
	guji_regex_match_t rm = guji_regex_find(cr.prog, subject, 0);
	guji_match_t* out = guji_match_from_regex_match(
		subject, rm, nsubs, names, cr.prog->public_cap_indexes);
	free(names);
	guji_regex_program_free(cr.prog);
	return out;
}

static char* guji_regex_escape_literal(const char* lit) {
	size_t cap = strlen(lit) * 2 + 1;
	char* out = (char*)guji_alloc(GUJI_KIND_STR, 0, cap);
	size_t len = 0;
	for (const unsigned char* p = (const unsigned char*)lit; *p; p++) {
		switch (*p) {
		case '\\': case '.': case '*': case '+': case '?': case '(':
		case ')': case '|': case '[': case ']': case '{': case '}':
		case '^': case '$': case '/':
			if (len + 2 + 1 > cap) {
				cap = (len + 2 + 1) * 2;
				out = guji_str_grow(out, cap);
			}
			out[len++] = '\\';
			out[len++] = (char)*p;
			break;
		default:
			if (len + 1 + 1 > cap) {
				cap = (len + 1 + 1) * 2;
				out = guji_str_grow(out, cap);
			}
			out[len++] = (char)*p;
			break;
		}
	}
	out[len] = '\0';
	GUJI_HDR(out)->count = (int64_t)len;
	return out;
}

/* guji_re_buf_append copies n bytes into a growable header-backed Str buffer
   (allocated with guji_alloc(GUJI_KIND_STR, ...)), keeping it NUL-terminated. */
static void guji_re_buf_append(char** out, size_t* out_len, size_t* cap, const char* src, size_t n) {
	if (*out_len + n + 1 > *cap) {
		*cap = (*out_len + n + 1) * 2;
		*out = guji_str_grow(*out, *cap);
	}
	memcpy(*out + *out_len, src, n);
	*out_len += n;
	(*out)[*out_len] = '\0';
}

/* guji_re_expand_template expands a replace() template against one match's
   absolute byte spans, appending to the output buffer.  Supports $0-$9,
   $<name>, and $$; an unrecognised $ escape emits a literal '$'.  cap_names[i]
   is the name of group i+1 (or NULL); spans/span_count come from the C engine. */
static void guji_re_expand_template(
		char** out, size_t* out_len, size_t* cap, const char* subject,
		const char* tmpl, int nsubs, const int32_t (*spans)[2],
		int32_t span_count, const char** cap_names, const int32_t* cap_indexes) {
	const char* tp = tmpl;
	while (*tp) {
		if (*tp != '$') {
			guji_re_buf_append(out, out_len, cap, tp, 1);
			tp++;
			continue;
		}
		tp++;
		if (*tp == '$') {
			guji_re_buf_append(out, out_len, cap, "$", 1);
			tp++;
			continue;
			}
			if (*tp >= '0' && *tp <= '9') {
				int idx = *tp - '0';
				int32_t span_index = idx == 0 ? 0
					: (cap_indexes != NULL && idx <= nsubs ? cap_indexes[idx - 1] : idx);
				if (idx <= nsubs && span_index < span_count && spans[span_index][0] >= 0) {
					guji_re_buf_append(out, out_len, cap, subject + spans[span_index][0], (size_t)(spans[span_index][1] - spans[span_index][0]));
			}
			tp++;
			continue;
		}
		if (*tp == '<') {
			const char* name_start = ++tp;
			while (*tp && *tp != '>') tp++;
			if (*tp == '>') {
				size_t nlen = (size_t)(tp - name_start);
				int found = -1;
					for (int i = 0; i < nsubs && found < 0; i++) {
						if (cap_names[i] && strlen(cap_names[i]) == nlen && strncmp(cap_names[i], name_start, nlen) == 0) {
							found = i;
						}
					}
					int32_t span_index = found >= 0
						? (cap_indexes != NULL ? cap_indexes[found] : found + 1) : -1;
					if (span_index >= 0 && span_index < span_count && spans[span_index][0] >= 0) {
						guji_re_buf_append(out, out_len, cap, subject + spans[span_index][0], (size_t)(spans[span_index][1] - spans[span_index][0]));
				}
				tp++;
				continue;
			}
			tp = name_start - 1;
		}
		/* unrecognised $ escape -> literal $ */
		guji_re_buf_append(out, out_len, cap, "$", 1);
	}
}

/* guji_regex_replace_engine replaces every non-overlapping match of the raw guji
   pattern in subject with an expansion of tmpl, using the C regex engine.  It
   mirrors the interpreter oracle's FindAll iteration exactly: leftmost-first
   matching, the empty-match advance rule, and the prevEnd dedup that drops an
   empty match adjacent to the previous match end. */
static const char* guji_regex_replace_engine(const char* subject, const char* pattern, int nsubs, const char* tmpl, const char** cap_names) {
	guji_regex_compile_result_t cr = guji_regex_compile(pattern);
	if (!cr.ok) {
		guji_regex_panic_compile(&cr);
		return NULL;
	}
	int32_t slen = (int32_t)GUJI_HDR(subject)->count;
	size_t cap = (size_t)slen + strlen(tmpl) + 1;
	char* out = (char*)guji_alloc(GUJI_KIND_STR, 0, cap);
	out[0] = '\0';
	size_t out_len = 0;

	int32_t prev_end = -1;
	int32_t pos = 0;
	int32_t last = 0;
	while (pos <= slen) {
		guji_regex_match_t m = guji_regex_find(cr.prog, subject, pos);
		if (!m.matched) {
			break;
		}
		int32_t start = m.spans[0][0];
		int32_t end = m.spans[0][1];
		int accept = 1;
		if (start == pos && end == pos) {
			if (start == prev_end) { accept = 0; }
			if (pos < slen) {
				pos = guji_regex_next_start(subject, slen, pos);
			} else {
				pos = slen + 1;
			}
		} else {
			pos = end;
		}
		prev_end = end;
		if (!accept) {
			continue;
		}
		guji_re_buf_append(&out, &out_len, &cap, subject + last, (size_t)(start - last));
		guji_re_expand_template(
			&out, &out_len, &cap, subject, tmpl, nsubs, m.spans,
			m.span_count, cap_names, cr.prog->public_cap_indexes);
		last = end;
	}
	guji_re_buf_append(&out, &out_len, &cap, subject + last, (size_t)(slen - last));
	guji_regex_program_free(cr.prog);
	GUJI_HDR(out)->count = (int64_t)out_len;
	return out;
}

static const char* guji_regex_replace_engine_parts(const char* loc, const char* subject, const guji_regex_part_t* parts, int32_t part_count, int nsubs, const char* tmpl, const char** cap_names) {
	guji_regex_compile_result_t cr = guji_regex_compile_spliced(parts, part_count);
	if (!cr.ok) {
		guji_regex_compile_fail(loc, &cr);
		return NULL;
	}
	int32_t slen = (int32_t)GUJI_HDR(subject)->count;
	size_t cap = (size_t)slen + strlen(tmpl) + 1;
	char* out = (char*)guji_alloc(GUJI_KIND_STR, 0, cap);
	out[0] = '\0';
	size_t out_len = 0;

	int32_t prev_end = -1;
	int32_t pos = 0;
	int32_t last = 0;
	while (pos <= slen) {
		guji_regex_match_t m = guji_regex_find(cr.prog, subject, pos);
		if (!m.matched) {
			break;
		}
		int32_t start = m.spans[0][0];
		int32_t end = m.spans[0][1];
		int accept = 1;
		if (start == pos && end == pos) {
			if (start == prev_end) { accept = 0; }
			if (pos < slen) {
				pos = guji_regex_next_start(subject, slen, pos);
			} else {
				pos = slen + 1;
			}
		} else {
			pos = end;
		}
		prev_end = end;
		if (!accept) {
			continue;
		}
		guji_re_buf_append(&out, &out_len, &cap, subject + last, (size_t)(start - last));
		guji_re_expand_template(
			&out, &out_len, &cap, subject, tmpl, nsubs, m.spans,
			m.span_count, cap_names, cr.prog->public_cap_indexes);
		last = end;
	}
	guji_re_buf_append(&out, &out_len, &cap, subject + last, (size_t)(slen - last));
	guji_regex_program_free(cr.prog);
	GUJI_HDR(out)->count = (int64_t)out_len;
	return out;
}

/* guji_peg_regex matches an anchored regex pattern at pos using the C engine. */
static int64_t guji_peg_regex(const char* pattern, const char* s, int64_t pos) {
	guji_regex_compile_result_t cr = guji_regex_compile(pattern);
	if (!cr.ok) {
		guji_panic(cr.msg[0] ? cr.msg : "invalid regex in grammar");
	}
	guji_regex_match_t m = guji_regex_find_anchored(cr.prog, s, (int32_t)pos);
	int64_t end = -1;
	if (m.matched && m.spans[0][0] == pos) {
		end = m.spans[0][1];
	}
	guji_regex_program_free(cr.prog);
	return end;
}
