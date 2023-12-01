#include "ccadical.h"

#include <assert.h>
#include <inttypes.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

static uint64_t next64 (uint64_t *rng) {
  uint64_t state = *rng;
  state *= 6364136223846793005ul;
  state += 1442695040888963407ul;
  *rng = state;
  return state;
}

static unsigned next32 (uint64_t *rng) { return next64 (rng) >> 32; }

static unsigned pick (uint64_t *rng, unsigned low, unsigned high) {
  assert (low <= high);
  if (low == high)
    return low;
  double delta = high - low;
  unsigned res = low + (delta + 1) * (next32 (rng) / 4294967296.0);
  assert (low <= res);
  assert (res <= high);
  return res;
}

static void hash (uint64_t value, uint64_t *state) {
  *state ^= value;
  (void) next64 (state);
}

static void die (const char *fmt, ...) {
  fputs ("idrup-check: error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static bool quiet;

static void msg (const char *fmt, ...) {
  if (quiet)
    return;
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static bool parse_uint64_t (const char *str, uint64_t *res_ptr) {
  const uint64_t MAX = ~(uint64_t) 0;
  uint64_t res = 0;
  unsigned char ch;
  for (const char *p = str; (ch = *p); p++) {
    if (MAX / 10 < res)
      return false;
    res *= 10;
    uint64_t digit = (ch - '0');
    if (MAX - digit < res)
      return false;
    res += digit;
  }
  *res_ptr = res;
  return true;
}

static volatile bool caught;
static volatile bool completed;
static void (*saved) (int);

static volatile uint64_t fuzzed;

static void statistics () {
  printf ("fuzzed %" PRIu64 " interactions\n", fuzzed);
  fflush (stdout);
}

static void catch (int sig) {
  if (caught)
    return;
  caught = true;
  signal (SIGINT, saved);
  if (!completed) {
    if (!quiet)
      fputc ('\n', stdout);
    completed = true;
  }
  if (!quiet) {
    printf ("caught signal %d\n", sig);
    statistics ();
  }
  raise (sig);
}

static FILE *write_to_file (const char *path) {
  FILE *file = fopen (path, "w");
  if (!file)
    die ("could not open and write to '%s'", path);
  return file;
}

static void fuzz (uint64_t rng) {
  unsigned vars = pick (&rng, 10, 100);
  double ratio = pick (&rng, 350, 450);
  unsigned clauses = vars * ratio / 100.0;
  unsigned calls = pick (&rng, 1, 10);
  if (!quiet)
    printf (" %u %u %u", vars, clauses, calls), fflush (stdout);
  FILE *icnf = write_to_file ("/tmp/idrup-fuzz.icnf");
  CCaDiCaL *solver = ccadical_init ();
  unsigned subset = (clauses + calls - 1) / calls;
  if (!quiet)
    fputs (" [", stdout), fflush (stdout);
  for (unsigned call = 0; call != calls; call++) {
    unsigned part = pick (&rng, (subset + 1) / 2, (3 * subset + 1) / 2);
    if (!quiet)
      printf (" %u", part), fflush (stdout);
    for (unsigned i = 0; i != part; i++) {
      unsigned k;
      if (!pick (&rng, 0, clauses / 2))
        k = 1;
      else if (!pick (&rng, 0, clauses / 10))
        k = 2;
      else if (!pick (&rng, 0, clauses / 10))
        k = 4;
      else if (!pick (&rng, 0, clauses / 10))
        k = 5;
      else if (!pick (&rng, 0, clauses / 10))
        k = 6;
      assert (k <= vars);
      int clause[k];
      for (unsigned j = 0; j != k; j++) {
      RESTART:
        int idx = pick (&rng, 1, vars);
        for (unsigned l = 0; l != j; l++)
          if (abs (clause[l]) == idx)
            goto RESTART;
        int sign = pick (&rng, 0, 1) ? -1 : 1;
        int lit = sign * idx;
        clause[j] = lit;
      }
    }
  }
  fclose (icnf);
  if (!quiet)
    fputs (" ]", stdout), fflush (stdout);
  ccadical_release (solver);
}

int main (int argc, char **argv) {
  bool seeded = false, repeat = false;
  uint64_t rng = 0, repetitions = 0;
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp (arg, "-h")) {
      printf ("usage: idrup-fuzz [-h|-q] [ <seed> [ <repetitions> ]]\n");
      exit (0);
    } else if (!strcmp (arg, "-q"))
      quiet = true;
    else if (arg[0] == '-')
      die ("invalid command line option '%s' (try '-h')", arg);
    else if (repeat)
      die ("too many arguments (try '-h')");
    else if (!seeded) {
      if (!parse_uint64_t (arg, &rng))
        die ("invalid seed argument '%s'", arg);
      seeded = true;
    } else if (!parse_uint64_t (arg, &repetitions))
      die ("invalid repetitions argument '%s'", arg);
    else
      repeat = true;
  }
  msg ("IDrup Fuzzer Version 0.0");
  msg ("using %s", ccadical_signature ());
  if (seeded)
    msg ("user specified seed %" PRIu64, rng);
  else {
    hash (getpid (), &rng);
    hash (clock (), &rng);
    msg ("random seed %" PRIu64, rng);
  }
  bool terminal = isatty (1);
  saved = signal (SIGINT, catch);
  do {
    fuzzed++;
    if (!quiet) {
      if (terminal)
        fputs ("\033[K\033[1G", stdout);
      printf ("%020" PRIu64 " %" PRIu64, rng, fuzzed);
      fflush (stdout);
    }
    completed = false;
    fuzz (rng);
    if (!quiet && !terminal) {
      putc ('\n', stdout);
      fflush (stdout);
    }
    completed = true;
    (void) next64 (&rng);
  } while (!seeded || (repeat && fuzzed < repetitions));
  if (!quiet) {
    if (terminal)
      fputs ("\033[1G\033[K", stdout);
    statistics ();
  }
  return 0;
}
