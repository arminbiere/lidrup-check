// clang-format off
static const char * usage =
"usage: idrup-fuzz [ <option> ... ] [ <number> [ <number> ] ]\n"
"\n"
"where '<option>' is one of the following two\n"
"\n"
" -h                print this command line option summary\n"
" -q                be quiet and do not print any messages\n"
"\n"
"and '<number> one of these\n"
"\n"
" <seed>            random number generator seed\n"
" [-]<repetitions>  number of repetitions (default infinity)\n"
"\n"
"If one number is given then its sign determines whether it is specifying\n"
"the overall fuzzing seed or the number of repetitions.  With two numbers\n"
"given a positive one specifies the seed and a negative one the number\n"
"of repetitions.  If both are positive the second specifies the number\n"
"of repetitions.  Two negative numbers are invalid.  All numbers are\n"
"assumed to be decimal encoded and parsed as 64-bit number in the range\n"
"0 to 2^64-1 (18446744073709551615).  If the number of repetitions is\n"
"unspecified fuzzing runs without limit.  Without a seed specified\n"
"a random seed is generated based the process identifier and\n"
"the processor clock cycles.\n"
;

// clang-format on

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
  if (!*str)
    return false;
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
static volatile uint64_t repetitions;
static bool limited = false;

static double average (double a, double b) { return b ? a / b : 0; }
static double percent (double a, double b) { return average (100 * a, b); }

static void statistics () {
  if (limited)
    printf ("fuzzed %" PRIu64 " interactions %.0f%%\n", fuzzed,
            percent (fuzzed, repetitions));
  else
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
  double ratio = pick (&rng, 3500, 4500);
  unsigned clauses = vars * ratio / 1000.0;
  unsigned calls = pick (&rng, 1, 10);
  if (!quiet)
    printf (" %u %u %u", vars, clauses, calls), fflush (stdout);
  FILE *icnf = write_to_file ("/tmp/idrup-fuzz.icnf");
  CCaDiCaL *solver = ccadical_init ();
  fputs ("p icnf\n", icnf);
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
      else
        k = 3;
      assert (k <= vars);
      int clause[k];
      fputc ('i', icnf);
      for (unsigned j = 0; j != k; j++) {
      RESTART:
        int idx = pick (&rng, 1, vars);
        for (unsigned l = 0; l != j; l++)
          if (abs (clause[l]) == idx)
            goto RESTART;
        int sign = pick (&rng, 0, 1) ? -1 : 1;
        int lit = sign * idx;
        clause[j] = lit;
        ccadical_add (solver, lit);
        fprintf (icnf, " %d", lit);
      }
      ccadical_add (solver, 0);
      fputs (" 0\n", icnf);
    }
    fputs ("q 0\n", icnf), fflush (icnf);
    int res = ccadical_solve (solver);
    if (res == 10) {
      fputs ("s SATISFIABLE\n", icnf), fflush (icnf);
      fputs ("v 0\n", icnf), fflush (icnf);
    } else {
      assert (res == 20);
      fputs ("s UNSATISFIABLE\n", icnf), fflush (icnf);
      fputs ("j 0\n", icnf), fflush (icnf);
    }
  }
  fclose (icnf);
  if (!quiet)
    fputs (" ]", stdout), fflush (stdout);
  ccadical_release (solver);
}

int main (int argc, char **argv) {
  bool seeded = false;
  uint64_t rng = 0;
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp (arg, "-h")) {
      fputs (usage, stdout);
      exit (0);
    } else if (!strcmp (arg, "-q"))
      quiet = true;
    else if (arg[0] == '-') {
      uint64_t tmp;
      if (!parse_uint64_t (arg + 1, &tmp))
        die ("invalid command line option '%s' (try '-h')", arg);
      if (limited)
        die ("multiple repetition limits '%" PRIu64 "' and '%" PRIu64 "'",
             repetitions, tmp);
      repetitions = tmp;
      limited = true;
    } else if (seeded && limited)
      die ("too many arguments (try '-h')");
    else {
      uint64_t tmp;
      if (!parse_uint64_t (arg, &tmp))
        die ("invalid number '%s'", arg);
      if (seeded) {
        repetitions = tmp;
        limited = true;
      } else {
        rng = tmp;
        seeded = true;
      }
    }
  }
  msg ("IDrup Fuzzer Version 0.0");
  msg ("using %s", ccadical_signature ());
  if (seeded)
    msg ("specified seed %" PRIu64, rng);
  else {
    hash (getpid (), &rng);
    hash (clock (), &rng);
    msg ("random seed %" PRIu64, rng);
  }
  if (limited)
    msg ("running %" PRIu64 " repetitions", repetitions);
  else
    msg ("unlimited fuzzing");
  bool terminal = isatty (1);
  saved = signal (SIGINT, catch);
  for (;;) {
    if (limited && fuzzed == repetitions)
      break;
    fuzzed++;
    if (!quiet) {
      if (terminal)
        fputs ("\033[K\033[1G", stdout);
      printf ("%020" PRIu64 " %" PRIu64, rng, fuzzed);
      if (limited)
        printf (" %.0f%%", percent (fuzzed, repetitions));
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
    if (!limited && seeded)
      break;
  }
  if (!quiet) {
    if (terminal)
      fputs ("\033[1G\033[K", stdout);
    statistics ();
  }
  return 0;
}
