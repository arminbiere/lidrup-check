// clang-format off

static const char * usage =

"usage: idrup-fuzz [ <option> ... ] [ <number> [ <number> ] ]\n"
"\n"
"where '<option>' is one of the following two\n"
"\n"
"  -h | --help          print this command line option summary\n"
"  -q | --quiet         be quiet and do not print any messages\n"
"  -n | --no-terminal   assume 'stdout' is not connected to a terminal\n"
"  -c | --continue      continue going even if test failed\n"
"  -s | --small         restrict range of variables\n"
"\n"
"and '<number> one of these\n"
"\n"
"  <seed>               random number generator seed\n"
"  [-]<repetitions>     number of repetitions (default infinity)\n"
"\n"

"If one number is given then its sign determines whether it is specifying\n"
"the overall fuzzing seed or the number of repetitions.  With two numbers\n"
"given a positive one specifies the seed and a negative one the number\n"
"of repetitions.  If both are positive the second specifies the number\n"
"of repetitions.  Two negative numbers are invalid.  With a single and\n"
"positive number only the test for that seed is run.\n"

"\n"

"All numbers are assumed to be decimally encoded and parsed as 64-bit\n"
"number in the range 0 to 2^64-1 (18446744073709551615).  If the number\n"
"of repetitions is unspecified fuzzing runs without limit.  Without a seed\n"
"specified a random seed is generated based on the process identifier and\n"
"the processor clock cycles.  If a seed is specified but no repetition\n"
"then only a single fuzzing test with this seed is run.  This is useful\n"
"to rerun and debug a failing fuzzing run.\n"

;

// clang-format on

/*------------------------------------------------------------------------*/

// Depends on 'CaDiCaL' but goes through its C interface for simplicity.

#include "ccadical.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <ctype.h>
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

/*------------------------------------------------------------------------*/

// Global configuration options.

static bool quiet;      // Force not output if enabled.
static bool small;      // Only use a small set of variables.
static bool terminal;   // Erase printed lines if connected to a terminal.
static bool keep_going; // Keep going even if 'idrup-check' failed.

static volatile uint64_t repetitions; // Number of repetitions if specified.
static bool limited = false;          // If repetitions limits this is set.

/*------------------------------------------------------------------------*/

static volatile bool completed;  // Line completed.
static volatile uint64_t fuzzed; // Number of fuzzed tests.

/*------------------------------------------------------------------------*/

// The picked number of variables for one test case.

static unsigned vars;

/*------------------------------------------------------------------------*/

// Random number generation functions.

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

/*------------------------------------------------------------------------*/

// Functions to print messages and errors and handle terminal output.

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

static void die (const char *, ...) __attribute__ ((format (printf, 1, 2)));

static void die (const char *fmt, ...) {
  fputs ("idrup-fuzz: error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void clear_to_end_of_line (void) {
  if (!quiet && terminal)
    fputs ("\033[K", stdout);
}

static void erase_line (void) {
  if (!quiet && terminal)
    fputs ("\033[1G", stdout);
}

/*------------------------------------------------------------------------*/

static bool parse_uint64_t (const char *str, uint64_t *res_ptr) {
  if (!*str)
    return false;
  const uint64_t MAX = ~(uint64_t) 0;
  uint64_t res = 0;
  unsigned char ch;
  for (const char *p = str; (ch = *p); p++) {
    if (!isdigit (ch))
      return false;
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

/*------------------------------------------------------------------------*/

static int min (int a, int b) { return a < b ? a : b; }
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

/*------------------------------------------------------------------------*/

// Signal handling (we only catch interrupts, i.e., '<control-c>').

static volatile bool caught; // Signal handled.

static void (*saved) (int); // Saved signal handler.

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

/*------------------------------------------------------------------------*/

// Open and write to the given file.

static FILE *write_to_file (const char *path) {
  FILE *file = fopen (path, "w");
  if (!file)
    die ("could not open and write to '%s'", path);
  return file;
}

// Generate a vector of literals (without repeated variables).

static void pick_literals (uint64_t *rng, int *lits, unsigned size) {
  for (unsigned j = 0; j != size; j++) {
  RESTART:;
    int idx = pick (rng, 1, vars);
    for (unsigned l = 0; l != j; l++)
      if (abs (lits[l]) == idx)
        goto RESTART;
    int sign = pick (rng, 0, 1) ? -1 : 1;
    int lit = sign * idx;
    lits[j] = lit;
  }
}

// The function which runs one fuzzing test.

static void fuzz (uint64_t seed) {
  uint64_t rng = seed;
  vars = pick (&rng, 3, small ? 10 : 100);
  double ratio = pick (&rng, 3500, 4500);
  unsigned clauses = vars * ratio / 1000.0;
  unsigned calls = pick (&rng, 1, small ? 3 : 10);
  if (!quiet)
    printf (" %u %u %u", vars, clauses, calls), fflush (stdout);
#define PATH "/tmp/idrup-fuzz"
#define ICNF PATH ".icnf"
#define IDRUP PATH ".idrup"
  FILE *icnf = write_to_file (ICNF);
  FILE *idrup = write_to_file (IDRUP);
  CCaDiCaL *solver = ccadical_init ();
  ccadical_set_option (solver, "idrup", 1);
  ccadical_set_option (solver, "binary", 0);
  ccadical_trace_proof (solver, idrup, IDRUP);
  fputs ("p icnf\n", icnf);
  unsigned subset = (clauses + calls - 1) / calls;
  if (!quiet)
    fputs (" [", stdout), fflush (stdout);
  for (unsigned call = 0; call != calls; call++) {
    unsigned part = pick (&rng, (subset + 1) / 2, (3 * subset + 1) / 2);
    if (!quiet)
      printf (" %u", part), fflush (stdout);
    unsigned p = pick (&rng, 0, 4 * part);
    for (unsigned i = 0; i != part; i++) {
      unsigned k;
      if (!pick (&rng, 0, clauses / 2))
        k = 1;
      else if (!pick (&rng, 0, clauses / 10))
        k = 2;
      else if (vars >= 4 && !pick (&rng, 0, clauses / 10))
        k = 4;
      else if (vars >= 5 && !pick (&rng, 0, clauses / 10))
        k = 5;
      else if (vars >= 6 && !pick (&rng, 0, clauses / 10))
        k = 6;
      else
        k = 3;
      assert (k <= vars);
      int clause[k];
      pick_literals (&rng, clause, k);
      fputc ('i', icnf);
      for (unsigned j = 0; j != k; j++) {
        int lit = clause[j];
        ccadical_add (solver, lit);
        fprintf (icnf, " %d", lit);
      }
      ccadical_add (solver, 0);
      fputs (" 0\n", icnf);
      if (i == p) {
        if (!quiet)
          fputc ('p', stdout), fflush (stdout);
        fputs ("q 0\n", icnf), fflush (icnf);
        int res = ccadical_simplify (solver);
        if (res) {
          fputs ("s UNSATISFIABLE\n", icnf), fflush (icnf);
          ccadical_conclude (solver);
          assert (res == 20);
          if (!quiet)
            fputs ("*u", stdout), fflush (stdout);
          fputs ("u 0\n", icnf), fflush (icnf);
          goto CONTINUE_WITH_OUTER_LOOP;
        } else
          fputs ("s UNKNOWN\n", icnf), fflush (icnf);
      }
    }
    {
      unsigned k = pick (&rng, 0, min (10, vars));
      if (!quiet)
        printf ("/%u", k), fflush (stdout);
      int query[k];
      fputc ('q', icnf);
      pick_literals (&rng, query, k);
      for (unsigned j = 0; j != k; j++) {
        int lit = query[j];
        ccadical_assume (solver, lit);
        fprintf (icnf, " %d", lit);
      }
      fputs (" 0\n", icnf), fflush (icnf);
      int res = ccadical_solve (solver);
      bool concluded = false;
      if (res == 10) {
        if (!quiet)
          fputc ('s', stdout), fflush (stdout);
        fputs ("s SATISFIABLE\n", icnf), fflush (icnf);
        if (pick (&rng, 0, 1)) {
          fputc ('v', icnf);
          unsigned values = pick (&rng, 0, vars);
          for (unsigned i = 0; i != values; i++) {
            int lit = pick (&rng, 1, vars);
            int val = ccadical_val (solver, lit);
            fprintf (icnf, " %d", val == lit ? lit : -lit);
            concluded = true;
          }
        } else {
          fputc ('m', icnf);
          int scrambled[vars];
          for (int i = 0; i != vars; i++) {
	    int idx = i + 1;
            if (i) {
	      int pos = pick (&rng, 0, i + 1);
	      if (pos < i) {
		int tmp = scrambled[pos];
		scrambled[pos] = idx;
		idx = tmp;
	      }
            }
	    scrambled[i] = idx;
          }
          for (int i = 0; i != vars; i++) {
	    int lit = scrambled[i];
            int val = ccadical_val (solver, lit);
            fprintf (icnf, " %d", val == lit ? lit : -lit);
            concluded = true;
          }
        }
      } else {
        if (!quiet)
          fputc ('u', stdout), fflush (stdout);
        assert (res == 20);
        fputs ("s UNSATISFIABLE\n", icnf), fflush (icnf);
        fputc ('u', icnf); // TODO what about 'f'?
        for (unsigned j = 0; j != k; j++) {
          int lit = query[j];
          if (ccadical_failed (solver, lit))
            fprintf (icnf, " %d", lit);
          concluded = true;
        }
      }
      fputs (" 0\n", icnf);
      fflush (icnf);
      (void) concluded;
      // if (!concluded) // TODO could make this optional.
      ccadical_conclude (solver);
    }
  CONTINUE_WITH_OUTER_LOOP:;
  }
  ccadical_release (solver);
  fclose (icnf);
  fclose (idrup);
  if (!quiet)
    fputs (" ]", stdout), fflush (stdout);

#define ERR PATH ".err"
#define LOG PATH ".log"
#define REDIRECT " 1>" LOG " 2>" ERR
#define CMD "./idrup-check -v " ICNF " " IDRUP

  int res = system (CMD REDIRECT);
  if (res) {
    if (quiet)
      printf ("%020" PRIu64 " %" PRIu64 " %u %u %u FAILED\n", seed, fuzzed,
              vars, clauses, calls);
    else {
      clear_to_end_of_line ();
      fputs (" FAILED\n", stdout);
    }
    if (!keep_going) {
      fflush (stdout);
      fputs (CMD, stdout);
      fputc ('\n', stdout);
      fflush (stdout);
      {
        FILE *file = fopen (LOG, "r");
        int ch;
        while ((ch = getc (file)) != EOF)
          fputc (ch, stdout);
        fclose (file);
        fflush (stdout);
      }
      {
        FILE *file = fopen (ERR, "r");
        int ch;
        while ((ch = getc (file)) != EOF)
          fputc (ch, stderr);
        fclose (file);
        fflush (stderr);
      }
      exit (1);
    }
  } else if (!quiet)
    fputs (" checked", stdout), fflush (stdout);
}

/*------------------------------------------------------------------------*/

int main (int argc, char **argv) {
  bool seeded = false;
  terminal = isatty (1);
  uint64_t rng = 0;
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp (arg, "-h") || !strcmp (arg, "--help")) {
      fputs (usage, stdout);
      exit (0);
    } else if (!strcmp (arg, "-q") || !strcmp (arg, "--quiet"))
      quiet = true;
    else if (!strcmp (arg, "-n") || !strcmp (arg, "--no-terminal"))
      terminal = false;
    else if (!strcmp (arg, "-c") || !strcmp (arg, "--continue"))
      keep_going = true;
    else if (!strcmp (arg, "-s") || !strcmp (arg, "--small"))
      small = true;
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
  msg ("IDRUP Fuzzer Version 0.0");
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
  saved = signal (SIGINT, catch);
  for (;;) {
    if (limited && fuzzed == repetitions)
      break;
    fuzzed++;
    if (!quiet) {
      printf ("%020" PRIu64 " %" PRIu64, rng, fuzzed);
      clear_to_end_of_line ();
      if (limited)
        printf (" %.0f%%", percent (fuzzed, repetitions));
      fflush (stdout);
    }
    completed = false;
    fuzz (rng);
    erase_line ();
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
    erase_line ();
    clear_to_end_of_line ();
    statistics ();
  }
  return 0;
}
