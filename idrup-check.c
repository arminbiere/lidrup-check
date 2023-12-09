// clang-format off

static const char * idrup_check_usage =
"usage: idrup-check [ <option> ... ] <icnf> <idrup>\n"
"\n"
"where '<option>' is one of the following options:\n"
"\n"
"  -h | --help     print command line option summary\n"
"  -q | --quiet    do not print any message beside errors\n"
"  -v | --verbose  print more verbose message too\n"
#ifndef NDEBUG
"  -l | --logging  enable very verbose logging\n"
#endif
"  --version       print version and exit\n"
"\n"

"Exactly two files are read. The first '<icnf>' is an incremental CNF file\n"
"augmented with all interactions between the user and the SAT solver.\n"
"Thus the letter 'i' is overloaded and means both 'incremental' and\n"
"'interactions'. The second '<idrup>' file is meant to be a super-set of\n"
"the interactions file but additionally has all the low level proof steps.\n"

"\n"

"The checker makes sure the interactions match the proof and all proof\n"
"steps are justified. This is only the case though for the default\n"
"'strict' and the 'pedantic' mode.  Checking is less strict in 'relaxed'\n"
"mode where conclusion missing in the proof will be skipped.  Still the\n"
"exit code will only be zero if all checks go through and thus the\n"
"interactions are all checked.\n"

"\n"
"These modes can can be set explicitly as follows:\n"
"\n"
"  --strict    strict mode (requires 'm' and 'u' proof lines only)\n"
"  --relaxed   relaxed mode (missing 'm' and 'u' proof lines ignored)\n"
"  --pedantic  pedantic mode (requires conclusion lines in both files\n"
"\n"

"The default mode is strict checking which still allows headers to be\n"
"skipped and interaction conclusions ('v', 'm', 'f' and 'u' lines) to be\n"
"optional in the interaction file while corresponding proof conclusions\n"
"('m' and 'u' lines) being mandatory in the proof file.\n"

;

// clang-format on

/*------------------------------------------------------------------------*/

#include "idrup-build.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

// We support three different modes.

enum {
  strict = 0,
  relaxed = -1,
  pedantic = 1,
};

// Generic integer stack for literals.

struct ints {
  int *begin, *end, *allocated;
};

// We are reading interleaved from two files in parallel.

struct file {
  FILE *file;
  const char *name;      // Actual path to this file.
  size_t lines;          // Proof lines read from this file.
  size_t lineno;         // Line number of lines parsed so far.
  size_t charno;         // Number of bytes parsed.
  size_t start_of_line;  // Line number of current proof line.
  size_t end_buffer;     // End of remaining characters in buffer.
  size_t size_buffer;    // Current position (bytes parsed) in buffer.
  bool end_of_file;      // Buffer 'read-char' detected end-of-file.
  char last_char;        // Last char used to bump 'lineno'.
  char buffer[1u << 20]; // The actual buffer (1MB).
};

struct clause {
#ifndef NDEBUG
  size_t id;
  size_t lineno;
#endif
  bool input;
  bool weakened;
  bool tautological;
  unsigned size;
  int lits[];
};

struct clauses {
  struct clause **begin, **end, **allocated;
};

/*------------------------------------------------------------------------*/

// Global options.

static int verbosity = 0;

static int mode = strict;

/*------------------------------------------------------------------------*/

// Section of parsing state.

// Array of two files statically allocated and initialized.

static struct file files[2] = {{.lineno = 1}, {.lineno = 1}};

// The actual interaction and proof files point into this array.

static struct file *interactions = files + 0;
static struct file *proof = files + 1;

// The current file from which we read (is set with 'set_file').

static struct file *file;

// The other file different from 'file' (so 'other_file == interactions'
// if 'file == proof' and vice versa).

static struct file *other_file;

/*------------------------------------------------------------------------*/

static bool querying;
static double start_time;

/*------------------------------------------------------------------------*/

static struct ints line;  // Current line of integers parsed.
static struct ints saved; // Saved line for checking.
static struct ints query; // Saved query for checking.

// When saving a line the type and start of the line is saved too.

static size_t start_of_query;
static size_t start_of_saved;
static int saved_type;

// Constant strings parsed in 'p' and 's' lines.

static const char *const SATISFIABLE = "SATISFIABLE";
static const char *const UNSATISFIABLE = "UNSATISFIABLE";
static const char *const UNKNOWN = "UNKNOWN";
static const char *const IDRUP = "idrup";
static const char *const ICNF = "icnf";

// The parser saves such strings here.

static const char *string;

/*------------------------------------------------------------------------*/

// Checker state.

static unsigned level; // Decision level.

static int max_var;      // Maximum variable index imported.
static size_t allocated; // Allocated variables.

static bool *imported;           // Variable index imported?
static unsigned *levels;         // Decision level of assigned variables.
static struct clauses *matrix;   // Mapping literals to watcher stacks.
static struct clauses *inactive; // Inactive weakened clauses.
static signed char *values;      // Assignment of literal: -1, 0, or 1.
static bool *marks;              // Marks of literals.

// Default preallocated trail.

static struct {
  int *begin, *end;
  int *units, *propagate;
} trail;

// Maps decision level to trail heights.

static bool inconsistent; // Empty clause derived.

// Need to store empty clauses on a separate stack as they are not watched.

static struct clauses empty_clauses;

// Input clauses are never actually deleted as they are needed for checking
// that models satisfy them.

static struct clauses input_clauses;

/*------------------------------------------------------------------------*/

// Global statistics

static struct {
  size_t added;
  size_t conclusions;
  size_t cores;
  size_t decisions;
  size_t deleted;
  size_t inputs;
  size_t imported;
  size_t lemmas;
  size_t models;
  size_t propagations;
  size_t queries;
  size_t restored;
  size_t weakened;
} statistics;

/*------------------------------------------------------------------------*/

// Buffers for printing literals when logging ('debug_literal').

#ifndef NDEBUG

#define capacity_debug_buffer 2
#define debug_buffer_line_size 64

static char debug_buffer[capacity_debug_buffer][debug_buffer_line_size];
static size_t next_debug_buffer_position;

#endif

/*------------------------------------------------------------------------*/

// Generic stack implementation (similar to 'std::vector').

#define BEGIN(S) (S).begin
#define END(S) (S).end
#define ALLOCATED(S) (S).allocated

#define SIZE(S) ((size_t) (END (S) - BEGIN (S)))
#define CAPACITY(S) ((size_t) (ALLOCATED (S) - BEGIN (S)))

#define CLEAR(S) (END (S) = BEGIN (S))
#define EMPTY(S) (END (S) == BEGIN (S))
#define FULL(S) (END (S) == ALLOCATED (S))

#define INIT(S) (BEGIN (S) = END (S) = ALLOCATED (S) = 0)
#define RELEASE(S) (free (BEGIN (S)), INIT (S))

#define ENLARGE(S) \
  do { \
    size_t OLD_SIZE = SIZE (S); \
    size_t OLD_CAPACITY = CAPACITY (S); \
    size_t NEW_CAPACITY = OLD_CAPACITY ? 2 * OLD_CAPACITY : 1; \
    size_t NEW_BYTES = NEW_CAPACITY * sizeof *BEGIN (S); \
    if (!(BEGIN (S) = realloc (BEGIN (S), NEW_BYTES))) \
      out_of_memory ("reallocating %zu bytes", NEW_BYTES); \
    END (S) = BEGIN (S) + OLD_SIZE; \
    ALLOCATED (S) = BEGIN (S) + NEW_CAPACITY; \
  } while (0)

#define PUSH(S, E) \
  do { \
    if (FULL (S)) \
      ENLARGE (S); \
    *END (S)++ = (E); \
  } while (0)

#define REMOVE(TYPE, S, E) \
  do { \
    TYPE *BEGIN = (S).begin; \
    TYPE *END = (S).end; \
    TYPE *Q = BEGIN; \
    TYPE *P = Q; \
    for (;;) { \
      assert (P != END); \
      TYPE TMP = *P++; \
      if (TMP == (E)) \
        break; \
      *Q++ = TMP; \
    } \
    assert (Q + 1 == P); \
    while (P != END) \
      *Q++ = *P++; \
    (S).end = Q; \
    if (EMPTY (S)) \
      RELEASE (S); \
  } while (0)

#define PEEK(S, POS) (assert ((POS) < SIZE (S)), (S).begin[POS])

#define all_elements(TYPE, E, S) \
  TYPE E, *E##_PTR = BEGIN (S), *const E##_END = END (S); \
  E##_PTR != E##_END && (E = *E##_PTR, 1); \
  ++E##_PTR

#define all_pointers(TYPE, E, S) \
  TYPE *E, **E##_PTR = BEGIN (S), **const E##_END = END (S); \
  E##_PTR != E##_END && (E = *E##_PTR, 1); \
  ++E##_PTR

#define COPY(TYPE, DST, SRC) \
  do { \
    CLEAR (DST); \
    for (all_elements (TYPE, E, SRC)) \
      PUSH (DST, E); \
  } while (0)

/*------------------------------------------------------------------------*/

// Iterator for the literals of clauses.

#define begin_literals(C) ((C)->lits)

#define end_literals(C) (begin_literals (C) + (C)->size)

#define all_literals(LIT, C) \
  int LIT, *P_##LIT = begin_literals (C), *END_##LIT = end_literals (C); \
  P_##LIT != END_##LIT && (LIT = *P_##LIT, true); \
  P_##LIT++

/*------------------------------------------------------------------------*/

// Function to print messages and errors with nice formatting prototypes to
// produce compiler warnings if arguments do not match format.

static void die (const char *, ...) __attribute__ ((format (printf, 1, 2)));

static void die (const char *fmt, ...) {
  fputs ("idrup-check: error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void out_of_memory (const char *, ...)
    __attribute__ ((format (printf, 1, 2)));

static void fatal_error (const char *fmt, ...) {
  fputs ("idrup-check: fatal internal error: ", stderr);
  if (file)
    fprintf (stderr, "at line %zu in '%s': ", file->start_of_line,
             file->name);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void out_of_memory (const char *fmt, ...) {
  fputs ("idrup-check: error: out-of-memory ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void message (const char *, ...)
    __attribute__ ((format (printf, 1, 2)));

static void message (const char *fmt, ...) {
  if (verbosity < 0)
    return;
  fputs ("c ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

#define verbose(...) \
  do { \
    if (verbosity >= 1) \
      message (__VA_ARGS__); \
  } while (0)

static void parse_error (const char *, ...)
    __attribute__ ((format (printf, 1, 2)));

static void parse_error (const char *fmt, ...) {
  assert (file);
  fprintf (stderr, "idrup-check: parse error: at line %zu in '%s': ",
           file->start_of_line, file->name);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void check_error (const char *, ...)
    __attribute__ ((format (printf, 1, 2)));

static void check_error (const char *fmt, ...) {
  assert (file);
  fprintf (stderr,
           "idrup-check: error: at line %zu in '%s': ", file->start_of_line,
           file->name);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void line_error (int type, const char *, ...)
    __attribute__ ((format (printf, 2, 3)));

static void line_error (int type, const char *fmt, ...) {
  assert (file);
  fflush (stdout);
  fprintf (stderr,
           "idrup-check: error: at line %zu in '%s': ", file->start_of_line,
           file->name);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fputc (type, stderr);
  for (all_elements (int, lit, line))
    fprintf (stderr, " %d", lit);
  fputs (" 0\n", stderr);
  exit (1);
}

#ifndef NDEBUG

static void debug (const char *, ...)
    __attribute__ ((format (printf, 1, 2)));

static void debug (const char *fmt, ...) {
  if (verbosity != INT_MAX)
    return;
  printf ("c DEBUG %u ", level);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void debug_print_parsed_line (int type) {
  if (verbosity < INT_MAX)
    return;
  assert (file);
  printf ("c DEBUG %u parsed line %zu in '%s': ", level, file->lineno,
          file->name);
  switch (type) {
  case 'p':
    fputs ("p ", stdout);
    assert (string);
    fputs (string, stdout);
    break;
  case 's':
    fputs ("s ", stdout);
    assert (string);
    fputs (string, stdout);
    break;
  case 0:
    fputs ("<end-of-file>", stdout);
    break;
  default:
    fputc (type, stdout);
    for (const int *p = line.begin; p != line.end; p++)
      printf (" %d", *p);
    fputs (" 0", stdout);
    break;
  }
  fputc ('\n', stdout);
  fflush (stdout);
}

static char *next_debug_buffer (void) {
  char *res = debug_buffer[next_debug_buffer_position++];
  if (next_debug_buffer_position == capacity_debug_buffer)
    next_debug_buffer_position = 0;
  return res;
}

static const char *debug_literal (int lit) {
  char *res = next_debug_buffer ();
  int value = values[lit];
  if (value)
    snprintf (res, debug_buffer_line_size, "%d@%u=%d", lit,
              levels[abs (lit)], value);
  else
    snprintf (res, debug_buffer_line_size, "%d", lit);
  return res;
}

static void debug_clause (struct clause *, const char *, ...)
    __attribute__ ((format (printf, 2, 3)));

static void debug_clause (struct clause *c, const char *fmt, ...) {
  if (verbosity < INT_MAX)
    return;
  printf ("c DEBUG %u ", level);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (c->tautological)
    fputs (" tautological", stdout);
  if (c->weakened)
    fputs (" weakened", stdout);
  if (c->input)
    fputs (" input", stdout);
  else
    fputs (" lemma", stdout);
  printf (" size %u line %zu clause[%zu]", c->size, c->lineno, c->id);
  for (all_literals (lit, c))
    printf (" %s", debug_literal (lit));
  fputc ('\n', stdout);
  fflush (stdout);
}

#else
#define debug(...) \
  do { \
  } while (false)
#define debug_clause(...) \
  do { \
  } while (false)
#endif

/*------------------------------------------------------------------------*/

// Resource usage code.

#include <sys/resource.h>
#include <sys/time.h>
#include <unistd.h>

static double process_time (void) {
  struct rusage u;
  double res;
  (void) getrusage (RUSAGE_SELF, &u);
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

static double start_of_wall_clock_time;

static double absolute_wall_clock_time (void) {
  struct timeval tv;
  if (gettimeofday (&tv, 0))
    return 0;
  return 1e-6 * tv.tv_usec + tv.tv_sec;
}

static double wall_clock_time () {
  return absolute_wall_clock_time () - start_of_wall_clock_time;
}

static size_t maximum_resident_set_size (void) {
  struct rusage u;
  (void) getrusage (RUSAGE_SELF, &u);
  return ((size_t) u.ru_maxrss) << 10;
}

static double mega_bytes (void) {
  return maximum_resident_set_size () / (double) (1 << 20);
}

static double average (double a, double b) { return b ? a / b : 0; }

static double percent (double a, double b) { return average (100 * a, b); }

/*------------------------------------------------------------------------*/

// Increasing allocated size of variables and importing a variable.

static void increase_allocated (int idx) {
  assert ((unsigned) idx >= allocated);
  size_t new_allocated = allocated ? 2 * allocated : 1;
  while ((unsigned) idx >= new_allocated)
    new_allocated *= 2;
  debug ("reallocating from %zu to %zu variables", allocated,
         new_allocated);
  {
    struct clauses *new_matrix =
        calloc (2 * new_allocated, sizeof *new_matrix);
    if (!new_matrix)
      out_of_memory ("reallocating matrix of size %zu", new_allocated);
    new_matrix += new_allocated;
    if (max_var)
      for (int lit = -max_var; lit <= max_var; lit++)
        new_matrix[lit] = matrix[lit];
    matrix -= allocated;
    free (matrix);
    matrix = new_matrix;
  }
  {
    struct clauses *new_inactive =
        calloc (2 * new_allocated, sizeof *new_inactive);
    if (!new_inactive)
      out_of_memory ("reallocating inactive matrix of size %zu",
                     new_allocated);
    new_inactive += new_allocated;
    if (max_var)
      for (int lit = -max_var; lit <= max_var; lit++)
        new_inactive[lit] = inactive[lit];
    inactive -= allocated;
    free (inactive);
    inactive = new_inactive;
  }
  {
    signed char *new_values =
        calloc (2 * new_allocated, sizeof *new_values);
    if (!new_values)
      out_of_memory ("reallocating values of size %zu", new_allocated);
    new_values += new_allocated;
    if (max_var)
      for (int lit = -max_var; lit <= max_var; lit++)
        new_values[lit] = values[lit];
    values -= allocated;
    free (values);
    values = new_values;
  }
  {
    bool *new_marks = calloc (2 * new_allocated, sizeof *new_marks);
    if (!new_marks)
      out_of_memory ("reallocating marks of size %zu", new_allocated);
    new_marks += new_allocated;
    if (max_var)
      for (int lit = -max_var; lit <= max_var; lit++)
        new_marks[lit] = marks[lit];
    marks -= allocated;
    free (marks);
    marks = new_marks;
  }
  {
    unsigned *new_levels = calloc (new_allocated, sizeof *new_levels);
    if (!new_levels)
      out_of_memory ("reallocating levels of size %zu", new_allocated);
    for (int idx = 1; idx <= max_var; idx++)
      new_levels[idx] = levels[idx];
    free (levels);
    levels = new_levels;
  }
  {
    bool *new_imported = calloc (new_allocated, sizeof *new_imported);
    if (!new_imported)
      out_of_memory ("reallocating imported of size %zu", new_allocated);
    for (int idx = 1; idx <= max_var; idx++)
      new_imported[idx] = imported[idx];
    free (imported);
    imported = new_imported;
  }
  {
    size_t size = SIZE (trail);
    size_t units = trail.units - trail.begin;
    size_t propagated = trail.propagate - trail.begin;
    trail.begin =
        realloc (trail.begin, new_allocated * sizeof *trail.begin);
    if (!trail.begin)
      out_of_memory ("reallocating trail of size %zu", new_allocated);
    trail.end = trail.begin + size;
    trail.units = trail.begin + units;
    trail.propagate = trail.begin + propagated;
    allocated = new_allocated;
  }
}

static void increase_max_var (int idx) {
  assert (max_var < idx);
  debug ("new maximum variable index %d", idx);
  if ((unsigned) idx >= allocated)
    increase_allocated (idx);
  max_var = idx;
}

static void import_variable (int idx) {
  assert (idx);
  if (max_var < idx) {
    if (idx == INT_MAX)
      parse_error ("can not handle INT_MAX variables");
    if (idx > max_var)
      increase_max_var (idx);
  }
  if (!imported[idx]) {
    imported[idx] = true;
    statistics.imported++;
    debug ("imported variable %d", idx);
  }
}

/*------------------------------------------------------------------------*/

// Section on low-level line reading and partial parsing.

static inline void set_file (struct file *new_file) {
  assert (new_file);
  assert (new_file->file);
  file = new_file;
  other_file = file == interactions ? proof : interactions;
  assert (other_file);
  assert (other_file->file);
}

static int read_char (void) {
  assert (file);
  assert (file->file);
  if (file->size_buffer == file->end_buffer) {
    if (file->end_of_file)
      return EOF;
    file->end_buffer =
        fread (file->buffer, 1, sizeof file->buffer, file->file);
    if (!file->end_buffer) {
      file->end_of_file = 1;
      return EOF;
    }
    file->size_buffer = 0;
  }
  assert (file->size_buffer < file->end_buffer);
  return file->buffer[file->size_buffer++];
}

static int next_char (void) {
  int res = read_char ();
  if (res == '\r') {
    res = read_char ();
    if (res != '\n')
      parse_error ("expected new-line after carriage return");
  }
  if (file->last_char == '\n')
    file->lineno++;
  file->last_char = res;
  if (res != EOF)
    file->charno++;
  return res;
}

static int ISDIGIT (int ch) { return '0' <= ch && ch <= '9'; }

static int next_line_without_printing (char default_type) {

  int ch;
  for (;;) {
    ch = next_char ();
    file->start_of_line = file->lineno;
    if (ch == 'c') {
      while ((ch = next_char ()) != '\n')
        if (ch == EOF)
          parse_error ("end-of-file in comment");
#ifndef NDEBUG
      if (verbosity == INT_MAX)
        message ("skipped line %zu in '%s': c...", file->start_of_line,
                 file->name);
#endif
    } else if (ch == EOF) {
#ifndef NDEBUG
      if (verbosity == INT_MAX)
        message ("parsed end-of-file in '%s' after %zu lines", file->name,
                 file->lineno);
#endif
      return 0;
    } else if (ch == '\n') {
      message ("skipping empty line %zu in '%s'", file->start_of_line,
               file->name);
    } else
      break;
  }

  int actual_type = 0;
  string = 0;

  CLEAR (line);
  file->lines++;

  if (ch == 'p') {
    if (next_char () != ' ')
    INVALID_HEADER_LINE:
      parse_error ("invalid 'p' header line");

    if (next_char () != 'i')
      goto INVALID_HEADER_LINE;

    // TODO parse 'p cnf <vars> <clauses>' header too.

    ch = next_char ();
    if (ch == 'c' && next_char () == 'n' && next_char () == 'f')
      string = ICNF;
    else if (ch == 'd' && next_char () == 'r' && next_char () == 'u' &&
             next_char () == 'p')
      string = IDRUP;
    else
      goto INVALID_HEADER_LINE;

    if (next_char () != '\n')
      parse_error ("expected new line after 'p icnf' header");

    return 'p';
  }

  if ('a' <= ch && ch <= 'z') {
    actual_type = ch;
    if ((ch = next_char ()) != ' ')
      parse_error ("expected space after '%c'", actual_type);
    ch = next_char ();
  } else if (!default_type) {
    if (isprint (ch))
      parse_error ("unexpected character '%c'", ch);
    else
      parse_error ("unexpected character code %02x", (int) ch);
  } else
    actual_type = default_type;
  if (actual_type == 's') {
    if (ch == 'S') {
      for (const char *p = "ATISFIABLE"; *p; p++)
        if (*p != next_char ())
        INVALID_STATUS_LINE:
          parse_error ("invalid status line");
      if (next_char () != '\n')
      EXPECTED_NEW_LINE_AFTER_STATUS:
        parse_error ("expected new-line after status");
      string = SATISFIABLE;
    } else if (ch == 'U') {
      if (next_char () != 'N')
        goto INVALID_STATUS_LINE;
      ch = next_char ();
      if (ch == 'S') {
        for (const char *p = "ATISFIABLE"; *p; p++)
          if (*p != next_char ())
            goto INVALID_STATUS_LINE;
        if (next_char () != '\n')
          goto EXPECTED_NEW_LINE_AFTER_STATUS;
        string = UNSATISFIABLE;
      } else if (ch == 'K') {
        for (const char *p = "NOWN"; *p; p++)
          if (*p != next_char ())
            goto INVALID_STATUS_LINE;
        if (next_char () != '\n')
          goto EXPECTED_NEW_LINE_AFTER_STATUS;
        string = UNKNOWN;
      } else
        goto INVALID_STATUS_LINE;
    } else
      goto INVALID_STATUS_LINE;
    return 's';
  }
  for (;;) {
    int sign;
    if (ch == '-') {
      ch = next_char ();
      if (ch == '0')
        parse_error ("expected non-zero digit after '-'");
      if (!ISDIGIT (ch))
        parse_error ("expected digit after '-'");
      sign = -1;
    } else {
      if (!ISDIGIT (ch))
        parse_error ("expected digit or '-'");
      sign = 1;
    }
    int idx = ch - '0';
    while (ISDIGIT (ch = next_char ())) {
      if (!idx)
        parse_error ("invalid leading '0' digit");
      if (INT_MAX / 10 < idx)
        parse_error ("index too large");
      idx *= 10;
      int digit = ch - '0';
      if (INT_MAX - digit < idx)
        parse_error ("index too large");
      idx += digit;
    }
    if (idx)
      import_variable (idx);
    assert (idx != INT_MIN);
    int lit = sign * idx;
    if (ch != ' ' && ch != '\n')
      parse_error ("expected space or new-line after '%d'", lit);
    if (ch == '\n') { // TODO what about continued lines (e.g., 'v' lines)?
      if (lit)
        parse_error ("expected zero literal '0' before new-line");
      return actual_type;
    }
    if (!lit)
      parse_error ("zero literal '0' without new-line");
    PUSH (line, lit);
    assert (ch == ' ');
    ch = next_char ();
  }
}

static inline int next_line (char default_type) {
  int type = next_line_without_printing (default_type);
#ifndef NDEBUG
  debug_print_parsed_line (type);
#endif
  return type;
}

static void unexpected_line (int type, const char *expected) {
  if (type)
    parse_error ("unexpected '%c' line (expected %s line)", type, expected);
  else
    parse_error ("unexpected end-of-file (expected %s line)", expected);
}

/*------------------------------------------------------------------------*/

// Update trail and control stack including the decision level.

static void push_trail (int lit) {
  assert (trail.end < trail.begin + max_var);
  *trail.end++ = lit;
}

static void pop_trail (int *new_end) {
  assert (trail.begin <= new_end);
  assert (new_end <= trail.end);
  debug ("truncating trail from %zu to %zu literals",
         trail.end - trail.begin, new_end - trail.begin);
  trail.end = new_end;
  assert (trail.units <= new_end);
  if (new_end < trail.propagate) {
    debug ("truncating propagated from %zu to %zu literals",
           trail.propagate - trail.begin, new_end - trail.begin);
    trail.propagate = new_end;
  }
}

/*------------------------------------------------------------------------*/

// We have four contexts in which we assign variables.

static void assign_root_level_unit (int lit) {
  assert (!level);
  assert (trail.end == trail.units);
  push_trail (lit);
  trail.units++;
  values[-lit] = -1;
  values[lit] = 1;
  int idx = abs (lit);
  levels[idx] = 0;
  debug ("assign %s as root-level unit", debug_literal (lit));
}

static void assign_forced (int lit, struct clause *c) {
  assert (level || trail.end == trail.units);
  push_trail (lit);
  if (!level)
    trail.units++;
  values[-lit] = -1;
  values[lit] = 1;
  int idx = abs (lit);
  levels[idx] = level;
  debug_clause (c, "assign %s %sforced by", debug_literal (lit),
                level ? "as root-level unit " : "");
  (void) c;
}

static void assign_decision (int lit) {
  push_trail (lit);
  values[-lit] = -1;
  values[lit] = 1;
  int idx = abs (lit);
  levels[idx] = level;
  statistics.decisions++;
  level++;
  debug ("assign %s as decision", debug_literal (lit));
}

/*------------------------------------------------------------------------*/

// Variables are only unassigned during backtracking.

static void backtrack (void) {
  debug ("backtracking to root decision level");
  int *new_trail_end = trail.units;
  int *p = trail.end;
  while (p != new_trail_end) {
    int lit = *--p;
    assert (values[lit] > 0);
    assert (values[-lit] < 0);
    values[lit] = values[-lit] = 0;
#ifndef NDEBUG
    int idx = abs (lit);
    unsigned lit_level = levels[idx];
    unsigned saved_level = level;
    level = lit_level;
    debug ("unassign %s", debug_literal (lit));
    level = saved_level;
#endif
  }
  level = 0;
  pop_trail (new_trail_end);
}

/*------------------------------------------------------------------------*/

#ifndef NDEBUG

// This function used in assertion checking determines whether the literal
// is valid in principle and fits the allocated size but does not require
// that its variable has been imported before.

bool valid_literal (int lit) {
  return lit && lit != INT_MIN && abs (lit) <= max_var;
}

#endif

/*------------------------------------------------------------------------*/

// We use a literal map which maps literals to true to mark literals in
// 'line', 'saved' and 'query' which allows us to check set equivalence
// ('match_literals') or subset properties ('subset_literals').

static void mark_literal (int lit) {
  // debug ("marking %s", debug_literal (lit));
  assert (valid_literal (lit));
  marks[lit] = true;
}

static void unmark_literal (int lit) {
  // debug ("unmarking %s", debug_literal (lit));
  assert (valid_literal (lit));
  marks[lit] = false;
}

static void mark_literals (struct ints *lits) {
  for (all_elements (int, lit, *lits))
    mark_literal (lit);
}

static void unmark_literals (struct ints *lits) {
  for (all_elements (int, lit, *lits))
    unmark_literal (lit);
}

static void mark_line (void) { mark_literals (&line); }
static void unmark_line (void) { unmark_literals (&line); }

static void mark_query (void) { mark_literals (&query); }
static void unmark_query (void) { unmark_literals (&query); }

static bool subset_literals (struct ints *a, struct ints *b) {
  mark_literals (b);
  bool res = true;
  for (all_elements (int, lit, *a)) {
    assert (valid_literal (lit));
    if (!marks[lit]) {
      res = false;
      break;
    }
  }
  unmark_literals (b);
  return res;
}

static bool match_literals (struct ints *a, struct ints *b) {
  return subset_literals (a, b) && subset_literals (b, a);
}

/*------------------------------------------------------------------------*/

// Clause allocation and deallocation.

static bool line_is_tautological () {
  bool res = false;
  for (all_elements (int, lit, line)) {
    assert (valid_literal (lit));
    if (!marks[lit]) {
      if (marks[-lit])
	res = true;
      marks[lit] = true;
    }
  }
  unmark_line ();
  return res;
}

static struct clause *allocate_clause (bool input) {
  size_t size = SIZE (line);
  if (size > UINT_MAX)
    parse_error ("maximum clause size exhausted");
  size_t lits_bytes = size * sizeof (int);
  size_t all_bytes = sizeof (struct clause) + lits_bytes;
  struct clause *c = malloc (all_bytes);
  if (!c)
    out_of_memory ("allocating clause of size %zu", size);
  assert (file);
  statistics.added++;
#ifndef NDEBUG
  c->id = statistics.added;
  c->lineno = file->start_of_line;
#endif
  c->size = size;
  c->weakened = false;
  c->input = input;
  c->tautological = line_is_tautological ();
  memcpy (c->lits, line.begin, lits_bytes);
  debug_clause (c, "allocate");
  if (input)
    PUSH (input_clauses, c);
  return c;
}

static void free_clause (struct clause *c) {
  debug ("freeing clause at %p", (void *) c);
  debug_clause (c, "free");
  free (c);
}

/*------------------------------------------------------------------------*/

// Watching and connecting literals is implementing here.

static void watch_literal (int lit, struct clause *c) {
  debug_clause (c, "watching %s in", debug_literal (lit));
  PUSH (matrix[lit], c);
}

static void unwatch_literal (int lit, struct clause *c) {
  debug_clause (c, "unwatching %s in", debug_literal (lit));
  struct clauses *watches = matrix + lit;
  REMOVE (struct clause *, *watches, c);
}

static void unwatch_clause (struct clause *c) {
  if (c->size) {
    unwatch_literal (c->lits[0], c);
    if (c->size > 1)
      unwatch_literal (c->lits[1], c);
  } else
    REMOVE (struct clause *, empty_clauses, c);
}

static void connect_literal (int lit, struct clause *c) {
  debug_clause (c, "connecting %d to", lit);
  PUSH (inactive[lit], c);
}

static void disconnect_literal (int lit, struct clause *c) {
  debug_clause (c, "disconnecting %d from", lit);
  REMOVE (struct clause *, inactive[lit], c);
}

static int move_best_watch_to_front (int *lits, const int *const end) {
  assert (!level);
  int watch = *lits;
  signed char watch_value = values[watch];
  if (watch_value < 0)
    for (int *p = lits + 1; p != end; p++) {
      int lit = *p;
      signed char lit_value = values[lit];
      if (lit_value < 0)
        continue;
      *lits = lit;
      *p = watch;
      return lit;
    }
  return watch;
}

static void watch_clause (struct clause *c) {
  assert (!level);
  if (!c->size)
    PUSH (empty_clauses, c);
  else if (c->size == 1)
    watch_literal (c->lits[0], c);
  else {
    int *lits = c->lits;
    const int *const end = lits + c->size;
    int lit0 = move_best_watch_to_front (lits, end);
    int lit1 = move_best_watch_to_front (lits + 1, end);
    debug ("first watch %s", debug_literal (lit0));
    debug ("second watch %s", debug_literal (lit1));
    watch_literal (lit0, c);
    watch_literal (lit1, c);
  }
}

static int simplify_clause (struct clause *c, bool *satisfied,
                            bool *falsified) {
  int unit = 0;
  for (all_literals (lit, c)) {
    signed char value = values[lit];
    int idx = abs (lit);
    if (value && levels[idx])
      value = 0;
    if (value > 0) {
      *satisfied = true;
      return 0;
    } else if (!value) {
      if (unit)
        return 0;
      unit = lit;
    }
  }
  if (!unit)
    *falsified = true;
  return unit;
}

static void add_clause (bool input) {
  struct clause *c = allocate_clause (input);
  watch_clause (c);
  bool satisfied = false, falsified = false;
  int unit = simplify_clause (c, &satisfied, &falsified);
  if (satisfied)
    debug_clause (c, "added root-level satisfied");
  else if (unit) {
    if (level) {
      debug_clause (c, "added root-level unit");
      backtrack ();
    }
    assign_root_level_unit (unit);
  } else if (!falsified)
    debug_clause (c, "added");
  else if (c->size) {
    debug_clause (c, "all literals falsified in added");
    if (!inconsistent) {
      if (input)
        message ("inconsistent input clause");
      else
        message ("derived inconsistent clause");
      inconsistent = true;
    }
  } else {
    debug_clause (c, "added empty");
    if (!inconsistent) {
      if (input)
        message ("empty input clause");
      else
        message ("derived empty clause");
      inconsistent = true;
    }
  }
}

/*------------------------------------------------------------------------*/

static bool propagate (void) {
  assert (!inconsistent);
  assert (trail.propagate <= trail.end);
  bool res = true;
  while (res && trail.propagate != trail.end) {
    int lit = *trail.propagate++;
    debug ("propagating %s", debug_literal (lit));
    statistics.propagations++;
    int not_lit = -lit;
    struct clauses *watches = matrix + not_lit;
    struct clause **watches_end = watches->end;
    struct clause **q = watches->begin, **p = q;
    while (res && p != watches_end) {
      struct clause *c = *q++ = *p++;
      debug_clause (c, "visiting");
      int *lits = c->lits;
      int other_watch = lits[0] ^ lits[1] ^ not_lit;
      signed char other_watch_value = values[other_watch];
      if (other_watch_value > 0) {
        debug ("satisfied by %s", debug_literal (other_watch));
        continue;
      }
      int *r = lits + 2, *end_lits = lits + c->size;
      signed char replacement_value = -1;
      int replacement = 0;
      while (r != end_lits) {
        replacement = *r;
        replacement_value = values[replacement];
        if (replacement_value >= 0)
          break;
        r++;
      }
      if (replacement_value >= 0) {
        debug_clause (c, "unwatching %s in", debug_literal (not_lit));
        *r = not_lit;
        lits[0] = other_watch;
        lits[1] = replacement;
        watch_literal (replacement, c);
        q--;
      } else if (!other_watch_value) {
        assert (!c->weakened);
        assign_forced (other_watch, c);
      } else {
        assert (other_watch_value < 0);
        assert (!c->weakened);
        debug_clause (c, "conflict");
        res = false;
      }
    }
    while (p != watches_end)
      *q++ = *p++;
    watches->end = q;
  }
  return res;
}

/*------------------------------------------------------------------------*/

// A new query starts a new context with potentially new assumptions and
// thus we have to backtrack to the root-level and reset the failed flag.

static void reset_checker (void) {
  if (!inconsistent && level) {
    debug ("resetting assignment");
    backtrack ();
  } else
    debug ("no need to reset assignment");
}

static void save_query (void) {
  debug ("saving query");
  COPY (int, query, line);
  start_of_query = file->start_of_line;
  statistics.queries++;
  reset_checker ();
}

/*------------------------------------------------------------------------*/

// This is the essential checking function which checks that added lemmas
// are indeed reverse unit propagation (RUP) implied and unsatisfiable
// cores are indeed unsatisfiable.  The first case requires the literals
// in the current line to be assumed negatively while the second case
// requires them to be assigned positively, as determined by the last
// 'sign' argument. The other arguments are for context sensitive logging
// and error messages.

static void check_implied (int type, const char *type_str, int sign) {

  assert (sign == 1 || sign == -1);

  if (inconsistent) {
    debug ("skipping %s implication check as formula already inconsistent",
           type_str);
    return;
  }

  assert (!level);

  // First propagate all new units on decision level zero.

  if (trail.propagate < trail.units && !propagate ()) {
    message ("root-level unit propagation yields conflict");
    inconsistent = true;
    return;
  }

  // After all root-level units have been propagated assume all literals
  // in the line as decision if 'sign=1' or their negation if 'sign=-1'.

  debug ("checking %s line is implied", type_str);
  for (all_elements (int, lit, line)) {
    lit *= sign;
    signed char value = values[lit];
    if (value > 0) {
      debug ("assumption %s already satisfied", debug_literal (lit));
      continue;
    }
    if (value < 0) {
      debug ("assumption %s already falsified", debug_literal (lit));
      goto IMPLICATION_CHECK_SUCCEEDED;
    }
    assign_decision (lit);
  }

  if (propagate ())
    line_error (type, "%s implication check failed:", type_str);

IMPLICATION_CHECK_SUCCEEDED:

  if (level)
    backtrack ();

  debug ("%s implication check succeeded", type_str);
  (void) type_str;
}

/*------------------------------------------------------------------------*/

// Clauses are found by marking the literals in the line and then
// traversing the watches of them to find all clause of the same size with
// all literals marked and active (not weakened).  It might be possible to
// speed up this part with hash table, which on the other hand would
// require more space.

static struct clause *find_empty_clause (bool weakened) {
  assert (EMPTY (line));
  for (all_pointers (struct clause, c, empty_clauses)) {
    if (c->weakened != weakened)
      continue;
    debug_clause (c, "found_matching");
    return c;
  }
  debug ("no matching clause found");
  return 0;
}

static struct clause *find_non_empty_clause (bool weakened) {
  size_t size = SIZE (line);
  assert (size);
  mark_line ();
  for (all_elements (int, lit, line)) {
    struct clauses *watches = (weakened ? inactive : matrix) + lit;
    for (all_pointers (struct clause, c, *watches)) {
      if (c->size != size)
        continue;
      if (c->weakened != weakened)
        continue;
      for (all_literals (other, c))
        if (!marks[other])
          goto CONTINUE_WITH_NEXT_CLAUSE;
      unmark_line ();
      debug_clause (c, "found matching");
      return c;
    CONTINUE_WITH_NEXT_CLAUSE:;
    }
  }
  unmark_line ();
  debug ("no matching clause found");
  return 0;
}

static struct clause *find_clause (bool weakened) {
  if (EMPTY (line))
    return find_empty_clause (weakened);
  else
    return find_non_empty_clause (weakened);
}

static struct clause *find_active_clause (void) {
  debug ("finding active clause");
  return find_clause (false);
}

static struct clause *find_weakened_clause (void) {
  debug ("finding weakened clause");
  return find_clause (true);
}

static int
move_least_occurring_inactive_literal_to_front (struct clause *c) {
  assert (c->size);
  int *lits = c->lits;
  int res = lits[0];
  size_t res_occurrences = SIZE (inactive[res]);
  const int *const end = lits + c->size;
  for (int *p = lits + 1; p != end; p++) {
    int other = *p;
    size_t other_occurrences = SIZE (inactive[other]);
    if (other_occurrences >= res_occurrences)
      continue;
    *p = res;
    res = other;
    res_occurrences = other_occurrences;
  }
  lits[0] = res;
  assert (res);
  debug ("literal %s occurs only %zu times", debug_literal (res),
         res_occurrences);
  return res;
}

/*------------------------------------------------------------------------*/

// This section has all the low-level checks.

static void delete_clause (struct clause *c) {
  assert (!c->weakened);
  debug ("deleting clause");
  unwatch_clause (c);
  if (c->input)
    debug_clause (c, "but not freeing");
  else
    free_clause (c);
  statistics.deleted++;
}

static void weaken_clause (struct clause *c) {
  assert (!c->weakened);
  debug_clause (c, "weakening");
  unwatch_clause (c);
  c->weakened = true;
  if (c->size) {
    int lit = move_least_occurring_inactive_literal_to_front (c);
    connect_literal (lit, c);
  }
  statistics.weakened++;
}

static void restore_clause (struct clause *c) {
  assert (!level);
  assert (c->weakened);
  debug_clause (c, "restoring");
  if (c->size) {
    int *lits = begin_literals (c);
    disconnect_literal (*lits, c);
    watch_clause (c);
    int lit0 = lits[0];
    int val0 = values[lit0];
    if (c->size > 1) {
      if (val0 <= 0) {
        int lit1 = lits[1];
        int val1 = values[lit1];
        if (val1 < 0 || (!val1 && val0 < 0)) {
          if (trail.begin < trail.propagate) {
            assert (!level);
            debug ("forcing repropagation after restoring clause");
            trail.propagate = trail.begin;
          }
        }
      }
    } else
      assert (val0 > 0);
  }
  c->weakened = false;
  statistics.restored++;
}

// Check that there are no clashing literals (both positive and negative
// occurrence of a variable) in the current line.  This is a mandatory
// check for conclusions, i.e., for both 'm' models and 'u' core lines.

static void check_line_consistency (int type) {
  for (all_elements (int, lit, line)) {
    assert (valid_literal (lit));
    if (marks[-lit])
      check_error ("inconsistent '%c' line with both %d and %d", type, -lit,
                   lit);
    marks[lit] = true;
  }
  unmark_line ();
  debug ("line consists of consistent literals");
}

// Check that there are no literals in the current line which clash with
// one literal in the saved line (a variable is not allowed to occur
// positively in one and negatively in the other line).

static void check_line_consistent_with_saved (int type) {
  mark_line ();
  for (all_elements (int, lit, saved)) {
    assert (valid_literal (lit));
    if (marks[-lit])
      check_error ("inconsistent '%d' line on %d with line %zu in '%s'",
                   type, lit, start_of_saved, other_file->name);
  }
  unmark_line ();
  debug ("current and saved line have consistent literals");
}

static void check_satisfied_clause (int type, struct clause *c) {
  if (c->tautological)
    return;
  for (all_literals (lit, c)) {
    assert (valid_literal (lit));
    if (marks[lit])
      return;
  }
  fflush (stdout);
  fprintf (stderr,
           "idrup-check: error: model at line %zu in '%s' "
           "does not satisfy %s clause:\n",
           file->start_of_line, file->name,
           c->input ? "input" : "derived"); // Defensive at this point!!!
  fputc (c->input ? 'i' : 'l', stderr);
  for (all_literals (lit, c))
    fprintf (stderr, " %d", lit);
  fputs (" 0\n", stderr);
  exit (1);
}

// A given model line is checked to satisfy all input clauses.

static void check_line_satisfies_input_clauses (int type) {
  debug ("checking model");
  mark_line ();
  for (all_pointers (struct clause, c, input_clauses))
    check_satisfied_clause (type, c);
  unmark_line ();
  debug ("model checked");
}

// The given core line leads to unsatisfiability through propagation.

static void check_line_propagation_yields_conflict (int type) {
  debug ("checking unsatisfiable core implied");
  check_implied (type, "unsatisfiable core", 1);
  debug ("unsatisfiable core implied");
}

// Check that the given literal has been imported before.

static void check_literal_imported (int type, int lit) {
  int idx = abs (lit);
  if (idx > max_var || !imported[idx])
    line_error (type, "literal %d unused", lit);
}

static void check_literals_imported (int type) {
  debug ("checking literals imported");
  for (all_elements (int, lit, line))
    check_literal_imported (type, lit);
}

/*------------------------------------------------------------------------*/

static void start_query (void) {
  if (querying)
    fatal_error ("query already started");
  if (verbosity > 0)
    start_time = wall_clock_time ();
  querying = true;
}

static void conclude_query (int res) {
  if (!querying)
    fatal_error ("query already concluded");
  if (verbosity > 0) {
    double current = wall_clock_time ();
    double delta = current - start_time;
    verbose ("concluded query %zu with %d after %.2f seconds "
             "in %.2f seconds",
             statistics.queries, res, current, delta);
  }
  querying = false;
}

/*------------------------------------------------------------------------*/

// Merged checking options for each line.

static void add_input_clause (int type) {
  add_clause (true);
  statistics.inputs++;
  (void) type;
}

static void check_then_add_lemma (int type) {
  check_implied (type, "lemma", -1);
  add_clause (false);
  statistics.lemmas++;
}

static void find_then_delete_clause (int type) {
  check_literals_imported (type);
  struct clause *c = find_active_clause ();
  if (c)
    delete_clause (c);
  else
    line_error (type, "could not find clause");
}

static void find_then_restore_clause (int type) {
  check_literals_imported (type);
  struct clause *c = find_weakened_clause ();
  if (c)
    restore_clause (c);
  else
    line_error (type, "could not find and restore weakened clause");
}

static void find_then_weaken_clause (int type) {
  check_literals_imported (type);
  struct clause *c = find_active_clause ();
  if (c)
    weaken_clause (c);
  else
    line_error (type, "could not find and weaken clause");
}

static bool is_learn_delete_restore_or_weaken (int type) {
  return type == 'l' || type == 'd' || type == 'r' || type == 'w';
}

static void learn_delete_restore_or_weaken (int type) {
  if (type == 'l')
    check_then_add_lemma (type);
  else if (type == 'd')
    find_then_delete_clause (type);
  else if (type == 'r')
    find_then_restore_clause (type);
  else {
    assert (type == 'w');
    find_then_weaken_clause (type);
  }
}

static void match_saved (int type, const char *type_str) {
  debug ("matching saved line");
  if (!match_literals (&line, &saved))
    check_error ("%s '%c' line does not match '%c' line %zu in '%s'",
                 type_str, type, saved_type, start_of_saved,
                 other_file->name);
  debug ("saved line matched");
}

static void save_line (int type) {
  debug ("saving '%c' line", type);
  COPY (int, saved, line);
  start_of_saved = file->start_of_line;
  saved_type = type;
}

static bool match_header (const char *expected) {
  if (file->lines > 1)
    return false;
  assert (file->lines == 1);
  if (string != expected)
    parse_error ("expected '%s' header and not 'p %s' "
                 "(input files swapped?)",
                 expected, string);
  verbose ("found '%s' header in '%s'", string, file->name);
  return true;
}

static void check_line_satisfies_query (int type) {
  mark_line ();
  for (all_elements (int, lit, query))
    if (!marks[lit])
      check_error ("model does not satisfy query literal %d "
                   "at line %zu in '%s'",
                   lit, start_of_query, interactions->name);
  unmark_line ();
  (void) type;
  debug ("line literals satisfy query");
}

static void conclude_satisfiable_query_with_model (int type) {
  debug ("concluding satisfiable query");
  assert (!inconsistent);
  check_line_consistency (type);
  check_line_satisfies_query (type);
  check_line_satisfies_input_clauses (type);
  check_line_consistent_with_saved (type);
  statistics.conclusions++;
  statistics.models++;
  assert (!level);
  debug ("satisfiable query concluded");
  conclude_query (10);
}

static void check_core_subset_of_query (int type) {
  mark_query ();
  for (all_elements (int, lit, line))
    if (!marks[lit])
      check_error ("core literal %d not in query at line %zu in '%s'", lit,
                   start_of_query, interactions->name);
  unmark_query ();
  debug ("core subset of query");
  (void) type;
}

static void check_line_variables_subset_of_query (int type) {
  mark_query ();
  for (all_elements (int, lit, line))
    if (!marks[lit] && !marks[-lit])
      check_error ("literal %d nor %d in query at line %zu in '%s'", lit,
                   -lit, start_of_query, interactions->name);
  unmark_query ();
  debug ("line variables subset of query");
  (void) type;
}

static void check_saved_failed_literals_match_core (int type) {
  for (all_elements (int, lit, line))
    marks[lit] = true;
  for (all_elements (int, lit, saved))
    if (marks[-lit])
      check_error (
          "literal %d claimed not to be a failed literal "
          "(as it occurs negatively as %d in the 'f' line %zu in '%s') "
          "is in this unsatisfiable core 'u' line of the proof",
          -lit, lit, start_of_saved, interactions->name);
  unmark_line ();
  for (all_elements (int, lit, line))
    marks[lit] = false;
  (void) type;
}

static void conclude_unsatisfiable_query_with_core (int type) {
  debug ("concluding satisfiable query");
  check_line_propagation_yields_conflict (type);
  check_core_subset_of_query (type);
  if (saved_type == 'u')
    match_saved (type, "unsatisfiable core");
  else {
    assert (saved_type == 'f');
    check_saved_failed_literals_match_core (type);
  }
  statistics.conclusions++;
  statistics.cores++;
  assert (!level || inconsistent);
  debug ("unsatisfiable query concluded");
  (void) type;
  conclude_query (20);
}

/*------------------------------------------------------------------------*/

// The main parsing and checking routine can be found below.  It is a
// simple state-machine implemented with GOTO style programming and uses
// the following function to show state changes during logging.

#ifndef NDEBUG

static void debug_state (const char *name) {
  if (verbosity < INT_MAX)
    return;
  size_t printed = printf ("c DEBUG %u ----[ %s ]", level, name);
  while (printed++ != 73)
    fputc ('-', stdout);
  fputc ('\n', stdout);
  fflush (stdout);
}

#else
#define debug_state(...) \
  do { \
  } while (false)
#endif

#define STATE(NAME) \
  goto UNREACHABLE;   /* Make sure that there are no fall-throughs! */ \
  NAME:               /* This is the actual state label. */ \
  debug_state (#NAME) /* And print entering state during logging */

// The checker state machine implemented here should match the graphs in
// the dot files and the corresponding pdf files, which come in three
// variants: 'strict' (the default), 'pedantic' and 'relaxed'.  Currently
// not all features of 'strict' are implemented yet (we still require as
// in 'pedantic' mode that the interaction file is required to conclude
// with 'm', 'v', 'u' or 'f' after an 's' status line but the headers can
// be dropped). Nor are any of the 'relaxed' features working.  The next
// two comment paragraphs are therefore only here for future reference.

static int parse_and_check (void) {

  // TODO Redundant at this point (see above).

  // By default any parse error or failed check will abort the program
  // with exit code '1' except in 'relaxed' parsing mode where parsing and
  // checking continues if in the proof a model 'm' line is missing after
  // a 's SATISFIABLE' status line. Without having such a model the
  // checker can not guarantee the input clauses to be satisfied at this
  // point.

  // TODO Redundant at this point (see above).

  // For missing 'u' proof conclusion lines the checker might end up in
  // a similar situation (in case the user claims an unsatisfiable core
  // which is not implied by unit propagation).  In these cases the
  // program continues without error but simply exit with exit code '2' to
  // denote that checking only partially.

  int res = 0; // The exit code of the program without error.

  verbose ("starting interactions and proof checking in strict mode");
  goto INTERACTION_HEADER; // Explicitly start with this state.

  {
    STATE (INTERACTION_HEADER);
    if (mode == pedantic) {
      set_file (interactions);
      int type = next_line ('p');
      if (type == 'p' && match_header (ICNF))
        goto PROOF_HEADER;
      else {
        unexpected_line (type, "in pedantic mode 'p icnf' header");
        goto UNREACHABLE;
      }
    } else
      goto PROOF_HEADER;
  }
  {
    STATE (PROOF_HEADER);
    if (mode == pedantic) {
      set_file (proof);
      int type = next_line ('p');
      if (type == 'p' && match_header (IDRUP))
        goto INTERACTION_INPUT;
      else {
        unexpected_line (type, "in pedantic mode 'p idrup' header");
        goto UNREACHABLE;
      }
    } else
      goto INTERACTION_INPUT;
  }
  {
    STATE (INTERACTION_INPUT);
    set_file (interactions);
    int type = next_line ('i');
    if (type == 'i') {
      save_line (type);
      add_input_clause (type);
      goto PROOF_INPUT;
    } else if (type == 'q') {
      start_query ();
      save_line (type);
      save_query ();
      goto PROOF_QUERY;
    } else if (type == 0)
      goto END_OF_CHECKING;
    else if (type == 'p') {
      if (match_header (ICNF))
        goto INTERACTION_INPUT;
      else
        goto INTERACTION_INPUT_UNEXPECTED_LINE;
    } else {
    INTERACTION_INPUT_UNEXPECTED_LINE:
      unexpected_line (type, "'i' or 'q'");
      goto UNREACHABLE;
    }
  }
  {
    STATE (PROOF_INPUT);
    set_file (proof);
    int type = next_line ('i');
    if (type == 'i') {
      match_saved (type, "input");
      goto INTERACTION_INPUT;
    } else if (type == 'p') {
      if (match_header (IDRUP))
        goto PROOF_INPUT;
      else
        goto PROOF_INPUT_UNEXPECTED_LINE;
    } else if (!is_learn_delete_restore_or_weaken (type)) {
    PROOF_INPUT_UNEXPECTED_LINE:
      unexpected_line (type, "'i', 'l', 'd', 'r' or 'w'");
      goto UNREACHABLE;
    } else {
      learn_delete_restore_or_weaken (type);
      goto PROOF_INPUT;
    }
  }
  {
    STATE (PROOF_QUERY);
    set_file (proof);
    int type = next_line (0);
    if (type == 'q') {
      match_saved (type, "query");
      goto PROOF_CHECK;
    } else if (type == 'p') {
      if (match_header (IDRUP))
        goto PROOF_QUERY;
      else
        goto PROOF_QUERY_UNEXPECTED_LINE;
    } else if (!is_learn_delete_restore_or_weaken (type)) {
    PROOF_QUERY_UNEXPECTED_LINE:
      unexpected_line (type, "'q', 'l', 'd', 'r' or 'w'");
      goto UNREACHABLE;
    } else {
      learn_delete_restore_or_weaken (type);
      goto PROOF_QUERY;
    }
  }
  {
    STATE (PROOF_CHECK);
    set_file (proof);
    int type = next_line ('l');
    if (is_learn_delete_restore_or_weaken (type)) {
      learn_delete_restore_or_weaken (type);
      goto PROOF_CHECK;
    } else if (type != 's') {
      unexpected_line (type, "'s', 'l', 'd', 'r' or 'w'");
      goto UNREACHABLE;
    } else if (string == SATISFIABLE)
      goto INTERACTION_SATISFIABLE;
    else if (string == UNSATISFIABLE)
      goto INTERACTION_UNSATISFIABLE;
    else {
      assert (string == UNKNOWN);
      goto INTERACTION_UNKNOWN;
    }
  }
  {
    STATE (INTERACTION_SATISFIABLE);
    set_file (interactions);
    int type = next_line (0);
    if (type == 's' && string == SATISFIABLE)
      goto INTERACTION_SATISFIED;
    else if (type == 's') {
      parse_error ("unexpected 's %s' line (expected 's SATISFIABLE')",
                   string);
      goto UNREACHABLE;
    } else {
      unexpected_line (type, "'s SATISFIABLE'");
      goto UNREACHABLE;
    }
  }
  {
    STATE (INTERACTION_UNSATISFIABLE);
    set_file (interactions);
    int type = next_line (0);
    if (type == 's' && string == UNSATISFIABLE)
      goto INTERACTION_UNSATISFIED;
    else if (type == 's') {
      parse_error ("unexpected 's %s' line (expected 's UNSATISFIABLE')",
                   string);
      goto UNREACHABLE;
    } else {
      unexpected_line (type, "'s UNSATISFIABLE'");
      goto UNREACHABLE;
    }
  }
  {
    STATE (INTERACTION_UNKNOWN);
    set_file (interactions);
    int type = next_line (0);
    if (type == 's' && string == UNKNOWN) {
      conclude_query (0);
      goto INTERACTION_INPUT;
    } else if (type == 's') {
      parse_error ("unexpected 's %s' line (expected 's UNKNOWN')", string);
      goto UNREACHABLE;
    } else {
      unexpected_line (type, "'s UNKNOWN'");
      goto UNREACHABLE;
    }
  }
  {
    STATE (INTERACTION_SATISFIED);
    set_file (interactions);
    int type = next_line (0);
    if (type == 'v') {
      check_line_consistency (type);
      save_line (type);
      goto PROOF_MODEL;
    } else if (type == 'm') {
      check_line_consistency (type);
      check_line_satisfies_query (type);
      check_line_satisfies_input_clauses (type);
      save_line (type);
      goto PROOF_MODEL;
    } else {
      unexpected_line (type, "'v' or 'm'");
      goto UNREACHABLE;
    }
  }
  {
    STATE (PROOF_MODEL);
    set_file (proof);
    int type = next_line (0);
    if (type == 'm') {
      conclude_satisfiable_query_with_model (type);
      goto INTERACTION_INPUT;
    } else {
      unexpected_line (type, "'m'");
      goto UNREACHABLE;
    }
  }
  {
    STATE (INTERACTION_UNSATISFIED);
    set_file (interactions);
    int type = next_line (0);
    if (type == 'f') {
      check_line_consistency (type);
      check_line_variables_subset_of_query (type);
      save_line (type);
      goto PROOF_CORE;
    } else if (type == 'u') {
      check_line_propagation_yields_conflict (type);
      save_line (type);
      goto PROOF_CORE;
    } else {
      unexpected_line (type, "'f' or 'u'");
      goto UNREACHABLE;
    }
  }
  {
    STATE (PROOF_CORE);
    set_file (proof);
    int type = next_line (0);
    if (type == 'u') {
      conclude_unsatisfiable_query_with_core (type);
      goto INTERACTION_INPUT;
    } else {
      unexpected_line (type, "'u'");
      goto UNREACHABLE;
    }
  }
  {
    STATE (END_OF_CHECKING);
    verbose ("succesfully reached end-of-checking");
    return res;
  }
  {
    STATE (UNREACHABLE);
    fatal_error ("invalid parser state reached");
    return 1;
  }
}

/*------------------------------------------------------------------------*/

// Clean-up functions.

// Without a global list of clauses we traverse watch lists during
// deallocation of clauses and only deallocate a clauses if we visit it
// the second time through its larger watch.

static void release_watches (void) {
  for (int lit = -max_var; lit <= max_var; lit++) {
    struct clauses *watches = matrix + lit;
    for (all_pointers (struct clause, c, *watches)) {
      if (c->input)
        continue; // Released separately.
      if (c->size < 2)
        free_clause (c);
      else {
        int *lits = c->lits;
        int other = lits[0] ^ lits[1] ^ lit;
        if (other < lit)
          free_clause (c);
      }
    }
    RELEASE (*watches);
  }
}

static void release_inactive (void) {
  for (int lit = -max_var; lit <= max_var; lit++) {
    struct clauses *watches = inactive + lit;
    for (all_pointers (struct clause, c, *watches))
      if (!c->input)
        free_clause (c);
    RELEASE (*watches);
  }
}

static void release_empty_clauses (void) {
  for (all_pointers (struct clause, c, empty_clauses))
    free_clause (c);
  RELEASE (empty_clauses);
}

static void release_input_clauses (void) {
  for (all_pointers (struct clause, c, input_clauses))
    free_clause (c);
  RELEASE (input_clauses);
}

static void release (void) {
  RELEASE (line);
  RELEASE (saved);
  RELEASE (query);
  if (max_var) {
    release_watches ();
    release_inactive ();
  }
  release_empty_clauses ();
  release_input_clauses ();
  free (trail.begin);
  matrix -= allocated;
  free (matrix);
  inactive -= allocated;
  free (inactive);
  values -= allocated;
  free (values);
  marks -= allocated;
  free (marks);
  free (imported);
  free (levels);
}

/*------------------------------------------------------------------------*/

static void print_statistics (void) {
  double p = process_time ();
  double w = wall_clock_time ();
  printf ("c %-20s %20zu %12.2f per variable\n", "added:", statistics.added,
          average (statistics.added, statistics.imported));
  printf ("c %-20s %20zu %12.2f %% queries\n",
          "conclusions:", statistics.conclusions,
          percent (statistics.conclusions, statistics.queries));
  printf ("c %-20s %20zu %12.2f %% conclusions\n",
          "cores:", statistics.cores,
          percent (statistics.cores, statistics.conclusions));
  printf ("c %-20s %20zu %12.2f per lemma\n",
          "decisions:", statistics.decisions,
          average (statistics.decisions, statistics.lemmas));
  printf ("c %-20s %20zu %12.2f %% added\n", "deleted:", statistics.deleted,
          percent (statistics.deleted, statistics.added));
  printf ("c %-20s %20zu %12.2f %% added\n", "inputs:", statistics.inputs,
          percent (statistics.inputs, statistics.added));
  printf ("c %-20s %20zu %12.2f %% added\n", "lemmas:", statistics.lemmas,
          percent (statistics.lemmas, statistics.added));
  printf ("c %-20s %20zu %12.2f %% conclusions\n",
          "models:", statistics.models,
          percent (statistics.models, statistics.conclusions));
  printf ("c %-20s %20zu %12.2f per decision\n",
          "propagations:", statistics.propagations,
          average (statistics.propagations, statistics.decisions));
  printf ("c %-20s %20zu %12.2f per second\n",
          "queries:", statistics.queries, average (w, statistics.queries));
  printf ("c %-20s %20zu %12.2f %% weakened\n",
          "restored:", statistics.restored,
          percent (statistics.restored, statistics.weakened));
  printf ("c %-20s %20zu %12.2f %% inputs\n",
          "weakened:", statistics.weakened,
          percent (statistics.weakened, statistics.inputs));
  fputs ("c\n", stdout);
  double m = mega_bytes ();
  printf ("c %-20s %20.2f seconds %4.0f %% wall-clock\n",
          "process-time:", p, percent (p, w));
  printf ("c %-20s %20.2f seconds  100 %%\n", "wall-clock-time:", w);
  printf ("c %-20s %11.2f MB\n", "bymaximum-resident-set-size:", m);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

// Signal handling to print statistics if aborted.

#define SIGNALS \
  SIGNAL (SIGABRT) \
  SIGNAL (SIGBUS) \
  SIGNAL (SIGILL) \
  SIGNAL (SIGINT) \
  SIGNAL (SIGSEGV) \
  SIGNAL (SIGTERM)

#define SIGNAL(SIG) static void (*saved_##SIG##_handler) (int);
SIGNALS
#undef SIGNAL

static void reset_signals (void) {
#define SIGNAL(SIG) signal (SIG, saved_##SIG##_handler);
  SIGNALS
#undef SIGNAL
}

static const char *signal_name (int sig) {
#define SIGNAL(SIG) \
  if (sig == SIG) \
    return #SIG;
  SIGNALS
#undef SIGNAL
  return "SIGUNKNOWN";
}

static volatile int caught_signal;

static void catch_signal (int sig) {
  if (caught_signal)
    return;
  caught_signal = 0;
  reset_signals ();
  if (verbosity >= 0) {
    printf ("c\nc caught signal %d (%s)\nc\n", sig, signal_name (sig));
    print_statistics ();
    printf ("c\nc raising signal %d (%s)\n", sig, signal_name (sig));
    fflush (stdout);
  }
  raise (sig);
}

static void init_signals (void) {
#define SIGNAL(SIG) saved_##SIG##_handler = signal (SIG, catch_signal);
  SIGNALS
}

/*------------------------------------------------------------------------*/

int main (int argc, char **argv) {
  start_of_wall_clock_time = absolute_wall_clock_time ();
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp (arg, "-h") || !strcmp (arg, "--help")) {
      fputs (idrup_check_usage, stdout);
      exit (0);
    } else if (!strcmp (arg, "-q") || !strcmp (arg, "--quiet"))
      verbosity = -1;
    else if (!strcmp (arg, "-v") || !strcmp (arg, "--verbose"))
      verbosity += (verbosity < INT_MAX);
    else if (!strcmp (arg, "-l") || !strcmp (arg, "--logging"))
#ifndef NDEBUG
      verbosity = INT_MAX;
#else
      die ("invalid line option '%s' (compiled without debugging)", arg);
#endif
    else if (!strcmp (arg, "--version"))
      printf ("%s\n", idrup_version), exit (0);
    else if (!strcmp (arg, "--strict"))
      mode = strict;
    else if (!strcmp (arg, "--relaxed"))
      mode = relaxed;
    else if (!strcmp (arg, "--pedantic"))
      mode = pedantic;
    else if (arg[0] == '-')
      die ("invalid command line option '%s' (try '-h')", arg);
    else if (!files[0].name)
      files[0].name = arg;
    else if (!files[1].name)
      files[1].name = arg;
    else
      die ("too many files '%s', '%s' and '%s'", files[0].name,
           files[1].name, arg);
  }
  if (!files[0].name)
    die ("no file given but expected two (try '-h')");
  if (!files[1].name)
    die ("one file '%s' given but expected two (try '-h')", files[0].name);
  if (!(files[0].file = fopen (files[0].name, "r")))
    die ("can not read incremental CNF file '%s'", files[0].name);
  if (!(files[1].file = fopen (files[1].name, "r")))
    die ("can not read incremental DRUP proof file '%s'", files[1].name);

  message ("Interaction DRUP Checker");
  message ("Copyright (c) 2023 Armin Biere University of Freiburg");
  if (idrup_gitid)
    message ("Version %s %s", idrup_version, idrup_gitid);
  else
    message ("Version %s", idrup_version);
  message ("Compiler %s", idrup_compiler);
  message ("Build %s", idrup_build);

  init_signals ();

  if (verbosity >= 0)
    fputs ("c\n", stdout);
  message ("reading incremental CNF '%s'", files[0].name);
  message ("reading and checking incremental DRUP proof '%s'",
           files[1].name);

  for (int i = 0; i != 2; i++)
    files[i].lineno = 1;

  int res = parse_and_check ();

  if (verbosity >= 0)
    fputs ("c\n", stdout);
  if (res)
    fputs ("s FAILED\n", stdout);
  else
    fputs ("s VERIFIED\n", stdout);
  fflush (stdout);

  for (int i = 0; i != 2; i++) {
    if (verbosity > 0) {
      if (!i)
        fputs ("c\n", stdout);
      message ("closing '%s' after reading %zu lines (%zu bytes)",
               files[i].name, files[i].lineno, files[i].charno);
    }
    fclose (files[i].file);
  }

  release ();
  reset_signals ();

  if (verbosity >= 0) {
    printf ("c\n");
    print_statistics ();
    printf ("c\nc exit %d\n", res);
    fflush (stdout);
  }

  return res;
}
