// clang-format off

static const char * lidrup_check_usage =
"usage: lidrup-check [ <option> ... ] [ <icnf> ] <lidrup>\n"
"\n"
"where '<option>' is one of the following options:\n"
"\n"
"  -h | --help      print command line option summary\n"
#ifndef NDEBUG     
"  -l | --logging   enable very verbose logging\n"
#endif             
"  -n | --no-reuse  do not reuse clause identifiers\n"
"  -q | --quiet     do not print any message beside errors\n"
"  -v | --verbose   print more verbose message too\n"
"  --version        print version and exit\n"
"\n"

"If two files are specified the first '<icnf>' is an incremental CNF file\n"
"augmented with all interactions between the user and the SAT solver.\n"
"Thus the letter 'i' is overloaded and means both 'incremental' and\n"
"'interactions'. The second '<lidrup>' file is meant to be a super-set\n"
"of the interactions file but additionally has all the low level linear\n"
"incremental DRUP proof steps.\n"

"\n"

"The checker then makes sure the interactions match the proof and\n"
"all proof steps are justified. This is only the case though for the\n"
"default 'strict' and the 'pedantic' mode.  Checking is less strict in\n"
"'relaxed' mode where conclusion missing in the proof will be skipped.\n"
"Still the exit code will only be zero if all checks go through and thus\n"
"the interactions are all checked.\n"

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

"\n"

"If only the '<lidrup>' file is specified then it is supposed to contain\n"
"only the interaction proof lines.  In this case the query and the input\n"
"lines are assumed to match those of the user and are thus not checked\n"
"but the rest of the checking works exactly in the same way.\n"

;

// clang-format on

/*------------------------------------------------------------------------*/

#include "lidrup-build.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <ctype.h>
#include <inttypes.h>
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

struct lits {
  int *begin, *end, *allocated;
};

// Generic integer stack for clause ids.

struct ids {
  int64_t *begin, *end, *allocated;
};

// Parsed line.

struct line {
  int64_t id;
  struct lits lits;
  struct ids ids;
};

// We are reading interleaved from two files in parallel.

struct file {
  FILE *file;
  const char *name;      // Actual path to this file.
  size_t lines;          // Proof lines read from this file.
  size_t lineno;         // Line number of lines parsed so far.
  size_t colno;          // Number of characters parsed in the line.
  size_t charno;         // Number of bytes parsed.
  size_t start_of_line;  // Line number of current proof line.
  bool end_of_file;      // Buffer 'read-char' detected end-of-file.
  char last_char;        // Saved last char for bumping 'lineno'.
  size_t end_buffer;     // End of remaining characters in buffer.
  size_t size_buffer;    // Current position (bytes parsed) in buffer.
  char buffer[1u << 20]; // The actual buffer (1MB).
};

struct clause {
  int64_t id; // Clause id and hash key for hash tables.
#ifndef NDEBUG
  size_t lineno; // For better error messages.
#endif
  bool input;        // Input clauses are never freed.
  bool weakened;     // Weakened clauses are inactive.
  bool tautological; // Tautological clauses are always satisfied.
  unsigned size;     // The actual allocated size of 'lits'.
  int lits[];        // Flexible array member: lits[0], ..., lits[size-1].
};

struct clauses {
  struct clause **begin, **end, **allocated;
};

struct hash_table {
  struct clause **table;
  size_t count, size;
};

struct bit_table {
  uint64_t *words;
  size_t count, size;
};

/*------------------------------------------------------------------------*/

#define REMOVED ((struct clause *) ((uintptr_t) 1))
#define VALID(C) ((C) && (C) != REMOVED)

/*------------------------------------------------------------------------*/

// Global command line run-time options.

static int verbosity;     // -1=quiet, 0=default, 1=verbose, INT_MAX=logging
static int mode = strict; // Default 'strict not 'relaxed' nor 'pedantic'.
static bool no_reuse;     // Do not allow to reuse clause IDs.

/*------------------------------------------------------------------------*/

// Section of parsing state.

// Array of two files statically allocated and initialized.

static int num_files;
static struct file files[2] = {{.lineno = 1}, {.lineno = 1}};

// The actual interaction and proof files point into this array.

static struct file *interactions;
static struct file *proof;

// The current file from which we read (is set with 'set_file').

static struct file *file;

// The other file different from 'file' (so 'other_file == interactions'
// if 'file == proof' and vice versa).

static struct file *other_file;

/*------------------------------------------------------------------------*/

static bool querying;
static double start_time;

/*------------------------------------------------------------------------*/

static struct line line;  // Current line of integers parsed.
static struct lits saved; // Saved line for matching lines.
static struct lits query; // Saved query for checking.

// When saving a line the type and start of the line is saved too, where
// with start-of-the-line we mean the line number in the file.

static size_t start_of_query;
static size_t start_of_saved;
static int saved_type;

// Constant strings parsed in 'p' and 's' lines.  By only using global
// constant strings we can compare expected and scanned strings by simple
// pointer comparison, e.g., 'string == SATISFIABLE', instead of 'strcmp'.

static const char *const SATISFIABLE = "SATISFIABLE";
static const char *const UNSATISFIABLE = "UNSATISFIABLE";
static const char *const UNKNOWN = "UNKNOWN";
static const char *const LIDRUP = "lidrup";
static const char *const ICNF = "icnf";

// The parser saves strings here.

static const char *string;

/*------------------------------------------------------------------------*/

// Checker state.

static int max_var;                // Maximum variable index imported.
static size_t allocated;           // Allocated variables (>= 'max_var').
static bool *imported;             // Variable index imported?
static struct hash_table active;   // Active clauses (map ID to clause).
static struct hash_table inactive; // Inactive clauses (map ID to clause).
static struct bit_table used;      // Used clause identifiers.
static signed char *values;        // Assignment of literal: -1, 0, or 1.
static bool *marks;                // Marks of literals.

// This is the default preallocated trail. It is only resized during
// importing a new variable and thus allows simpler 'push' operations,
// without the need to check for the need for resizing when traversing
// either, which gives an nicer code when propagating literals.

static struct { int *begin, *end; } trail;

// Maps decision level to trail heights.

static bool inconsistent; // Empty clause derived.

// Input clauses are never actually deleted as they are needed for checking
// that models satisfy them.

static struct clauses input_clauses;

/*------------------------------------------------------------------------*/

// Global statistics

static struct {
  size_t added;
  size_t checks;
  size_t conclusions;
  size_t cores;
  size_t deleted;
  size_t inputs;
  size_t imported;
  size_t lemmas;
  size_t models;
  size_t resolutions;
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

// Iterator for the literals of a clause.

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
  fputs ("lidrup-check: error: ", stderr);
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
  fputs ("lidrup-check: fatal internal error: ", stderr);
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
  fputs ("lidrup-check: error: out-of-memory ", stderr);
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

static void verbose (const char *, ...)
    __attribute__ ((format (printf, 1, 2)));

static void verbose (const char *fmt, ...) {
  if (verbosity < 1)
    return;
  fputs ("c ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void parse_error (const char *, ...)
    __attribute__ ((format (printf, 1, 2)));

static void parse_error (const char *fmt, ...) {
  assert (file);
  fprintf (stderr,
           "lidrup-check: parse error: at line %zu column %zu in '%s': ",
           file->start_of_line, file->colno, file->name);
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
  fprintf (stderr, "lidrup-check: error: at line %zu in '%s': ",
           file->start_of_line, file->name);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static bool type_has_id (int t) { return t == 'i' || t == 'l'; }

static bool type_has_lits (int t) {
  return t == 'i' || t == 'l' || t == 'q' || t == 'm' || t == 'u' ||
         t == 'v' || t == 'f';
}

static bool type_has_ids (int t) {
  return t == 'l' || t == 'd' || t == 'w' || t == 'r' || t == 'u';
}

static void line_error (int type, const char *, ...)
    __attribute__ ((format (printf, 2, 3)));

static void line_error (int type, const char *fmt, ...) {
  assert (type != 's');
  assert (type != 'p');
  assert (file);
  fflush (stdout);
  fprintf (stderr, "lidrup-check: error: at line %zu in '%s': ",
           file->start_of_line, file->name);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fputc (type, stderr);
  if (type_has_id (type)) {
    assert (line.id > 0);
    fprintf (stderr, " %" PRId64, line.id);
  } else
    assert (!line.id);
  if (type_has_lits (type)) {
    for (all_elements (int, lit, line.lits))
      fprintf (stderr, " %d", lit);
    fputs (" 0", stderr);
  } else
    assert (EMPTY (line.lits));
  if (type_has_ids (type)) {
    for (all_elements (int64_t, id, line.ids))
      fprintf (stderr, " %" PRId64, id);
    fputs (" 0", stderr);
  } else
    assert (EMPTY (line.ids));
  fputc ('\n', stderr);
  exit (1);
}

#ifndef NDEBUG

static void debug (const char *, ...)
    __attribute__ ((format (printf, 1, 2)));

static void debug (const char *fmt, ...) {
  if (verbosity != INT_MAX)
    return;
  fputs ("c DEBUG ", stdout);
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
  printf ("c DEBUG parsed line %zu in '%s': ", file->lineno, file->name);
  if (!type)
    fputs ("<end-of-file>", stdout);
  else if (type == 'p' || type == 's')
    printf ("%c %s", type, string);
  else {
    printf ("%c", type);
    if (type_has_id (type))
      printf (" %" PRId64, line.id);
    if (type_has_lits (type)) {
      for (const int *p = line.lits.begin; p != line.lits.end; p++)
        printf (" %d", *p);
      fputs (" 0", stdout);
    }
    if (type_has_ids (type)) {
      for (const int64_t *p = line.ids.begin; p != line.ids.end; p++)
        printf (" %" PRId64, *p);
      fputs (" 0", stdout);
    }
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
    snprintf (res, debug_buffer_line_size, "%d=%d", lit, value);
  else
    snprintf (res, debug_buffer_line_size, "%d", lit);
  return res;
}

static void debug_clause (struct clause *, const char *, ...)
    __attribute__ ((format (printf, 2, 3)));

static void debug_clause (struct clause *c, const char *fmt, ...) {
  if (verbosity < INT_MAX)
    return;
  fputs ("c DEBUG ", stdout);
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
  printf (" size %u line %zu clause[%" PRId64 "]", c->size, c->lineno,
          c->id);
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
    bool *new_imported = calloc (new_allocated, sizeof *new_imported);
    if (!new_imported)
      out_of_memory ("reallocating imported of size %zu", new_allocated);
    for (int idx = 1; idx <= max_var; idx++)
      new_imported[idx] = imported[idx];
    free (imported);
    imported = new_imported;
  }
  {
    assert (EMPTY (trail));
    trail.begin =
        realloc (trail.begin, new_allocated * sizeof *trail.begin);
    if (!trail.begin)
      out_of_memory ("reallocating trail of size %zu", new_allocated);
    trail.end = trail.begin;
  }
  allocated = new_allocated;
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
  if (num_files == 2) {
    other_file = file == interactions ? proof : interactions;
    assert (other_file);
    assert (other_file->file);
  } else
    assert (!other_file);
}

static int read_char (void) {
  assert (file);
  assert (file->file);
  if (file->size_buffer == file->end_buffer) {
    if (file->end_of_file)
      return EOF;
    file->end_buffer =
        read (fileno (file->file), file->buffer, sizeof file->buffer);
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
  if (res != EOF) {
    file->charno++;
    file->colno++;
  }
  return res;
}

static int ISDIGIT (int ch) { return '0' <= ch && ch <= '9'; }

static int next_line_without_printing (char default_type) {

  int ch;

  for (;;) {
    file->colno = 0;
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

  // We have three 'types' denoting the letter 'i' etc. of the parsed line.
  // The 'default_type' (if non-zero) is the one used in this context if the
  // line does actually not contain a type (like in the DIMACS or original
  // DRUP format).  The 'actual_type' is returned and allows to normalize
  // types (for instance replacing 'a' with 'q').  The 'parsed_type' is the
  // actual parsed letter (and zero if no letter was given).

  int parsed_type = 0;
  int actual_type = 0;
  string = 0;

  line.id = 0;
  CLEAR (line.lits);
  CLEAR (line.ids);
  file->lines++;

  if (ch == 'p') {
    if (next_char () != ' ')
    INVALID_HEADER_LINE:
      parse_error ("invalid 'p' header line");

    ch = next_char ();
    if (ch == 'i') {
      for (const char *p = "cnf"; (ch = *p); p++)
        if (next_char () != ch)
          goto INVALID_HEADER_LINE;
      string = ICNF;
    } else if (ch == 'l') {
      for (const char *p = "idrup"; (ch = *p); p++)
        if (next_char () != ch)
          goto INVALID_HEADER_LINE;
      string = LIDRUP;
    } else
      goto INVALID_HEADER_LINE;

    // TODO parse 'p cnf <vars> <clauses>' header too.

    if (next_char () != '\n')
      parse_error ("expected new line after '%s' header", string);

    return 'p';
  }

  if ('a' <= ch && ch <= 'z') {
    parsed_type = ch;
    if (ch == 'a')
      actual_type = 'q';
    else
      actual_type = ch;
    if ((ch = next_char ()) != ' ')
      parse_error ("expected space after '%c'", parsed_type);
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

  if (file != interactions && type_has_id (actual_type)) {

    assert (!line.id);

    if (ch == '-')
      parse_error ("expected non-negative clause identifier "
                   "(non-linear '.idrup' file?)");
    if (!ISDIGIT (ch))
      parse_error ("expected clause identifier");
    if (ch == '0')
      parse_error ("expected non-zero clause identifier");

    int64_t id = ch - '0';

    while (ISDIGIT (ch = next_char ())) {
      assert (id);
      if (INT64_MAX / 10 < id)
        parse_error ("clause identifier too large");
      id *= 10;
      int digit = ch - '0';
      if (INT64_MAX - digit < id)
        parse_error ("clause identifier too large");
      id += digit;
    }

    if (ch != ' ')
      parse_error ("expected space after '%" PRId64 "'", id);

    assert (id);
    line.id = id;

    ch = next_char ();
  }

  if (type_has_lits (actual_type)) {

    assert (EMPTY (line.lits));

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
          parse_error ("variable index too large");
        idx *= 10;
        int digit = ch - '0';
        if (INT_MAX - digit < idx)
          parse_error ("variable index too large");
        idx += digit;
      }

      if (idx)
        import_variable (idx);

      assert (idx != INT_MIN);
      int lit = sign * idx;

      if (file != interactions && type_has_ids (actual_type)) {
        if (ch != ' ')
          parse_error ("expected space after '%d'", lit);
        if (!lit) {
          ch = next_char ();
          break;
        }
      } else {
        if (!lit && ch != '\n')
          parse_error ("expected new-line after '0'");
        if (lit && ch != ' ')
          parse_error ("expected space after '%d'", lit);
        assert (ch == ' ' || ch == '\n');
        if (!lit)
          return actual_type;
      }
      assert (lit);
      PUSH (line.lits, lit);
      assert (ch == ' ');
      ch = next_char ();
    }
  }

  assert (file != interactions);
  assert (type_has_ids (actual_type));
  assert (EMPTY (line.ids));

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

    int64_t id = ch - '0';

    while (ISDIGIT (ch = next_char ())) {
      if (!id)
        parse_error ("invalid leading '0' digit");
      if (INT64_MAX / 10 < id)
        parse_error ("antecedent clause identifier too large");
      id *= 10;
      int digit = ch - '0';
      if (INT64_MAX - digit < id)
        parse_error ("antecedent clause identifier too large");
      id += digit;
    }

    if (id) {

      id *= sign;
      if (ch != ' ')
        parse_error ("expected space after '%" PRId64 "'", id);

      assert (id);
      PUSH (line.ids, id);
      ch = next_char ();

    } else if (ch != '\n')
      parse_error ("expected new-line after '0'");
    else
      return actual_type;
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

// Assigning a single variable and backtracking / unassigning all.

static void assign (int lit) {
  assert (!values[lit]);
  assert (!values[-lit]);
  *trail.end++ = lit;
  values[-lit] = -1;
  values[lit] = 1;
  debug ("assign %s", debug_literal (lit));
}

static void backtrack (void) {
  for (all_elements (int, lit, trail)) {
    debug ("unassign %s", debug_literal (lit));
    assert (values[lit] > 0);
    assert (values[-lit] < 0);
    values[lit] = values[-lit] = 0;
  }
  trail.end = trail.begin;
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

static void mark_literals (struct lits *lits) {
  for (all_elements (int, lit, *lits))
    mark_literal (lit);
}

static void unmark_literals (struct lits *lits) {
  for (all_elements (int, lit, *lits))
    unmark_literal (lit);
}

static void mark_line (void) { mark_literals (&line.lits); }
static void unmark_line (void) { unmark_literals (&line.lits); }

static void mark_query (void) { mark_literals (&query); }
static void unmark_query (void) { unmark_literals (&query); }

static bool subset_literals (struct lits *a, struct lits *b) {
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

static bool match_literals (struct lits *a, struct lits *b) {
  return subset_literals (a, b) && subset_literals (b, a);
}

/*------------------------------------------------------------------------*/

// Clause allocation and deallocation.

static bool line_is_tautological () {
  bool res = false;
  for (all_elements (int, lit, line.lits)) {
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
  size_t size = SIZE (line.lits);
  if (size > UINT_MAX)
    parse_error ("maximum clause size exhausted");
  size_t lits_bytes = size * sizeof (int);
  size_t all_bytes = sizeof (struct clause) + lits_bytes;
  struct clause *c = malloc (all_bytes);
  if (!c)
    out_of_memory ("allocating clause of size %zu", size);
  assert (VALID (c));
  c->id = line.id;
#ifndef NDEBUG
  assert (file);
  c->lineno = file->start_of_line;
#endif
  c->size = size;
  c->weakened = false;
  c->input = input;
  c->tautological = line_is_tautological ();
  memcpy (c->lits, line.lits.begin, lits_bytes);
  debug_clause (c, "allocate");
  if (input)
    PUSH (input_clauses, c);
  statistics.added++;
  return c;
}

static void free_clause (struct clause *c) {
  debug ("freeing clause at %p", (void *) c);
  debug_clause (c, "freeing");
  free (c);
}

/*------------------------------------------------------------------------*/

// Hash table insertion of clauses based on their ID.

#ifndef NDEBUG

static bool is_power_of_two (size_t n) { return n && !(n & (n - 1)); }

#endif

static const char *hash_table_name (struct hash_table *hash_table) {
  return hash_table == &active ? "active" : "inactive";
}

static size_t reduce_hash (int64_t id, size_t size) {
  assert (id > 0);
  assert (is_power_of_two (size));
  return ((size_t) id) & (size - 1);
}

static void enlarge_hash_table (struct hash_table *hash_table) {
  size_t old_size = hash_table->size;
  size_t old_count = hash_table->count;
  struct clause **old_table = hash_table->table;
  size_t new_size = old_size ? 2 * old_size : 1;
  debug ("enlarging %s clause hash table to %zu",
         hash_table_name (hash_table), new_size);
  struct clause **new_table = calloc (new_size, sizeof *new_table);
  if (!new_table)
    out_of_memory ("enlarging %s clause hash table of size %zu",
                   hash_table_name (hash_table), old_size);
  size_t removed = 0;
  struct clause **const end_of_old_table = old_table + old_size;
#ifndef NDEBUG
  size_t old_clauses = 0;
  for (struct clause **p = old_table; p != end_of_old_table; p++)
    if (VALID (*p))
      old_clauses++;
#endif
  for (struct clause **p = old_table; p != end_of_old_table; p++) {
    struct clause *c = *p;
    if (!c)
      continue;
    if (c == REMOVED) {
      removed++;
      continue;
    }
    size_t new_pos = reduce_hash (c->id, new_size);
    while (new_table[new_pos])
      if (++new_pos == new_size)
        new_pos = 0;
    new_table[new_pos] = c;
  }
  size_t new_count = old_count - removed;
  hash_table->count = new_count;
  hash_table->size = new_size;
  hash_table->table = new_table;
#ifndef NDEBUG
  size_t new_clauses = 0;
  struct clause **const end_of_new_table = new_table + new_size;
  for (struct clause **p = new_table; p != end_of_new_table; p++)
    if (VALID (*p))
      new_clauses++;
  assert (old_clauses == new_clauses);
  assert (new_count == new_clauses);
#endif
  free (old_table);
}

static struct clause *find_clause (struct hash_table *hash_table,
                                   int64_t id) {
  size_t size = hash_table->size;
  struct clause *res = 0;
  if (size) {
    struct clause **table = hash_table->table;
    size_t start = reduce_hash (id, size), pos = start;
    for (;;) {
      res = table[pos];
      if (!res)
        break;
      if (res != REMOVED && res->id == id)
        break;
      if (++pos == size)
        pos = 0;
      if (pos == start) {
        res = 0;
        break;
      }
    }
  }
#ifndef NDEBUG
  if (res)
    debug_clause (res, "found in %s clause hash table",
                  hash_table_name (hash_table));
  else
    debug ("could not find clause with identifier %" PRId64
           " in %s clause hash table",
           id, hash_table_name (hash_table));
#endif
  return res;
}

static bool is_full_hash_table (struct hash_table *hash_table) {
  size_t size = hash_table->size;
  size_t count = hash_table->count;
  return 2 * count >= size;
}

static void insert_clause (struct hash_table *hash_table,
                           struct clause *c) {
  debug_clause (c, "inserting in %s clause hash table",
                hash_table_name (hash_table));
  if (is_full_hash_table (hash_table))
    enlarge_hash_table (hash_table);
  size_t size = hash_table->size;
  size_t start = reduce_hash (c->id, size), pos = start;
  struct clause **table = hash_table->table;
  for (;;) {
    struct clause *res = table[pos];
    if (res == REMOVED)
      break;
    if (!res) {
      hash_table->count++;
      break;
    }
    assert (res != c);
    if (++pos == size)
      pos = 0;
    assert (pos != start);
  }
  table[pos] = c;
}

static void remove_clause (struct hash_table *hash_table,
                           struct clause *c) {
  debug_clause (c, "removing from %s clause hash table",
                hash_table_name (hash_table));
  size_t size = hash_table->size;
  struct clause **table = hash_table->table;
  size_t start = reduce_hash (c->id, size), pos = start;
  for (;;) {
    struct clause *res = table[pos];
    if (res == c)
      break;
    assert (res);
    if (++pos == size)
      pos = 0;
    assert (pos != start);
  }
  table[pos] = REMOVED;
}

/*------------------------------------------------------------------------*/

static bool contains_bit (struct bit_table *bits, int64_t id) {
  size_t word_size = bits->size;
  if (!word_size)
    return false;
  size_t id_pos = id;
  size_t id_word_pos = id_pos >> 6;
  if (id_word_pos >= word_size)
    return false;
  unsigned id_word_bit = id_pos & 63;
  uint64_t id_word_mask = ((uint64_t) 1) << id_word_bit;
  return bits->words[id_word_pos] & id_word_mask;
}

static void enlarge_bit_table (struct bit_table *bits,
                               size_t new_word_size) {
  size_t old_word_size = bits->size;
  assert (old_word_size < new_word_size);
  size_t delta_word_size = new_word_size - old_word_size;
  size_t delta_bytes = delta_word_size * 8;
  size_t new_bytes = new_word_size * 8;
  bits->words = realloc (bits->words, new_bytes);
  if (!bits->words)
    out_of_memory ("allocating used ids table");
  memset (bits->words + old_word_size, 0, delta_bytes);
  bits->size = new_word_size;
}

static void insert_bit (struct bit_table *bits, int64_t id) {
  size_t old_word_size = bits->size;
  size_t id_pos = id;
  size_t id_word_pos = id_pos >> 6;
  if (id_word_pos >= old_word_size) {
    size_t new_word_size = old_word_size ? 2 * old_word_size : 1;
    while (new_word_size <= id_word_pos)
      new_word_size *= 2;
    enlarge_bit_table (bits, new_word_size);
  }
  unsigned id_word_bit = id_pos & 63;
  uint64_t id_word_mask = ((uint64_t) 1) << id_word_bit;
  assert (!(bits->words[id_word_pos] & id_word_mask));
  bits->words[id_word_pos] |= id_word_mask;
}

/*------------------------------------------------------------------------*/

// The assumptions in the query have to be saved until the query ends.

static void save_query (void) {
  debug ("saving query");
  COPY (int, query, line.lits);
  start_of_query = file->start_of_line;
  statistics.queries++;
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

  statistics.checks++;
#ifndef NDEBUG
  if (sign < 0)
    debug ("checking unsatisfiable core justified");
  else
    debug ("checking lemma is justified");
#endif

  debug ("assigning first all literals");
  for (all_elements (int, lit, line.lits)) {
    int signed_lit = sign * lit;
    signed char value = values[signed_lit];
    if (value < 0) {
      debug ("skipping duplicated literal %s", debug_literal (signed_lit));
      continue;
    }
    if (value > 0) {
      debug ("found tautological literal %s and %s",
             debug_literal (-signed_lit), debug_literal (signed_lit));
      goto IMPLICATION_CHECK_SUCCEEDED;
    }
    assign (-signed_lit);
  }

  for (all_elements (int64_t, id, line.ids)) {
    if (id < 0)
      line_error (type, "negative antecedent %" PRId64 " unsupported", id);
    struct clause *c = find_clause (&active, id);
    if (!c) {
      if (find_clause (&inactive, id))
        line_error (type, "antecedent %" PRId64 " weakened", id);
      else
        line_error (type, "could not find antecedent %" PRId64, id);
    }
    statistics.resolutions++;
    debug_clause (c, "resolving");
    int unit = 0;
    for (all_literals (lit, c)) {
      signed char value = values[lit];
      if (value < 0)
        continue;
      if (unit && unit != lit)
        line_error (type, "antecedent %" PRId64 " not resolvable", id);
      unit = lit;
      if (!value)
        assign (lit);
    }
    if (!unit) {
      debug_clause (c, "justifying conflicting");
      goto IMPLICATION_CHECK_SUCCEEDED;
    }
  }

  line_error (type, "%s resolution check failed:", type_str);

IMPLICATION_CHECK_SUCCEEDED:

  backtrack ();

  debug ("%s resolution check succeeded", type_str);
  (void) type_str;
}

/*------------------------------------------------------------------------*/

// This section has all the low-level checks.

static void check_unused (int type) {
  assert (line.id);
  if (no_reuse) {
    if (contains_bit (&used, line.id))
      line_error (type, "clause identifier %" PRId64 " already used",
                  line.id);
    insert_bit (&used, line.id);
    debug ("clause identifier %" PRId64 " was never used", line.id);
  } else {
    if (find_clause (&active, line.id))
      line_error (type, "clause identifier %" PRId64 " actively in use",
                  line.id);
    if (find_clause (&inactive, line.id))
      line_error (type, "clause identifier %" PRId64 " inactive but in use",
                  line.id);
    debug ("clause identifier %" PRId64 " is not in use", line.id);
  }
}

static void delete_clause (struct clause *c) {
  assert (!c->weakened);
  remove_clause (&active, c);
  if (c->input)
    debug_clause (c, "deleting but not freeing");
  else
    free_clause (c);
  statistics.deleted++;
}

static void weaken_clause (struct clause *c) {
  assert (!c->weakened);
  debug_clause (c, "weakening");
  c->weakened = true;
  remove_clause (&active, c);
  insert_clause (&inactive, c);
  statistics.weakened++;
}

static void restore_clause (struct clause *c) {
  assert (c->weakened);
  debug_clause (c, "restoring");
  remove_clause (&inactive, c);
  insert_clause (&active, c);
  c->weakened = false;
  statistics.restored++;
}

// Check that there are no clashing literals (both positive and negative
// occurrence of a variable) in the current line.  This is a mandatory
// check for conclusions, i.e., for both 'm' models and 'u' core lines.

static void check_line_consistency (int type) {
  for (all_elements (int, lit, line.lits)) {
    assert (valid_literal (lit));
    if (marks[-lit])
      check_error ("inconsistent '%c' line with literals %d and %d", type, -lit,
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
      check_error ("inconsistent '%c' line on literal %d with line %zu in '%s'",
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
           "lidrup-check: error: model at line %zu in '%s' "
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

/*------------------------------------------------------------------------*/

// TODO remove or add back?

#if 0

// Check that the given literal has been imported before.  This in a
// certain sense is redundant for checking correctness but gives more
// useful error messages and should be really cheap anyhow since it does
// not require even marking literals.  Imported statistics are probably
// useful too.

static void check_literal_imported (int type, int lit) {
  int idx = abs (lit);
  if (idx > max_var || !imported[idx])
    line_error (type, "literal %d unused", lit);
}

static void check_literals_imported (int type) {
  debug ("checking literals imported");
  for (all_elements (int, lit, line.lits))
    check_literal_imported (type, lit);
}

#endif

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
  check_unused (type);
  struct clause *c = allocate_clause (true);
  insert_clause (&active, c);
  statistics.inputs++;
  (void) type;
}

static void check_then_add_lemma (int type) {
  check_unused (type);
  check_implied (type, "lemma", 1);
  struct clause *c = allocate_clause (false);
  insert_clause (&active, c);
  statistics.lemmas++;
  (void) type;
}

static void find_then_delete_clause (int type, int64_t id) {
  struct clause *c = find_clause (&active, id);
  if (c)
    delete_clause (c);
  else
    line_error (type, "could not find and delete clause %" PRId64, id);
}

static void find_then_weaken_clause (int type, int64_t id) {
  struct clause *c = find_clause (&active, id);
  if (c)
    weaken_clause (c);
  else
    line_error (type, "could not find and weaken clause %" PRId64, id);
}

static void find_then_restore_clause (int type, int64_t id) {
  struct clause *c = find_clause (&inactive, id);
  if (c)
    restore_clause (c);
  else
    line_error (type, "could not find and restore weakened clause %" PRId64,
                id);
}

static void find_then_delete_clauses (int type) {
  assert (type == 'd');
  for (all_elements (int64_t, id, line.ids))
    find_then_delete_clause (type, id);
}

static void find_then_weaken_clauses (int type) {
  assert (type == 'w');
  for (all_elements (int64_t, id, line.ids))
    find_then_weaken_clause (type, id);
}

static void find_then_restore_clauses (int type) {
  assert (type == 'r');
  for (all_elements (int64_t, id, line.ids))
    find_then_restore_clause (type, id);
}

static bool is_input_learn_delete_restore_or_weaken (int type) {
  return type == 'i' || type == 'l' || type == 'd' || type == 'r' ||
         type == 'w';
}

static void learn_delete_restore_or_weaken (int type) {
  if (type == 'l')
    check_then_add_lemma (type);
  else if (type == 'd')
    find_then_delete_clauses (type);
  else if (type == 'r')
    find_then_restore_clauses (type);
  else if (type == 'i')
    add_input_clause (type);
  else {
    assert (type == 'w');
    find_then_weaken_clauses (type);
  }
}

static void match_saved (int type, const char *type_str) {
  debug ("matching saved line");
  if (!match_literals (&line.lits, &saved))
    check_error ("%s '%c' line does not match '%c' line %zu in '%s'",
                 type_str, type, saved_type, start_of_saved,
                 other_file->name);
  debug ("saved line matched");
}

static void save_line (int type) {
  debug ("saving '%c' line", type);
  COPY (int, saved, line.lits);
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

static void check_core_subset_of_query (int type) {
  mark_query ();
  for (all_elements (int, lit, line.lits))
    if (!marks[lit])
      check_error ("core literal %d not in query at line %zu in '%s'", lit,
                   start_of_query, interactions->name);
  unmark_query ();
  debug ("core subset of query");
  (void) type;
}

static void check_line_variables_subset_of_query (int type) {
  mark_query ();
  for (all_elements (int, lit, line.lits))
    if (!marks[lit] && !marks[-lit])
      check_error ("literal %d nor %d in query at line %zu in '%s'", lit,
                   -lit, start_of_query, interactions->name);
  unmark_query ();
  debug ("line variables subset of query");
  (void) type;
}

static void check_saved_failed_literals_match_core (int type) {
  for (all_elements (int, lit, line.lits))
    marks[lit] = true;
  for (all_elements (int, lit, saved))
    if (marks[-lit])
      check_error ("literal '%d' in this unsatisfiable core 'u' line "
                   "of the proof "
                   "is claimed not to be a failed literal "
                   "in the 'f' line %zu of the interaction file '%s' "
                   "(as it occurs negated as '%d' there)",
                   -lit, start_of_saved, interactions->name, lit);
  unmark_line ();
  for (all_elements (int, lit, line.lits))
    marks[lit] = false;
  (void) type;
}

/*------------------------------------------------------------------------*/

// The two conclusion functions here make sure that the last query was
// checked correctly and can be discharged and depending on whether the
// solvers answer was that the query was satisfiable or unsatisfiable
// either require a model line or an unsatisfiable core, which are
// checked.

static void conclude_satisfiable_query_with_model (int type) {
  debug ("concluding satisfiable query");
  assert (!inconsistent);
  check_line_consistency (type);
  check_line_satisfies_query (type);
  check_line_satisfies_input_clauses (type);
  if (num_files > 1)
    check_line_consistent_with_saved (type);
  statistics.conclusions++;
  statistics.models++;
  debug ("satisfiable query concluded");
  conclude_query (10);
}

static void conclude_unsatisfiable_query_with_core (int type) {
  debug ("concluding satisfiable query");
  check_core_subset_of_query (type);
  if (num_files > 1) {
    if (saved_type == 'u')
      match_saved (type, "unsatisfiable core");
    else {
      assert (saved_type == 'f');
      check_saved_failed_literals_match_core (type);
    }
  }
  check_implied (type, "unsatisfiable core", -1);
  statistics.conclusions++;
  statistics.cores++;
  debug ("unsatisfiable query concluded");
  (void) type;
  conclude_query (20);
}

/*------------------------------------------------------------------------*/

static const char *mode_string (void) {
  if (mode == strict)
    return "strict";
  if (mode == relaxed)
    return "relaxed";
  if (mode == pedantic)
    return "pedantic";
  return "unknown";
}

// The main parsing and checking routine can be found below.  It is a
// simple state-machine implemented with GOTO style programming and uses
// the following function to show state changes during logging.

#ifndef NDEBUG

static void debug_state (const char *name) {
  if (verbosity < INT_MAX)
    return;
  size_t printed = printf ("c DEBUG ----[ %s ]", name);
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
// the dot files and the corresponding PDF files.  They come in three
// variants: 'strict' (the default), 'pedantic' and 'relaxed'. Currently
// not all features of 'strict' are implemented yet (we still require as
// in 'pedantic' mode that the interaction file is required to conclude
// with 'm', 'v', 'u' or 'f' after an 's' status line but the headers
// can be dropped). Nor are any of the 'relaxed' features working.  The
// next two comment paragraphs are therefore only here for future
// reference.

static int parse_and_check_icnf_and_idrup (void) {

  // TODO Redundant at this point (see above).

  // By default any parse error or failed check will abort the program
  // with exit code '1' except in 'relaxed' parsing mode where parsing
  // and checking continues if in the proof a model 'm' line is missing
  // after a 's SATISFIABLE' status line. Without having such a model
  // the checker can not guarantee the input clauses to be satisfied at
  // this point.

  // TODO Redundant at this point (see above).

  // For missing 'u' proof conclusion lines the checker might end up in
  // a similar situation (in case the user claims an unsatisfiable core
  // which is not implied by unit propagation).  In these cases the
  // program continues without error but simply exit with exit code '2'
  // to denote that checking only partially.

  int res = 0; // The exit code of the program without error.

  message ("parallel interaction and proof checking in %s mode",
           mode_string ());
  goto INTERACTION_HEADER; // Explicitly start with this state.

  // In order to build a clean state-machine the basic block of each
  // state should always be left with a 'goto'.  To ease code reviewing
  // we even want to enforce this rule for unreachable code after error
  // message (which abort the program) by adding a 'goto UNREACHABLE'
  // after those error messages and further have a 'goto UNREACHABLE'
  // implicitly before each 'state' label.  The 'UNREACHABLE' state
  // should not be reachable and if in a corner cases it still is prints
  // a fatal error message.

  {
    STATE (INTERACTION_HEADER);
    if (mode == pedantic) {
      set_file (interactions);
      int type = next_line (0);
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
      int type = next_line (0);
      if (type == 'p' && match_header (LIDRUP))
        goto INTERACTION_INPUT;
      else {
        unexpected_line (type, "in pedantic mode 'p lidrup' header");
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
        goto ERROR_INTERACTION_INPUT_UNEXPECTED_LINE;
    } else {
    ERROR_INTERACTION_INPUT_UNEXPECTED_LINE:
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
      add_input_clause (type);
      goto INTERACTION_INPUT;
    } else if (type == 'p') {
      if (match_header (LIDRUP))
        goto PROOF_INPUT;
      else
        goto ERROR_PROOF_INPUT_UNEXPECTED_LINE;
    } else if (!is_input_learn_delete_restore_or_weaken (type)) {
    ERROR_PROOF_INPUT_UNEXPECTED_LINE:
      unexpected_line (type, "'i', 'l', 'd', 'w' or 'r'");
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
      if (match_header (LIDRUP))
        goto PROOF_QUERY;
      else
        goto PROOF_QUERY_UNEXPECTED_LINE;
    } else if (!is_input_learn_delete_restore_or_weaken (type)) {
    PROOF_QUERY_UNEXPECTED_LINE:
      unexpected_line (type, "'q', 'l', 'd', 'w' or 'r'");
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
    if (type == 'i') {
      save_line (type);
      add_input_clause (type);
      goto INTERACTION_PROPAGATE;
    } else if (is_input_learn_delete_restore_or_weaken (type)) {
      learn_delete_restore_or_weaken (type);
      goto PROOF_CHECK;
    } else if (type != 's') {
      unexpected_line (type, "'s', 'i', 'l', 'd', 'w' or 'r'");
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
    STATE (INTERACTION_PROPAGATE);
    set_file (interactions);
    int type = next_line ('l');
    if (type == 'i') {
      match_saved (type, "input");
      goto PROOF_CHECK;
    } else {
      unexpected_line (type, "'i'");
      goto UNREACHABLE;
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
    verbose ("successfully reached end-of-checking");
    return res;
  }
  {
    STATE (UNREACHABLE);
    fatal_error ("invalid parser state reached");
    return 1;
  }
}

/*------------------------------------------------------------------------*/

// This is the version of the parser and checker when only the
// '<lidrup>' file is given. It is much simpler but otherwise works the
// same way as 'parse_and_check_icnf_and_idrup' which checks the
// interactions in the
// '<icnf>' file against the proof lines in '<lidrup>'.

static int parse_and_check_idrup (void) {

  int res = 0; // See comments above why we have this redundant 'res'.

  set_file (proof);
  message ("sequential checking only proof in %s mode", mode_string ());
  goto PROOF_HEADER;

  {
    STATE (PROOF_HEADER);
    if (mode == pedantic) {
      int type = next_line (0);
      if (type == 'p' && match_header (ICNF))
        goto PROOF_INPUT;
      else {
        unexpected_line (type, "in pedantic mode 'p icnf' header");
        goto UNREACHABLE;
      }
    } else
      goto PROOF_INPUT;
  }
  {
    STATE (PROOF_INPUT);
    int type = next_line ('i');
    if (type == 'i') {
      add_input_clause (type);
      goto PROOF_INPUT;
    } else if (type == 'p') {
      if (match_header (LIDRUP))
        goto PROOF_INPUT;
      else
        goto PROOF_INPUT_UNEXPECTED_LINE;
    } else if (type == 'q') {
      start_query ();
      save_query ();
      goto PROOF_CHECK;
    } else if (type == 0)
      goto END_OF_CHECKING;
    else if (!is_input_learn_delete_restore_or_weaken (type)) {
    PROOF_INPUT_UNEXPECTED_LINE:
      unexpected_line (type, "'q', 'i', 'l', 'd', 'w' or 'r'");
      goto UNREACHABLE;
    } else {
      learn_delete_restore_or_weaken (type);
      goto PROOF_INPUT;
    }
  }
  {
    STATE (PROOF_CHECK);
    int type = next_line ('l');
    if (type == 'i') {
      add_input_clause (type);
      goto PROOF_CHECK;
    } else if (is_input_learn_delete_restore_or_weaken (type)) {
      learn_delete_restore_or_weaken (type);
      goto PROOF_CHECK;
    } else if (type != 's') {
      unexpected_line (type, "'s', 'i', 'l', 'd', 'w' or 'r'");
      goto UNREACHABLE;
    } else if (string == SATISFIABLE)
      goto PROOF_MODEL;
    else if (string == UNSATISFIABLE)
      goto PROOF_CORE;
    else {
      assert (string == UNKNOWN);
      conclude_query (0);
      goto PROOF_INPUT;
    }
  }
  {
    STATE (PROOF_MODEL);
    set_file (proof);
    int type = next_line (0);
    if (type == 'm') {
      save_line (type);
      conclude_satisfiable_query_with_model (type);
      goto PROOF_INPUT;
    } else {
      unexpected_line (type, "'m'");
      goto UNREACHABLE;
    }
  }
  {
    STATE (PROOF_CORE);
    set_file (proof);
    int type = next_line (0);
    if (type == 'u') {
      save_line (type);
      conclude_unsatisfiable_query_with_core (type);
      goto PROOF_INPUT;
    } else {
      unexpected_line (type, "'u'");
      goto UNREACHABLE;
    }
  }
  {
    STATE (END_OF_CHECKING);
    verbose ("successfully reached end-of-checking");
    return res;
  }
  {
    STATE (UNREACHABLE);
    fatal_error ("invalid parser state reached");
    return 1;
  }
}

/*------------------------------------------------------------------------*/

// Memory leaks could be a show-stopper for large proofs.  To find
// memory leaks reclaiming all memory before successfully exiting the
// checker is thus not only good style.  Reclaiming all memory combined
// with memory checkers, e.g., 'configure -a' to compile with ASAN,
// allows to check for memory leaks.  For the linear clause checker we
// use two hash tables to map clause identifiers to clauses, one for
// active and one for inactive clauses.  We traverse those hash tables
// to properly reclaim clauses.

static void release_clauses_in_hash_table (struct hash_table *hash_table) {
  struct clause **table = hash_table->table;
  struct clause **end = table + hash_table->size;
  for (struct clause **p = table; p != end; p++) {
    struct clause *c = *p;
    if (VALID (c) && !c->input)
      free_clause (c);
  }
}

static void release_active_clauses (void) {
  debug ("releasing active clauses");
  release_clauses_in_hash_table (&active);
}

static void release_inactive_clauses (void) {
  debug ("releasing inactive clauses");
  release_clauses_in_hash_table (&inactive);
}

static void release_input_clauses (void) {
  debug ("releasing input clauses");
  for (all_pointers (struct clause, c, input_clauses))
    free_clause (c);
  RELEASE (input_clauses);
}

static void release (void) {
  RELEASE (line.lits);
  RELEASE (line.ids);
  RELEASE (saved);
  RELEASE (query);
  release_active_clauses ();
  release_inactive_clauses ();
  release_input_clauses ();
  if (no_reuse && used.words)
    free (used.words);
  free (active.table);
  free (inactive.table);
  free (trail.begin);
  values -= allocated;
  free (values);
  marks -= allocated;
  free (marks);
  free (imported);
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
  printf ("c %-20s %20zu %12.2f %% lemmas\n", "checks:", statistics.checks,
          percent (statistics.lemmas, statistics.checks));
  printf ("c %-20s %20zu %12.2f %% added\n", "deleted:", statistics.deleted,
          percent (statistics.deleted, statistics.added));
  printf ("c %-20s %20zu %12.2f %% added\n", "inputs:", statistics.inputs,
          percent (statistics.inputs, statistics.added));
  printf ("c %-20s %20zu %12.2f %% added\n", "lemmas:", statistics.lemmas,
          percent (statistics.lemmas, statistics.added));
  printf ("c %-20s %20zu %12.2f %% conclusions\n",
          "models:", statistics.models,
          percent (statistics.models, statistics.conclusions));
  printf ("c %-20s %20zu %12.2f per check\n",
          "resolutions:", statistics.resolutions,
          average (statistics.resolutions, statistics.checks));
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
  printf ("c %-20s %11.2f MB\n", "maximum-resident-set-size:", m);
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
      fputs (lidrup_check_usage, stdout);
      exit (0);
    } else if (!strcmp (arg, "-q") || !strcmp (arg, "--quiet"))
      verbosity = -1;
    else if (!strcmp (arg, "-n") || !strcmp (arg, "--no-reuse"))
      no_reuse = true;
    else if (!strcmp (arg, "-v") || !strcmp (arg, "--verbose"))
      verbosity += (verbosity < INT_MAX);
    else if (!strcmp (arg, "-l") || !strcmp (arg, "--logging"))
#ifndef NDEBUG
      verbosity = INT_MAX;
#else
      die ("invalid line option '%s' (compiled without debugging)", arg);
#endif
    else if (!strcmp (arg, "--version"))
      printf ("%s\n", lidrup_version), exit (0);
    else if (!strcmp (arg, "--strict"))
      mode = strict;
    else if (!strcmp (arg, "--relaxed"))
      mode = relaxed;
    else if (!strcmp (arg, "--pedantic"))
      mode = pedantic;
    else if (arg[0] == '-')
      die ("invalid command line option '%s' (try '-h')", arg);
    else if (num_files < 2)
      files[num_files++].name = arg;
    else
      die ("too many files '%s', '%s' and '%s'", files[0].name,
           files[1].name, arg);
  }

  if (!num_files)
    die ("no file given but expected two (try '-h')");

  if (num_files == 2) {
    interactions = files;
    proof = interactions + 1;
    if (!(files[0].file = fopen (files[0].name, "r")))
      die ("can not read incremental CNF file '%s'", files[0].name);
  } else
    proof = files;

  if (!(proof->file = fopen (proof->name, "r")))
    die ("can not read incremental DRUP proof file '%s'", proof->name);

  message ("Interaction DRUP Checker");
  message ("Copyright (c) 2023 Armin Biere University of Freiburg");
  if (lidrup_gitid)
    message ("Version %s %s", lidrup_version, lidrup_gitid);
  else
    message ("Version %s", lidrup_version);
  message ("Compiler %s", lidrup_compiler);
  message ("Build %s", lidrup_build);

  init_signals ();

  if (verbosity >= 0)
    fputs ("c\n", stdout);

  if (no_reuse)
    message ("checking that all clause identifiers are distincts");
  else
    message ("allowing to reuse deleted clause identifiers");

  if (interactions)
    message ("reading incremental CNF '%s'", interactions->name);
  message ("reading and checking incremental DRUP proof '%s'", proof->name);

  int res;
  if (num_files == 1)
    res = parse_and_check_idrup ();
  else
    res = parse_and_check_icnf_and_idrup ();

  if (verbosity >= 0)
    fputs ("c\n", stdout);
  if (res)
    fputs ("s FAILED\n", stdout);
  else
    fputs ("s VERIFIED\n", stdout);
  fflush (stdout);

  for (int i = 0; i != num_files; i++) {
    if (verbosity > 0) {
      if (!i)
        fputs ("c\n", stdout);
      message ("closing '%s' after reading %zu lines (%zu bytes)",
               files[i].name, files[i].lineno - 1, files[i].charno);
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
