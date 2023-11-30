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
"\n"
"Exactly two files are read. The first '<icnf>' is an incremental CNF file\n"
"augmented with all interactions between the user and the SAT solver.\n"
"Thus the letter 'i' is overloaded and means both 'incremental' and\n"
"'interactions'. The second '<idrup>' file is meant to be a super-set of\n"
"the interactions file but additionally has all the low level proof steps.\n"
"\n"
"The checker makes sure the interactions match the proof and all proof\n"
"steps are justified. This is only the case though for the default\n"
"'pedantic' and the 'strict' mode.  Checking is less strict in 'relaxed'\n"
"mode where conclusion missing in the proof will be skipped.  Still the\n"
"exit code will only be zero if all checks go through and thus the\n"
"interactions are all checked.\n"
"\n"
"These modes can can be set explicitly as follows:\n"
"\n"
"  --strict    strict mode (requires 'v' and 'j' lines in proof only)\n"
"  --relaxed   relaxed mode (missing 'v' and 'j' proof lines ignored)\n"
"  --pedantic  pedantic mode (requires 'v' and 'j' in both files\n"
;

// clang-format on

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

static void out_of_memory (const char *fmt, ...) {
  fputs ("idrup-check: error: out-of-memory ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static int verbosity = 0;

enum {
  strict = 0,
  relaxed = -1,
  pedantic = 1,
};

static int mode = pedantic;

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

#ifndef NDEBUG

#define debug(...) \
  do { \
    if (verbosity == INT_MAX) \
      message ("DEBUG " __VA_ARGS__); \
  } while (0)

#else

#define debug(...) \
  do { \
  } while (0)

#endif

struct ints {
  int *begin, *end, *allocated;
};

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

#define all_elements(TYPE, E, S) \
  TYPE E, *E##_PTR = BEGIN (S), *const E##_END = END (S); \
  E##_PTR != E##_END && (E = *E##_PTR, 1); \
  ++E##_PTR

#define COPY(TYPE, DST, SRC) \
  do { \
    CLEAR (DST); \
    for (all_elements (TYPE, E, SRC)) \
      PUSH (DST, E); \
  } while (0)

struct file {
  FILE *file;
  const char *name;
  size_t lineno, charno;
  size_t start_of_line;
  size_t end_buffer;
  size_t size_buffer;
  int end_of_file;
  char buffer[1u << 20];
};

static struct file files[2];
static struct file *interactions = files + 0;
static struct file *proof = files + 1;
static struct file *file;

static struct ints saved;
static struct ints line;

static const char *const SATISFIABLE = "SATISFIABLE";
static const char *const UNSATISFIABLE = "UNSATISFIABLE";
static const char *status;

static const char *const ICNF = "icnf";
// static const char * const CNF = "cnf"; // TODO
static const char *cnf_file_type;

static inline void set_file (struct file *new_file) {
  assert (new_file);
  assert (new_file->file);
  file = new_file;
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

static void type_error (const char *, ...)
    __attribute__ ((format (printf, 1, 2)));

static void type_error (const char *fmt, ...) {
  assert (file);
  fprintf (stderr, "idrup-check: error: at line %zu in '%s': ",
           file->start_of_line + 1, file->name);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

#ifndef NDEBUG

static void debug_print_parsed_line (int type) {
  if (verbosity < INT_MAX)
    return;
  assert (file);
  printf ("c DEBUG parsed line %zu in '%s': ", file->lineno, file->name);
  switch (type) {
  case 'p':
    fputs ("p ", stdout);
    assert (cnf_file_type);
    fputs (cnf_file_type, stdout);
    break;
  case 's':
    fputs ("s ", stdout);
    assert (status);
    fputs (status, stdout);
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

#endif

static int next_char (void) {
  int res = read_char ();
  if (res == '\r') {
    res = read_char ();
    if (res != '\n')
      parse_error ("expected new-line after carriage return");
  }
  if (res == '\n')
    file->lineno++;
  if (res != EOF)
    file->charno++;
  return res;
}

static int ISDIGIT (int ch) { return '0' <= ch && ch <= '9'; }

static int next_line_without_printing (char default_type) {
  int actual_type = 0;
  CLEAR (line);
  file->start_of_line = file->lineno;
  int ch;
RESTART:
  while ((ch = next_char ()) == 'c') {
    while ((ch = next_char ()) != '\n')
      if (ch == EOF)
        parse_error ("end-of-file in comment");
#ifndef NDEBUG
    if (verbosity == INT_MAX)
      message ("skipped line %zu in '%s': c...", file->start_of_line + 1,
               file->name);
#endif
  }
  if (ch == EOF) {
#ifndef NDEBUG
    if (verbosity == INT_MAX)
      message ("parsed end-of-file in '%s' after %zu lines", file->name,
               file->lineno);
#endif
    return 0;
  }
  if (ch == '\n') {
    message ("skipping empty line %zu in '%s'", file->start_of_line + 1,
             file->name);
    goto RESTART;
  }

  if (ch == 'p') {
    for (const char *p = " icnf"; *p; p++)
      if (next_char () != *p)
        parse_error ("invalid 'p' header line");
    if (next_char () != '\n')
      parse_error ("expected new line after 'p icnf' header");
    cnf_file_type = ICNF;

    // TODO parse 'p cnf <vars> <clauses>' header too.
    // TODO parse 'p idrup' header?

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
      status = SATISFIABLE;
    } else if (ch == 'U') {
      for (const char *p = "NSATISFIABLE"; *p; p++)
        if (*p != next_char ())
          goto INVALID_STATUS_LINE;
      if (next_char () != '\n')
        goto EXPECTED_NEW_LINE_AFTER_STATUS;
      status = UNSATISFIABLE;
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
    type_error ("unexpected '%c' line (expected %s line)", type, expected);
  else
    type_error ("unexpected end-of-file (expected %s line)", expected);
}

static struct {
  size_t added;
  size_t conclusions;
  size_t decisions;
  size_t deleted;
  size_t inputs;
  size_t imported;
  size_t justifications;
  size_t lemmas;
  size_t models;
  size_t propagations;
  size_t queries;
  size_t restored;
  size_t weakened;
} statistics;

struct clause {
#ifndef NDEBUG
  size_t id, lineno;
#endif
  unsigned size;
  bool active;
  bool input;
  int lits[];
};

#define begin_literals(C) ((C)->lits)
#define end_literals(C) (begin_literals (C) + (C)->size)
#define all_literals(LIT, C) \
  int LIT, *P_##LIT = begin_literals (C), *END_##LIT = end_literals (C); \
  P_##LIT != END_##LIT && (LIT = *P_##LIT, true); \
  P_##LIT++

struct watches {
  struct clause **begin, **end, **allocated;
};

static int max_var;
static size_t allocated;

static struct watches *matrix;
static signed char *values;
static bool *imported;

static struct ints trail;
// static size_t propagate;

static void import_literal (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  int idx = abs (lit);
  if (idx <= max_var)
    return;
  if (idx == INT_MAX)
    parse_error ("can not handle INT_MAX variables");
  if (idx > max_var) {
    debug ("new maximum variable index %d", idx);
    if ((unsigned) idx >= allocated) {
      size_t new_allocated = allocated ? 2 * allocated : 1;
      while ((unsigned) idx >= new_allocated)
        new_allocated *= 2;
      debug ("reallocating from %zu to %zu variables", allocated,
             new_allocated);

      struct watches *new_matrix =
          calloc (2 * new_allocated, sizeof *new_matrix);
      new_matrix += new_allocated;
      if (max_var)
        for (int lit = -max_var; lit <= max_var; lit++)
          new_matrix[lit] = matrix[lit];
      matrix -= allocated;
      free (matrix);
      matrix = new_matrix;

      signed char *new_values =
          calloc (2 * new_allocated, sizeof *new_values);
      new_values += new_allocated;
      if (max_var)
        for (int lit = -max_var; lit <= max_var; lit++)
          new_values[lit] = values[lit];
      values -= allocated;
      free (values);
      values = new_values;

      bool *new_imported = calloc (new_allocated, sizeof *new_imported);
      for (int idx = 1; idx <= max_var; idx++)
        new_imported[idx] = imported[idx];
      free (imported);
      imported = new_imported;
      allocated = new_allocated;
    }
    max_var = idx;
  }
  if (!imported[idx]) {
    imported[idx] = true;
    statistics.imported++;
    debug ("imported variable %d", idx);
  }
}

static void import_literals () {
  debug ("importing literals");
  for (all_elements (int, lit, line))
    import_literal (lit);
}

static void literal_imported (int lit) {}

static void literals_imported () {
  debug ("checking literals imported");
  for (all_elements (int, lit, line))
    literal_imported (lit);
}

#ifndef NDEBUG

#define capacity_debug_buffer 2
#define debug_buffer_line_size 64

static char debug_buffer[capacity_debug_buffer][debug_buffer_line_size];
static size_t next_debug_buffer_position;

static char *next_debug_buffer () {
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
  if (c->input)
    fputs (" input", stdout);
  else
    fputs (" lemma", stdout);
  if (!c->active)
    fputs (" inactive", stdout);
  printf (" size %u line %zu clause[%zu]", c->size, c->lineno, c->id);
  for (all_literals (lit, c))
    printf (" %s", debug_literal (lit));
  fputc ('\n', stdout);
  fflush (stdout);
}

#else
#define debug_clause(...) \
  do { \
  } while (false)
#endif

static void add_clause (bool input) {
  size_t size = SIZE (line);
  if (size > UINT_MAX)
    parse_error ("maximum clause size exhausted");
  size_t lits_bytes = size * sizeof (int);
  size_t all_bytes = sizeof (struct clause) + lits_bytes;
  struct clause *c = malloc (all_bytes);
  if (!c)
    out_of_memory ("allocating clause of size %zu", size);
  assert (file);
#ifndef NDEBUG
  c->lineno = file->start_of_line + 1;
  c->id = statistics.added;
#endif
  c->size = size;
  c->active = true;
  c->input = input;
  memcpy (c->lits, line.begin, lits_bytes);
  statistics.added++;
  debug_clause (c, "added");
}

static void save_query () {
  debug ("saving query");
  statistics.queries++;
}

static void check_implied () { debug ("checking implied"); }

static struct clause *find_clause (bool active) {
  debug ("finding clause");
  return 0;
}

static void delete_clause (struct clause *) { debug ("deleting clause"); }

static void weaken_clause (struct clause *) { debug ("weakening clause"); }

static void restore_clause (struct clause *c) {
  debug ("restoring clause");
}

static void check_model () {
  debug ("checking model");
  statistics.conclusions++;
  statistics.models++;
}

static void justify_core () {
  debug ("justifying core");
  statistics.conclusions++;
  statistics.justifications++;
}

static void consistent_line () { debug ("checking consistency"); }

static void subset_saved () { debug ("checking subset saved"); }

static void superset_saved () { debug ("checking superset saved"); }

static void import_add_input () {
  import_literals ();
  add_clause (true);
  statistics.inputs++;
}

static void import_check_add_lemma () {
  import_literals ();
  check_implied ();
  add_clause (false);
  statistics.lemmas++;
}

static void imported_find_delete_clause () {
  literals_imported ();
  struct clause *c = find_clause (true);
  delete_clause (c);
  statistics.deleted++;
}

static void imported_find_restore_clause () {
  literals_imported ();
  struct clause *c = find_clause (false);
  restore_clause (c);
  statistics.restored++;
}

static void imported_find_weaken_clause () {
  literals_imported ();
  struct clause *c = find_clause (true);
  weaken_clause (c);
  statistics.weakened++;
}

static bool is_learn_delete_restore_or_weaken (int type) {
  return type == 'l' || type == 'd' || type == 'r' || type == 'w';
}

static void learn_delete_restore_or_weaken (int type) {
  if (type == 'l')
    import_check_add_lemma ();
  else if (type == 'd')
    imported_find_delete_clause ();
  else if (type == 'r')
    imported_find_restore_clause ();
  else {
    assert (type == 'w');
    imported_find_weaken_clause ();
  }
}

static void match_saved (const char *type_str) {
  debug ("matching saved line");
  if (SIZE (line) != SIZE (saved))
  SAVED_LINE_DOES_NOT_MATCH:
    type_error ("%s line does not match", type_str);
  const int *const end = saved.end;
  const int *p = saved.begin;
  const int *q = line.begin;
  while (p != end)
    if (*p != *q)
      goto SAVED_LINE_DOES_NOT_MATCH;
    else
      p++, q++;
}

static void save_line () {
  debug ("saving line");
  COPY (int, saved, line);
}

#ifndef NDEBUG
#define STATE(NAME) \
  goto NAME; \
  NAME: \
  if (verbosity == INT_MAX) \
    fputs ("c DEBUG STATE " #NAME " \n", stdout);
#else
#define STATE(NAME) \
  goto NAME; \
  NAME:
#endif

static int parse_and_check_in_pedantic_mode () {
  verbose ("starting interactions and proof checking in strict mode");
  {
    STATE (INTERACTION_HEADER)
    set_file (interactions);
    int type = next_line (0);
    if (type != 'p')
      unexpected_line (type, "'p'");
    goto INTERACTION_INPUT;
  }
  {
    STATE (INTERACTION_INPUT)
    set_file (interactions);
    int type = next_line ('i');
    switch (type) {
    case 'i':
      import_add_input ();
      save_line ();
      goto PROOF_INPUT;
    case 'q':
      save_query ();
      save_line ();
      goto PROOF_QUERY;
    case 0:
      verbose ("finished interactions and proof checking in strict mode");
      return 0;
    default:
      unexpected_line (type, "'i' or 'q'");
    }
    goto PROOF_INPUT;
  }
  {
    STATE (PROOF_INPUT)
    set_file (proof);
    int type = next_line ('i');
    if (type == 'i')
      match_saved ("input");
    else if (!is_learn_delete_restore_or_weaken (type))
      unexpected_line (type, "'i', 'l', 'd', 'r' or 'w'");
    else {
      learn_delete_restore_or_weaken (type);
      goto PROOF_INPUT;
    }
    goto INTERACTION_INPUT;
  }
  {
    STATE (PROOF_QUERY)
    set_file (proof);
    int type = next_line (0);
    if (type == 'q') {
      match_saved ("query");
      goto PROOF_CHECK;
    }
    if (!is_learn_delete_restore_or_weaken (type))
      unexpected_line (type, "'q', 'l', 'd', 'r' or 'w'");
    else
      learn_delete_restore_or_weaken (type);
    goto PROOF_QUERY;
  }
  {
    STATE (PROOF_CHECK)
    set_file (proof);
    int type = next_line ('l');
    if (is_learn_delete_restore_or_weaken (type)) {
      learn_delete_restore_or_weaken (type);
      goto PROOF_CHECK;
    } else if (type != 's')
      unexpected_line (type, "'s', 'l', 'd', 'r' or 'w'");
    else if (status == SATISFIABLE)
      goto INTERACTION_SATISFIABLE;
    else
      goto INTERACTION_UNSATISFIABLE;
  }
  {
    STATE (INTERACTION_SATISFIABLE)
    set_file (interactions);
    int type = next_line (0);
    if (type != 's')
      unexpected_line (type, "'s'");
    if (status != SATISFIABLE)
      type_error ("unexpected 's %s' line (expected 's SATISFIABLE')",
                  status);
    goto INTERACTION_SATISFIED;
  }
  {
    STATE (INTERACTION_UNSATISFIABLE)
    set_file (interactions);
    int type = next_line (0);
    if (type != 's')
      unexpected_line (type, "'s'");
    if (status != UNSATISFIABLE)
      type_error ("unexpected 's %s' line (expected 's UNSATISFIABLE')",
                  status);
    goto INTERACTION_UNSATISFIED;
    ;
  }
  {
    STATE (INTERACTION_SATISFIED)
    set_file (interactions);
    int type = next_line (0);
    if (type != 'v')
      unexpected_line (type, "'v'");
    consistent_line ();
    save_line ();
    goto PROOF_VALUES;
  }
  {
    STATE (PROOF_VALUES)
    set_file (proof);
    int type = next_line (0);
    if (type != 'v')
      unexpected_line (type, "'v'");
    consistent_line ();
    superset_saved ();
    check_model ();
    goto INTERACTION_INPUT;
  }
  {
    STATE (INTERACTION_UNSATISFIED)
    set_file (interactions);
    int type = next_line (0);
    if (type != 'j')
      unexpected_line (type, "'j'");
    consistent_line ();
    save_line ();
    goto PROOF_JUSTIFY;
  }
  {
    STATE (PROOF_JUSTIFY)
    set_file (proof);
    int type = next_line (0);
    if (type != 'j')
      unexpected_line (type, "'j'");
    consistent_line ();
    subset_saved ();
    justify_core ();
    goto INTERACTION_INPUT;
  }
}

static int parse_and_check_in_strict_mode () {
  die ("strict checking mode not implemented yet");
  return 1;
}

static int parse_and_check_in_relaxed_mode () {
  die ("relaxed checking mode not implemented yet");
  return 1;
}

static void release (void) {
  RELEASE (line);
  RELEASE (saved);
  RELEASE (trail);
  values -= allocated;
  free (values);
  for (int lit = -max_var; lit != max_var; lit++)
    free (matrix[lit].begin);
  matrix -= allocated;
  free (matrix);
  free (imported);
}

#include <sys/resource.h>
#include <sys/time.h>
#include <unistd.h>

static double process_time () {
  struct rusage u;
  double res;
  (void) getrusage (RUSAGE_SELF, &u);
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
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

static void print_statistics () {
  double t = process_time ();
  printf ("c %-20s %20zu %12.2f per variable\n", "added:", statistics.added,
          average (statistics.added, statistics.imported));
  printf ("c %-20s %20zu %12.2f %% queries\n",
          "conclusions:", statistics.conclusions,
          percent (statistics.conclusions, statistics.queries));
  printf ("c %-20s %20zu %12.2f per lemma\n",
          "decisions:", statistics.decisions,
          average (statistics.decisions, statistics.lemmas));
  printf ("c %-20s %20zu %12.2f %% added\n", "deleted:", statistics.deleted,
          percent (statistics.deleted, statistics.added));
  printf ("c %-20s %20zu %12.2f %% added\n", "inputs:", statistics.inputs,
          percent (statistics.inputs, statistics.added));
  printf ("c %-20s %20zu %12.2f %% conclusions\n",
          "justifications:", statistics.justifications,
          percent (statistics.justifications, statistics.conclusions));
  printf ("c %-20s %20zu %12.2f %% added\n", "lemmas:", statistics.lemmas,
          percent (statistics.lemmas, statistics.added));
  printf ("c %-20s %20zu %12.2f %% conclusions\n",
          "models:", statistics.models,
          percent (statistics.models, statistics.conclusions));
  printf ("c %-20s %20zu %12.2f per decision\n",
          "propagations:", statistics.propagations,
          average (statistics.propagations, statistics.decisions));
  printf ("c %-20s %20zu %12.2f per second\n",
          "queries:", statistics.queries, average (t, statistics.queries));
  printf ("c %-20s %20zu %12.2f %% weakened\n",
          "restored:", statistics.restored,
          percent (statistics.restored, statistics.weakened));
  printf ("c %-20s %20zu %12.2f %% inputs\n",
          "weakened:", statistics.weakened,
          percent (statistics.weakened, statistics.inputs));
  fputs ("c\n", stdout);
  double m = mega_bytes ();
  printf ("c %-20s %33.2f seconds\n", "process-time:", t);
  printf ("c %-20s %25.2f MB\n", "bymaximum-resident-set-size:", m);
  fflush (stdout);
}

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

static void reset_signals () {
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

static void init_signals () {
#define SIGNAL(SIG) saved_##SIG##_handler = signal (SIG, catch_signal);
  SIGNALS
}

int main (int argc, char **argv) {
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

  message ("Interaction DRUP Checker Version 0.0.0");
  message ("Copyright (c) 2023 University of Freiburg");

  init_signals ();

  if (verbosity >= 0)
    fputs ("c\n", stdout);
  message ("reading incremental CNF '%s'", files[0].name);
  message ("reading and checking incremental DRUP proof '%s'",
           files[1].name);

  int res;
  if (mode == strict)
    res = parse_and_check_in_strict_mode ();
  else if (mode == pedantic)
    res = parse_and_check_in_pedantic_mode ();
  else
    res = parse_and_check_in_relaxed_mode ();

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
