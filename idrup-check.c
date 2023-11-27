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
#include <stdarg.h>
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

static const char *const ICNF = "ICNF";
// static const char * const CNF = "CNF"; // TODO
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

static void print_parsed_line (int type) {
  if (verbosity < INT_MAX)
    return;
  assert (file);
  printf ("c parsed line %zu in '%s': ", file->lineno, file->name);
  switch (type) {
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
    break;
  }
  fputc ('\n', stdout);
  fflush (stdout);
}

#else

#define print_parsed_line(...) \
  do { \
  } while (0)

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
    }
    assert (idx != INT_MIN);
    int lit = sign * idx;
    if (ch != ' ' && ch != '\n')
      parse_error ("expected space or new-line after '%d'", lit);
    PUSH (line, lit);
    if (ch == '\n') // TODO what about continued lines (e.g., 'v' lines)?
      return actual_type;
    assert (ch == ' ');
    ch = next_char ();
  }
}

static inline int next_line (char default_type) {
  int type = next_line_without_printing (default_type);
  print_parsed_line (type);
  return type;
}

static void unexpected_line (int type, const char *expected) {
  if (type)
    type_error ("unexpected '%c' line (expected %s line)", type, expected);
  else
    type_error ("unexpected end-of-file (expected %s line)", expected);
}

static void add_input_clause () {}

static void save_query () {}

static void check_implied_and_add_lemma () {}

static void find_active_and_delete () {}

static void find_active_and_weaken () {}

static void find_inactive_and_restore () {}

static void check_values_of_model () {}

static void justify_core () {}

static void match_saved (const char *type_str) {
  if (SIZE (line) != SIZE (saved))
  INPUT_LINE_DOES_NOT_MATCH:
    type_error ("%s line does not match", type_str);
  const int *const end = saved.end;
  const int *p = saved.begin;
  const int *q = line.begin;
  while (p != end)
    if (*p != *q)
      goto INPUT_LINE_DOES_NOT_MATCH;
    else
      p++, q++;
}

static void save_line () { COPY (int, saved, line); }

static int parse_and_check_in_pedantic_mode () {
  verbose ("starting interactions and proof checking in strict mode");
  {
    // INTERACTION_HEADER:
    set_file (interactions);
    int type = next_line (0);
    if (type != 'p')
      unexpected_line (type, "'p'");
    goto INTERACTION_INPUT;
  }
  {
  INTERACTION_INPUT:
    set_file (interactions);
    int type = next_line ('i');
    switch (type) {
    case 'i':
      add_input_clause ();
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
  }
  {
  PROOF_INPUT:
    set_file (proof);
    int type = next_line ('i');
    if (type == 'i') {
      match_saved ("input");
      goto INTERACTION_INPUT;
    } else if (type == 'l')
      check_implied_and_add_lemma ();
    else if (type == 'd')
      find_active_and_delete ();
    else if (type == 'r')
      find_inactive_and_restore ();
    else
      unexpected_line (type, "'i', 'l', 'd', or 'r'");
  }
  {
  PROOF_QUERY:
    set_file (proof);
    int type = next_line (0);
    if (type != 'q')
      unexpected_line (type, "'q'");
    match_saved ("query");
    goto PROOF_CHECK;
  }
  {
  PROOF_CHECK:
    set_file (proof);
    int type = next_line ('l');
    if (type == 'l') {
      check_implied_and_add_lemma ();
      goto PROOF_CHECK;
    } else if (type == 'd') {
      find_active_and_delete ();
      goto PROOF_CHECK;
    } else if (type == 'r') {
      find_inactive_and_restore ();
      goto PROOF_CHECK;
    } else if (type == 'w') {
      find_active_and_weaken ();
      goto PROOF_CHECK;
    } else if (type != 's')
      unexpected_line (type, "'s'");
    else if (status == SATISFIABLE)
      goto INTERACTION_SATISFIABLE;
    else
      goto INTERACTION_UNSATISFIABLE;
  }
  {
  INTERACTION_SATISFIABLE:
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
  INTERACTION_UNSATISFIABLE:
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
  INTERACTION_SATISFIED:
    set_file (interactions);
    int type = next_line (0);
    if (type != 'v')
      unexpected_line (type, "'v'");
    goto PROOF_VALUES;
  }
  {
  PROOF_VALUES:
    set_file (proof);
    int type = next_line (0);
    if (type != 'v')
      unexpected_line (type, "'v'");
    check_values_of_model ();
    goto INTERACTION_INPUT;
  }
  {
  INTERACTION_UNSATISFIED:
    set_file (interactions);
    int type = next_line (0);
    if (type != 'j')
      unexpected_line (type, "'j'");
    goto PROOF_JUSTIFY;
  }
  {
  PROOF_JUSTIFY:
    set_file (proof);
    int type = next_line (0);
    if (type != 'j')
      unexpected_line (type, "'j'");
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

  message ("Incremental DRUP Checker Version 0.0.0");
  message ("Copyright (c) 2023 University of Freiburg");
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

  for (int i = 0; i != 2; i++) {
    verbose ("closing '%s' after reading %zu lines (%zu bytes)",
             files[i].name, files[i].lineno, files[i].charno);
    fclose (files[i].file);
  }
  release ();
  return res;
}
