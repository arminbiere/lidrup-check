// clang-format off

static const char * idrup_check_usage =
"usage: idrup-check [ <option> ... ] <icnf> <proof>\n"
"\n"
"where '<option>' is one of the following options:\n"
"\n"
"  -h | --help     print command line option summary\n"
"  -q | --quiet    do not print any message beside errors\n"
"  -v | --verbose  print more verbose message too\n"
"  -l | --logging  enable very verbose logging\n"
"\n"
"Exactly two files are read, where '<icnf>' is an incremental CNF file\n"
"augmented with all interactions between the user and the SAT solver.\n"
"The '<proof>' file is meant to be a super-set of the interactions\n"
"but additionally has all the low level proof steps.  The checker makes\n"
"sure the interactions match the proof and all proof steps are justified.\n"
;

// clang-format on

#include <assert.h>
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

// static int merge = 1;
static int verbosity = 0;

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
  } while (false)

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

static struct ints iline;
static struct ints pline;

static struct ints line;
static const char * status;

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
  fprintf (stderr,
           "idrup-check: error: at line %zu in '%s': ",
	   file->start_of_line, file->name);
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
  printf ("c parsed line %zu in '%s': ", file->lineno,
           file->name);
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
      for (const int * p = line.begin; p != line.end; p++)
	printf (" %d", *p);
    break;
  }
  fputc ('\n', stdout);
  fflush (stdout);
}

#else

#define print_parsed_line (...) do { } while (false)

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
  assert (default_type);
  int actual_type = 0;
  CLEAR (line);
  int ch;
  while ((ch = next_char ()) == 'c') {
    debug ("skipping comment line");
    while ((ch = next_char ()) != '\n')
      if (ch == EOF)
        parse_error ("end-of-file in comment");
  }
  if (ch == EOF) {
    debug ("found end-of-line");
    return 0;
  }
  if (ch == '\n')
    parse_error ("unexpected empty line");
  file->start_of_line = file->lineno;
  if ('a' <= ch && ch <= 'z') {
    actual_type = ch;
    if ((ch = next_char ()) != ' ')
      parse_error ("expected space after '%c'", actual_type);
    ch = next_char ();
  } else
    actual_type = default_type;
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
    if (ch == '\n')
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

#if 0

static int next_query (void) {
  set_file_to (icnf);
  for (;;) {
    int type = next_line ('i');
    if (!type)
      return 0;
    if (type == 'a')
      type = 'q';
    else if (type != 'i' && type != 'q')
      type_error ("unexpected '%c' line", type);
    if (merge)
      print_line (type);
    if (type == 'q') {
      COPY (int, query, line);
      return 'q';
    }
  }
}
#endif

static void parse_and_check () {
  int type;
  {
  INTERACTION_INPUT:
    set_file (interactions);
    type = next_line ('i');
    switch (type) {
    case 'i':
      COPY (int, iline, line);
      goto PROOF_INPUT;
    case 'q':
      COPY (int, iline, line);
      goto PROOF_QUERY;
    case 0:
      goto INTERACTION_COMPLETED;
    default:
      type_error ("unexpected '%c' line (expected 'i' or 'q' line)", type);
    }
  }
  {
  INTERACTION_COMPLETED:
    return;
  }
  {
  PROOF_INPUT:
    set_file (proof);
    type = next_line ('i');
    if (type == 'i') {
      if (SIZE (line) != SIZE (iline))
      INPUT_LINE_DOES_NOT_MATCH:
        type_error ("input line does not match");
      const int *const end = iline.end;
      const int *p = iline.begin;
      const int *q = line.begin;
      while (p != end)
        if (*p != *q)
          goto INPUT_LINE_DOES_NOT_MATCH;
        else
          p++, q++;
      goto INTERACTION_INPUT;
    } else if (type)
      type_error ("unexpected '%c' line (expected 'i' line)", type);
    else
      type_error ("unexpected end-of-file (expected 'i' line)");
  }
  {
  PROOF_QUERY:
    set_file (proof);
    type = next_line ('i');
    if (type == 'q') {
      if (SIZE (line) != SIZE (iline))
      QUERY_LINE_DOES_NOT_MATCH:
        type_error ("query line does not match");
      const int *const end = iline.end;
      const int *p = iline.begin;
      const int *q = line.begin;
      while (p != end)
        if (*p != *q)
          goto QUERY_LINE_DOES_NOT_MATCH;
        else
          p++, q++;
      goto INTERACTION_INPUT;
    } else if (type)
      type_error ("unexpected %c line (expected 'q' line)", type);
    else
      type_error ("unexpected end-of-file (expected 'q' line)");
  }
}

static void release (void) {
  RELEASE (line);
  RELEASE (iline);
  RELEASE (pline);
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
      verbosity = INT_MAX;
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

  parse_and_check ();

  for (int i = 0; i != 2; i++) {
    verbose ("closing '%s' after reading %zu lines (%zu bytes)",
             files[i].name, files[i].lineno, files[i].charno);
    fclose (files[i].file);
  }
  release ();
  return 0;
}
