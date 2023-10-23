// clang-format off

static const char * idrup_check_usage =
"usage: idrup-check [ <option> ... ] <icnf> <answers> <proof>\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"  -h | --help     print command line option summary\n"
"  -q | --quiet    do not print any message beside errors\n"
"  -v | --verbose  print more verbose message too\n"
"\n"
"and '<icnf>' is the incremental CNF file with file clauses and queries\n"
"under assumptions, '<answers>' a file with status reports for queries\n"
"with optional model values and failed assumption justifications and\n."
"finally '<proof>' the incrememental DRUP proof lines.\n"
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

struct ints {
  int *begin, *end, *allocated;
};

struct lines {
  int **begin, **end, **allocated;
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
};

static struct file files[3];
static struct file *file;

static struct ints line;
static struct ints query;

static char buffer[1u << 20];
static size_t end_buffer;
static size_t size_buffer;
static int end_of_file;

static void set_file (struct file *new_file) {
  assert (new_file);
  assert (new_file->file);
  file = new_file;
  end_buffer = size_buffer = 0;
  end_of_file = 0;
}

static int read_char (void) {
  assert (file);
  assert (file->file);
  if (size_buffer == end_buffer) {
    if (end_of_file)
      return EOF;
    end_buffer = fread (buffer, 1, sizeof buffer, file->file);
    if (!end_buffer) {
      end_of_file = 1;
      return EOF;
    }
    size_buffer = 0;
  }
  assert (size_buffer < end_buffer);
  return buffer[size_buffer++];
}

static void parse_error (const char *, ...)
    __attribute__ ((format (printf, 1, 2)));

static void parse_error (const char *fmt, ...) {
  assert (file);
  fprintf (stderr, "idrup-check: parse error: at line %zu in '%s': ",
           file->lineno + 1, file->name);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

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

static int next_line (char default_type) {
  assert (default_type);
  int actual_type = 0;
  CLEAR (line);
  int ch;
  while ((ch = next_char ()) == 'c')
    while ((ch = next_char ()) != '\n')
      if (ch == EOF)
        parse_error ("end-of-file in comment");
  if (ch == EOF)
    return 0;
  if (ch == '\n')
    parse_error ("unexpected empty line");
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
    if (ch == '\n') {
      PUSH (line, 0);
      assert (actual_type);
      return actual_type;
    }
    assert (ch == ' ');
    ch = next_char ();
  }
}

static void print_line (int type) {
  printf ("%c", type);
  for (all_elements (int, lit, line))
    printf (" %d", lit);
  fputc ('\n', stdout);
}

static int next_query (void) {
  set_file (files + 0);
  int type;
  while ((type = next_line ('i')) != 'a' && type != 'q')
    print_line (type);
  print_line ('q');
  return 'q';
}

static void release (void) {
  RELEASE (line);
  RELEASE (query);
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
      verbosity = 1;
    else if (arg[0] == '-')
      die ("invalid command line option '%s' (try '-h')", arg);
    else if (!files[0].name)
      files[0].name = arg;
    else if (!files[1].name)
      files[1].name = arg;
    else if (!files[2].name)
      files[2].name = arg;
    else
      die ("too many files '%s', '%s', '%s' and '%s'", files[0].name,
           files[1].name, files[2].name, arg);
  }
  if (!files[0].name)
    die ("no file given but expected three (try '-h')");
  if (!files[1].name)
    die ("one file '%s' given but expected three (try '-h')",
         files[0].name);
  if (!files[2].name)
    die ("two files '%s' and '%s' given but expected three (try '-h')",
         files[0].name, files[1].name);
  if (!(files[0].file = fopen (files[0].name, "r")))
    die ("can not read incremental CNF file '%s'", files[0].name);
  if (!(files[1].file = fopen (files[1].name, "r")))
    die ("can not read answer file '%s'", files[1].name);
  if (!(files[2].file = fopen (files[2].name, "r")))
    die ("can not read incremental IDRUP proof file '%s'", files[2].name);

  message ("Incremenal Drup Checker Version 0.0");
  message ("reading incremental CNF '%s'", files[0].name);
  message ("reading query answers from '%s'", files[1].name);
  message ("reading and checking incremental DRUP proof '%s'",
           files[2].name);

  int type;
  while ((type = next_query ())) {
    assert (type == 'q');
  }

  for (int i = 0; i != 3; i++) {
    verbose ("closing '%s' after reading %zu lines (%zu bytes)",
             files[i].name, files[i].lineno, files[i].charno);
    fclose (files[i].file);
  }
  release ();
  return 0;
}
