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
"and '<icnf>' is the incremental CNF file with input clauses and queries\n"
"under assumptions, '<answers>' a file with status reports for queries\n"
"with optional model values and failed assumption justifications and\n."
"finally '<proof>' the incrememental DRUP proof lines.\n"
;

// clang-format on

#include <assert.h>
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

#define ALL_STACK(TYPE, E, S) \
  TYPE E, *E##_PTR = BEGIN (S), *const E##_END = END (S); \
  E##_PTR != E##_END && (E = *E##_PTR, true); \
  ++E##_PTR

#define COPY(TYPE, DST, SRC) \
  do { \
    CLEAR (DST); \
    for (ALL_STACK (TYPE, E, SRC)) \
      PUSH (DST, E); \
  } while (0)

struct input {
  FILE *file;
  const char *name;
  size_t lineno, charno;
};

static struct input inputs[3];
static struct input *input;

static struct ints line;
static struct ints query;

static char buffer[1u << 20];
static size_t end_buffer;
static size_t size_buffer;
static int end_of_file;

static void set_input (struct input *new_input) {
  assert (new_input);
  assert (new_input->file);
  input = new_input;
  end_buffer = size_buffer = 0;
  end_of_file = 0;
}

static int read_char (void) {
  assert (file);
  assert (file->file);
  if (size_buffer == end_buffer) {
    if (end_of_file)
      return EOF;
    end_buffer = fread (buffer, 1, sizeof buffer, input->file);
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
           input->lineno + 1, input->name);
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
    input->lineno++;
  if (res != EOF)
    input->charno++;
  return res;
}

static int next_line (char default_type) {
  assert (default_type);
  int actual_type = 0;
  CLEAR (line);
  for (;;) {
    int ch = next_char ();
    if (ch == EOF) {
      if (!EMPTY (line))
        parse_error ("end-of-file in the middle of a line");
      return 0;
    }
    if (ch == 'c') {
      if (!EMPTY (line))
        parse_error ("comment without 'c' as first character of line");
      while ((ch = next_char ()) != '\n')
        if (ch == EOF)
          parse_error ("end-of-file in comment");
      continue;
    }
    if (ch == '\n') {
      if (EMPTY (line))
        parse_error ("empty line");
      PUSH (line, 0);
      return actual_type ? actual_type : default_type;
    }
    if ('a' <= ch && ch <= 'z') {
      if (actual_type || !EMPTY (line))
        parse_error ("misplaced '%c' in line", ch);
      actual_type = ch;
      continue;
    }
    int sign;
    if (ch == '-') {
      ch = next_char ();
      sign = -1;
    } else {
      sign = 1;
    }
    (void) sign;
  }
}

static int next_query (void) {
  set_input (inputs + 0);
  if (!next_line ('i'))
    return 0;
  return 1;
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
    else if (!inputs[0].name)
      inputs[0].name = arg;
    else if (!inputs[1].name)
      inputs[1].name = arg;
    else if (!inputs[2].name)
      inputs[2].name = arg;
    else
      die ("too many inputs '%s', '%s', '%s' and '%s'", inputs[0].name,
           inputs[1].name, inputs[2].name, arg);
  }
  if (!inputs[0].name)
    die ("no file given but expected three (try '-h')");
  if (!inputs[1].name)
    die ("only one file '%s' given but expected three (try '-h')",
         inputs[0].name);
  if (!inputs[2].name)
    die (
        "only two inputs '%s' and '%s' given but expected three (try '-h')",
        inputs[0].name, inputs[1].name);
  if (!(inputs[0].file = fopen (inputs[0].name, "r")))
    die ("can not read incremental CNF file '%s'", inputs[0].name);
  if (!(inputs[1].file = fopen (inputs[1].name, "r")))
    die ("can not read answer file '%s'", inputs[1].name);
  if (!(inputs[2].file = fopen (inputs[2].name, "r")))
    die ("can not read incremental IDRUP proof file '%s'", inputs[2].name);

  message ("Incremenal Drup Checker Version 0.0");
  message ("reading incremental CNF '%s'", inputs[0].name);
  message ("reading query answers from '%s'", inputs[1].name);
  message ("reading and checking incremental DRUP proof '%s'",
           inputs[2].name);

  while (next_query ()) {
  }

  for (int i = 0; i != 3; i++) {
    verbose ("closing '%s' after reading %zu lines (%zu bytes)",
             inputs[i].name, inputs[i].lineno, inputs[i].charno);
    fclose (inputs[i].file);
  }
  release ();
  return 0;
}
