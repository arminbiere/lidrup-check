// clang-format off

static const char * idrup_check_usage =
"usage: idrup-check [ <option> ... ] <icnf> <answers> <proof>\n"
;

// clang-format on

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void die(const char *, ...) __attribute__((format(printf, 1, 2)));

static void die(const char *fmt, ...) {
  fputs("idrup-check: error: ", stderr);
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

struct {
  const char *name;
  FILE *file;
} files[3];

int main(int argc, char **argv) {
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "-h") || !strcmp(arg, "--help")) {
      fputs(idrup_check_usage, stdout);
      exit(0);
    } else if (!files[0].name)
      files[0].name = arg;
    else if (!files[1].name)
      files[1].name = arg;
    else if (!files[2].name)
      files[2].name = arg;
    else
      die("too many files '%s', '%s', '%s' and '%s'", files[0].name,
	  files[1].name, files[2].name, arg);
  }
  if (!files[0].name)
    die("no file given but expected three (try '-h')");
  if (!files[1].name)
    die("only one file '%s' given but expected three (try '-h')",
	files[0].name);
  if (!files[2].name)
    die("only two files '%s' and '%s' given but expected three (try '-h')",
	files[0].name, files[1].name);
  if (!(files[0].file = fopen(files[0].name, "r")))
    die("can not read incremental CNF file '%s'", files[0].name);
  if (!(files[1].file = fopen(files[1].name, "r")))
    die("can not read answer file '%s'", files[1].name);
  if (!(files[2].file = fopen(files[2].name, "r")))
    die("can not read incremental IDRUP proof file '%s'", files[2].name);
  for (int i = 0; i != 3; i++)
    fclose (files[i].file);
  return 0;
}
