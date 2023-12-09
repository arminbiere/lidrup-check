// This is a simple hard coded bounded model checking example for a two-bit
// counter with (active high) reset and enable signals similar to 'cnt2re'
// in the AIGER and CaMiCaL regression suite.

#include "cadical.hpp"

#include <cassert>
#include <cstdlib>

CaDiCaL::Solver *solver;
FILE *icnf;

#define NAME "cnt2re"

static void start () {
  icnf = fopen (NAME ".icnf", "w");
  fprintf (icnf, "p icnf\n");
  solver = new CaDiCaL::Solver ();
  solver->set ("idrup", 1);
  solver->set ("binary", 0);
  solver->trace_proof (NAME ".idrup");
  printf ("c start bounded model checking\n"), fflush (stdout);
}

void end () {
  delete solver;
  fclose (icnf);
  printf ("c end bounded model checking\n"), fflush (stdout);
}

static void clause (int a) {
  fprintf (icnf, "i %d 0\n", a);
  solver->clause (a);
}

static void clause (int a, int b) {
  fprintf (icnf, "i %d %d 0\n", a, b);
  solver->clause (a, b);
}

static void clause (int a, int b, int c) {
  fprintf (icnf, "i %d %d %d 0\n", a, b, c);
  solver->clause (a, b, c);
}

static void clause (int a, int b, int c, int d) {
  fprintf (icnf, "i %d %d %d %d 0\n", a, b, c, d);
  solver->clause (a, b, c, d);
}

static void clause (int a, int b, int c, int d, int e) {
  fprintf (icnf, "i %d %d %d %d %d 0\n", a, b, c, d, e);
  solver->clause (a, b, c, d, e);
}

static void assume (int a) {
  fprintf (icnf, "q %d 0\n", a);
  solver->assume (a);
}

const static int inputs = 2;
const static int latches = 2;
const static int gates = 1;
const static int frame = inputs + latches + gates;

static int input (int i, int k) { return frame * k + i + 1; }

static int latch (int i, int k) { return frame * k + inputs + i + 1; }

static int gate (int i, int k) {
  return frame * k + inputs + latches + i + 1;
}

static void encode_reset () {
  for (int i = 0; i != latches; i++)
    clause (-latch (i, 0));
}

static void encode_transition (int from, int to) {
  int from_lsb = latch (0, from);
  int to_lsb = latch (0, to);
  int from_msb = latch (1, from);
  int to_msb = latch (1, to);
  int reset = input (0, from);
  int enable = input (1, from);

  // reset -> !from_lsb
  // reset -> !from_msb
  //
  clause (-reset, -to_lsb);
  clause (-reset, -to_msb);

  // !reset && !enable -> to_lsb = from_lsb
  // !reset && !enable -> to_msb = from_msb
  //
  clause (reset, enable, to_lsb, -from_lsb);
  clause (reset, enable, -to_lsb, from_lsb);
  clause (reset, enable, to_msb, -from_msb);
  clause (reset, enable, -to_msb, from_msb);

  // !reset && enable -> to_lsb = !from_lsb
  // !reset && !enable -> to_msb = from_lsb ^ from_msb
  //
  clause (reset, -enable, to_lsb, from_lsb);
  clause (reset, -enable, -to_lsb, -from_lsb);
  clause (reset, -enable, to_msb, from_lsb, -from_msb);
  clause (reset, -enable, to_msb, -from_lsb, from_msb);
  clause (reset, -enable, -to_msb, from_lsb, from_msb);
  clause (reset, -enable, -to_msb, -from_lsb, -from_msb);
}

static int encode_bad (int k) {
  int bad = gate (0, k);
  int lsb = latch (0, k);
  int msb = latch (1, k);
  clause (-bad, lsb);
  clause (-bad, msb);
  clause (bad, -lsb, -msb);
  return bad;
}

static int solve_bound (int k) {
  int bad = encode_bad (k);
  assume (bad);
  fflush (icnf);
  printf ("c encoded bound %d\n", k), fflush (stdout);
  int res = solver->solve ();
  if (res == 10) {
    printf ("c bound %d check satisfiable\n", k), fflush (stdout);
    fputs ("s SATISFIABLE\n", icnf);
    assert (bad > 0);
    fputc ('m', icnf);
    for (int idx = 1; idx <= bad; idx++)
      fprintf (icnf, " %d", solver->val (idx));
    fputs (" 0\n", icnf);
  } else if (res == 20) {
    printf ("c bound %d check unsatisfiable\n", k), fflush (stdout);
    fputs ("s UNSATISFIABLE\n", icnf);
    fputc ('u', icnf);
    if (solver->failed (bad))
      fprintf (icnf, " %d", bad);
    fputs (" 0\n", icnf);
  } else {
    printf ("c bound %d check unknown\n", k), fflush (stdout);
    fputs ("s UNKNOWN\n", icnf);
  }
  fflush (icnf);
  return res;
}

static void encode_and_solve_bound (int k, int expected) {
  if (k)
    encode_transition (k - 1, k);
  else
    encode_reset ();
  int res = solve_bound (k);
  if (res == expected)
    printf ("c solving bound %d returns %d as expected\n", k, expected),
        fflush (stdout);
  else
    fprintf (stderr,
             NAME ".exe: error: "
                  "solving bound %d returned %d but expected %d\n",
             k, res, expected),
        exit (1);
}

int main () {
  start ();
  encode_and_solve_bound (0, 20);
  encode_and_solve_bound (1, 20);
  encode_and_solve_bound (2, 20);
  encode_and_solve_bound (3, 10);
  end ();
  return 0;
}
