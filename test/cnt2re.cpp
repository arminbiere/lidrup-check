
#include "cadical.hpp"

#include <cassert>

CaDiCaL::Solver * solver;
FILE * icnf;

static void init () {
  icnf = fopen ("cnt2re.icnf", "w");
  fprintf (icnf, "p icnf\n");
  solver = new CaDiCaL::Solver ();
  solver->set ("idrup", 1);
  solver->set ("binary", 0);
  solver->trace_proof ("cnt2re.idrup");
  printf ("init");
}

void reset () {
  delete solver;
  fclose (icnf);
  printf ("reset");
}

bool encode_and_solve_bound (int k) {
  assert (k >= 0);
  if (k) {
  }
  return false;
}

int main () {
  init ();
  assert (!encode_and_solve_bound (0));
  assert (!encode_and_solve_bound (1));
  assert (!encode_and_solve_bound (2));
  assert (encode_and_solve_bound (3));
  reset ();
  return 0;
}
