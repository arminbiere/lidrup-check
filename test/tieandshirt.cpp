#include "cadical.hpp"

#include <cassert>

int main () {
  CaDiCaL::Solver solver;
  solver.set ("idrup", 1);
  solver.set ("binary", 0);
  solver.trace_proof ("tieandshirt.idrup");
  // tie = 1, shirt = 2;
  solver.clause (1, 2);
  solver.clause (-1, 2);
  solver.clause (-1, -2);
  int res = solver.solve ();
  assert (res == 10); // SATISFIABLE
  solver.assume (1);
  res = solver.solve ();
  assert (res == 20); // UNSATISFIABLE
  res = solver.failed (1);
  assert (res); // 'tie' in the core
  return 0;
}
