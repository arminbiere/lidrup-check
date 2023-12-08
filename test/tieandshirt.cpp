#include "cadical.hpp"

#include <cassert>

int main () {
  CaDiCaL::Solver solver;
  solver.set ("idrup", 1);
  solver.set ("binary", 0);
  solver.trace_proof ("tieandshirt.idrup");
  // tie = 1, shirt = 2;
  solver.clause (1, 2);   // tie | shirt
  solver.clause (-1, 2);  // tier -> shirt
  solver.clause (-1, -2); // !(tier & shirt)
  int res = solver.solve ();
  assert (res == 10); // SATISFIABLE
  res = solver.val (1), assert (res == -1);
  res = solver.val (2), assert (res == 2);
  solver.assume (1); // Can I have a tie?
  res = solver.solve ();
  assert (res == 20);      // UNSATISFIABLE
  res = solver.failed (1); // No, and its the tie.
  assert (res);            // 'tie' in the core
  return 0;
}
