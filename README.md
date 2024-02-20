# Linear Incremental DRUP Checker

This is a proof checker for the linear incremental DRUP proof format.

Run `configure && make test` to configure, compile and test `idrup-check`.

If the configuration script finds `../cadical/build/libcadical.a` and
`../cadical/src/ccadical.h` then `idrup-fuzz` will be compiled and
linked against this CaDiCaL version.
