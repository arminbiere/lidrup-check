# Incremental DRUP Checker

This is a proof checker for incremental DRUP.

Run `configure && make test` to configure, compile and test `idrup-check`.

If the configuration script finds `../cadical/build/libcadical.a` and
`../cadical/src/ccadical.h` then `idrup-fuzz` will be compiled and
linked against this CaDiCaL version.
