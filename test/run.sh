#!/bin/sh

die () {
  echo "test/run.sh: error: $*" 1>&2
  exit 1
}

cd `dirname $0` || die "could not change to 'test' directory"
cd .. || die "could not change back to 'test/..'"

binary=idrup-check

[ -f ./$binary ] || die "could not find '$binary' binary"

passed=0

run () {
  expected=$1
  shift
  base="$1"
  icnf=test/$base.icnf
  proof=test/$base.idrup
  log=test/$base.log
  err=test/$base.err
  cmd="./$binary $icnf $proof"
  printf "%s" "$cmd"
  $cmd 1>$log 2>$err
  actual=$?
  if [ ! $actual = $expected ]
  then
    echo " # FAILED"
    die "exit status '$actual' but expected '$expected'"
  fi
  if test $actual = 0
  then
    echo " # succeeded"
  else
    echo " # failed as expected"
  fi
  passed=`expr $passed + 1`
}

run 0 empty
run 0 unit0
run 0 unit1
run 0 taut
run 0 full1
run 0 full2
run 0 full3
run 0 ifull1
run 0 ifull2
run 0 ifull3
run 0 tieandshirt
run 0 inputlearn1
run 0 example1
run 0 example2
run 0 example3
run 0 dp2
run 0 dp3
run 0 dp4

run 0 regr1
run 0 regr2

run 0 cnt2re

run 1 litnotincore

echo "all $passed tests passed"
