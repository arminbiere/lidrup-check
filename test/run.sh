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
  answers=test/$base.answers
  proof=test/$base.proof
  log=test/$base.log
  err=test/$base.err
  cmd="./$binary $icnf $answers $proof"
  echo "$cmd"
  $cmd 1>$log 2>$err
  actual=$?
  [ $actual = $expected ] || \
    die "exit status '$actual' but expected '$expected'"
  passed=`expr $passed + 1`
}

run 0 empty

echo "all $passed tests passed"
