#!/bin/sh
VERSION="`cat VERSION`"
if [ -d .git -a .git/config ] 
then
  GITID="`git rev-parse --short HEAD`"
  VERSION="$VERSION-$GITID"
fi
NAME=idrup-check-$VERSION
DIR=/tmp/$NAME
ARCHIVE=$DIR.tar.xz
rm -rf $DIR
mkdir $DIR || exit 1
mkdir $DIR/test/ || exit 1
cp -p \
configure \
idrup-build.c \
idrup-build.h \
idrup-check.c \
idrup-check-pedantic-clear.dot \
idrup-check-pedantic-clear.pdf \
idrup-fuzz.c \
LICENSE \
makefile.in \
mkconfig.sh \
README.md \
VERSION \
$DIR/
cp -p \
test/*.cpp \
test/*.icnf \
test/*.idrup \
test/makefile \
test/run.sh \
$DIR/test
cd /tmp/
tar cJf $ARCHIVE $NAME
rm -rf $DIR
echo $ARCHIVE
