.SUFFIXES: .cpp .exe
.cpp.exe:
	g++ -o $@ $< -I../../cadical/src ../../cadical/build/libcadical.a -lm
SRC=$(wildcard *.cpp)
PRG=$(SRC:.cpp=.exe)
all: $(PRG)
	for i in $(PRG); do ./$$i; done
	./run.sh
clean:
	rm -f *.log *.err *.exe
.PHONY: all clean
