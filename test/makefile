all:
	./run.sh
tieandshirt: tieandshirt.cpp
	g++ -o $@ $< -I../../cadical/src ../../cadical/build/libcadical.a -lm
clean:
	rm -f *.log *.err tieandshirt
.PHONY: all clean
