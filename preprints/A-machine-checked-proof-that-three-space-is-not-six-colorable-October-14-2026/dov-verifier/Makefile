#
# Makefile for C++ verification programs.
#
# You need to have both GMP and MPFR installed!
#

CPPFLAGS = --std=c++11 -Wall -Wno-sign-compare -O2

.PHONY: all clean

all: sn_verify rn_verify

sn_verify: sn_verify.cpp
	$(CXX) $(CPPFLAGS) -o $@ $^ -lgmpxx -lgmp


rn_verify: rn_verify.cpp omega.o
	$(CXX) $(CPPFLAGS) -o $@ $^ -lmpfr -lgmp -lm

omega.o: omega.cpp omega.h

clean:
	$(RM) *.o *~ sn_verify rn_verify
