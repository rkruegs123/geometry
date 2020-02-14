LEANC=leanc
LEAN=lean
COMMON_SRCS = Util.lean Background/Real.lean Background/Set.lean Background/Nat.lean Background/List.lean Background/Vec.lean Background/Tuple.lean Arith/CRing.lean Arith/Field.lean Geo/Analytic.lean Geo/Core.lean Problems/IMO_2019_P6.lean Problems/IMO_2019_P2.lean Problems/IMO_2018_P1.lean Test/TestCRing.lean Test/TestField.lean
SRCS = $(COMMON_SRCS) Test.lean
OLEANS = $(SRCS:.lean=.olean)
CPPS = $(SRCS:.lean=.cpp)
COMMON_OBJS = $(COMMON_SRCS:.lean=.o)
DEPS = $(SRCS:.lean=.depend)
CPPFLAGS = -O3

.PHONY: all clean

all: test $(OLEANS)

depends: $(DEPS)

%.depend: %.lean
	@echo $(<:.lean=.olean): `$(LEAN) --deps $< | python relative.py` > $@

%.olean: %.lean %.depend
	$(LEAN) --make --cpp="$*.cpp.tmp" $<
	mv "$*.cpp.tmp" "$*.cpp"
	@touch $*.olean

%.cpp: %.olean
	@

%.o: %.cpp
	$(LEANC) -c $(CPPFLAGS) -o $@ $<

test: Test.o $(COMMON_OBJS)
	$(LEANC) -o $@ $^

clean:
	rm -f *~ *#* *.olean *.cpp *.o *.depend
	rm -f */*~ */*#* */*.olean */*.cpp */*.o */*.depend
	rm -f */*/*/~ */*/*#* */*/*.olean */*/*.cpp */*/*.o */*/*.depend
	rm -f */*/*/*/~ */*/*/*#* */*/*/*.olean */*/*/*.cpp */*/*/*.o */*/*/*.depend
	rm -f */*/*/*/*/~ */*/*/*/*#* */*/*/*/*.olean */*/*/*/*.cpp */*/*/*/*.o */*/*/*/*.depend
	rm -f test

.PRECIOUS: %.depend %.cpp

include $(DEPS)
