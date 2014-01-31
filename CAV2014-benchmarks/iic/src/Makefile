-include ../Make.config

LIBSOURCES=exceptions.cpp parallelization.cpp parser_interface.cpp \
	   vass_global_state.cpp iic_algorithm.cpp io_helper.cpp \
	   solver_petri_net.cpp vass_state_sets.cpp error.c laparser.c \
	   tbsymbol.c tbsymbolinfo.c tree.c xmalloc.c lexer.l parser.y
MAINSOURCES=iic.cpp

LIBCSOURCES=$(patsubst %.y,%.c,$(patsubst %.l,%.c,$(LIBSOURCES)))

LIBOBJECTS=$(patsubst %.cpp,%.o,$(patsubst %.c,%.o,$(LIBCSOURCES)))
MAINOBJECTS=$(patsubst %.cpp,%.o,$(MAINSOURCES))
TESTOBJECTS=$(patsubst %.cpp,%.o,$(TESTSOURCES))

BINARIES=ic3wsts $(patsubst %.o,%,$(TESTOBJECTS))

all: $(BINARIES)

.PHONY: depend
.depend depend: $(LIBCSOURCES) $(MAINSOURCES) $(TESTSOURCES)
	$(CC) -MM $^ >.depend

libic3wsts.a: $(LIBOBJECTS)
	ar cru $@ $(LIBOBJECTS)

ic3wsts: libic3wsts.a $(MAINOBJECTS)
	$(CXX) -o $@ $(LDFLAGS) $(MAINOBJECTS) libic3wsts.a $(LIBS)

test%: test%.o libic3wsts.a
	$(CXX) -o $@ $(LDFLAGS) $< libic3wsts.a $(LIBS) -lboost_unit_test_framework

%.c %.h: %.y
	yacc -d $<
	-mv y.tab.c $*.c
	-mv y.tab.h $*.h

%.c: %.l
	lex -t $< >$@

lexer.o: lexer.c parser.h

clean:
	rm -f $(BINARIES) $(LIBOBJECTS) $(MAINOBJECTS) libic3wsts.a

-include .depend
	
