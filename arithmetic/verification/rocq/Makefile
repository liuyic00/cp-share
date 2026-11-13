COQMAKEFILE ?= coq_makefile
COQCHK_STACK_KB ?= 65536
SOURCES := $(sort $(wildcard Generated/*.v) $(wildcard Proofs/*.v))
.PHONY: all clean check
all: Makefile.coq
	$(MAKE) -f Makefile.coq all
Makefile.coq: Makefile $(SOURCES)
	$(COQMAKEFILE) -Q Generated Generated -Q Proofs Proofs $(SOURCES) -o $@
check: all
	ulimit -s $(COQCHK_STACK_KB); coqchk -silent -Q Generated Generated -Q Proofs Proofs $(patsubst Proofs/%.v,Proofs.%,$(wildcard Proofs/*.v))
clean:
	if test -f Makefile.coq; then $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq Makefile.coq.conf
