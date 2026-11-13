ROCQ ?= rocq
SOURCES := $(sort $(wildcard Generated/*.v) $(wildcard Proofs/*.v))
REFERENCE_INPUTS := $(wildcard ../rocq/Generated/*.v ../rocq/Proofs/*.v)
LOADPATH := -Q Generated BitsGenerated -Q Proofs BitsProofs -Q Reference/Generated ReferenceGenerated -Q Reference/Proofs ReferenceProofs
.PHONY: all check clean
all: Makefile.rocq
	ulimit -s 65536; $(MAKE) -f Makefile.rocq all
Makefile.rocq: Makefile $(SOURCES) $(REFERENCE_INPUTS) ../../scripts/stage-rocq-bits-reference.py
	python3 ../../scripts/stage-rocq-bits-reference.py
	$(ROCQ) makefile $(LOADPATH) $(SOURCES) Reference/Generated/*.v Reference/Proofs/*.v -o $@
check: all
	ulimit -s 65536; $(ROCQ) check -silent $(LOADPATH) $(patsubst Generated/%.v,BitsGenerated.%,$(wildcard Generated/*.v)) $(patsubst Proofs/%.v,BitsProofs.%,$(wildcard Proofs/*.v)) ReferenceProofs.ArrayInvariant
clean:
	if test -f Makefile.rocq; then $(MAKE) -f Makefile.rocq clean; fi
