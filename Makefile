all: Makefile.coq
	$(MAKE) -f Makefile.coq


Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

clean:
	$(MAKE) -f Makefile.coq clean

check:
	# Check for z3
	apt-get install coinor-csdp

.PHONEY: all clean
