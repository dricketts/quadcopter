# copied from tla directory, with some changes...

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

compcert:
	wget http://compcert.inria.fr/release/compcert-2.4.tgz -O - | tar zxf -
