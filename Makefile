MODULES    := Common EquivalenceRelation Schema Category Functor NaturalTransformation NaturalEquivalence SmallCategory Definitions Examples Theorems
VS         := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
