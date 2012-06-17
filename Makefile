MODULES    := Common \
	FEqualDep \
	Category \
	CategoryEquality \
	Functor \
	FunctorEquality \
	ComputableCategory \
	NaturalTransformation \
	NaturalEquivalence \
	FunctorCategory \
	SmallCategory \
	Limits \
	Duals \
	ProductCategory \
	ProductFunctor \
	SetCategory \
	Hom \
	Adjoint \
	Grothendieck \
	EquivalenceClass \
	EquivalenceRelation \
	Schema \
	Instance \
	Translation \
	CategorySchemaEquivalence \
	Examples \
	Theorems
VS         := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
