MODULES    := Common \
	FEqualDep \
	Category \
	CategoryEquality \
	Functor \
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
	FunctorAttributes \
	Adjoint \
	Grothendieck \
	EquivalenceClass \
	EquivalenceRelation \
	Schema \
	SetSchema \
	Instance \
	Translation \
	MetaTranslation \
	CategorySchemaEquivalence \
	ComputableSchemaCategory \
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
