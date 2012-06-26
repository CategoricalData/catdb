MODULES    := Common \
	FEqualDep \
	Category \
	CategoryEquality \
	Functor \
	ComputableCategory \
	NaturalTransformation \
	SmallNaturalTransformation \
	NaturalEquivalence \
	FunctorCategory \
	SmallCategory \
	Limits \
	LimitFunctors \
	Duals \
	ProductCategory \
	ProductFunctor \
	SetCategory \
	Hom \
	FunctorAttributes \
	AdjointUnit \
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
	SNaturalEquivalence \
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
