MODULES    := Common \
	FEqualDep \
	StructureEquality \
	DefinitionSimplification \
	EquivalenceSet \
	EquivalenceClass \
	EquivalenceRelation \
	EquivalenceRelationGenerator \
	SpecializedCategory \
	Category \
	CategoryEquality \
	Functor \
	NaturalTransformation \
	NaturalEquivalence \
	FunctorCategory \
	ComputableCategory \
	DiscreteCategory \
	ProductCategory \
	ProductFunctor \
	SmallCat \
	CommaCategory \
	UniversalProperties \
	Duals \
	SetCategory \
	Hom \
	FunctorAttributes \
	Groupoid \
	AdjointUnit \
	Adjoint \
	Limits \
	SpecializedLimitFunctors \
	SpecializedLimitFunctorTheorems \
	Grothendieck \
	SetLimits \
	SetColimits \
	SetCategoryFacts \
	Yoneda \
	\
	LimitFunctors \
	LimitFunctorTheorems \
	Schema \
	SmallSchema \
	SetSchema \
	Instance \
	Translation \
	SmallTranslation \
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
