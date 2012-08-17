MODULES    := Notations \
	Common \
	FEqualDep \
	StructureEquality \
	DefinitionSimplification \
	NatFacts \
	EquivalenceSet \
	EquivalenceClass \
	EquivalenceRelationGenerator \
	SpecializedCategory \
	Category \
	CategoryEquality \
	CategoryIsomorphisms \
	Functor \
	FunctorIsomorphisms \
	NaturalTransformation \
	NaturalEquivalence \
	SigCategory \
	SigTCategory \
	SigTSigCategory \
	SigSigTCategory \
	SigTInducedFunctors \
	SigTSigInducedFunctors \
	NatCategory \
	BoolCategory \
	Subcategory \
	FunctorCategory \
	ComputableCategory \
	DiscreteCategory \
	ProductCategory \
	ProductFunctor \
	ProductNaturalTransformation \
	MonoidalCategory \
	EnrichedCategory \
	SetCategory \
	DecidableDiscreteCategory \
	DecidableComputableCategory \
	DecidableSmallCat \
	DecidableSetCategory \
	InitialTerminalCategory \
	SmallCat \
	CommaCategory \
	SpecializedCommaCategory \
	LaxCommaCategory \
	SpecializedLaxCommaCategory \
	CommaCategoryFunctors \
	UniversalProperties \
	Duals \
	Hom \
	FunctorAttributes \
	Correspondences \
	Groupoid \
	AdjointUnit \
	Adjoint \
	DiscreteCategoryFunctors \
	DecidableDiscreteCategoryFunctors \
	Limits \
	LimitFunctors \
	LimitFunctorTheorems \
	InducedLimitFunctors \
	Equalizer \
	Products \
	Coend \
	Grothendieck \
	SetLimits \
	SetColimits \
	SetCategoryFacts \
	Yoneda \
	\
	Schema \
	SmallSchema \
	SetSchema \
	Instance \
	Translation \
	SmallTranslation \
	MetaTranslation \
	CategorySchemaEquivalence \
	ComputableSchemaCategory \
	MetaEquivalence \
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
