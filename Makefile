MODULES    := Common \
	FEqualDep \
	StructureEquality \
	DefinitionSimplification \
	NatFacts \
	EquivalenceSet \
	EquivalenceClass \
	EquivalenceRelation \
	EquivalenceRelationGenerator \
	SpecializedCategory \
	Category \
	CategoryEquality \
	CategoryIsomorphisms \
	Functor \
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
