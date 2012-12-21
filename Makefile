MODULES    := Notations \
	Common \
	GetArguments \
	FEqualDep \
	StructureEquality \
	DefinitionSimplification \
	NatFacts \
	EquivalenceSet \
	EquivalenceClass \
	EquivalenceRelationGenerator \
	Paths \
	SpecializedCategory \
	Category \
	CategoryEquality \
	CategoryIsomorphisms \
	Functor \
	FunctorIsomorphisms \
	NaturalTransformation \
	NaturalEquivalence \
	\
	Graph \
	GraphTranslation \
	ComputableGraphCategory \
	\
	SigCategory \
	SigTCategory \
	SigTSigCategory \
	SigSigTCategory \
	SigTInducedFunctors \
	SigTSigInducedFunctors \
	ChainCategory \
	BoolCategory \
	NatCategory \
	Subcategory \
	FunctorCategory \
	ComputableCategory \
	DiscreteCategory \
	PathsCategory \
	ProductCategory \
	FunctorProduct \
	ProductNaturalTransformation \
	ProductInducedFunctors \
	SumCategory \
	ExponentialLaws \
	FunctorialComposition \
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
	CommaCategoryFunctorProperties \
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
	PathsCategoryFunctors \
	Limits \
	LimitFunctors \
	LimitFunctorTheorems \
	InducedLimitFunctors \
	Graphs \
	Equalizer \
	EqualizerFunctor \
	Products \
	ProductFunctors \
	Coend \
	CoendFunctor \
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
	MetaEquivalence \
	Examples \
	Theorems # \
	CategorySchemaEquivalence \
	ComputableSchemaCategory
VS         := $(MODULES:%=%.v)
VDS	   := $(MODULES:%=%.v.d)

.PHONY: coq clean timed

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

timed: Makefile-timed.coq
	$(MAKE) -f Makefile.coq clean
	time $(MAKE) -f Makefile-timed.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -o Makefile.coq

Makefile-timed.coq: Makefile.coq
	cp -f Makefile.coq Makefile-timed.coq
	sed s'/^\t$$(COQC) /\ttime $$(COQC) /g' -i Makefile-timed.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile-timed.coq .depend
