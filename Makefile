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
	ProductLaws \
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
	DataMigrationFunctors \
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

# TODO(jgross): Look into combining this with the time-make.sh script
timed: Makefile.coq
	$(MAKE) -f Makefile.coq SHELL=./report_time.sh

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
