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
	EqdepFacts_one_variable \
	Eqdep_dec_one_variable \
	\
	SpecializedCategory \
	Functor \
	NaturalTransformation \
	ProductCategory \
	SumCategory \
	\
	LtacReifiedSimplification \
	TypeclassSimplification \
	TypeclassUnreifiedSimplification \
	CanonicalStructureSimplification \
	\
	Category \
	CategoryEquality \
	CategoryIsomorphisms \
	FunctorIsomorphisms \
	NaturalEquivalence \
	\
	Graph \
	GraphTranslation \
	ComputableGraphCategory \
	\
	NaturalNumbersObject \
	ChainCategory \
	BoolCategory \
	NatCategory \
	FunctorCategory \
	ComputableCategory \
	DiscreteCategory \
	IndiscreteCategory \
	PathsCategory \
	FunctorProduct \
	ProductNaturalTransformation \
	ProductInducedFunctors \
	SumInducedFunctors \
	ExponentialLaws \
	ProductLaws \
	FunctorialComposition \
	MonoidalCategory \
	EnrichedCategory \
	SetCategory \
	SetCategoryProductFunctor \
	InitialTerminalCategory \
	SmallCat \
	CommaCategory \
	SpecializedCommaCategory \
	LaxCommaCategory \
	SpecializedLaxCommaCategory \
	CommaCategoryProjection \
	CommaCategoryInducedFunctors \
	CommaCategoryProjectionFunctors \
	CommaCategoryFunctors \
	CommaCategoryFunctorProperties \
	UniversalProperties \
	Duals \
	DualFunctor \
	FunctorCategoryFunctorial \
	Hom \
	FunctorAttributes \
	SigCategory \
	SigTCategory \
	SigTSigCategory \
	SigSigTCategory \
	SigTInducedFunctors \
	SigTSigInducedFunctors \
	Subcategory \
	DecidableDiscreteCategory \
	DecidableComputableCategory \
	DecidableSmallCat \
	DecidableSetCategory \
	SimplicialSets \
	SemiSimplicialSets \
	Correspondences \
	Groupoid \
	AdjointUnit \
	Adjoint \
	AdjointUniversalMorphisms \
	AdjointComposition \
	AdjointPointwise \
	DiscreteCategoryFunctors \
	DecidableDiscreteCategoryFunctors \
	PathsCategoryFunctors \
	\
	Group \
	GroupCategory \
	\
	Limits \
	LimitFunctors \
	LimitFunctorTheorems \
	InducedLimitFunctors \
	Graphs \
	Equalizer \
	EqualizerFunctor \
	Pullback \
	PullbackFunctor \
	Products \
	ProductFunctors \
	Coend \
	CoendFunctor \
	SubobjectClassifier \
	Grothendieck \
	GrothendieckFunctorial \
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
	Theorems \
	\
	Database \
	SQLQueries \
	DatabaseConstraints \
	DatabaseMorphisms # \
	DataMigrationFunctors \
	CategorySchemaEquivalence \
	ComputableSchemaCategory
VS         := $(MODULES:%=%.v)
VDS	   := $(MODULES:%=%.v.d)

NEW_TIME_FILE=time-of-build-after.log
OLD_TIME_FILE=time-of-build-before.log
BOTH_TIME_FILE=time-of-build-both.log
NEW_PRETTY_TIME_FILE=time-of-build-after-pretty.log
TIME_SHELF_NAME=time-of-build-shelf



.PHONY: coq clean timed pretty-timed pretty-timed-files html

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

html: Makefile.coq
	$(MAKE) -f Makefile.coq html

# TODO(jgross): Look into combining this with the time-make.sh script
timed: Makefile.coq
	chmod +x ./report_time.sh
	./report_time.sh -c $(MAKE) -f Makefile.coq SHELL=./report_time.sh

pretty-timed-diff:
	sh ./make-each-time-file.sh "$(NEW_TIME_FILE)" "$(OLD_TIME_FILE)"
	$(MAKE) combine-pretty-timed

combine-pretty-timed:
	python ./make-both-time-files.py "$(NEW_TIME_FILE)" "$(OLD_TIME_FILE)" "$(BOTH_TIME_FILE)"
	cat "$(BOTH_TIME_FILE)"

pretty-timed:
	sh ./make-each-time-file.sh "$(NEW_TIME_FILE)"
	python ./make-one-time-file.py "$(NEW_TIME_FILE)" "$(NEW_PRETTY_TIME_FILE)"

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -arg -dont-load-proofs -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
