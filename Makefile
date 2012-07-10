MODULES    := Common \
	FEqualDep \
	StructureEquality \
	DefinitionSimplification \
	EquivalenceSet \
	EquivalenceRelationGenerator \
	SpecializedCategory \
	SpecializedFunctor \
	SpecializedNaturalTransformation \
	SpecializedNaturalEquivalence \
	SpecializedFunctorCategory \
	SpecializedComputableCategory \
	SpecializedDiscreteCategory \
	SpecializedProductCategory \
	SpecializedProductFunctor \
	SpecializedCommaCategory \
	SpecializedUniversalProperties \
	SpecializedDuals \
	SpecializedSetCategory \
	SpecializedHom \
	SpecializedFunctorAttributes \
	SpecializedGroupoid \
	SpecializedAdjointUnit \
	SpecializedAdjoint \
	SpecializedLimits \
	SpecializedLimitFunctors \
	SpecializedLimitFunctorTheorems \
	SpecializedGrothendieck \
	SpecializedYoneda \
	Category \
	CategoryEquality \
	SmallCategory \
	Functor \
	SmallFunctor \
	ComputableCategory \
	NaturalTransformation \
	SmallNaturalTransformation \
	NaturalEquivalence \
	FunctorCategory \
	DiscreteCategory \
	SmallCat \
	ProductCategory \
	CommaCategory \
	UniversalProperties \
	Limits \
	LimitFunctors \
	LimitFunctorTheorems \
	Duals \
	SmallDuals \
	ProductFunctor \
	SetCategory \
	Hom \
	FunctorAttributes \
	AdjointUnit \
	Adjoint \
	Grothendieck \
	Yoneda \
	EquivalenceClass \
	EquivalenceRelation \
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
