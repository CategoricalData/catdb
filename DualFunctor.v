Require Export Duals SmallCat.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section OppositeCategory.
  Definition SmallOppositeFunctor : SpecializedFunctor SmallCat SmallCat.
    refine (Build_SpecializedFunctor SmallCat SmallCat
                                     (fun x => OppositeCategory x : SmallSpecializedCategory)
                                     (fun _ _ m => OppositeFunctor m)
                                     _
                                     _);
    simpl; abstract functor_eq.
  Defined.

  Definition LocallySmallOppositeFunctor : SpecializedFunctor LocallySmallCat LocallySmallCat.
    refine (Build_SpecializedFunctor LocallySmallCat LocallySmallCat
                                     (fun x => OppositeCategory x : LocallySmallSpecializedCategory)
                                     (fun _ _ m => OppositeFunctor m)
                                     _
                                     _);
    simpl; abstract functor_eq.
  Defined.
End OppositeCategory.
