Require Export Duals Cat.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section OppositeCategory.
  Definition SmallOppositeFunctor : Functor Cat Cat.
    refine (Build_Functor Cat Cat
                                     (fun x => OppositeCategory x : Category)
                                     (fun _ _ m => OppositeFunctor m)
                                     _
                                     _);
    simpl; abstract functor_eq.
  Defined.

  Definition OppositeFunctor : Functor Cat Cat.
    refine (Build_Functor Cat Cat
                                     (fun x => OppositeCategory x : Category)
                                     (fun _ _ m => OppositeFunctor m)
                                     _
                                     _);
    simpl; abstract functor_eq.
  Defined.
End OppositeCategory.
