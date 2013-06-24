Require Import FunctionalExtensionality.
Require Export ProductCategory SetCategory Functor.
Require Import Common Notations.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Close Scope nat_scope.

Section ProductFunctor.
  Hint Extern 1 (@eq (_ -> _) _ _) => apply functional_extensionality_dep; intro.
  Hint Extern 2 => destruct_head @prod.

  Local Ltac build_functor :=
    hnf;
    let C := match goal with | [ |- Functor ?C ?D ] => constr:(C) end in
    let D := match goal with | [ |- Functor ?C ?D ] => constr:(D) end in
    refine (@Build_Functor C D
                                      (fun ab => (fst ab) * (snd ab))
                                      (fun _ _ fg => (fun xy => ((fst fg) (fst xy), (snd fg) (snd xy))))
                                      _
                                      _);
      simpl; abstract (intros; eauto).

  Definition TypeProductFunctor : Functor (TypeCat * TypeCat) TypeCat. build_functor. Defined.
  Definition SetProductFunctor  : Functor (SetCat * SetCat) SetCat. build_functor. Defined.
  Definition PropProductFunctor : Functor (PropCat * PropCat) PropCat. build_functor. Defined.
End ProductFunctor.
