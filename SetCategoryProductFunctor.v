Require Import FunctionalExtensionality.
Require Export ProductCategory SetCategory Functor.
Require Import Common Notations.

Set Implicit Arguments.

Local Close Scope nat_scope.

Section ProductFunctor.
  Polymorphic Hint Extern 1 (@eq (_ -> _) _ _) => apply functional_extensionality_dep; intro.
  Polymorphic Hint Extern 2 => destruct_head @prod.

  Local Ltac build_functor :=
    hnf;
    match goal with
      | [ |- @SpecializedFunctor ?objC ?C ?objD ?D ] =>
        refine (@Build_SpecializedFunctor objC C objD D
                                          (fun ab => (fst ab) * (snd ab))
                                          (fun _ _ fg => (fun xy => ((fst fg) (fst xy), (snd fg) (snd xy))))
                                          _
                                          _);
          abstract (simpl in *; eauto)
    end.

  Polymorphic Definition TypeProductFunctor : SpecializedFunctor (TypeCat * TypeCat) TypeCat. build_functor. Defined.
  Polymorphic Definition SetProductFunctor  : SpecializedFunctor (SetCat * SetCat) SetCat. build_functor. Defined.
  Polymorphic Definition PropProductFunctor : SpecializedFunctor (PropCat * PropCat) PropCat. build_functor. Defined.
End ProductFunctor.
