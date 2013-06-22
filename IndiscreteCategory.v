Require Export SpecializedCategory Functor.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section IndiscreteCategory.
  (** The indiscrete category has exactly one morphism between any two objects. *)
  Variable O : Type.

  Definition IndiscreteCategory : SpecializedCategory
    := @Build_SpecializedCategory O
                                  (fun _ _ => unit)
                                  (fun _ => tt)
                                  (fun _ _ _ _ _ => tt)
                                  (fun _ _ _ _ _ _ _ => eq_refl)
                                  (fun _ _ f => match f with tt => eq_refl end)
                                  (fun _ _ f => match f with tt => eq_refl end).
End IndiscreteCategory.

Section FunctorToIndiscrete.
  Variable O : Type.
  Context `(C : SpecializedCategory).
  Variable objOf : C -> O.

  Definition FunctorToIndiscrete : SpecializedFunctor C (IndiscreteCategory O)
    := Build_SpecializedFunctor C (IndiscreteCategory O)
                                objOf
                                (fun _ _ _ => tt)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).
End FunctorToIndiscrete.
