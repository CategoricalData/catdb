Require Export Category Functor.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section IndiscreteCategory.
  (** The indiscrete category has exactly one morphism between any two objects. *)
  Variable O : Type.

  Definition IndiscreteCategory : Category
    := @Build_Category O
                                  (fun _ _ => unit)
                                  (fun _ => tt)
                                  (fun _ _ _ _ _ => tt)
                                  (fun _ _ _ _ _ _ _ => eq_refl)
                                  (fun _ _ f => match f with tt => eq_refl end)
                                  (fun _ _ f => match f with tt => eq_refl end).
End IndiscreteCategory.

Section FunctorToIndiscrete.
  Variable O : Type.
  Variable C : Category.
  Variable objOf : C -> O.

  Definition FunctorToIndiscrete : Functor C (IndiscreteCategory O)
    := Build_Functor C (IndiscreteCategory O)
                                objOf
                                (fun _ _ _ => tt)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).
End FunctorToIndiscrete.
