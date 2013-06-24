Require Export FunctorCategory ProductCategory.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section FunctorialComposition.
  Variable C : Category.
  Variable D : Category.
  Variable E : Category.

  Definition FunctorialComposition : Functor ((E ^ D) * (D ^ C)) (E ^ C).
  Proof.
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor C D
          (fun fg => ComposeFunctors (fst fg) (snd fg))
          (fun _ _ tu => NTComposeF (fst tu) (snd tu))
          _
          _
        )
    end;
    abstract (
      intros;
        destruct_hypotheses;
        auto with category;
          nt_eq;
          repeat rewrite FIdentityOf;
            auto with category
    ).
  Defined.
End FunctorialComposition.
