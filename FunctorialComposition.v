Require Export FunctorCategory ProductCategory.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Section FunctorialComposition.
  Context `(C : SpecializedCategory objC).
  Context `(D : SpecializedCategory objD).
  Context `(E : SpecializedCategory objE).

  Definition FunctorialComposition : SpecializedFunctor ((E ^ D) * (D ^ C)) (E ^ C).
  Proof.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (fun fg => ComposeFunctors (fst fg) (snd fg))
          (fun _ _ tu => NTComposeF (fst tu) (snd tu))
          _
          _
        )
    end;
    abstract (
      intros; present_spnt;
        destruct_hypotheses;
        auto with category;
          nt_eq;
          repeat rewrite FIdentityOf;
            auto with category
    ).
  Defined.
End FunctorialComposition.
