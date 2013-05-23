Require Export SpecializedCategory Functor.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section SumCategory.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Definition SumCategory_Morphism (s d : objC + objD) : Type
    := match (s, d) with
         | (inl s, inl d) => C.(Morphism) s d
         | (inr s, inr d) => D.(Morphism) s d
         | _ => Empty_set
       end.

  Global Arguments SumCategory_Morphism _ _ /.

  Definition SumCategory_Identity (x : C + D) : SumCategory_Morphism x x
    := match x with
         | inl x => Identity x
         | inr x => Identity x
       end.

  Global Arguments SumCategory_Identity _ /.

  Definition SumCategory_Compose (s d d' : C + D) (m1 : SumCategory_Morphism d d') (m2 : SumCategory_Morphism s d) : SumCategory_Morphism s d'.
    (* XXX NOTE: try to use typeclasses and work up to existance of morphisms here *)
    case s, d, d'; simpl in *; try destruct_to_empty_set;
    eapply Compose; eassumption.
  Defined.

  Global Arguments SumCategory_Compose [_ _ _] _ _ /.

  Definition SumCategory : @SpecializedCategory (objC + objD)%type.
    refine (@Build_SpecializedCategory _
                                       SumCategory_Morphism
                                       SumCategory_Identity
                                       SumCategory_Compose
                                       _
                                       _
                                       _);
    abstract (
        repeat match goal with
                 | [ H : Empty_set |- _ ] => case H
                 | _ => let H := fresh in intro H; try (case H; clear H); simpl in *
               end;
        auto with morphism
      ).
  Defined.
End SumCategory.

Infix "+" := SumCategory : category_scope.

Section SumCategoryFunctors.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Definition inl_Functor : SpecializedFunctor C (C + D)
    := Build_SpecializedFunctor C (C + D)
                                (@inl _ _)
                                (fun _ _ m => m)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Definition inr_Functor : SpecializedFunctor D (C + D)
    := Build_SpecializedFunctor D (C + D)
                                (@inr _ _)
                                (fun _ _ m => m)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).
End SumCategoryFunctors.
