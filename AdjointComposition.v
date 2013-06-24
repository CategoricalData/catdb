Require Export Adjoint.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section compose.
  Variable C : Category.
  Variable D : Category.
  Variable E : Category.

  Variable F : Functor C D.
  Variable F' : Functor D E.
  Variable G : Functor D C.
  Variable G' : Functor E D.

  Variable A' : Adjunction F' G'.
  Variable A : Adjunction F G.

  Definition ComposeAdjunctionsUnitMorphism
  : NaturalTransformation (IdentityFunctor C)
                          (ComposeFunctors (ComposeFunctors G G') (ComposeFunctors F' F)).
    pose (projT1 (A : AdjunctionUnit _ _)) as η.
    pose (projT1 (A' : AdjunctionUnit _ _)) as η'.
    refine (NTComposeT _ (* associator *)
                       (NTComposeT (NTComposeF (IdentityNaturalTransformation G) (NTComposeF η' (IdentityNaturalTransformation F)))
                                   (NTComposeT _ (* identity *)
                                               η)));
      nt_solve_associator.
    match goal with
      | [ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
                                                       (fun _ => Identity _)
                                                       _)
    end.
    simpl;
    abstract (
        intros;
        autorewrite with morphism;
        reflexivity
      ).
  Defined.

  (* TODO(jgross): speed this up, automate it more *)
  Definition ComposeAdjunctions : Adjunction (ComposeFunctors F' F) (ComposeFunctors G G').
    refine (_ : AdjunctionUnit (ComposeFunctors F' F) (ComposeFunctors G G')).
    exists ComposeAdjunctionsUnitMorphism.
    pose (projT2 (A : AdjunctionUnit _ _)) as Hη.
    pose (projT2 (A' : AdjunctionUnit _ _)) as Hη'.
    intros c d f.
    exists (proj1_sig (Hη' _ _ (proj1_sig (Hη _ _ f)))).
    abstract (
        subst_body; intro_proj2_sig_from_goal;
        hnf in *; split_and; split;
        simpl in *;
          autorewrite with category;
        [ try_associativity ltac:(progress repeat rewrite <- FCompositionOf);
          simpl in *;
          repeat match goal with
                   | [ H : _ |- _ ] => apply f_equal; solve [ trivial ]
                   | [ H : _ |- _ ] => symmetry; rewrite <- H at 1; apply f_equal2; try reflexivity; []; symmetry
                 end
        | intros x' H;
          repeat match goal with
                   | [ H : _ |- _ ] => apply H
                   | [ H : _ |- _ ] => symmetry; apply H
                 end;
          rewrite <- H;
          try_associativity ltac:(progress repeat rewrite FCompositionOf);
          autorewrite with morphism;
          reflexivity ]
      ).
  Defined.
End compose.
