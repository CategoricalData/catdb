Require Export Adjoint.
Require Import Common Notations TypeclassUnreifiedSimplification.

Set Implicit Arguments.

Generalizable All Variables.

Section compose.
  Context `(C : SpecializedCategory objC).
  Context `(D : SpecializedCategory objD).
  Context `(E : SpecializedCategory objE).

  Variable F : SpecializedFunctor C D.
  Variable F' : SpecializedFunctor D E.
  Variable G : SpecializedFunctor D C.
  Variable G' : SpecializedFunctor E D.

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
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
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
          [
          | intros x' H;
            repeat match goal with
                     | [ H : _ |- _ ] => apply H
                     | [ H : _ |- _ ] => symmetry; apply H
                   end;
            rewrite <- H ];
        rsimplify_morphisms;
        simpl in *;
          try_associativity ltac:(progress repeat rewrite <- FCompositionOf);
        rewrite_hyp;
        reflexivity
      ).
  Defined.
End compose.
