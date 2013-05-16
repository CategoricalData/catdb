Require Export Adjoint.
Require Import Notations Common FunctorCategoryFunctorial Duals TypeclassSimplification.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section AdjointPointwise.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).
  Context `(C' : @SpecializedCategory objC').
  Context `(D' : @SpecializedCategory objD').

  Variable F : SpecializedFunctor C D.
  Variable G : SpecializedFunctor D C.

  Variable A : Adjunction F G.
  Let A' : AdjunctionUnitCounit F G := A.

  Variables F' G' : SpecializedFunctor C' D'.

(*  Variable T' : SpecializedNaturalTransformation F' G'.*)

  Definition AdjointPointwise_NT_Unit : SpecializedNaturalTransformation (IdentityFunctor (C ^ E))
                                                                    (ComposeFunctors (G ^ IdentityFunctor E) (F ^ IdentityFunctor E)).
    clearbody A'; clear A.
    pose proof (A' : AdjunctionUnit _ _) as A''.
    refine (NTComposeT _ (LiftIdentityPointwise _ _)).
    refine (NTComposeT _ (projT1 A'' ^ (IdentityNaturalTransformation (IdentityFunctor E)))).
    refine (NTComposeT (LiftComposeFunctorsPointwise _ _ (IdentityFunctor E) (IdentityFunctor E)) _).
    refine (LiftNaturalTransformationPointwise (IdentityNaturalTransformation _) _).
    exact (LeftIdentityFunctorNaturalTransformation2 _).
  Defined.

  Definition AdjointPointwise_NT_Counit : SpecializedNaturalTransformation (ComposeFunctors (F ^ IdentityFunctor E) (G ^ IdentityFunctor E))
                                                                           (IdentityFunctor (D ^ E)).
    clearbody A'; clear A.
    pose proof (A' : AdjunctionCounit _ _) as A''.
    refine (NTComposeT (LiftIdentityPointwise_Inverse _ _) _).
    refine (NTComposeT (projT1 A'' ^ (IdentityNaturalTransformation (IdentityFunctor E))) _).
    refine (NTComposeT _ (LiftComposeFunctorsPointwise_Inverse _ _ (IdentityFunctor E) (IdentityFunctor E))).
    refine (LiftNaturalTransformationPointwise (IdentityNaturalTransformation _) _).
    exact (LeftIdentityFunctorNaturalTransformation1 _).
  Defined.

  Definition AdjointPointwise : Adjunction (F ^ (IdentityFunctor E)) (G ^ (IdentityFunctor E)).
    clearbody A'; clear A.
    match goal with
      | [ |- Adjunction ?F ?G ] =>
        refine (_ : AdjunctionUnitCounit F G)
    end.
    exists AdjointPointwise_NT_Unit
           AdjointPointwise_NT_Counit;
      simpl;
      abstract (
          destruct A';
          simpl in *;
            nt_eq;
          rsimplify_morphisms;
          try match goal with
                | [ H : _ |- _ ] => apply H
              end
        ).
  Defined.
End AdjointPointwise.
