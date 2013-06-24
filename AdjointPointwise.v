Require Export Adjoint.
Require Import Notations Common FunctorCategoryFunctorial Duals TypeclassSimplification.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section AdjointPointwise.
  Variable C : Category.
  Variable D : Category.
  Variable E : Category.
  Variable C' : Category.
  Variable D' : Category.

  Variable F : Functor C D.
  Variable G : Functor D C.

  Variable A : Adjunction F G.
  Let A' : AdjunctionUnitCounit F G := A.

  Variables F' G' : Functor C' D'.

(*  Variable T' : NaturalTransformation F' G'.*)

  Definition AdjointPointwise_NT_Unit : NaturalTransformation (IdentityFunctor (C ^ E))
                                                                    (ComposeFunctors (G ^ IdentityFunctor E) (F ^ IdentityFunctor E)).
    clearbody A'; clear A.
    pose proof (A' : AdjunctionUnit _ _) as A''.
    refine (NTComposeT _ (LiftIdentityPointwise _ _)).
    refine (NTComposeT _ (projT1 A'' ^ (IdentityNaturalTransformation (IdentityFunctor E)))).
    refine (NTComposeT (LiftComposeFunctorsPointwise _ _ (IdentityFunctor E) (IdentityFunctor E)) _).
    refine (LiftNaturalTransformationPointwise (IdentityNaturalTransformation _) _).
    exact (LeftIdentityFunctorNaturalTransformation2 _).
  Defined.

  Definition AdjointPointwise_NT_Counit : NaturalTransformation (ComposeFunctors (F ^ IdentityFunctor E) (G ^ IdentityFunctor E))
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
