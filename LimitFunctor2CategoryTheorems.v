Require Import FunctionalExtensionality.
Require Export Adjoint Functor Category.
Require Import Common Notations FunctorCategory NaturalTransformation Hom Duals CommaCategoryFunctors SetLimits SetColimits LimitFunctors LimitFunctorTheorems InducedLimitFunctors DefinitionSimplification FEqualDep CommaCategoryFunctorProperties.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

(* This should be useful for proving that the data migration functors
in DataMigrationFunctors.v are adjoint, for
DataMigrationFunctorsAdjoint.v *)

Section LimReady.
  (* Variables C D : Category. *)
  Variable S : Category.

  Local Notation "A ↓ F" := (CosliceCategory A F).
  (*Local Notation "C / c" := (@SliceCategoryOver _ _ C c).*)

  Variable I : Type.
  Variable Index2Object : I -> Type.
  Variable Index2Cat : forall i : I, Category (Index2Object i).

  Local Coercion Index2Cat : I >-> Category.

  Local Notation "'CAT' ⇑ D" := (@LaxCosliceCategory _ _ Index2Cat _ D).

  Variable HasLimits : forall C0 : CAT ⇑ S, Limit (projT2 C0).

  Definition CatUpSet2Morphism A B (m1 m2 : Morphism (CAT ⇑ S) A B) : Type
    := { T : NaturalTransformation (snd (projT1 m1)) (snd (projT1 m2)) |
         NTComposeT (projT2 m2) (NTComposeF (IdentityNaturalTransformation (projT2 A)) T) = projT2 m1 }.

  Lemma LimReady A B m1 m2 (LimitF := @InducedLimitFunctor _ _ Index2Cat _ S HasLimits) :
    @CatUpSet2Morphism A B m1 m2 -> MorphismOf LimitF m1 = MorphismOf LimitF m2.
    intro X; destruct X.
    simpl in *.
    unfold InducedLimitFunctor_MorphismOf.
    unfold InducedLimitMap.

    apply f_equal.
    match goal with
      | [ |- @eq ?T ?A ?B ] => let T' := eval hnf in T in change (@eq T' A B)
    end.


    subst_body.
    simpl in *.
    hnf in *.
    destruct A as [A], B as [B], m1 as [m1], m2 as [m2].
    simpl in *.
    destruct A, B, m1, m2; simpl in *.


    repeat subst; simpl in *.

    apply NaturalTransformation_eq;
      apply functional_extensionality_dep; intro; simpl.
    repeat rewrite RightIdentity.
    repeat rewrite LeftIdentity.
    try_associativity ltac:(apply f_equal).
    try_associativity ltac:(rewrite <- FCompositionOf).
    simpl.
    present_spcategory.
    repeat rewrite FIdentityOf.
    repeat rewrite RightIdentity.
    repeat rewrite LeftIdentity.
    unfold Object in *.

    destruct_head @prod; simpl in *.
    destruct_head unit.
    clear.

    rename i0 into D, i into C.
    rename s into H, S into SET.
    rename s3 into F', s1 into F, x into b.
    rename x4 into c.

    match goal with
      | [ |- appcontext[@TerminalMorphism_Morphism ?C ?D ?U ?X ?M] ] =>
        let T := fresh "T" in
        set (T := @TerminalMorphism_Morphism C D U X M);
          hnf in T
    end.
    match goal with
      | [ T : NaturalTransformation _ _ |- _ ] =>
        let H := fresh in
        pose proof (Commutes T) as H;
          simpl in H;
          symmetry; etransitivity; try apply H; []
    end.
    rewrite RightIdentity.
    reflexivity.
  Defined.
