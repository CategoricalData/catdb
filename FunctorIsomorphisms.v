Require Import Setoid.
Require Export Functor CategoryIsomorphisms.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope category_scope.

Section FunctorIsomorphism.
  (* Copy definitions from CategoryIsomorphisms.v *)

  Section FunctorIsInverseOf.
    Context `{C : @SpecializedCategory objC}.
    Context `{D : @SpecializedCategory objD}.

    Definition FunctorIsInverseOf1 (F : SpecializedFunctor C D) (G : SpecializedFunctor D C) : Prop :=
      ComposeFunctors G F = IdentityFunctor C.
    Definition FunctorIsInverseOf2 (F : SpecializedFunctor C D) (G : SpecializedFunctor D C) : Prop :=
      ComposeFunctors F G = IdentityFunctor D.

    Global Arguments FunctorIsInverseOf1 / _ _.
    Global Arguments FunctorIsInverseOf2 / _ _.

    Definition FunctorIsInverseOf (F : SpecializedFunctor C D) (G : SpecializedFunctor D C) : Prop := Eval simpl in
      FunctorIsInverseOf1 F G /\ FunctorIsInverseOf2 F G.
  End FunctorIsInverseOf.

  Lemma FunctorIsInverseOf_sym `{C : @SpecializedCategory objC} `{D : @SpecializedCategory objD}
    (F : SpecializedFunctor C D) (G : SpecializedFunctor D C) :
    FunctorIsInverseOf F G -> FunctorIsInverseOf G F.
    intros; hnf in *; split_and; split; trivial.
  Qed.

  Section FunctorIsomorphismOf.
    Record FunctorIsomorphismOf `{C : @SpecializedCategory objC} `{D : @SpecializedCategory objD} (F : SpecializedFunctor C D) := {
      FunctorIsomorphismOf_Functor :> _ := F;
      InverseFunctor : SpecializedFunctor D C;
      LeftInverseFunctor : ComposeFunctors InverseFunctor F = IdentityFunctor C;
      RightInverseFunctor : ComposeFunctors F InverseFunctor = IdentityFunctor D
    }.

    Hint Resolve RightInverseFunctor LeftInverseFunctor.

    Definition FunctorIsomorphismOf_Identity `(C : @SpecializedCategory objC) : FunctorIsomorphismOf (IdentityFunctor C).
      exists (IdentityFunctor _); eauto.
    Defined.

    Definition InverseOfFunctor `{C : @SpecializedCategory objC} `{D : @SpecializedCategory objD} (F : SpecializedFunctor C D)
      (i : FunctorIsomorphismOf F) : FunctorIsomorphismOf (InverseFunctor i).
      exists i; auto.
    Defined.

    Definition ComposeFunctorIsmorphismOf `{C : @SpecializedCategory objC} `{D : @SpecializedCategory objD} `{E : @SpecializedCategory objE}
      {F : SpecializedFunctor D E} {G : SpecializedFunctor C D} (i1 : FunctorIsomorphismOf F) (i2 : FunctorIsomorphismOf G) :
      FunctorIsomorphismOf (ComposeFunctors F G).
      exists (ComposeFunctors (InverseFunctor i2) (InverseFunctor i1));
        abstract (
          match goal with
            | [ |- context[ComposeFunctors (ComposeFunctors ?F ?G) (ComposeFunctors ?H ?I)] ] =>
              transitivity (ComposeFunctors (ComposeFunctors F (ComposeFunctors G H)) I);
                try solve [ repeat rewrite ComposeFunctorsAssociativity; reflexivity ]; []
          end;
          destruct i1, i2; t_with t'
        ).
    Defined.
  End FunctorIsomorphismOf.

  Section IsomorphismOfCategories.
    Record IsomorphismOfCategories `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD) := {
      IsomorphismOfCategories_Functor : SpecializedFunctor C D;
      IsomorphismOfCategories_Of :> FunctorIsomorphismOf IsomorphismOfCategories_Functor
    }.

    Global Coercion Build_IsomorphismOfCategories : FunctorIsomorphismOf >-> IsomorphismOfCategories.
  End IsomorphismOfCategories.

  Section FunctorIsIsomorphism.
    Definition FunctorIsIsomorphism `{C : @SpecializedCategory objC} `{D : @SpecializedCategory objD} (F : SpecializedFunctor C D) : Prop :=
      exists G, FunctorIsInverseOf F G.

    Lemma FunctorIsmorphismOf_FunctorIsIsomorphism `{C : @SpecializedCategory objC} `{D : @SpecializedCategory objD} (F : SpecializedFunctor C D) :
      FunctorIsomorphismOf F -> FunctorIsIsomorphism F.
      intro i; hnf.
      exists (InverseFunctor i);
        destruct i; simpl;
          split; present_spcategory;
            assumption.
    Qed.

    Lemma FunctorIsIsomorphism_FunctorIsmorphismOf `{C : @SpecializedCategory objC} `{D : @SpecializedCategory objD} (F : SpecializedFunctor C D) :
      FunctorIsIsomorphism F -> exists _ : FunctorIsomorphismOf F, True.
      intro i; destruct_hypotheses.
      destruct_exists; trivial.
      eexists; eassumption.
    Qed.
  End FunctorIsIsomorphism.

  Section CategoriesIsomorphic.
    Definition CategoriesIsomorphic (C D : Category) : Prop :=
      exists (F : SpecializedFunctor C D) (G : SpecializedFunctor D C), FunctorIsInverseOf F G.

    Lemma IsmorphismOfCategories_CategoriesIsomorphic `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD) :
      IsomorphismOfCategories C D -> CategoriesIsomorphic C D.
      intro i; destruct i as [ m i ].
      exists m.
      apply FunctorIsmorphismOf_FunctorIsIsomorphism; assumption.
    Qed.

    Lemma CategoriesIsomorphic_IsomorphismOfCategories (C D : Category) :
      CategoriesIsomorphic C D -> exists _ : IsomorphismOfCategories C D, True.
      intro i; destruct_hypotheses.
      destruct_exists; trivial.
      repeat esplit; eassumption.
    Qed.

    Local Ltac t_iso' := intros;
      repeat match goal with
               | [ i : CategoriesIsomorphic _ _ |- _ ] => destruct (CategoriesIsomorphic_IsomorphismOfCategories i) as [ ? [] ] ; clear i
               | [ |- CategoriesIsomorphic _ _ ] => apply IsmorphismOfCategories_CategoriesIsomorphic
             end.

    Local Ltac t_iso:= t_iso';
      repeat match goal with
               | [ i : IsomorphismOfCategories _ _ |- _ ] => unique_pose (IsomorphismOfCategories_Of i); try clear i
               | [ |- IsomorphismOfCategories _ _ ] => eapply Build_IsomorphismOfCategories
             end.

    Hint Resolve @FunctorIsomorphismOf_Identity @ComposeFunctorIsmorphismOf.
    Hint Extern 1 => eassumption.

    Lemma CategoriesIsomorphic_refl (C : Category) : CategoriesIsomorphic C C.
      t_iso.
      apply FunctorIsomorphismOf_Identity.
    Qed.

    Lemma CategoriesIsomorphic_sym (C D : Category) :
      CategoriesIsomorphic C D -> CategoriesIsomorphic D C.
      t_iso.
      eapply InverseOfFunctor.
      Grab Existential Variables.
      eauto.
    Qed.

    Lemma CategoriesIsomorphic_trans (C D E : Category) :
      CategoriesIsomorphic C D -> CategoriesIsomorphic D E -> CategoriesIsomorphic C E.
      t_iso.
      apply @ComposeFunctorIsmorphismOf;
        eauto.
    Qed.

    Global Add Parametric Relation : _ @CategoriesIsomorphic
      reflexivity proved by @CategoriesIsomorphic_refl
      symmetry proved by @CategoriesIsomorphic_sym
      transitivity proved by @CategoriesIsomorphic_trans
        as CategoriesIsomorphic_rel.
  End CategoriesIsomorphic.
End FunctorIsomorphism.
