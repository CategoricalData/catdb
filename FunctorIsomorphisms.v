Require Import Setoid.
Require Export Functor CategoryIsomorphisms.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Section FunctorIsomorphism.
  (* Copy definitions from CategoryIsomorphisms.v *)

  Section FunctorIsInverseOf.
    Context `{C : Category}.
    Context `{D : Category}.

    Definition FunctorIsInverseOf1 (F : Functor C D) (G : Functor D C) : Prop :=
      ComposeFunctors G F = IdentityFunctor C.
    Definition FunctorIsInverseOf2 (F : Functor C D) (G : Functor D C) : Prop :=
      ComposeFunctors F G = IdentityFunctor D.

    Global Arguments FunctorIsInverseOf1 / _ _.
    Global Arguments FunctorIsInverseOf2 / _ _.

    Definition FunctorIsInverseOf (F : Functor C D) (G : Functor D C) : Prop := Eval simpl in
      FunctorIsInverseOf1 F G /\ FunctorIsInverseOf2 F G.
  End FunctorIsInverseOf.

  Lemma FunctorIsInverseOf_sym `{C : Category} `{D : Category}
    (F : Functor C D) (G : Functor D C) :
    FunctorIsInverseOf F G -> FunctorIsInverseOf G F.
    intros; hnf in *; split_and; split; trivial.
  Qed.

  Section FunctorIsomorphismOf.
    Record FunctorIsomorphismOf `{C : Category} `{D : Category} (F : Functor C D) := {
      FunctorIsomorphismOf_Functor :> _ := F;
      InverseFunctor : Functor D C;
      LeftInverseFunctor : ComposeFunctors InverseFunctor F = IdentityFunctor C;
      RightInverseFunctor : ComposeFunctors F InverseFunctor = IdentityFunctor D
    }.

    Hint Resolve RightInverseFunctor LeftInverseFunctor : category.
    Hint Resolve RightInverseFunctor LeftInverseFunctor : functor.

    Definition FunctorIsomorphismOf_Identity (C : Category) : FunctorIsomorphismOf (IdentityFunctor C).
      exists (IdentityFunctor _); eauto with functor.
    Defined.

    Definition InverseOfFunctor `{C : Category} `{D : Category} (F : Functor C D)
      (i : FunctorIsomorphismOf F) : FunctorIsomorphismOf (InverseFunctor i).
      exists i; auto with functor.
    Defined.

    Definition ComposeFunctorIsmorphismOf `{C : Category} `{D : Category} `{E : Category}
      {F : Functor D E} {G : Functor C D} (i1 : FunctorIsomorphismOf F) (i2 : FunctorIsomorphismOf G) :
      FunctorIsomorphismOf (ComposeFunctors F G).
      exists (ComposeFunctors (InverseFunctor i2) (InverseFunctor i1));
      abstract (
          match goal with
            | [ |- context[ComposeFunctors (ComposeFunctors ?F ?G) (ComposeFunctors ?H ?I)] ] =>
              transitivity (ComposeFunctors (ComposeFunctors F (ComposeFunctors G H)) I);
                try solve [ repeat rewrite ComposeFunctorsAssociativity; reflexivity ]; []
          end;
          destruct i1, i2; simpl;
          repeat (rewrite_hyp; autorewrite with functor);
          trivial
        ).
    Defined.
  End FunctorIsomorphismOf.

  Section IsomorphismOfCategories.
    Record IsomorphismOfCategories (C : Category) (D : Category) := {
      IsomorphismOfCategories_Functor : Functor C D;
      IsomorphismOfCategories_Of :> FunctorIsomorphismOf IsomorphismOfCategories_Functor
    }.

    Global Coercion Build_IsomorphismOfCategories : FunctorIsomorphismOf >-> IsomorphismOfCategories.
  End IsomorphismOfCategories.

  Section FunctorIsIsomorphism.
    Definition FunctorIsIsomorphism `{C : Category} `{D : Category} (F : Functor C D) : Prop :=
      exists G, FunctorIsInverseOf F G.

    Lemma FunctorIsmorphismOf_FunctorIsIsomorphism `{C : Category} `{D : Category} (F : Functor C D) :
      FunctorIsomorphismOf F -> FunctorIsIsomorphism F.
      intro i; hnf.
      exists (InverseFunctor i);
        destruct i; simpl;
        split;
        assumption.
    Qed.

    Lemma FunctorIsIsomorphism_FunctorIsmorphismOf `{C : Category} `{D : Category} (F : Functor C D) :
      FunctorIsIsomorphism F -> exists _ : FunctorIsomorphismOf F, True.
      intro i; destruct_hypotheses.
      destruct_exists; trivial.
      eexists; eassumption.
    Qed.
  End FunctorIsIsomorphism.

  Section CategoriesIsomorphic.
    Definition CategoriesIsomorphic (C D : Category) : Prop :=
      exists (F : Functor C D) (G : Functor D C), FunctorIsInverseOf F G.

    Lemma IsmorphismOfCategories_CategoriesIsomorphic (C : Category) (D : Category) :
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

Section Functor_preserves_isomorphism.
  Variable C : Category.
  Variable D : Category.
  Variable F : Functor C D.

  Hint Rewrite <- FCompositionOf : functor.

  Definition MorphismOf_IsomorphismOf s d (m : Morphism C s d) (i : IsomorphismOf m) : IsomorphismOf (F.(MorphismOf) m).
    refine {| Inverse := (F.(MorphismOf) (Inverse i)) |};
    abstract (
        destruct i; simpl;
        repeat (rewrite_hyp; autorewrite with functor);
        reflexivity
      ).
  Defined.
End Functor_preserves_isomorphism.

Hint Resolve @MorphismOf_IsomorphismOf : category functor.
