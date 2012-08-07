Require Import ProofIrrelevance FunctionalExtensionality JMeq.
Require Export SpecializedCommaCategory SmallCat Duals.
Require Import Common DiscreteCategory FEqualDep DefinitionSimplification SigTSigCategory SigTSigInducedFunctors.

Set Implicit Arguments.

Local Open Scope category_scope.

Local Ltac slice_t :=
  repeat match goal with
           | [ |- @JMeq (sig _) _ (sig _) _ ] => apply sig_JMeq
           | [ |- (_ -> _) = (_ -> _) ] => apply f_type_equal
           | _ => progress (intros; simpl in *; trivial; subst_body)
           | _ => progress simpl_eq
           | _ => progress (repeat rewrite Associativity; repeat rewrite LeftIdentity; repeat rewrite RightIdentity)
           | _ => progress JMeq_eq
           | [ |- @JMeq ?Ta ?a ?Tb ?b ] =>
             match type of Ta with
               Prop => match type of Tb with
                         Prop =>
                         cut (Ta = Tb);
                           [ generalize b a; simpl in *; generalize Ta Tb; intros; subst; JMeq_eq; apply proof_irrelevance | ]
                       end
             end
           | _ => apply f_equal
           | [ |- JMeq (?f ?x) (?f ?y) ] =>
             apply (@f_equal1_JMeq _ _ x y f)
           | [ |- JMeq (?f ?x) (?g ?y) ] =>
             apply (@f_equal_JMeq _ _ _ _ x y f g)
           | _ =>
             progress (
               destruct_sig;
               present_spcategory
             )
           | [ |- @eq (SpecializedFunctor _ _) _ _ ] => functor_eq
         end.

Section CommaCategory.
  Variable objA : Type.
  Variable morA : objA -> objA -> Type.
  Variable A : SpecializedCategory morA.
  Variable objB : Type.
  Variable morB : objB -> objB -> Type.
  Variable B : SpecializedCategory morB.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable S : SpecializedFunctor A C.
  Variable T : SpecializedFunctor B C.

  Let AOp := OppositeCategory A.

  Local Notation "S ↓ T" := (CommaSpecializedCategory S T) (at level 70, no associativity).

  Definition CommaCategoryProjection : SpecializedFunctor (S ↓ T) (A * B) := proj1_functor_sigT_sig _ _ _ _.
End CommaCategory.

Section SliceCategory.
  Variable objA : Type.
  Variable morA : objA -> objA -> Type.
  Variable A : SpecializedCategory morA.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable a : C.
  Variable S : SpecializedFunctor A C.

  Section Slice.
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F) (at level 70, no associativity).

    Definition SliceCategoryProjection : SpecializedFunctor (S ↓ a) A
      := ComposeFunctors fst_Functor (CommaCategoryProjection S (SliceSpecializedCategory_Functor C a)).
  End Slice.

  Section Coslice.
    Local Notation "A ↓ F" := (CosliceSpecializedCategory A F) (at level 70, no associativity).

    Definition CosliceCategoryProjection : SpecializedFunctor (a ↓ S) A
      := ComposeFunctors snd_Functor (CommaCategoryProjection (SliceSpecializedCategory_Functor C a) S).
  End Coslice.
End SliceCategory.

Section SliceCategoryInducedFunctor.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.
  Variable F : SpecializedFunctor C D.

  Local Ltac solve_slice := abstract (
    simpl; intros; destruct_sig; simpl in *;
      try rewrite LeftIdentity in *; try rewrite RightIdentity in *;
        subst; repeat rewrite Associativity; reflexivity
  ).

  Section Slice.
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F) (at level 70, no associativity).
    Local Notation "C / c" := (@SliceSpecializedCategoryOver _ _ C c).

    Definition SliceCategoryInducedFunctor s d (m : Morphism D s d) :
      SpecializedFunctor (F ↓ s) (F ↓ d).
      eapply (@InducedT2Functor_sigT_sig _ _ (C * TerminalCategory)).
      instantiate (1 := fun _ m0 => Compose m m0).
      solve_slice.
    Defined.
  End Slice.

  Section Coslice.
    Local Notation "A ↓ F" := (CosliceSpecializedCategory A F) (at level 70, no associativity).
    Local Notation "C / c" := (@SliceSpecializedCategoryOver _ _ C c).

    Let DOp := OppositeCategory D.

    Definition CosliceCategoryInducedFunctor (s d : D) (m : Morphism DOp s d) :
      SpecializedFunctor (s ↓ F) (d ↓ F).
      eapply (@InducedT2Functor_sigT_sig _ _ (TerminalCategory * C)).
      instantiate (1 := fun _ m0 => Compose m m0).
      solve_slice.
    Defined.
  End Coslice.
End SliceCategoryInducedFunctor.

Section SliceCategoryProjectionFunctor.
  Local Transparent Object Morphism.

  Variable C : LocallySmallCategory.
  Variable D : Category.
  Variable F : SpecializedFunctor C D. (* [SpecializedFunctor], not [Functor], because otherwise Sort-poylmorphism won't work *)

  Section Slice.
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F) (at level 70, no associativity).
    Local Notation "C / c" := (@SliceSpecializedCategoryOver _ _ C c).

    Let SliceCategoryProjectionFunctor_ObjectOf (d : D) : LocallySmallCat / C.
      exists ((F ↓ d : LocallySmallSpecializedCategory _) : LocallySmallCategory, tt).
      exact (SliceCategoryProjection d F).
    Defined.

    Definition SliceCategoryProjectionFunctor_MorphismOf s d (m : Morphism D s d) :
      Morphism (LocallySmallCat / C)
      (SliceCategoryProjectionFunctor_ObjectOf s)
      (SliceCategoryProjectionFunctor_ObjectOf d).
      subst_body;
      hnf; simpl.
      exists (@SliceCategoryInducedFunctor _ _ C _ _ D F s d m, tt).
      unfold SliceCategoryInducedFunctor in *; simpl; intros.
      abstract (
        functor_eq;
        f_equal;
        match goal with
          | [ |- proj1_sig ?x = projT1 _ ] => destruct x; simpl; reflexivity
        end
      ).
    Defined.

    Let SliceCategoryProjectionFunctor' : Functor D (LocallySmallCat / C).
      refine (Build_SpecializedFunctor D (LocallySmallCat / (C : LocallySmallCategory))
        (@SliceCategoryProjectionFunctor_ObjectOf)
        (@SliceCategoryProjectionFunctor_MorphismOf)
        _
        _
      );
      unfold SliceCategoryProjectionFunctor_MorphismOf, SliceCategoryInducedFunctor in *; subst_body;
        abstract slice_t.
    Defined.

    Let SliceCategoryProjectionFunctor'' : Functor D (LocallySmallCat / C).
      simpl_definition_by_tac_and_exact SliceCategoryProjectionFunctor' ltac:(unfold SliceCategoryProjectionFunctor_MorphismOf in *; subst_body; eta_red).
    Defined.

    Definition SliceCategoryProjectionFunctor : Functor D (LocallySmallCat / C)
      := Eval cbv beta iota zeta delta [SliceCategoryProjectionFunctor''] in SliceCategoryProjectionFunctor''.
  End Slice.

  Section Coslice.
    Local Notation "A ↓ F" := (CosliceSpecializedCategory A F) (at level 70, no associativity).
    Local Notation "C / c" := (@SliceSpecializedCategoryOver _ _ C c).

    Let DOp := OppositeCategory D.

    Let CosliceCategoryProjectionFunctor_ObjectOf (d : D) : LocallySmallCat / C.
      exists ((d ↓ F : LocallySmallSpecializedCategory _) : LocallySmallCategory, tt).
      exact (CosliceCategoryProjection d F).
    Defined.

    Definition CosliceCategoryProjectionFunctor_MorphismOf (s d : D) (m : Morphism DOp s d) :
      Morphism (LocallySmallCat / C)
      (CosliceCategoryProjectionFunctor_ObjectOf s)
      (CosliceCategoryProjectionFunctor_ObjectOf d).
      Transparent Morphism.
      subst_body; hnf; simpl.
      exists (@CosliceCategoryInducedFunctor _ _ C _ _ D F s d m, tt).
      simpl; intros.
      abstract (
        functor_eq;
        f_equal;
        match goal with
          | [ |- proj1_sig ?x = projT1 _ ] => destruct x; simpl; reflexivity
        end
      ).
    Defined.

    Let CosliceCategoryProjectionFunctor' : Functor DOp (LocallySmallCat / C).
      refine (Build_SpecializedFunctor DOp (LocallySmallCat / (C : LocallySmallCategory))
        (@CosliceCategoryProjectionFunctor_ObjectOf)
        (@CosliceCategoryProjectionFunctor_MorphismOf)
        _
        _
      );
      unfold CosliceCategoryProjectionFunctor_MorphismOf, CosliceCategoryInducedFunctor in *; subst_body;
        abstract slice_t.
    Defined.

    Let CosliceCategoryProjectionFunctor'' : Functor DOp (LocallySmallCat / C).
      simpl_definition_by_tac_and_exact CosliceCategoryProjectionFunctor' ltac:(unfold CosliceCategoryProjectionFunctor_MorphismOf in *; subst_body; eta_red).
    Defined.

    Definition CosliceCategoryProjectionFunctor : Functor DOp (LocallySmallCat / C)
      := Eval cbv beta iota zeta delta [CosliceCategoryProjectionFunctor''] in CosliceCategoryProjectionFunctor''.
  End Coslice.
End SliceCategoryProjectionFunctor.
