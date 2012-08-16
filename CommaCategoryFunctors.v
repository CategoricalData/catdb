Require Import ProofIrrelevance FunctionalExtensionality JMeq.
Require Export SpecializedCommaCategory SmallCat Duals.
Require Import Common Notations DiscreteCategory FEqualDep DefinitionSimplification.

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
           | _ => apply f_equal
           | [ |- JMeq (?f ?x) (?f ?y) ] =>
             apply (@f_equal1_JMeq _ _ x y f)
           | [ |- JMeq (?f ?x) (?g ?y) ] =>
             apply (@f_equal_JMeq _ _ _ _ x y f g)
           | _ =>
             progress (
               destruct_type @CommaSpecializedCategory_Object;
               destruct_type @CommaSpecializedCategory_Morphism;
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

  Local Notation "S ↓ T" := (CommaSpecializedCategory S T).

  Hint Resolve FCompositionOf FIdentityOf.

  Definition CommaCategoryProjection : SpecializedFunctor (S ↓ T) (A * B).
    refine (Build_SpecializedFunctor (S ↓ T) (A * B)
      (@projT1 _ _)
      (fun _ _ m => (proj1_sig m))
      _
      _
    ); abstract trivial.
  Defined.
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
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F).

    Definition SliceCategoryProjection : SpecializedFunctor (S ↓ a) A
      := ComposeFunctors fst_Functor (CommaCategoryProjection S (SliceSpecializedCategory_Functor C a)).
  End Slice.

  Section Coslice.
    Local Notation "A ↓ F" := (CosliceSpecializedCategory A F).

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

  Section Slice.
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F).
    Local Notation "C / c" := (@SliceSpecializedCategoryOver _ _ C c).

    Let SliceCategoryInducedFunctor_ObjectOf s d (m : Morphism D s d) :
      CommaSpecializedCategory_Object F (SliceSpecializedCategory_Functor D s) ->
      CommaSpecializedCategory_Object F (SliceSpecializedCategory_Functor D d).
      intro x; constructor.
      exists (projT1 x).
      exact (Compose m (projT2 x)).
    Defined.

    Let SliceCategoryInducedFunctor_MorphismOf s d (m : Morphism D s d) : forall
      (s0 d0 : CommaSpecializedCategory_Object F (SliceSpecializedCategory_Functor D s))
      (m0 : CommaSpecializedCategory_Morphism s0 d0),
      CommaSpecializedCategory_Morphism
      (@SliceCategoryInducedFunctor_ObjectOf s d m s0)
      (@SliceCategoryInducedFunctor_ObjectOf s d m d0).
      subst_body.
      intros s0 d0 m0.
      constructor.
      exists (projT1 m0); simpl.
      abstract (
        destruct m0 as [ [ ? ? ] ]; simpl in *;
          rewrite LeftIdentity in *;
            repeat rewrite Associativity;
              apply f_equal;
                assumption
      ).
    Defined.

    Let SliceCategoryInducedFunctor' s d (m : Morphism D s d) :
      SpecializedFunctor (F ↓ s) (F ↓ d).
      refine (Build_SpecializedFunctor (F ↓ s) (F ↓ d)
        (@SliceCategoryInducedFunctor_ObjectOf s d m)
        (@SliceCategoryInducedFunctor_MorphismOf s d m)
        _
        _
      );
      subst_body; simpl; intros;
      abstract (
        present_spcategory;
        subst_body;
        simpl in *;
          apply f_equal; simpl_eq; trivial;
            present_spcategory;
            repeat match goal with
                     | [ H : CommaSpecializedCategory_Morphism _ _ |- _ ] => destruct H as [ [ ] ]; simpl in *
                   end;
            reflexivity
      ).
    Defined.

    Let SliceCategoryInducedFunctor'' s d (m : Morphism D s d) :
      SpecializedFunctor (F ↓ s) (F ↓ d).
      simpl_definition_by_tac_and_exact (@SliceCategoryInducedFunctor' s d m) ltac:(subst_body; eta_red).
    Defined.

    Definition SliceCategoryInducedFunctor s d (m : Morphism D s d) :
      SpecializedFunctor (F ↓ s) (F ↓ d)
      := Eval cbv beta iota zeta delta [SliceCategoryInducedFunctor''] in @SliceCategoryInducedFunctor'' s d m.
  End Slice.

  Section Coslice.
    Local Notation "A ↓ F" := (CosliceSpecializedCategory A F).
    Local Notation "C / c" := (@SliceSpecializedCategoryOver _ _ C c).

    Let DOp := OppositeCategory D.

    Let CosliceCategoryInducedFunctor_ObjectOf s d (m : Morphism DOp s d) :
      CommaSpecializedCategory_Object (SliceSpecializedCategory_Functor D s) F ->
      CommaSpecializedCategory_Object (SliceSpecializedCategory_Functor D d) F.
      intro x; constructor.
      exists (projT1 x).
      exact (Compose (projT2 x) m).
    Defined.

    Let CosliceCategoryInducedFunctor_MorphismOf s d (m : Morphism DOp s d) : forall
      (s0 d0 : CommaSpecializedCategory_Object (SliceSpecializedCategory_Functor D s) F)
      (m0 : CommaSpecializedCategory_Morphism s0 d0),
      CommaSpecializedCategory_Morphism
      (@CosliceCategoryInducedFunctor_ObjectOf s d m s0)
      (@CosliceCategoryInducedFunctor_ObjectOf s d m d0).
      subst_body.
      intros s0 d0 m0.
      constructor; simpl.
      exists (projT1 m0).
      abstract (
        destruct m0 as [ [ ? ? ] ]; simpl in *;
          rewrite RightIdentity in *;
            repeat rewrite <- Associativity;
              f_equal;
              assumption
      ).
    Defined.

    Let CosliceCategoryInducedFunctor' (s d : D) (m : Morphism DOp s d) :
      SpecializedFunctor (s ↓ F) (d ↓ F).
      refine (Build_SpecializedFunctor (s ↓ F) (d ↓ F)
        (@CosliceCategoryInducedFunctor_ObjectOf s d m)
        (@CosliceCategoryInducedFunctor_MorphismOf s d m)
        _
        _
      );
      subst_body; simpl; intros;
      abstract (
        present_spcategory;
        subst_body;
        simpl in *;
          apply f_equal; simpl_eq; trivial;
            present_spcategory;
            repeat match goal with
                     | [ H : CommaSpecializedCategory_Morphism _ _ |- _ ] => destruct H as [ [ ] ]; simpl in *
                   end;
            reflexivity
      ).
    Defined.

    Let CosliceCategoryInducedFunctor'' (s d : D) (m : Morphism DOp s d) :
      SpecializedFunctor (s ↓ F) (d ↓ F).
      simpl_definition_by_tac_and_exact (@CosliceCategoryInducedFunctor' s d m) ltac:(subst_body; eta_red).
    Defined.

    Definition CosliceCategoryInducedFunctor (s d : D) (m : Morphism DOp s d) :
      SpecializedFunctor (s ↓ F) (d ↓ F)
      := Eval cbv beta iota zeta delta [CosliceCategoryInducedFunctor''] in @CosliceCategoryInducedFunctor'' s d m.
  End Coslice.
End SliceCategoryInducedFunctor.


Section SliceCategoryProjectionFunctor.
  Variable C : LocallySmallCategory.
  Variable D : Category.
  Variable F : SpecializedFunctor C D. (* [SpecializedFunctor], not [Functor], because otherwise Sort-poylmorphism won't work *)

  Section Slice.
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F).
    Local Notation "C / c" := (@SliceSpecializedCategoryOver _ _ C c).

    Let SliceCategoryProjectionFunctor_ObjectOf (d : D) : LocallySmallCat / C.
      constructor.
      exists ((F ↓ d : LocallySmallSpecializedCategory _) : LocallySmallCategory, tt).
      exact (SliceCategoryProjection d F).
    Defined.

    Definition SliceCategoryProjectionFunctor_MorphismOf s d (m : Morphism D s d) :
      CommaSpecializedCategory_MorphismT
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
    Local Notation "A ↓ F" := (CosliceSpecializedCategory A F).
    Local Notation "C / c" := (@SliceSpecializedCategoryOver _ _ C c).

    Let DOp := OppositeCategory D.

    Let CosliceCategoryProjectionFunctor_ObjectOf (d : D) : LocallySmallCat / C.
      constructor.
      exists ((d ↓ F : LocallySmallSpecializedCategory _) : LocallySmallCategory, tt).
      exact (CosliceCategoryProjection d F).
    Defined.

    Definition CosliceCategoryProjectionFunctor_MorphismOf (s d : D) (m : Morphism DOp s d) :
      CommaSpecializedCategory_MorphismT
      (CosliceCategoryProjectionFunctor_ObjectOf s)
      (CosliceCategoryProjectionFunctor_ObjectOf d).
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
