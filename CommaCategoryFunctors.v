Require Import ProofIrrelevance FunctionalExtensionality JMeq.
Require Export SpecializedCommaCategory SmallCat Duals.
Require Import Common Notations DiscreteCategory FEqualDep DefinitionSimplification.

Set Implicit Arguments.

Generalizable All Variables.

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

Local Ltac rewrite_step :=
  (progress repeat rewrite @LeftIdentity in * )
    || (progress repeat rewrite @RightIdentity in * )
    || (progress (repeat rewrite @Associativity; apply f_equal))
    || (progress (repeat rewrite <- @Associativity; apply f_equal2; trivial; [])).

Local Ltac quick_step :=
  ((progress repeat subst)
     || (apply sig_eq; simpl)
     || apply f_equal
     || (apply f_equal2; trivial; []));
  trivial.

Local Ltac step :=
  (quick_step
     || rewrite_step
     || (progress auto 1 with category));
  trivial.

Local Ltac pre_anihilate :=
  subst_body;
  repeat intro; simpl in *;
  repeat quick_step;
  simpl in *;
  destruct_head_hnf @CommaSpecializedCategory_Morphism;
  destruct_head_hnf @CommaSpecializedCategory_Object;
  destruct_sig;
  subst_body;
  simpl in *;
  trivial.

Local Ltac anihilate := pre_anihilate; repeat step.

Section CommaCategory.
  Context `(A : @SpecializedCategory objA).
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).
  Variable S : SpecializedFunctor A C.
  Variable T : SpecializedFunctor B C.

  Let AOp := OppositeCategory A.

  Local Notation "S ↓ T" := (CommaSpecializedCategory S T).

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
  Context `(A : @SpecializedCategory objA).
  Context `(C : @SpecializedCategory objC).
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

Section SliceCategoryNTInducedFunctor.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variables F F' : SpecializedFunctor C D.
  Variable a : D.

  Section Slice.
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F).

    Variable T : SpecializedNaturalTransformation F' F.

    Let SliceCategoryNTInducedFunctor_ObjectOf (x : F ↓ a) : F' ↓ a
      := existT _ (projT1 x) (Compose (projT2 x) (T (fst (projT1 x)))) : CommaSpecializedCategory_ObjectT _ _.

    Let SliceCategoryNTInducedFunctor_MorphismOf s d (m : Morphism (F ↓ a) s d) :
      Morphism (F' ↓ a) (SliceCategoryNTInducedFunctor_ObjectOf s) (SliceCategoryNTInducedFunctor_ObjectOf d).
      subst_body; simpl in *.
      constructor.
      exists (projT1 m); simpl.
      abstract anihilate.
    Defined.

    Let SliceCategoryNTInducedFunctor' : SpecializedFunctor (F ↓ a) (F' ↓ a).
      refine (Build_SpecializedFunctor (F ↓ a) (F' ↓ a)
                                       SliceCategoryNTInducedFunctor_ObjectOf
                                       SliceCategoryNTInducedFunctor_MorphismOf
                                       _
                                       _
             );
      subst_body; simpl;
      abstract anihilate.
    Defined.

    Let SliceCategoryNTInducedFunctor'' : SpecializedFunctor (F ↓ a) (F' ↓ a).
      simpl_definition_by_tac_and_exact SliceCategoryNTInducedFunctor' ltac:(subst_body; eta_red).
    Defined.

    Definition SliceCategoryNTInducedFunctor : SpecializedFunctor (F ↓ a) (F' ↓ a)
      := Eval cbv beta iota zeta delta [SliceCategoryNTInducedFunctor''] in @SliceCategoryNTInducedFunctor''.
  End Slice.

  Section Coslice.
    Local Notation "A ↓ F" := (CosliceSpecializedCategory A F).

    Variable T : SpecializedNaturalTransformation F F'.

    Let CosliceCategoryNTInducedFunctor_ObjectOf (x : a ↓ F) : a ↓ F'
      := existT _ (projT1 x) (Compose (T (snd (projT1 x))) (projT2 x)) : CommaSpecializedCategory_ObjectT _ _.

    Let CosliceCategoryNTInducedFunctor_MorphismOf s d (m : Morphism (a ↓ F) s d) :
      Morphism (a ↓ F') (CosliceCategoryNTInducedFunctor_ObjectOf s) (CosliceCategoryNTInducedFunctor_ObjectOf d).
      subst_body; simpl in *.
      constructor.
      exists (projT1 m); simpl.
      abstract anihilate.
    Defined.

    Let CosliceCategoryNTInducedFunctor' : SpecializedFunctor (a ↓ F) (a ↓ F').
      refine (Build_SpecializedFunctor (a ↓ F) (a ↓ F')
                                       CosliceCategoryNTInducedFunctor_ObjectOf
                                       CosliceCategoryNTInducedFunctor_MorphismOf
                                       _
                                       _
             );
      subst_body; simpl;
      abstract anihilate.
    Defined.

    Let CosliceCategoryNTInducedFunctor'' : SpecializedFunctor (a ↓ F) (a ↓ F').
      simpl_definition_by_tac_and_exact CosliceCategoryNTInducedFunctor' ltac:(subst_body; eta_red).
    Defined.

    Definition CosliceCategoryNTInducedFunctor : SpecializedFunctor (a ↓ F) (a ↓ F')
      := Eval cbv beta iota zeta delta [CosliceCategoryNTInducedFunctor''] in CosliceCategoryNTInducedFunctor''.
  End Coslice.
End SliceCategoryNTInducedFunctor.

Section SliceCategoryInducedFunctor.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.

  Section Slice.
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F).

    Let SliceCategoryInducedFunctor_ObjectOf s d (m : Morphism D s d) (x : F ↓ s) : F ↓ d
      := existT _ (projT1 x) (Compose m (projT2 x)) : CommaSpecializedCategory_ObjectT F (SliceSpecializedCategory_Functor D d).

    Let SliceCategoryInducedFunctor_MorphismOf s d (m : Morphism D s d)
        s0 d0 (m0 : Morphism (F ↓ s) s0 d0) :
      Morphism (F ↓ d)
               (@SliceCategoryInducedFunctor_ObjectOf s d m s0)
               (@SliceCategoryInducedFunctor_ObjectOf s d m d0).
      subst_body; constructor.
      exists (projT1 m0); simpl.
      abstract anihilate.
    Defined.

    Let SliceCategoryInducedFunctor' s d (m : Morphism D s d) :
      SpecializedFunctor (F ↓ s) (F ↓ d).
      refine (Build_SpecializedFunctor (F ↓ s) (F ↓ d)
                                       (@SliceCategoryInducedFunctor_ObjectOf s d m)
                                       (@SliceCategoryInducedFunctor_MorphismOf s d m)
                                       _
                                       _
             );
      subst_body; simpl;
      abstract anihilate.
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

    Let CosliceCategoryInducedFunctor_ObjectOf (s d : D) (m : Morphism DOp s d) (x : s ↓ F) : d ↓ F
      := existT _ (projT1 x) (Compose (projT2 x) m) : CommaSpecializedCategory_ObjectT (SliceSpecializedCategory_Functor D d) F.

    Let CosliceCategoryInducedFunctor_MorphismOf (s d : D) (m : Morphism DOp s d)
        s0 d0 (m0 : Morphism (s ↓ F) s0 d0) :
      Morphism (d ↓ F)
               (@CosliceCategoryInducedFunctor_ObjectOf s d m s0)
               (@CosliceCategoryInducedFunctor_ObjectOf s d m d0).
      subst_body; constructor.
      exists (projT1 m0); simpl.
      abstract anihilate.
    Defined.

    Let CosliceCategoryInducedFunctor' (s d : D) (m : Morphism DOp s d) :
      SpecializedFunctor (s ↓ F) (d ↓ F).
      refine (Build_SpecializedFunctor (s ↓ F) (d ↓ F)
                                       (@CosliceCategoryInducedFunctor_ObjectOf s d m)
                                       (@CosliceCategoryInducedFunctor_MorphismOf s d m)
                                       _
                                       _
             );
      subst_body; simpl;
      abstract anihilate.
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
    Local Notation "C / c" := (SliceSpecializedCategoryOver C c).

    Let SliceCategoryProjectionFunctor_ObjectOf (d : D) : LocallySmallCat / C
      := existT _
                ((F ↓ d : LocallySmallSpecializedCategory _) : LocallySmallCategory, tt)
                (SliceCategoryProjection d F) :
           CommaSpecializedCategory_ObjectT (IdentityFunctor _)
                                            (SliceSpecializedCategory_Functor LocallySmallCat C).

    Definition SliceCategoryProjectionFunctor_MorphismOf s d (m : Morphism D s d) :
      CommaSpecializedCategory_MorphismT
        (SliceCategoryProjectionFunctor_ObjectOf s)
        (SliceCategoryProjectionFunctor_ObjectOf d).
      subst_body;
      hnf; simpl.
      exists (SliceCategoryInducedFunctor (C := C) (D := D) F s d m, tt).
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
    Local Notation "C / c" := (SliceSpecializedCategoryOver C c).

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
      exists (CosliceCategoryInducedFunctor (C := C) (D := D) F s d m, tt).
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
