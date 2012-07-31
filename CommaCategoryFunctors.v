Require Import ProofIrrelevance FunctionalExtensionality JMeq.
Require Export SpecializedCommaCategory SmallCat Duals.
Require Import Common DiscreteCategory FEqualDep.

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

  Local Notation "S ↓ T" := (CommaSpecializedCategory S T) (at level 70, no associativity).

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

Section SliceCategoryFunctor.
  Variable C : LocallySmallCategory.
  Variable D : Category.
  Variable F : SpecializedFunctor C D. (* [SpecializedFunctor], not [Functor], because otherwise Sort-poylmorphism won't work *)

  Section Slice.
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F) (at level 70, no associativity).
    Local Notation "C / c" := (@SliceSpecializedCategoryOver _ _ C c).

    Let SliceCategoryProjectionFunctor_ObjectOf (d : D) : LocallySmallCat / C.
      constructor.
      exact (existT (fun _ => _) ((F ↓ d : LocallySmallSpecializedCategory _) : LocallySmallCategory, tt) (SliceCategoryProjection d F)).
    Defined.

    Let SliceCategoryProjectionFunctor_Morphism_ObjectOf s d (m : Morphism D s d) :
      CommaSpecializedCategory_Object F (SliceSpecializedCategory_Functor D s) ->
      CommaSpecializedCategory_Object F (SliceSpecializedCategory_Functor D d).
      intro x; constructor.
      exact (existT _ (projT1 x) (Compose m (projT2 x))).
    Defined.

    Let SliceCategoryProjectionFunctor_Morphism_MorphismOf s d (m : Morphism D s d) : forall
      (s0 d0 : CommaSpecializedCategory_Object F (SliceSpecializedCategory_Functor D s))
      (m0 : CommaSpecializedCategory_Morphism s0 d0),
      CommaSpecializedCategory_Morphism
      (@SliceCategoryProjectionFunctor_Morphism_ObjectOf s d m s0)
      (@SliceCategoryProjectionFunctor_Morphism_ObjectOf s d m d0).
      subst SliceCategoryProjectionFunctor_Morphism_ObjectOf.
      intros s0 d0 m0.
      constructor; simpl in *.
      exists (projT1 m0).
      subst_body; simpl; intros.
      abstract (
        destruct m0 as [ [ ? ? ] ]; simpl in *;
          rewrite LeftIdentity in *;
            repeat rewrite Associativity;
              apply f_equal;
                assumption
      ).
    Defined.

    Let SliceCategoryProjectionFunctor_Morphism_Functor s d (m : Morphism D s d) :
      SpecializedFunctor (F ↓ s) (F ↓ d).
      refine {| ObjectOf' := @SliceCategoryProjectionFunctor_Morphism_ObjectOf s d m;
        MorphismOf' := @SliceCategoryProjectionFunctor_Morphism_MorphismOf s d m
      |};
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

    Definition SliceCategoryProjectionFunctor_MorphismOf s d (m : Morphism D s d) :
      CommaSpecializedCategory_MorphismT
      (SliceCategoryProjectionFunctor_ObjectOf s)
      (SliceCategoryProjectionFunctor_ObjectOf d).
      Transparent Morphism.
      hnf; simpl.
      exists (@SliceCategoryProjectionFunctor_Morphism_Functor s d m, tt).
      subst_body; simpl; intros.
      abstract (
        functor_eq;
        f_equal;
        match goal with
          | [ |- proj1_sig ?x = projT1 _ ] => destruct x; simpl; reflexivity
        end
      ).
    Defined.

    Definition SliceCategoryProjectionFunctor : Functor D (LocallySmallCat / C).
      refine (Build_SpecializedFunctor D (LocallySmallCat / (C : LocallySmallCategory))
        (@SliceCategoryProjectionFunctor_ObjectOf)
        (@SliceCategoryProjectionFunctor_MorphismOf)
        _
        _
      );
      subst_body;
      abstract slice_t.
    Defined.
  End Slice.

  Section Coslice.
    Local Notation "A ↓ F" := (CosliceSpecializedCategory A F) (at level 70, no associativity).
    Local Notation "C / c" := (@SliceSpecializedCategoryOver _ _ C c).

    Let DOp := OppositeCategory D.

    Let CosliceCategoryProjectionFunctor_ObjectOf (d : D) : LocallySmallCat / C.
      constructor.
      exact (existT (fun _ => _) ((d ↓ F : LocallySmallSpecializedCategory _) : LocallySmallCategory, tt) (CosliceCategoryProjection d F)).
    Defined.

    Let CosliceCategoryProjectionFunctor_Morphism_ObjectOf s d (m : Morphism DOp s d) :
      CommaSpecializedCategory_Object (SliceSpecializedCategory_Functor D s) F ->
      CommaSpecializedCategory_Object (SliceSpecializedCategory_Functor D d) F.
      intro x; constructor.
      exact (existT _ (projT1 x) (Compose (projT2 x) m)).
    Defined.

    Let CosliceCategoryProjectionFunctor_Morphism_MorphismOf s d (m : Morphism DOp s d) : forall
      (s0 d0 : CommaSpecializedCategory_Object (SliceSpecializedCategory_Functor D s) F)
      (m0 : CommaSpecializedCategory_Morphism s0 d0),
      CommaSpecializedCategory_Morphism
      (@CosliceCategoryProjectionFunctor_Morphism_ObjectOf s d m s0)
      (@CosliceCategoryProjectionFunctor_Morphism_ObjectOf s d m d0).
      subst CosliceCategoryProjectionFunctor_Morphism_ObjectOf.
      intros s0 d0 m0.
      constructor; simpl in *.
      exists (projT1 m0).
      subst_body; simpl; intros.
      abstract (
        destruct m0 as [ [ ? ? ] ]; simpl in *;
          rewrite RightIdentity in *;
            repeat rewrite <- Associativity;
              f_equal;
              assumption
      ).
    Defined.

    Let CosliceCategoryProjectionFunctor_Morphism_Functor (s d : D) (m : Morphism DOp s d) :
      SpecializedFunctor (s ↓ F) (d ↓ F).
      refine (Build_SpecializedFunctor (s ↓ F) (d ↓ F)
        (@CosliceCategoryProjectionFunctor_Morphism_ObjectOf s d m)
        (@CosliceCategoryProjectionFunctor_Morphism_MorphismOf s d m)
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

    Definition CosliceCategoryProjectionFunctor_MorphismOf (s d : D) (m : Morphism DOp s d) :
      CommaSpecializedCategory_MorphismT
      (CosliceCategoryProjectionFunctor_ObjectOf s)
      (CosliceCategoryProjectionFunctor_ObjectOf d).
      Transparent Morphism.
      hnf; simpl.
      exists (@CosliceCategoryProjectionFunctor_Morphism_Functor s d m, tt).
      subst_body; simpl; intros.
      abstract (
        functor_eq;
        f_equal;
        match goal with
          | [ |- proj1_sig ?x = projT1 _ ] => destruct x; simpl; reflexivity
        end
      ).
    Defined.

    Definition CosliceCategoryProjectionFunctor : Functor DOp (LocallySmallCat / C).
      refine (Build_SpecializedFunctor DOp (LocallySmallCat / (C : LocallySmallCategory))
        (@CosliceCategoryProjectionFunctor_ObjectOf)
        (@CosliceCategoryProjectionFunctor_MorphismOf)
        _
        _
      );
      subst_body;
      abstract slice_t.
    Defined.
  End Coslice.
End SliceCategoryFunctor.
