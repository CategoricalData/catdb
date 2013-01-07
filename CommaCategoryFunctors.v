Require Import (*ProofIrrelevance FunctionalExtensionality *) JMeq.
Require Export SpecializedCommaCategory SmallCat Duals ProductCategory FunctorCategory.
Require Import Common Notations DiscreteCategory FEqualDep DefinitionSimplification.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope category_scope.

Local Notation "C / a" := (SliceSpecializedCategory a (IdentityFunctor C)) : category_scope.
Local Notation "a \ C" := (CosliceSpecializedCategory a (IdentityFunctor C)) (at level 70) : category_scope.

Local Ltac slice_t :=
  repeat match goal with
           | [ |- @JMeq (sig _) _ (sig _) _ ] => apply sig_JMeq
           | [ |- (_ -> _) = (_ -> _) ] => apply f_type_equal
           | _ => progress (intros; simpl in *; subst_body; simpl in *; trivial)
           | _ => progress (simpl_eq; simpl in *; trivial)
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
           | [ |- @eq ?T ?A ?B ] => let T' := eval hnf in T in progress change (@eq T' A B)
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
  unfold Object in *;
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

  Definition ArrowCategoryProjection : SpecializedFunctor (ArrowSpecializedCategory A) A
    := ComposeFunctors fst_Functor (CommaCategoryProjection _ (IdentityFunctor A)).

  Definition SliceCategoryOverProjection (a : A) : SpecializedFunctor (A / a) A
    := ComposeFunctors fst_Functor (CommaCategoryProjection (IdentityFunctor A) _).

  Definition CosliceCategoryOverProjection (a : A) : SpecializedFunctor (a \ A) A
    := ComposeFunctors snd_Functor (CommaCategoryProjection _ (IdentityFunctor A)).

  Section Slice_Coslice.
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
  End Slice_Coslice.
End SliceCategory.


Section CommaCategoryInducedFunctor.
  Context `(A : @SpecializedCategory objA).
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).

  Local Notation "S ↓ T" := (CommaSpecializedCategory S T).

  Local Ltac induced_step :=
    reflexivity
      || (try_associativity ltac:(rewrite <- Commutes))
      || (try_associativity ltac:(apply f_equal))
      || (match goal with
            | [ H : _ = _ |- _ = _ ] => try_associativity ltac:(rewrite H)
          end).

  Local Ltac induced_anihilate :=
    unfold Object in *;
    simpl in *;
    destruct_head @prod;
    simpl in *;
    pre_anihilate;
    repeat induced_step.

  Let CommaCategoryInducedFunctor_ObjectOf s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d)
      (x : fst s ↓ snd s) : (fst d ↓ snd d)
    := existT _
              (projT1 x)
              (Compose ((snd m) (snd (projT1 x))) (Compose (projT2 x) ((fst m) (fst (projT1 x))))) :
         CommaSpecializedCategory_ObjectT (fst d) (snd d).

  Let CommaCategoryInducedFunctor_MorphismOf s d m s0 d0 (m0 : Morphism (fst s ↓ snd s) s0 d0) :
    Morphism (fst d ↓ snd d)
             (@CommaCategoryInducedFunctor_ObjectOf s d m s0)
             (@CommaCategoryInducedFunctor_ObjectOf s d m d0).
    hnf in *; subst_body; constructor; simpl in *.
    exists (projT1 m0).
    abstract induced_anihilate.
  Defined.

  Let CommaCategoryInducedFunctor' s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    SpecializedFunctor (fst s ↓ snd s) (fst d ↓ snd d).
    refine (Build_SpecializedFunctor (fst s ↓ snd s) (fst d ↓ snd d)
                                     (@CommaCategoryInducedFunctor_ObjectOf s d m)
                                     (@CommaCategoryInducedFunctor_MorphismOf s d m)
                                     _
                                     _
           );
    subst_body; simpl;
    abstract pre_anihilate. (* TODO(jgross): speed this up :-( *)
  Defined.

  Let CommaCategoryInducedFunctor'' s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    SpecializedFunctor (fst s ↓ snd s) (fst d ↓ snd d).
    simpl_definition_by_tac_and_exact (@CommaCategoryInducedFunctor' s d m) ltac:(subst_body; eta_red).
  Defined.

  Definition CommaCategoryInducedFunctor s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    SpecializedFunctor (fst s ↓ snd s) (fst d ↓ snd d)
    := Eval cbv beta iota zeta delta [CommaCategoryInducedFunctor''] in @CommaCategoryInducedFunctor'' s d m.
End CommaCategoryInducedFunctor.

Section SliceCategoryNTInducedFunctor.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variables F F' : SpecializedFunctor C D.
  Variable a : D.

  Section Slice.
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F).

    Definition SliceCategoryNTInducedFunctor (T : SpecializedNaturalTransformation F' F) : SpecializedFunctor (F ↓ a) (F' ↓ a)
      := CommaCategoryInducedFunctor (s := (F, _))
                                     (d := (F', _))
                                     (T, IdentityNaturalTransformation (SliceSpecializedCategory_Functor D a)).
  End Slice.

  Section Coslice.
    Local Notation "A ↓ F" := (CosliceSpecializedCategory A F).

    Definition CosliceCategoryNTInducedFunctor (T : SpecializedNaturalTransformation F F') : SpecializedFunctor (a ↓ F) (a ↓ F')
      := CommaCategoryInducedFunctor (s := (_, F))
                                     (d := (_, F'))
                                     (IdentityNaturalTransformation (SliceSpecializedCategory_Functor D a), T).
  End Coslice.
End SliceCategoryNTInducedFunctor.

Section SliceCategoryInducedFunctor.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.

  Definition SliceCategoryInducedFunctor_NT s d (m : Morphism D s d) :
    SpecializedNaturalTransformation (SliceSpecializedCategory_Functor D s)
                                     (SliceSpecializedCategory_Functor D d).
    exists (fun _ : unit => m).
    simpl; intros; present_spcategory;
    abstract (autorewrite with category; reflexivity).
  Defined.

  Section Slice.
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F).

    Definition SliceCategoryInducedFunctor s d (m : Morphism D s d) :
      SpecializedFunctor (F ↓ s) (F ↓ d)
      := CommaCategoryInducedFunctor (s := (_, _))
                                     (d := (_, _))
                                     (IdentityNaturalTransformation F, @SliceCategoryInducedFunctor_NT s d m).
  End Slice.

  Section Coslice.
    Local Notation "A ↓ F" := (CosliceSpecializedCategory A F).

    Let DOp := OppositeCategory D.

    Definition CosliceCategoryInducedFunctor (s d : D) (m : Morphism DOp s d) :
      SpecializedFunctor (s ↓ F) (d ↓ F)
      := CommaCategoryInducedFunctor (s := (_, _))
                                     (d := (_, _))
                                     (@SliceCategoryInducedFunctor_NT d s m, IdentityNaturalTransformation F).
  End Coslice.
End SliceCategoryInducedFunctor.


Section CommaCategoryProjectionFunctor.
  Variables A B : LocallySmallCategory.
  Variable C : Category.
  (*Variable S : SpecializedFunctor A C.
  Variable T : SpecializedFunctor B C. (* [SpecializedFunctor], not [Functor], because otherwise Sort-poylmorphism won't work *)*)

  Local Notation "S ↓ T" := (CommaSpecializedCategory S T).
  Local Notation "C / c" := (SliceSpecializedCategoryOver C c).

  Definition CommaCategoryProjectionFunctor_ObjectOf (ST : (OppositeCategory (C ^ A)) * (C ^ B)) :
    LocallySmallCat / (A * B : LocallySmallSpecializedCategory _)
    := let S := (fst ST) in
       let T := (snd ST) in
       existT _
              ((S ↓ T : LocallySmallSpecializedCategory _) : LocallySmallCategory, tt)
              (CommaCategoryProjection S T) :
         CommaSpecializedCategory_ObjectT (IdentityFunctor _)
                                          (SliceSpecializedCategory_Functor LocallySmallCat
                                                                            (A * B : LocallySmallSpecializedCategory _)).

  Definition CommaCategoryProjectionFunctor_MorphismOf s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    Morphism (LocallySmallCat / (A * B : LocallySmallSpecializedCategory _))
             (CommaCategoryProjectionFunctor_ObjectOf s)
             (CommaCategoryProjectionFunctor_ObjectOf d).
    hnf in *; constructor; simpl in *.
    exists (CommaCategoryInducedFunctor m, tt).
    abstract (
        simpl;
        functor_eq;
        destruct_head_hnf @CommaSpecializedCategory_Morphism;
        destruct_sig;
        reflexivity
      ).
  Defined.

  Lemma CommaCategoryProjectionFunctor_FIdentityOf x :
    CommaCategoryProjectionFunctor_MorphismOf (Identity x) = Identity _.
    abstract (expand; slice_t).
  Qed.

  Lemma CommaCategoryProjectionFunctor_FCompositionOf s d d' m m' :
    CommaCategoryProjectionFunctor_MorphismOf (@Compose _ _ s d d' m m')
    = Compose (CommaCategoryProjectionFunctor_MorphismOf m)
              (CommaCategoryProjectionFunctor_MorphismOf m').
    (* expand; slice_t. (* TODO(jgross): Fix that this is painfully slow *)
  Qed. *)
  Admitted.

  Definition CommaCategoryProjectionFunctor :
    SpecializedFunctor ((OppositeCategory (C ^ A)) * (C ^ B))
                       (LocallySmallCat / (A * B : LocallySmallSpecializedCategory _)).
    refine (Build_SpecializedFunctor ((OppositeCategory (C ^ A)) * (C ^ B))
                                     (LocallySmallCat / (A * B : LocallySmallSpecializedCategory _))
                                     CommaCategoryProjectionFunctor_ObjectOf
                                     CommaCategoryProjectionFunctor_MorphismOf
                                     _
                                     _);
    intros; present_spcategory;
    [ apply CommaCategoryProjectionFunctor_FCompositionOf
    | apply CommaCategoryProjectionFunctor_FIdentityOf ].
  Defined.
End CommaCategoryProjectionFunctor.

Section SliceCategoryProjectionFunctor.
  Variable C : LocallySmallCategory.
  Variable D : Category.
  Variable F : SpecializedFunctor C D. (* [SpecializedFunctor], not [Functor], because otherwise Sort-poylmorphism won't work *)

  Section Slice.
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F).
    Local Notation "C / c" := (SliceSpecializedCategoryOver C c).

    Definition SliceCategoryProjectionFunctor_ObjectOf (x : D) : LocallySmallCat / C.
      pose (@CommaCategoryProjectionFunctor (TerminalCategory : LocallySmallSpecializedCategory _) C D); simpl in *.

    Definition SliceCategoryProjectionFunctor : Functor D (LocallySmallCat / C).
      pose (@CommaCategoryProjectionFunctor (TerminalCategory : LocallySmallSpecializedCategory _) C D); simpl in *.
      (* HERE *)
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
