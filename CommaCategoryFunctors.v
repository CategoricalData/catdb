Require Import (*ProofIrrelevance FunctionalExtensionality *) JMeq.
Require Export SpecializedCommaCategory SmallCat Duals ProductCategory FunctorCategory.
Require Import Common Notations DefinitionSimplification DiscreteCategory FEqualDep DefinitionSimplification ExponentialLaws FunctorProduct ProductLaws.

Set Implicit Arguments.

Generalizable All Variables.

Local Notation "C / a" := (@SliceSpecializedCategoryOver _ C a) : category_scope.
Local Notation "a \ C" := (@CosliceSpecializedCategoryOver _ C a) (at level 70) : category_scope.

Local Open Scope category_scope.

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
    refine (_ : CommaSpecializedCategory_MorphismT _ _); subst_body; simpl in *.
    exists (projT1 m0);
      simpl in *.
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

Section SliceCategoryInducedFunctor.
  Context `(C : @SpecializedCategory objC).

  Section Slice_Coslice.
    Context `(D : @SpecializedCategory objD).

    (* TODO(jgross): See if this can be recast as an exponential law functor about how Cat ^ 1 is isomorphic to Cat, or something *)
    Definition SliceCategoryInducedFunctor_NT s d (m : Morphism D s d) :
      SpecializedNaturalTransformation (SliceSpecializedCategory_Functor D s)
                                       (SliceSpecializedCategory_Functor D d).
      exists (fun _ : unit => m).
      simpl; intros; present_spcategory;
      abstract (autorewrite with category; reflexivity).
    Defined.

    Variables F : SpecializedFunctor C D.
    Variable a : D.

    Section Slice.
      Local Notation "F ↓ A" := (SliceSpecializedCategory A F).

      Definition SliceCategoryInducedFunctor F' a' (m : Morphism D a a') (T : SpecializedNaturalTransformation F' F) :
        SpecializedFunctor (F ↓ a) (F' ↓ a')
        := CommaCategoryInducedFunctor (s := (F, SliceSpecializedCategory_Functor D a))
                                       (d := (F', SliceSpecializedCategory_Functor D a'))
                                       (T, @SliceCategoryInducedFunctor_NT a a' m).

      Definition SliceCategoryNTInducedFunctor F' T := @SliceCategoryInducedFunctor F' a (Identity _) T.
      Definition SliceCategoryMorphismInducedFunctor a' m := @SliceCategoryInducedFunctor F a' m (IdentityNaturalTransformation _).
    End Slice.

    Section Coslice.
      Local Notation "A ↓ F" := (CosliceSpecializedCategory A F).

      Definition CosliceCategoryInducedFunctor F' a' (m : Morphism D a' a) (T : SpecializedNaturalTransformation F F') :
        SpecializedFunctor (a ↓ F) (a' ↓ F')
        := CommaCategoryInducedFunctor (s := (SliceSpecializedCategory_Functor D a, F))
                                       (d := (SliceSpecializedCategory_Functor D a', F'))
                                       (@SliceCategoryInducedFunctor_NT a' a m, T).

      Definition CosliceCategoryNTInducedFunctor F' T := @CosliceCategoryInducedFunctor F' a (Identity _) T.
      Definition CosliceCategoryMorphismInducedFunctor a' m := @CosliceCategoryInducedFunctor F a' m (IdentityNaturalTransformation _).
    End Coslice.
  End Slice_Coslice.

  Definition SliceCategoryOverInducedFunctor a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a')
    := Eval hnf in SliceCategoryMorphismInducedFunctor _ _ _ m.
  Definition CosliceCategoryOverInducedFunctor a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C)
    := Eval hnf in CosliceCategoryMorphismInducedFunctor _ _ _ m.
End SliceCategoryInducedFunctor.

Section LocallySmallCatOverInducedFunctor.
  (* Let's do this from scratch so we get better polymorphism *)
  Let C := LocallySmallCat.
  Local Opaque LocallySmallCat.

  Let SliceCategoryOverInducedFunctor_ObjectOf a a' (m : Morphism C a a') : C / a -> C / a'
    := fun x => existT (fun αβ : _ * unit => Morphism C (fst αβ) a')
                       (projT1 x)
                       (Compose m (projT2 x)) :
                  CommaSpecializedCategory_ObjectT (IdentityFunctor C) (SliceSpecializedCategory_Functor C a').
  Let CosliceCategoryOverInducedFunctor_ObjectOf a a' (m : Morphism C a' a) : a \ C -> a' \ C
    := fun x => existT (fun αβ : unit * _ => Morphism C a' (snd αβ))
                       (projT1 x)
                       (Compose (projT2 x) m) :
                  CommaSpecializedCategory_ObjectT (SliceSpecializedCategory_Functor C a') (IdentityFunctor C).

  Let SliceCategoryOverInducedFunctor_MorphismOf a a' (m : Morphism C a a') s d (m0 : Morphism (C / a) s d) :
    Morphism (C / a') (@SliceCategoryOverInducedFunctor_ObjectOf _ _ m s) (@SliceCategoryOverInducedFunctor_ObjectOf _ _ m d).
    refine (_ : CommaSpecializedCategory_MorphismT _ _).
    exists (projT1 m0);
      simpl in *.
    abstract anihilate.
  Defined.
  Let CosliceCategoryOverInducedFunctor_MorphismOf a a' (m : Morphism C a' a) s d (m0 : Morphism (a \ C) s d) :
    Morphism (a' \ C) (@CosliceCategoryOverInducedFunctor_ObjectOf _ _ m s) (@CosliceCategoryOverInducedFunctor_ObjectOf _ _ m d).
    refine (_ : CommaSpecializedCategory_MorphismT _ _).
    exists (projT1 m0);
      simpl in *.
    abstract anihilate.
  Defined.

  Let SliceCategoryOverInducedFunctor'' a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a').
    refine (Build_SpecializedFunctor (C / a) (C / a')
                                     (@SliceCategoryOverInducedFunctor_ObjectOf _ _ m)
                                     (@SliceCategoryOverInducedFunctor_MorphismOf _ _ m)
                                     _
                                     _
           );
    subst_body; simpl;
    abstract anihilate.
  Defined.
  Let CosliceCategoryOverInducedFunctor'' a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C).
    refine (Build_SpecializedFunctor (a \ C) (a' \ C)
                                     (@CosliceCategoryOverInducedFunctor_ObjectOf _ _ m)
                                     (@CosliceCategoryOverInducedFunctor_MorphismOf _ _ m)
                                     _
                                     _
           );
    subst_body; simpl;
    abstract anihilate.
  Defined.

  Let SliceCategoryOverInducedFunctor''' a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a').
    simpl_definition_by_tac_and_exact (@SliceCategoryOverInducedFunctor'' _ _ m) ltac:(subst_body; eta_red).
  Defined.
  Let CosliceCategoryOverInducedFunctor''' a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C).
    simpl_definition_by_tac_and_exact (@CosliceCategoryOverInducedFunctor'' _ _ m) ltac:(subst_body; eta_red).
  Defined.

  Definition LocallySmallCatOverInducedFunctor a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a')
    := Eval cbv beta iota zeta delta [SliceCategoryOverInducedFunctor'''] in @SliceCategoryOverInducedFunctor''' _ _ m.
  Definition OverLocallySmallCatInducedFunctor a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C)
    := Eval cbv beta iota zeta delta [CosliceCategoryOverInducedFunctor'''] in @CosliceCategoryOverInducedFunctor''' _ _ m.
  Local Transparent LocallySmallCat.
End LocallySmallCatOverInducedFunctor.


Section CommaCategoryProjectionFunctor.
  Context `(A : LocallySmallSpecializedCategory objA).
  Context `(B : LocallySmallSpecializedCategory objB).
  Context `(C : SpecializedCategory objC).

  Local Notation "S ↓ T" := (CommaSpecializedCategory S T).

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
    (*abstract (expand; slice_t). (* TODO(jgross): Fix that this is painfully slow *)
  Qed.*)
  Admitted.

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
  Context `(C : LocallySmallSpecializedCategory objC).
  Context `(D : SpecializedCategory objD).

  Definition SliceCategoryProjectionFunctor : ((LocallySmallCat / C) ^ D) ^ (OppositeCategory (D ^ C)).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    refine (ComposeFunctors _ ((ExponentialLaw1Functor_Inverse D) * IdentityFunctor (OppositeCategory (D ^ C)))).
    refine (ComposeFunctors _ (SwapFunctor _ _)).
    refine (ComposeFunctors _ (CommaCategoryProjectionFunctor (C : LocallySmallSpecializedCategory _) (1 : LocallySmallSpecializedCategory _) D)).
    refine (LocallySmallCatOverInducedFunctor _).
    exact (ProductLaw1Functor _).
  Defined.

  Definition CosliceCategoryProjectionFunctor : ((LocallySmallCat / C) ^ (OppositeCategory D)) ^ (D ^ C).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    refine (ComposeFunctors _ ((OppositeFunctor (ExponentialLaw1Functor_Inverse D)) * IdentityFunctor (D ^ C))).
    refine (ComposeFunctors _ (CommaCategoryProjectionFunctor (1 : LocallySmallSpecializedCategory _) (C : LocallySmallSpecializedCategory _) D)).
    refine (LocallySmallCatOverInducedFunctor _).
    refine (ComposeFunctors _ (SwapFunctor _ _)).
    exact (ProductLaw1Functor _).
  Defined.
End SliceCategoryProjectionFunctor.
