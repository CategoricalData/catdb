Require Import (*ProofIrrelevance FunctionalExtensionality *) JMeq.
Require Export SpecializedCommaCategory SmallCat Duals ProductCategory FunctorCategory.
Require Import Common Notations DefinitionSimplification DiscreteCategory FEqualDep DefinitionSimplification ExponentialLaws FunctorProduct ProductLaws.

Set Implicit Arguments.

Generalizable All Variables.

Local Notation "C / a" := (@SliceSpecializedCategoryOver _ C a) : category_scope.
Local Notation "a \ C" := (@CosliceSpecializedCategoryOver _ C a) (at level 70) : category_scope.

Local Open Scope category_scope.

Local Ltac rewrite_step :=
  (progress repeat rewrite @LeftIdentity in * )
    || (progress repeat rewrite @RightIdentity in * )
    || (progress repeat rewrite @LeftIdentityFunctor in * )
    || (progress repeat rewrite @RightIdentityFunctor in * )
    || (progress (repeat rewrite @Associativity; (reflexivity || apply f_equal)))
    || (progress (repeat rewrite <- @Associativity; apply f_equal2; trivial; [])).

Local Ltac quick_step :=
  ((progress repeat subst)
     || (apply sig_eq; simpl)
     || apply f_equal
     || (apply f_equal2; trivial; []));
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

Local Ltac slice_step :=
  match goal with
    | _ => apply Functor_eq; simpl; intros; pre_anihilate
    | [ |- @JMeq (sig _) _ (sig _) _ ] => apply sig_JMeq; pre_anihilate
    | [ |- JMeq (?f ?x) (?f ?y) ] =>
      apply (@f_equal1_JMeq _ _ x y f); pre_anihilate
    | [ |- JMeq (?f ?x) (?g ?y) ] =>
      apply (@f_equal_JMeq _ _ _ _ x y f g); pre_anihilate
  end.

Local Ltac step :=
  (quick_step
     || rewrite_step
     || (progress auto 1 with category)
     || slice_step);
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

  Local Arguments fst_Functor / .
  Local Arguments snd_Functor / .
  Local Arguments CommaCategoryProjection / .
  Local Arguments SliceSpecializedCategory_Functor / .

  Let ArrowCategoryProjection' : SpecializedFunctor (ArrowSpecializedCategory A) A
    := ComposeFunctors fst_Functor (CommaCategoryProjection _ (IdentityFunctor A)).
  Let ArrowCategoryProjection'' : SpecializedFunctor (ArrowSpecializedCategory A) A. functor_simpl_abstract_trailing_props ArrowCategoryProjection'. Defined.
  Definition ArrowCategoryProjection : SpecializedFunctor (ArrowSpecializedCategory A) A := Eval hnf in ArrowCategoryProjection''.

  Let SliceCategoryOverProjection' (a : A) : SpecializedFunctor (A / a) A
    := ComposeFunctors fst_Functor (CommaCategoryProjection (IdentityFunctor A) _).
  Let SliceCategoryOverProjection'' (a : A) : SpecializedFunctor (A / a) A. functor_simpl_abstract_trailing_props (SliceCategoryOverProjection' a). Defined.
  Definition SliceCategoryOverProjection (a : A) : SpecializedFunctor (A / a) A := Eval hnf in SliceCategoryOverProjection'' a.

  Let CosliceCategoryOverProjection' (a : A) : SpecializedFunctor (a \ A) A
    := ComposeFunctors snd_Functor (CommaCategoryProjection _ (IdentityFunctor A)).
  Let CosliceCategoryOverProjection'' (a : A) : SpecializedFunctor (a \ A) A. functor_simpl_abstract_trailing_props (CosliceCategoryOverProjection' a). Defined.
  Definition CosliceCategoryOverProjection (a : A) : SpecializedFunctor (a \ A) A := Eval hnf in CosliceCategoryOverProjection'' a.

  Section Slice_Coslice.
    Context `(C : @SpecializedCategory objC).
    Variable a : C.
    Variable S : SpecializedFunctor A C.

    Section Slice.
      Local Notation "F ↓ A" := (SliceSpecializedCategory A F).

      Let SliceCategoryProjection' : SpecializedFunctor (S ↓ a) A.
        functor_simpl_abstract_trailing_props (ComposeFunctors fst_Functor (CommaCategoryProjection S (SliceSpecializedCategory_Functor C a))).
      Defined.
      Definition SliceCategoryProjection : SpecializedFunctor (S ↓ a) A := Eval hnf in SliceCategoryProjection'.
    End Slice.

    Section Coslice.
      Local Notation "A ↓ F" := (CosliceSpecializedCategory A F).

      Let CosliceCategoryProjection' : SpecializedFunctor (a ↓ S) A.
        functor_simpl_abstract_trailing_props (ComposeFunctors snd_Functor (CommaCategoryProjection (SliceSpecializedCategory_Functor C a) S)).
      Defined.
      Definition CosliceCategoryProjection : SpecializedFunctor (a ↓ S) A := Eval hnf in CosliceCategoryProjection'.
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
      simpl in *; clear.
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
    subst_body; simpl; clear;
    (* admit. *)
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
      simpl; intros; present_spcategory; clear;
      abstract (autorewrite with category; reflexivity).
    Defined.

    Variable F : SpecializedFunctor C D.
    Variable a : D.

    Section Slice.
      Local Notation "F ↓ A" := (SliceSpecializedCategory A F).

      Let SliceCategoryInducedFunctor' F' a' (m : Morphism D a a') (T : SpecializedNaturalTransformation F' F) :
        SpecializedFunctor (F ↓ a) (F' ↓ a').
        functor_simpl_abstract_trailing_props (CommaCategoryInducedFunctor (s := (F, SliceSpecializedCategory_Functor D a))
                                                                       (d := (F', SliceSpecializedCategory_Functor D a'))
                                                                       (T, @SliceCategoryInducedFunctor_NT a a' m)).
      Defined.
      Definition SliceCategoryInducedFunctor F' a' (m : Morphism D a a') (T : SpecializedNaturalTransformation F' F) :
        SpecializedFunctor (F ↓ a) (F' ↓ a')
        := Eval hnf in @SliceCategoryInducedFunctor' F' a' m T.

      Definition SliceCategoryNTInducedFunctor F' T := @SliceCategoryInducedFunctor F' a (Identity _) T.
      Definition SliceCategoryMorphismInducedFunctor a' m := @SliceCategoryInducedFunctor F a' m (IdentityNaturalTransformation _).
    End Slice.

    Section Coslice.
      Local Notation "A ↓ F" := (CosliceSpecializedCategory A F).

      Let CosliceCategoryInducedFunctor' F' a' (m : Morphism D a' a) (T : SpecializedNaturalTransformation F F') :
        SpecializedFunctor (a ↓ F) (a' ↓ F').
        functor_simpl_abstract_trailing_props (CommaCategoryInducedFunctor (s := (SliceSpecializedCategory_Functor D a, F))
                                                                       (d := (SliceSpecializedCategory_Functor D a', F'))
                                                                       (@SliceCategoryInducedFunctor_NT a' a m, T)).
      Defined.
      Definition CosliceCategoryInducedFunctor F' a' (m : Morphism D a' a) (T : SpecializedNaturalTransformation F F') :
        SpecializedFunctor (a ↓ F) (a' ↓ F')
        := Eval hnf in @CosliceCategoryInducedFunctor' F' a' m T.

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
  (*Local Opaque LocallySmallCat.*)

  Let LocallySmallCatOverInducedFunctor_ObjectOf a a' (m : Morphism C a a') : C / a -> C / a'.
    refine (fun x => existT (fun αβ : _ * unit => Morphism C (fst αβ) a')
                            (projT1 x)
                            _ :
                       CommaSpecializedCategory_ObjectT (IdentityFunctor C) (SliceSpecializedCategory_Functor C a')).
    functor_simpl_abstract_trailing_props (Compose m (projT2 x)).
  Defined.
  Let OverLocallySmallCatInducedFunctor_ObjectOf a a' (m : Morphism C a' a) : a \ C -> a' \ C.
    refine (fun x => existT (fun αβ : unit * _ => Morphism C a' (snd αβ))
                            (projT1 x)
                            _ :
                       CommaSpecializedCategory_ObjectT (SliceSpecializedCategory_Functor C a') (IdentityFunctor C)).
    functor_simpl_abstract_trailing_props (Compose (projT2 x) m).
  Defined.

  Let LocallySmallCatOverInducedFunctor_MorphismOf a a' (m : Morphism C a a') s d (m0 : Morphism (C / a) s d) :
    Morphism (C / a') (@LocallySmallCatOverInducedFunctor_ObjectOf _ _ m s) (@LocallySmallCatOverInducedFunctor_ObjectOf _ _ m d).
    refine (_ : CommaSpecializedCategory_MorphismT _ _).
    exists (projT1 m0).
      subst_body; simpl in *; clear.
    abstract anihilate.
  Defined.
  Let OverLocallySmallCatInducedFunctor_MorphismOf a a' (m : Morphism C a' a) s d (m0 : Morphism (a \ C) s d) :
    Morphism (a' \ C) (@OverLocallySmallCatInducedFunctor_ObjectOf _ _ m s) (@OverLocallySmallCatInducedFunctor_ObjectOf _ _ m d).
    refine (_ : CommaSpecializedCategory_MorphismT _ _).
    exists (projT1 m0);
      subst_body; simpl in *; clear.
    abstract anihilate.
  Defined.

  Local Opaque LocallySmallCat.
  Let LocallySmallCatOverInducedFunctor'' a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a').
    refine (Build_SpecializedFunctor (C / a) (C / a')
                                     (@LocallySmallCatOverInducedFunctor_ObjectOf _ _ m)
                                     (@LocallySmallCatOverInducedFunctor_MorphismOf _ _ m)
                                     _
                                     _
           );
    subst_body; simpl; clear;
    (* admit. *)
    abstract anihilate.
  Defined.
  Let OverLocallySmallCatInducedFunctor'' a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C).
    refine (Build_SpecializedFunctor (a \ C) (a' \ C)
                                     (@OverLocallySmallCatInducedFunctor_ObjectOf _ _ m)
                                     (@OverLocallySmallCatInducedFunctor_MorphismOf _ _ m)
                                     _
                                     _
           );
    subst_body; simpl; clear;
    (* admit. *) abstract anihilate.
  Defined.

  Let LocallySmallCatOverInducedFunctor''' a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a').
    simpl_definition_by_tac_and_exact (@LocallySmallCatOverInducedFunctor'' _ _ m) ltac:(subst_body; eta_red).
  Defined.
  Let OverLocallySmallCatInducedFunctor''' a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C).
    simpl_definition_by_tac_and_exact (@OverLocallySmallCatInducedFunctor'' _ _ m) ltac:(subst_body; eta_red).
  Defined.

  Definition LocallySmallCatOverInducedFunctor a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a')
    := Eval cbv beta iota zeta delta [LocallySmallCatOverInducedFunctor'''] in @LocallySmallCatOverInducedFunctor''' _ _ m.
  Definition OverLocallySmallCatInducedFunctor a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C)
    := Eval cbv beta iota zeta delta [OverLocallySmallCatInducedFunctor'''] in @OverLocallySmallCatInducedFunctor''' _ _ m.
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
    exists (CommaCategoryInducedFunctor m, @unit_eq _ _).
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
    (* admit. *) Time (expand; anihilate). (* 20 s  :-( *)
  Qed.

  Lemma CommaCategoryProjectionFunctor_FCompositionOf s d d' m m' :
    CommaCategoryProjectionFunctor_MorphismOf (@Compose _ _ s d d' m m')
    = Compose (CommaCategoryProjectionFunctor_MorphismOf m)
              (CommaCategoryProjectionFunctor_MorphismOf m').
    (* admit. *) Time (expand; anihilate). (* 57 s  :-( :-( *)
  Qed.

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

  Local Arguments ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf / .
  Local Arguments ComposeFunctors / .
  Local Arguments LocallySmallCatOverInducedFunctor / .
  (*Local Arguments ProductLaw1Functor / . *)
  Local Arguments CommaCategoryProjectionFunctor / .
  Local Arguments SwapFunctor / .
  Local Arguments ExponentialLaw1Functor_Inverse / .
  Local Arguments IdentityFunctor / .
(*
  Let ArrowCategoryProjection' : SpecializedFunctor (ArrowSpecializedCategory A) A
    := ComposeFunctors fst_Functor (CommaCategoryProjection _ (IdentityFunctor A)).
  Let ArrowCategoryProjection'' : SpecializedFunctor (ArrowSpecializedCategory A) A. functor_simpl_abstract_trailing_props ArrowCategoryProjection'. Defined.
  Definition ArrowCategoryProjection : SpecializedFunctor (ArrowSpecializedCategory A) A := Eval hnf in ArrowCategoryProjection''.
*)

  Definition SliceCategoryProjectionFunctor_pre_pre'
    := Eval hnf in (LocallySmallCatOverInducedFunctor (ProductLaw1Functor C : Morphism LocallySmallCat (C * 1 : LocallySmallSpecializedCategory _) C)).

  Definition SliceCategoryProjectionFunctor_pre_pre : SpecializedFunctor (LocallySmallCat / (C * 1 : LocallySmallSpecializedCategory _)) (LocallySmallCat / C).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor_pre_pre'.
  Defined.

  Arguments SliceCategoryProjectionFunctor_pre_pre / .

(*  Arguments Build_CommaSpecializedCategory_Object' / .

  Eval simpl in SliceCategoryProjectionFunctor_pre_pre'.

  Set Printing Coercions.
  Print SliceCategoryProjectionFunctor_pre_pre'.
    functor_abstract_trailing_props
  Defined.

*)
  (*Local Ltac pose_functor_by_abstract H F :=
    let T := type of F in assert (H : T) by (functor_simpl_abstract_trailing_props F).

  Local Ltac refine_right_compose_functor_by_abstract F :=
    let H := fresh in pose_functor_by_abstract H F; refine (ComposeFunctors _ H); clear H.*)

  Definition SliceCategoryProjectionFunctor_pre' : ((LocallySmallCat / C) ^ (D * (OppositeCategory (D ^ C)))).
    refine (ComposeFunctors _ ((ExponentialLaw1Functor_Inverse D) * IdentityFunctor (OppositeCategory (D ^ C)))).
    refine (ComposeFunctors _ (SwapFunctor _ _)).
    refine (ComposeFunctors _ (CommaCategoryProjectionFunctor (C : LocallySmallSpecializedCategory _) (1 : LocallySmallSpecializedCategory _) D)).
    (*
    refine_right_compose_functor_by_abstract ((ExponentialLaw1Functor_Inverse D) * IdentityFunctor (OppositeCategory (D ^ C)))%functor.
    refine_right_compose_functor_by_abstract (SwapFunctor (D ^ 1)%functor (OppositeCategory (D ^ C)%functor)).
    refine_right_compose_functor_by_abstract (CommaCategoryProjectionFunctor (C : LocallySmallSpecializedCategory _) (1 : LocallySmallSpecializedCategory _) D).*)
    let F := (eval hnf in SliceCategoryProjectionFunctor_pre_pre) in
    exact F.
(* (LocallySmallCatOverInducedFunctor (ProductLaw1Functor C : Morphism LocallySmallCat (C * 1 : LocallySmallSpecializedCategory _) (C : LocallySmallSpecializedCategory _))). *)
  Defined.

  Definition SliceCategoryProjectionFunctor_pre'' : ((LocallySmallCat / C) ^ (D * (OppositeCategory (D ^ C)))).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor_pre'.
  Defined.

  Definition SliceCategoryProjectionFunctor_pre := Eval hnf in SliceCategoryProjectionFunctor_pre''.

  Definition SliceCategoryProjectionFunctor' : (((LocallySmallCat / C) ^ D) ^ (OppositeCategory (D ^ C))).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    let F := (eval hnf in SliceCategoryProjectionFunctor_pre) in
    exact F.
  Defined.

  Definition SliceCategoryProjectionFunctor'' : (((LocallySmallCat / C) ^ D) ^ (OppositeCategory (D ^ C))).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor'.
  Defined.

  Definition SliceCategoryProjectionFunctor : ((LocallySmallCat / C) ^ D) ^ (OppositeCategory (D ^ C))
    := Eval cbv beta iota zeta delta [SliceCategoryProjectionFunctor''] in SliceCategoryProjectionFunctor''.

  Definition CosliceCategoryProjectionFunctor : ((LocallySmallCat / C) ^ (OppositeCategory D)) ^ (D ^ C).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    refine (ComposeFunctors _ ((OppositeFunctor (ExponentialLaw1Functor_Inverse D)) * IdentityFunctor (D ^ C))).
    refine (ComposeFunctors _ (CommaCategoryProjectionFunctor (1 : LocallySmallSpecializedCategory _) (C : LocallySmallSpecializedCategory _) D)).
    refine (LocallySmallCatOverInducedFunctor _).
    refine (ComposeFunctors _ (SwapFunctor _ _)).
    exact (ProductLaw1Functor _).
  Defined.
End SliceCategoryProjectionFunctor.
