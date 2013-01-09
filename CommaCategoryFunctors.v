Require Import (*ProofIrrelevance FunctionalExtensionality *) JMeq.
Require Export SpecializedCommaCategory SmallCat Duals ProductCategory FunctorCategory.
Require Import Common Notations DefinitionSimplification DiscreteCategory FEqualDep DefinitionSimplification ExponentialLaws FunctorProduct ProductLaws.

Set Implicit Arguments.

Generalizable All Variables.

Local Notation "C / a" := (@SliceSpecializedCategoryOver _ C a) : category_scope.
Local Notation "a \ C" := (@CosliceSpecializedCategoryOver _ C a) (at level 70) : category_scope.

Local Open Scope category_scope.

(* TODO(jgross): Move this somewhere better, give it a better name *)
Local Ltac build_non_prop_part_by' H :=
  match H with
    | ?f ?x => let t := type of x in
               match type of t with
                 | Prop => build_non_prop_part_by' f || fail 2 "Cannot build_non_prop_part_by'" f
                 | _ => apply H
               end
    | _ => apply H
  end.

Local Ltac build_non_prop_part_by H :=
  (let H' := eval hnf in H in let H'' := eval simpl in H' in build_non_prop_part_by' H'').

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
  Definition LocallySmallCatOverInducedFunctor a a' (m : Morphism LocallySmallCat a a') :
    SpecializedFunctor (LocallySmallCat / a) (LocallySmallCat / a').
    assert (H : focus (fun objC C a a' m => ObjectOf (@SliceCategoryOverInducedFunctor objC C a a' m))) by constructor.
    simpl in *.
    setoid_rewrite @RightIdentity in H.
    (* HERE *)
    assert (H : focus (SliceCategoryOverInducedFunctor LocallySmallCat _ _ m)) by constructor.
    clear H.
    admit.
    Show Proof.
  Defined.
    hnf.

  Section CategoryOver.
    (* Let's do this from scratch so we get better polymorphism *)

    Definition SliceCategoryOverInducedFunctor_ObjectOf a a' (m : Morphism C a a') : C / a -> C / a'
      := fun x => existT (fun αβ : objC * unit => Morphism C (fst αβ) a')
                         (projT1 x)
                         (Compose m (projT2 x)) :
                    CommaSpecializedCategory_ObjectT (IdentityFunctor C) (SliceSpecializedCategory_Functor C a').
    Let CosliceCategoryOverInducedFunctor_ObjectOf a a' (m : Morphism C a' a) : a \ C -> a' \ C
      := fun x => existT (fun αβ : unit * objC => Morphism C a' (snd αβ))
                         (projT1 x)
                         (Compose (projT2 x) m) :
                    CommaSpecializedCategory_ObjectT (SliceSpecializedCategory_Functor C a') (IdentityFunctor C).

    Definition SliceCategoryOverInducedFunctor_MorphismOf a a' (m : Morphism C a a') s d (m0 : Morphism (C / a) s d) :
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

    Definition SliceCategoryOverInducedFunctor'' a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a').
      refine (Build_SpecializedFunctor (C / a) (C / a')
                                       (@SliceCategoryOverInducedFunctor_ObjectOf _ _ m)
                                       (@SliceCategoryOverInducedFunctor_MorphismOf _ _ m)
                                       _
                                       _
             );
      subst_body; simpl;
      abstract (unfold SliceCategoryOverInducedFunctor_ObjectOf, SliceCategoryOverInducedFunctor_MorphismOf in *; anihilate).
    Defined.
    Definition CosliceCategoryOverInducedFunctor'' a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C).
      refine (Build_SpecializedFunctor (a \ C) (a' \ C)
                                       (@CosliceCategoryOverInducedFunctor_ObjectOf _ _ m)
                                       (@CosliceCategoryOverInducedFunctor_MorphismOf _ _ m)
                                       _
                                       _
             );
      subst_body; simpl;
      abstract anihilate.
    Defined.

    Definition SliceCategoryOverInducedFunctor''' a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a').
      simpl_definition_by_tac_and_exact (@SliceCategoryOverInducedFunctor'' _ _ m) ltac:(subst_body; eta_red).
    Defined.
    Definition CosliceCategoryOverInducedFunctor''' a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C).
      simpl_definition_by_tac_and_exact (@CosliceCategoryOverInducedFunctor'' _ _ m) ltac:(subst_body; eta_red).
    Defined.

    Definition SliceCategoryOverInducedFunctor a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a')
      := Eval cbv beta iota zeta delta [SliceCategoryOverInducedFunctor'''] in @SliceCategoryOverInducedFunctor''' _ _ m.
    Definition CosliceCategoryOverInducedFunctor a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C)
      := Eval cbv beta iota zeta delta [CosliceCategoryOverInducedFunctor'''] in @CosliceCategoryOverInducedFunctor''' _ _ m.
    Print SliceCategoryOverInducedFunctor.
  End CategoryOver.
End SliceCategoryInducedFunctor.
Set Printing Universes.
Check SliceCategoryOverInducedFunctor_ObjectOf LocallySmallC
Check ((fun (objC : Type (* Top.235278 *)) (C : SpecializedCategory objC)
  (a a' : C) (m : Morphism C a a') => fun x : C / a =>
             existT (fun αβ : objC * unit => Morphism C (fst αβ) a')
               (projT1 x) (Compose m (projT2 x))) _ LocallySmallCat).
Check (SliceCategoryOverInducedFunctor LocallySmallCat).

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
  Context `(C : SmallSpecializedCategory objC).
  Context `(D : SmallSpecializedCategory objD).

  Set Printing Universes.

  (* Variable F : SpecializedFunctor C D. (* [SpecializedFunctor], not [Functor], because otherwise Sort-poylmorphism won't work *)

  Section Slice.
    Local Notation "F ↓ A" := (SliceSpecializedCategory A F).


    Check SpecializedFunctor 1 ((LocallySmallCat / C) ^ D). *)

  Definition SliceCategoryLocallySmallCatOverInducedFunctor_ObjectOf (a a' : LocallySmallCat) (m : SpecializedFunctor a a') :
    LocallySmallCat / a -> LocallySmallCat / a'
    := fun x =>
         existT (fun αβ : LocallySmallCategory * unit => SpecializedFunctor (fst αβ) a')
                (projT1 x)
                (ComposeFunctors m (projT2 x)) :
           CommaSpecializedCategory_ObjectT (IdentityFunctor LocallySmallCat) (SliceSpecializedCategory_Functor LocallySmallCat a').

  Definition SliceCategoryLocallySmallCatOverInducedFunctor_MorphismOf (a a' : LocallySmallCat) (m : SpecializedFunctor a a')
             s0 d0 (m0 : Morphism (LocallySmallCat / a) s0 d0) :
    Morphism (LocallySmallCat / a')
             (@SliceCategoryLocallySmallCatOverInducedFunctor_ObjectOf a a' m s0)
             (@SliceCategoryLocallySmallCatOverInducedFunctor_ObjectOf a a' m d0).
    refine (_ : CommaSpecializedCategory_MorphismT _ _).
    exists (projT1 m0).
    simpl.
    abstract (
        pre_anihilate;
        repeat rewrite LeftIdentityFunctor in *;
          (* WTF? *)
          progress match goal with [ H : _ |- _ ] => rewrite LeftIdentityFunctor in H end;
        subst;
        anihilate
      ).
  Defined.

  Definition SliceCategoryLocallySmallCatOverInducedFunctor

    simpl in s.
 CommaSpecializedCategory_Morphism
    LocallySmallCat / a -> LocallySmallCat / a'
    := fun x =>
         existT (fun αβ : LocallySmallCategory * unit => SpecializedFunctor (fst αβ) a')
                (projT1 x)
                (ComposeFunctors m (projT2 x)) :
           CommaSpecializedCategory_ObjectT (IdentityFunctor LocallySmallCat) (SliceSpecializedCategory_Functor LocallySmallCat a').

  Definition SliceCategoryLocallySmallCatOverInducedFunctor (a a' : LocallySmallCat) (m : SpecializedFunctor a a') :
    SpecializedFunctor (LocallySmallCat / a) (LocallySmallCat / a').

    {|
       ObjectOf' := fun
                      x : CommaSpecializedCategory
                            (IdentityFunctor LocallySmallCat)
                            (SliceSpecializedCategory_Functor LocallySmallCat
                               a) =>
                    existT
                      (fun αβ : LocallySmallCategory * unit =>
                       SpecializedFunctor (fst αβ) a')
                      (projT1 x)
                      (ComposeFunctors m
                         (ComposeFunctors (projT2 x)
                            (IdentityFunctor (fst (projT1 x)))));
       MorphismOf' := fun
                        (s0
                         d0 : CommaSpecializedCategory
                                (IdentityFunctor LocallySmallCat)
                                (SliceSpecializedCategory_Functor
                                   LocallySmallCat a))
                        (m0 : CommaSpecializedCategory_Morphism s0 d0) =>
                      {|
                      CommaSpecializedCategory_Morphism_Member := exist
                                                  (fun
                                                  gh :
                                                  SpecializedFunctor
                                                  (fst (projT1 s0))
                                                  (fst (projT1 d0)) * unit =>
                                                  ComposeFunctors
                                                  (IdentityFunctor a')
                                                  (ComposeFunctors m
                                                  (ComposeFunctors
                                                  (projT2 s0)
                                                  (IdentityFunctor
                                                  (fst (projT1 s0))))) =
                                                  ComposeFunctors
                                                  (ComposeFunctors m
                                                  (ComposeFunctors
                                                  (projT2 d0)
                                                  (IdentityFunctor
                                                  (fst (projT1 d0)))))
                                                  (fst gh)) (projT1 m0)
                                                  (CommaCategoryInducedFunctor_MorphismOf_subproof
                                                  (
                                                  IdentityFunctor
                                                  LocallySmallCat,
                                                  SliceSpecializedCategory_Functor
                                                  LocallySmallCat a)
                                                  (
                                                  IdentityFunctor
                                                  LocallySmallCat,
                                                  SliceSpecializedCategory_Functor
                                                  LocallySmallCat a')
                                                  (
                                                  IdentityNaturalTransformation
                                                  (IdentityFunctor
                                                  LocallySmallCat),
                                                  SliceCategoryInducedFunctor_NT
                                                  LocallySmallCat a a' m) s0
                                                  d0 m0) |};
       FCompositionOf' := CommaCategoryInducedFunctor'_subproof
                            (IdentityNaturalTransformation
                               (IdentityFunctor LocallySmallCat),
                            SliceCategoryInducedFunctor_NT LocallySmallCat a
                              a' m);
       FIdentityOf' := CommaCategoryInducedFunctor'_subproof0
                         (IdentityNaturalTransformation
                            (IdentityFunctor LocallySmallCat),
                         SliceCategoryInducedFunctor_NT LocallySmallCat a a'
                           m) |}

  Definition SliceCategoryProjectionFunctor : ((LocallySmallCat / (C : LocallySmallSpecializedCategory _)) ^ D) ^ (OppositeCategory (D ^ C)).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    refine (ComposeFunctors _ ((ExponentialLaw1Functor_Inverse D) * IdentityFunctor (OppositeCategory (D ^ C)))).
    refine (ComposeFunctors _ (SwapFunctor _ _)).
    refine (ComposeFunctors _ (CommaCategoryProjectionFunctor (C : LocallySmallSpecializedCategory _) (1 : LocallySmallSpecializedCategory _) D)).
    pose (SliceCategoryOverInducedFunctor LocallySmallCat).
    hnf in s.
    unfold SliceCategoryMorphismInducedFunctor, SliceCategoryInducedFunctor, CommaCategoryInducedFunctor in s; simpl in s.
    setoid_rewrite RightIdentityFunctor in s.
    compute in s.
    apply SliceCategoryOverInducedFunctor.
    Show Proof.
    admit.
  Defined.
    Show Proof.
    pose @CosliceCategoryMorphismInducedFunctor.
    unfold CosliceCategoryMorphismInducedFunctor in *.
    unfold CosliceCategoryInducedFunctor in *.
    Implicit Arguments SliceCategoryInducedFunctor_NT [].
    Implicit Arguments CommaCategoryInducedFunctor [].
    Check LocallySmallCat.
    Print LocallySmallCategory.
    pose @CommaCategoryProjectionFunctor.
    Check (@CommaCategoryInducedFunctor unit TerminalCategory).
    pose @SliceCategoryOverInducedFunctor.
    unfold SliceCategoryOverInducedFunctor in s1.
    unfold SliceCategoryMorphismInducedFunctor in s1.
    unfold SliceCategoryInducedFunctor in s1.
    pose CommaCategoryInducedFunctor.
    Check (CommaCategoryInducedFunctor _ LocallySmallCat).
    specialize (s1 _ LocallySmallCat).
    Check (fun (objB : Type (* Top.50759 *)) (B : SpecializedCategory objB)
         (objC : Type (* Top.50765 *)) (C : SpecializedCategory objC)
         (s
          d : ((OppositeCategory (C ^ TerminalCategory)%functor) * (C ^ LocallySmallCat)%functor)%category) =>
       Morphism ((OppositeCategory (C ^ TerminalCategory)%functor) * (C ^ LocallySmallCat)%functor) s d ->
       SpecializedFunctor (CommaSpecializedCategory (fst s) (snd s))
         (CommaSpecializedCategory (fst d) (snd d))). _ LocallySmallCat.
    Check @CommaCategoryProjectionFunctor TerminalCategory LocallySmallCat.


    Check fun (A B : LocallySmallCategory) => (fun (C : Category) => SpecializedFunctor ((OppositeCategory (LocallySmallCat ^ A)%functor) * (LocallySmallCat ^ B)%functor)
         (LocallySmallCat /
                          (A * B:LocallySmallSpecializedCategory (LSObject A * LSObject B)))) LocallySmallCat.
    Check SpecializedFunctor (CommaSpecializedCategory (fst s) (snd s))
         (CommaSpecializedCategory (fst d) (snd d))
    unfold CommaCategoryInducedFunctor in s0.
    Check @CommaCategoryInducedFunctor unit TerminalCategory LocallySmallCategory.
    Check (fun (objC : Type (* Top.84951 *)) (C : SpecializedCategory objC)
         (objD : Type (* Top.84957 *)) (D : SpecializedCategory objD)
         (F : SpecializedFunctor C D) (a a' : D) (m : Morphism D a' a) =>
       CommaCategoryInducedFunctor unit TerminalCategory objC C objD D
         (SliceSpecializedCategory_Functor D a, F)
         (SliceSpecializedCategory_Functor D a', F)
         (SliceCategoryInducedFunctor_NT objD D a' a m,
         IdentityNaturalTransformation F)) LocallySmallCategory.
    Check @SliceCategoryOverInducedFunctor.
    Check @CosliceCategoryMorphismInducedFunctor LocallySmallCategory.
    Check ( _ _ ).
    Check (SliceCategoryOverInducedFunctor LocallySmallCat ((C : LocallySmallSpecializedCategory _) * 1 : LocallySmallSpecializedCategory _) (C : LocallySmallSpecializedCategory _)).
    admit.
    Check (OppositeCategory (D ^ C)).
    Check SpecializedCategory (SpecializedFunctor C D).
  Defined.
  Print SpecializedCategory.
    exact (ProductLaw1Functor _).
  Defined.
End Slice.


    Definition CosliceCategoryProjectionFunctor : ((LocallySmallCat / C) ^ (OppositeCategory D)) ^ (D ^ C).
      refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
      refine (ComposeFunctors _ ((ExponentialLaw1Functor_Inverse D) * IdentityFunctor (OppositeCategory (D ^ C)))).
      refine (ComposeFunctors _ (ComposeFunctors (@CommaCategoryProjectionFunctor C (1 : LocallySmallSpecializedCategory _) D) (SwapFunctor _ _))).
      apply SliceCategoryOverInducedFunctor.
      apply ProductLaw1Functor.
    Defined.

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
