Require Import FunctionalExtensionality.
Require Export Limits.
Require Import Common NaturalTransformation SmallNaturalTransformation FunctorCategory Adjoint AdjointUnit.

Set Implicit Arguments.

Local Notation "C ^ D" := (FunctorCategory D C).

Section HasLimits.
  Variable C : Category.

  Definition FunctorHasLimit' (D : SmallCategory) (F : Functor D C) := exists L, exists _ : Limit F L, True.
  Definition FunctorHasLimit (D : SmallCategory) (F : Functor D C) := { L : C & Limit F L }.

  Definition HasLimits' (D : SmallCategory) := forall F : Functor D C, FunctorHasLimit' F.
  Definition HasLimits (D : SmallCategory) := forall F : Functor D C, FunctorHasLimit F.

  Definition FunctorHasColimit' (D : SmallCategory) (F : Functor D C) := exists c, exists _ : Colimit F c, True.
  Definition FunctorHasColimit (D : SmallCategory) (F : Functor D C) := { c : C & Colimit F c }.

  Definition HasColimits' (D : SmallCategory) := forall F : Functor D C, FunctorHasColimit' F.
  Definition HasColimits (D : SmallCategory) := forall F : Functor D C, FunctorHasColimit F.
End HasLimits.

Section LimitFunctors.
  Variable C : Category.
  Variable D : SmallCategory.

  Hypothesis HL : HasLimits C D.
  Hypothesis HC : HasColimits C D.

  Let LimitOf (F : @Object (C ^ D)) := projT1 (HL F).
  Let ColimitOf (F : @Object (C ^ D)) := projT1 (HC F).

  (* TODO: Perhaps there is a better way to define this, or a more automated way to define this. *)
  (* I wonder if there's a way to simplify the definition that Coq comes up with when I use
     destruct and specialize and generalize *)
  Definition LimitFunctor_morphism_of (F G : @Object (C ^ D)) (m : Morphism (C ^ D) F G) : Morphism C (LimitOf F) (LimitOf G).
(*    unfold LimitOf, HasLimits, FunctorHasLimit in *.
    generalize (HL F); intro limF. generalize (HL G); intro limG.
    destruct limF as [ limF [ t s ] ], limG as [ limG [ t' s' ] ].
    simpl.
    specialize (s limG); specialize (s' limF).
    exact (projT1 (s' (NTComposeT m t))).*)
    exact (projT1 ((projT2 (projT2 (HL G))) (projT1 (HL F)) (SNTComposeT m (projT1 (projT2 (HL F)))))).
  Defined.

  Definition ColimitFunctor_morphism_of (F G : @Object (C ^ D)) (m : Morphism (C ^ D) F G) : Morphism C (ColimitOf F) (ColimitOf G).
(*    unfold ColimitOf, HasColimits, FunctorHasColimit in *. generalize (HC F); intro colimF. generalize (HC G); intro colimG.
    destruct colimF as [ colimF [ t s ] ], colimG as [ colimG [ t' s' ] ].
    simpl.
    specialize (s colimG); specialize (s' colimF).
    exact (projT1 (s (NTComposeT t' m))).*)
    exact (projT1 ((projT2 (projT2 (HC F))) (projT1 (HC G)) (SNTComposeT (projT1 (projT2 (HC G))) m))).
  Defined.

  Hint Unfold ColimitFunctor_morphism_of LimitFunctor_morphism_of.

  Definition LimitFunctor : Functor (C ^ D) C.
    refine {| ObjectOf := LimitOf;
      MorphismOf := LimitFunctor_morphism_of
      |}; abstract (
        unfold LimitFunctor_morphism_of; simpl; intros;
          try rewrite LeftIdentityNaturalTransformation; try rewrite RightIdentityNaturalTransformation;
            match goal with
              | [ |- context[projT1 ?x] ] => unique_pose (projT2 x)
            end;
            simpl in *; destruct_hypotheses;
              auto
      ).
  Defined.

  Definition ColimitFunctor : Functor (C ^ D) C.
    refine {| ObjectOf := ColimitOf;
      MorphismOf := ColimitFunctor_morphism_of
      |}; abstract (
        unfold ColimitFunctor_morphism_of; simpl; intros;
          try rewrite LeftIdentityNaturalTransformation; try rewrite RightIdentityNaturalTransformation;
            match goal with
              | [ |- context[projT1 ?x] ] => unique_pose (projT2 x)
            end;
            simpl in *; destruct_hypotheses;
              auto
      ).
  Defined.
End LimitFunctors.

Section Adjoint.
  Variable C : Category.
  Variable D : SmallCategory.
  Hypothesis HL : HasLimits C D.
  Hypothesis HC : HasColimits C D.

  Definition LimitAdjunction : Adjunction (DiagonalFunctor C D) (LimitFunctor HL).
    refine {| AComponentsOf := (fun (c : C) (F : C ^ D)
      => (fun (T : Hom.HomFunctor (C ^ D) ((DiagonalFunctor C D) c, F))
        => proj1_sig (projT2 (projT2 (HL F)) c T) : Hom.HomFunctor C (c, (LimitFunctor HL) F)
      )) |}; intros; unfold CategoryIsomorphism, HasLimits, FunctorHasLimit, Limit in *; simpl in *;
    try match goal with
          | [ |- { _ : Morphism _ ?c ?L -> SmallNaturalTransformation (diagonal_functor_object_of _ _ ?c) ?F | _ } ] =>
            eexists (fun f : Morphism _ c L =>
              Build_SmallNaturalTransformation (diagonal_functor_object_of C D c) F
              (fun d => Compose (projT1 (projT2 (HL F)) d) f)
              _
            )
        end;
    repeat split; simpl in *; repeat (apply functional_extensionality_dep; intro);
      try snt_eq;
        intro_proj2_sig_from_goal;
        simpl in *; destruct_hypotheses;
          try rewrite_unique;
            intro_fresh_unique;
            t_rev_with t'.
    Grab Existential Variables.
    abstract (
      intros; simpl in *; auto; autorewrite with core; simpl;
        try_associativity ltac:(apply f_equal2; try reflexivity);
        match goal with
          | [ |- SComponentsOf ?T ?d = Compose _ _ ] => simpl_do do_rewrite_rev (SCommutes T)
        end;
        autorewrite with core; reflexivity
    ).
  Defined.

  Definition ColimitAdjunction : Adjunction (ColimitFunctor HC) (DiagonalFunctor C D).
    refine {| AComponentsOf := (fun (F : C ^ D) (c : C)
      => fun f : Hom.HomFunctor C (ColimitFunctor HC F, c)
        => Build_SmallNaturalTransformation F (diagonal_functor_object_of C D c)
        (fun d => Compose f (projT1 (projT2 (HC F)) d))
        _
        : Hom.HomFunctor (C ^ D) (F, DiagonalFunctor C D c)
    ) |}; try (
      intros F c; eexists (fun (T : SmallNaturalTransformation F (DiagonalFunctor C D c))
        => proj1_sig (projT2 (projT2 (HC F)) c T)
      )
    );
    intros; repeat split; simpl in *;
      try snt_eq;
        repeat try_associativity ltac:(apply f_equal2; try reflexivity);
          unfold ColimitFunctor_morphism_of;
            intro_proj2_sig_from_goal;
            intro_projT2_from_goal;
            simpl in *; destruct_hypotheses;
              try rewrite_unique;
                intro_fresh_unique;
                t_rev_with t';
                match goal with
                  | [ H : ?a = ?b |- _ ] => assert (forall x, a x = b x) by (rewrite H || rewrite <- H; reflexivity)
                end;
                simpl in *; t_with t'.
    Grab Existential Variables.
    abstract (
      intros; simpl in *; auto; autorewrite with core; simpl;
        try_associativity ltac:(apply f_equal2; try reflexivity);
        match goal with
          | [ |- Compose _ _ = SComponentsOf ?T ?d ] => simpl_do do_rewrite (SCommutes T)
        end;
        autorewrite with core; reflexivity
    ).
  Defined.
End Adjoint.
