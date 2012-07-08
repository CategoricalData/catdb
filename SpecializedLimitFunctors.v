Require Import FunctionalExtensionality Setoid.
Require Export SpecializedLimits.
Require Import Common SpecializedNaturalTransformation SpecializedFunctorCategory SpecializedAdjoint SpecializedAdjointUnit DefinitionSimplification SpecializedHom.

Set Implicit Arguments.

Local Notation "C ^ D" := (SpecializedFunctorCategory D C).

Section HasLimits.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.

  Definition HasLimits' := forall F : SpecializedFunctor D C, exists _ : Limit F, True.
  Definition HasLimits := forall F : SpecializedFunctor D C, Limit F.

  Definition HasColimits' := forall F : SpecializedFunctor D C, exists _ : Colimit F, True.
  Definition HasColimits := forall F : SpecializedFunctor D C, Colimit F.
End HasLimits.

Section LimitSpecializedFunctors.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.

  Hypothesis HL : HasLimits C D.
  Hypothesis HC : HasColimits C D.

  Let LimitOf (F : C ^ D) := LimitObject (HL F).
  Let ColimitOf (F : C ^ D) := ColimitObject (HC F).

  Ltac define_limit_morphism' :=
    clear HL HC;
      intros;
        match goal with
          | [ |- Morphism _ ?a ?b ] => pose a; pose b
        end;
        unfold Colimit, ColimitObject, Limit, LimitObject in *;
          intro_universal_morphisms;
          intro_universal_property_morphisms;
          simpl in *;
            repeat match goal with
                     | [ m : _, t : _ |- _ ] => unique_pose (SPNTComposeT m t)
                   end;
            specialized_assumption idtac.

  (* TODO: Perhaps there is a better way to define this, or a more automated way to define this. *)
  Definition LimitSpecializedFunctor_morphism_of' (F G : C ^ D) (m : (C ^ D).(Morphism) F G) : C.(Morphism) (LimitOf F) (LimitOf G).
    subst LimitOf ColimitOf.
    simpl in *.
    generalize (HL G) (HL F).
    define_limit_morphism'.
  Defined.

  Definition ColimitSpecializedFunctor_morphism_of' (F G : C ^ D) (m : (C ^ D).(Morphism) F G) : C.(Morphism) (ColimitOf F) (ColimitOf G).
    subst LimitOf ColimitOf.
    simpl in *.
    generalize (HC G) (HC F).
    define_limit_morphism'.
  Defined.

  Definition LimitSpecializedFunctor_morphism_of'' (F G : C ^ D) (m : (C ^ D).(Morphism) F G) : C.(Morphism) (LimitOf F) (LimitOf G).
    simpl_definition_by_tac_and_exact (LimitSpecializedFunctor_morphism_of' m) ltac:( unfold LimitSpecializedFunctor_morphism_of', LimitOf in * ).
  Defined.

  Definition ColimitSpecializedFunctor_morphism_of'' (F G : C ^ D) (m : (C ^ D).(Morphism) F G) : C.(Morphism) (ColimitOf F) (ColimitOf G).
    simpl_definition_by_tac_and_exact (ColimitSpecializedFunctor_morphism_of' m) ltac:( unfold ColimitSpecializedFunctor_morphism_of', ColimitOf in * ).
  Defined.

  (* Then we clean up a bit with reduction. *)
  Let LimitSpecializedFunctor_morphism_of := Eval cbv beta iota zeta delta [LimitSpecializedFunctor_morphism_of''] in LimitSpecializedFunctor_morphism_of''.
  Let ColimitSpecializedFunctor_morphism_of := Eval cbv beta iota zeta delta [ColimitSpecializedFunctor_morphism_of''] in ColimitSpecializedFunctor_morphism_of''.

  (* XXX TODO: Automate this better *)
  Definition LimitSpecializedFunctor' : SpecializedFunctor (C ^ D) C.
    Transparent Object Morphism Compose Identity.
    refine {| ObjectOf' := LimitOf;
      MorphismOf' := LimitSpecializedFunctor_morphism_of
    |};
    abstract (
      subst LimitOf ColimitOf LimitSpecializedFunctor_morphism_of ColimitSpecializedFunctor_morphism_of; present_spnt;
        simpl; intros; autorewrite with core;
          repeat match goal with
                   | [ |- context[HL ?o] ] => generalize (HL o); intro
                 end;
          clear HL HC;
            unfold Limit, LimitObject, Colimit, ColimitObject in *;
              match goal with
                | [ |- TerminalProperty_Morphism ?l0 ?Y ?f = _ ] => let H := fresh in pose (proj2 (TerminalProperty l0 Y f)) as H; simpl in H; apply H; clear H
              end;
              try simpl_do_clear do_rewrite (DiagonalSpecializedFunctor C D).(FCompositionOf');
                spnt_eq;
                try solve [
                  autorewrite with core;
                    try reflexivity
                ];
                repeat rewrite Associativity;
                  match goal with
                    | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
                      eapply (@eq_trans _ _ (Compose a' (Compose _ c)) _);
                        try_associativity ltac:(apply f_equal2; try reflexivity)
                  end;
                  intro_universal_properties;
                  unfold unique in *;
                    split_and;
                    repeat match goal with
                             | [ H : forall Y f, @?a Y f = @?b Y f |- _ ] =>
                               let H' := fresh in assert (H' := (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (H Y f))); simpl in H'; clear H
                           end;
                    etransitivity; solve [ t_with t' ]
    ).
 (*
    rename s into F0. rename d into G0.  rename d' into H0.
    rename l into F.
    rename l0 into H.
    rename l1 into G.
    Definition Δ {C D} := diagonal_functor_object_of C D.
    Definition ΔMor {C D} o1 o2 := diagonal_functor_morphism_of C D o1 o2.
    Definition limo := TerminalMorphism_Object.
    Definition φ := TerminalMorphism_Morphism.
    Definition unique_m C a b c d := @TerminalProperty_Morphism C a b c d.
    change (diagonal_functor_morphism_of C D) with (@ΔMor C D) in *;
    change (MorphismOf (DiagonalSpecializedFunctor C D)) with (@ΔMor C D) in *;
    change (ObjectOf (DiagonalSpecializedFunctor C D)) with (@Δ C D) in *;
    change TerminalMorphism_Object with limo in *;
    change TerminalMorphism_Morphism with φ in *;
    change TerminalProperty_Morphism with unique_m in *. *)
  Defined.

  Definition ColimitSpecializedFunctor' : SpecializedFunctor (C ^ D) C.
    refine {| ObjectOf' := ColimitOf;
      MorphismOf' := ColimitSpecializedFunctor_morphism_of
      |};(* abstract ( *)
      subst LimitOf ColimitOf LimitSpecializedFunctor_morphism_of ColimitSpecializedFunctor_morphism_of;
        simpl; intros; autorewrite with core;
          repeat match goal with
                   | [ |- context[HC ?o] ] => generalize (HC o); intro
                 end;
          clear HL HC;
            unfold Limit, LimitObject, Colimit, ColimitObject in *;
              match goal with
                | [ |- InitialProperty_Morphism ?l0 ?Y ?f = _ ] => let H := fresh in pose (proj2 (InitialProperty l0 Y f)) as H; simpl in H; apply H; clear H
              end;
              try simpl_do_clear do_rewrite (DiagonalSpecializedFunctor C D).(FCompositionOf');
                spnt_eq;
                try solve [
                  autorewrite with core;
                    try reflexivity
                ];
                repeat rewrite Associativity.
(*                  intro_universal_properties.*)

    rename s into F0; rename d into G0;  rename d' into H0;
    rename c into F;
      rename c0 into H;
        rename c1 into G.
    intro_universal_properties.
    Definition Δ {objC morC objD morD C D} := @diagonal_functor_object_of objC morC objD morD C D.
    Definition ΔMor {objC morC objD morD C D} o1 o2 := @diagonal_functor_morphism_of objC morC objD morD C D o1 o2.
    Definition colimo := InitialMorphism_Object.
    Definition φ := InitialMorphism_Morphism.
    Definition unique_m {objC morC objD morD} C {a b c d} := @InitialProperty_Morphism objC morC objD morD C a b c d.

    change (diagonal_functor_morphism_of C D) with (@ΔMor _ _ _ _ C D) in *;
    change (MorphismOf (DiagonalSpecializedFunctor C D)) with (@ΔMor _ _ _ _ C D) in *;
    change (ObjectOf (DiagonalSpecializedFunctor C D)) with (@Δ _ _ _ _ C D) in *;
    change InitialMorphism_Object with colimo in *;
    change InitialMorphism_Morphism with φ in *;
    change @InitialProperty_Morphism with @unique_m in *.
                  (* XXX WTF? AssociativityNoEvar seems broken...*)
                  match goal with
                    | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
                      eapply (@eq_trans _ _ (Compose a (Compose _ c')) _)
                  end.
                  Focus 2.
                  repeat rewrite <- AssociativityNoEvar by noEvar.
                  Set Printing All.
                  (* XXX  broken: *)
                  (*rewrite <- AssociativityNoEvar at 2. (* WTF?!  That is _exactly_ what the RHS of the equal sign is.  Down to the very last character, according to vimdiff *)*)
                  Unset Printing All.
                  Unfocus.
                  try_associativity ltac:(apply f_equal2; try reflexivity).
                  unfold unique in *;
                    split_and;
                    repeat match goal with
                             | [ H : forall Y f, @?a Y f = @?b Y f |- _ ] =>
                               let H' := fresh in assert (H' := (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (H Y f))); simpl in H'; clear H
                           end;
                      etransitivity; solve [ t_with t' ].
                  try_associativity ltac:(apply f_equal2; try reflexivity).
                  unfold unique in *;
                    split_and;
                    repeat match goal with
                             | [ H : forall Y f, @?a Y f = @?b Y f |- _ ] =>
                               let H' := fresh in assert (H' := (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (H Y f))); simpl in H'; clear H
                           end;
                      etransitivity; solve [ t_with t' ].
(*    transitivity (Compose (unique_m (colimo H) (SPNTComposeT (φ H) m2)) (Compose ((φ G) x) (m1 x)));
      try_associativity ltac:(apply PreComposeMorphisms || apply PostComposeMorphisms; try reflexivity).*)
(*      ).*)
  Defined.
End LimitSpecializedFunctors.

Definition LimitSpecializedFunctor := Eval cbv beta iota zeta delta [LimitSpecializedFunctor'(* LimitSpecializedFunctor_morphism_of*)] in LimitSpecializedFunctor'.
Definition ColimitSpecializedFunctor := Eval cbv beta iota zeta delta [ColimitSpecializedFunctor'(* ColimitSpecializedFunctor_morphism_of*)] in ColimitSpecializedFunctor'.
(*
Section Adjoint.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Hypothesis HL : HasLimits C D.
  Hypothesis HC : HasColimits C D.

  Let LimitOf (F : C ^ D) := LimitObject (HL F).
  Let ColimitOf (F : C ^ D) := ColimitObject (HC F).


  Let LimitAdjunction_AComponentsOf (c : C) (F : C ^ D)
    : TypeCat.(Morphism) (HomSpecializedFunctor (C ^ D) ((DiagonalSpecializedFunctor C D) c, F)) (HomSpecializedFunctor C (c, (LimitSpecializedFunctor HL) F))
    := (fun T : HomSpecializedFunctor (C ^ D) ((DiagonalSpecializedFunctor C D) c, F)
      => LimitProperty_Morphism (HL F) T : HomSpecializedFunctor C (c, (LimitSpecializedFunctor HL) F)).

  Definition LimitAdjunction_AComponentsOf_Inverse (c : C) (F : C ^ D)
    : TypeCat.(Morphism) (HomSpecializedFunctor C (c, (LimitSpecializedFunctor HL) F)) (HomSpecializedFunctor (C ^ D) ((DiagonalSpecializedFunctor C D) c, F)).
    Transparent Morphism.
    simpl in *; intro f; hnf; simpl.
    match goal with
      | [ |- SpecializedNaturalTransformation ?DF ?F ] =>
        eapply (Build_SpecializedNaturalTransformation DF F
          (fun d => Compose (LimitMorphism (HL F) d) f)
          _
        )
    end.
    Grab Existential Variables.
    abstract (
      simpl in *; intros; rewrite RightIdentity;
        try_associativity ltac:(apply f_equal2; try reflexivity);
        match goal with
          | [ |- ComponentsOf ?T ?d = Compose _ _ ] => simpl_do do_rewrite_rev (Commutes T)
        end;
        rewrite RightIdentity;
          reflexivity
    ).
  Defined.

  Definition LimitAdjunction_AIsomorphism (c : C) (F : C ^ D) : CategoryIsomorphism (@LimitAdjunction_AComponentsOf c F).
    Transparent Morphism Compose Identity.
    unfold CategoryIsomorphism, CategoryIsomorphism'.
    exists (LimitAdjunction_AComponentsOf_Inverse _).
(*    abstract ( *)
      subst LimitAdjunction_AComponentsOf; unfold LimitAdjunction_AComponentsOf_Inverse;
        unfold LimitMorphism, LimitProperty_Morphism, LimitObject, Limit in *;
          split; simpl in *;
            spnt_eq;
            unfold LimitMorphism, LimitProperty_Morphism, LimitObject, Limit in *;
            intro_universal_properties;
            intro_universal_morphisms;
            destruct_hypotheses;
            specialize_all_ways;
            destruct_hypotheses;
            specialize_all_ways;
            destruct_hypotheses;
            repeat match goal with
                     | [ H : _ |- _ ] => apply (f_equal ComponentsOf) in H
                   end; fg_equal;
            destruct_hypotheses.
            t_with t'.
      match goal with
        | [ |- TerminalProperty_Morphism ?M ?a ?b = _ ] => pose (TerminalProperty M a b)
      end.
      destruct_hypotheses.
      specialize_all_ways.
            repeat match goal with
                     | [ H : _ |- _ ] => apply (f_equal ComponentsOf) in H
                   end; fg_equal.
            simpl in *.
            eapply H6.
            rewrite <- H8 at 2

              try rewrite_unique;
                intro_fresh_unique; simpl.
              try rewrite_unique.

            intro_proj2_sig_from_goal; simpl;
              destruct_hypotheses;
              try rewrite_unique;
                intro_fresh_unique; simpl.
      hnf in *.
      unfold TerminalProperty_Morphism.
      intro_proj2_sig_from_goal; simpl;
              destruct_hypotheses;
              try rewrite_unique;
                intro_fresh_unique; simpl.
      unfold Morphism in *; simpl in *.
      unfold CommaSpecializedCategory_Morphism in *.
      repeat match goal with
               | [ H : _ |- _ ] => clear H
             end.
      intro_proj2_sig_from_goal; simpl;
              destruct_hypotheses;
              try rewrite_unique;
                intro_fresh_unique; simpl.

 . simpl.
            intro_proj2_sig_from_goal; simpl.

                t_rev_with t'.
    ).
  Defined.

  Definition LimitAdjunction : Adjunction (DiagonalSpecializedFunctor C D) (LimitSpecializedFunctor HL).
    refine {| AComponentsOf := LimitAdjunction_AComponentsOf;
      AIsomorphism := LimitAdjunction_AIsomorphism
    |}; abstract (
      intros; simpl in *;
        snt_eq;
        unfold LimitAdjunction_AComponentsOf;
          match goal with
            | [ |- proj1_sig ?x = _ ] => let H := fresh in pose (proj1 (proj2_sig x)) as H; simpl in H; apply H || symmetry; apply H
          end
    ).
  Defined.

  Definition ColimitAdjunction : Adjunction (ColimitSpecializedFunctor HC) (DiagonalSpecializedFunctor C D).
    refine {| AComponentsOf := (fun (F : C ^ D) (c : C)
      => fun f : HomSpecializedFunctor C (ColimitSpecializedFunctor HC F, c)
        => Build_SpecializedNaturalTransformation F (diagonal_functor_object_of C D c)
        (fun d => Compose f (projT1 (projT2 (HC F)) d))
        _
        : HomSpecializedFunctor (C ^ D) (F, DiagonalSpecializedFunctor C D c)
    ) |}; try (
      intros F c; eexists (fun (T : SpecializedNaturalTransformation F (DiagonalSpecializedFunctor C D c))
        => proj1_sig (projT2 (projT2 (HC F)) c T)
      )
    );
    intros; repeat split; simpl in *;
      try snt_eq;
        repeat try_associativity ltac:(apply f_equal2; try reflexivity);
          unfold ColimitSpecializedFunctor_morphism_of;
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
*)
