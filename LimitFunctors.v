Require Import FunctionalExtensionality.
Require Export Limits.
Require Import Common DefinitionSimplification NaturalTransformation FunctorCategory Adjoint Hom SetCategory Duals FunctorProduct.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope category_scope.

Section HasLimits.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Definition HasLimits' := forall F : SpecializedFunctor D C, exists _ : Limit F, True.
  Definition HasLimits := forall F : SpecializedFunctor D C, Limit F.

  Definition HasColimits' := forall F : SpecializedFunctor D C, exists _ : Colimit F, True.
  Definition HasColimits := forall F : SpecializedFunctor D C, Colimit F.
End HasLimits.

Section LimitFunctors.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

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
                     | [ m : _, t : _ |- _ ] => unique_pose (NTComposeT m t)
                   end;
            specialized_assumption idtac.

  (* TODO: Perhaps there is a better way to define this, or a more automated way to define this. *)
  Definition LimitFunctor_morphism_of' (F G : C ^ D) (m : (C ^ D).(Morphism) F G) : C.(Morphism) (LimitOf F) (LimitOf G).
    subst_body.
    simpl in *.
    generalize (HL G) (HL F).
    define_limit_morphism'.
  Defined.

  Definition ColimitFunctor_morphism_of' (F G : C ^ D) (m : (C ^ D).(Morphism) F G) : C.(Morphism) (ColimitOf F) (ColimitOf G).
    subst_body.
    simpl in *.
    generalize (HC G) (HC F).
    define_limit_morphism'.
  Defined.

  Definition LimitFunctor_morphism_of'' (F G : C ^ D) (m : (C ^ D).(Morphism) F G) : C.(Morphism) (LimitOf F) (LimitOf G).
    simpl_definition_by_tac_and_exact (LimitFunctor_morphism_of' m) ltac:( unfold LimitFunctor_morphism_of', LimitOf in * ).
  Defined.

  Definition ColimitFunctor_morphism_of'' (F G : C ^ D) (m : (C ^ D).(Morphism) F G) : C.(Morphism) (ColimitOf F) (ColimitOf G).
    simpl_definition_by_tac_and_exact (ColimitFunctor_morphism_of' m) ltac:( unfold ColimitFunctor_morphism_of', ColimitOf in * ).
  Defined.

  (* Then we clean up a bit with reduction. *)
  Let LimitFunctor_morphism_of := Eval cbv beta iota zeta delta [LimitFunctor_morphism_of''] in LimitFunctor_morphism_of''.
  Let ColimitFunctor_morphism_of := Eval cbv beta iota zeta delta [ColimitFunctor_morphism_of''] in ColimitFunctor_morphism_of''.

  (* XXX TODO: Automate this better *)
  Definition LimitFunctor' : SpecializedFunctor (C ^ D) C.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          LimitOf
          LimitFunctor_morphism_of
          _
          _
        )
    end;
    subst_body; simpl;
      abstract (
        present_spnt;
        simpl; intros; autorewrite with category;
          repeat match goal with
                   | [ |- context[HL ?o] ] => generalize (HL o); intro
                 end;
          clear HL HC;
            unfold Limit, LimitObject, Colimit, ColimitObject in *;
              match goal with
                | [ |- TerminalProperty_Morphism ?l0 ?Y ?f = _ ] =>
                  simpl_do_clear ltac:(fun H => apply H) (proj2 (TerminalProperty l0 Y f))
              end;
              nt_eq;
              try solve [
                autorewrite with category;
                  reflexivity
              ];
              repeat rewrite Associativity;
                match goal with
                  | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
                    eapply (@eq_trans _ _ (Compose a' (Compose _ c)) _);
                      try_associativity ltac:(apply f_equal2; try reflexivity)
                end;
                match goal with
                  | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] =>
                    let H := constr:(TerminalProperty a) in
                      let H' := fresh in
                        pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                          simpl in H'
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

  Definition ColimitFunctor' : SpecializedFunctor (C ^ D) C.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          ColimitOf
          ColimitFunctor_morphism_of
          _
          _
        )
    end;
    abstract (
      subst LimitOf ColimitOf LimitFunctor_morphism_of ColimitFunctor_morphism_of;
        simpl; intros; autorewrite with category;
          repeat match goal with
                   | [ |- context[HC ?o] ] => generalize (HC o); intro
                 end;
          clear HL HC;
            unfold Limit, LimitObject, Colimit, ColimitObject in *;
              match goal with
                | [ |- InitialProperty_Morphism ?l0 ?Y ?f = _ ] =>
                  simpl_do_clear ltac:(fun H => apply H) (proj2 (InitialProperty l0 Y f))
              end;
              nt_eq;
              try solve [
                autorewrite with category;
                  try reflexivity
              ];
              repeat rewrite Associativity;
                intro_universal_properties;
                unfold unique in *;
                  split_and;
                  repeat match goal with
                           | [ H : forall Y f, @?a Y f = @?b Y f |- _ ] =>
                             let H' := fresh in assert (H' := (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (H Y f))); simpl in H'; clear H
                         end;
                  match goal with
                    | [ |- Compose ?a (Compose ?b ?c) = Compose ?a' (Compose ?b' ?c') ] =>
                      eapply (@eq_trans _ _ (Compose a (Compose _ c')) _);
                        symmetry; (* I'm confused why I need this.  But if I don't have it, [rewrite <- AssociativityNoEvar at 2] fails *)
                          [ try_associativity ltac:(apply f_equal2; try reflexivity) |
                            repeat rewrite <- AssociativityNoEvar by noEvar ]
                  end;
                  etransitivity; solve [ t_with t' ]
    ).
(*    transitivity (Compose (unique_m (colimo H) (SPNTComposeT (φ H) m2)) (Compose ((φ G) x) (m1 x)));
      try_associativity ltac:(apply PreComposeMorphisms || apply PostComposeMorphisms; try reflexivity).*)
(*      ).*)
(*    rename s into F0; rename d into G0;  rename d' into H0;
    rename c into F;
      rename c0 into H;
        rename c1 into G.*)
(*    Definition Δ {objC morC objD C D} := @diagonal_functor_object_of objC morC objD C D.
    Definition ΔMor {objC morC objD C D} o1 o2 := @diagonal_functor_morphism_of objC morC objD C D o1 o2.
    Definition colimo := InitialMorphism_Object.
    Definition φ := InitialMorphism_Morphism.
    Definition unique_m {objC morC objD morD} C {a b c d} := @InitialProperty_Morphism objC morC objD C a b c d.

    change (diagonal_functor_morphism_of C D) with (@ΔMor _ _ _ _ C D) in *;
    change (MorphismOf (DiagonalSpecializedFunctor C D)) with (@ΔMor _ _ _ _ C D) in *;
    change (ObjectOf (DiagonalSpecializedFunctor C D)) with (@Δ _ _ _ _ C D) in *;
    change InitialMorphism_Object with colimo in *;
    change InitialMorphism_Morphism with φ in *;
    change @InitialProperty_Morphism with @unique_m in *.*)
  Defined.
End LimitFunctors.

Definition LimitFunctor := Eval cbv beta iota zeta delta [LimitFunctor'(* LimitFunctor_morphism_of*)] in @LimitFunctor'.
Definition ColimitFunctor := Eval cbv beta iota zeta delta [ColimitFunctor'(* ColimitFunctor_morphism_of*)] in @ColimitFunctor'.

Section Adjoint.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Hypothesis HL : HasLimits C D.
  Hypothesis HC : HasColimits C D.

  Let LimitOf (F : C ^ D) := LimitObject (HL F).
  Let ColimitOf (F : C ^ D) := ColimitObject (HC F).

  Definition LimitAdjunction_AComponentsOf (c : C) (F : C ^ D) :
    Morphism TypeCat
    (HomFunctor (C ^ D) ((DiagonalFunctor C D) c, F))
    (HomFunctor C (c, (LimitFunctor HL) F))
    := (fun T => LimitProperty_Morphism (HL F) T).

  Definition LimitAdjunction_AComponentsOf_Inverse (c : C) (F : C ^ D)
    : TypeCat.(Morphism) (HomFunctor C (c, (LimitFunctor HL) F)) (HomFunctor (C ^ D) ((DiagonalFunctor C D) c, F)).
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

  Lemma LimitAdjunction_AIsomorphism' (c : C) (F : C ^ D) :
    IsInverseOf (@LimitAdjunction_AComponentsOf c F) (@LimitAdjunction_AComponentsOf_Inverse c F).
    unfold LimitAdjunction_AComponentsOf, LimitAdjunction_AComponentsOf_Inverse;
      unfold LimitMorphism, LimitProperty_Morphism, LimitObject, Limit in *;
        split; simpl in *;
          repeat (apply functional_extensionality_dep; intro);
            repeat match goal with
                     | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => let H0 := fresh in let H1 := fresh in
                       destruct (TerminalProperty a b c) as [ H0 H1 ]; apply H0 || apply H1; clear H0 H1
                   end;
              nt_eq;
              intro_universal_properties;
              intro_universal_morphisms;
              specialize_all_ways;
              destruct_hypotheses;
              match goal with
                | [ T : _ |- _ ] => apply (f_equal ComponentsOf) in T
              end; fg_equal;
              try specialized_assumption idtac.
  Qed.

  Definition LimitAdjunction_AIsomorphism (c : C) (F : C ^ D) : IsomorphismOf (@LimitAdjunction_AComponentsOf c F).
    exists (LimitAdjunction_AComponentsOf_Inverse c F);
      eapply (@LimitAdjunction_AIsomorphism' _ _).
  Defined.

  Lemma LimitAdjunction_ACommutes (c : C) (F : C ^ D) (c' : C) (F' : C ^ D)
    (m : Morphism C c' c) (m' : Morphism (C ^ D) F F') :
    (Compose (@LimitAdjunction_AComponentsOf c' F')
      (MorphismOf (HomFunctor (C ^ D)) (s := (_, F)) (d := (_, F')) ((DiagonalFunctor C D).(MorphismOf) m, m'))) =
    (Compose
      (MorphismOf (HomFunctor C) (s := (c, _)) (d := (c', _)) (m, (LimitFunctor HL).(MorphismOf) m'))
      (@LimitAdjunction_AComponentsOf c F)).
  Proof.
    Local Opaque FunctorCategory.
    repeat match goal with
             | [ |- context G [MorphismOf (HomFunctor ?C) (s := ?s) (d := ?d) ?m] ] =>
               rewrite_by_context G (@SplitHom _ C s d m)
           end;
    repeat rewrite Associativity;
      unfold fst, snd; (* shaves off 4 seconds! *)
        match goal with
          | [ |- @Compose _ _ ?s ?d ?e ?a (@Compose _ _ ?f ?g ?h ?b ?c) = @Compose _ _ ?s' ?d' ?e' ?a' (@Compose _ _ ?f' ?g' ?h' ?b' ?c') ] =>
            eapply (@eq_trans _ _
              (Compose a' (Compose
                (TerminalProperty_Morphism (HL _) _ : Morphism TypeCat _ _)
                c)) _);
            try_associativity ltac:(apply f_equal2; try reflexivity)
        end;
        simpl;
          unfold LimitAdjunction_AComponentsOf, LimitProperty_Morphism, LimitObject;
            apply functional_extensionality_dep; intro;
              repeat match goal with
                       | [ |- appcontext[@NTComposeT ?objD ?D ?objC ?C ?F ?G ?H ?T ?U] ]
                         => change (@NTComposeT objD D objC C F G H T U) with (@Compose _ (C ^ D) F G H T U) in *
                     end;
              repeat match goal with
                       | [ |- context[TerminalProperty_Morphism ?a ?b ?c] ] => let H := constr:(TerminalProperty a b c) in
                         first [ apply H | symmetry; apply H; symmetry ];
                           repeat rewrite FCompositionOf; repeat rewrite <- Associativity;
                             simpl; f_equal
                       | [ |- context[TerminalProperty_Morphism ?a ?b ?c] ] => let H := constr:(TerminalProperty a b c) in
                         first [ simpl_do_clear do_rewrite (proj1 H) | simpl_do_clear do_rewrite (proj2 H) ];
                           repeat rewrite FCompositionOf; repeat rewrite Associativity;
                             simpl; f_equal
                     end;
              try (intros; reflexivity).
    Local Transparent FunctorCategory.
  Qed.

  Definition LimitAdjunction : Adjunction (DiagonalFunctor C D) (LimitFunctor HL).
    match goal with
      | [ |- Adjunction ?F ?G ] =>
        refine (Build_HomAdjunction F G
          LimitAdjunction_AComponentsOf
          LimitAdjunction_AIsomorphism
          LimitAdjunction_ACommutes
        )
    end.
  Defined.


  Definition ColimitAdjunction_AComponentsOf_Inverse (F : C ^ D) (c : C) :
    Morphism TypeCat
    (HomFunctor (C ^ D) (F, (DiagonalFunctor C D) c))
    (HomFunctor C ((ColimitFunctor HC) F, c))
    := (fun T => ColimitProperty_Morphism (HC F) T).

  Definition ColimitAdjunction_AComponentsOf (F : C ^ D) (c : C) :
    Morphism TypeCat
    (HomFunctor C ((ColimitFunctor HC) F, c))
    (HomFunctor (C ^ D) (F, (DiagonalFunctor C D) c)).
    simpl in *; intro f; hnf; simpl.
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?DF ] =>
        eapply (Build_SpecializedNaturalTransformation F DF
          (fun d => Compose f (ColimitMorphism (HC F) d))
          _
        )
    end.
    Grab Existential Variables.
    abstract (
      simpl in *; intros; rewrite LeftIdentity;
        try_associativity ltac:(apply f_equal2; try reflexivity);
        match goal with
          | [ |- Compose _ _ = ComponentsOf ?T ?d ] => simpl_do do_rewrite (Commutes T)
        end;
        rewrite LeftIdentity;
          reflexivity
    ).
  Defined.

  Lemma ColimitAdjunction_AIsomorphism' (F : C ^ D) (c : C) :
    IsInverseOf (@ColimitAdjunction_AComponentsOf F c) (@ColimitAdjunction_AComponentsOf_Inverse F c).
    unfold ColimitAdjunction_AComponentsOf, ColimitAdjunction_AComponentsOf_Inverse;
      unfold ColimitMorphism, ColimitProperty_Morphism, ColimitObject, Colimit in *;
        split; simpl in *;
          repeat (apply functional_extensionality_dep; intro);
            repeat match goal with
                     | [ |- appcontext[InitialProperty_Morphism ?a ?b ?c] ] => let H := constr:(InitialProperty a b c) in
                       apply (proj1 H) || apply (proj2 H)
                   end;
            nt_eq;
            intro_universal_properties;
            intro_universal_morphisms;
            specialize_all_ways;
            destruct_hypotheses;
            match goal with
              | [ T : _ |- _ ] => apply (f_equal (@ComponentsOf _ _ _ _ _ _)) in T
            end; fg_equal;
            try specialized_assumption idtac.
  Qed.

  Definition ColimitAdjunction_AIsomorphism (F : C ^ D) (c : C) : IsomorphismOf (@ColimitAdjunction_AComponentsOf F c).
    exists (@ColimitAdjunction_AComponentsOf_Inverse F c);
      eapply (@ColimitAdjunction_AIsomorphism' _ _).
  Defined.

  Lemma ColimitAdjunction_ACommutes_Inverse (F : C ^ D) (c : C) (F' : C ^ D) (c' : C)
    (m' : Morphism (C ^ D) F' F) (m : Morphism C c c') :
    (Compose
      (MorphismOf (HomFunctor C) (s := (_, c)) (d := (_, c')) ((ColimitFunctor HC).(MorphismOf) m', m))
      (@ColimitAdjunction_AComponentsOf_Inverse F c)) =
    (Compose (@ColimitAdjunction_AComponentsOf_Inverse F' c')
      (MorphismOf (HomFunctor (C ^ D)) (s := (F, _)) (d := (F', _)) (m', (DiagonalFunctor C D).(MorphismOf) m))).
  Proof.
    Local Opaque FunctorCategory.
    repeat match goal with
             | [ |- context G [MorphismOf (HomFunctor ?C) (s := ?s) (d := ?d) ?m] ] =>
               rewrite_by_context G (@SplitHom _ C s d m)
           end;
    repeat rewrite Associativity;
      unfold fst, snd; (* shaves off 4 seconds! *)
        match goal with
          | [ |- @Compose _ _ ?s ?d ?e ?a (@Compose _ _ ?f ?g ?h ?b ?c) = @Compose _ _ ?s' ?d' ?e' ?a' (@Compose _ _ ?f' ?g' ?h' ?b' ?c') ] =>
            eapply (@eq_trans _ _
              (Compose a (Compose
                (InitialProperty_Morphism (HC _) _ : Morphism TypeCat _ _)
                c')) _);
            try_associativity ltac:(apply f_equal2; try reflexivity)
        end;
        simpl;
          unfold ColimitAdjunction_AComponentsOf_Inverse, ColimitProperty_Morphism, ColimitObject;
            apply functional_extensionality_dep; intro;
              repeat match goal with
                       | [ |- appcontext[@NTComposeT ?objD ?D ?objC ?C ?F ?G ?H ?T ?U] ]
                         => change (@NTComposeT objD D objC C F G H T U) with (@Compose _ (C ^ D) F G H T U) in *
                     end;
          repeat match goal with
                   | [ |- context[InitialProperty_Morphism ?a ?b ?c] ] => let H := constr:(InitialProperty a b c) in
                     first [ apply H | symmetry; apply H; symmetry ];
                       repeat rewrite FCompositionOf; repeat rewrite Associativity;
                         simpl; f_equal
                   | [ |- context[InitialProperty_Morphism ?a ?b ?c] ] => let H := constr:(InitialProperty a b c) in
                     first [ simpl_do_clear do_rewrite (proj1 H) | simpl_do_clear do_rewrite (proj2 H) ];
                         repeat rewrite FCompositionOf; repeat rewrite <- Associativity;
                           simpl; f_equal
                 end;
          try (intros; present_spcategory; apply f_equal2; trivial).
    Local Transparent FunctorCategory.
  Qed.

  Lemma ColimitAdjunction_ACommutes (F : C ^ D) (c : C) (F' : C ^ D) (c' : C)
    (m' : Morphism (C ^ D) F' F) (m : Morphism C c c'):
    (Compose (@ColimitAdjunction_AComponentsOf F' c')
      (MorphismOf (HomFunctor C) (s := (_, c)) (d := (_, c')) ((ColimitFunctor HC).(MorphismOf) m', m))) =
    (Compose
      (MorphismOf (HomFunctor (C ^ D)) (s := (F, _)) (d := (F', _)) (m', (DiagonalFunctor C D).(MorphismOf) m))
      (@ColimitAdjunction_AComponentsOf F c)).
  Proof.
    Local Opaque FunctorCategory TypeCat HomFunctor.
    pose (@ColimitAdjunction_AComponentsOf_Inverse F c).
    pose (@ColimitAdjunction_AComponentsOf_Inverse F' c').
    pose (@ColimitAdjunction_AIsomorphism' F c).
    pose (@ColimitAdjunction_AIsomorphism' F' c').
    unfold InverseOf in *; destruct_hypotheses.
    present_spcategory.
    pre_compose_to_identity; post_compose_to_identity.
    apply ColimitAdjunction_ACommutes_Inverse.
  Qed.

  Definition ColimitAdjunction : Adjunction (ColimitFunctor HC) (DiagonalFunctor C D).
    match goal with
      | [ |- Adjunction ?F ?G ] =>
        refine (Build_HomAdjunction F G
          ColimitAdjunction_AComponentsOf
          ColimitAdjunction_AIsomorphism
          ColimitAdjunction_ACommutes
        )
    end.
  Defined.
End Adjoint.
