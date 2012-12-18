Require Import FunctionalExtensionality.
Require Export Adjoint Functor Category.
Require Import Common Notations FunctorCategory NaturalTransformation Hom Duals CommaCategoryFunctors SetLimits SetColimits LimitFunctors LimitFunctorTheorems InducedLimitFunctors DefinitionSimplification FEqualDep CommaCategoryFunctorProperties.

Set Implicit Arguments.

Local Open Scope category_scope.

Section DataMigrationFunctors.
  Variables C D : LocallySmallCategory.
  Variables S : Category.

  Variable F : SpecializedFunctor C D.

  Section Δ.
    Let PullbackAlong_ObjectOf : S ^ D -> S ^ C := fun f => ComposeFunctors f F.

    Definition PullbackAlong_MorphismOf s d (m : Morphism (S ^ D) s d) : Morphism (S ^ C) (PullbackAlong_ObjectOf s) (PullbackAlong_ObjectOf d)
      := Build_SpecializedNaturalTransformation (ComposeFunctors s F) (ComposeFunctors d F)
      (fun c => m.(ComponentsOf) (F c))
      (fun _ _ _ => m.(Commutes) _ _ _).

    Definition PullbackAlong : Functor (S ^ D) (S ^ C).
    Proof.
      hnf.
      match goal with
        | [ |- SpecializedFunctor ?C ?D ] =>
          refine (Build_SpecializedFunctor C D
            PullbackAlong_ObjectOf
            PullbackAlong_MorphismOf
            _
            _
          )
      end;
      abstract (intros; simpl in *; nt_eq).
    Defined.
  End Δ.

  Section Π.
    Local Notation "A ↓ F" := (CosliceSpecializedCategory A F).
    (*Local Notation "C / c" := (@SliceSpecializedCategoryOver _ _ C c).*)

    (** Quoting David Spivak in "Functorial Data Migration":
       Definition 2.1.2. Let [F : C -> D] be a morphism of schemas and
       [Δ_F : D–Set -> C–Set] be the associated data pull-back functor
       (see Definition 1.3.1). There exists a right adjoint to [Δ_F]
       called the right push-forward functor associated to [F], denoted
       [Π_F : C–Set -> D–Set], and defined as follows.
       Given an object [ɣ : C -> Set] in [C–Set] define [Π_F ɣ] on an
       object [d : D] as
       [[
         Π_F ɣ(d) := lim_{d ↓ F} (ɣ ○ (π^F d))
       ]]
       This is simply the limit of the functor
       [[
         (d ↓ F) --- (π^F d) ---> C --- ɣ ---> Set
       ]]
       Given a map [h : d -> d'] in D one obtains a map
       [Π_F ɣ(h) : Π_F ɣ(d) -> Π_F ɣ(d')] by the universal property of
       limits.
       The idea is this. We have some [C-set] [ɣ] and we want a [D-set]
       [Π_F ɣ]. To each object in [d] we look at the objects in [C]
       which are sent to the right of [d] (i.e. those equipped with a
       chosen morphism from [d]). Each has been assigned by [ɣ]some
       set of rows; we take the limit of all these sets and assign
       that to [Π_F ɣ(d)].
       *)

    (* Define [ɣ ○ (π^F d)] *)
    Definition RightPushforwardAlong_pre_Functor (g : S ^ C) (d : D) : SpecializedFunctor (d ↓ F) S
      := ComposeFunctors g (projT2 (CosliceCategoryProjectionFunctor C D F d)).

    Variable HasLimits : forall g d, Limit (RightPushforwardAlong_pre_Functor g d).

    Let Index2Cat d := d ↓ F.

    Local Notation "'CAT' ⇑ D" := (@LaxCosliceSpecializedCategory _ _ Index2Cat _ D).

    Let RightPushforwardAlong_ObjectOf_ObjectOf (g : S ^ C) d := LimitObject (HasLimits g d).

    Let RightPushforwardAlong_ObjectOf_MorphismOf_Pre' (g : S ^ C) s d (m : Morphism D s d) :
      {F0 : unit * SpecializedFunctor (d ↓ F) (s ↓ F) &
        SpecializedNaturalTransformation
        (ComposeFunctors (RightPushforwardAlong_pre_Functor g s) (snd F0))
        (RightPushforwardAlong_pre_Functor g d) }.
      exists (tt, fst (proj1_sig (MorphismOf (CosliceCategoryProjectionFunctor C D F) m))).
      unfold RightPushforwardAlong_pre_Functor;
        hnf;
          simpl;
            unfold Object, Morphism, GeneralizeFunctor.
      match goal with
        | [ |- SpecializedNaturalTransformation (ComposeFunctors (ComposeFunctors ?g ?h) ?i) _ ] =>
          eapply (NTComposeT _ (ComposeFunctorsAssociator1 g h i))
      end.
      Grab Existential Variables.
      eapply (NTComposeF (IdentityNaturalTransformation g) _).
      Grab Existential Variables.
      match goal with
        | [ C : _ |- SpecializedNaturalTransformation ?F ?G ] =>
          refine (Build_SpecializedNaturalTransformation F G
            (fun _ => Identity (C := C) _)
            _
          )
      end;
      abstract (
        simpl; present_spnt; intros ? ? m0;
          destruct m0 as [ [ m0 ] ]; simpl;
            rewrite LeftIdentity; rewrite RightIdentity;
              reflexivity
      ).
    Defined.

    Let RightPushforwardAlong_ObjectOf_MorphismOf_Pre'' (g : S ^ C) s d (m : Morphism D s d) :
      Morphism (CAT ⇑ S)
      (existT _ (tt, s) (RightPushforwardAlong_pre_Functor g s) : @LaxCosliceSpecializedCategory_ObjectT _ _ Index2Cat _ _)
      (existT _ (tt, d) (RightPushforwardAlong_pre_Functor g d) : @LaxCosliceSpecializedCategory_ObjectT _ _ Index2Cat _ _).
    Proof.
      hnf.
      match goal with
        | [ |- LaxCosliceSpecializedCategory_Morphism ?a ?b ] =>
          exact (RightPushforwardAlong_ObjectOf_MorphismOf_Pre' g _ _ m : @LaxCosliceSpecializedCategory_MorphismT _ _ _ _ _ a b)
      end.
    Defined.

    Definition RightPushforwardAlong_ObjectOf_MorphismOf_Pre (g : S ^ C) s d (m : Morphism D s d) :
      Morphism (CAT ⇑ S)
      (existT _ (tt, s) (RightPushforwardAlong_pre_Functor g s) : @LaxCosliceSpecializedCategory_ObjectT _ _ Index2Cat _ _)
      (existT _ (tt, d) (RightPushforwardAlong_pre_Functor g d) : @LaxCosliceSpecializedCategory_ObjectT _ _ Index2Cat _ _)
      := Eval cbv beta iota zeta delta [RightPushforwardAlong_ObjectOf_MorphismOf_Pre' RightPushforwardAlong_ObjectOf_MorphismOf_Pre'' RightPushforwardAlong_ObjectOf_ObjectOf Index2Cat] in
        @RightPushforwardAlong_ObjectOf_MorphismOf_Pre'' g s d m.

    (* TODO(jgross): Check if [simpl in *] would make this faster. *)
    Ltac step := clear; subst_body;
                 ((abstract (autorewrite with category; reflexivity))
                    || (abstract apply SliceCategoryInducedFunctor_FIdentityOf)
                    || (abstract apply CosliceCategoryInducedFunctor_FIdentityOf)
                    || (abstract apply SliceCategoryInducedFunctor_FCompositionOf)
                    || (abstract apply CosliceCategoryInducedFunctor_FCompositionOf)
                    || apply CommaSpecializedCategory_Morphism_eq
                    || apply f_equal
                    || apply sigT_eq (* simpl_eq *)
                    || (progress nt_eq)
                    || (progress functor_eq)); simpl; trivial.

    Ltac anihilate := repeat step.

    Local Ltac pre_anihilate :=
      simpl;
      subst_body;
      clear;
      nt_hideProofs;
      unfold NTComposeF, NTComposeT; simpl;
      nt_hideProofs;
      clear; simpl in *; present_spcategory.


    Lemma RightPushforwardAlong_ObjectOf_FCompositionOf_Pre (g : S ^ C) s d d' (m1 : Morphism D s d) (m2 : Morphism D d d') :
      RightPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ (Compose m2 m1) =
      Compose (C := LaxCosliceSpecializedCategory _ _) (RightPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ m2) (RightPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ m1).
    Proof.
      (* For speed temporarily *)
    Admitted. (*
      unfold RightPushforwardAlong_ObjectOf_MorphismOf_Pre.
Time pre_anihilate.
      Time (anihilate). (* 85 s *)
    Qed. *)

    Lemma RightPushforwardAlong_ObjectOf_FIdentityOf_Pre (g : S ^ C) x :
      RightPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ (Identity x) =
      Identity (C := LaxCosliceSpecializedCategory _ _) _.
    Proof.
      unfold RightPushforwardAlong_ObjectOf_MorphismOf_Pre.
      Time pre_anihilate.
      Time anihilate. (* 12 s *)
    Qed.

    Definition RightPushforwardAlong_ObjectOf_MorphismOf (g : S ^ C) s d (m : Morphism D s d) :
      Morphism S (RightPushforwardAlong_ObjectOf_ObjectOf g s) (RightPushforwardAlong_ObjectOf_ObjectOf g d).
      subst RightPushforwardAlong_ObjectOf_ObjectOf RightPushforwardAlong_ObjectOf_MorphismOf_Pre' RightPushforwardAlong_ObjectOf_MorphismOf_Pre''; simpl.
      apply (InducedLimitFunctor_MorphismOf (Index2Cat := Index2Cat) (D := S)
        (s := existT _ (tt, s) (RightPushforwardAlong_pre_Functor g s) : LaxCosliceSpecializedCategory_ObjectT _ _)
        (d := existT _ (tt, d) (RightPushforwardAlong_pre_Functor g d) : LaxCosliceSpecializedCategory_ObjectT _ _)
        (HasLimits g s)
        (HasLimits g d)
      ); simpl in *.
      apply RightPushforwardAlong_ObjectOf_MorphismOf_Pre; assumption.
    Defined.

    Hint Resolve RightPushforwardAlong_ObjectOf_FIdentityOf_Pre RightPushforwardAlong_ObjectOf_FCompositionOf_Pre.

    Definition RightPushforwardAlong_ObjectOf (g : S ^ C) : S ^ D.
      pose proof (InducedLimitFunctor (Index2Cat := Index2Cat) (D := S)).
      hnf.
      unfold Object in X.
      simpl in X.
(*      Set Printing All. *)
      refine (Build_SpecializedFunctor D S
        (@RightPushforwardAlong_ObjectOf_ObjectOf g)
        (@RightPushforwardAlong_ObjectOf_MorphismOf g)
        _
        _
      );
      unfold RightPushforwardAlong_ObjectOf_MorphismOf;
        subst RightPushforwardAlong_ObjectOf_MorphismOf_Pre'' RightPushforwardAlong_ObjectOf_MorphismOf_Pre' RightPushforwardAlong_ObjectOf_ObjectOf;
          simpl;
            present_spcategory;
            abstract (
              present_spcategory;
              first [
                intros s d d' m1 m2;
                  etransitivity;
                  try apply (InducedLimitFunctor_FCompositionOf (Index2Cat := Index2Cat) (D := S)
                    (s := existT _ (tt, s) (RightPushforwardAlong_pre_Functor g s) : LaxCosliceSpecializedCategory_ObjectT _ _)
                    (d := existT _ (tt, d) (RightPushforwardAlong_pre_Functor g d) : LaxCosliceSpecializedCategory_ObjectT _ _)
                    (d' := existT _ (tt, d') (RightPushforwardAlong_pre_Functor g d') : LaxCosliceSpecializedCategory_ObjectT _ _)
                    (HasLimits g s)
                    (HasLimits g d)
                    (HasLimits g d')
                    (RightPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ m1)
                    (RightPushforwardAlong_ObjectOf_MorphismOf_Pre g _ _ m2)
                  ); []
                |
                  intros x;
                    etransitivity;
                    try apply (InducedLimitFunctor_FIdentityOf (Index2Cat := Index2Cat) (D := S)
                      (existT _ (tt, x) (RightPushforwardAlong_pre_Functor g x) : LaxCosliceSpecializedCategory_ObjectT _ _)
                      (HasLimits g x)
                    ); []
              ];
              apply f_equal;
                trivial
            ).
    Defined.

    Definition RightPushforwardAlong_MorphismOf_ComponentsOf_Pre (s d : S ^ C) (m : SpecializedNaturalTransformation s d) (c : D) :
      NaturalTransformation
      (ComposeFunctors (RightPushforwardAlong_pre_Functor s c) (IdentityFunctor _))
      (RightPushforwardAlong_pre_Functor d c).
    Proof.
      eapply (NTComposeT (ComposeFunctorsAssociator1 _ _ _) _).
      Grab Existential Variables.
      match goal with
        | [ |- SpecializedNaturalTransformation ?F ?G ] =>
          refine (Build_SpecializedNaturalTransformation F G
            (fun x => m (snd (projT1 x)))
            _
          )
      end;
      abstract (
        present_spnt; repeat (let H := fresh in intro H; destruct H as [ [ [ ] ] ]; simpl in *);
          match goal with
            | [ H : _ |- _ ] => rewrite RightIdentity in H
          end;
          subst;
            apply Commutes
      ).
    Defined.

    Definition RightPushforwardAlong_MorphismOf_ComponentsOf (s d : S ^ C) (m : SpecializedNaturalTransformation s d) (c : D) :
      Morphism S ((RightPushforwardAlong_ObjectOf s) c) ((RightPushforwardAlong_ObjectOf d) c).
    Proof.
      simpl; subst_body; simpl.
      apply (InducedLimitMap (G := IdentityFunctor _)).
      exact (@RightPushforwardAlong_MorphismOf_ComponentsOf_Pre s d m c).
    Defined.

    Definition RightPushforwardAlong_MorphismOf (s d : S ^ C) (m : SpecializedNaturalTransformation s d) :
      SpecializedNaturalTransformation (RightPushforwardAlong_ObjectOf s) (RightPushforwardAlong_ObjectOf d).
    Proof.
      exists (@RightPushforwardAlong_MorphismOf_ComponentsOf s d m).
      present_spnt.
      unfold RightPushforwardAlong_MorphismOf_ComponentsOf, RightPushforwardAlong_MorphismOf_ComponentsOf_Pre;
        subst_body; clear.
      intros.
      Time pre_anihilate.
      simpl.

      simpl; intros; subst_body; simpl in *.
      hnf in s, d.
      unfold RightPushforwardAlong_MorphismOf_ComponentsOf; simpl in *.
      unfold InducedLimitMap, LimitObject; simpl.
      unfold RightPushforwardAlong_ObjectOf_MorphismOf.
      simpl.
      unfold InducedLimitMap.
      subst_body; simpl.
      unfold RightPushforwardAlong_MorphismOf_ComponentsOf_Pre.
      unfold LimitObject.

      admit.

      (*
      Definition Δ {objC C objD D} := @diagonal_functor_object_of objC C objD D.
      Definition ΔMor {objC C objD D} o1 o2 := @diagonal_functor_morphism_of objC C objD D o1 o2.
      Definition limo F x := TerminalMorphism_Object (HasLimits F x).
      Definition φ := TerminalMorphism_Morphism.
      Definition unique_m := @TerminalProperty_Morphism.
      Print unique_m.
      Arguments unique_m [C D U X] [M] Y f.

      change (diagonal_functor_morphism_of C D) with (@ΔMor _ C _ D) in *;
      change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor _ C _ D) in *;
      change (ObjectOf (DiagonalFunctor C D)) with (@Δ _ C _ D) in *;
      change (TerminalMorphism_Object (HasLimits ?a ?b)) with (limo a b) in *;
      change TerminalMorphism_Morphism with φ in *;
      change @TerminalProperty_Morphism with @unique_m in *.

      unfold RightPushforwardAlong_pre_Functor  in *.


      change (diagonal_functor_morphism_of C D) with (@ΔMor _ C _ D) in *;
        change (MorphismOf (DiagonalFunctor C D)) with (@ΔMor _ C _ D) in *;
          change (ObjectOf (DiagonalFunctor C D)) with (@Δ _ C _ D) in *;
            change TerminalMorphism_Object with limo in *;
              change TerminalMorphism_Morphism with φ in *;
                change TerminalProperty_Morphism with unique_m in *.


*)

(*    transitivity (Compose (unique_m (colimo H) (SPNTComposeT (φ H) m2)) (Compose ((φ G) x) (m1 x)));
      try_associativity ltac:(apply PreComposeMorphisms || apply PostComposeMorphisms; try reflexivity).*)
(*      ).*)
(*    rename s into F0; rename d into G0;  rename d' into H0;
    rename c into F;
      rename c0 into H;
        rename c1 into G.*)
(*

    change (diagonal_functor_morphism_of C D) with (@ΔMor _ _ _ _ C D) in *;
    change (MorphismOf (DiagonalSpecializedFunctor C D)) with (@ΔMor _ _ _ _ C D) in *;
    change (ObjectOf (DiagonalSpecializedFunctor C D)) with (@Δ _ _ _ _ C D) in *;
    change InitialMorphism_Object with colimo in *;
    change InitialMorphism_Morphism with φ in *;
    change @InitialProperty_Morphism with @unique_m in *.*)



(*
      match goal with
        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => pose proof (proj2 (TerminalProperty a b c)); simpl in *
      end (* 9 s *).
      simpl in *.
      pose proof (fun x' => H x'
      erewrite H.

      unfold RightPushforwardAlong_MorphismOf_ComponentsOf.
      unfold InducedLimitMap.
      unfold LimitObject, Limit in *.
      subst RightPushforwardAlong_ObjectOf_MorphismOf; simpl.
      unfold InducedLimitMap, LimitObject; simpl.
      unfold RightPushforwardAlong_MorphismOf_ComponentsOf_Pre; simpl.
      match goal with
        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => pose proof (proj2 (TerminalProperty a b c))
      end (* 9 s *).
      erewrite H.
      match goal with
        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => pose proof (proj2 (TerminalProperty a b c))
      end (* 9 s *).
      erewrite H0.
      Focus 2.
      nt_eq.
      repeat rewrite FIdentityOf;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity.
      clear H H0.


      simpl
      subst_body.
      simpl.
      apply Commutes.
      symmetry.
      simpl.
      unfold RightPushforwardAlong_ObjectOf_MorphismOf at 1.
      unfold InducedLimitMap at 1.
      simpl.
      unfold LimitObject, Limit in *; simpl in *.


      match goal with
        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] =>
          let H := constr:(TerminalProperty a) in
            let H' := fresh in
              pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                simpl in H';
                  unfold Object, Morphism in *;
                    simpl in *
      end.
      subst_body.

      Focus 2.
      simpl in *.
      nt_eq.
      repeat rewrite FIdentityOf;
        repeat rewrite LeftIdentity; repeat rewrite RightIdentity.
      clear H.
      hnf in x.
      destruct x as [ [ [ [] x ] Hx ] ]; simpl in *.
      simpl.

      Time match goal with
        | [ |- appcontext[TerminalMorphism_Morphism ?a] ] =>
          let H := constr:(TerminalProperty a) in
            let H' := fresh in
              pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                simpl in H'
      end (* 7 s *).
      erewrite H.

      etransitivity; try apply Commutes.
      Focus 2.
      symmetry; apply (Commutes m ().
      etransitivity; [ rewrite H0 | ].
      rewrite H0.


      match goal with
        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => pose proof (proj2 (TerminalProperty a b c))
      end (* 9 s *).
      unfold Object, Morphism in *.
      simpl in *.
      unfold Limit, LimitObject in *.
      fg_equal.


      subst_body

      simpl.
      unfold LimitObject.
      unfold InducedLimitMap.
      simpl.
      symmetry.

      match goal with
        | [ |- appcontext[TerminalProperty_Morphism ?a ?b ?c] ] => pose proof (proj2 (TerminalProperty a b c))
      end (* 9 s *).


      Time match goal with
        | [ |- appcontext[TerminalMorphism_Morphism ?a] ] =>
          let H := constr:(TerminalProperty a) in
            let H' := fresh in
              pose proof (fun x Y f => f_equal (fun T => T.(ComponentsOf) x) (proj1 (H Y f))) as H';
                simpl in H'
      end (* 7 s *).

      present_spcategory;
      unfold InducedLimitMap;
        simpl.
              match goal with
                | [ |- TerminalProperty_Morphism ?a ?b ?c = _ ] => apply (proj2 (TerminalProperty a b c))
              end (* 9 s *);
              nt_eq (* 5 s *);
              repeat rewrite FIdentityOf;
                repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                  try reflexivity;
                    repeat rewrite Associativity; (* 27 s for this past block *)
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
                                simpl in H';
                                  unfold Object, Morphism in *;
                                    simpl in *;
                                      rewrite H'
                      end;
                      simpl;
                        repeat rewrite FIdentityOf;
                          repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                            reflexivity (* 8 s *).

      auto.
      simpl.
      apply (NTComposeF
      exists (ComponentsOf' m).
      assert (forall
         c0 : CommaSpecializedCategory_Object
                (SliceSpecializedCategory_Functor D c) F,
       CMorphism S
         (ObjectOf'
            (ComposeFunctors (RightPushforwardAlong_pre_Functor s c)
               (IdentityFunctor (c ↓ F))) c0)
         (ObjectOf' (RightPushforwardAlong_pre_Functor d c) c0)).
      present_spnt.
      intro c0; destruct c0 as [ [ [ [] c0 ] cm ] ]; simpl in *.
      match goal with
        | [ |- SpecializedNaturalTransformation ?F ?G ] =>
          refine (Build_SpecializedNaturalTransformation F G
            (fun _ => Identity _)
            _
          )
      end.












      Set Printing All.
      Check LaxCosliceSpecializedCategory_Object LSObject LSMorphism
                LSUnderlyingCategory S.
      specialize (s0 (fun c => (HasLimits (projT2 c)))).
      specialize

      simpl in *.
      S ^ D.
      refine (Build_SpecializedFunctor D S
        (@RightPushforwardAlong_ObjectOf_ObjectOf g)
        (@RightPushforwardAlong_ObjectOf_MorphismOf g)
        _
        _
      );


     Definition RightPushforwardAlong : Functor (S ^ C) (S ^ D).
       Check @MorphismOf' _ _ (S ^ C) _ _ (S ^ D) _.

       refine {| ObjectOf' := (fun
*)
(*
 & Adjunction PushforwardAlong PullbackAlong }.
      eexists; try reflexivity.
      refine {| AComponentsOf' := (fun A A' => (fun _ : HomFunctor _ (_, _) => _ )) |};
        intros; simpl in *; repeat (apply functional_extensionality_dep; intro; try snt_eq; simpl in *)(*; try reflexivity.
      unfold CategoryIsomorphism; simpl.
      eexists (fun _ => Build_SmallNaturalTransformation _ _ _ _); try reflexivity.
      split; simpl in *; repeat (apply functional_extensionality_dep; intro); try reflexivity.
      snt_eq.
      symmetry.
      symmetry.

      apply SmallNaturalTransformations_Equal
      snt_eq
      destruct x; try reflexivity.

      assert (forall (C : SmallCategory) D (F G : Functor C D) (T : SmallNaturalTransformation F G), T = {| SComponentsOf := SComponentsOf T; SCommutes := SCommutes T |}).
      let T := fresh in intros ? ? ? ? T; destruct T; simpl; reflexivity.
      symmetry.
      rewrite (H .
      apply SmallNaturalTransformations_Equal.

      destruct_type @SmallNaturalTransformation.
      try solve [ destruct_type SmallNaturalTransformation; snt_eq ].
*)
    Defined.

    Definition RightPushforwardAlong : SpecializedFunctor (S ^ C) (S ^ D).
      match goal with
          | [ |- SpecializedFunctor ?C ?D ] =>
            refine (Build_SpecializedFunctor
                      C D
                      RightPushforwardAlong_ObjectOf
                      RightPushforwardAlong_MorphismOf
                      _
                      _
                   )
      end.
      Focus 2.
      present_spcategory.
      intro.
      simpl.
      Time pre_anihilate.
      Time step.
      simpl.
      unfold RightPushforwardAlong_MorphismOf_ComponentsOf.
      apply functional_extensionality_dep.
      intro.
      Time step.
      pose (fun I Index2Object Index2Cat objD D C => @FIdentityOf _ _ _ _ (@InducedLimitFunctor I Index2Object Index2Cat objD D C)) as a.
      unfold InducedLimitFunctor, InducedLimitFunctor_MorphismOf in a; simpl in a.
      unfold RightPushforwardAlong_MorphismOf.
    Admitted.
  End Π.

  Section Σ.
  End Σ.
End DataMigrationFunctors.
