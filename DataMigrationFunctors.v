Require Import FunctionalExtensionality ProofIrrelevance JMeq.
Require Export Adjoint Functor Category.
Require Import Common Notations FunctorCategory NaturalTransformation Hom Duals SetLimits SetColimits LimitFunctors LimitFunctorTheorems InducedLimitFunctors DefinitionSimplification FEqualDep FunctorialComposition ExponentialLaws FunctorProduct NatCategory DiscreteCategoryFunctors ProductLaws CommaCategoryFunctors.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Local Open Scope category_scope.

Local Ltac pre_anihilate :=
  simpl;
  subst_body;
  clear;
  nt_hideProofs;
  unfold NTComposeF, NTComposeT; simpl;
  nt_hideProofs;
  clear; simpl in *.

(* TODO(jgross): Check if [simpl in *] would make this faster. *)
Local Ltac step := clear; subst_body;
                   ((abstract (autorewrite with category; reflexivity))
                      (*|| (abstract apply SliceCategoryInducedFunctor_FIdentityOf)
                      || (abstract apply CosliceCategoryInducedFunctor_FIdentityOf)
                      || (abstract apply SliceCategoryInducedFunctor_FCompositionOf)
                      || (abstract apply CosliceCategoryInducedFunctor_FCompositionOf)*)
                      || apply CommaCategory_Morphism_eq
                      || apply f_equal
                      || (apply f_equal2; try reflexivity; [])
                      || apply sigT_eq (* simpl_eq *)
                      || (progress nt_eq)
                      || (progress functor_eq)
                      || (progress (destruct_head_hnf @CommaCategory_Object;
                                    destruct_head_hnf @CommaCategory_Morphism;
                                    destruct_sig)));
                   simpl; trivial.

Local Ltac anihilate := repeat step.

Local Ltac t :=
  repeat match goal with
           | _ => reflexivity
           | _ => progress (subst_body; trivial)
           | _ => progress (simpl in *; unfold Object in *; repeat intro)
           (* | _ => progress nt_hideProofs *) (* makes things slower, I think; it probably needs a more delicate application *)
           | _ => progress simpl_eq'
           | _ => progress (apply Functor_eq || apply Functor_JMeq)
           | _ => progress (apply NaturalTransformation_eq || apply NaturalTransformation_JMeq)
           | _ => progress apply CommaCategory_Morphism_eq
           | _ => progress (destruct_head_hnf @CommaCategory_Object; destruct_head_hnf @CommaCategory_Morphism)
           | _ => progress destruct_sig
           | _ => progress autorewrite with morphism
           | _ => progress repeat rewrite FIdentityOf
           | [ |- @eq (LaxCosliceCategory_Object _ _) _ _ ] => expand; apply f_equal
           | [ |- @eq (LaxCosliceCategory_Morphism _ _) _ _ ] => expand; apply f_equal
           | [ |- @eq (LaxSliceCategory_Object _ _) _ _ ] => expand; apply f_equal
           | [ |- @eq (LaxSliceCategory_Morphism _ _) _ _ ] => expand; apply f_equal
           | _ => progress (apply functional_extensionality_dep_JMeq; intros)
         end.

Section DataMigrationFunctors.
  Variable C : Category.
  Variable D : Category.
  Variable S : Category.

  Section Δ.
    Definition PullbackAlongFunctor : ((S ^ C) ^ (S ^ D)) ^ (D ^ C)
      := (ExponentialLaw4Functor_Inverse _ _ _) (FunctorialComposition _ _ _).
    Definition PullbackAlong (F : Functor C D) : (S ^ C) ^ (S ^ D)
      := Eval hnf in PullbackAlongFunctor F.
    (*

    Local Arguments ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf / .
    Local Arguments ExponentialLaw4Functor_Inverse_ObjectOf / .
    Local Arguments FunctorialComposition / .
    Local Arguments ExponentialLaw4Functor_Inverse_ObjectOf_MorphismOf / .


    Let PullbackAlongFunctor'' : { F | PullbackAlongFunctor' = F }.
      assert (Hf : focus (exist _ PullbackAlongFunctor' eq_refl)) by constructor.
      subst_body.
      simpl in Hf.

      Implicit Arguments exist [A P].
      unfold IdentityFunctor, IdentityNaturalTransformation, NTComposeF, NTComposeT, ComposeFunctors in Hf.
      simpl in Hf.
    Let PullbackAlong' (F : Functor C D) : { PA : (S ^ C) ^ (S ^ D) | PullbackAlongFunctor' F = PA }.
      pre_abstract_trailing_props.
      functor_simpl_abstract_trailing_props_with_equality.
    Defined.
    Let PullbackAlongFunctor'_MorphismOf' s d m : { T : Morphism _ (proj1_sig (PullbackAlong' s)) (proj1_sig (PullbackAlong' d))
                                                 | T == MorphismOf PullbackAlongFunctor' (s := s) (d := d) m }.
      repeat match goal with
               | [ |- context[proj1_sig ?E] ] => destruct (proj2_sig E)
             end.
      pre_abstract_trailing_props.
      nt_simpl_abstract_trailing_props_with_equality.
    Defined.

    Definition PullbackAlong (F : Functor C D) : (S ^ C) ^ (S ^ D)
      := Eval hnf in proj1_sig (PullbackAlong' F).

    Let PullbackAlongFunctor'' : ((S ^ C) ^ (S ^ D)) ^ (D ^ C).
      hnf.
      match goal with
        | [ |- Functor ?C ?D ] =>
          refine (Build_Functor C D
                                           PullbackAlong
                                           (fun s d m => proj1_sig (@PullbackAlongFunctor'_MorphismOf' s d m))
                                           _
                                           _)
      end.
      intros.
      change PullbackAlong with (fun F => proj1_sig (PullbackAlong' F)); cbv beta.
      unfold PullbackAlongFunctor'_MorphismOf'.
      simpl.
      match goal with
        | [ |- context[proj1_sig ?E] ] => let H := fresh in let H' := fresh in set (H' := E) in *; set (H := proj2_sig H'); destruct H; simpl
      end.

      repeat m
      exact (FCompositionOf PullbackAlongFunctor').
      let f := fresh in pose PullbackAlongFunctor' as f; destruct f.
      assumption.
      destruct PullbackAlongFunctor'.

      refine (

    Let PullbackAlongFunctor'_MorphismOf'' s d (m : Morphism (D ^ C) s d) : Morphism _ (PullbackAlong s) (PullbackAlong d)
      := Eval cbv beta iota zeta delta [PullbackAlongFunctor'_MorphismOf' proj1_sig proj2_sig PullbackAlong'] in proj1_sig (@PullbackAlongFunctor'_MorphismOf' s d m).
    Print PullbackAlongFunctor'_MorphismOf''.

    Definition PullbackAlongFunctor'_MorphismOf'' s d (m : Morphism (D ^ C) s d) : Morphism _ (PullbackAlong s) (PullbackAlong d)
    Print PullbackAlongFunctor'_MorphismOf''.

                                                 | T == MorphismOf PullbackAlongFunctor' (s := s) (d := d) m }.

    Let
    Print PullbackAlong''.

      pre_abstract_trailing_props.
      functor_simpl_abstract_trailing_props_with_equality.
    Defined.
    Let Definition
    Goal True.
    pose (fun F => proj1_sig (PullbackAlong' F)) as f.
    unfold PullbackAlong' in f.
    hnf in f.
    simpl in f.
    simpl in f.
    pose (fun s d m => proj1_sig (@PullbackAlongFunctor'_MorphismOf' s d m)) as g.
    unfold PullbackAlongFunctor'_MorphismOf' in g.
    hnf in g.
    simpl in g.
    simpl in g.
    Eval simpl in PullbackAlong'.
    Let PullbackAlongFunctor'_MorphismOf s d m : { T : Morphism _ (proj1_sig (PullbackAlong' s)) (proj1_sig (PullbackAlong' d))
                                                 | T == MorphismOf PullbackAlongFunctor' (s := s) (d := d) m }.
      assert (Hf : focus (proj1_sig (@PullbackAlongFunctor'_MorphismOf' s d m))) by constructor.
      unfold PullbackAlongFunctor'_MorphismOf' in Hf.
      simpl in Hf.
      destruct_match_in_hyp Hf.
      simpl in Hf.
      destruct (projT2 (PullbackAlong' s)).
      destruct (projT2 (PullbackAlong' d)).



(* HERE *)
      match type of Hf with
        | focus ?E => (exists E)
      end.

      subst_body.

      pose
      unfold PullbackAlongFunctor'_MorphismOf in f.
      simpl in f.
      let f' := (eval hnf in f) in
      match f' with
        | appcontext[match ?E with _ => _ end] => let x := fresh in set (x := E) in *; destruct x
      end.
      simpl in f.
      revert f; clear.

      set (x := projT2 (PullbackAlong' s)) in *.
      destruct x.
      set (x := projT2 (PullbackAlong' d)) in *.
      destruct x.
      simpl.
      destruct (projT2 (PullbackAlong' s)).
      revert f; subst_body; intro f.
      hnf in f.
      simpl in f.
      set (H := (PullbackAlong'_subproof1 (PullbackAlong'_subproof d)
                 (PullbackAlong'_subproof0 d))) in *.
      simpl in *.
      hnf.
      intro f.
      destruct H.
      match type of H with
        | ?a = ?b => set (A := a) in *; set (B := b) in *
      end.
      destruct H.

      destruct (projT2 (PullbackAlong' s)).
      hnf in f.
      revert f; subst_body; clear; intro f.
      let f' := (eval hnf in f) in
      match f' with
        | appcontext[match ?E with _ => _ end] => destruct E
      end.
      Transparent JMeq_rect_r.
      Print JMeq_rect_r.
      unfold JMeq_rect_r.

      revert f; subst_body; clear; intro f.
      subst PullbackAlongFunctor'_MorphismOf.
      re

      simpl in *.
      simpl.
      unfold Morphism.
      change
      unfold Morphism, FunctorCategory at 1.
      functor_simpl_abstract_trailing_props_with_equality.
    Defined.
    Definition PullbackAlong (F : Functor C D) : Functor (S ^ D) (S ^ C)
      := Eval hnf in PullbackAlong' F.
    Print PullbackAlong.
      := ComposeFunctors (FunctorialComposition C D S)
                         (ComposeFunctors ((IdentityFunctor (S ^ D)) * (FunctorFromDiscrete (D ^ C) (fun _ : Object 1 => F)))
                                          (ProductLaw1Functor_Inverse _)).



*)
  End Δ.
  Local Arguments PullbackAlongFunctor / .
  Eval simpl in PullbackAlongFunctor.

  Section Π.
    Local Notation "A ↓ F" := (CosliceCategory A F).
    (*Local Notation "C / c" := (@SliceCategoryOver _ _ C c).*)

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

    Section pre_functorial.
      Variable F : Functor C D.

      (* Define [ɣ ○ (π^F d)] *)
      Definition RightPushforwardAlong_pre_pre_Functor (g : S ^ C) (d : D) : Functor (d ↓ F) S.
        refine (ComposeFunctors (ComposeFunctors g (projT2 (CosliceCategoryProjectionFunctor C D F d))) _).
        unfold CosliceCategory, SliceCategory_Functor, Object; simpl.
        refine (CommaCategoryInducedFunctor (s := (_, F)) (d := (_, F)) (_, IdentityNaturalTransformation F)).
        simpl.
        match goal with
          | [ |- NaturalTransformation ?F ?G ] =>
            refine (Build_NaturalTransformation F G
                                                           (fun _ => Identity _)
                                                           _)
        end;
          simpl; abstract (intros; reflexivity).
      Defined.

      (*Variable HasLimits : forall g d, Limit (RightPushforwardAlong_pre_Functor g d).*)
      (* Variable HasLimits : forall d (F' : Functor (d ↓ F) S), Limit F'.*)

      Let Index2Cat d := d ↓ F.

      Local Notation "'CAT' ⇑ D" := (@LaxCosliceCategory _ _ Index2Cat _ D).

      (*Let HasLimits' (C0 : CAT ⇑ S) : Limit (projT2 C0)
        := HasLimits (projT2 C0). *)

      Let RightPushforwardAlong_pre_curried_ObjectOf_pre (g : S ^ C) (d : D) : CAT ⇑ S
        := existT _ (tt, _) (RightPushforwardAlong_pre_pre_Functor g d) : LaxCosliceCategory_ObjectT Index2Cat S.

      Let RightPushforwardAlong_pre_curried_ObjectOf (gd : (S ^ C) * D) : CAT ⇑ S
        := RightPushforwardAlong_pre_curried_ObjectOf_pre (fst gd) (snd gd).

      Let RightPushforwardAlong_pre_curried_MorphismOf_pre g d g' d' (m : Morphism (S ^ C) g g') (m' : Morphism D d d') :
        Morphism (CAT ⇑ S) (RightPushforwardAlong_pre_curried_ObjectOf_pre g d) (RightPushforwardAlong_pre_curried_ObjectOf_pre g' d').
        constructor.
        exists (tt, CosliceCategoryMorphismInducedFunctor F _ _ m').
        subst_body; simpl in *;
        unfold RightPushforwardAlong_pre_pre_Functor;
        simpl;
        unfold Object, Morphism, GeneralizeFunctor.
        match goal with
          | [ |- NaturalTransformation ?F ?G ] =>
            let F' := eval hnf in F in let G' := eval hnf in G in change (NaturalTransformation F' G')
        end.
        exists (fun c : d' ↓ F => m (snd (projT1 c)) : Morphism S _ _).
        simpl;
          abstract (
              intros; rewrite Commutes; reflexivity
            ).
      Defined.

      Definition RightPushforwardAlong_pre_curried_MorphismOf gd g'd' (m : Morphism ((S ^ C) * D) gd g'd') :
        Morphism (CAT ⇑ S) (RightPushforwardAlong_pre_curried_ObjectOf gd) (RightPushforwardAlong_pre_curried_ObjectOf g'd')
        := @RightPushforwardAlong_pre_curried_MorphismOf_pre (fst gd) (snd gd) (fst g'd') (snd g'd') (fst m) (snd m).

      Lemma RightPushforwardAlong_pre_curried_FCompositionOf (s d d' : Functor C S * LSObject D)
            (m1 : Morphism ((S ^ C)%functor * D) s d)
            (m2 : Morphism ((S ^ C)%functor * D) d d') :
        RightPushforwardAlong_pre_curried_MorphismOf (Compose m2 m1) =
        Compose (RightPushforwardAlong_pre_curried_MorphismOf m2)
                (RightPushforwardAlong_pre_curried_MorphismOf m1).
      Proof.
        unfold RightPushforwardAlong_pre_curried_MorphismOf, RightPushforwardAlong_pre_curried_ObjectOf.
      (*(* for speed *)
      Admitted. *)
        Time pre_anihilate.
        Time anihilate.
      Qed.

      Lemma RightPushforwardAlong_pre_curried_FIdentityOf (o : Functor C S * LSObject D) :
        RightPushforwardAlong_pre_curried_MorphismOf (Identity o) =
        Identity (RightPushforwardAlong_pre_curried_ObjectOf o).
      Proof.
        unfold RightPushforwardAlong_pre_curried_MorphismOf, RightPushforwardAlong_pre_curried_ObjectOf.
      (*(* for speed *)
      Admitted. *)
        Time pre_anihilate.
        Time anihilate.
      Qed.

      Definition RightPushforwardAlong_pre_curried : Functor ((S ^ C) * D) (CAT ⇑ S).
        match goal with
          | [ |- Functor ?F ?G ] =>
            exact (Build_Functor F G
                                            RightPushforwardAlong_pre_curried_ObjectOf
                                            RightPushforwardAlong_pre_curried_MorphismOf
                                            RightPushforwardAlong_pre_curried_FCompositionOf
                                            RightPushforwardAlong_pre_curried_FIdentityOf
                  )
        end.
      Defined.
    End pre_functorial.

    Section functorial.
      Let Index2Cat (dF : D * (D ^ C)) := (fst dF) ↓ (snd dF).

      Local Notation "'CAT' ⇑ D" := (@LaxCosliceCategory _ _ Index2Cat _ D).

      Let RightPushforwardAlongFunctor_pre_curried_ObjectOf (dgF : D * ((S ^ C) * (OppositeCategory (D ^ C)))) : CAT ⇑ S
        := let d := fst dgF in
           let g := fst (snd dgF) in
           let F := snd (snd dgF) in
           existT _ (tt, (d, F)) (projT2 (RightPushforwardAlong_pre_curried F (g, d))) : LaxCosliceCategory_ObjectT Index2Cat S.

      Definition RightPushforwardAlongFunctor_pre_curried_MorphismOf dgF d'g'F' (m : Morphism (D * ((S ^ C) * (OppositeCategory (D ^ C)))) dgF d'g'F') :
        Morphism (CAT ⇑ S)
                 (RightPushforwardAlongFunctor_pre_curried_ObjectOf dgF)
                 (RightPushforwardAlongFunctor_pre_curried_ObjectOf d'g'F').
        constructor.
        let d := constr:(fst dgF) in
        let g := constr:(fst (snd dgF)) in
        let F := constr:(snd (snd dgF)) in
        let d' := constr:(fst d'g'F') in
        let g' := constr:(fst (snd d'g'F')) in
        let F' := constr:(snd (snd d'g'F')) in
        let md := constr:(fst m) in
        let mg := constr:(fst (snd m)) in
        let mF := constr:(snd (snd m)) in
        exists (tt, CosliceCategoryInducedFunctor d' d md mF);
          exists (fun c : CommaCategory_Object (SliceCategory_Functor D d') F'
                  => mg (snd (projT1 c)));
          simpl; subst_body;
          abstract (
              intros;
              destruct_head @CommaCategory_Object;
              destruct_head @CommaCategory_Morphism;
              destruct_sig;
              destruct_head_hnf @prod;
              simpl in *;
                apply Commutes
            ).
      Defined.

      Definition RightPushforwardAlongFunctor_pre_curried : Functor (D * ((S ^ C) * (OppositeCategory (D ^ C)))) (CAT ⇑ S).
        match goal with
          | [ |- Functor ?C ?D ] =>
            refine (Build_Functor C D
                                             RightPushforwardAlongFunctor_pre_curried_ObjectOf
                                             RightPushforwardAlongFunctor_pre_curried_MorphismOf
                                             _
                                             _)
        end.
        Time abstract t.
        Time abstract t.
      Defined.
    End functorial.

    Section applied.
      Variable HasLimits : forall (F : Functor C D) d (F' : Functor (d ↓ F) S), Limit F'.

      Let Index2Cat (dF : D * (D ^ C)) := (fst dF) ↓ (snd dF).

      Local Notation "'CAT' ⇑ D" := (@LaxCosliceCategory _ _ Index2Cat _ D).

      Let HasLimits' (C0 : CAT ⇑ S) : Limit (projT2 C0)
        := HasLimits (projT2 C0).

      Definition RightPushforwardAlongFunctor_curried : Functor (D * ((S ^ C) * (OppositeCategory (D ^ C)))) S
        := ComposeFunctors (InducedLimitFunctor HasLimits') RightPushforwardAlongFunctor_pre_curried.

      Definition RightPushforwardAlongFunctor : ((S ^ D) ^ (S ^ C)) ^ (OppositeCategory (D ^ C))
        := (ExponentialLaw4Functor_Inverse _ _ _) ((ExponentialLaw4Functor_Inverse _ _ _) RightPushforwardAlongFunctor_curried).


      (*Definition RightPushforwardAlong_ObjectOf (x : S ^ C) (F : (OppositeCategory (D ^ C))) : S ^ D
        := ComposeFunctors RightPushforwardAlongFunctor_curried (ComposeFunctors (IdentityFunctor _ * FunctorFrom1 _ (x, F)) (ProductLaw1Functor_Inverse _)).
      Definition RightPushforwardAlong_MorphismOf s0 d0 (m0 : Morphism (S ^ C) s0 d0) s1 d1 (m1 : Morphism (OppositeCategory (D ^ C)) s1 d1) :
        Morphism (S ^ D) (RightPushforwardAlong_ObjectOf s0 s1) (RightPushforwardAlong_ObjectOf d0 d1).
        hnf.
        assert (forall x, Morphism _ ((RightPushforwardAlong_ObjectOf s0 s1) x) ((RightPushforwardAlong_ObjectOf d0 d1) x)).
        intro.
        Print ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf.
        simpl.
        Print ExponentialLaw4Functor_Inverse.
        Check ExponentialLaw4Functor_Inverse_ObjectOf _. *)

      (*
      Definition RightPushforwardAlong_MorphismOf_ComponentsOf_Pre (s d : S ^ C) (m : NaturalTransformation s d) (c : D) :
        NaturalTransformation
          (ComposeFunctors (RightPushforwardAlong_pre_Functor s c) (IdentityFunctor _))
          (RightPushforwardAlong_pre_Functor d c).
      Proof.
        eapply (NTComposeT (ComposeFunctorsAssociator1 _ _ _) _).
        Grab Existential Variables.
        match goal with
          | [ |- NaturalTransformation ?F ?G ] =>
            refine (Build_NaturalTransformation F G
                                                           (fun x => m (snd (projT1 x)))
                                                           _
                   )
        end;
          abstract (
              repeat (let H := fresh in intro H; destruct H as [ [ [ ] ] ]; simpl in * );
              match goal with
                | [ H : _ |- _ ] => rewrite RightIdentity in H
                | [ H : _ |- _ ] => rewrite LeftIdentity in H
              end;
              subst;
              apply Commutes
            ).
      Defined.

      Definition RightPushforwardAlong_MorphismOf_ComponentsOf (s d : S ^ C) (m : NaturalTransformation s d) (c : D) :
        Morphism S ((RightPushforwardAlong_ObjectOf s) c) ((RightPushforwardAlong_ObjectOf d) c).
      Proof.
        simpl; subst_body; simpl.
        apply (InducedLimitMap (G := IdentityFunctor _)).
        exact (@RightPushforwardAlong_MorphismOf_ComponentsOf_Pre s d m c).
      Defined.

      Definition RightPushforwardAlong_MorphismOf (s d : S ^ C) (m : NaturalTransformation s d) :
        NaturalTransformation (RightPushforwardAlong_ObjectOf s) (RightPushforwardAlong_ObjectOf d).
      Proof.
        exists (@RightPushforwardAlong_MorphismOf_ComponentsOf s d m).
        rename d into t.
        intros d d' g.
        unfold RightPushforwardAlong_MorphismOf_ComponentsOf, RightPushforwardAlong_ObjectOf, RightPushforwardAlong_ObjectOf_MorphismOf; simpl.
        pose InducedLimitFunctor_FCompositionOf as H;
          unfold InducedLimitFunctor_MorphismOf in *.
        rewrite <- H.
        simpl in *.

       *)
      End applied.
  End Π.

  Section Σ.
    Local Notation "F ↓ A" := (SliceCategory A F).
    (*Local Notation "C / c" := (@SliceCategoryOver _ _ C c).*)

    (** Quoting David Spivak in "Functorial Data Migration":
       Definition 2.1.3. Let [F : C -> D] be a morphism of schemas and
       [Δ_F : D–Set -> C–Set] be the associated data pull-back functor
       (see Definition 1.3.1). There exists a left adjoint to [Δ_F]
       called the left push-forward functor associated to [F], denoted
       [Σ_F : C–Set -> D–Set], and defined as follows.
       Given an object [ɣ : C -> Set] in [C–Set] define [Σ_F ɣ] on an
       object [d : D] as
       [[
         Σ_F ɣ(d) := colim_{F ↓ d} (ɣ ○ (π_F d))
       ]]
       This is simply the limit of the functor
       [[
         (F ↓ d) --- (π_F d) ---> C --- ɣ ---> Set
       ]]
       Given a map [h : d -> d'] in D one obtains a map
       [Σ_F ɣ(h) : Σ_F ɣ(d) -> Σ_F ɣ(d')] by the universal property of
       colimits.

       Here, we have some [C-set] [ɣ] and we want a [D-set] [Σ_F ɣ].
       To each object in [d] we look at the objects in [C] which are
       sent to the left of [d] (i.e. those equipped with a chosen
       morphism to [d]). Each has been assigned by [ɣ] some set of
       rows; we take the colimit of all these sets and assign that to
       [Σ_F ɣ(d)].
     *)

    Section pre_functorial.
      Variable F : Functor C D.

      Let Index2Cat d := F ↓ d.

      Local Notation "'CAT' ⇓ D" := (@LaxSliceCategory _ _ Index2Cat _ D).

      (* Define [ɣ ○ (π_F d)] *)
      Definition LeftPushforwardAlong_pre_pre_Functor (g : S ^ C) (d : D) : Functor (F ↓ d) S.
        refine (ComposeFunctors (ComposeFunctors g (projT2 (SliceCategoryProjectionFunctor C D F d))) _).
        unfold SliceCategory, SliceCategory_Functor, Object; simpl.
        refine (CommaCategoryInducedFunctor (s := (F, _)) (d := (F, _)) (IdentityNaturalTransformation F, _)).
        simpl.
        match goal with
          | [ |- NaturalTransformation ?F ?G ] =>
            refine (Build_NaturalTransformation F G
                                                           (fun _ => Identity _)
                                                           _)
        end;
          simpl; abstract (intros; reflexivity).
      Defined.

      Let LeftPushforwardAlong_pre_curried_ObjectOf_pre (g : S ^ C) (d : D) : CAT ⇓ S
        := existT _ (_, tt) (LeftPushforwardAlong_pre_pre_Functor g d) : LaxSliceCategory_ObjectT _ Index2Cat S.

      Let LeftPushforwardAlong_pre_curried_ObjectOf (gd : (S ^ C) * D) : CAT ⇓ S
        := LeftPushforwardAlong_pre_curried_ObjectOf_pre (fst gd) (snd gd).

      Let LeftPushforwardAlong_pre_curried_MorphismOf_pre g d g' d' (m : Morphism (S ^ C) g g') (m' : Morphism D d d') :
        Morphism (CAT ⇓ S) (LeftPushforwardAlong_pre_curried_ObjectOf_pre g d) (LeftPushforwardAlong_pre_curried_ObjectOf_pre g' d').
        constructor.
        exists (SliceCategoryMorphismInducedFunctor F _ _ m', tt).
        subst_body; simpl in *;
        unfold LeftPushforwardAlong_pre_pre_Functor;
        simpl;
        unfold Object, Morphism, GeneralizeFunctor.
        match goal with
          | [ |- NaturalTransformation ?F ?G ] =>
            let F' := eval hnf in F in let G' := eval hnf in G in change (NaturalTransformation F' G')
        end.
        exists (fun c : F ↓ d => m (fst (projT1 c)) : Morphism S _ _).
        simpl;
          abstract (
              intros; rewrite Commutes; reflexivity
            ).
      Defined.

      Definition LeftPushforwardAlong_pre_curried_MorphismOf gd g'd' (m : Morphism ((S ^ C) * D) gd g'd') :
        Morphism (CAT ⇓ S) (LeftPushforwardAlong_pre_curried_ObjectOf gd) (LeftPushforwardAlong_pre_curried_ObjectOf g'd')
        := @LeftPushforwardAlong_pre_curried_MorphismOf_pre (fst gd) (snd gd) (fst g'd') (snd g'd') (fst m) (snd m).

      Lemma LeftPushforwardAlong_pre_curried_FCompositionOf (s d d' : Functor C S * LSObject D)
            (m1 : Morphism ((S ^ C)%functor * D) s d)
            (m2 : Morphism ((S ^ C)%functor * D) d d') :
        LeftPushforwardAlong_pre_curried_MorphismOf (Compose m2 m1) =
        Compose (LeftPushforwardAlong_pre_curried_MorphismOf m2)
                (LeftPushforwardAlong_pre_curried_MorphismOf m1).
      Proof.
        unfold LeftPushforwardAlong_pre_curried_MorphismOf, LeftPushforwardAlong_pre_curried_ObjectOf.
      (* (* for speed *)
      Admitted. *)
        Time pre_anihilate.
        Time anihilate.
      Qed.

      Lemma LeftPushforwardAlong_pre_curried_FIdentityOf (o : Functor C S * LSObject D) :
        LeftPushforwardAlong_pre_curried_MorphismOf (Identity o) =
        Identity (LeftPushforwardAlong_pre_curried_ObjectOf o).
      Proof.
        unfold LeftPushforwardAlong_pre_curried_MorphismOf, LeftPushforwardAlong_pre_curried_ObjectOf.
      (* (* for speed *)
      Admitted. *)
        Time pre_anihilate.
        Time anihilate.
      Qed.

      Definition LeftPushforwardAlong_pre_curried : Functor ((S ^ C) * D) (CAT ⇓ S).
        match goal with
          | [ |- Functor ?F ?G ] =>
            exact (Build_Functor F G
                                            LeftPushforwardAlong_pre_curried_ObjectOf
                                            LeftPushforwardAlong_pre_curried_MorphismOf
                                            LeftPushforwardAlong_pre_curried_FCompositionOf
                                            LeftPushforwardAlong_pre_curried_FIdentityOf
                  )
        end.
      Defined.
    End pre_functorial.

    Section functorial.
      Let Index2Cat (dF : D * (D ^ C)) := (snd dF) ↓ (fst dF).

      Local Notation "'CAT' ⇓ D" := (@LaxSliceCategory _ _ Index2Cat _ D).

      Let LeftPushforwardAlongFunctor_pre_curried_ObjectOf (dgF : D * ((S ^ C) * (OppositeCategory (D ^ C)))) : CAT ⇓ S
        := let d := fst dgF in
           let g := fst (snd dgF) in
           let F := snd (snd dgF) in
           existT _ ((d, F), tt) (projT2 (LeftPushforwardAlong_pre_curried F (g, d))) : LaxSliceCategory_ObjectT _ Index2Cat S.

      Definition LeftPushforwardAlongFunctor_pre_curried_MorphismOf dgF d'g'F' (m : Morphism (D * ((S ^ C) * (OppositeCategory (D ^ C)))) dgF d'g'F') :
        Morphism (CAT ⇓ S)
                 (LeftPushforwardAlongFunctor_pre_curried_ObjectOf dgF)
                 (LeftPushforwardAlongFunctor_pre_curried_ObjectOf d'g'F').
        constructor.
        let d := constr:(fst dgF) in
        let g := constr:(fst (snd dgF)) in
        let F := constr:(snd (snd dgF)) in
        let d' := constr:(fst d'g'F') in
        let g' := constr:(fst (snd d'g'F')) in
        let F' := constr:(snd (snd d'g'F')) in
        let md := constr:(fst m) in
        let mg := constr:(fst (snd m)) in
        let mF := constr:(snd (snd m)) in
        exists (SliceCategoryInducedFunctor d d' md mF, tt);
          exists (fun c : CommaCategory_Object F (SliceCategory_Functor D d)
                  => mg (fst (projT1 c)));
          simpl; subst_body;
          abstract (
              intros;
              destruct_head @CommaCategory_Object;
              destruct_head @CommaCategory_Morphism;
              destruct_sig;
              destruct_head_hnf @prod;
              simpl in *;
                apply Commutes
            ).
      Defined.

      Definition LeftPushforwardAlongFunctor_pre_curried : Functor (D * ((S ^ C) * (OppositeCategory (D ^ C)))) (CAT ⇓ S).
        match goal with
          | [ |- Functor ?C ?D ] =>
            refine (Build_Functor C D
                                             LeftPushforwardAlongFunctor_pre_curried_ObjectOf
                                             LeftPushforwardAlongFunctor_pre_curried_MorphismOf
                                             _
                                             _)
        end.
        Time abstract t.
        Time abstract t.
      Defined.
    End functorial.

    Section applied.
      Variable HasColimits : forall (F : Functor C D) d (F' : Functor (F ↓ d) S), Colimit F'.

      Let Index2Cat (dF : D * (D ^ C)) := (snd dF) ↓ (fst dF).

      Local Notation "'CAT' ⇓ D" := (@LaxSliceCategory _ _ Index2Cat _ D).

      Let HasColimits' (C0 : CAT ⇓ S) : Colimit (projT2 C0)
        := HasColimits (projT2 C0).

      Definition LeftPushforwardAlongFunctor_curried : Functor (D * ((S ^ C) * (OppositeCategory (D ^ C)))) S
        := ComposeFunctors (InducedColimitFunctor HasColimits') LeftPushforwardAlongFunctor_pre_curried.

      Definition LeftPushforwardAlongFunctor : ((S ^ D) ^ (S ^ C)) ^ (OppositeCategory (D ^ C))
        := (ExponentialLaw4Functor_Inverse _ _ _) ((ExponentialLaw4Functor_Inverse _ _ _) LeftPushforwardAlongFunctor_curried).
    End applied.
  End Σ.
End DataMigrationFunctors.
