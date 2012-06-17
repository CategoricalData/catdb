Require Import Bool Omega Setoid Program.
Require Export Schema Category.
Require Import Common EquivalenceRelation EquivalenceClass.
Require Import NaturalEquivalence FunctorEquality.

Set Implicit Arguments.

Section Schema_Category_Equivalence.
  Variable C : Category.
  Variable S : Schema.

  Hint Rewrite concatenate_noedges_p concatenate_p_noedges concatenate_addedge.
  Hint Rewrite <- concatenate_prepend_equivalent.
  Hint Rewrite concatenate_associative.

  Hint Extern 1 (@RelationsEquivalent _ _ _ (PathsEquivalent _) _ _ _ _) => apply addedge_equivalent.
  Hint Extern 1 (@RelationsEquivalent _ _ _ (PathsEquivalent _) _ _ _ _) => apply PreCompose.

  Definition path2path' s d (p : path S s d) : path' (Edge S) s d := p.

  Hint Rewrite concatenate_p_noedges concatenate_noedges_p concatenate_associative.

  Ltac replace_noedges' :=
    match goal with
      | [ H : ?rel NoEdges ?x |- _ ] => rewrite <- H in *; clear H
      | [ H : ?rel ?x NoEdges |- _ ] => rewrite H in *; clear H
    end.

  Ltac replace_noedges :=
        repeat replace_noedges'; repeat (rewrite concatenate_p_noedges in * || rewrite concatenate_noedges_p in *).

  Ltac clear_paths :=
    repeat match goal with
             | [ H : path' _ _ _ |- _ ] => subst H || clear H
           end.

  Ltac replace_paths_equivalent' :=
    try replace_noedges;
      try solve [ assumption || symmetry; assumption ];
        clear_paths;
        repeat match goal with
                 | [ H : context[PathsEquivalent] |- _ ] => rewrite <- H in *; clear H
               end; clear_paths; repeat rewrite concatenate_associative in *; try reflexivity || symmetry;
        repeat match goal with
                 | [ H : context[PathsEquivalent] |- _ ] => rewrite H in *; clear H
               end; clear_paths; repeat rewrite concatenate_associative in *; try reflexivity || symmetry.

  (* TODO: Speed this up, automate this better. *)
  Definition saturate : Category.
    refine {| Object := S;
      Morphism := (fun s d => EquivalenceClass (@PathsEquivalent S s d));
      (* foo := 1; *) (* uncommenting this line gives "Anomaly: uncaught exception Not_found. Please report."  Maybe I should report this?  But I haven't figured out a minimal test case. *)
      Identity := (fun _ => classOf NoEdges);
      Compose := (fun s d d' m1 m2 => apply2_to_class (@concatenate S S.(Edge) s d d') (@concatenate_mor S s d d') m2 m1)
    |}; intros; apply forall__eq; intros; split; intros; simpl in *; destruct_hypotheses; clear_paths; clear_InClass;
      try (replace_noedges; assumption || symmetry; assumption);
        repeat (replace_InClass; try eexists; eauto); clear_InClass; replace_paths_equivalent'.
    Grab Existential Variables.
    intros; solve [ reflexivity || (symmetry; assumption) || etransitivity; eauto ].
    intros; solve [ reflexivity || (symmetry; assumption) || etransitivity; eauto ].
    intros; solve [ reflexivity || (symmetry; assumption) || etransitivity; eauto ].
    intros; solve [ reflexivity || (symmetry; assumption) || etransitivity; eauto ].
    intros; solve [ reflexivity || (symmetry; assumption) || etransitivity; eauto ].
    intros; solve [ reflexivity || (symmetry; assumption) || etransitivity; eauto ].
(* abstract (intros; solve [ t | match goal with
                                          | [ p : path _ _ _ |- _ ] => solve [ induction p; t ]
                                        end ]).*)
  Defined.

  Fixpoint compose_morphism_path s d (p : path' C.(Morphism) s d) : Morphism _ s d :=
    match p with
      | NoEdges => Identity s
      | AddEdge _ _ p' E => Compose E (compose_morphism_path p')
    end.

  Hint Rewrite Associativity.

  Lemma compose_morphism_path_alt : forall s d d' (E : Morphism C s d) (p : path' _ d d'),
    compose_morphism_path (prepend p E) = Compose (compose_morphism_path p) E.
    induction p; t; eauto.
  Qed.

  Hint Rewrite compose_morphism_path_alt.

  Definition unsaturate : Schema.
    refine {| Vertex := C;
      Edge := C.(Morphism);
      PathsEquivalent' := (fun s d (p p' : _ s d) => compose_morphism_path p = compose_morphism_path p')
    |}; abstract (t; etransitivity; eauto).
  Defined.
End Schema_Category_Equivalence.

Section CategorySchemaCategory_RoundTrip.
  Variable C : Category.

  Hint Rewrite concatenate_noedges_p concatenate_p_noedges concatenate_addedge.
  Hint Rewrite <- concatenate_prepend_equivalent.
  Hint Rewrite concatenate_associative.

  Hint Extern 1 (@RelationsEquivalent _ _ _ (PathsEquivalent _) _ _ _ _) => apply addedge_equivalent.
  Hint Extern 1 (@RelationsEquivalent _ _ _ (PathsEquivalent _) _ _ _ _) => apply PreCompose.

  Hint Rewrite concatenate_p_noedges concatenate_noedges_p concatenate_associative.

  Ltac replace_noedges' :=
    match goal with
      | [ H : ?rel NoEdges ?x |- _ ] => rewrite <- H in *; clear H
      | [ H : ?rel ?x NoEdges |- _ ] => rewrite H in *; clear H
    end.

  Ltac replace_noedges :=
        repeat replace_noedges'; repeat (rewrite concatenate_p_noedges in * || rewrite concatenate_noedges_p in *).

  Ltac clear_paths :=
    repeat match goal with
             | [ H : path' _ _ _ |- _ ] => subst H || clear H
           end.

  Ltac replace_paths_equivalent' :=
    try replace_noedges;
      try solve [ assumption || symmetry; assumption ];
        clear_paths;
        repeat match goal with
                 | [ H : context[PathsEquivalent] |- _ ] => rewrite <- H in *; clear H
               end; clear_paths; repeat rewrite concatenate_associative in *; try reflexivity || symmetry;
        repeat match goal with
                 | [ H : context[PathsEquivalent] |- _ ] => rewrite H in *; clear H
               end; clear_paths; repeat rewrite concatenate_associative in *; try reflexivity || symmetry.


  Hint Rewrite compose_morphism_path_alt.

  Hint Rewrite LeftIdentity RightIdentity.

  Lemma compose_morphism_path_distr s d d' (x : path' _ s d) (y : path' _ d d') : compose_morphism_path C (concatenate x y) = Compose (compose_morphism_path C y) (compose_morphism_path C x).
    induction x; t_with t'.
  Qed.

  Hint Rewrite compose_morphism_path_distr.

  Definition sautrate_unsaturate_functor_to : Functor C (saturate (unsaturate C)).
    refine {| ObjectOf := (fun x : C => x : (saturate (unsaturate C)));
      MorphismOf := (fun s d m => @classOf (path' _ s d) _ (Reflexive _ _ _) (Symmetric _ _ _) (Transitive _ _ _) (AddEdge NoEdges m))
    |};
    abstract (t_with t'; unfold RelationsEquivalent in *; apply forall__eq; t_with t'; destruct_hypotheses; subst;
      t_with t'; repeat eexists (AddEdge NoEdges _); eauto; t_with t'; t_rev_with t').
  Defined.

  Section chooser.
    Variable chooser : forall s d, forall cls : EquivalenceClass (PathsEquivalent (unsaturate C) s d),
      { m : _ | exists v, m = compose_morphism_path C v /\ InClass cls v }.

    Ltac simpl_chooser :=
      repeat match goal with
               | [ |- context[proj1_sig (chooser ?m)] ] =>
                 let hyp := constr:(proj2_sig (chooser m)) in
                   let T := type of hyp in
                     match goal with
                       | [ H : T |- _ ] => fail 1
                       | _ => let H := fresh in assert (H := hyp)
                     end
             end; simpl in *; t_rev_with t'.

  (* XXX TODO: Automate this better. *)
    Definition sautrate_unsaturate_functor_from : Functor (saturate (unsaturate C)) C.
      refine {| ObjectOf := (fun x : saturate (unsaturate C) => x : C);
        MorphismOf := (fun s d m => proj1_sig (chooser m))
      |};
      abstract (
        repeat simpl in *; intros; unfold RelationsEquivalent in *;
          simpl_chooser; destruct_hypotheses;
          clear_InClass; unfold equiv in *; t_with t'
      ).
    Defined.

    Lemma sautrate_unsaturate_roundtrip' : CategoriesNaturallyEquivalent C (saturate (unsaturate C)).
      unfold CategoriesNaturallyEquivalent.
      exists sautrate_unsaturate_functor_to.
      exists sautrate_unsaturate_functor_from.
      split;
        match goal with
          | [ |- FunctorsNaturallyEquivalent ?F ?G ] => cut (F = G);
            try solve [ let H := fresh in intro H; rewrite H; reflexivity ]
        end; functor_eq; simpl_chooser; destruct_hypotheses; try apply forall__eq; repeat split; intros; simpl in *;
        clear_InClass; unfold equiv, RelationsEquivalent in *; simpl in *; t_with t'; t_rev_with t'.
    Qed.
  End chooser.

  Section chooser'.
    Ltac simpl_chooser chooser :=
      repeat match goal with
               | [ |- context[proj1_sig (chooser ?s ?d ?m)] ] =>
                 let hyp := constr:(proj2_sig (chooser s d m)) in
                   let T := type of hyp in
                     match goal with
                       | [ H : T |- _ ] => fail 1
                       | _ => let H := fresh in assert (H := hyp)
                     end
             end; simpl in *; t_rev_with t'.

    Lemma sautrate_unsaturate_functor_from_unique chooser chooser'
      : sautrate_unsaturate_functor_from chooser = sautrate_unsaturate_functor_from chooser'.
      unfold sautrate_unsaturate_functor_from.
      functor_eq; simpl_chooser chooser; simpl_chooser chooser'; destruct_hypotheses;
      clear_InClass; unfold equiv, RelationsEquivalent in *; t_with t'.
    Qed.

    Lemma sat_unsat_exist_helper'' A B : forall f : A -> B, f = (fun x => f x).
      intros; apply functional_extensionality_dep; intros; reflexivity.
    Qed.

    Lemma sat_unsat_exist_helper' A (f f' : A -> Prop) x x' H H' H'' : f = f' -> exist f x H = exist f x' H' -> exist f x H ~= exist f' x' H''.
      intros H0 H1; etransitivity; eauto.
      subst.
      assert (H' = H'') by (apply proof_irrelevance).
      subst.
      rewrite H1; clear H1.
      reflexivity.
    Qed.

    Lemma sat_unsat_exist_helper A (f : A -> Prop) x x' H H' : exist f x H = exist f x' H' -> exist f x H = exist (fun v => f v) x' H'.
      intros; apply JMeq_eq; eapply sat_unsat_exist_helper'; eauto;
        apply sat_unsat_exist_helper''.
    Qed.

    Lemma sat_unsat_exist_helper2 A (f : A -> Prop) x x' H H' : x = x' -> exist f x H = exist f x' H'.
      intro; repeat subst; f_equal; apply proof_irrelevance.
    Qed.

    (* XXX TODO: Automate this better. *)
    Lemma sautrate_unsaturate_functor_from_exists' :
      forall s d, forall cls : EquivalenceClass (PathsEquivalent (unsaturate C) s d),
        exists! choice : { m : _ | exists v, m = compose_morphism_path C v /\ InClass cls v }, True.
      intros s d cls.
      destruct (ClassInhabited cls) as [ x H ].
      simpl.
      eexists (exist _ (compose_morphism_path C x) (ex_intro _ x (conj (eq_refl _) H))).
      constructor; trivial; intros x' ?.
      destruct x' as [ x' H' ].
      destruct_hypotheses; simpl in *.
      subst x'.
      apply sat_unsat_exist_helper2; replace_InClass; assumption.
    Qed.

    Lemma sautrate_unsaturate_functor_from_chooser_unique
      (chooser chooser' : forall s d
        (cls : EquivalenceClass ((PathsEquivalent (unsaturate C)) s d)),
        { m : _ | exists v, m = compose_morphism_path C v /\ InClass cls v}) :
      chooser = chooser'.
    Proof.
      repeat (apply functional_extensionality_dep; intro).
      destruct chooser, chooser'; destruct_hypotheses.
      apply sat_unsat_exist_helper2; clear_InClass;
        unfold equiv, RelationsEquivalent, PathsEquivalent', unsaturate in *; simpl in *; t_with t'.
    Qed.

    Lemma chooser_helper s d (cls : EquivalenceClass ((PathsEquivalent (unsaturate C)) s d)) : (exists _ :
      forall s' d' (cls' : EquivalenceClass ((PathsEquivalent (unsaturate C)) s' d')),
        s = s' -> d = d' -> cls ~= cls' ->
        { m : _ | exists v, m = compose_morphism_path C v /\ InClass cls' v}, True).
    Proof.
      destruct (ClassInhabited cls) as [ x H ].
      constructor; intros; repeat subst; trivial.
      exists (compose_morphism_path C x); exists x; split; trivial.
    Qed.

    (* [Require Import] here, because otherwise [sat_unsat_exist_helper2]
       depends on [classic], because [classic |- proof_irrelevance] *)
    Require Import ClassicalUniqueChoice.

    Lemma dependent_unique_choice_unique : forall (A : Type) (B : A -> Type) (R : forall x, B x -> Prop),
      (forall x : A, exists! y, R x y) ->
      exists! f : (forall x, B x), forall x, R x (f x).
      intros A B R H.
      destruct (dependent_unique_choice _ _ _ H) as [ f ].
      exists f; split; try assumption.
      intros f' ?.
      apply functional_extensionality_dep; intro x.
      repeat match goal with
               | [ H : forall _ : A, _ |- _ ] => specialize (H x)
             end.
      destruct H as [ y [ H'0 H'1 ] ].
      pose (H'1 (f x)); pose (H'1 (f' x)).
      intuition.
      etransitivity; symmetry; eauto.
    Qed.

    Lemma dependent_unique_choice_unique_true : forall (A : Type) (B : A -> Type),
      (forall x : A, exists! y : B x, True) ->
      exists! f : (forall x, B x), True.
      intros A B H.
      destruct (dependent_unique_choice _ _ _ H) as [ f ].
      exists f; split; trivial.
      intros f' ?.
      apply functional_extensionality_dep; intro x.
      repeat match goal with
               | [ H : forall _ : A, _ |- _ ] => specialize (H x)
             end.
      destruct H as [ y [ H'0 H'1 ] ].
      pose (H'1 (f x)); pose (H'1 (f' x)).
      intuition.
      etransitivity; symmetry; eauto.
    Qed.

    Lemma chooser_exists : exists! _ : (forall s d
      (cls : EquivalenceClass ((PathsEquivalent (unsaturate C)) s d)),
      { m : _ | exists v, m = compose_morphism_path C v /\ InClass cls v }), True.
      repeat match goal with
               | [ |- exists! _ : (forall s : ?T, @?f s), True ] => cut (forall s : T, exists! _ : f s, True);
                 try solve [ let H := fresh in intro H; exact (@dependent_unique_choice_unique_true _ _ H) ];
                   intros
             end.
      apply sautrate_unsaturate_functor_from_exists'.
    Qed.
  End chooser'.

  Theorem sautrate_unsaturate_roundtrip : CategoriesNaturallyEquivalent (saturate (unsaturate C)) C.
    destruct chooser_exists as [ chooser H ].
    symmetry. exact (sautrate_unsaturate_roundtrip' chooser).
  Qed.
End CategorySchemaCategory_RoundTrip.
