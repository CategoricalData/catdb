Require Import Bool Omega Setoid Program.
Require Export Schema Category.
Require Import Common EquivalenceRelation EquivalenceClass.
Require Import NaturalEquivalence ComputableCategory SNaturalEquivalence ComputableSchemaCategory.

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

  Definition sautrate_unsaturate_roundtrip_category : Category := ComputableCategory
    (fun b => match b with
                | true => C
                | false => saturate (unsaturate C)
              end).

  Definition sautrate_unsaturate_functor_to_morphism : Morphism sautrate_unsaturate_roundtrip_category true false := sautrate_unsaturate_functor_to.

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
             end; simpl in *.

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

    Lemma sautrate_unsaturate_roundtrip_natural_equivalence' : CategoriesNaturallyEquivalent C (saturate (unsaturate C)).
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

    Lemma sautrate_unsaturate_roundtrip' : @CategoryIsomorphism sautrate_unsaturate_roundtrip_category _ _
      (sautrate_unsaturate_functor_to : Morphism sautrate_unsaturate_roundtrip_category true false).
      simpl; unfold CategoryIsomorphism'.
      exists sautrate_unsaturate_functor_from.
      unfold InverseOf; split; simpl; functor_eq; simpl_chooser;
        destruct_hypotheses; unfold equiv, RelationsEquivalent in *; simpl in *; t_with t';
        apply forall__eq; intros; split; intros; replace_InClass; unfold equiv, RelationsEquivalent in *; simpl in *;
          autorewrite with core in *; assumption.
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

  Theorem sautrate_unsaturate_roundtrip_natrual_equivalence : CategoriesNaturallyEquivalent (saturate (unsaturate C)) C.
    destruct chooser_exists as [ chooser H ].
    symmetry. exact (sautrate_unsaturate_roundtrip_natural_equivalence' chooser).
  Qed.


  Theorem sautrate_unsaturate_roundtrip : @CategoryIsomorphism' sautrate_unsaturate_roundtrip_category _ _
    (sautrate_unsaturate_functor_to : Morphism sautrate_unsaturate_roundtrip_category true false).
    destruct chooser_exists as [ chooser H ].
    apply CategoryIsomorphism2Isomorphism'. exact (sautrate_unsaturate_roundtrip' chooser).
  Qed.
End CategorySchemaCategory_RoundTrip.

Section SchemaCategorySchema_RoundTrip.
  Variable C : Schema.

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
  Hint Rewrite compose_morphism_path_distr.

  Definition unsaturate_saturate_translation_to_PathOf s d (e : C.(Edge) s d) : path (unsaturate (saturate C)) s d :=
    AddEdge NoEdges (@classOf (path' _ s d) _ (Reflexive _ _ _) (Symmetric _ _ _) (Transitive _ _ _) (AddEdge NoEdges e)).

  Hint Unfold unsaturate_saturate_translation_to_PathOf.

  Lemma unsaturate_saturate_translation_to_PathOf_InClass s d (p : path C s d) :
    InClass (compose_morphism_path (saturate C) (transferPath _ unsaturate_saturate_translation_to_PathOf p)) p.
    induction p; simpl; repeat esplit; try reflexivity; t_with t'; try apply AddEdge_mor; try reflexivity; assumption.
  Qed.

  Hint Rewrite concatenate_p_addedge.
  Hint Resolve unsaturate_saturate_translation_to_PathOf_InClass.

  Ltac unsaturate_saturate_translation_to_PathOf_InClass' :=
    unfold path in *;
    match goal with
      | [ H : InClass ?C _, p : path' _ _ _ |- _ ] =>
        assert (InClass C p) by (apply unsaturate_saturate_translation_to_PathOf_InClass);
          clear_InClass; unfold equiv in *;
            try match goal with
                  | [ H : InClass C _, H' : context[C] |- _ ] => fail 1
                  | [ H : InClass C _ |- context[C] ] => fail 1
                  | [ H : InClass C _ |- _ ] => clear H
                  | _ => idtac
                end
      | [ p : path' _ _ _ |- InClass ?C _ ] =>
        assert (InClass C p) by (apply unsaturate_saturate_translation_to_PathOf_InClass);
          clear_InClass; unfold equiv in *
    end.

  Ltac unsaturate_saturate_translation_to_PathOf_InClass := repeat unsaturate_saturate_translation_to_PathOf_InClass'.

  Lemma unsaturate_saturate_translation_to_PathOf_equivalent s d (p : path C s d) :
    PathsEquivalent _ _ _ (transferPath _ unsaturate_saturate_translation_to_PathOf p)
    (AddEdge NoEdges (@classOf (path' _ s d) _ (Reflexive _ _ _) (Symmetric _ _ _) (Transitive _ _ _) p)).
    induction p; unfold RelationsEquivalent, unsaturate_saturate_translation_to_PathOf in *; simpl;
    apply forall__eq; intros; split; intros; simpl in *; destruct_hypotheses; replace_noedges; repeat esplit; try reflexivity;
      eauto; autorewrite with core in *;
        try solve [ eauto || symmetry; eauto || etransitivity; eauto; try (symmetry; eauto) ];
          repeat match goal with
                   | [ H : context[@eq] |- _ ] => clear H
                 end.
    unsaturate_saturate_translation_to_PathOf_InClass.
    replace_paths_equivalent'.
  Qed.

  Definition unsautrate_saturate_translation_to : Translation C (unsaturate (saturate C)).
    refine {| VertexOf := (fun x : C => x : (unsaturate (saturate C)));
      PathOf := unsaturate_saturate_translation_to_PathOf (* (fun s d e => AddEdge NoEdges (@classOf (path' _ s d) _ (Reflexive _ _ _) (Symmetric _ _ _) (Transitive _ _ _) (AddEdge NoEdges e))) *)
    |};
    abstract (
      t_with t'; unfold RelationsEquivalent, unsaturate_saturate_translation_to_PathOf in *; apply forall__eq; t_with t';
        unsaturate_saturate_translation_to_PathOf_InClass;
        solve [ assumption || symmetry; assumption || etransitivity; eauto; symmetry; eauto ]
    ).
  Defined.

  Lemma unsaturate_saturate_cmp_eq_eqv s d (p1 p2 : path (unsaturate (saturate C)) s d) :
    (compose_morphism_path (saturate C) p1 = compose_morphism_path (saturate C) p2) =
    (PathsEquivalent _ _ _ p1 p2).
    simpl; unfold RelationsEquivalent in *; trivial.
  Qed.

  Definition unsautrate_saturate_roundtrip_category : Category := ComputableSchemaCategory
    (fun b => match b with
                | true => C
                | false => unsaturate (saturate C)
              end).

  Section chooser.
    Variable chooser : forall s d, forall cls : EquivalenceClass ((PathsEquivalent C) s d),
      { p : _ | InClass cls p }.

    Ltac simpl_chooser :=
      repeat match goal with
               | [ |- context[proj1_sig (chooser ?m)] ] =>
                 let hyp := constr:(proj2_sig (chooser m)) in
                   let T := type of hyp in
                     match goal with
                       | [ H : T |- _ ] => fail 1
                       | _ => let H := fresh in assert (H := hyp); try rewrite <- H in *
                     end
             end; simpl in *; trivial.

    Ltac simpl_chooser_more := simpl_chooser;
      repeat match goal with
               | [ H : context[proj1_sig (chooser ?m)] |- _ ] =>
                 let hyp := constr:(proj2_sig (chooser m)) in
                   let T := type of hyp in
                     match goal with
                       | [ H : T |- _ ] => fail 1
                       | _ => let H := fresh in assert (H := hyp); try rewrite <- H in *
                     end
             end; simpl in *; trivial.

    Definition unsaturate_saturate_translation_from_PathOf s d (e : Edge (unsaturate (saturate C)) s d) : path C s d :=
      proj1_sig (chooser e).

    Hint Unfold unsaturate_saturate_translation_from_PathOf.

    Lemma unsaturate_saturate_translation_from_PathOf_eqv s d (p : path (unsaturate (saturate C)) s d) :
      PathsEquivalent _ _ _
      (transferPath _ (fun s d (e : Edge (unsaturate (saturate C)) s d) => proj1_sig (chooser e)) p)
      (proj1_sig (chooser (compose_morphism_path (saturate C) p))).
      induction p; simpl in *; simpl_chooser_more.
      destruct_hypotheses; clear_InClass.
      unfold equiv in *.
      repeat_subst_mor_of_type @path'.
      match goal with
        | [ H : _ |- _ ] => rewrite H; apply concatenate_mor; eauto
      end.
    Qed.

    Hint Rewrite concatenate_p_addedge.
    Hint Resolve unsaturate_saturate_translation_from_PathOf_eqv.

    Definition unsautrate_saturate_translation_from : Translation (unsaturate (saturate C)) C.
      refine {| VertexOf := (fun x : unsaturate (saturate C) => x : C);
        PathOf := (fun s d e => proj1_sig (chooser e))
      |};
      abstract (
        repeat simpl in *; intros; unfold RelationsEquivalent in *;
          do 2 (etransitivity; try apply unsaturate_saturate_translation_from_PathOf_eqv; symmetry);
            match goal with
              | [ H : _ |- _ ] => rewrite H; reflexivity
            end
      ).
    Defined.

    Hint Rewrite apply2_to_classOf unsaturate_saturate_translation_to_PathOf_equivalent.

    (* TODO: Simplify this proof. *)
    Lemma unsautrate_saturate_roundtrip' : @CategoryIsomorphism unsautrate_saturate_roundtrip_category _ _
      (@classOf _ _ (@TranslationsEquivalent_refl _ _) (@TranslationsEquivalent_sym _ _) (@TranslationsEquivalent_trans _ _)
        unsautrate_saturate_translation_to : Morphism unsautrate_saturate_roundtrip_category true false).
      eexists (@classOf _ _ (@TranslationsEquivalent_refl _ _) (@TranslationsEquivalent_sym _ _) (@TranslationsEquivalent_trans _ _)
        unsautrate_saturate_translation_from).
      split; translation_eq; rewrite apply2_to_classOf;
        apply forall__eq; intros; split; intros;
          clear_InClass; unfold equiv in *;
            repeat_subst_mor_of_type @Translation;
            repeat esplit; intros; eauto; try reflexivity; simpl in *; autorewrite with core in *;
              unfold RelationsEquivalent in *;
                unfold TransferPath, unsautrate_saturate_translation_to, unsautrate_saturate_translation_from in *;
                  simpl; try rewrite unsaturate_saturate_translation_to_PathOf_equivalent;
                    autorewrite with core in *;
                      simpl_chooser; auto; try solve [ symmetry; auto ];
                        simpl;
                          autorewrite with core;
                            apply forall__eq; intros; split; intros; simpl in *; destruct_hypotheses; auto;
                              repeat (clear_InClass; eexists; eauto; try reflexivity); clear_InClass;
                                unfold equiv in *; auto;
                                  repeat_subst_mor_of_type @path'; autorewrite with core; reflexivity.
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

    Lemma unsautrate_saturate_translation_from_unique chooser chooser'
      : TranslationsEquivalent (unsautrate_saturate_translation_from chooser) (unsautrate_saturate_translation_from chooser').
      unfold unsautrate_saturate_translation_from.
      translation_eqv; simpl_chooser chooser; simpl_chooser chooser'; destruct_hypotheses;
      clear_InClass; unfold equiv, RelationsEquivalent in *; t_with t'.
    Qed.

    (* XXX TODO: Automate this better. *)
    Lemma unsautrate_saturate_translation_from_exists' :
      forall s d, forall cls : EquivalenceClass ((PathsEquivalent C) s d),
        exists choice : { p : _ | InClass cls p }, True.
      intros s d cls.
      destruct (ClassInhabited cls) as [ x H ].
      simpl.
      eexists (exist _ x H).
      trivial.
    Qed.

    Require Import IndefiniteDescription.

    Lemma unsat_sat_chooser_exists : exists _ : (forall s d
      (cls : EquivalenceClass ((PathsEquivalent C) s d)),
      { p : _ | InClass cls p }), True.
      constructor; trivial; intros s d cls.
      apply constructive_indefinite_description.
      destruct (unsautrate_saturate_translation_from_exists' cls) as [ [ p H ] ].
      eexists; eauto.
    Qed.
  End chooser'.

  Theorem unsautrate_saturate_roundtrip : @CategoryIsomorphism' unsautrate_saturate_roundtrip_category _ _
    (@classOf _ _ (@TranslationsEquivalent_refl _ _) (@TranslationsEquivalent_sym _ _) (@TranslationsEquivalent_trans _ _)
      unsautrate_saturate_translation_to : Morphism unsautrate_saturate_roundtrip_category true false).
    destruct unsat_sat_chooser_exists as [ chooser H ].
    apply CategoryIsomorphism2Isomorphism'. exact (unsautrate_saturate_roundtrip' chooser).
  Qed.
End SchemaCategorySchema_RoundTrip.

Section CatSchIsomorphic.
  Section Cat2Sch.
    Variable O : Type.
    Variable Object2Cat : O -> Category.

    Local Coercion Object2Cat : O >-> Category.

    Set Printing Universes.
(*    Definition Cat2Sch := ComputableSchemaCategory (fun o => unsaturate o).*)

  End Cat2Sch.
End CatSchIsomorphic.
