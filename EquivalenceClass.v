Require Import Program Setoid Ensembles.
Require Import Common.

Set Implicit Arguments.

(**
   An equivalence class is a non-empty set of all values
   which are all equivalent to some particular value.
*)

Local Ltac specialize_with tac fin_tac :=
  match goal with
    | [ x : ?T, H : forall _ : ?T, _ |- _ ] => specialize (H x); tac; specialize_with tac fin_tac
    | _ => fin_tac
  end.

Section equiv.
  Variable value : Type.
  Variable equiv' : value -> value -> Prop.

  (* [E] is an equivalence class if it is non-empty and if all it consists
     of all values that are equivalent to some particular value.
     Because the equivalence relation is transitive, we can encode
     this without picking a representative element by requiring that
     for every member of the class, the class consists of exactly the
     values equivalent to that member. *)
  Record EquivalenceClass := {
    UnderlyingClass :> Ensemble value;

    InClass := fun v => In _ UnderlyingClass v;

    ClassInhabited : exists v, InClass v;

    equiv := equiv';

    ElementsEquivalent : forall v v', InClass v -> InClass v' -> equiv v v';
    ContainsEquivalent : forall v v', InClass v -> equiv v v' -> InClass v';

  (* Equivalence relations are reflexive, symmetric, and transitive. *)
    equiv_refl : forall (v : value), equiv v v;
    equiv_sym : forall (v v' : value), equiv v v' -> equiv v' v;
    equiv_trans : forall (v v' v'' : value), equiv v v' -> equiv v' v'' -> equiv v v''
  }.

  Global Add Parametric Relation (E : EquivalenceClass) : _ (equiv E)
    reflexivity proved by (@equiv_refl _)
    symmetry proved by (@equiv_sym _)
    transitivity proved by (@equiv_trans _)
      as equiv_equiv_rel.

  Hypothesis equiv'_refl : forall (v : value), equiv' v v.
  Hypothesis equiv'_sym : forall (v v' : value), equiv' v v' -> equiv' v' v.
  Hypothesis equiv'_trans : forall (v v' v'' : value), equiv' v v' -> equiv' v' v'' -> equiv' v v''.

  Local Add Parametric Relation : _ equiv'
    reflexivity proved by equiv'_refl
    symmetry proved by equiv'_sym
    transitivity proved by equiv'_trans
      as equiv_equiv'_rel.

  (* The equivalence [classOf] a particular [value] is defined by the proposition that
     the elements are equivalent to that [value]. *)
  Definition classOf (v : value) : EquivalenceClass.
    exists (fun v' => equiv' v v');
      repeat esplit; unfold In in *; eauto.
  Defined.

  Lemma classOf_refl : forall v, InClass (classOf v) v.
    compute; intro; reflexivity.
  Qed.

  Global Add Parametric Morphism C : (InClass C)
    with signature (@equiv C) ==> iff
      as InClass_mor.
    intros x y eqv; split; intro inc;
      eapply ContainsEquivalent; eauto; try symmetry; eauto.
  Qed.

  (* Two equivalence classes are the same if they share all values *)
  Definition sameClass (C C' : EquivalenceClass) := forall v, (InClass C v <-> InClass C' v).

  Definition disjointClasses (C C' : EquivalenceClass) := forall v, ~InClass C v \/ ~InClass C' v.

  Definition differentClasses (C C' : EquivalenceClass) := exists v,
    (InClass C v /\ ~InClass C' v) \/
    (~InClass C v /\ InClass C' v).

  Definition notDisjointClasses (C C' : EquivalenceClass) := exists v, InClass C v /\ InClass C' v.

  Definition notDisjointClasses' (C C' : EquivalenceClass) := exists v v', InClass C v /\ InClass C' v' /\ equiv' v v'.

  Lemma sameClass_refl (C : EquivalenceClass) : sameClass C C.
    firstorder.
  Qed.

  Lemma sameClass_sym (C C' : EquivalenceClass) : sameClass C C' -> sameClass C' C.
    firstorder.
  Qed.

  Lemma sameClass_trans (C C' C'' : EquivalenceClass) : sameClass C C' -> sameClass C' C'' -> sameClass C C''.
    firstorder.
  Qed.

  Lemma iff_eq_eq (A B : Prop) : (A <-> B) -> A = B.
    intro H; destruct H.
    pose (a := fun _ : unit => A).
    pose (b := fun _ : unit => B).
    cut (a = b).
    intro H2.
    cut (a tt = b tt); solve [ rewrite H2; reflexivity ] || solve [ compute; trivial ].
    apply Extensionality_Ensembles; compute; tauto.
  Qed.

  Lemma sameClass_eq (C C' : EquivalenceClass) : (sameClass C C') -> (C = C').
    intro H; unfold sameClass, proj1_sig in H.
    destruct C as [ x a b c d e ], C' as [ x' a' b' c' d' e' ].
    subst a a' c c'.
    generalize b b' d d' e e'.
    cut (x = x').
    intro; subst x.
    intros.
    f_equal; try apply proof_irrelevance.
    apply Extensionality_Ensembles.
    constructor; unfold Included; intro; specialize_with intuition trivial.
  Qed.

  Global Add Parametric Morphism : classOf
    with signature equiv' ==> eq
      as classOf_mor.
    intros x y eqv;
      apply sameClass_eq; compute in *; eauto.
  Qed.

  Lemma disjointClasses_differentClasses (C C' : EquivalenceClass) : (disjointClasses C C') -> (differentClasses C C').
    unfold differentClasses, disjointClasses; intro H.
    pose (ClassInhabited C) as H'; destruct H' as [ x H' ].
    exists x; specialize (H x); tauto.
  Qed.

  Lemma notDisjointClasses_sameClass (C C' : EquivalenceClass) : (notDisjointClasses C C') -> (sameClass C C').
    unfold notDisjointClasses, sameClass; intro H; destruct H as [ x [ H0 H1 ] ]; intro v; split; intros;
      match goal with
        | [ H0 : InClass ?C ?x, H1 : InClass ?C ?y |- InClass ?C' ?x ]
          => let H := fresh in
            assert (H : equiv' x y) by (apply (ElementsEquivalent C); assumption);
              rewrite H; assumption
      end.
  Qed.

  Lemma notDisjointClasses_eq (C C' : EquivalenceClass) : (notDisjointClasses C C') -> C = C'.
    intro; apply sameClass_eq; apply notDisjointClasses_sameClass; assumption.
  Qed.

  Lemma forall_equiv__eq (C C' : EquivalenceClass) :
    (forall v v', (InClass C v \/ InClass C' v') -> (InClass C v /\ InClass C' v' <-> equiv' v v')) ->
    C' = C.
    intro H. apply sameClass_eq; unfold sameClass; intro v.
    assert (equiv' v v) by reflexivity; firstorder.
  Qed.

  Lemma forall__eq (C C' : EquivalenceClass) :
    (forall v, InClass C v <-> InClass C' v) ->
    C' = C.
    intro H. apply sameClass_eq; unfold sameClass;
    firstorder.
  Qed.
End equiv.

Implicit Arguments classOf [value equiv' equiv'_refl equiv'_sym equiv'_trans].

Add Parametric Relation value equiv' (E : @EquivalenceClass value equiv') : _ (equiv E)
    reflexivity proved by (equiv_refl _)
    symmetry proved by (equiv_sym _)
    transitivity proved by (equiv_trans _)
      as equiv_rel.

Add Parametric Relation value equiv : _ (@sameClass value equiv)
  reflexivity proved by (@sameClass_refl _ _)
  symmetry proved by (@sameClass_sym _ _)
  transitivity proved by (@sameClass_trans _ _)
    as sameClass_mor.

Ltac create_classOf_InClass :=
  repeat match goal with
           | [ H : InClass (@classOf ?v ?e ?r ?s ?t ?val) _ |- _ ] =>
             let hyp := constr:(@classOf_refl v e r s t val) in
               let T := type of hyp in
                 match goal with
                   | [ H' : T |- _ ] => fail 1 (* the hypothesis already exists *)
                   | _ => let H' := fresh in assert (H' := hyp)
                 end
           | [ |- InClass (@classOf ?v ?e ?r ?s ?t ?val) _ ] =>
             let hyp := constr:(@classOf_refl v e r s t val) in
               let T := type of hyp in
                 match goal with
                   | [ H' : T |- _ ] => fail 1 (* the hypothesis already exists *)
                   | _ => let H' := fresh in assert (H' := hyp)
                 end
         end.

Ltac replace_InClass := create_classOf_InClass;
  repeat match goal with
           | [ H : InClass ?C ?x, H' : InClass ?C ?x' |- _ ] =>
             let equiv := constr:(ElementsEquivalent C _ _ H H') in
               let equivT := type of equiv in
                 match goal with
                   | [ H'' : equivT |- _ ] => fail 1 (* the hypothesis already exists *)
                   | _ => let H'' := fresh in assert (H'' := equiv); try (clear H' || clear H) (* try, in case both appear in the conclusion *)
                 end
           | [ H : InClass ?C ?x |- InClass ?C ?x' ] => apply (ContainsEquivalent C x x' H)
           | [ |- exists v : ?T, @?G v ] =>
             match G with
               | appcontext[InClass ?C ?v] => fail 1 (* [?v] cannot be the same as [v] above, so we fail *)
               | appcontext[InClass ?C _] => (* match an [InClass] expression that references a variable not scoped outside.
                                                This is a kludge to get the correct InClass, which matches the [exists]. *)
                 let v := fresh in let H := fresh in
                   destruct (ClassInhabited C) as [ v H ]; exists v
             end
         end.

Hint Extern 1 (@eq (EquivalenceClass _ _) _ _) => apply forall__eq; replace_InClass.

Ltac clear_InClass' :=
  repeat match goal with
           | [ |- context[InClass] ] => fail 1
           | [ H : InClass _ _ |- _ ] => clear H
         end.

Ltac clear_InClass := replace_InClass; clear_InClass'.

Section apply1.
  Variable value0 : Type.
  Variable equiv0 : value0 -> value0 -> Prop.

  Variable value' : Type.
  Variable equiv' : value' -> value' -> Prop.

  Variable f : value0 -> value'.
  Hypothesis f_mor : forall v v', equiv0 v v' -> equiv' (f v) (f v').
  Variable E0 : EquivalenceClass equiv0.

  Local Add Parametric Relation : _ equiv0
    reflexivity proved by (equiv_refl E0)
    symmetry proved by (equiv_sym E0)
    transitivity proved by (equiv_trans E0)
      as apply_equiv_rel.

  Hypothesis equiv'_refl : forall (v : value'), equiv' v v.
  Hypothesis equiv'_sym : forall (v v' : value'), equiv' v v' -> equiv' v' v.
  Hypothesis equiv'_trans : forall (v v' v'' : value'), equiv' v v' -> equiv' v' v'' -> equiv' v v''.

  Local Add Parametric Relation : _ equiv'
    reflexivity proved by equiv'_refl
    symmetry proved by equiv'_sym
    transitivity proved by equiv'_trans
      as apply_equiv'_rel.

  Hint Resolve f_mor.

  Definition apply_to_class : EquivalenceClass equiv'.
    refine {| UnderlyingClass := (fun v => exists v0, InClass E0 v0 /\ equiv' v (f v0)) |};
      abstract (intros; try solve [ reflexivity || (symmetry; assumption) || (etransitivity; eauto) ];
        solve [ (destruct (ClassInhabited E0) as [ v0 ]; exists (f v0); eexists; split; eauto; apply f_mor; reflexivity) ||
          (unfold In in *; destruct_hypotheses; repeat esplit; clear_InClass; try reflexivity; etransitivity; eauto)
        ]).
  Defined.

  Lemma apply_to_class_f_inj : forall v, InClass E0 v -> InClass apply_to_class (f v).
    compute; firstorder.
  Qed.

  Lemma apply_to_class_f_surj : forall v, InClass apply_to_class v -> exists v', equiv' v (f v') /\ InClass E0 v'.
    compute; firstorder.
  Qed.
End apply1.

Hint Resolve apply_to_class_f_inj.

Implicit Arguments apply_to_class [value0 equiv0
  value' equiv' equiv'_refl equiv'_sym equiv'_trans].

Lemma apply_to_classOf value0 equiv0 equiv0_refl equiv0_sym equiv0_trans value' equiv' equiv'_refl equiv'_sym equiv'_trans f f_mor e0 :
  @apply_to_class value0 equiv0 value' equiv' f f_mor
  (@classOf _ _ equiv0_refl equiv0_sym equiv0_trans e0)
  equiv'_refl equiv'_sym equiv'_trans
  = @classOf _ _ equiv'_refl equiv'_sym equiv'_trans (f e0).
Proof.
  apply forall__eq; intros; split; intros;
    hnf in *; destruct_hypotheses; clear_InClass; eauto.
Qed.

Section apply2.
  Variable value0 : Type.
  Variable equiv0 : value0 -> value0 -> Prop.

  Variable value1 : Type.
  Variable equiv1 : value1 -> value1 -> Prop.

  Variable value' : Type.
  Variable equiv' : value' -> value' -> Prop.

  (* Equivalence relations are reflexive, symmetric, and transitive. *)
  Hypotheses equiv'_refl : forall (v : value'), equiv' v v.
  Hypothesis equiv'_sym : forall (v v' : value'),
    equiv' v v' -> equiv' v' v.
  Hypothesis equiv'_trans : forall (v v' v'' : value'),
    equiv' v v' -> equiv' v' v'' -> equiv' v v''.

  Add Parametric Relation : _ equiv'
    reflexivity proved by equiv'_refl
    symmetry proved by equiv'_sym
    transitivity proved by equiv'_trans
      as apply2_equiv'_rel.

  Variable f : value0 -> value1 -> value'.
  Hypothesis f_mor : forall v0 v0', equiv0 v0 v0' -> forall v1 v1', equiv1 v1 v1' -> equiv' (f v0 v1) (f v0' v1').

  Variable E0 : EquivalenceClass equiv0.
  Variable E1 : EquivalenceClass equiv1.

  Local Add Parametric Relation : _ equiv0
    reflexivity proved by (equiv_refl E0)
    symmetry proved by (equiv_sym E0)
    transitivity proved by (equiv_trans E0)
      as apply2_equiv0_rel.

  Local Add Parametric Relation : _ equiv1
    reflexivity proved by (equiv_refl E1)
    symmetry proved by (equiv_sym E1)
    transitivity proved by (equiv_trans E1)
      as apply2_equiv1_rel.

  Definition apply2_to_class : EquivalenceClass equiv'.
    refine {| UnderlyingClass := (fun v => exists v0 v1, InClass E0 v0 /\ InClass E1 v1 /\ equiv' v (f v0 v1)) |};
      abstract (intros; try solve [ reflexivity || (symmetry; assumption) || (etransitivity; eauto) ];
        solve [
          (destruct (ClassInhabited E0) as [ v0 ], (ClassInhabited E1) as [ v1 ]; exists (f v0 v1); repeat eexists; eauto) ||
            (unfold In in *; destruct_hypotheses; repeat esplit; clear_InClass; try reflexivity; etransitivity; eauto)
        ]).
  Defined.

  Lemma apply2_to_class_f_inj : forall v0 v1, InClass E0 v0 -> InClass E1 v1 -> InClass apply2_to_class (f v0 v1).
    compute; firstorder.
  Qed.

  Lemma apply2_to_class_f_surj : forall v, InClass apply2_to_class v -> exists v0 v1, equiv' v (f v0 v1) /\ InClass E0 v0 /\ InClass E1 v1.
    compute; firstorder.
  Qed.
End apply2.

Hint Resolve apply2_to_class_f_inj.

Implicit Arguments apply2_to_class [value0 equiv0
  value1 equiv1
  value' equiv' equiv'_refl equiv'_sym equiv'_trans].

Lemma apply2_to_classOf
  value0 equiv0 equiv0_refl equiv0_sym equiv0_trans
  value1 equiv1 equiv1_refl equiv1_sym equiv1_trans
  value' equiv' equiv'_refl equiv'_sym equiv'_trans
  f f_mor e0 e1 :
  @apply2_to_class value0 equiv0 value1 equiv1 value' equiv'
  equiv'_refl equiv'_sym equiv'_trans
  f f_mor
  (@classOf _ _ equiv0_refl equiv0_sym equiv0_trans e0)
  (@classOf _ _ equiv1_refl equiv1_sym equiv1_trans e1)
  = @classOf _ _ equiv'_refl equiv'_sym equiv'_trans (f e0 e1).
Proof.
  apply forall__eq; intros; split; intros;
    hnf in *; destruct_hypotheses;
      repeat (clear_InClass; eexists; repeat split);
      clear_InClass; eauto; try reflexivity.
Qed.
