Require Import Program Setoid Ensembles.

Set Implicit Arguments.

(**
   An equivalence class is a non-empty set of all values
   which are all equivalent to some particular value.
*)

(* [firstorder] does better without [<->] *)
Section unfold_iff.
  Lemma unfold_iff T (f : T -> Prop) eqv : (forall v : T, f v -> forall v' : T, eqv v v' <-> f v') ->
    (forall v : T, f v -> forall v' : T, eqv v v' -> f v') /\
    (forall v : T, f v -> forall v' : T, f v' -> eqv v v').
    repeat match goal with
             | [ H : _ |- _ ] => clear H
           end.
    firstorder.
  Qed.
End unfold_iff.

Implicit Arguments unfold_iff [T f eqv].

Local Ltac unfold_iff :=
  repeat match goal with
           | [ H : _ |- _ ] => destruct (unfold_iff H); clear H
         end.

Local Ltac specialize_with tac fin_tac :=
  match goal with
    | [ x : ?T, H : forall _ : ?T, _ |- _ ] => specialize (H x); tac; specialize_with tac fin_tac
    | _ => fin_tac
  end.

Section equiv.
  Variable value : Type.
  Variable equiv : value -> value -> Prop.

  (* Equivalence relations are reflexive, symmetric, and transitive. *)
  Hypotheses equiv_refl : forall (v : value), equiv v v.
  Hypothesis equiv_sym : forall (v v' : value),
    equiv v v' -> equiv v' v.
  Hypothesis equiv_trans : forall (v v' v'' : value),
    equiv v v' -> equiv v' v'' -> equiv v v''.

  Add Parametric Relation : _ equiv
    reflexivity proved by equiv_refl
    symmetry proved by equiv_sym
    transitivity proved by equiv_trans
      as equiv_equiv_rel.

  (* [E] is an equivalence class if it is non-empty and if all it consists
     of all values that are equivalent to some particular value.
     Because the equivalence relation is transitive, we can encode
     this without picking a representative element by requiring that
     for every member of the class, the class consists of exactly the
     values equivalent to that member. *)
  Let isEquivalenceClass (E : Ensemble value) := Inhabited _ E /\ forall v, In _ E v -> forall v', (equiv v v' <-> In _ E v').

  Definition EquivalenceClass (r := equiv_refl) (s := equiv_sym) (t := equiv_trans) := { E : Ensemble value | isEquivalenceClass E }.

  (* The equivalence [classOf] a particular [value] is defined by the proposition that
     the elements are equivalent to that [value]. *)
  Definition classOf (v : value) : EquivalenceClass.
    exists (fun v' => equiv v v').
    firstorder.
  Defined.

  (* Convenience methods to deal with equivalence classes.
     These allow us to define an abstraction barrier, and
     prove everything that we want to prove, without unfolding
     past the barrier. *)

  Definition inClass (C : EquivalenceClass) (v : value) := In _ (proj1_sig C) v.

  Lemma EquivalenceClass_inhabited (C : EquivalenceClass) : exists v, inClass C v.
    destruct C as [ ? [ [ ] ? ] ].
    eauto.
  Qed.

  Lemma classOf_refl : forall v, inClass (classOf v) v.
    compute; intro; reflexivity.
  Qed.

  Lemma EquivalenceClass_equivalent (C : EquivalenceClass) : forall v, inClass C v -> forall v', inClass C v' -> equiv v v'.
    destruct C as [ ? [ [ ] ? ] ].
    unfold inClass, In, proj1_sig in *.
    unfold_iff.
    intros.
    specialize_with idtac ltac:(solve [ intuition ]).
  Qed.

  Lemma EquivalenceClass_contains_equivalent (C : EquivalenceClass) : forall v, inClass C v -> forall v', equiv v v' -> inClass C v'.
    destruct C as [ ? [ [ ] ? ] ].
    unfold inClass, In, proj1_sig in *.
    unfold_iff.
    intros.
    specialize_with idtac ltac:(solve [ intuition ]).
  Qed.

  Global Add Parametric Morphism C : (inClass C)
    with signature equiv ==> iff
      as inClass_mor.
    intros x y eqv; split; intro inc;
      eapply EquivalenceClass_contains_equivalent; eauto.
  Qed.

  (* Two equivalence classes are the same if they share all values *)
  Definition sameClass (C C' : EquivalenceClass) := forall v, (inClass C v <-> inClass C' v).

  Definition disjointClasses (C C' : EquivalenceClass) := forall v, ~inClass C v \/ ~inClass C' v.

  Definition differentClasses (C C' : EquivalenceClass) := exists v,
    (inClass C v /\ ~inClass C' v) \/
    (~inClass C v /\ inClass C' v).

  Definition notDisjointClasses (C C' : EquivalenceClass) := exists v, inClass C v /\ inClass C' v.

  Definition notDisjointClasses' (C C' : EquivalenceClass) := exists v v', inClass C v /\ inClass C' v' /\ equiv v v'.

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
    intro H; unfold sameClass, inClass, proj1_sig in H.
    destruct C as [ x eqv ], C' as [ x' eqv' ].
    generalize eqv; generalize eqv'.
    cut (x = x').
    let H := fresh in intro H; rewrite H; clear H;
      let a := fresh in
        let b := fresh in
          intros a b;
            assert (H : a = b) by (apply proof_irrelevance); rewrite H; clear H; reflexivity.
    apply Extensionality_Ensembles.
    constructor; unfold Included; intro; specialize_with intuition trivial.
  Qed.

  Global Add Parametric Morphism : classOf
    with signature equiv ==> eq
      as classOf_mor.
    intros x y eqv;
      apply sameClass_eq; compute in *; eauto.
  Qed.

  Lemma disjointClasses_differentClasses (C C' : EquivalenceClass) : (disjointClasses C C') -> (differentClasses C C').
    unfold differentClasses, disjointClasses; intro H.
    pose (EquivalenceClass_inhabited C) as H'; destruct H' as [ x H' ].
    exists x; specialize (H x); tauto.
  Qed.

  Lemma notDisjointClasses_sameClass (C C' : EquivalenceClass) : (notDisjointClasses C C') -> (sameClass C C').
    unfold notDisjointClasses, sameClass; intro H; destruct H as [ x [ H0 H1 ] ]; intro v;
      firstorder;
        match goal with
          | [ H0 : inClass ?C ?x, H1 : inClass ?C ?y |- inClass ?C' ?x ]
            => let H := fresh in
              assert (equiv x y) by (apply (EquivalenceClass_equivalent C); assumption);
                rewrite H; assumption
        end.
  Qed.

  Lemma notDisjointClasses_eq (C C' : EquivalenceClass) : (notDisjointClasses C C') -> C = C'.
    intro; apply sameClass_eq; apply notDisjointClasses_sameClass; assumption.
  Qed.

  Lemma forall_equiv__eq (C C' : EquivalenceClass) :
    (forall v v', (inClass C v \/ inClass C' v') -> (inClass C v /\ inClass C' v' <-> equiv v v')) ->
    C' = C.
    intro H. apply sameClass_eq; unfold sameClass; intro v.
    assert (equiv v v) by reflexivity; firstorder.
  Qed.
End equiv.

Implicit Arguments classOf [value equiv equiv_refl equiv_sym equiv_trans].

Add Parametric Relation value equiv equiv_refl equiv_sym equiv_trans : _ (@sameClass value equiv equiv_refl equiv_sym equiv_trans)
  reflexivity proved by (@sameClass_refl _ _ _ _ _)
  symmetry proved by (@sameClass_sym _ _ _ _ _)
  transitivity proved by (@sameClass_trans _ _ _ _ _)
    as sameClass_mor.

Hint Extern 1 (@eq (EquivalenceClass _ _ _ _ _ _) _ _) => apply forall_equiv__eq.

Ltac replace_inClass :=
  repeat match goal with
           | [ H : inClass ?C ?x, H' : inClass ?C ?x' |- _ ] =>
             let H'' := fresh in assert (H'' := EquivalenceClass_equivalent C _ H _ H'); clear H'
           | [ H : inClass ?C ?x |- inClass ?C ?x' ] => apply (EquivalenceClass_contains_equivalent C x H x')
           | [ |- exists v : ?T, @?G v ] =>
             match G with
               | appcontext[inClass ?C ?v] => fail (* [?v] cannot be the same as [v] above, so we fail *)
               | appcontext[inClass ?C _] => (* match an [inClass] expression that references a variable not scoped outside.
                                                This is a kludge to get the correct inClass, which matches the [exists]. *)
                 let v := fresh in let H := fresh in
                   destruct (EquivalenceClass_inhabited C) as [ v H ]; exists v
             end
         end.

Ltac clear_inClass' :=
  repeat match goal with
           | [ H : inClass _ _ |- _ ] => clear H
         end.

Ltac clear_inClass := replace_inClass; clear_inClass'.

Section apply1.
  Variable value0 : Type.
  Variable equiv0 : value0 -> value0 -> Prop.

  (* Equivalence relations are reflexive, symmetric, and transitive. *)
  Hypotheses equiv0_refl : forall (v : value0), equiv0 v v.
  Hypothesis equiv0_sym : forall (v v' : value0),
    equiv0 v v' -> equiv0 v' v.
  Hypothesis equiv0_trans : forall (v v' v'' : value0),
    equiv0 v v' -> equiv0 v' v'' -> equiv0 v v''.

  Add Parametric Relation : _ equiv0
    reflexivity proved by equiv0_refl
    symmetry proved by equiv0_sym
    transitivity proved by equiv0_trans
      as apply1_equiv0_rel.


  Variable value : Type.
  Variable equiv : value -> value -> Prop.

  (* Equivalence relations are reflexive, symmetric, and transitive. *)
  Hypotheses equiv_refl : forall (v : value), equiv v v.
  Hypothesis equiv_sym : forall (v v' : value),
    equiv v v' -> equiv v' v.
  Hypothesis equiv_trans : forall (v v' v'' : value),
    equiv v v' -> equiv v' v'' -> equiv v v''.

  Add Parametric Relation : _ equiv
    reflexivity proved by equiv_refl
    symmetry proved by equiv_sym
    transitivity proved by equiv_trans
      as apply1_equiv_rel.

  Variable f : value0 -> value.
  Hypothesis f_mor : forall v v', equiv0 v v' -> equiv (f v) (f v').
  Variable E0 : EquivalenceClass equiv0 equiv0_refl equiv0_sym equiv0_trans.

  (* XXX TODO: automate this better *)
  Definition apply_to_class : EquivalenceClass equiv equiv_refl equiv_sym equiv_trans.
    unfold EquivalenceClass.
    exists (fun v => exists v0, inClass E0 v0 /\ equiv v (f v0)); unfold In; simpl.
    split.
    destruct (EquivalenceClass_inhabited E0) as [ v0 H ]; exists (f v0); eexists; eauto.
    intros v H v'; destruct H as [ x [ ] ]; split; intro H'; solve [ eexists; eauto ] ||
      destruct H' as [ x0 [ ] ].
    match goal with
      | [ H : equiv ?v (f ?x), H' : equiv ?v' (f ?x') |- equiv ?v ?v' ] => transitivity (f x); auto; transitivity (f x'); auto
    end.
    apply f_mor; eapply EquivalenceClass_equivalent; eauto.
  Defined.

  Lemma apply_to_class_f_inj : forall v, inClass E0 v -> inClass apply_to_class (f v).
    compute. intro v.
    destruct E0 as [ ? [ [ x0 ? ] ? ] ].
    exists x0;
      try split; unfold_iff; firstorder.
  Qed.

  Lemma apply_to_class_f_surj : forall v, inClass apply_to_class v -> exists v', equiv v (f v') /\ inClass E0 v'.
    compute. intro v.
    destruct E0 as [ ? [ [ ? ? ] ? ] ].
    destruct 1 as [ ? [ ] ].
    match goal with
      | [ H : equiv v (f ?x) |- _ ] => exists x
    end.
    split; unfold_iff; firstorder.
  Qed.
End apply1.

Hint Resolve apply_to_class_f_inj.

Implicit Arguments apply_to_class [value0 equiv0 equiv0_refl equiv0_sym equiv0_trans
  value equiv equiv_refl equiv_sym equiv_trans].

Section apply2.
  Variable value0 : Type.
  Variable equiv0 : value0 -> value0 -> Prop.

  (* Equivalence relations are reflexive, symmetric, and transitive. *)
  Hypotheses equiv0_refl : forall (v : value0), equiv0 v v.
  Hypothesis equiv0_sym : forall (v v' : value0),
    equiv0 v v' -> equiv0 v' v.
  Hypothesis equiv0_trans : forall (v v' v'' : value0),
    equiv0 v v' -> equiv0 v' v'' -> equiv0 v v''.

  Add Parametric Relation : _ equiv0
    reflexivity proved by equiv0_refl
    symmetry proved by equiv0_sym
    transitivity proved by equiv0_trans
      as apply2_equiv0_rel.


  Variable value1 : Type.
  Variable equiv1 : value1 -> value1 -> Prop.

  (* Equivalence relations are reflexive, symmetric, and transitive. *)
  Hypotheses equiv1_refl : forall (v : value1), equiv1 v v.
  Hypothesis equiv1_sym : forall (v v' : value1),
    equiv1 v v' -> equiv1 v' v.
  Hypothesis equiv1_trans : forall (v v' v'' : value1),
    equiv1 v v' -> equiv1 v' v'' -> equiv1 v v''.

  Add Parametric Relation : _ equiv1
    reflexivity proved by equiv1_refl
    symmetry proved by equiv1_sym
    transitivity proved by equiv1_trans
      as apply2_equiv1_rel.


  Variable value : Type.
  Variable equiv : value -> value -> Prop.

  (* Equivalence relations are reflexive, symmetric, and transitive. *)
  Hypotheses equiv_refl : forall (v : value), equiv v v.
  Hypothesis equiv_sym : forall (v v' : value),
    equiv v v' -> equiv v' v.
  Hypothesis equiv_trans : forall (v v' v'' : value),
    equiv v v' -> equiv v' v'' -> equiv v v''.

  Add Parametric Relation : _ equiv
    reflexivity proved by equiv_refl
    symmetry proved by equiv_sym
    transitivity proved by equiv_trans
      as apply2_equiv_rel.

  Variable f : value0 -> value1 -> value.
  Hypothesis f_mor : forall v0 v0', equiv0 v0 v0' -> forall v1 v1', equiv1 v1 v1' -> equiv (f v0 v1) (f v0' v1').
  Variable E0 : EquivalenceClass equiv0 equiv0_refl equiv0_sym equiv0_trans.
  Variable E1 : EquivalenceClass equiv1 equiv1_refl equiv1_sym equiv1_trans.

  (* XXX TODO: automate this better *)
  Definition apply2_to_class : EquivalenceClass equiv equiv_refl equiv_sym equiv_trans.
    unfold EquivalenceClass.
    exists (fun v => exists v0 v1, inClass E0 v0 /\ inClass E1 v1 /\ equiv v (f v0 v1)).
    split.
    destruct (EquivalenceClass_inhabited E0) as [ v0 H0 ],
      (EquivalenceClass_inhabited E1) as [ v1 H1 ]; exists (f v0 v1); eexists; eauto.
    intros v H0 v'; destruct H0 as [ x0 [ x1 [ ? [ ] ] ] ]; split; intro H'; solve [ eexists; eexists; eauto ] ||
      unfold In in H'; destruct H' as [ x0' [ x1' [ ? [ ] ] ] ].
    match goal with
      | [ H : equiv ?v (f ?x0 ?x1), H' : equiv ?v' (f ?x0' ?x1') |- equiv ?v ?v' ] => transitivity (f x0 x1); auto; transitivity (f x0' x1'); auto
    end.
    apply f_mor; eapply EquivalenceClass_equivalent; eauto.
  Defined.

  Lemma apply2_to_class_f_inj : forall v0 v1, inClass E0 v0 -> inClass E1 v1 -> inClass apply2_to_class (f v0 v1).
    compute. intros v0 v1.
    destruct E0 as [ ? [ [ x0' ? ] ? ] ].
    destruct E1 as [ ? [ [ x1' ? ] ? ] ].
    exists x0'; exists x1';
      try split; unfold_iff; firstorder.
  Qed.

  Lemma apply2_to_class_f_surj : forall v, inClass apply2_to_class v -> exists v0 v1, equiv v (f v0 v1) /\ inClass E0 v0 /\ inClass E1 v1.
    compute. intro v.
    destruct E0 as [ ? [ [ ? ? ] ? ] ].
    destruct E1 as [ ? [ [ ? ? ] ? ] ].
    destruct 1 as [ ? [ ? [ ? [ ] ] ] ].
    match goal with
      | [ H : equiv v (f ?x0 ?x1) |- _ ] => exists x0; exists x1
    end.
    split; unfold_iff; firstorder.
  Qed.
End apply2.

Hint Resolve apply2_to_class_f_inj.

Implicit Arguments apply2_to_class [value0 equiv0 equiv0_refl equiv0_sym equiv0_trans
  value1 equiv1 equiv1_refl equiv1_sym equiv1_trans
  value equiv equiv_refl equiv_sym equiv_trans].
