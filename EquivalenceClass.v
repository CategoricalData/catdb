Require Import Program.
Require Import Setoid.
Require Import Ensembles.

Set Implicit Arguments.

Section equiv.
  Variable value : Type.
  Variable equiv : value -> value -> Prop.

  Hypotheses equiv_refl : forall (v : value), equiv v v.
  Hypothesis equiv_sym : forall (v v' : value),
    equiv v v' -> equiv v' v.
  Hypothesis equiv_trans : forall (v v' v'' : value),
    equiv v v' -> equiv v' v'' -> equiv v v''.

(*  Hint Immediate equiv_sym.
  Hint Resolve equiv_trans.*)

  Add Parametric Relation : _ equiv
    reflexivity proved by equiv_refl
    symmetry proved by equiv_sym
    transitivity proved by equiv_trans
      as equiv_rel.

  Definition isEquivalenceClass (E : Ensemble value) := forall v, In value E v -> forall v', (equiv v v' <-> In value E v').

  Definition EquivalenceClass := { E : Ensemble value | isEquivalenceClass E }.

  Definition classOf (v : value) : EquivalenceClass.
    exists (fun v' => equiv v v').
    intros; split; intros;
      unfold In in *;
        etransitivity; eauto.
  Defined.

  Definition in_class (C : EquivalenceClass) (v : value) := In value (proj1_sig C) v.

  Ltac specialized_assumption :=
    repeat match goal with
             | [ x : ?T, H : forall _ : ?T, _ |- _ ] => specialize (H x); specialized_assumption
             | _ => assumption
           end.

  Theorem EquivalenceClass_not_disjoint_imp_equal (C C' : EquivalenceClass) :
    (exists v, in_class C v /\ in_class C' v) -> Same_set value (proj1_sig C) (proj1_sig C').
    intro H; destruct H as [ ? [ ] ].
    destruct C, C'.
    constructor;
      unfold in_class, In, isEquivalenceClass, proj1_sig, Included in *;
        repeat match goal with
                 | [ H : ?C ?x, H' : forall v, ?C v -> _ |- _ ] => specialize (H' x H)
               end; firstorder.
  Qed.

  Theorem EquivalenceClass_not_equal_imp_disjoint (C C' : EquivalenceClass) :
    (exists v : value, (in_class C v /\ ~in_class C' v) \/ (~in_class C v /\ in_class C' v)) ->
    Disjoint value (proj1_sig C) (proj1_sig C').
    destruct C, C'.
    intro H; destruct H as [ ? [ ] ]; destruct H;
      constructor; intros; destruct 1;
        unfold Same_set, Included, In, in_class, isEquivalenceClass, proj1_sig in *;
          repeat match goal with
                   | [ H : ?C ?x, H' : forall v, ?C v -> _ |- _ ] => specialize (H' x H)
                 end; firstorder.
  Qed.

  Lemma EquivalenceClass_refl : forall v, in_class (classOf v) v.
    compute; intro; reflexivity.
  Qed.

  Lemma EquivalenceClassOf_trans' : forall v v' : value, equiv v v' -> Same_set _ (proj1_sig (classOf v)) (proj1_sig (classOf v')).
    intros v v' eqV.
    unfold Same_set, Included, In.
    split; intro x; simpl; intro; etransitivity; eauto.
  Qed.


  Theorem EquivalenceClassOf_trans : forall (v v' : value),
    equiv v v'
    -> classOf v = classOf v'.
    intros v v' eqV.
    pose (EquivalenceClassOf_trans' eqV) as H; generalize H; clear H.
    unfold proj1_sig in *.
    match goal with
      | [ |- _ -> ?a = ?b ] => destruct a as [ x ? ], b as [ y ? ]
    end.
    intro H.
    cut (x = y).
    let H := fresh in intro H; generalize i; generalize i0; rewrite H; intros; apply f_equal; apply proof_irrelevance.
    apply Extensionality_Ensembles; assumption.
  Qed.
End equiv.
