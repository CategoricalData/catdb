Require Import Program Setoid Ensembles.

Set Implicit Arguments.

(**
   An equivalence class is a non-empty set of all values
   which are all equivalent to some particular value.
*)

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
      as equiv_rel.

  (* [E] is an equivalence class if it is non-empty and if all it consists
     of all values that are equivalent to some particular value.
     Because the equivalence relation is transitive, we can encode
     this without picking a representative element by requiring that
     for every member of the class, the class consists of exactly the
     values equivalent to that member. *)
  Let isEquivalenceClass (E : Ensemble value) := Inhabited _ E /\ forall v, In _ E v -> forall v', (equiv v v' <-> In _ E v').

  Definition EquivalenceClass := { E : Ensemble value | isEquivalenceClass E }.

  (* The equivalence [classOf] a particular [value] is defined by the proposition that
     the elements are equivalent to that [value]. *)
  Definition classOf (v : value) : EquivalenceClass.
    exists (fun v' => equiv v v').
    firstorder.
  Defined.

  Let in_class (C : EquivalenceClass) (v : value) := In _ (proj1_sig C) v.

  (* [firstorder] does better without [<->] *)
  Lemma unfold_iff T (f : T -> Prop) eqv : (forall v : T, f v -> forall v' : T, eqv v v' <-> f v') ->
    (forall v : T, f v -> forall v' : T, eqv v v' -> f v') /\
    (forall v : T, f v -> forall v' : T, f v' -> eqv v v').
    firstorder.
  Qed.

  Implicit Arguments unfold_iff [T f eqv].

  Ltac unfold_iff :=
    repeat match goal with
             | [ H : _ |- _ ] => destruct (unfold_iff H); clear H
           end.

  (* If two equivalence classes share one value, then they are equal. *)
  Theorem EquivalenceClass_not_disjoint_imp_equal (C C' : EquivalenceClass) :
    (exists v, in_class C v /\ in_class C' v) -> Same_set value (proj1_sig C) (proj1_sig C').
    intro H; destruct H as [ ? [ ] ].
    destruct C, C'.
    constructor;
      unfold in_class, In, isEquivalenceClass, proj1_sig, Included in *;
        repeat match goal with
                 | [ H : ?C ?x, H' : forall v, ?C v -> _ |- _ ] => specialize (H' x H)
               end; intros; intuition;
        unfold_iff; firstorder.
  Qed.

  (* If two equivalence classes are not equal, then they are disjoint. *)
  Theorem EquivalenceClass_not_equal_imp_disjoint (C C' : EquivalenceClass) :
    (exists v : value, (in_class C v /\ ~in_class C' v) \/ (~in_class C v /\ in_class C' v)) ->
    Disjoint value (proj1_sig C) (proj1_sig C').
    destruct C, C'.
    intro H; destruct H as [ ? [ ] ]; destruct H;
      constructor; intros; destruct 1;
        unfold Same_set, Included, In, in_class, isEquivalenceClass, proj1_sig in *;
          repeat match goal with
                   | [ H : ?C ?x, H' : forall v, ?C v -> _ |- _ ] => specialize (H' x H)
                 end; intuition; unfold_iff; firstorder.
  Qed.

  Lemma classOf_refl : forall v, in_class (classOf v) v.
    compute; intro; reflexivity.
  Qed.

  Lemma classOf_trans' : forall v v' : value, equiv v v' -> Same_set _ (proj1_sig (classOf v)) (proj1_sig (classOf v')).
    intros v v' eqV.
    unfold Same_set, Included, In.
    split; intro x; simpl; intro; etransitivity; eauto.
  Qed.


  Hint Extern 1 (_ = _) => apply proof_irrelevance.
  Hint Resolve f_equal.

  Theorem classOf_trans : forall (v v' : value),
    equiv v v'
    -> classOf v = classOf v'.
    intros v v' eqV.
    generalize (classOf_trans' eqV).
    unfold proj1_sig in *.
    match goal with
      | [ |- _ -> ?a = ?b ] => destruct a as [ x i ], b as [ y i0 ]; intro; generalize i; generalize i0
    end.
    let H := fresh in assert (H : x = y) by (apply Extensionality_Ensembles; assumption);
      rewrite H; eauto.
  Qed.
End equiv.
