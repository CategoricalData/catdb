Require Import Setoid ProofIrrelevance FunctionalExtensionality.
Require Import Common Notations.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

(**
   An equivalence class is a non-empty set of all values
   which are all equivalent to some particular value.
*)

Local Ltac apply_proof_irrelevance :=
  match goal with
    | [ |- @eq ?T _ _ ] => let T' := type of T in
                           match eval hnf in T' with
                             | Prop => apply proof_irrelevance
                           end
  end.

Local Ltac specialize_with tac fin_tac :=
  match goal with
    | [ x : ?T, H : forall _ : ?T, _ |- _ ] => specialize (H x); tac; specialize_with tac fin_tac
    | _ => fin_tac
  end.

Section EquivalenceSet.
  Variable value : Set.
  Variable equiv : value -> value -> Prop.

  (* [E] is an equivalence class if it is non-empty and if all it consists
     of all values that are equivalent to some particular value.
     Because the equivalence relation is transitive, we can encode
     this without picking a representative element by requiring that
     for every member of the class, the class consists of exactly the
     values equivalent to that member.

     We define an [EquivalenceSet] by a map [value -> bool], rather than
     [value -> Prop], so that it can live in [Set]. *)
  Record EquivalenceSet : Set := {
    InSet' : value -> bool;
    InSet : value -> Prop := (fun v => InSet' v = true);

    SetInhabited : exists v : value, InSet v;

    SetEquivalent : relation value := equiv;
    SetEquivalent_refl : Reflexive SetEquivalent;
    SetEquivalent_sym : Symmetric SetEquivalent;
    SetEquivalent_trans : Transitive SetEquivalent;

    SetElementsEquivalent : forall v, InSet v -> forall v', InSet v' -> SetEquivalent v v';
    SetContainsEquivalent : forall v, InSet v -> forall v', SetEquivalent v v' -> InSet v'
  }.
End EquivalenceSet.

Add Parametric Relation value equiv (E : @EquivalenceSet value equiv) : _ (SetEquivalent E)
  reflexivity proved by (@SetEquivalent_refl _ _ _)
  symmetry proved by (@SetEquivalent_sym _ _ _)
  transitivity proved by (@SetEquivalent_trans _ _ _)
    as SetEquivalent_rel.

Add Parametric Morphism value equiv (E : @EquivalenceSet value equiv) : (InSet E)
  with signature equiv ==> iff
    as InSet_mor.
  intros x y eqv; split; intro inc;
    eapply SetContainsEquivalent; eauto; try symmetry; eauto.
Qed.

Section equiv.
  Variable value : Set.
  Variable equiv : value -> value -> Prop.

  Hypothesis equiv_Equivalence : Equivalence equiv.

  Local Add Parametric Relation : _ equiv
    reflexivity proved by (Equivalence.equiv_reflexive _)
    symmetry proved by (Equivalence.equiv_symmetric _)
    transitivity proved by (Equivalence.equiv_transitive _)
      as equiv_equiv_rel.

  Hypotheses equiv_dec : forall v v', {equiv v v'} + {~equiv v v'}.

  Local Infix "~=" := equiv_dec.

  Local Ltac destruct_equiv :=
    repeat match goal with
             | [ |- context[?a ~= ?b] ] => destruct (a ~= b); trivial
             | [ _ : context[?a ~= ?b] |- _ ] => let H := fresh in destruct (a ~= b) as [ H | H ]; try discriminate H; trivial
           end.

  Local Ltac simpl_equiv := hnf; intros; trivial;
    repeat match goal with
             | _ => solve [ reflexivity ]
             | _ => solve [ symmetry; trivial ]
             | _ => solve [ etransitivity; eauto ]
             | _ => solve [ symmetry; etransitivity; eauto ]
             | _ => solve [ etransitivity; eauto; symmetry; eauto ]
             | [ H : false = true |- _ ] => discriminate H
             | [ H : equiv _ _ -> False |- _ ] => contradict H; trivial
             | [ H : ~ equiv _ _ |- _ ] => contradict H; trivial
             | _ => destruct_equiv
           end.

  (* The equivalence [setOf] a particular [value] is defined by the proposition that
     the elements are equivalent to that [value]. *)
  Definition setOf (v : value) : EquivalenceSet equiv.
    exists (fun v' => if v ~= v' then true else false);
      abstract (
        try exists v; repeat split; unfold InSet in *;
          simpl_equiv
      ).
  Defined.

  Lemma setOf_refl : forall v, InSet (setOf v) v.
    compute; intro; simpl_equiv.
  Qed.

  (* Two equivalence classes are the same if they share all values *)
  Definition sameSet (C C' : EquivalenceSet equiv) := forall v, (InSet C v <-> InSet C' v).

  Definition disjointSets (C C' : EquivalenceSet equiv) := forall v, ~InSet C v \/ ~InSet C' v.

  Definition differentSets (C C' : EquivalenceSet equiv) := exists v,
    (InSet C v /\ ~InSet C' v) \/
    (~InSet C v /\ InSet C' v).

  Definition notDisjointSets (C C' : EquivalenceSet equiv) := exists v, InSet C v /\ InSet C' v.

  Definition notDisjointSets' (C C' : EquivalenceSet equiv) := exists v v', InSet C v /\ InSet C' v' /\ equiv v v'.

  Lemma sameSet_refl : Reflexive sameSet.
    clear equiv_Equivalence; firstorder.
  Qed.

  Lemma sameSet_sym : Symmetric sameSet.
    clear equiv_Equivalence; firstorder.
  Qed.

  Lemma sameSet_trans : Transitive sameSet.
    clear equiv_Equivalence; firstorder.
  Qed.

  Lemma sameSet_eq (C C' : EquivalenceSet equiv) : sameSet C C' -> C = C'.
    clear equiv_Equivalence; intro H.
    cut (InSet' C = InSet' C');
      destruct C, C'; simpl;
        intros;
          unfold sameSet, proj1_sig, InSet, InSet' in *;
            simpl in *;
              repeat match goal with
                       | [ H := _ |- _ ] => subst H
                     end;
              subst;
                split_iff;
                f_equal; try apply_proof_irrelevance;
                  apply functional_extensionality_dep; intro;
                    repeat match goal with
                             | [ H : forall v, ?x v = true -> _ |- context[?x ?v] ] => specialize (H v)
                             | [ |- @eq bool ?a ?b ] => progress (destruct a; destruct b; trivial)
                             | [ H : _ |- _ ] => specialize (H (eq_refl _))
                           end;
                    assumption || symmetry; assumption.
  Qed.

  Lemma eq_sameSet (C C' : EquivalenceSet equiv) : C = C' -> sameSet C C'.
    intro; subst; apply sameSet_refl.
  Qed.

  Global Add Parametric Morphism : setOf
    with signature equiv ==> eq
      as setOf_mor.
    intros x y eqv;
      apply sameSet_eq; compute in *; intros; split; intros; simpl_equiv.
  Qed.

  Lemma setOf_eq x y : setOf x = setOf y <-> equiv x y.
    split; intro H; try apply setOf_mor; trivial.
    pose (setOf_refl x).
    pose (setOf_refl y).
    rewrite H in *;
      compute in *;
        simpl_equiv.
  Qed.

  Lemma disjointSets_differentSets (C C' : EquivalenceSet equiv) : (disjointSets C C') -> (differentSets C C').
    clear equiv_Equivalence; unfold differentSets, disjointSets; intro H.
    pose (SetInhabited C) as H'; destruct H' as [ x H' ].
    exists x; specialize (H x); tauto.
  Qed.

  Lemma notDisjointSets_sameSet (C C' : EquivalenceSet equiv) : (notDisjointSets C C') -> (sameSet C C').
    clear equiv_Equivalence; unfold notDisjointSets, sameSet; intro H; destruct H as [ x [ H0 H1 ] ]; intro v; split; intros;
      match goal with
        | [ H0 : InSet ?C ?x, H1 : InSet ?C ?y |- InSet ?C' ?x ]
          => let H := fresh in
            assert (H : equiv x y) by (apply (@SetElementsEquivalent _ _ C); assumption);
              rewrite H; assumption
      end.
  Qed.

  Lemma notDisjointSets_eq (C C' : EquivalenceSet equiv) : (notDisjointSets C C') -> C = C'.
    clear equiv_Equivalence; intro; apply sameSet_eq; apply notDisjointSets_sameSet; assumption.
  Qed.

  Lemma EquivalenceSet_forall_equiv__eq (C C' : EquivalenceSet equiv) :
    (forall v v', (InSet C v \/ InSet C' v') -> (InSet C v /\ InSet C' v' <-> equiv v v')) ->
    C' = C.
    clear equiv_Equivalence; intro H. apply sameSet_eq; unfold sameSet; intro v.
    assert (equiv v v) by reflexivity; firstorder.
  Qed.

  Lemma EquivalenceSet_forall__eq (C C' : EquivalenceSet equiv) :
    (forall v, InSet C v <-> InSet C' v) ->
    C' = C.
    clear equiv_Equivalence; intro H. apply sameSet_eq; unfold sameSet;
    firstorder.
  Qed.
End equiv.

Add Parametric Relation value equiv : _ (@sameSet value equiv)
  reflexivity proved by (@sameSet_refl _ _)
  symmetry proved by (@sameSet_sym _ _)
  transitivity proved by (@sameSet_trans _ _)
    as sameSet_mor.

Section InSet_setOf.
  Variable value : Set.
  Variable equiv : value -> value -> Prop.
  Variable C : EquivalenceSet equiv.

  Hypothesis equiv_dec : forall v v', {equiv v v'} + {~ equiv v v'}.

  Lemma InSet_setOf_eq eqv v : InSet C v -> C = setOf eqv equiv_dec v.
    intro H.
    apply sameSet_eq.
    pose (setOf eqv equiv_dec v).
    pose (setOf_refl eqv equiv_dec v).
    pose (@SetContainsEquivalent _ equiv).
    pose (@SetElementsEquivalent _ equiv).
    specialize_all_ways.
    intro; split; intro;
      eauto.
  Qed.

  Let C_Equivalence : Equivalence equiv
    := {| Equivalence_Reflexive := SetEquivalent_refl C;
          Equivalence_Symmetric := SetEquivalent_sym C;
          Equivalence_Transitive := SetEquivalent_trans C |}.

  Definition InSet_setOf_eq' : forall v, InSet C v -> C = setOf C_Equivalence equiv_dec v
    := InSet_setOf_eq C_Equivalence.
End InSet_setOf.

Ltac create_setOf_InSet :=
  repeat match goal with
           | [ H : InSet (@setOf ?v ?e ?eq ?eqdec ?val) _ |- _ ] => unique_pose (@setOf_refl v e eq eqdec val)
           | [ |- InSet (@setOf ?v ?e ?eq ?eqdec ?val) _ ] => unique_pose (@setOf_refl v e eq eqdec val)
         end.

Ltac replace_InSet := create_setOf_InSet;
  repeat match goal with
           | [ H : InSet ?C ?x, H' : InSet ?C ?x' |- _ ] => unique_pose (SetElementsEquivalent H H');
             try (clear H' || clear H) (* try, in case both appear in the conclusion *)
           | [ H : InSet ?C ?x |- InSet ?C ?x' ] => apply (SetContainsEquivalent H)
           | [ |- exists v : ?T, @?G v ] =>
             match G with
               | appcontext[InSet ?C ?v] => fail 1 (* [?v] cannot be the same as [v] above, so we fail *)
               | appcontext[InSet ?C _] => (* match an [InSet] expression that references a variable not scoped outside.
                                                This is a kludge to get the correct InSet, which matches the [exists]. *)
                 let v := fresh in let H := fresh in
                   destruct (SetInhabited C) as [ v H ]; exists v
             end
         end.

Ltac InSet2setOf eqv :=
  repeat match goal with
           | [ equiv_dec : forall v v' : _, {?equiv v v'} + {~ ?equiv v v'}, H : InSet ?C ?x |- _ ] =>
             apply (@InSet_setOf_eq _ _ C equiv_dec eqv _) in H
         end.

Ltac InSet2setOf' :=
  repeat match goal with
           | [ equiv_dec : forall v v' : _, {?equiv v v'} + {~ ?equiv v v'}, H : InSet ?C ?x |- _ ] =>
             apply (@InSet_setOf_eq' _ _ C equiv_dec _) in H
         end.

Hint Extern 1 (@eq (@EquivalenceSet _ _) _ _) => apply EquivalenceSet_forall__eq; replace_InSet.

Ltac clear_InSet' :=
  repeat match goal with
           | [ |- context[InSet] ] => fail 1
           | [ H : InSet _ _ |- _ ] => clear H
         end.

Ltac clear_InSet := replace_InSet; clear_InSet'.
(*
Section apply1.
  Variable value0 : Set.
  Variable equiv0 : value0 -> value0 -> Prop.

  Variable value' : Set.
  Variable equiv' : value' -> value' -> Prop.

  Variable f : value0 -> value'.
  Hypothesis f_mor : forall v v', equiv0 v v' -> equiv' (f v) (f v').
  Variable E0 : EquivalenceSet equiv0.

  Local Add Parametric Relation : _ equiv0
    reflexivity proved by (SetEquivalent_refl E0)
    symmetry proved by (SetEquivalent_sym E0)
    transitivity proved by (SetEquivalent_trans E0)
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

  Definition apply_to_class : EquivalenceSet equiv'.
    Print EquivalenceSet.
    refine {| UnderlyingSet := (fun v => exists v0, InSet E0 v0 /\ equiv' v (f v0)) |};
      abstract (intros; try solve [ reflexivity || (symmetry; assumption) || (etransitivity; eauto) ];
        solve [ (destruct (SetInhabited E0) as [ v0 ]; exists (f v0); eexists; split; eauto; apply f_mor; reflexivity) ||
          (unfold In in *; destruct_hypotheses; repeat esplit; clear_InSet; try reflexivity; etransitivity; eauto)
        ]).
  Defined.

  Lemma apply_to_class_f_inj : forall v, InSet E0 v -> InSet apply_to_class (f v).
    compute; firstorder.
  Qed.

  Lemma apply_to_class_f_surj : forall v, InSet apply_to_class v -> exists v', equiv' v (f v') /\ InSet E0 v'.
    compute; firstorder.
  Qed.
End apply1.

Hint Resolve apply_to_class_f_inj.

Implicit Arguments apply_to_class [value0 equiv0
  value' equiv' equiv'_refl equiv'_sym equiv'_trans].

Lemma apply_to_setOf value0 equiv0 equiv0_refl equiv0_sym equiv0_trans value' equiv' equiv'_refl equiv'_sym equiv'_trans f f_mor e0 :
  @apply_to_class value0 equiv0 value' equiv' f f_mor
  (@setOf _ _ equiv0_refl equiv0_sym equiv0_trans e0)
  equiv'_refl equiv'_sym equiv'_trans
  = @setOf _ _ equiv'_refl equiv'_sym equiv'_trans (f e0).
Proof.
  apply forall__eq; intros; split; intros;
    hnf in *; destruct_hypotheses; clear_InSet; eauto.
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

  Variable E0 : EquivalenceSet equiv0.
  Variable E1 : EquivalenceSet equiv1.

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

  Definition apply2_to_class : EquivalenceSet equiv'.
    refine {| UnderlyingSet := (fun v => exists v0 v1, InSet E0 v0 /\ InSet E1 v1 /\ equiv' v (f v0 v1)) |};
      abstract (intros; try solve [ reflexivity || (symmetry; assumption) || (etransitivity; eauto) ];
        solve [
          (destruct (SetInhabited E0) as [ v0 ], (SetInhabited E1) as [ v1 ]; exists (f v0 v1); repeat eexists; eauto) ||
            (unfold In in *; destruct_hypotheses; repeat esplit; clear_InSet; try reflexivity; etransitivity; eauto)
        ]).
  Defined.

  Lemma apply2_to_class_f_inj : forall v0 v1, InSet E0 v0 -> InSet E1 v1 -> InSet apply2_to_class (f v0 v1).
    compute; firstorder.
  Qed.

  Lemma apply2_to_class_f_surj : forall v, InSet apply2_to_class v -> exists v0 v1, equiv' v (f v0 v1) /\ InSet E0 v0 /\ InSet E1 v1.
    compute; firstorder.
  Qed.
End apply2.

Hint Resolve apply2_to_class_f_inj.

Implicit Arguments apply2_to_class [value0 equiv0
  value1 equiv1
  value' equiv' equiv'_refl equiv'_sym equiv'_trans].

Lemma apply2_to_setOf
  value0 equiv0 equiv0_refl equiv0_sym equiv0_trans
  value1 equiv1 equiv1_refl equiv1_sym equiv1_trans
  value' equiv' equiv'_refl equiv'_sym equiv'_trans
  f f_mor e0 e1 :
  @apply2_to_class value0 equiv0 value1 equiv1 value' equiv'
  equiv'_refl equiv'_sym equiv'_trans
  f f_mor
  (@setOf _ _ equiv0_refl equiv0_sym equiv0_trans e0)
  (@setOf _ _ equiv1_refl equiv1_sym equiv1_trans e1)
  = @setOf _ _ equiv'_refl equiv'_sym equiv'_trans (f e0 e1).
Proof.
  apply forall__eq; intros; split; intros;
    hnf in *; destruct_hypotheses;
      repeat (clear_InSet; eexists; repeat split);
      clear_InSet; eauto; try reflexivity.
Qed.
*)

Section description.
  (** Can be imported from Coq.Logic.ClassicalDescription,
      Coq.Logic.ClassicalEpsilon, Coq.Logic.ConstructiveEpsilon,
      Coq.Logic.Epsilon, Coq.Logic.IndefiniteDescription, or, for the
      axiom, Coq.Logic.Description *)

  Hypothesis constructive_definite_description :
    forall (A : Type) (P : A->Prop),
      (exists! x, P x) -> { x : A | P x }.

  Variable T : Set.
  Hypothesis eq_dec : forall v v' : T, {v = v'} + {v <> v'}.

  Definition EquivalenceSet_eq_lift
  : EquivalenceSet (@eq T) -> T.
    intro x.
    cut (exists! u, InSet x u).
    - apply constructive_definite_description.
    - destruct (SetInhabited x) as [u H].
      exists u.
      abstract (
          split; [ exact H
                 | intros; apply (@SetElementsEquivalent _ _ x); assumption ]
        ).
  Defined.

  Definition EquivalenceSet_eq_proj
  : T -> EquivalenceSet (@eq T).
    apply setOf; try assumption; abstract typeclasses eauto.
  Defined.

  Lemma EquivalenceSet_eq_iso1
  : forall x, EquivalenceSet_eq_lift (EquivalenceSet_eq_proj x) = x.
    intros.
    expand.
    repeat match goal with
             | _ => progress intuition
             | _ => intro
             | [ |- appcontext[match ?E with _ => _ end] ] => case E
             | [ H : appcontext[match ?E with _ => _ end] |- _ ] => destruct E
             | [ H : _ |- _ ] => solve [ inversion H ]
             | _ => progress (hnf in *; simpl in *; idtac)
           end.
  Qed.

  Lemma EquivalenceSet_eq_iso2
  : forall x, EquivalenceSet_eq_proj (EquivalenceSet_eq_lift x) = x.
    intros.
    apply sameSet_eq; simpl.
    split;
      intros;
      simpl in *;
      subst;
      hnf;
      unfold EquivalenceSet_eq_lift;
      hnf in *;
      simpl in *;
      repeat match goal with
               | _ => progress intuition
               | _ => intro
               | [ |- appcontext[match ?E with _ => _ end] ] => case E
               | [ H : appcontext[match ?E with _ => _ end] |- _ ] => destruct E
               | [ H : _ |- _ ] => solve [ inversion H ]
               | _ => progress unfold EquivalenceSet_eq_lift
               | _ => progress (hnf in *; simpl in *; idtac)
               | _ => progress subst
               | [ H : _, H' : _ |- _ ] => unique_pose (SetElementsEquivalent H H')
             end.
  Qed.
End description.
