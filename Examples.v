Require Import Omega Arith List Eqdep_dec Program.
Require Import Schema Category Instance Translation.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.


(** * The empty category *)

Definition empty : Schema.
  refine {| Vertex := Empty_set;
    Edge := fun _ _ => Empty_set;
    PathsEquivalent := (fun _ _ _ _ => True) |};
  abstract (repeat intuition).
Defined.

Definition emptyI : Instance empty.
  refine {| TypeOf := fun x : empty => match x with end;
    FunctionOf := fun _ _ (x : Empty_set) _ => match x with end |};
  abstract destruct s.
Defined.


(** * The Booleans with "implies" edges *)

Definition booleans : Schema.
  refine {| Vertex := bool;
    Edge := (fun b1 b2 => b2 = false \/ b1 = true);
    PathsEquivalent := (fun _ _ _ _ => True) |};
  abstract (repeat intuition).
Defined.


(** * The naturals with >= edges *)

Definition naturals : Schema.
  refine {| Vertex := nat;
    Edge := ge;
    PathsEquivalent := (fun _ _ _ _ => True) |};
  abstract (repeat intuition).
Defined.


(** * Silly functor from Booleans to naturals *)

Definition boolToNat (b : bool) := if b then 1 else 0.

Theorem boolToNat_ge : forall b1 b2, (b2 = false \/ b1 = true)
  -> boolToNat b1 >= boolToNat b2.
  destruct b1; destruct b2; simpl; intuition.
Qed.

Definition booleans_to_naturals : Translation booleans naturals.
  refine {| VertexOf := (boolToNat : booleans -> naturals);
    PathOf := fun _ _ e => AddEdge NoEdges (boolToNat_ge e) |};
  abstract auto.
Defined.


(** Give an instance by interpreting naturals as bitvectors and edges as forgetting of initial bits. *)

Inductive bitvector : nat -> Type :=
| BO : bitvector O
| BS : forall n, bool -> bitvector n -> bitvector (S n).

Fixpoint forget (n m : nat) (bv : bitvector n) : bitvector (n - m) :=
  match bv in bitvector n return bitvector (n - m) with
    | BO => BO
    | BS n' b bv' => match m return bitvector (S n' - m) with
                       | O => BS b bv'
                       | S m' => forget _ bv'
                     end
  end.

Theorem bitvector_case : forall n (bv : bitvector n),
  match n return bitvector n -> Prop with
    | O => fun bv => bv = BO
    | S _ => fun bv => exists b, exists bv', bv = BS b bv'
  end bv.
  destruct bv; eauto.
Qed.

Fixpoint erase n (bv : bitvector n) : list bool :=
  match bv with
    | BO => nil
    | BS _ b bv' => b :: erase bv'
  end.

Theorem erase_eq : forall n (bv bv' : bitvector n),
  erase bv = erase bv'
  -> bv = bv'.
  induction bv; intro bv'; specialize (bitvector_case bv'); firstorder; subst; simpl in *.
  injection H0; intros.
  f_equal; eauto.
Qed.

Fixpoint forget' (m : nat) (bv : list bool) : list bool :=
  match bv with
    | nil => nil
    | b :: bv' => match m with
                    | O => b :: bv'
                    | S m' => forget' m' bv'
                  end
  end.

Theorem forget_forget' : forall n (bv : bitvector n) m,
  erase (forget m bv) = forget' m (erase bv).
  induction bv; destruct m; simpl; intuition.
Qed.

Theorem double_sub : forall n1 n2, n1 >= n2 -> n1 - (n1 - n2) = n2.
  intros; omega.
Qed.

Theorem push_app : forall dom (ran : nat -> Type) n1 n2 (f : dom -> ran n1) x (pf : n1 = n2),
  match pf in _ = N return dom -> ran N with
    | refl_equal => f
  end x = match pf in _ = N return ran N with
            | refl_equal => f x
          end.
  intros; subst; reflexivity.
Qed.

Theorem push_erase : forall n1 n2 (Heq : n1 = n2) bv,
  erase (match Heq in _ = N return bitvector N with
           | refl_equal => bv
         end) = erase bv.
  intros; subst; reflexivity.
Qed.

Theorem double_forget' : forall m2 bv m1,
  forget' m2 (forget' m1 bv) = forget' (m1 + m2) bv.
  induction bv; destruct m1; simpl; intuition.
  induction m2; auto.
Qed.

Lemma path_ge : forall n1 n2, path' ge n1 n2 -> n1 >= n2.
  induction 1; simpl; intuition.
Qed.

Lemma compose_unique' : forall n1 n2 (p : path' ge n1 n2) bv,
  erase (compose bitvector (fun n1 n2 pf => match double_sub pf in _ = N return _ -> bitvector N with
                                              | refl_equal => @forget n1 (n1 - n2)
                                            end) p bv)
  = erase (forget (n1 - n2) bv).
  induction p; simpl; intuition.

  rewrite minus_diag.
  destruct bv; reflexivity.

  rewrite push_app.
  rewrite push_erase.
  repeat rewrite forget_forget'.
  rewrite IHp.
  rewrite forget_forget'.
  rewrite <- forget_forget'.
  rewrite forget_forget'.
  rewrite double_forget'.
  f_equal.
  specialize (path_ge p).
  omega.
Qed.

Lemma compose_unique : forall n1 n2 Heq (p : path' ge n1 n2) bv,
  compose bitvector (fun n1 n2 pf => match double_sub pf in _ = N return _ -> bitvector N with
                                       | refl_equal => @forget n1 (n1 - n2)
                                     end) p bv
  = match Heq in _ = N return bitvector N with
      | refl_equal => forget (n1 - n2) bv
    end.
  intros; apply erase_eq.
  rewrite compose_unique'.
  generalize (forget (n1 - n2) bv), Heq.
  rewrite Heq; intros.
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.

Definition bitvectors : Instance naturals.
  refine {| TypeOf := (bitvector : Vertex naturals -> _);
    FunctionOf := (fun n1 n2 pf => match double_sub pf in _ = N return _ -> bitvector N with
                                     | refl_equal => @forget n1 (n1 - n2)
                                   end) |}.
  abstract (intros; assert (Heq : s - (s - d) = d) by (specialize (path_ge p1); omega);
    repeat rewrite (compose_unique Heq); reflexivity).
Defined.


(** * A sample schema and database *)

Inductive emailsV :=
| SelfEmails
| Emails
| People.

Inductive emailsE : emailsV -> emailsV -> Type :=
| SelfEmails_Emails : emailsE SelfEmails Emails
| Sender : emailsE Emails People
| Receiver : emailsE Emails People.

Inductive emailsEq : forall s d, path' emailsE s d -> path' emailsE s d -> Prop :=
| Refl : forall s d (p : path' emailsE s d), emailsEq p p
| Law : emailsEq (AddEdge (AddEdge NoEdges SelfEmails_Emails) Sender)
  (AddEdge (AddEdge NoEdges SelfEmails_Emails) Receiver)
| LawSymm : emailsEq (AddEdge (AddEdge NoEdges SelfEmails_Emails) Receiver)
  (AddEdge (AddEdge NoEdges SelfEmails_Emails) Sender).

Hint Constructors emailsEq.

Inductive selfEmailId := S181.
Inductive emailId := E180 | E181.
Inductive person := Bob | Sue | David.

Ltac dep_destruct H := generalize H; intro H'; dependent destruction H'.

Ltac destructor := simpl; intuition;
  repeat (match goal with
            | [ H : ?T |- _ ] =>
              match eval hnf in T with
                | emailsEq ?X ?Y =>
                  match goal with
                    | [ x : _ |- _ ] =>
                      match x with
                        | X => hnf in H; dep_destruct H
                        | Y => hnf in H; dep_destruct H
                      end
                  end
                | emailsE _ _ => dep_destruct H
                | selfEmailId => destruct H
              end
          end; simpl in *); auto.

Definition emailsSchema : Schema.
  refine {| Vertex := emailsV;
    Edge := emailsE;
    PathsEquivalent := emailsEq
    |}; abstract (repeat destructor; try split; hnf; destructor).
Defined.

Definition emailsTypeof (v : emailsSchema) : Set :=
  match v with
    | SelfEmails => selfEmailId
    | Emails => emailId
    | People => person
  end.

Definition emailsInstance : Instance emailsSchema.
  refine {| TypeOf := emailsTypeof;
    FunctionOf := (fun s d (E : Edge emailsSchema s d) =>
      match E in emailsE s d return emailsTypeof s -> emailsTypeof d with
        | SelfEmails_Emails => fun id => match id with
                                           | S181 => E181
                                         end
        | Sender => fun id => match id with
                                | E180 => Bob
                                | E181 => David
                              end
        | Receiver => fun id => match id with
                                  | E180 => Sue
                                  | E181 => David
                                end
      end)
   |}; abstract destructor.
Defined.
