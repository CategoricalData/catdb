Require Import List Omega Program Eqdep_dec.

Set Implicit Arguments.

Section path'.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Inductive path' (s : V) : V -> Type :=
  | OneEdge : forall d, E s d -> path' s d
  | AddEdge : forall d d', path' s d -> E d d' -> path' s d'.

  Fixpoint prepend s d (p : path' s d) : forall s', E s' s -> path' s' d :=
    match p in path' _ d return forall s', E s' s -> path' s' d with
      | OneEdge _ E => fun _ E' => AddEdge (OneEdge E') E
      | AddEdge _ _ p' E => fun _ E' => AddEdge (prepend p' E') E
    end.

  Variable typeOf : V -> Type.
  Variable functionOf : forall s d, E s d -> typeOf s -> typeOf d.

  Fixpoint compose s d (p : path' s d) : typeOf s -> typeOf d :=
    match p with
      | OneEdge _ E => functionOf E
      | AddEdge _ _ p' E => fun x => functionOf E (compose p' x)
    end.
End path'.

Implicit Arguments AddEdge [V E s d d'].
Implicit Arguments prepend [V E s d s'].

Record Category := {
  Vertex :> Type;
  Edge : Vertex -> Vertex -> Type;

  PathsEquivalent : forall s d, path' Edge s d -> path' Edge s d -> Prop;
  Reflexive : forall s d (p : path' _ s d),
    PathsEquivalent p p;
  Symmetric : forall s d (p1 p2 : path' _ s d),
    PathsEquivalent p1 p2 -> PathsEquivalent p2 p1;
  Transitive : forall s d (p1 p2 p3 : path' _ s d),
    PathsEquivalent p1 p2 -> PathsEquivalent p2 p3 -> PathsEquivalent p1 p3;

  PreCompose : forall s d (E : Edge s d) d' (p1 p2 : path' _ d d'),
    PathsEquivalent p1 p2 -> PathsEquivalent (prepend p1 E) (prepend p2 E);
  PostCompose : forall s d (p1 p2 : path' _ s d) d' (E : Edge d d'),
    PathsEquivalent p1 p2 -> PathsEquivalent (AddEdge p1 E) (AddEdge p2 E)
}.

Section Category.
  Variable C : Category.

  Definition path := path' C.(Edge).

  Record Instance := {
    TypeOf :> C.(Vertex) -> Type;
    FunctionOf : forall s d (E : C.(Edge) s d), TypeOf s -> TypeOf d;
    EquivalenceOf : forall s d (p1 p2 : path s d), C.(PathsEquivalent) p1 p2
      -> forall x, compose TypeOf FunctionOf p1 x = compose TypeOf FunctionOf p2 x
  }.
End Category.


(** * The empty category *)

Definition empty : Category.
  refine {| Vertex := Empty_set;
    Edge := fun _ _ => Empty_set;
    PathsEquivalent := (fun _ _ _ _ => True) |};
  abstract auto.
Defined.

Definition emptyI : Instance empty.
  refine {| TypeOf := fun x : Vertex empty => match x with end;
    FunctionOf := fun _ _ (x : Empty_set) _ => match x with end |};
  abstract destruct s.
Defined.


(** * The naturals with >= edges *)

Definition naturals : Category.
  refine {| Vertex := nat;
    Edge := ge;
    PathsEquivalent := (fun _ _ _ _ => True) |};
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

  rewrite push_app.
  apply push_erase.
  
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
