Require Import List String.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

(* Largely copied from CPDT *)
Section ilist.
  Variable A : Type.

  Inductive ilist : nat -> Type :=
  | inil : ilist 0
  | icons : forall n, A -> ilist n -> ilist (S n).

  Inductive fin : nat -> Set :=
  | First : forall n, fin (S n)
  | Next : forall n, fin n -> fin (S n).

End ilist.

Arguments inil [A].
Arguments First [n].

Local Infix "::" := (@icons _ _).

Definition ihd' n (il : ilist Type n) : Type :=
  match il with
    | inil => Set
    | icons _ T _ => T
  end.

Definition ihd n (il : ilist Type (S n)) : Type := ihd' il.

Definition itl' n (il : ilist Type n) :=
  match il in ilist _ N return ilist Type (pred N) with
    | inil => inil
    | icons _ _ il' => il'
  end.

Definition itl n (il : ilist Type (S n)) : ilist Type n := itl' il.

Fixpoint iget n (i : fin n) : ilist Type n -> Type :=
  match i with
    | First _ => fun il => ihd il
    | Next _ i' => fun il => iget i' (itl il)
  end.

Section ilist_map.
  Variables A B : Type.
  Variable f : A -> B.

  Fixpoint imap n (ls : ilist A n) : ilist B n :=
    match ls with
      | inil => inil
      | icons _ x ls' => icons (f x) (imap ls')
    end.
End ilist_map.

(* heterogeneous indexed lists *)
Section hilist.
  Inductive hilist : forall n, ilist Type n -> Type :=
  | hinil : hilist inil
  | hicons : forall n x (ls : ilist _ n), x -> hilist ls -> hilist (icons x ls).

  Definition hihd n (il : ilist Type (S n)) (hl : hilist il) : ihd il :=
    match hl in hilist il return ihd' il with
      | hinil => unit
      | hicons _ _ _ v _ => v
    end.

  Definition hitl n (il : ilist Type (S n)) (hl : hilist il) : hilist (itl il) :=
    match hl in hilist il return hilist (itl' il) with
      | hinil => hinil
      | hicons _ _ _ _ hl' => hl'
    end.

  Fixpoint higet n (i : fin n) : forall (ils : ilist Type n), hilist ils -> iget i ils :=
    match i in fin n return forall (ils : ilist Type n), hilist ils -> iget i ils with
      | First _ => fun _ hl => hihd hl
      | Next _ i' => fun _ hl => higet i' (hitl hl)
    end.
End hilist.
