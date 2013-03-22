Require Import List.

Set Implicit Arguments.


(** * Types *)

Definition rowTy := list Type.

Inductive column (T : Type) : rowTy -> Type :=
| CFirst : forall Ts, column T (T :: Ts)
| CNext : forall T' Ts, column T Ts -> column T (T' :: Ts).

Inductive row : rowTy -> Type :=
| RNil : row nil
| RCons : forall T Ts, T -> row Ts -> row (T :: Ts).

Definition table (R : rowTy) := list (row R).
(* Might be nicer to use a multiset type instead of [list]. *)

Definition dbTy := list rowTy.

Inductive tableName (R : rowTy) : dbTy -> Type :=
| TFirst : forall Rs, tableName R (R :: Rs)
| TNext : forall R' Rs, tableName R Rs -> tableName R (R' :: Rs).

Inductive db : dbTy -> Type :=
| DNil : db nil
| DCons : forall R Rs, table R -> db Rs -> db (R :: Rs).


(** * Operations *)

Definition rowHd T Ts (r : row (T :: Ts)) : T :=
  match r in row R return match R with
                            | nil => unit
                            | T :: _ => T
                          end with
    | RNil => tt
    | RCons _ _ v _ => v
  end.

Definition rowTl T Ts (r : row (T :: Ts)) : row Ts :=
  match r in row R return match R with
                            | nil => unit
                            | _ :: Ts => row Ts
                          end with
    | RNil => tt
    | RCons _ _ _ r' => r'
  end.

Fixpoint getColumn T R (c : column T R) : row R -> T :=
  match c with
    | CFirst _ => fun r => rowHd r
    | CNext _ _ c' => fun r => getColumn c' (rowTl r)
  end.

Definition dbHd R Rs (d : db (R :: Rs)) : table R :=
  match d in db Rs return match Rs with
                            | nil => unit
                            | R :: _ => table R
                          end with
    | DNil => tt
    | DCons _ _ r _ => r
  end.

Definition dbTl R Rs (d : db (R :: Rs)) : db Rs :=
  match d in db R return match R with
                            | nil => unit
                            | _ :: Rs => db Rs
                          end with
    | DNil => tt
    | DCons _ _ _ d' => d'
  end.

Fixpoint getTable R Rs (tn : tableName R Rs) : db Rs -> table R :=
  match tn with
    | TFirst _ => fun d => dbHd d
    | TNext _ _ tn' => fun d => getTable tn' (dbTl d)
  end.
