Require Import List.

Set Implicit Arguments.


(** * Types *)

(** Every cell in a row has a [Type]; a row is an ordered list of cells *)
Definition RowType := list Type.

(** A [Column] is a fancy way of indexing into a [Row].  It's typed
    with the type of the relevant cell in the row, for convenience *)
Inductive Column (T : Type) : RowType -> Type :=
| CFirst : forall Ts, Column T (T :: Ts)
| CNext : forall T' Ts, Column T Ts -> Column T (T' :: Ts).

(** A [Row] is a list of cells, each cell having the type specified by the [RowType] *)
Inductive Row : RowType -> Type :=
| RNil : Row nil
| RCons : forall T Ts, T -> Row Ts -> Row (T :: Ts).

(** A [Table] of a particular [RowType] is a list of [Row]s of that type. *)
Definition Table (R : RowType) := list (Row R).
(* Might be nicer to use a multiset type instead of [list]. *)

(** A database is typed as a collection of [Table]s, each having a [RowType] *)
Definition DatabaseType := list RowType.

(** A [TableName] is a fancy way of indexing into a [Database]. *)
Inductive TableName (R : RowType) : DatabaseType -> Type :=
| TFirst : forall Rs, TableName R (R :: Rs)
| TNext : forall R' Rs, TableName R Rs -> TableName R (R' :: Rs).

(** A database is a list of tables *)
Inductive Database : DatabaseType -> Type :=
| DNil : Database nil
| DCons : forall R Rs, Table R -> Database Rs -> Database (R :: Rs).


(** * Operations *)

Definition RowHd T Ts (r : Row (T :: Ts)) : T :=
  match r with
    | RNil => tt
    | RCons _ _ v _ => v
  end.

Definition RowTl T Ts (r : Row (T :: Ts)) : Row Ts :=
  match r with
    | RNil => tt
    | RCons _ _ _ r' => r'
  end.

Fixpoint getColumn T R (c : Column T R) : Row R -> T :=
  match c with
    | CFirst _ => fun r => RowHd r
    | CNext _ _ c' => fun r => getColumn c' (RowTl r)
  end.

Definition DatabaseHd R Rs (d : Database (R :: Rs)) : Table R :=
  match d with
    | DNil => tt
    | DCons _ _ r _ => r
  end.

Definition DatabaseTl R Rs (d : Database (R :: Rs)) : Database Rs :=
  match d with
    | DNil => tt
    | DCons _ _ _ d' => d'
  end.

Fixpoint getTable R Rs (tn : TableName R Rs) : Database Rs -> Table R :=
  match tn with
    | TFirst _ => fun d => DatabaseHd d
    | TNext _ _ tn' => fun d => getTable tn' (DatabaseTl d)
  end.
