Require Import List Setoid Classes.RelationClasses.
Require Export Database.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

(** * Constraints *)
Section keys.
  (** A [KeyConstraint] is an assertion that some column in some table
      is a key.  Morally, this amounts to requiring that [forall x y :
      row in table, x.key_col = y.key_col -> x = y]. *)

  Inductive KeyConstraint (R : RowType) T (c : Column T R) : Prop := ColumnIsKey.

  Definition KeyConstraintDenote (R : RowType) T (c : Column T R) (KC : KeyConstraint c) (Tbl : Table R) : Prop
    := forall x y, In x Tbl -> In y Tbl -> getColumn c x = getColumn c y -> x = y.

  (** A [ForeignKeyConstraint] is an assertion that some column in
      some table points to some column in some other table.  We
      require that foreign key columns point only to columns which are
      keys.  Morally, this amounts to requiring that [forall x : row
      in table 1, exists y : row in table 2, x.fk_source =
      y.fk_destination]. *)

  Inductive ForeignKeyConstraint
            (R_src R_dst : RowType) T (c_src : Column T R_src) (c_dst : Column T R_dst)
            (destination_is_key : KeyConstraint c_dst) : Prop
    := ColumnsAreForeignKeys.

  Definition ForeignKeyConstraintDenote R_src R_dst T c_src c_dst destination_is_key
             (FKC : @ForeignKeyConstraint R_src R_dst T c_src c_dst destination_is_key)
             (Tbl_src : Table R_src) (Tbl_dst : Table R_dst)
  : Prop
    := KeyConstraintDenote destination_is_key Tbl_dst
       /\ forall x,
            In x Tbl_src
            -> exists y,
                 In y Tbl_dst
                 /\ getColumn c_src x = getColumn c_dst y.

  Inductive DatabaseTypeConstraintList (D : DatabaseType) : Type :=
  | DTCNil : DatabaseTypeConstraintList D
  | KeyConstraintCons : forall (R : RowType) T (c : Column T R) (TN : TableName R D),
                          @KeyConstraint R T c
                          -> DatabaseTypeConstraintList D
                          -> DatabaseTypeConstraintList D
  | ForeignKeyConstraintCons : forall (R_src R_dst : RowType) T (c_src : Column T R_src) (c_dst : Column T R_dst)
                                      (destination_is_key : KeyConstraint c_dst)
                                      (TN_src : TableName R_src D) (TN_dst : TableName R_dst D),
                                 @ForeignKeyConstraint R_src R_dst T c_src c_dst destination_is_key
                                 -> DatabaseTypeConstraintList D
                                 -> DatabaseTypeConstraintList D.

  Fixpoint DatabaseTypeConstraintListDenote DT (D : DatabaseInstance DT) (l : DatabaseTypeConstraintList DT)
  : Prop
    := match l with
         | DTCNil => True
         | KeyConstraintCons R T c TN KC xs
           => DatabaseTypeConstraintListDenote D xs
              /\ KeyConstraintDenote KC (getTable TN D)
         | ForeignKeyConstraintCons R_src R_dst T c_src c_dst destination_is_key TN_src TN_dst FKC xs
           => DatabaseTypeConstraintListDenote D xs
              /\ ForeignKeyConstraintDenote FKC (getTable TN_src D) (getTable TN_dst D)
       end.
End keys.
