Require Import List Setoid Classes.RelationClasses.
Require Export Database.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

(** * Operations *)
Section sql.
  (** [SelectFromTable fromR toR cs] is the SQL query [SELECT cs FROM
      fromR], and [toR] is the resulting schema.  This operation is
      specific to a single table. *)

  Fixpoint SelectFromTable fromR toR (cs : ColumnList fromR toR) : Row fromR -> Row toR
    := match cs in (ColumnList fromR toR) return (Row fromR -> Row toR) with
         | CNil _ =>
           fun _ => RNil
         | CCons T fromTs toTs c cs' =>
           fun r => RCons (getColumn c r) (SelectFromTable cs' r)
       end.

  (** [UnionAllTables2 r t1 t2] is the SQL query [SELECT *
    FROM t1 UNION ALL SELECT * FROM t2]. *)
  Definition UnionAllTables2 (r : RowType) (t1 t2 : Table r) : Table r
    := t1 ++ t2.

  (** [UnionAllTables r [t1, t2, ..., tn]] is the SQL query [SELECT *
    FROM t1 UNION ALL SELECT * FROM t2 UNION ALL ... UNION ALL SELECT
    * FROM tn]. *)
  Definition UnionAllTables (r : RowType) (ts : list (Table r)) : Table r
    := fold_left (@UnionAllTables2 r) ts nil.

  (** [UnionTables2 r t1 t2] is the SQL query [SELECT * FROM t1 UNION
      SELECT * FROM t2]; it removes duplicates *)

  Definition UnionTables2 (r : RowType) (H : RowTypeDecidable _ _ r) (t1 t2 : Table r) : Table r
    := unique_from (Row_eq H) (UnionAllTables2 t1 t2).

  (** [UnionTables r [t1, t2, ..., tn]] is the SQL query [SELECT *
      FROM t1 UNION SELECT * FROM t2 UNION ... UNION SELECT * FROM
      tn].  It removes duplicates. *)

  Definition UnionTables (r : RowType) (H : RowTypeDecidable _ _ r) (ts : list (Table r)) : Table r
    := unique_from (Row_eq H) (UnionAllTables ts).


  (** ** CROSS JOIN *)
  (** Quoting Wikipedia (http://en.wikipedia.org/wiki/Join_(SQL)):

      CROSS JOIN returns the Cartesian product of rows from tables in
      the join. In other words, it will produce rows which combine
      each row from the first table with each row from the second
      table.[1]

      Example of an explicit cross join:

<<
      SELECT *
      FROM employee CROSS JOIN department;
>>

      Example of an implicit cross join:

<<
      SELECT *
      FROM employee, department;
>>
   *)

  (** [app_list [a b c ...] = a ++ b ++ c ++ ...] *)
  Let app_list A := fold_right (@app A) nil.

  Definition CrossJoinRowTypes2 (r1 r2 : RowType) : RowType := r1 ++ r2.
  Definition CrossJoinRowTypes (rs : list RowType) : RowType := app_list rs.

  Fixpoint CrossJoinTables2_helper r1 (t10 : Row r1) r2 (t2 : Table r2)
  : Table (CrossJoinRowTypes2 r1 r2)
    := match t2 with
         | nil => nil
         | t20 :: t2s => (RowApp t10 t20)
                           :: CrossJoinTables2_helper t10 t2s
       end.

  (** [CrossJoinTables2 r1 t1 r2 t2] is the SQL query [SELECT * FROM
      t1 CROSS JOIN t2].  It contains all pairs of rows from [t1] and
      [t2]. *)

  Fixpoint CrossJoinTables2 r1 (t1 : Table r1) r2 (t2 : Table r2)
  : Table (CrossJoinRowTypes2 r1 r2)
    := match t1 with
         | nil => nil
         | t10 :: t1s => (CrossJoinTables2_helper t10 t2)
                           ++ CrossJoinTables2 t1s t2
       end.

  (** A [Database] is a list of tables.  We can cross join all of them. *)
  Fixpoint CrossJoinTables (DT : list RowType) (ts : DatabaseInstance DT)
  : Table (CrossJoinRowTypes DT)
    := match ts with
         | DNil => nil
         | DCons _ _ t ts => CrossJoinTables2 t (CrossJoinTables ts)
       end.

  (** [Filter1 r T P c t] is the SQL query [SELECT * FROM t WHERE P(c)]
   *)

  Definition Filter1 (r : RowType) T (P : T -> bool) (c : Column T r)
  : Table r -> Table r
    := filter (fun r0 : Row r => P (getColumn c r0)).
  Definition Filter2 (r : RowType) T1 T2 (P : T1 -> T2 -> bool) (c1 : Column T1 r) (c2 : Column T2 r)
  : Table r -> Table r
    := filter (fun r0 : Row r => P (getColumn c1 r0) (getColumn c2 r0)).

  (* TODO(jgross): Add [Filter n] for arbitrary [n] *)

  (** [FilterEqual r T eq_dec c1 c2 t] is the SQL query [SELECT * FROM t WHERE c1
    = c2]. *)
  Definition FilterEqual r T (eq_dec : forall x y : T, {x = y} + {x <> y})
    := @Filter2 r T T (fun x y => if eq_dec x y then true else false).

  (** [InnerJoinTables2 r1 t1 r2 t2 T c1 c2] is the SQL query [SELECT * FROM t1
    INNTER JOIN t2 ON t1.c1 = t2.c2]. *)
  Definition InnerJoinTables2 r1 (t1 : Table r1) r2 (t2 : Table r2)
             T
             (eq_dec : forall x y : T, {x = y} + {x <> y})
             (c1 : Column T r1)
             (c2 : Column T r2)
             (t1 : Table r1)
             (t2 : Table r2)
  : Table (CrossJoinRowTypes2 r1 r2)
    := FilterEqual eq_dec
                   (@Column_RowApp_Left r1 r2 T c1)
                   (@Column_RowApp_Right r1 r2 T c2)
                   (CrossJoinTables2 t1 t2).
End sql.
