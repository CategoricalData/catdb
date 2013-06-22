Require Import List Setoid Classes.RelationClasses.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.


(** * Types *)
Section Database.
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

  (** A database instance is a list of tables *)
  Inductive DatabaseInstance : DatabaseType -> Type :=
  | DNil : DatabaseInstance nil
  | DCons : forall R Rs, Table R -> DatabaseInstance Rs -> DatabaseInstance (R :: Rs).


  (** * Operations *)

  Definition RowHead T Ts (r : Row (T :: Ts)) : T :=
    match r with
      | RCons _ _ v _ => v
    end.

  Definition RowTail T Ts (r : Row (T :: Ts)) : Row Ts :=
    match r with
      | RCons _ _ _ r' => r'
    end.

  Lemma RowEta T Ts r : RCons (@RowHead T Ts r) (@RowTail T Ts r) = r.
    refine match r with
             | RCons _ _ v r' => _
           end.
    reflexivity.
  Qed.

  Fixpoint RowApp rt1 (r1 : Row rt1) rt2 (r2 : Row rt2)
  : Row (rt1 ++ rt2)
    := match r1 in (Row r) return (Row (r ++ rt2)) with
         | RNil => r2
         | RCons _ _ a r1s => RCons a (RowApp r1s r2)
       end.

  (** Lift [Column]s to concatenations of row types *)
  Fixpoint Column_RowApp_Left (rt1 rt2 : RowType) T (c : Column T rt1)
  : Column T (rt1 ++ rt2)
    := match c in (Column _ r) return (Column T (r ++ rt2)) with
         | CFirst Ts => CFirst T (Ts ++ rt2)
         | CNext T' Ts c0 => CNext T' (@Column_RowApp_Left Ts rt2 T c0)
       end.

  Fixpoint Column_RowApp_Right (rt1 rt2 : RowType) T {struct rt1}
  : Column T rt2 -> Column T (rt1 ++ rt2)
    := match rt1 as l return (Column T rt2 -> Column T (l ++ rt2)) with
         | nil => fun x : Column T rt2 => x
         | T0 :: rt3 => fun c : Column T rt2 => CNext T0 (@Column_RowApp_Right rt3 rt2 T c)
       end.

  Fixpoint getColumn T R (c : Column T R) : Row R -> T :=
    match c with
      | CFirst _ => fun r => RowHead r
      | CNext _ _ c' => fun r => getColumn c' (RowTail r)
    end.

  Definition DatabaseInstanceHead R Rs (d : DatabaseInstance (R :: Rs)) : Table R :=
    match d with
      | DCons _ _ r _ => r
    end.

  Definition DatabaseInstanceTail R Rs (d : DatabaseInstance (R :: Rs)) : DatabaseInstance Rs :=
    match d with
      | DCons _ _ _ d' => d'
    end.

  Fixpoint getTable R Rs (tn : TableName R Rs) : DatabaseInstance Rs -> Table R :=
    match tn with
      | TFirst _ => fun d => DatabaseInstanceHead d
      | TNext _ _ tn' => fun d => getTable tn' (DatabaseInstanceTail d)
    end.

  (** A [ColumnList] on an [r : RowType] is a list of columns in [r];
    the types of these columns gives a new [RowType], which must be
    passed as the second parameter to this type. *)
  Inductive ColumnList : RowType -> RowType -> Type :=
  | CNil : forall fromTs, ColumnList fromTs nil
  | CCons : forall T fromTs toTs, Column T fromTs -> ColumnList fromTs toTs -> ColumnList fromTs (T :: toTs).

  Lemma RNil_unique : forall x : Row nil, x = RNil.
    intros; refine (match x in Row Ts return match Ts return Row Ts -> Prop with
                                               | nil => fun x => x = RNil
                                               | _ => fun _ => True
                                             end x with
                      | RNil => eq_refl
                      | _ => I
                    end).
  Qed.

  Lemma RowNil_unique : forall x y : Row nil, x = y.
    intros x y.
    rewrite (RNil_unique x).
    rewrite (RNil_unique y).
    reflexivity.
  Qed.

  Local Hint Immediate RowNil_unique.

  (** Equality of rows is decidable if equality of all constituent types
    is decidable. *)
  Inductive RowTypeDecidable (P : forall T, relation T) `(H : forall T, Equivalence (P T))
  : RowType -> Type :=
  | RTDecNil : RowTypeDecidable P H nil
  | RTDecCons : forall T Ts, (forall t0 t1 : T,
                                {P T t0 t1} + {~P T t0 t1})
                             -> RowTypeDecidable P H Ts
                             -> RowTypeDecidable P H (T :: Ts).

  Definition RowTypeDecHead P H T Ts (r : RowTypeDecidable P H (T :: Ts))
  : forall t0 t1 : T, {P T t0 t1} + {~ P T t0 t1} :=
    match r with
      | RTDecCons _ _ v _ => v
    end.

  Definition RowTypeDecTail P H T Ts (r : RowTypeDecidable P H (T :: Ts))
  : RowTypeDecidable P H Ts :=
    match r with
      | RTDecCons _ _ _ r' => r'
    end.

  Lemma RowTypeDecidableEta P H T Ts (r : RowTypeDecidable P H (T :: Ts))
  : RTDecCons (@RowTypeDecHead P H T Ts r) (@RowTypeDecTail P H T Ts r) = r.
    refine match r with
             | RTDecCons _ _ v r' => _
           end.
    reflexivity.
  Qed.

  Lemma Cons_not_eq
  : forall T Ts (h1 : T) (t1 : Row Ts) h2 t2,
      (h1 <> h2 \/ t1 <> t2)
      -> RCons h1 t1 <> RCons h2 t2.
    intuition;
    match goal with
      | [ H : RCons _ _ = RCons _ _ |- _ ] => (apply (f_equal (@RowHead _ _)) in H; tauto)
                                                || (apply (f_equal (@RowTail _ _)) in H; tauto)
    end.
  Qed.

  Hint Resolve Cons_not_eq.

  Fixpoint Row_eq Ts
  : RowTypeDecidable (fun T => @eq T) (@eq_equivalence) Ts -> forall r1 r2 : Row Ts, {r1 = r2} + {r1 <> r2}.
  Proof.
    refine match Ts return RowTypeDecidable _ _ Ts -> forall r1 r2 : Row Ts, {r1 = r2} + {r1 <> r2} with
             | nil => fun _ _ _ => left _
             | _ :: Ts' => fun D r1 r2 =>
                             if (RowTypeDecHead D) (RowHead r1) (RowHead r2)
                             then if Row_eq _ (RowTypeDecTail D) (RowTail r1) (RowTail r2)
                                  then left _
                                  else right _
                             else right _
           end;
    clear Row_eq;
    abstract (repeat match goal with
                       | [ r : Row nil |- _ ] => (generalize (RNil_unique r); intro; subst)
                       | [ r : Row (_ :: _) |- _ ] => progress (rewrite <- (RowEta r) in *; simpl in *; idtac)
                     end; auto; congruence).
  Defined.

  (** If a type has decidable equality, so does [In] *)
  Fixpoint In_dec A (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A)
  : forall x, {In x l} + {~In x l}.
  Proof.
    refine match l with
             | nil
               => fun _
                  => right _
             | b :: m
               => fun x
                  => match eq_dec b x with
                       | left H
                         => left _
                       | right not_eq
                         => match In_dec _ eq_dec m x with
                              | left H => left _
                              | right not_in => right _
                            end
                     end
           end;
    clear In_dec eq_dec;
    abstract firstorder.
  Defined.

  (** Takes in a list, and returns the list of unique elements in that list *)
  Fixpoint unique_from A (eq_dec : forall x y : A, {x = y} + {x <> y})
           (l : list A) : list A :=
    match l with
      | nil => nil
      | b :: t => if In_dec eq_dec t b
                  then unique_from eq_dec t
                  else b :: unique_from eq_dec t
    end.
  Arguments unique_from _ _ !l / .

  Lemma unique_no_change_in A (l : list A) eq_dec
  : forall x, In x l <-> In x (@unique_from  A eq_dec l).
    intro x; split; intro;
    induction l;
    repeat match goal with
             | _ => easy
             | _ => solve [ intuition ]
             | _ => solve [ exfalso; intuition ]
             | [ H : _ \/ _ |- _ ] => destruct H
             | _ => progress (simpl in *; subst)
             | [ H : appcontext[match ?E with _ => _ end] |- _ ] => destruct E
             | [ |- appcontext[match ?E with _ => _ end] ] => destruct E
           end.
  Qed.

  Lemma unique_from_NoDup A (l : list A) eq_dec
  : NoDup l -> @unique_from A eq_dec l = l.
    intro H.
    induction H; [ reflexivity | ].
    simpl.
    match goal with
      | [ |- appcontext[match ?E with _ => _ end] ] => destruct E
    end;
      try solve [ exfalso; abstract intuition ].
    f_equal.
    assumption.
  Qed.

  Lemma NoDup_unique_from A (l : list A) eq_dec
  : NoDup (@unique_from A eq_dec l).
    induction l; [ simpl; constructor | ].
    repeat match goal with
             | _ => progress simpl in *
             | _ => assumption
             | [ |- appcontext[match ?E with _ => _ end] ] => destruct E
             | _ => intro
             | _ => progress intuition
             | _ => constructor
             | [ H : _ |- _ ] => apply <- unique_no_change_in in H
           end.
  Qed.
End Database.
