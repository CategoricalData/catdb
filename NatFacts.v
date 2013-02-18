Require Import Omega.

Set Implicit Arguments.

Section le_rel.
  Polymorphic Lemma le_refl n : n <= n. trivial. Qed.

  Polymorphic Lemma le_trans : forall n m p, n <= m -> m <= p -> n <= p.
    intuition.
  Qed.
End le_rel.

Add Parametric Relation : _ @le
  reflexivity proved by le_refl
  transitivity proved by le_trans
    as le_rel.
