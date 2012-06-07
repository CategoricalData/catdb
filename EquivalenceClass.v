Require Import Ensembles.

Set Implicit Arguments.

Section equiv.
  Variable A : Type.
  Variable value : Type.
  Variable equiv : value -> value -> Prop.

  Hypotheses equiv_refl : forall (v : value), equiv v v.
  Hypothesis equiv_sym : forall (v v' : value),
    equiv v v' -> equiv v' v.
  Hypothesis equiv_trans : forall (v v' v'' : value),
    equiv v v' -> equiv v' v'' -> equiv v v''.

  Hint Immediate equiv_sym.
  Hint Resolve equiv_trans.

  Definition EquivalenceClassOf (v : value) := {v' : value | equiv v v'}.

  Theorem EquivalenceClassOf_trans : forall (v v' : value),
    equiv v v'
    -> EquivalenceClassOf v = EquivalenceClassOf v'.
    unfold EquivalenceClassOf; intros; f_equal.
    apply Extensionality_Ensembles.
    unfold Same_set, Included, In; eauto.
  Qed.
End equiv.
