Require Import Setoid Program.

Set Implicit Arguments.

Section EquivalenceRelation.
  Variable Object : Type.
  Variable Relation : Object -> Object -> Type.
  Variable RelationsEquivalent' : forall o1 o2, Relation o1 o2 -> Relation o1 o2 -> Prop.

  Record EquivalenceRelation := {
    RelationsEquivalent :> forall o1 o2, Relation_Definitions.relation (Relation o1 o2) := RelationsEquivalent';
    Reflexive : forall o1 o2 (r : Relation o1 o2),
      RelationsEquivalent r r;
    Symmetric : forall o1 o2 (r1 r2 : Relation o1 o2),
      RelationsEquivalent r1 r2 -> RelationsEquivalent r2 r1;
    Transitive : forall o1 o2 (r1 r2 r3 : Relation o1 o2),
      RelationsEquivalent r1 r2 -> RelationsEquivalent r2 r3 -> RelationsEquivalent r1 r3
  }.

  Definition relations_equivalence_equivalent (R : EquivalenceRelation) : Prop :=
    @RelationsEquivalent' = @RelationsEquivalent R.
End EquivalenceRelation.

Implicit Arguments EquivalenceRelation [Object Relation].
Implicit Arguments RelationsEquivalent [Object Relation].
Implicit Arguments Reflexive [Object Relation RelationsEquivalent'].
Implicit Arguments Symmetric [Object Relation RelationsEquivalent'].
Implicit Arguments Transitive [Object Relation RelationsEquivalent'].

Add Parametric Relation O R o1 o2 RE ER : _ (@RelationsEquivalent O R RE ER o1 o2)
  reflexivity proved by (Reflexive _ _ _)
  symmetry proved by (Symmetric _ _ _)
  transitivity proved by (Transitive _ _ _)
    as relations_eq.

Hint Unfold RelationsEquivalent.

(*Theorem RelationsEquivalent_def : forall (Object : Type) (Relation : Object -> Object -> Type)
  (RelationsEquivalent' : forall o1 o2 : Object,
    Relation o1 o2 -> Relation o1 o2 -> Prop)
  (H : EquivalenceRelation RelationsEquivalent'),
  RelationsEquivalent RelationsEquivalent' H = RelationsEquivalent'.
  reflexivity.
Qed.

Hint Rewrite RelationsEquivalent_def.*)
