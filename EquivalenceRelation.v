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
    forall o1 o2, @RelationsEquivalent' o1 o2 = @RelationsEquivalent R o1 o2.

  Inductive GeneralizedRelationsEquivalent (R : EquivalenceRelation) o1 o2 : forall o1' o2', Relation o1 o2 -> Relation o1' o2' -> Prop :=
  | GRE : forall (r1 r2 : Relation o1 o2), R.(RelationsEquivalent) r1 r2 -> GeneralizedRelationsEquivalent R r1 r2.

  Lemma generalized_relations_equivalent_refl (R : EquivalenceRelation) o1 o2 (r : Relation o1 o2) : GeneralizedRelationsEquivalent R r r.
    constructor; apply Reflexive.
  Qed.

  Lemma generalized_relations_equivalent_sym (R : EquivalenceRelation) o1 o2 o1' o2' (r : Relation o1 o2) (r' : Relation o1' o2') :
    GeneralizedRelationsEquivalent R r r' -> GeneralizedRelationsEquivalent R r' r.
    destruct 1; constructor; apply Symmetric; assumption.
  Qed.

  Lemma generalized_relations_equivalent_trans (R : EquivalenceRelation) o1 o2 o1' o2' o1'' o2'' (r : Relation o1 o2) (r' : Relation o1' o2') (r'' : Relation o1'' o2'') :
    GeneralizedRelationsEquivalent R r r' -> GeneralizedRelationsEquivalent R r' r'' -> GeneralizedRelationsEquivalent R r r''.
    repeat (destruct 1); constructor.
    match goal with
      [ 
        H : @RelationsEquivalent _ _ _ ?r ?r',
        H' : @RelationsEquivalent _ _ _ ?r' ?r''
        |- @RelationsEquivalent _ _ _ ?r ?r''
      ] => apply (Transitive H H')
    end.
  Qed.

  Hint Constructors GeneralizedRelationsEquivalent.

  Theorem generalized_relations_equivalent_ne o1 o2 o1' o2' (R : EquivalenceRelation) :
    forall r1 r2, o1 <> o1' \/ o2 <> o2' -> ~@GeneralizedRelationsEquivalent R o1 o2 o1' o2' r1 r2.
    intros r1 r2 H g; inversion g; destruct H; contradiction.
  Qed.

  (* XXX TODO: Come up with better names for the following two theorems. *)
  Theorem generalized_relations_equivalent_eq1 o1 o2 (R : EquivalenceRelation) :
    forall r1 r2, R o1 o2 r1 r2 -> GeneralizedRelationsEquivalent R r1 r2.
    intros r1 r2; constructor; assumption.
  Qed.

  Theorem generalized_relations_equivalent_eq2 o1 o2 (R : EquivalenceRelation) :
    forall r1 r2, GeneralizedRelationsEquivalent R r1 r2 -> R o1 o2 r1 r2.
    intros r1 r2 r; dependent destruction r; assumption.
  Qed.
End EquivalenceRelation.

Implicit Arguments EquivalenceRelation [Object Relation].
Implicit Arguments RelationsEquivalent [Object Relation].
Implicit Arguments Reflexive [Object Relation RelationsEquivalent'].
Implicit Arguments Symmetric [Object Relation RelationsEquivalent'].
Implicit Arguments Transitive [Object Relation RelationsEquivalent'].

Implicit Arguments GeneralizedRelationsEquivalent [Object Relation RelationsEquivalent' o1 o2 o1' o2'].

Add Parametric Relation O R o1 o2 RE ER : _ (@RelationsEquivalent O R RE ER o1 o2)
  reflexivity proved by (Reflexive _ _ _)
  symmetry proved by (Symmetric _ _ _)
  transitivity proved by (Transitive _ _ _)
    as relations_eq.

Hint Unfold RelationsEquivalent.

Hint Resolve generalized_relations_equivalent_sym generalized_relations_equivalent_refl generalized_relations_equivalent_trans.
Hint Resolve generalized_relations_equivalent_eq1.

(*Theorem RelationsEquivalent_def : forall (Object : Type) (Relation : Object -> Object -> Type)
  (RelationsEquivalent' : forall o1 o2 : Object,
    Relation o1 o2 -> Relation o1 o2 -> Prop)
  (H : EquivalenceRelation RelationsEquivalent'),
  RelationsEquivalent RelationsEquivalent' H = RelationsEquivalent'.
  reflexivity.
Qed.

Hint Rewrite RelationsEquivalent_def.*)
