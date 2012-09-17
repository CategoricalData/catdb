Require Export SpecializedCategory.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Record Category := {
  CObject : Type;

  UnderlyingCategory :> @SpecializedCategory CObject
}.

Definition GeneralizeCategory `(C : @SpecializedCategory obj) : Category.
  refine {| CObject := C.(Object) |}; auto.
Defined.

Coercion GeneralizeCategory : SpecializedCategory >-> Category.

Record SmallCategory := {
  SObject : Set;

  SUnderlyingCategory :> @SmallSpecializedCategory SObject
}.

Definition GeneralizeSmallCategory `(C : @SmallSpecializedCategory obj) : SmallCategory.
  refine {| SObject := obj |}; auto.
Defined.

Coercion GeneralizeSmallCategory : SmallSpecializedCategory >-> SmallCategory.

Record LocallySmallCategory := {
  LSObject : Type;

  LSUnderlyingCategory :> @LocallySmallSpecializedCategory LSObject
}.

Definition GeneralizeLocallySmallCategory `(C : @LocallySmallSpecializedCategory obj) : LocallySmallCategory.
  refine {| LSObject := obj |}; auto.
Defined.

Coercion GeneralizeLocallySmallCategory : LocallySmallSpecializedCategory >-> LocallySmallCategory.

Bind Scope category_scope with Category.
Bind Scope category_scope with SmallCategory.
Bind Scope category_scope with LocallySmallCategory.



(** * The saturation prover: up to some bound on number of steps, consider all ways to extend equivalences with pre- or post-composition. *)

(** The main tactic, which tries a single round of making deductions from hypotheses that exist at the start of the round.
    Only variables in the goal are chosen to compose. *)

Ltac saturate := repeat match goal with
                          | [ H : @eq (Morphism _ _ _) ?M ?N |- _ ] =>
                            let tryIt G :=
                              match goal with
                                | [ _ : G |- _ ] => fail 1
                                | [ |- context[G] ] => fail 1
                                | _ => let H' := fresh "H" in assert (H' : G) by eauto; generalize dependent H'
                              end in
                              repeat match goal with
                                       | [ m : Morphism _ _ _ |- _ ] =>
                                         tryIt (Compose M m = Compose N m)
                                       | [ m : Morphism _ _ _ |- _ ] =>
                                         tryIt (Compose m M = Compose m N)
                                     end; generalize dependent H
                        end; intros; autorewrite with core in *.

(** To be sure that all relevant terms are represented as variables, we use this tactic to create variables for
    all non-[Compose] subterms of a morphism expression. *)

Ltac extractMorphisms G :=
  match G with
    | Compose ?G1 ?G2 =>
      extractMorphisms G1;
      extractMorphisms G2
    | _ =>
      match goal with
        | [ x := G |- _ ] => idtac
        | [ x : _ |- _ ] =>
          match x with
            | G => idtac
          end
        | _ => pose G
      end
  end.

(** This tactic calls the above on two morphisms being compared for equivalence in the goal. *)

Ltac createVariables :=
  match goal with
    | [ |- @eq (Morphism _ _ _) ?X ?Y ] =>
      extractMorphisms X;
      extractMorphisms Y
  end.

(** After we are done with our variable-related hijinks, we can clean up by removing the new variables,
    replacing them by their definitions. *)

Ltac removeVariables :=
  repeat match goal with
           | [ x := _ |- _ ] => subst x
         end.

(** This notation ties it all together, taking as argument the number of [saturate] rounds to run. *)

Tactic Notation "morphisms" integer(numSaturations) :=
  t; createVariables; do numSaturations saturate; removeVariables; eauto 3.
