Require Import Common.

Set Implicit Arguments.

Lemma sigT_eta : forall A (P : A -> Type) (x : sigT P),
  x = existT _ (projT1 x) (projT2 x).
  destruct x; reflexivity.
Qed.

Lemma sigT2_eta : forall A (P Q : A -> Type) (x : sigT2 P Q),
  x = existT2 _ _ (projT1 x) (projT2 x) (projT3 x).
  destruct x; reflexivity.
Qed.

Lemma sig_eta : forall A (P : A -> Prop) (x : sig P),
  x = exist _ (proj1_sig x) (proj2_sig x).
  destruct x; reflexivity.
Qed.

Lemma sig2_eta : forall A (P Q : A -> Prop) (x : sig2 P Q),
  x = exist2 _ _ (proj1_sig x) (proj2_sig x) (proj3_sig x).
  destruct x; reflexivity.
Qed.

(* Silly predicate that we can use to get Ltac to help us manipulate terms *)
Definition focus A (_ : A) := True.

(* This definition does most of the work of simplification. *)
Ltac simpl_definition_by_tac_and_exact defn tac :=
  assert (Hf : focus defn) by constructor;
    try unfold defn in Hf; try tac; simpl in Hf;
      repeat match type of Hf with
               | context[match ?E with existT2 _ _ _ => _ end] => rewrite (sigT2_eta E) in Hf; simpl in Hf
               | context[match ?E with exist2 _ _ _ => _ end] => rewrite (sig2_eta E) in Hf; simpl in Hf
               | context[match ?E with existT _ _ => _ end] => rewrite (sigT_eta E) in Hf; simpl in Hf
               | context[match ?E with exist _ _ => _ end] => rewrite (sig_eta E) in Hf; simpl in Hf
             end;
      match type of Hf with
        | focus ?V => exact V
      end.

Ltac simpl_definition_by_exact defn := simpl_definition_by_tac_and_exact defn idtac.

(** To simplify something defined as [Ident'] of type [IdentT] into [Ident], do something like:
Definition Ident'' : IdentT.
  simpl_definition_by_exact Ident'.
Defined.

(* Then we clean up a bit with reduction. *)
Definition Ident := Eval cbv beta iota zeta delta [Ident''] in Ident''.
*)
