Require Import Common.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

(* Silly predicate that we can use to get Ltac to help us manipulate terms *)
Definition focus A (_ : A) := True.

(* This definition does most of the work of simplification. *)
Ltac simpl_definition_by_tac_and_exact defn tac :=
  assert (Hf : focus defn) by constructor;
    let defnH := head defn in try unfold defnH in Hf; try tac; simpl in Hf;
      rewrite_eta_in Hf;
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
