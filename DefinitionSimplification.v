Set Implicit Arguments.

Lemma sigT_eta : forall A (P : A -> Type) (x : sigT P),
  x = existT _ (projT1 x) (projT2 x).
  destruct x; reflexivity.
Qed.

Lemma sig_eta : forall A (P : A -> Prop) (x : sig P),
  x = exist _ (proj1_sig x) (proj2_sig x).
  destruct x; reflexivity.
Qed.

(* Silly predicate that we can use to get Ltac to help us manipulate terms *)
Definition focus A (_ : A) := True.

(* This definition does most of the work of simplification. *)
Ltac simpl_definition_by_exact defn :=
  assert (Hf : focus defn) by constructor;
    try unfold defn in Hf; simpl in Hf;
      repeat match type of Hf with
               | context[match ?E with existT _ _ => _ end] => rewrite (sigT_eta E) in Hf; simpl in Hf
               | context[match ?E with exist _ _ => _ end] => rewrite (sig_eta E) in Hf; simpl in Hf
             end;
      match type of Hf with
        | focus ?V => exact V
      end.

(** To simplify something defined as [Ident'] of type [IdentT] into [Ident], do something like:
Definition Ident'' : IdentT.
  simpl_definition_by_exact Ident'.
Defined.

(* Then we clean up a bit with reduction. *)
Definition Ident := Eval cbv beta iota zeta delta [Ident''] in Ident''.
*)
