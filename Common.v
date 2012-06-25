Require Import Program.
Set Implicit Arguments.

Ltac unique_pose defn :=
  let T := type of defn in
    match goal with
      | [ H : T |- _ ] => fail 1
      | _ => let H := fresh in assert (H := defn)
    end.

Ltac t' := repeat progress (simpl; intros; try split; trivial).
Ltac t'_long := repeat progress (simpl; intuition).

Ltac t_con_with con tac := tac;
  repeat (match goal with
            | [ H : context[con] |- _ ] => rewrite H
            | _ => progress autorewrite with core in *
          end; tac).

Ltac t_con_rev_with con tac := tac;
  repeat (match goal with
            | [ H : context[con] |- _ ] => rewrite <- H
            | _ => progress autorewrite with core in *
          end; tac).

Ltac t_with tac := t_con_with @eq tac.

Ltac t_rev_with tac := t_con_rev_with @eq tac.

Ltac t_con con := t_con_with con t'; t_con_with con t'_long.
Ltac t_con_rev con := t_con_rev_with con t'; t_con_rev_with con t'_long.

Ltac t := t_with t'; t_with t'_long.
Ltac t_rev := t_rev_with t'; t_rev_with t'_long.

Ltac simpl_transitivity :=
  try solve [ match goal with
                | [ _ : ?Rel ?a ?b, _ : ?Rel ?b ?c |- ?Rel ?a ?c ] => transitivity b; assumption
              end ].

Ltac eq2eq_refl :=
  repeat match goal with
           | [ H : _ = ?a |- _ ] => assert (H = eq_refl _) by (apply proof_irrelevance); subst
         end.

Ltac destruct_type T :=
  repeat match goal with
           | [ H : context[T] |- _ ] => destruct H
         end.

Ltac destruct_hypotheses :=
  repeat match goal with
           | [ H : ex _ |- _ ] => destruct H
           | [ H : and _ _ |- _ ] => destruct H
           | [ H : prod _ _ |- _ ] => destruct H
         end.

Ltac specialized_assumption tac := tac;
  match goal with
    | [ x : ?T, H : forall _ : ?T, _ |- _ ] => specialize (H x); specialized_assumption tac
    | _ => assumption
  end.

Ltac try_rewrite rew_H tac :=
  (repeat (rewrite rew_H); tac) ||
    (repeat (rewrite <- rew_H); tac).

Ltac try_rewrite_repeat rew_H tac :=
  (repeat (rewrite rew_H; tac)) ||
    (repeat (rewrite <- rew_H; tac)).

Ltac solve_repeat_rewrite rew_H tac :=
  solve [ repeat (rewrite rew_H; tac) ] ||
    solve [ repeat (rewrite <- rew_H; tac) ].

Ltac simpl_exist :=
  match goal with
    | [ |- exist _ ?x1 ?p1 = exist _ ?x2 ?p2 ] => generalize p1; generalize p2; cut (x1 = x2);
      try solve [ let H := fresh in intro H; rewrite H; intros ? ?; apply f_equal; apply proof_irrelevance ]
  end.

Ltac split_iff :=
  repeat match goal with
           | [ H : context p [iff] |- _ ] =>
             let H0 := context p[fun a b => a -> b] in let H0' := eval simpl in H0 in assert H0' by (apply H);
               let H1 := context p[fun a b => b -> a] in let H1' := eval simpl in H1 in assert H1' by (apply H);
                 clear H
         end.

Ltac clear_hyp_of_type type :=
  repeat match goal with
           | [ H : type |- _ ] => clear H
         end.

(* If [conVar] is not mentioned in any hypothesis other than [hyp],
   nor in the goal, then clear any hypothesis of the same type as [hyp] *)
Ltac clear_hyp_unless_context hyp conVar :=
  let hypT := type of hyp in
    match goal with
      | [ H0 : hypT, H : context[conVar] |- _ ] => fail 1 (* there is a hypotheses distinct from [hyp] which mentions [conVar] *)
      | [ |- context[conVar] ] => fail 1
      | _ => clear_hyp_of_type hypT
    end.

(* equivalent to [idtac] if [subexpr] appears nowhere in [expr],
   equivalent to [fail] otherwise *)
Ltac FreeQ expr subexpr :=
  match expr with
    | appcontext[subexpr] => fail 1
    | _ => idtac
  end.

Ltac subst_mor x :=
  match goal with
    | [ H : ?Rel ?a x |- _ ] => FreeQ a x; rewrite <- H in *;
      try clear_hyp_unless_context H x
    | [ H : ?Rel x ?a |- _ ] => FreeQ a x; rewrite H in *;
      try clear_hyp_unless_context H x
  end.

Ltac repeat_subst_mor_of_type type :=
  repeat match goal with
           | [ m : context[type] |- _ ] => subst_mor m; try clear m
         end.

Lemma fg_equal A B (f g : A -> B) : f = g -> forall x, f x = g x.
  intros; repeat subst; reflexivity.
Qed.

Ltac fg_equal :=
  repeat match goal with
           | [ H : _ |- _ ] => let H' := fresh in assert (H' := fg_equal H); clear H; simpl in H'
         end.

Ltac intro_proj2_sig_from_goal :=
  repeat match goal with
           | [ |- appcontext[proj1_sig ?x] ] => unique_pose (proj2_sig x)
         end; simpl in *.

Ltac recr_destruct_with tac H :=
  let H0 := fresh in let H1 := fresh in
    (tac H; try reflexivity; try clear H) ||
      (destruct H as [ H0 H1 ];
        simpl in H0, H1;
          recr_destruct_with tac H0 || recr_destruct_with tac H1;
            try clear H0; try clear H1).

Ltac do_rewrite H := rewrite H.
Ltac do_rewrite_rev H := rewrite <- H.
Ltac recr_destruct_rewrite H := recr_destruct_with do_rewrite H.
Ltac recr_destruct_rewrite_rev H := recr_destruct_with do_rewrite_rev H.


Ltac use_proj2_sig_with tac :=
  repeat match goal with
           | [ |- appcontext[proj1_sig ?x] ] =>
             match x with
               | context[proj1_sig] => fail 1
               | _ => let H := fresh in assert (H := proj2_sig x); simpl in H;
                 tac H; try clear H
             end
         end.

Ltac rewrite_proj2_sig := use_proj2_sig_with recr_destruct_rewrite.
Ltac rewrite_rev_proj2_sig := use_proj2_sig_with recr_destruct_rewrite_rev.
