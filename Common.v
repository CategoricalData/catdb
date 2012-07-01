Require Import ProofIrrelevance.

Set Implicit Arguments.

Ltac not_tac tac := (tac; fail 1) || idtac.

Ltac unique_pose defn :=
  let T := type of defn in
    match goal with
      | [ H : T |- _ ] => fail 1
      | _ => let H := fresh in assert (H := defn)
    end.

Ltac simpl_do tac H :=
  let H' := fresh in pose H as H'; simpl; simpl in H'; tac H'.

Ltac simpl_do_clear tac H :=
  let H' := fresh in pose H as H'; simpl; simpl in H'; tac H'; try clear H'.

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

Ltac destruct_sig :=
  repeat match goal with
           | [ H : @sig _ _ |- _ ] => destruct H
           | [ H : @sigT _ _ |- _ ] => destruct H
           | [ H : @sig2 _ _ _ |- _ ] => destruct H
           | [ H : @sigT2 _ _ _ |- _ ] => destruct H
         end.

Ltac specialized_assumption tac := tac;
  match goal with
    | [ x : ?T, H : forall _ : ?T, _ |- _ ] => specialize (H x); specialized_assumption tac
    | _ => assumption
  end.

Ltac specialize_uniquely :=
  repeat match goal with
           | [ x : ?T, y : ?T, H : _ |- _ ] => fail 1
           | [ x : ?T, H : _ |- _ ] => specialize (H x)
         end.

Ltac specialize_all_ways_forall :=
  repeat match goal with
           | [ x : ?T, H : forall _ : ?T, _ |- _ ] => unique_pose (H x)
         end.

Ltac specialize_all_ways :=
  repeat match goal with
           | [ x : ?T, H : _ |- _ ] => unique_pose (H x)
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

Ltac recur_clear_context con :=
  repeat match goal with
           | [ H : appcontext[con] |- _ ] =>
             recur_clear_context H; try clear H
           | [ H := appcontext[con] |- _ ] =>
             recur_clear_context H; try clear H
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

Ltac intro_projT2_from_goal :=
  repeat match goal with
           | [ |- appcontext[projT1 ?x] ] => unique_pose (projT2 x)
         end; simpl in *.

Ltac intro_proj2_sig :=
  repeat match goal with
           | [ |- appcontext[proj1_sig ?x] ] => unique_pose (proj2_sig x)
           | [ H : appcontext[proj1_sig ?x] |- _ ] => unique_pose (proj2_sig x)
           | [ H := appcontext[proj1_sig ?x] |- _ ] => unique_pose (proj2_sig x)
         end; simpl in *.

Ltac intro_projT2 :=
  repeat match goal with
           | [ |- appcontext[projT1 ?x] ] => unique_pose (projT2 x)
           | [ H : appcontext[projT1 ?x] |- _ ] => unique_pose (projT2 x)
           | [ H := appcontext[projT1 ?x] |- _ ] => unique_pose (projT2 x)
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
               | _ => simpl_do_clear tac (proj2_sig x)
             end
         end.

Ltac rewrite_proj2_sig := use_proj2_sig_with recr_destruct_rewrite.
Ltac rewrite_rev_proj2_sig := use_proj2_sig_with recr_destruct_rewrite_rev.

Definition is_unique (A : Type) (x : A) := forall x' : A, x' = x.
Implicit Arguments is_unique [A].

Ltac rewrite_unique :=
  match goal with
    | [ H : is_unique _ |- _ ] => unfold is_unique in H; rewrite H || rewrite <- H; reflexivity
  end.

Ltac generalize_is_unique_hyp H T :=
  assert (forall a b : T, a = b) by (intros; etransitivity; apply H || symmetry; apply H); clear H.

Ltac generalize_is_unique :=
  repeat match goal with
           | [ H : @is_unique ?T _ |- _ ] => generalize_is_unique_hyp H T
         end.

Ltac intro_fresh_unique :=
  repeat match goal with
           | [ H : @is_unique ?T ?x |- _ ] => let x' := fresh in assert (x' := x); rewrite <- (H x') in *; generalize_is_unique_hyp H T
         end.

Lemma eq_exist T (P : T -> Prop) (a b : { x | P x }) : proj1_sig a = proj1_sig b -> a = b.
  destruct a, b; simpl in *; intro; repeat subst; f_equal; apply proof_irrelevance.
Qed.
