Require Import ProofIrrelevance.

Set Implicit Arguments.

Section sig.
  Definition sigT2_sigT A P Q (x : @sigT2 A P Q) := let (a, h, _) := x in existT _ a h.
  Global Coercion sigT2_sigT : sigT2 >-> sigT.
  Definition projT3 A P Q (x : @sigT2 A P Q) :=
    let (x0, _, h) as x0 return (Q (projT1 x0)) := x in h.

  Definition sig2_sig A P Q (x : @sig2 A P Q) := let (a, h, _) := x in exist _ a h.
  Global Coercion sig2_sig : sig2 >-> sig.
  Definition proj3_sig A P Q (x : @sig2 A P Q) :=
    let (x0, _, h) as x0 return (Q (proj1_sig x0)) := x in h.
End sig.

Tactic Notation "not_tac" tactic(tac) := (tac; fail 1) || idtac.

Tactic Notation "test_tac" tactic(tac) := not_tac (not_tac tac).

Ltac unique_pose defn :=
  let T := type of defn in
    match goal with
      | [ H : T |- _ ] => fail 1
      | _ => let H := fresh in assert (H := defn)
    end.

Ltac unique_pose_with_body defn :=
  match goal with
    | [ H := defn |- _ ] => fail 1
    | _ => pose defn
  end.

Tactic Notation "has_no_body" hyp(H) :=
  not_tac (let H' := fresh in pose H as H'; unfold H in H').

Tactic Notation "has_body" hyp(H) :=
  not_tac (has_no_body H).

Ltac simpl_do tac H :=
  let H' := fresh in pose H as H'; simpl; simpl in H'; tac H'.

Ltac simpl_do_clear tac H :=
  let H' := fresh in pose H as H'; simpl; simpl in H'; tac H'; try clear H'.

Ltac destruct_exists' T := cut T; try (let H := fresh in intro H; exists H).
Ltac destruct_exists :=
  match goal with
    | [ |- @ex ?T _ ] => destruct_exists' T
    | [ |- @sig ?T _ ] => destruct_exists' T
    | [ |- @sigT ?T _ ] => destruct_exists' T
    | [ |- @sig2 ?T _ _ ] => destruct_exists' T
    | [ |- @sigT2 ?T _ _ ] => destruct_exists' T
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

Ltac destruct_all_matches matcher :=
  repeat match goal with
           | [ H : ?T |- _ ] => matcher T; destruct H; simpl in *
         end.

Ltac destruct_type_matcher T HT :=
  match HT with
    | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).

Ltac destruct_hypotheses_matcher HT :=
  let HT' := eval hnf in HT in
    match HT' with
      | ex _ => idtac
      | and _ _ => idtac
      | prod _ _ => idtac
    end.
Ltac destruct_hypotheses := destruct_all_matches destruct_hypotheses_matcher.

Ltac destruct_sig_matcher HT :=
  let HT' := eval hnf in HT in
    match HT' with
      | @sig _ _ => idtac
      | @sigT _ _ => idtac
      | @sig2 _ _ _ => idtac
      | @sigT2 _ _ _ => idtac
    end.
Ltac destruct_sig := destruct_all_matches destruct_sig_matcher.

Ltac destruct_all_hypotheses := destruct_all_matches ltac:(fun HT =>
  destruct_hypotheses_matcher HT || destruct_sig_matcher HT
).

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
  (repeat rewrite rew_H; tac) ||
    (repeat rewrite <- rew_H; tac).

Ltac try_rewrite_by rew_H by_tac tac :=
  (repeat rewrite rew_H by by_tac; tac) ||
    (repeat rewrite <- rew_H by by_tac; tac).

Ltac try_rewrite_repeat rew_H tac :=
  (repeat (rewrite rew_H; tac)) ||
    (repeat (rewrite <- rew_H; tac)).

Ltac solve_repeat_rewrite rew_H tac :=
  solve [ repeat (rewrite rew_H; tac) ] ||
    solve [ repeat (rewrite <- rew_H; tac) ].

Lemma sig_eq A P (s s' : @sig A P) : proj1_sig s = proj1_sig s' -> s = s'.
  destruct s, s'; simpl; intro; subst; f_equal; apply proof_irrelevance.
Qed.

Lemma sig2_eq A P Q (s s' : @sig2 A P Q) : proj1_sig s = proj1_sig s' -> s = s'.
  destruct s, s'; simpl; intro; subst; f_equal; apply proof_irrelevance.
Qed.

Ltac simpl_eq := repeat (
  (
    apply sig_eq ||
      apply sig2_eq ||
        apply injective_projections
  );
  simpl in *
).

Ltac split_in_context ident funl funr :=
  repeat match goal with
           | [ H : context p [ident] |- _ ] =>
             let H0 := context p[funl] in let H0' := eval simpl in H0 in assert H0' by (apply H);
               let H1 := context p[funr] in let H1' := eval simpl in H1 in assert H1' by (apply H);
                 clear H
         end.

Ltac split_iff := split_in_context iff (fun a b : Prop => a -> b) (fun a b : Prop => b -> a).
Ltac split_and := split_in_context and (fun a b : Prop => a) (fun a b : Prop => b).

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

(* So we know the difference betwen the [sigT]s we're using and the [sigT]s others use *)
Inductive Common_sigT (A : Type) (P : A -> Type) : Type :=
    Common_existT : forall x : A, P x -> Common_sigT P.
Definition Common_projT1 (A : Type) (P : A -> Type) (x : @Common_sigT A P) := let (a, _) := x in a.
Definition Common_projT2 (A : Type) (P : A -> Type) (x : @Common_sigT A P) := let (x0, h) as x0 return (P (Common_projT1 x0)) := x in h.

Ltac uncurryT H :=
  match eval simpl in H with
    | forall (x : ?T1) (y : @?T2 x), @?f x y => uncurryT (forall xy : @Common_sigT T1 T2, f (Common_projT1 xy) (Common_projT2 xy))
    | ?H' => H'
  end.

Ltac curryT H :=
  match eval simpl in H with
    | forall xy : @Common_sigT ?T1 ?T2, @?f xy => curryT (forall (x : T1) (y : T2 x), f (@Common_existT T1 T2 x y))
    | ?H' => H'
  end.

Ltac uncurry H := let HT := type of H in
  match eval simpl in HT with
    | forall (x : ?T1) (y : @?T2 x) (z : @?T3 x y), @?f x y z =>
      uncurry (fun xyz => H (Common_projT1 (Common_projT1 xyz)) (Common_projT2 (Common_projT1 xyz)) (Common_projT2 xyz))
    | forall (x : ?T1) (y : @?T2 x), @?f x y => uncurry (fun xy : @Common_sigT T1 T2 => H (Common_projT1 xy) (Common_projT2 xy))
    | ?H' => H
  end.

Ltac curry H := let HT := type of H in
  match eval simpl in HT with
    | forall xy : @Common_sigT ?T1 ?T2, @?f xy => curry (fun (x : T1) (y : T2 x) => H (@Common_existT T1 T2 x y))
    | ?H' => H
  end.

Lemma fg_equal A B (f g : A -> B) : f = g -> forall x, f x = g x.
  intros; repeat subst; reflexivity.
Qed.

Section telescope.
  Inductive telescope :=
  | Base : forall (A : Type) (B : A -> Type), (forall a, B a) -> (forall a, B a) -> telescope
  | Quant : forall A : Type, (A -> telescope) -> telescope.

  Fixpoint telescopeOut (t : telescope) :=
    match t with
      | Base _ _ x y => x = y
      | Quant _ f => forall x, telescopeOut (f x)
    end.

  Fixpoint telescopeOut' (t : telescope) :=
    match t with
      | Base _ _ f g => forall x, f x = g x
      | Quant _ f => forall x, telescopeOut' (f x)
    end.

  Theorem generalized_fg_equal : forall (t : telescope),
    telescopeOut t
    -> telescopeOut' t.
    induction t; simpl; intuition; subst; auto.
  Qed.
End telescope.

Ltac curry_in_Quant H :=
  match eval simpl in H with
    | @Quant (@Common_sigT ?T1 ?T2) (fun xy => @?f xy) => curry_in_Quant (@Quant T1 (fun x => @Quant (T2 x) (fun y => f (@Common_existT T1 T2 x y))))
    | ?H' => H'
  end.

Ltac reifyToTelescope' H := let HT := type of H in let H' := uncurryT HT in
  match H' with
    | @eq ?T ?f ?g => let T' := eval hnf in T in
      match T' with
        | forall x : ?a, @?b x => constr:(@Base a b f g)
      end
    | forall x, @eq (@?T x) (@?f x) (@?g x) => let T' := eval hnf in T in (* XXX does [hnf] even do anything on [(fun _ => _)]?  I want to do [hnf] inside the function, but I don't want to do [compute] *)
      match T' with
        | (fun x => forall y : @?a x, @?b x y) => constr:(Quant (fun x => @Base (a x) (b x) (f x) (g x)))
      end
  end.

Ltac reifyToTelescope H := let t' := reifyToTelescope' H in curry_in_Quant t'.
Ltac fg_equal_in H := let t := reifyToTelescope H in apply (generalized_fg_equal t) in H; simpl in H.

Ltac fg_equal :=
  repeat match goal with
           | [ H : _ |- _ ] => fg_equal_in H
         end.

Lemma f_equal_helper A0 (A B : A0 -> Type) (f : forall a0, A a0 -> B a0) (x y : forall a0, A a0) :
  (forall a0, x a0 = y a0) -> (forall a0, f a0 (x a0) = f a0 (y a0)).
  intros H a0; specialize (H a0); rewrite H; reflexivity.
Qed.

Ltac f_equal_in_r H k := let H' := uncurry H in let H'T := type of H' in
  let k' := (fun v => let v' := curry v in let H := fresh in assert (H := v'); simpl in H) in
    match eval simpl in H'T with
      | @eq ?A ?x ?y => k (fun B (f : A -> B) => @f_equal A B f x y H') k'
      | forall a0 : ?A0, @eq (@?A a0) (@?x a0) (@?y a0)
        => k (fun (B : A0 -> Type) (f : forall a0 : A0, A a0 -> B a0) => @f_equal_helper A0 A B f x y H') k'
    end; clear H.
Ltac f_equal_in f H := f_equal_in_r H ltac:(fun pf k => k (pf _ f)).

Ltac eta_red :=
  repeat match goal with
           | [ H : appcontext[fun x => ?f x] |- _ ] => change (fun x => f x) with f in H
           | [ |- appcontext[fun x => ?f x] ] => change (fun x => f x) with f
         end.

Ltac intro_proj2_sig_from_goal' :=
  repeat match goal with
           | [ |- appcontext[proj1_sig ?x] ] => unique_pose (proj2_sig x)
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

(* rewrite fails if hypotheses depend on one another.  simultaneous rewrite does not *)
Ltac simultaneous_rewrite' E :=
  match type of E with
    | ?X = _ => generalize E; generalize dependent X; intros until 1;
      let H := fresh in intro H at top;
        match type of H with
          ?X' = _ => subst X'
        end
  end.

Ltac simultaneous_rewrite_rev' E :=
  match type of E with
    | _ = ?X => generalize E; generalize dependent X; intros until 1;
      let H := fresh in intro H at top;
        match type of H with
          _ = ?X' => subst X'
        end
  end.

Ltac simultaneous_rewrite E :=
  match type of E with
    | forall x : ?T, _ =>
      let y := fresh in evar (y : T);
        let y' := (eval unfold y in y) in clear y; simultaneous_rewrite (E y')
    | ?T = _ => let H := fresh in
      match goal with
        | [ _ : context[?F] |- _ ] =>
          assert (H : T = F) by reflexivity; clear H
      end; simultaneous_rewrite' E
  end.

Ltac simultaneous_rewrite_rev E :=
  match type of E with
    | forall x : ?T, _ =>
      let y := fresh in evar (y : T);
        let y' := (eval unfold y in y) in clear y; simultaneous_rewrite (E y')
    | _ = ?T => let H := fresh in
      match goal with
        | [ _ : context[?F] |- _ ] =>
          assert (H : T = F) by reflexivity; clear H
      end; simultaneous_rewrite_rev' E
  end.

(* rewrite by convertiblity rather than syntactic equality *)
Ltac conv_rewrite_with rew_tac H :=
  match type of H with
    | ?a = _ => match goal with
                  | [ |- appcontext[?a'] ] => change a' with a; rew_tac H
                end
  end.
Ltac conv_rewrite_rev_with rew_tac H :=
  match type of H with
    | _ = ?a => match goal with
                  | [ |- appcontext[?a'] ] => change a' with a; rew_tac H
                end
  end.

Ltac conv_rewrite H := conv_rewrite_with ltac:(fun h => rewrite h) H.
Ltac conv_rewrite_rev H := conv_rewrite_rev_with ltac:(fun h => rewrite <- h) H.
Ltac conv_repeat_rewrite H := repeat conv_rewrite_with ltac:(fun h => repeat rewrite h) H.
Ltac conv_repeat_rewrite_rev H := repeat conv_rewrite_rev_with ltac:(fun h => repeat rewrite <- h) H.

Ltac rewrite_by_context ctx H :=
  match type of H with
    | ?x = ?y => let ctx' := context ctx[x] in let ctx'' := context ctx[y] in
      cut ctx'; [ let H' := fresh in intro H'; simpl in H' |- *; exact H' | ];
        cut ctx''; [ let H' := fresh in intro H'; etransitivity; try apply H'; rewrite H; reflexivity
          |
        ]
  end.

Ltac rewrite_rev_by_context ctx H :=
  match type of H with
    | ?x = ?y => let ctx' := context ctx[y] in let ctx'' := context ctx[x] in
      cut ctx'; [ let H' := fresh in intro H'; simpl in H' |- *; exact H' | ];
        cut ctx''; [ let H' := fresh in intro H'; etransitivity; try apply H'; rewrite <- H; reflexivity
          |
        ]
  end.

Section unit.
  Lemma unit_singleton (u : unit) : u = tt.
    case u; reflexivity.
  Qed.

  Lemma unit_eq (u u' : unit) : u = u'.
    case u; case u'; reflexivity.
  Qed.

  Lemma Empty_set_eq (a b : Empty_set) : a = b.
    destruct a.
  Qed.
End unit.

Hint Rewrite unit_singleton.
Hint Extern 0 (@eq unit _ _) => apply unit_eq.
Hint Extern 0 unit => constructor.
Hint Extern 0 (@eq Empty_set _ _) => apply Empty_set_eq.
