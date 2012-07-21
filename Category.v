Require Import Setoid.
Require Export SpecializedCategory.
Require Import Common.

Set Implicit Arguments.

Class Composable (obj : Type) (mor : obj -> obj -> Type) := {
  Morphism := mor;

  Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d';

  Associativity : forall o1 o2 o3 o4 (m1 : Morphism o1 o2) (m2 : Morphism o2 o3) (m3 : Morphism o3 o4),
    Compose m3 (Compose m2 m1) = Compose (Compose m3 m2) m1
}.

Arguments Compose {obj mor Composable} {s d d'} _ _.

Infix "o" := Compose (at level 40, left associativity) : morphism_scope.
Infix "○" := Compose (at level 40, left associativity) : morphism_scope. (* Unicode Character 'WHITE CIRCLE' (U+25CB) *)

Delimit Scope morphism_scope with morphism.

Local Open Scope morphism_scope.

(** * Version of [Associativity] that avoids going off into the weeds in the presence of unification variables *)

Definition NoEvar T (_ : T) := True.

Lemma AssociativityNoEvar `(C : Composable) : forall o1 o2 o3 o4 (m1 : Morphism o1 o2)
  (m2 : Morphism o2 o3) (m3 : Morphism o3 o4),
  NoEvar (m1, m2) \/ NoEvar (m2, m3) \/ NoEvar (m1, m3)
  -> m3 o (m2 o m1) = (m3 o m2) o m1.
  intros; apply Associativity.
Qed.

Ltac noEvar := match goal with
                 | [ |- context[NoEvar ?X] ] => (has_evar X; fail 1) ||
                   cut (NoEvar X); [ intro; tauto | constructor ]
               end.

Hint Rewrite @AssociativityNoEvar using noEvar.

Section foo.
  Context `{C : Composable}.
  Goal forall h i j k l m n (a : Morphism m n) (b : Morphism l m) (c : Morphism k l) (d : Morphism j k) (e : Morphism i j) (f : Morphism h i) g, a o b o c o d o e o f = g.
    intros.
    repeat rewrite AssociativityNoEvar by noEvar.
    Check 1.
SearchAbout (_ + _ + _).
Lemma nat_assoc a b c : (a + b) + c = a + (b + c).
  induction a; simpl; try reflexivity.
  rewrite IHa; reflexivity.
Qed.

  Goal forall (a b c d e f g : nat), a + b + c + d + e + f = g.

    Ltac stepAssociativity' n := rewrite nat_assoc at n.
    Tactic Notation "stepAssociativity" integer(n) :=
      rewrite nat_assoc at n; try stepAssociativity (S n).
    stepAssociativity' 1.
    let n := constr:(1) in rewrite <- AssociativityNoEvar at n by noEvar.
    stepAssociativity' 1.

    stepAssociativity' 1.
      first [ stepAssociativity 1 | stepAssociativity (S n) ].
      |
        rewrite <- AssociativityNoEvar at n by noEvar;
    rewrite <- AssociativityNoEvar at 1 by noEvar.

Ltac try_associativity_quick tac := try_rewrite @Associativity tac.
Ltac try_associativity tac := try_rewrite_by @AssociativityNoEvar ltac:(idtac; noEvar) tac.

Section AssociativityComposition.
  Context `{C : Composable}.

  Lemma compose4associativity_helper o0 o1 o2 o3 o4
    (a : Morphism o3 o4) (b : Morphism o2 o3)
    (c : Morphism o1 o2) (d : Morphism o0 o1) :
    a o b o c o d = (a o b) o (c o d).
    repeat rewrite Associativity; reflexivity.
  Qed.
End AssociativityComposition.

Ltac compose4associativity' a b c d := transitivity ((a o b) o (c o d)); try solve [ apply compose4associativity_helper ].
Ltac compose4associativity :=
  match goal with
    | [ |- (?a o ?b) o (?c o ?d) = _ ] => compose4associativity' a b c d
    | [ |- _ = (?a o ?b) o (?c o ?d) ] => compose4associativity' a b c d
  end.


Section morphisms.
  Context `{C : Composable}.
  (* Quoting Wikipedia,
     In category theory, an epimorphism (also called an epic
     morphism or, colloquially, an epi) is a morphism [f : X -> Y]
     which is right-cancellative in the sense that, for all
     morphisms [g, g' : Y -> Z],
     [g ○ f = g' ○ f -> g = g']

     Epimorphisms are analogues of surjective functions, but they
     are not exactly the same. The dual of an epimorphism is a
     monomorphism (i.e. an epimorphism in a category [C] is a
     monomorphism in the dual category [OppositeCategory C]).
     *)
  Definition Epimorphism x y (m : Morphism x y) : Prop :=
    forall z (m1 m2 : Morphism y z), m1 o m = m2 o m ->
      m1 = m2.
  Definition Monomorphism x y (m : Morphism x y) : Prop :=
    forall z (m1 m2 : Morphism z x), m o m1 = m o m2 ->
      m1 = m2.
End morphisms.

Arguments Epimorphism {obj mor C} [x y] m.
Arguments Monomorphism {obj mor C} [x y] m.

Class HasIdentity `(Composable) := {
  Identity : forall a, Morphism a a;

  LeftIdentity : forall a b (f : Morphism a b),  (Identity b) o f = f;
  RightIdentity : forall a b (f : Morphism a b), f o (Identity a) = f
}.

Hint Rewrite @LeftIdentity @RightIdentity.

Section identity.
  Context `{C : Composable}.
  Context {H : HasIdentity C}.

  (* [m'] is the inverse of [m] if both compositions are
     equivalent to the relevant identity morphisms. *)
  (* [Definitions] don't get sort-polymorphism :-(  *)
  (*Definition InverseOf' s d (m : mor s d) (m' : mor d s) : Prop :=
    C.(Compose') _ _ _ m' m = C.(Identity') s /\
    C.(Compose') _ _ _ m m' = C.(Identity') d.*)
  Definition InverseOf s d (m : Morphism s d) (m' : Morphism d s) : Prop :=
    m' o m  = Identity s /\
    m  o m' = Identity d.

  Lemma InverseOf_sym s d m m' : @InverseOf s d m m' -> @InverseOf d s m' m.
    firstorder.
  Qed.

  (* A morphism is an isomorphism if it has an inverse *)
  Definition IsIsomorphism s d (m : Morphism s d) : Prop :=
    exists m', InverseOf m m'.
  Definition Isomorphic s d := exists m : Morphism s d, IsIsomorphism m.

  (* As per David's comment, everything is better when we supply a witness rather
     than an assertion.  (In particular the [exists m' -> m'] transformation is only
     permissible for [m' : Prop].  Trying it on other with
       refine match H with
                | ex_intro x x0 => _ x x0
              end
     gives
       Error:
       Incorrect elimination of "H" in the inductive type "ex":
       the return type has sort "Type" while it should be "Prop".
       Elimination of an inductive object of sort Prop
       is not allowed on a predicate in sort Type
       because proofs can be eliminated only to build proofs.
     ) *)
  (*Definition CategoryIsomorphism' (s d : obj) (m : mor s d) := { m' | InverseOf' m m' }.*)
  Definition Isomorphism s d (m : Morphism s d) := { m' | InverseOf m m' }.

  Hint Unfold InverseOf IsIsomorphism Isomorphism.

  Lemma InverseOf1 : forall s d (m : Morphism s d) m', InverseOf m m'
    -> m' o m = Identity s.
    firstorder.
  Qed.

  Lemma InverseOf2 : forall s d (m : Morphism s d) m', InverseOf m m'
    -> m o m' = Identity d.
    firstorder.
  Qed.

  Lemma IsomorphismIsIsomorphism s d (m : Morphism s d) : Isomorphism m -> IsIsomorphism m.
    firstorder.
  Qed.

  Hint Rewrite <- InverseOf1 InverseOf2 using assumption.

  (* XXX TODO: Automate this better. *)
  Lemma iso_is_epi s d (m : Morphism s d) : IsIsomorphism m -> Epimorphism m.
    destruct 1 as [ x [ i0 i1 ] ]; intros z m1 m2 e.
    transitivity (m1 o (m o x)); [ t_with t' | ].
    transitivity (m2 o (m o x)); repeat rewrite <- Associativity; t_with t'.
  Qed.

  Lemma InverseOf1' : forall x y z (m : Morphism x y) (m' : Morphism y x) (m'' : Morphism z _),
    InverseOf m m'
    -> m' o (m o m'') = m''.
    unfold InverseOf; intros; destruct_hypotheses; repeat rewrite <- Associativity; t.
  Qed.

  Hint Rewrite InverseOf1' using assumption.

  (* XXX TODO: Automate this better. *)
  Lemma iso_is_mono s d (m : Morphism s d) : IsIsomorphism m -> Monomorphism m.
    destruct 1 as [ x [ i0 i1 ] ]; intros z m1 m2 e.
    transitivity (x o m o m1); [ t_with t' | ].
    transitivity (x o m o m2); [ repeat rewrite Associativity | ]; t_with t'.
  Qed.

  Theorem IdentityInverse a : InverseOf (Identity a) (Identity a).
    hnf; t.
  Qed.

  Hint Resolve CategoryIdentityInverse.

  Theorem IdentityIsomorphism a : Isomorphism (Identity a).
    eexists; t.
  Qed.
End identity.

Arguments IsIsomorphism {obj mor C H} [s d] m.
Arguments Isomorphism {obj mor C H} [s d] m.
Arguments InverseOf {obj mor C H} [s d] m m'.

Section IsomorphismEquivalenceRelation.
  Context `{C : Composable}.
  Variable H : HasIdentity C.

  Theorem IsomorphismComposition s d d' (m : Morphism s d) (m' : Morphism d d') :
    Isomorphism m -> Isomorphism m' -> Isomorphism (m' o m).
    repeat destruct 1; unfold InverseOf in *; destruct_hypotheses;
      match goal with
        | [ m : Morphism _ _, m' : Morphism _ _ |- _ ] => exists (m o m')
      end;
      split.
    repeat rewrite Associativity.
        compose4associativity t.
  Qed.
End CategoryIsomorphismEquivalenceRelation.

Section CategoryObjects1.
  Variable C : Category.

  Definition UniqueUpToUniqueIsomorphism' (P : C -> Prop) : Prop :=
    forall o, P o -> forall o', P o' -> exists m : Morphism o o', IsCategoryIsomorphism m /\ is_unique m.

  Definition UniqueUpToUniqueIsomorphism (P : C -> Type) :=
    forall o, P o -> forall o', P o' -> { m : Morphism o o' | IsCategoryIsomorphism m & is_unique m }.





(*
Ltac solve_for_identity :=
  match goal with
    | [ |- @Compose ?C ?s ?s ?d ?a ?b = ?b ] => cut (a = @Identity C s);
      try solve [ let H := fresh in intro H; rewrite H; apply LeftIdentity ]
    | [ |- @Compose ?C ?s ?d ?d ?a ?b = ?a ] => cut (b = @Identity C d );
      try solve [ let H := fresh in intro H; rewrite H; apply RightIdentity ]
  end.

Ltac find_composition_to_identity :=
  match goal with
    | [ H : @Compose _ _ _ _ ?a ?b = @Identity _ _ |- context[@Compose ?A ?B ?C ?D ?c ?d] ]
      => let H' := fresh in
        assert (H' : b = d /\ a = c) by (split; reflexivity); clear H';
          (rewrite H || (let HT := type of H in fail 1 "error in rewriting a found identity" HT))
(*          assert (H' : @Compose A B C D c d = @Identity _ _) by (
            exact H ||
              (unfold_Object; simpl in H |- *; exact H || (rewrite H; reflexivity))
          );
          simpl in H'; rewrite H' || (simpl; rewrite H') ||
            (let H'T := type of H' in fail 1 "error in rewriting a found identity" H'T);
            clear H'*)
  end.
*)

Hint Resolve @IsomorphismIsIsomorphism.

(*Ltac eapply_by_compose H :=
  match goal with
    | [ |- @eq (@Morphism ?obj ?mor ?C) _ _ ] => eapply (H obj mor C)
    | [ |- @Compose ?obj ?mor ?C _ _ _ _ _ = _ ] => eapply (H obj mor C)
    | [ |- _ = @Compose ?obj ?mor ?C _ _ _ _ _ ] => eapply (H obj mor C)
    | _ => eapply H
    | [ C : @SpecializedCategory ?obj ?mor |- _ ] => eapply (H obj mor C)
    | [ C : ?T |- _ ] => match eval hnf in T with | @SpecializedCategory ?obj ?mor => eapply (H obj mor C) end
  end.
*)
(*
Ltac solve_isomorphism := destruct_hypotheses;
  solve [ eauto ] ||
    match goal with
      | [ _ : Compose ?x ?x' = Identity _ |- IsCategoryIsomorphism ?x ] => solve [ exists x'; hnf; eauto ]
      | [ _ : Compose ?x ?x' = Identity _ |- CategoryIsomorphism ?x ] => solve [ exists x'; hnf; eauto ]
      | [ _ : Compose ?x ?x' = Identity _ |- context[Compose ?x _ = Identity _] ] => solve [ try exists x'; hnf; eauto ]
    end.
*)
(* [eapply] the theorem to get a pre/post composed mono/epi, then find the right one by looking
   for an [Identity], then solve the requirement that it's an isomorphism *)
(*Ltac post_compose_to_identity :=
  eapply iso_is_epi;
  [ | repeat rewrite AssociativityNoEvar by noEvar; find_composition_to_identity; rewrite RightIdentity ];
  [ solve_isomorphism | ].
Ltac pre_compose_to_identity :=
  eapply iso_is_mono;
  [ | repeat rewrite <- AssociativityNoEvar by noEvar; find_composition_to_identity; rewrite LeftIdentity ];
  [ solve_isomorphism | ].
*)
  (* A terminal object is an object with a unique morphism from every other object. *)
  Definition TerminalObject' (o : C) : Prop :=
    forall o', exists! m : Morphism o' o, True.

  Definition TerminalObject (o : C) :=
    forall o', { m : Morphism o' o | is_unique m }.

  (* An initial object is an object with a unique morphism from every other object. *)
  Definition InitialObject' (o : C) : Prop :=
    forall o', exists! m : Morphism o o', True.

  Definition InitialObject (o : C) :=
    forall o', { m : Morphism o o' | is_unique m }.
End CategoryObjects1.

Arguments UniqueUpToUniqueIsomorphism' [C] P.
Arguments UniqueUpToUniqueIsomorphism [C] P.
Arguments InitialObject' [C] o.
Arguments InitialObject [C] o.
Arguments TerminalObject' [C] o.
Arguments TerminalObject [C] o.

Section CategoryObjects2.
  Variable C : Category.

  Hint Unfold TerminalObject InitialObject InverseOf.

  Ltac unique := hnf; intros; specialize_all_ways; destruct_sig;
    unfold is_unique, unique, uniqueness in *;
      repeat (destruct 1);
      repeat match goal with
               | [ x : _ |- _ ] => exists x
             end; eauto; try split; try solve [ etransitivity; eauto ].

  (* The terminal object is unique up to unique isomorphism. *)
  Theorem TerminalObjectUnique : UniqueUpToUniqueIsomorphism (TerminalObject (C := C)).
    unique.
  Qed.

  (* The initial object is unique up to unique isomorphism. *)
  Theorem InitialObjectUnique : UniqueUpToUniqueIsomorphism (InitialObject (C := C)).
    unique.
  Qed.
End CategoryObjects2.



Instance Category' obj mor (C : @SpecializedCategory obj mor) : Composable mor.
  refine {|
    Compose := C.(Compose');
    Associativity := C.(Associativity')
  |}.
Defined.

Instance Category obj mor (C : @SpecializedCategory obj mor) : HasIdentity (Category' C).
  refine {|
    Identity := C.(Identity')
  |};
  exact C.(LeftIdentity') || exact C.(RightIdentity').
Defined.


(*
Ltac sanitize_category_by_destruction' C := (* Thanks, andersk! *)
  first [ has_no_body C | let C' := constr:(C) in
    fail "Sanitization by destruction only works if a hypothesis has no body.  Hypothesis " C' " has a body." ];
  let objC := fresh in let morC := fresh in let C' := fresh in
    destruct C as [ objC morC C' ]; try clear C; (* because sometimes it isn't cleared... *)
      progress change
        (@Build_Category (@Object (@Build_Category objC morC C')) (@Morphism (@Build_Category objC morC C')) (@UnderlyingCategory (@Build_Category objC morC C'))) with
        (@Build_Category objC morC C') in *;
        set (C := @Build_Category objC morC C') in *;
          clearbody C;
            clear objC morC C'.

Ltac sanitize_category_by_destruction := unfold GeneralizeCategory in *;
  repeat match goal with
           | [ _ : appcontext[@Build_Category (Object ?C) (Morphism ?C) (UnderlyingCategory ?C)] |- _ ] => sanitize_category_by_destruction' C
           | [ |- appcontext[@Build_Category (Object ?C) (Morphism ?C) (UnderlyingCategory ?C)] ] => sanitize_category_by_destruction' C
         end.

Ltac sanitize_spcategory :=
  repeat match goal with
           | [ _ : appcontext[fun x => ?f x] |- _ ] => progress change (fun x => f x) with f in *
           | [ |- appcontext[fun x => ?f x] ] => progress change (fun x => f x) with f in *
 (*
           | [ _ : appcontext [?f (@Morphism ?obj ?mor ?C) ?C] |- _ ] => progress change (f (@Morphism obj mor C) C) with (f mor C) in *
           | [ |- appcontext [?f (@Morphism ?obj ?mor ?C) ?C] ] => progress change (f (@Morphism obj mor C) C) with (f mor C) in *
           | [ _ : appcontext [?f (@Object ?obj ?mor ?C) ?mor ?C] |- _ ] => progress change (f (@Object obj mor C) mor C) with (f obj mor C) in *
           | [ |- appcontext [?f (@Object ?obj ?mor ?C) ?mor ?C] ] => progress change (f (@Object obj mor C) mor C) with (f obj mor C) in * *)
         end;
  repeat rewrite Category_eta in *;
    sanitize_category_by_destruction.

Ltac present_mor_all mor_fun cat :=
  repeat match goal with
           | [ _ : appcontext[mor_fun ?s ?d] |- _ ] => progress change (mor_fun s d) with (@Morphism cat s d) in *
           | [ |- appcontext[mor_fun ?s ?d] ] => progress change (mor_fun s d) with (@Morphism cat s d) in *
         end.

Ltac present_mor mor_fun cat :=
  repeat match goal with
           | [ _ : mor_fun ?s ?d |- _ ] => progress change (mor_fun s d) with (@Morphism cat s d) in *
         end.

Ltac present_obj obj cat := change obj with (Object cat) in *; simpl in *.

Ltac present_mor_from_context cmd :=
  repeat match goal with
           | [ _ : appcontext[cmd ?obj ?mor ?C] |- _ ] => progress present_mor mor C
           | [ |- appcontext[cmd ?obj ?mor ?C] ] => progress present_mor mor C
         end.

Ltac present_obj_mor from to :=
  repeat match goal with
           | [ _ : appcontext[from ?obj ?mor ?C] |- _ ] => progress change (from obj mor C) with (to C) in *
           | [ |- appcontext[from ?obj ?mor ?C] ] => progress change (from obj mor C) with (to C) in *
         end.

Ltac present_spcategory' := present_obj_mor @Identity' @Identity; present_obj_mor @Compose' @Compose;
  repeat match goal with
           | [ C : @SpecializedCategory ?obj ?mor |- _ ] => progress present_mor mor C
         end.

Ltac present_spcategory := present_obj_mor @Identity' @Identity; present_obj_mor @Compose' @Compose;
  repeat match goal with
           | [ C : @SpecializedCategory ?obj ?mor |- _ ] => progress present_mor mor C
         end;
  sanitize_spcategory.

Ltac present_spcategory_all := present_obj_mor @Identity' @Identity; present_obj_mor @Compose' @Compose;
  repeat match goal with
           | [ C : @SpecializedCategory ?obj ?mor |- _ ] => progress (present_mor_all mor C; present_obj obj C)
         end;
  sanitize_spcategory.

*)
