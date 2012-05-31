Require Import Setoid Coq.Program.Basics Program.
Require Import Common EquivalenceRelation Category.

Section Functor.
  Variable C D : Category.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of categories is known as a functor. Namely, given
     categories [C] and [C'], a (covariant) functor [F : C -> C'] is a rule that assigns to
     each object [A] of [C] an object [F A] of [C'] and to each map [m : A -> B] of [C] a map
     [F m : F A -> F B] of [C'] preserving composition and identity; that is,
     (1) [F (m' ○ m) = (F m') ○ (F m)] for maps [m : A -> B] and [m' : B -> C] of [C], and
     (2) [F (id A) = id (F A)] for any object [A] of [C], where [id A] is the identity morphism of [A].

     Since we are using [MorhpismsEquivalent] rather than [=], we must additionally require
     that [F] preserves [MorphismsEquivalent].
     **)
  Record Functor := {
    ObjectOf :> C -> D;
    MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d);
    FEquivalenceOf : forall s d (m1 m2 : C.(Morphism) s d),
      MorphismsEquivalent _ _ _ m1 m2
      -> MorphismsEquivalent _ _ _ (MorphismOf _ _ m1) (MorphismOf _ _ m2);
    FCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
      MorphismsEquivalent _ _ _ (MorphismOf _ _ (Compose m2 m1))
      (Compose (MorphismOf _ _ m2) (MorphismOf _ _ m1));
    FIdentityOf : forall o, MorphismsEquivalent _ _ _ (MorphismOf _ _ (Identity o)) (Identity (ObjectOf o))
  }.
End Functor.

Implicit Arguments MorphismOf [C D s d].
Implicit Arguments FEquivalenceOf [C D s d m1 m2].
Implicit Arguments FCompositionOf [C D s d d' m1 m2].
Implicit Arguments FIdentityOf [C D].

Add Parametric Morphism C D s d F :
  (@MorphismOf C D F s d)
    with signature (MorphismsEquivalent C _ _) ==> (MorphismsEquivalent D _ _) as functor_morphism_eq_mor.
  intros; apply FEquivalenceOf; assumption.
Qed.

Section FunctorsEquivalent.
  Variable C D : Category.
  Variable F G : Functor C D.

  Definition FunctorsEquivalent :=
    exists objOf,
      exists morOf1, exists morOf2,
        exists feq1, exists feq2,
          exists fco1, exists fco2,
            exists fid1, exists fid2,
              F = {| ObjectOf := objOf;
                MorphismOf := morOf1;
                FEquivalenceOf := feq1;
                FCompositionOf := fco1;
                FIdentityOf := fid1 |}
              /\ G = {| ObjectOf := objOf;
                MorphismOf := morOf2;
                FEquivalenceOf := feq2;
                FCompositionOf := fco2;
                FIdentityOf := fid2 |}
              /\ forall s d (m : C.(Morphism) s d),
                D.(MorphismsEquivalent) _ _ (morOf1 _ _ m) (morOf2 _ _ m).

(*
  (* XXX TODO: Move to Common.v. *)
  Lemma JMeq_type_eq A B (a : A) (b : B) : a ~= b -> A = B.
    intro H; dependent destruction H; trivial.
  Qed.

  Implicit Arguments JMeq_type_eq [A B a b].

  Definition cast a b (p : a = b) : a -> b.
    intro; rewrite <- p; assumption.
  Defined.

  Implicit Arguments cast [a b].

  Lemma cast_nop T (p : T = T) (a : T) : cast p a = a.
    unfold cast; rewrite <- eq_rect_eq; reflexivity.
  Qed.

  Implicit Arguments cast_nop [T].

  Lemma cast_app_nop A : forall (F := A -> Type) (pF : F = F) (pA : A = A) (f : F) (a : A), ((cast pF f) (cast pA a)) = f a.
    intros; unfold cast; repeat (rewrite <- eq_rect_eq); reflexivity.
  Qed.

  Implicit Arguments cast_app_nop [A].

  Definition build_eq_functor objOf (morOf : forall s d : C, Morphism C s d -> Morphism D (objOf s) (objOf d)) p
    (objOfEq : objOf = (@ObjectOf _ _ F)) (morOfEq : morOf = cast p F.(MorphismOf)) :
    exists feq,
      exists fco,
        exists fid,
          F = {| ObjectOf := objOf;
            MorphismOf := morOf;
            FEquivalenceOf := feq;
            FCompositionOf := fco;
            FIdentityOf := fid |}.
  admit.
(*  apply  cast.
  Check F.(FEquivalenceOf).
  match goal with
    [ |- exists _ : ?T, _ ] => cut (T = forall (s d : C) (m1 m2 : Morphism C s d),
      (MorphismsEquivalent C) s d m1 m2 ->
       (MorphismsEquivalent D) (F s) (F d) (MorphismOf F m1)
       (MorphismOf F m2))
  end.
  admit.
  rewrite objOfEq.

  rewrite morOfEq.
  Print eq_rect.
Print cast.
Search (_ ~= _).
Print JMeq.
Check (eq_rect _ (fun b0 : Type => b0) F.(FEquivalenceOf) _ H).

FEquivalenceOf F
     : forall (s d : C) (m1 m2 : Morphism C s d),
       (MorphismsEquivalent C) s d m1 m2 ->
       (MorphismsEquivalent D) (F s) (F d) (MorphismOf F m1)
         (MorphismOf F m2)

 { F' | F = F' /\
  Print eq_rect_eq.
  Print eq_rect.*)
  Defined.
*)
End FunctorsEquivalent.

Implicit Arguments FunctorsEquivalent [C D].

Ltac clear_exists_in_assum :=
  repeat match goal with
           [ H : (exists _, _) |- _ ] => refine (ex_ind _ H); clear H; intros
         end.

Ltac exists_assum_with_tac2 exists_tac data :=
  match goal with
    | [ H : ?T |- exists _ : ?T, _ ] => exists_tac data H
    | [ H : ?T |- @sigT ?T _ ] => exists_tac data H
    | [ H : ?T |- @sig ?T _ ] => exists_tac data H
  end.
Ltac apply_tac tac arg := tac arg.
Ltac exists_assum_with_tac exists_tac := exists_assum_with_tac2 apply_tac exists_tac.
Ltac exists_tac H := exists H.
Ltac exists_assum := exists_assum_with_tac exists_tac.
Ltac exists_assum_solve_with_tac' final_tac H :=
  exists H; exists_assum_with_tac2 exists_assum_solve_with_tac' final_tac || solve [ final_tac ].
Ltac exists_assum_solve_with_tac final_tac := exists_assum_with_tac2 exists_assum_solve_with_tac' final_tac.
Ltac exists_assum_solve := exists_assum_solve_with_tac t.

Ltac functors_equivalent_destruct :=
  repeat match goal with
           | [ F : Functor _ _ |- _ ] => destruct F
           | [ H : @sigT _ _ |- _ ] => destruct H
           | [ H : @sig _ _ |- _ ] => destruct H
           | [ H : @and _ _ |- _ ] => destruct H
         end.

Ltac start_functors_equivalent :=
  intros; repeat (functors_equivalent_destruct; repeat (autounfold with core in *)); clear_exists_in_assum.

Lemma eq_functors_equivalent C D (F G : Functor C D) : (@ObjectOf _ _ F) ~= (@ObjectOf _ _ G) -> F.(MorphismOf) ~= G.(MorphismOf) -> FunctorsEquivalent F G.
  unfold FunctorsEquivalent; start_functors_equivalent.
  repeat exists_assum. repeat split; try assumption; try reflexivity.
  repeat
    match goal with
      [ H : _ ~= _ |- _ ] => inversion H; clear H; repeat simpl_existT
    end.
  cut (MorphismOf1 ~= MorphismOf0);
    cut (FEquivalenceOf1 ~= FEquivalenceOf0);
      cut (FCompositionOf1 ~= FCompositionOf0);
        cut (FIdentityOf1 ~= FIdentityOf0); t;
            repeat
              match goal with
                [ H : _ ~= _ |- _ ] => inversion H; clear H; repeat simpl_existT
              end;
  admit.
(*
  rewrite H1 in *.
  constructor. destruct 1.
  match goal with
    [ |- ?a ~= ?b ] => cut (a = b)
  end.
  t.  proof_irrelevance.

  simpl.

  unfold FunctorsEquivalent; start_functors_equivalent.
  repeat exists_assum.
  rewrite <- H.
  compute.
  rewrite H1.
  intro

  unfold FunctorsEquivalent; start_functors_equivalent.
  repeat exists_assum. repeat split; try assumption; try reflexivity.
  rewrite H1 in MorphismOf1.
  rewrite <- H1 in H4.
  repeat simpl_existT.
  Print Ltac simpl_existT
  Print functional_extensionality_dep.

    intros; unfold FunctorsEquivalent. *)
Qed.

Hint Resolve eq_functors_equivalent.

Section FunctorsEquivalenceReltation.
  Variable C D : Category.

  Hint Unfold FunctorsEquivalent.

  Lemma functors_equivalent_refl (F : Functor C D) : FunctorsEquivalent F F.
    start_functors_equivalent; exists_assum_solve.
  Qed.

  Lemma functors_equivalent_sym (F G : Functor C D) :
    FunctorsEquivalent F G -> FunctorsEquivalent G F.
    (* Is there a way to do something like [exists_assum_solve_with_tac [ repeat split; assumption || symmetry; intuition ]]? *)
    Ltac final := repeat split; assumption || symmetry; intuition.
    start_functors_equivalent; exists_assum_solve_with_tac final.
  Qed.

  Lemma functors_equivalent_trans (F G H : Functor C D) :
    FunctorsEquivalent F G -> FunctorsEquivalent G H -> FunctorsEquivalent F H.
    start_functors_equivalent.
(*      exists_assum. exists x1. exists x0. exists x6. exists x5. exists x8. exists x7. exists x10. exists x9.*)
    admit.
(*      exists_assum. exists x0. exists x1. exists x5. exists x6. exists x7. exists x8. exists x9. exists x10.
      repeat split; try assumption.
      transitivity {|
       ObjectOf := x2;
       MorphismOf := x3;
       FEquivalenceOf := x11;
       FCompositionOf := x13;
       FIdentityOf := x15 |}; try assumption.
      transitivity {|
      ObjectOf := ObjectOf1;
      MorphismOf := MorphismOf1;
      FEquivalenceOf := FEquivalenceOf1;
      FCompositionOf := FCompositionOf1;
      FIdentityOf := FIdentityOf1 |}; try assumption.
      transitivity {|
       ObjectOf := x2;
       MorphismOf := x4;
       FEquivalenceOf := x12;
       FCompositionOf := x14;
       FIdentityOf := x16 |}; try (assumption || symmetry; assumption).
      match goal with
        | [ H1 : ?a = ?b, H3 : ?c = ?d |- ?a = ?d ] => idtac a; idtac d
      end.
      apply (eq_trans H2). symmetry. apply (eq_trans H0).

apply (fun x => eq_trans x H3). Check eq_trans. rewrite H3. apply (eq_trans H3).  impl_transitivity.

    repeat (autounfold with core in * ); intros.
    (* XXX ?GeneralizedRelationsEquivalent is a kludge *)
    match goal with
      [
        H0 : (forall _ _ _, ?GeneralizedRelationsEquivalent _ _ _ _ _ _),
        H1 : (forall _ _ _, ?GeneralizedRelationsEquivalent _ _ _ _ _ _)
        |- ?GeneralizedRelationsEquivalent _ _ _ _ _ _
      ] => apply (generalized_relations_equivalent_trans (H0 _ _ _) (H1 _ _ _)) ||
      apply (generalized_relations_equivalent_trans (H1 _ _ _) (H0 _ _ _))
    end.*)
  Qed.
End FunctorsEquivalenceReltation.

Add Parametric Relation (C D : Category) : _ (@FunctorsEquivalent C D)
  reflexivity proved by (functors_equivalent_refl _ _)
  symmetry proved by (functors_equivalent_sym _ _)
  transitivity proved by (functors_equivalent_trans _ _)
    as functors_equivalent.

Section FunctorComposition.
  Variable B C D E : Category.

  Hint Resolve FEquivalenceOf FCompositionOf FIdentityOf.

  (* XXX TODO: automate theis proof better so that we don't refer to [m1], [m2], or [o] explicitly *)
  Definition ComposeFunctors (G : Functor D E) (F : Functor C D) : Functor C E.
    refine {| ObjectOf := (fun c => G (F c));
      MorphismOf := (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
      |}; t.
    transitivity (MorphismOf G (Compose (MorphismOf F m2) (MorphismOf F m1))); t.
    transitivity (MorphismOf G (Identity (F o))); t.
  Defined.
End FunctorComposition.

Implicit Arguments ComposeFunctors [C D E].

(*
Add Parametric Morphism C D E :
  (@ComposeFunctors C D E)
  with signature (@FunctorsEquivalent _ _) ==> (@FunctorsEquivalent _ _) ==> (@FunctorsEquivalent _ _) as functor_eq_mor.
  intros.
  match goal with
    [
      H : FunctorsEquivalent ?a ?a',
      H' : FunctorsEquivalent ?b ?b'
      |- FunctorsEquivalent (ComposeFunctors ?a ?b) (ComposeFunctors ?a' ?b')
    ] => transitivity (ComposeFunctors a b')
  end; t.
  unfold FunctorsEquivalent; unfold GeneralizedMorphismsEquivalent. intros F G e F' G' e' s d m.
  specialize (e s d m).
  dependent destruction e.
  transitivity (F'.(MorphismOf) (F.(MorphismOf) m)).
  cbv delta.
  rewrite FCompositionOf.
  unfold ComposeFunctors MorphismOf.
  apply
  t.
  t. transitivity (ComposeFunctors x y0).
  unfold FunctorsNaturallyEquivalent in *.
  simpl in *.*)


Section Category.
  Variable C D : Category.

  (* There is an identity functor.  It does the obvious thing. *)
  Definition IdentityFunctor : Functor C C.
    refine {| ObjectOf := (fun x => x);
      MorphismOf := (fun _ _ x => x)
    |};
    abstract t.
  Defined.

(*  Hint Unfold FunctorsEquivalent ComposeFunctors IdentityFunctor.*)

  Hint Extern 1 ( _ = _ ) => apply functional_extensionality_dep.
  Hint Extern 1 ( ?a ~= ?b ) => cut (a = b); try solve [ intro H; rewrite H; reflexivity ].

  Hint Rewrite eq_functors_equivalent.

  Lemma LeftIdentityFunctor (F : Functor D C) : FunctorsEquivalent (ComposeFunctors IdentityFunctor F) F.
    t.
  Qed.

  Lemma RightIdentityFunctor (F : Functor C D) : FunctorsEquivalent (ComposeFunctors F IdentityFunctor) F.
    t.
  Qed.
End Category.

Section FunctorCompositionLemmas.
  Variable B C D E : Category.

  Hint Unfold FunctorsEquivalent GeneralizedMorphismsEquivalent.
  Hint Resolve FEquivalenceOf FCompositionOf FIdentityOf.

  Hint Extern 1 ( _ = _ ) => apply functional_extensionality_dep.
  Hint Extern 1 ( ?a ~= ?b ) => cut (a = b); try solve [ intro H; rewrite H; reflexivity ].

  Hint Rewrite eq_functors_equivalent.

  Lemma PreComposeFunctors (G : Functor D E) (F1 F2 : Functor C D) :
    FunctorsEquivalent F1 F2 -> FunctorsEquivalent (ComposeFunctors G F1) (ComposeFunctors G F2).
    intros; apply eq_functors_equivalent; t;
      start_functors_equivalent;
    match goal with
      [ |- (?a : (_ -> _)) ~= (?b : (_ -> _)) ] => cut (forall x, a x ~= b x)
    end; t; admit.
(*    admit.
    match goal with
      [ |- ?f ?a ~= ?f ?b ] => cut (a ~= b)
    end.
    intro; auto with *.
    firstorder.
    admit.
    start_functors_equivalent. destruct H. destruct H0.
    unfold FunctorsEquivalent in *.
    t.

    admit. *)
    (*
    repeat ( autounfold with core in * ); t.
    match goal with
      | [ HT : Morphism _ ?s ?d, H : (forall s d (m : Morphism _ s d), _) |- _ ] => specialize (H s d HT)
    end.
    cut (
      GeneralizedRelationsEquivalent (MorphismsEquivalent E) (MorphismOf (ComposeFunctors G F1) m) (MorphismOf G (MorphismOf F1 m))
      /\
      GeneralizedRelationsEquivalent (MorphismsEquivalent E) (MorphismOf (ComposeFunctors G F2) m) (MorphismOf G (MorphismOf F1 m))
      ); split || destruct 1; t.
    inversion H; t.
    Print Ltac simpl_existT.
    match goal with
      | [ H : existT _ ?x _ = existT _ ?x _ |- _ ] =>
              let Hi := fresh H in
      pose proof (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H) as Hi; clear H
end.
    simpl_existTs in H6.
    dependent destruction H.
    dependent destruction x.
    autounfold with core in *.
    match goal with
      | [ H : @MorphismsEquivalent' _ _ _ ?m1 ?m2 |- _ ] => generalize (G.(FEquivalenceOf) H)
    end.
    Search (_ ~= _ -> _ = _).
    intro H'.
    Check JMeq_congr
    rewrite (JMeq_congr _ x) in H.
    match goal with
      [ H : ?a ~= ?b |- _ ] => cut (a = b)
    end.

    rewrite <- x.
    generalize (FEquivalenceOf G H).
    Check @JMeq_eq.
    rewrite (@JMeq_eq _ r2 (MorphismOf F2 m) x) in H.
    Search (_ ~= _ -> _ = _).
    rewrite x in H.
    Check @JMeq_eq.

(*    match goal with
      | [ |- ?Rel (MorphismOf (ComposeFunctors ?F ?G) ?m) ?H ] => cut (Rel ( *)
    apply generalized_relations_equivalent_trans.*)
  Qed.

  Lemma PostComposeFunctors (G1 G2 : Functor D E) (F : Functor C D) :
    FunctorsEquivalent G1 G2 -> FunctorsEquivalent (ComposeFunctors G1 F) (ComposeFunctors G2 F).
    admit.
  Qed.

  Lemma ComposeFunctorsAssociativity (F : Functor B C) (G : Functor C D) (H : Functor D E) :
    FunctorsEquivalent (ComposeFunctors (ComposeFunctors H G) F) (ComposeFunctors H (ComposeFunctors G F)).
    admit.
  Qed.
End FunctorCompositionLemmas.
