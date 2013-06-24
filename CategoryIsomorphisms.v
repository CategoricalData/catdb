Require Import ProofIrrelevance Setoid.
Require Export Category.
Require Import Common StructureEquality.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Category.
  Context `{C : Category}.

  (* [m'] is the inverse of [m] if both compositions are
     equivalent to the relevant identity morphisms. *)
  (* [Definitions] don't get sort-polymorphism :-(  *)
  Definition IsInverseOf1 (s d : C) (m : C.(Morphism) s d) (m' : C.(Morphism) d s) : Prop :=
    Compose m' m = Identity s.
  Definition IsInverseOf2 (s d : C) (m : C.(Morphism) s d) (m' : C.(Morphism) d s) : Prop :=
    Compose m m' = Identity d.

  Global Arguments IsInverseOf1 / _ _ _ _.
  Global Arguments IsInverseOf2 / _ _ _ _.

  Definition IsInverseOf {s d : C} (m : C.(Morphism) s d) (m' : C.(Morphism) d s) : Prop := Eval simpl in
    @IsInverseOf1 s d m m' /\ @IsInverseOf2 s d m m'.

  Lemma IsInverseOf_sym s d m m' : @IsInverseOf s d m m' -> @IsInverseOf d s m' m.
    firstorder.
  Qed.

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
  (* [Record]s are [Inductive] and get sort-polymorphism *)
  Section IsomorphismOf.
    (* A morphism is an isomorphism if it has an inverse *)
    Record IsomorphismOf {s d : C} (m : C.(Morphism) s d) := {
      IsomorphismOf_Morphism :> C.(Morphism) s d := m;
      Inverse : C.(Morphism) d s;
      LeftInverse : Compose Inverse m = Identity s;
      RightInverse : Compose m Inverse = Identity d
    }.

    Hint Resolve RightInverse LeftInverse : category.
    Hint Resolve RightInverse LeftInverse : morphism.

    Definition IsomorphismOf_sig2 {s d : C} (m : C.(Morphism) s d) (i : @IsomorphismOf s d m) :
      { m' | Compose m' m = Identity s & Compose m m' = Identity d }.
      exists (Inverse i);
        [ apply LeftInverse | apply RightInverse ].
    Defined.

    Definition IsomorphismOf_sig {s d : C} (m : C.(Morphism) s d) := { m' | Compose m' m = Identity s & Compose m m' = Identity d }.

    Global Identity Coercion Isomorphism_sig : IsomorphismOf_sig >-> sig2.

    Definition sig2_IsomorphismOf {s d : C} (m : C.(Morphism) s d) (i : @IsomorphismOf_sig s d m) :
      @IsomorphismOf s d m.
      exists (proj1_sig i);
        [ apply (proj2_sig i) | apply (proj3_sig i) ].
    Defined.

    Global Coercion IsomorphismOf_sig2 : IsomorphismOf >-> sig2.
    Global Coercion sig2_IsomorphismOf : IsomorphismOf_sig >-> IsomorphismOf.

    Definition IsomorphismOf_Identity (c : C) : IsomorphismOf (Identity c).
      exists (Identity _); auto with morphism.
    Defined.

    Definition InverseOf {s d : C} (m : C.(Morphism) s d) (i : IsomorphismOf m) : IsomorphismOf (Inverse i).
      exists (i : Morphism C _ _); auto with morphism.
    Defined.

    Definition ComposeIsomorphismOf {s d d' : C} {m1 : C.(Morphism) d d'} {m2 : C.(Morphism) s d} (i1 : IsomorphismOf m1) (i2 : IsomorphismOf m2) :
      IsomorphismOf (Compose m1 m2).
      exists (Compose (Inverse i2) (Inverse i1));
      abstract (
          simpl; compose4associativity;
          destruct i1, i2; simpl;
          repeat (rewrite_hyp; autorewrite with morphism);
          trivial
        ).
    Defined.
  End IsomorphismOf.

  Section Isomorphism.
    Record Isomorphism (s d : C) := {
      Isomorphism_Morphism : C.(Morphism) s d;
      Isomorphism_Of :> IsomorphismOf Isomorphism_Morphism
    }.

    Global Coercion Build_Isomorphism : IsomorphismOf >-> Isomorphism.
  End Isomorphism.

  Section IsIsomorphism.
    Definition IsIsomorphism {s d : C} (m : C.(Morphism) s d) : Prop :=
      exists m', IsInverseOf m m'.

    Lemma IsomrphismOf_IsIsomorphism {s d : C} (m : C.(Morphism) s d) : IsomorphismOf m -> IsIsomorphism m.
      intro i; hnf.
      exists (Inverse i);
        destruct i; simpl;
        split;
        assumption.
    Qed.

    Lemma IsIsomorphism_IsomrphismOf {s d : C} (m : C.(Morphism) s d) : IsIsomorphism m -> exists _ : IsomorphismOf m, True.
      intro i; destruct_hypotheses.
      destruct_exists; trivial.
      eexists; eassumption.
    Qed.
  End IsIsomorphism.

  Section Isomorphic.
    Definition Isomorphic (s d : C) : Prop :=
      exists (m : C.(Morphism) s d) (m' : C.(Morphism) d s), IsInverseOf m m'.

    Lemma Isomrphism_Isomorphic s d : Isomorphism s d -> Isomorphic s d.
      intro i; destruct i as [ m i ].
      exists m.
      apply IsomrphismOf_IsIsomorphism; assumption.
    Qed.

    Lemma Isomorphic_Isomorphism s d : Isomorphic s d -> exists _ : Isomorphism s d, True.
      intro i; destruct_hypotheses.
      destruct_exists; trivial.
      repeat esplit; eassumption.
    Qed.

    Local Ltac t_iso' := intros;
      repeat match goal with
               | [ i : Isomorphic _ _ |- _ ] => destruct (Isomorphic_Isomorphism i) as [ ? [] ] ; clear i
               | [ |- Isomorphic _ _ ] => apply Isomrphism_Isomorphic
             end.

    Local Ltac t_iso:= t_iso';
      repeat match goal with
               | [ i : Isomorphism _ _ |- _ ] => unique_pose (Isomorphism_Of i); try clear i
               | [ |- Isomorphism _ _ ] => eapply Build_Isomorphism
             end.

    Hint Resolve @IsomorphismOf_Identity @InverseOf @ComposeIsomorphismOf : category morphism.
    Local Hint Extern 1 => eassumption.

    Lemma Isomorphic_refl c : Isomorphic c c.
      t_iso.
      apply IsomorphismOf_Identity.
    Qed.

    Lemma Isomorphic_sym s d : Isomorphic s d -> Isomorphic d s.
      t_iso.
      eauto with morphism.
      Grab Existential Variables.
      eauto with morphism.
    Qed.

    Lemma Isomorphic_trans s d d' : Isomorphic s d -> Isomorphic d d' -> Isomorphic s d'.
      t_iso.
      apply @ComposeIsomorphismOf;
        eauto with morphism.
    Qed.

    Global Add Parametric Relation : _ Isomorphic
      reflexivity proved by Isomorphic_refl
      symmetry proved by Isomorphic_sym
      transitivity proved by Isomorphic_trans
        as Isomorphic_rel.
  End Isomorphic.

  (* XXX TODO: Automate this better. *)
  Lemma iso_is_epi s d (m : _ s d) : IsIsomorphism m -> IsEpimorphism (C := C) m.
    destruct 1 as [ x [ i0 i1 ] ]; intros z m1 m2 e.
    transitivity (Compose m1 (Compose m x)); [ rewrite_hyp; autorewrite with morphism | ]; trivial.
    transitivity (Compose m2 (Compose m x)); [ repeat rewrite <- Associativity | ]; rewrite_hyp; autorewrite with morphism; trivial.
  Qed.

  (* XXX TODO: Automate this better. *)
  Lemma iso_is_mono s d (m : _ s d) : IsIsomorphism m -> IsMonomorphism (C := C) m.
    destruct 1 as [ x [ i0 i1 ] ]; intros z m1 m2 e.
    transitivity (Compose (Compose x m) m1); [ rewrite_hyp; autorewrite with morphism | ]; trivial.
    transitivity (Compose (Compose x m) m2); [ repeat rewrite Associativity | ]; rewrite_hyp; autorewrite with morphism; trivial.
  Qed.
End Category.

Hint Resolve @RightInverse @LeftInverse @IsomorphismOf_Identity @ComposeIsomorphismOf : category morphism.

Ltac eapply_by_compose H :=
  match goal with
    | [ |- @eq (@Morphism ?C) _ _ ] => eapply (H C)
    | [ |- @Compose ?C _ _ _ _ _ = _ ] => eapply (H C)
    | [ |- _ = @Compose ?C _ _ _ _ _ ] => eapply (H C)
    | _ => eapply H
    | [ C : Category |- _ ] => eapply (H C)
    | [ C : ?T |- _ ] => match eval hnf in T with | Category => eapply (H C) end
  end.

Ltac solve_isomorphism := destruct_hypotheses;
  solve [ eauto ] ||
    match goal with
      | [ _ : Compose ?x ?x' = Identity _ |- IsIsomorphism ?x ] => solve [ exists x'; hnf; eauto ]
      | [ _ : Compose ?x ?x' = Identity _ |- Isomorphism ?x ] => solve [ exists x'; hnf; eauto ]
      | [ _ : Compose ?x ?x' = Identity _ |- IsomorphismOf ?x ] => solve [ exists x'; hnf; eauto ]
      | [ _ : Compose ?x ?x' = Identity _ |- context[Compose ?x _ = Identity _] ] => solve [ try exists x'; hnf; eauto ]
    end.

(* [eapply] the theorem to get a pre/post composed mono/epi, then find the right one by looking
   for an [Identity], then solve the requirement that it's an isomorphism *)
Ltac post_compose_to_identity :=
  eapply_by_compose iso_is_epi;
  [ | repeat rewrite AssociativityNoEvar by noEvar; find_composition_to_identity; rewrite RightIdentity ];
  [ solve_isomorphism | ].
Ltac pre_compose_to_identity :=
  eapply_by_compose iso_is_mono;
  [ | repeat rewrite <- AssociativityNoEvar by noEvar; find_composition_to_identity; rewrite LeftIdentity ];
  [ solve_isomorphism | ].

Section CategoryObjects1.
  Variable C : Category.

  Definition UniqueUpToUniqueIsomorphism' (P : C.(Object) -> Prop) : Prop :=
    forall o, P o -> forall o', P o' -> exists m : C.(Morphism) o o', IsIsomorphism m /\ is_unique m.

  Definition UniqueUpToUniqueIsomorphism (P : C.(Object) -> Type) :=
    forall o, P o -> forall o', P o' -> { m : C.(Morphism) o o' | IsIsomorphism m & is_unique m }.

  Section terminal.
    (* A terminal object is an object with a unique morphism from every other object. *)
    Definition IsTerminalObject' (o : C) : Prop :=
      forall o', exists! m : C.(Morphism) o' o, True.

    Definition IsTerminalObject (o : C) :=
      forall o', { m : C.(Morphism) o' o | is_unique m }.

    Record TerminalObject :=
      {
        TerminalObject_Object' : C;
        TerminalObject_Morphism : forall o, Morphism C o TerminalObject_Object';
        TerminalObject_Property : forall o, is_unique (TerminalObject_Morphism o)
      }.

    Definition TerminalObject_Object : TerminalObject -> C := TerminalObject_Object'.

    Global Coercion TerminalObject_Object : TerminalObject >-> Object.

    Definition TerminalObject_IsTerminalObject (o : TerminalObject) : IsTerminalObject o
      := fun o' => exist _ (TerminalObject_Morphism o o') (TerminalObject_Property o o').

    Definition IsTerminalObject_TerminalObject o : IsTerminalObject o -> TerminalObject
      := fun H => @Build_TerminalObject o (fun o' => proj1_sig (H o')) (fun o' => proj2_sig (H o')).

    Global Coercion TerminalObject_IsTerminalObject : TerminalObject >-> IsTerminalObject.
    Global Coercion IsTerminalObject_TerminalObject : IsTerminalObject >-> TerminalObject.
  End terminal.

  Section initial.
    (* An initial object is an object with a unique morphism from every other object. *)
    Definition IsInitialObject' (o : C) : Prop :=
      forall o', exists! m : C.(Morphism) o o', True.

    Definition IsInitialObject (o : C) :=
      forall o', { m : C.(Morphism) o o' | is_unique m }.

    Record InitialObject :=
      {
        InitialObject_Object' :> C;
        InitialObject_Morphism : forall o, Morphism C InitialObject_Object' o;
        InitialObject_Property : forall o, is_unique (InitialObject_Morphism o)
      }.

    Definition InitialObject_Object : InitialObject -> C := InitialObject_Object'.

    Global Coercion InitialObject_Object : InitialObject >-> Object.

    Definition InitialObject_IsInitialObject (o : InitialObject) : IsInitialObject o
      := fun o' => exist _ (InitialObject_Morphism o o') (InitialObject_Property o o').

    Definition IsInitialObject_InitialObject o : IsInitialObject o -> InitialObject
      := fun H => @Build_InitialObject o (fun o' => proj1_sig (H o')) (fun o' => proj2_sig (H o')).

    Global Coercion InitialObject_IsInitialObject : InitialObject >-> IsInitialObject.
    Global Coercion IsInitialObject_InitialObject : IsInitialObject >-> InitialObject.
  End initial.
End CategoryObjects1.

Arguments UniqueUpToUniqueIsomorphism {C} P.
Arguments IsInitialObject' {C} o.
Arguments IsInitialObject {C} o.
Arguments IsTerminalObject' {C} o.
Arguments IsTerminalObject {C} o.

Section CategoryObjects2.
  Variable C : Category.

  Ltac unique := hnf; intros; specialize_all_ways; destruct_sig;
    unfold is_unique, unique, uniqueness in *;
      repeat (destruct 1);
      repeat match goal with
               | [ x : _ |- _ ] => exists x
             end; eauto with category; try split; try solve [ etransitivity; eauto with category ].

  (* The terminal object is unique up to unique isomorphism. *)
  Theorem TerminalObjectUnique : UniqueUpToUniqueIsomorphism (IsTerminalObject (C := C)).
    unique.
  Qed.

  (* The initial object is unique up to unique isomorphism. *)
  Theorem InitialObjectUnique : UniqueUpToUniqueIsomorphism (IsInitialObject (C := C)).
    unique.
  Qed.
End CategoryObjects2.
