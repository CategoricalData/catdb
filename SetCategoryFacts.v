Require Import FunctionalExtensionality.
Require Export Category SetCategory DiscreteCategory CategoryIsomorphisms.
Require Import Common NaturalNumbersObject.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Notation IndexedTInitialOf obj coerce initial_obj :=
  ((fun o => exist _
                   (fun x : initial_obj%type => match x with end)
                   (fun _ => functional_extensionality_dep _ _ (fun x : initial_obj%type => match x with end)))
   : IsInitialObject (C := IndexedCatOf obj coerce) initial_obj%type).

Notation IndexedTTerminalOf obj coerce terminal_obj constr all_eq :=
  ((fun o : obj => exist (fun m : o -> terminal_obj => forall x : o -> terminal_obj, x = m)
                         (fun _ : o => constr)
                         (fun H : o -> terminal_obj => functional_extensionality_dep H
                                                                                     (fun _ : o => constr)
                                                                                     (fun x : o => all_eq _ _)))
   : IsTerminalObject (C := IndexedCatOf obj coerce) terminal_obj%type).

Notation IndexedEmptySetInitialOf obj coerce := (IndexedTInitialOf obj coerce Empty_set).
Notation IndexedFalseInitialOf obj coerce := (IndexedTInitialOf obj coerce False).

Notation IndexedUnitTerminalOf obj coerce := (IndexedTTerminalOf obj coerce unit tt unit_eq).
Notation IndexedTrueTerminalOf obj coerce := (IndexedTTerminalOf obj coerce True I True_eq).

Notation EmptySetInitialOf obj := (IndexedEmptySetInitialOf obj (fun x => x)).
Notation FalseInitialOf obj := (IndexedFalseInitialOf obj (fun x => x)).

Notation UnitTerminalOf obj := (IndexedUnitTerminalOf obj (fun x => x)).
Notation TrueTerminalOf obj := (IndexedTrueTerminalOf obj (fun x => x)).

Notation CoercedEmptySetInitialOf obj T := (IndexedEmptySetInitialOf obj (fun x => x : T)).
Notation CoercedFalseInitialOf obj T := (IndexedFalseInitialOf obj (fun x => x : T)).

Notation CoercedUnitTerminalOf obj T := (IndexedUnitTerminalOf obj (fun x => x : T)).
Notation CoercedTrueTerminalOf obj T := (IndexedTrueTerminalOf obj (fun x => x : T)).

Section InitialTerminal.
  Definition TypeCatFalseInitial : IsInitialObject (C := TypeCat) False := Eval simpl in FalseInitialOf Type.
  Definition SetCatFalseInitial : IsInitialObject (C := SetCat) False := Eval simpl in FalseInitialOf Set.
  Definition PropCatFalseInitial : IsInitialObject (C := PropCat) False := Eval simpl in FalseInitialOf Prop.

  Definition TypeCatEmptyInitial : IsInitialObject (C := TypeCat) Empty_set := Eval simpl in EmptySetInitialOf Type.
  Definition SetCatEmptyInitial : IsInitialObject (C := SetCat) Empty_set := Eval simpl in EmptySetInitialOf Set.

  Definition TypeCatTrueTerminal : IsTerminalObject (C := TypeCat) True := Eval simpl in TrueTerminalOf Type.
  Definition SetCatTrueTerminal : IsTerminalObject (C := SetCat) True := Eval simpl in TrueTerminalOf Set.
  Definition PropCatTrueTerminal : IsTerminalObject (C := PropCat) True := Eval simpl in TrueTerminalOf Prop.

  Definition TypeCatUnitTerminal : IsTerminalObject (C := TypeCat) unit := Eval simpl in UnitTerminalOf Type.
  Definition SetCatUnitTerminal : IsTerminalObject (C := SetCat) unit := Eval simpl in UnitTerminalOf Set.

  Definition TypeCatSingletonTerminal : IsTerminalObject (C := TypeCat) unit := Eval hnf in TypeCatUnitTerminal.
  Definition SetCatSingletonTerminal : IsTerminalObject (C := SetCat) unit := Eval hnf in SetCatUnitTerminal.
End InitialTerminal.

Section EpiMono.
  Definition compose {A B C : Type} (f : B -> C) (g : A -> B) := (fun x => f (g x)).

  Variables S : Type.

  Local Ltac t' :=
    match goal with
      | _ => progress (intros; subst; trivial)
      | _ => eexists; reflexivity
      | _ => discriminate
      | [ H : _ -> False |- _ ] => contradict H; solve [ t' ]
      | [ H : ~_ |- _ ] => contradict H; solve [ t' ]
      | [ dec : forall _, {_} + {_} |- _ ] =>
        match goal with
          | [ _ : appcontext[dec ?x] |- _ ] => destruct (dec x)
          | [ |- appcontext[dec ?x] ] => destruct (dec x)
        end
      | _ => apply functional_extensionality_dep; intro
      | _ => progress (unfold compose in *; simpl in *; fg_equal)
      | _ => progress apply_hyp'
      | _ => progress destruct_type bool
      | [ H : (_ -> exists _, _), x : _ |- _ ] => destruct (H x); clear H
      | _ => progress specialize_uniquely
    end.

  Local Ltac t :=
    repeat match goal with
             | _ => t'
             | [ H : ?A -> _ |- _ ] =>
               match goal with
                 | [ _ : A |- _ ] => fail 1 (* don't make an [A] if we already have one *)
                 | _ => let a := fresh in assert (a : A) by (repeat t'); specialize (H a)
               end
           end.

  Lemma InjMono B (f : B -> S) :
    (forall x y : B, f x = f y -> x = y)
    -> (forall A (g g' : A -> B), (compose f g) = (compose f g') -> g = g').
  Proof.
    t.
  Qed.

  Lemma MonoInj B (f : B -> S) :
    (forall A (g g' : A -> B), (compose f g) = (compose f g') -> g = g')
    -> (forall x y : B, f x = f y -> x = y).
  Proof.
    intros H x y; t.
    pose proof (fun H' => H bool (fun b => if b then x else y) (fun _ => y) H' true).
    t.
  Qed.

  Lemma SurjEpi A (f : A -> S) :
    (forall x : S, exists y : A, f y = x)
    -> (forall C (g g' : S -> C), (compose g f) = (compose g' f) -> g = g').
  Proof.
    t.
  Qed.

  Lemma EpiSurj A (f : A -> S) (member_dec : forall x : S, {exists y, f y = x} + {~exists y, f y = x}) :
    (forall C (g g' : S -> C), (compose g f) = (compose g' f) -> g = g')
    -> (forall x : S, exists y : A, f y = x).
  Proof.
    intro H.
    assert (H' := fun H' => H bool (fun y => if member_dec y then true else false) (fun y => true) H').
    clear H.
    t.
  Qed.
End EpiMono.

Section nat.
  Fixpoint NatBuilderFunction A (o : unit -> A) (s : A -> A) (n : nat) : A
    := match n with
         | 0 => o tt
         | S n' => s (NatBuilderFunction o s n')
       end.

  Local Ltac t :=
    simpl in *;
    repeat (split || intro || apply functional_extensionality_dep);
    destruct_head unit;
    split_and;
    subst;
    trivial;
    fg_equal;
    match goal with | [ n : nat |- _ ] => induction n end;
    simpl in *;
    congruence.

  Local Notation PartialBuild_NaturalNumbersPreObject T Cat :=
    (fun pf => @Build_NaturalNumbersPreObject Cat
                                              nat
                                              (UnitTerminalOf T)
                                              (fun _ => 0)
                                              S
                                              (fun A q f => exist _ (NatBuilderFunction q f) (pf A q f))).

  Local Ltac build_nat T Cat :=
    let t0 := constr:(PartialBuild_NaturalNumbersPreObject T Cat) in
    let t0' := (eval simpl in t0) in
    refine (t0' _);
      abstract t.

  Let SetCatNaturalNumbersPreObject' : NaturalNumbersPreObject SetCat. build_nat Set SetCat. Defined.
  Definition SetCatNaturalNumbersPreObject := Eval hnf in SetCatNaturalNumbersPreObject'.
  Let TypeCatNaturalNumbersPreObject' : NaturalNumbersPreObject TypeCat. build_nat Type TypeCat. Defined.
  Definition TypeCatNaturalNumbersPreObject := Eval hnf in TypeCatNaturalNumbersPreObject'.
End nat.
