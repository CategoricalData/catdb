Require Import FunctionalExtensionality.
Require Export Functor.
Require Import Common Hom Duals FunctorProduct NaturalTransformation SetCategory.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Section FullFaithful.
  Variable C : Category.
  Context `(C' : @Category).
  Variable D : Category.
  Context `(D' : @Category).
  Variable F : Functor C D.
  Variable F' : Functor C' D'.
  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.
  Let FOp := OppositeFunctor F.
  Let C'Op := OppositeCategory C'.
  Let D'Op := OppositeCategory D'.
  Let F'Op := OppositeFunctor F'.

  Definition InducedHomNaturalTransformation :
    NaturalTransformation (HomFunctor C) (ComposeFunctors (HomFunctor D) (FOp * F)).
    refine (Build_NaturalTransformation (HomFunctor C) (ComposeFunctors (HomFunctor D) (FOp * F))
      (fun sd : (COp * C) =>
        MorphismOf F (s := _) (d := _))
      _
    );
    abstract (
        simpl; intros;
        destruct_type @prod;
        simpl in *;
          repeat (apply functional_extensionality_dep; intro);
        repeat rewrite FCompositionOf; reflexivity
      ).
  Defined.

  (* We really want surjective/injective here, but we only have epi/mono.
     They're equivalent in the category of sets.  Are they equivalent in the
     category of [Type]s? *)
  Definition FunctorFull := forall x y : C, IsEpimorphism (InducedHomNaturalTransformation.(ComponentsOf) (x, y)).
  Definition FunctorFaithful := forall x y : C, IsMonomorphism (InducedHomNaturalTransformation.(ComponentsOf) (x, y)).

  Definition FunctorFullyFaithful := forall x y : C, IsIsomorphism (InducedHomNaturalTransformation.(ComponentsOf) (x, y)).

  Lemma FunctorFullyFaithful_split : FunctorFullyFaithful -> FunctorFull /\ FunctorFaithful.
    unfold FunctorFullyFaithful, FunctorFull, FunctorFaithful; intro H; split; intros;
      apply iso_is_epi || apply iso_is_mono; auto.
  Qed.

(*
  (* Depends on injective + surjective -> isomorphism, and epi = surj, mono = inj *)
  Definition FunctorFullFaithful_and : FunctorFull /\ FunctorFaithful -> FunctorFullyFaithful.
    intro H; destruct H as [ e m ].
    unfold FunctorFullyFaithful, FunctorFull, FunctorFaithful in *.
    intros x y; specialize (e x y); specialize (m x y).
    unfold IsEpimorphism, IsMonomorphism in *; simpl in *.
    unfold IsIsomorphism; simpl.
    eexists;
      split.
    destruct C, D, F; simpl in *; clear C D F.
    *)
End FullFaithful.
