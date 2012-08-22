Require Import FunctionalExtensionality.
Require Export Functor.
Require Import Common Hom Duals ProductFunctor NaturalTransformation SetCategory.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope category_scope.

Section FullFaithful.
  Context `(C : @SpecializedCategory objC).
  Context `(C' : @LocallySmallSpecializedCategory objC').
  Context `(D : @SpecializedCategory objD).
  Context `(D' : @LocallySmallSpecializedCategory objD').
  Variable F : SpecializedFunctor C D.
  Variable F' : SpecializedFunctor C' D'.
  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.
  Let FOp := OppositeFunctor F.
  Let C'Op := OppositeCategory C'.
  Let D'Op := OppositeCategory D'.
  Let F'Op := OppositeFunctor F'.

  Hint Rewrite @FCompositionOf.

  Definition InducedHomNaturalTransformation :
    SpecializedNaturalTransformation (HomFunctor C) (ComposeFunctors (HomFunctor D) (FOp * F)).
    refine (Build_SpecializedNaturalTransformation (HomFunctor C) (ComposeFunctors (HomFunctor D) (FOp * F))
      (fun sd : (COp * C) =>
        MorphismOf F (s := _) (d := _))
      _
    );
    abstract (simpl; intros; destruct_type @prod; simpl in *; repeat (apply functional_extensionality_dep; intro); t_with t').
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
    unfold Epimorphism, Monomorphism in *; simpl in *.
    unfold SpecializedCategoryIsomorphism; simpl.
    destruct C, D, F; simpl in *; clear C D F.
    *)
End FullFaithful.
