Require Import FunctionalExtensionality.
Require Export Functor.
Require Import Common Hom Duals ProductFunctor NaturalTransformation SetCategory.

Set Implicit Arguments.

Local Infix "*" := ProductCategory.
Local Infix "**" := ProductFunctor (at level 70).

Section FullFaithful.
  Variables C D : Category.
  Variable F : Functor C D.
  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.
  Let FOp := OppositeFunctor F.

  Hint Rewrite FCompositionOf.

  Definition InducedHomNaturalTransformation : NaturalTransformation (HomFunctor C) (ComposeFunctors (HomFunctor D) (FOp ** F)).
    match goal with
      | [ |- NaturalTransformation ?F0 ?G0 ] =>
        refine (Build_NaturalTransformation F0 G0
          (fun sd => (fun m => F.(MorphismOf) m))
          _
        )
    end;
    abstract (simpl; intros; destruct_type @prod; simpl in *; repeat (apply functional_extensionality_dep; intro); t_with t').
  Defined.

  (* We really want surjective/injective here, but we only have epi/mono.
     They're equivalent in the category of sets.  Are they equivalent in the
     category of [Type]s? *)
  Definition FunctorFull := forall x y : C, Epimorphism (InducedHomNaturalTransformation.(ComponentsOf) (x, y)).
  Definition FunctorFaithful := forall x y : C, Monomorphism (InducedHomNaturalTransformation.(ComponentsOf) (x, y)).

  Definition FunctorFullyFaithful := forall x y : C, CategoryIsomorphism (InducedHomNaturalTransformation.(ComponentsOf) (x, y)).

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
    unfold CategoryIsomorphism; simpl.
    destruct C, D, F; simpl in *; clear C D F.
    *)
End FullFaithful.
