Require Import FunctionalExtensionality.
Require Export Functor.
Require Import Common Hom Duals ProductFunctor NaturalTransformation SetCategory.

Set Implicit Arguments.

Local Infix "*" := ProductFunctor.

Section FullFaithful.
  Variables C D : Category.
  Variable F : Functor C D.

  Hint Rewrite FCompositionOf.

  Definition InducedHomNaturalTransformation : NaturalTransformation (HomFunctor C) (ComposeFunctors (HomFunctor D) ((OppositeFunctor F) * F)).
  (* Gahhh, type signatures and casting *)
    refine {| ComponentsOf := (fun sd : (Object (ProductCategory (OppositeCategory C) C)) =>
      (fun m : Morphism C (fst sd) (snd sd) =>
        F.(MorphismOf) m) : Morphism TypeCat ((HomFunctor C) _) ((ComposeFunctors (HomFunctor D) ((OppositeFunctor F) * F)) _))
      |}; abstract (simpl; intros; destruct_type @prod; simpl in *; repeat (apply functional_extensionality_dep; intro); t_with t').
  Defined.

  (* We really want surjective/injective here, but we only have epi/mono.
     They're equivalent in the category of sets.  Are they equivalent in the
     category of [Type]s? *)
  Definition FunctorFull := forall x y : C, Epimorphism (InducedHomNaturalTransformation.(ComponentsOf) (x, y)).
  Definition FunctorFaithful := forall x y : C, Monomorphism (InducedHomNaturalTransformation.(ComponentsOf) (x, y)).

  Definition FunctorFullyFaithful := forall x y : C, CategoryIsomorphism (InducedHomNaturalTransformation.(ComponentsOf) (x, y)).

  Lemma FunctorFullyFaithful_split : FunctorFullyFaithful -> FunctorFull /\ FunctorFaithful.
    unfold FunctorFullyFaithful, FunctorFull, FunctorFaithful; intro H; split; intros;
      apply iso_is_epi || apply iso_is_mono; trivial.
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
