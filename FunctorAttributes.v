Require Import FunctionalExtensionality.
Require Export Functor.
Require Import Common Hom Duals ProductFunctor NaturalTransformation SetCategory.

Set Implicit Arguments.

Local Infix "*" := ProductCategory.
Local Infix "**" := ProductFunctor (at level 70).

Section FullFaithful.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable morC' : objC -> objC -> Set.
  Variable C : SpecializedCategory morC.
  Variable C' : LocallySmallSpecializedCategory morC'.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable morD' : objD -> objD -> Set.
  Variable D : SpecializedCategory morD.
  Variable D' : LocallySmallSpecializedCategory morD'.
  Variable F : SpecializedFunctor C D.
  Variable F' : SpecializedFunctor C' D'.
  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.
  Let FOp := OppositeFunctor F.
  Let C'Op := OppositeCategory C'.
  Let D'Op := OppositeCategory D'.
  Let F'Op := OppositeFunctor F'.

  Hint Rewrite FCompositionOf.

  Definition InducedHomNaturalTransformation :
    SpecializedNaturalTransformation (HomFunctor C) (ComposeFunctors (HomFunctor D) (FOp ** F)).
    refine (Build_SpecializedNaturalTransformation (HomFunctor C) (ComposeFunctors (HomFunctor D) (FOp ** F))
      (fun sd : (COp * C) =>
        @MorphismOf _ _ _ _ _ _ F _ _ )
      _
    );
    abstract (simpl; intros; destruct_type @prod; simpl in *; repeat (apply functional_extensionality_dep; intro); t_with t').
  Defined.

  Definition InducedHomSetNaturalTransformation :
    SpecializedNaturalTransformation (HomSetFunctor C') (ComposeFunctors (HomSetFunctor D') (F'Op ** F')).
    clear morC morD C D COp DOp FOp F.
    refine (Build_SpecializedNaturalTransformation (HomSetFunctor C') (ComposeFunctors (HomSetFunctor D') (F'Op ** F'))
      (fun sd : (C'Op * C') =>
        @MorphismOf _ _ _ _ _ _ F' _ _ )
      _
    );
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
    unfold SpecializedCategoryIsomorphism; simpl.
    destruct C, D, F; simpl in *; clear C D F.
    *)
End FullFaithful.
