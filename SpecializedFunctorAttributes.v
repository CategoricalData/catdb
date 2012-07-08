Require Import FunctionalExtensionality.
Require Export SpecializedFunctor.
Require Import Common SpecializedHom SpecializedDuals SpecializedProductFunctor SpecializedNaturalTransformation SpecializedSetCategory.

Set Implicit Arguments.

Local Infix "*" := ProductSpecializedFunctor.

Section FullFaithful.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.
  Variable F : SpecializedFunctor C D.
  Let COp := OppositeSpecializedCategory C.
  Let DOp := OppositeSpecializedCategory D.
  Let FOp := OppositeSpecializedFunctor F.

  Hint Rewrite FCompositionOf.

  Definition InducedHomSpecializedNaturalTransformation :
    SpecializedNaturalTransformation (HomSpecializedFunctor C) (ComposeSpecializedFunctors (HomSpecializedFunctor D) (FOp * F)).
  (* Gahhh, type signatures and casting *)
    refine {| ComponentsOf' := (fun sd : (ProductSpecializedCategory COp C) =>
      (fun m : Morphism C (fst sd) (snd sd) =>
        F.(MorphismOf) m) : Morphism TypeCat ((HomSpecializedFunctor C) _) ((ComposeSpecializedFunctors (HomSpecializedFunctor D) ((OppositeSpecializedFunctor F) * F)) _))
      |}; abstract (simpl; intros; destruct_type @prod; simpl in *; repeat (apply functional_extensionality_dep; intro); t_with t').
  Defined.

  (* We really want surjective/injective here, but we only have epi/mono.
     They're equivalent in the category of sets.  Are they equivalent in the
     category of [Type]s? *)
  Definition SpecializedFunctorFull := forall x y : C, Epimorphism (InducedHomSpecializedNaturalTransformation.(ComponentsOf) (x, y)).
  Definition SpecializedFunctorFaithful := forall x y : C, Monomorphism (InducedHomSpecializedNaturalTransformation.(ComponentsOf) (x, y)).

  Definition SpecializedFunctorFullyFaithful := forall x y : C, CategoryIsomorphism (InducedHomSpecializedNaturalTransformation.(ComponentsOf) (x, y)).

  Lemma SpecializedFunctorFullyFaithful_split : SpecializedFunctorFullyFaithful -> SpecializedFunctorFull /\ SpecializedFunctorFaithful.
    unfold SpecializedFunctorFullyFaithful, SpecializedFunctorFull, SpecializedFunctorFaithful; intro H; split; intros;
      apply iso_is_epi || apply iso_is_mono; trivial.
  Qed.

(*
   (* Depends on injective + surjective -> isomorphism, and epi = surj, mono = inj *)
  Definition SpecializedFunctorFullFaithful_and : SpecializedFunctorFull /\ SpecializedFunctorFaithful -> SpecializedFunctorFullyFaithful.
    intro H; destruct H as [ e m ].
    unfold SpecializedFunctorFullyFaithful, SpecializedFunctorFull, SpecializedFunctorFaithful in *.
    intros x y; specialize (e x y); specialize (m x y).
    unfold Epimorphism, Monomorphism in *; simpl in *.
    unfold SpecializedCategoryIsomorphism; simpl.
    destruct C, D, F; simpl in *; clear C D F.
    *)
End FullFaithful.
