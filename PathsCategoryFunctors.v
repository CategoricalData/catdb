Require Import FunctionalExtensionality.
Require Export PathsCategory Functor SetCategory ComputableCategory SmallCat NaturalTransformation.
Require Import Common Adjoint.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Section FunctorFromPaths.
  Variable V : Type.
  Variable E : V -> V -> Type.
  Context `(D : @SpecializedCategory objD).
  Variable objOf : V -> objD.
  Variable morOf : forall s d, E s d -> Morphism' D (objOf s) (objOf d).

  Polymorphic Fixpoint path_compose s d (m : Morphism' (PathsCategory E) s d) : Morphism' D (objOf s) (objOf d) :=
    match m with
      | NoEdges => Identity _
      | AddEdge _ _ m' e => Compose (morOf e) (path_compose m')
    end.

  Polymorphic Lemma FunctorFromPaths_FCompositionOf s d d' (p1 : path E s d) (p2 : path E d d') :
    path_compose (concatenate p1 p2) = Compose (path_compose p2) (path_compose p1).
  Proof.
    induction p2; t_with t'; autorewrite with morphism; reflexivity.
  Qed.

  Polymorphic Definition FunctorFromPaths : SpecializedFunctor (PathsCategory E) D.
  Proof.
    refine {|
      ObjectOf' := objOf;
      MorphismOf' := path_compose;
      FCompositionOf' := FunctorFromPaths_FCompositionOf
    |};
    present_spcategory; abstract intuition.
  Defined.
End FunctorFromPaths.

Section Underlying.
  Polymorphic Definition UnderlyingGraph `(C : @SpecializedCategory objC) := @PathsCategory objC (Morphism C).
End Underlying.
