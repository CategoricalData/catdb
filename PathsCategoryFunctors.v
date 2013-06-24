Require Import FunctionalExtensionality.
Require Export PathsCategory Functor SetCategory ComputableCategory Cat NaturalTransformation.
Require Import Common Adjoint.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section FunctorFromPaths.
  Variable V : Type.
  Variable E : V -> V -> Type.
  Variable D : Category.
  Variable objOf : V -> D.
  Variable morOf : forall s d, E s d -> Morphism D (objOf s) (objOf d).

  Fixpoint path_compose s d (m : Morphism (PathsCategory E) s d) : Morphism D (objOf s) (objOf d) :=
    match m with
      | NoEdges => Identity _
      | AddEdge _ _ m' e => Compose (morOf e) (path_compose m')
    end.

  Lemma FunctorFromPaths_FCompositionOf s d d' (p1 : path E s d) (p2 : path E d d') :
    path_compose (concatenate p1 p2) = Compose (path_compose p2) (path_compose p1).
  Proof.
    induction p2; t_with t'; autorewrite with morphism; reflexivity.
  Qed.

  Definition FunctorFromPaths : Functor (PathsCategory E) D.
  Proof.
    refine (Build_Functor (PathsCategory E) D
                                     objOf
                                     path_compose
                                     FunctorFromPaths_FCompositionOf
                                     _);
    abstract intuition.
  Defined.
End FunctorFromPaths.

Section Underlying.
  Definition UnderlyingGraph (C : Category) := @PathsCategory _ (Morphism C).
End Underlying.
