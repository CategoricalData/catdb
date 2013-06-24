Require Export Category Paths.
Require Import Common.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section PCategory.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Hint Immediate concatenate_associative.
  Hint Rewrite concatenate_associative.

  Definition PathsCategory : Category.
    refine (@Build_Category V
                                       (@path V E)
                                       (@NoEdges _ _)
                                       (fun _ _ _ p p' => concatenate p' p)
                                       _
                                       _
                                       _);
    abstract t_with t'.
  Defined.
End PCategory.
