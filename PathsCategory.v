Require Export SpecializedCategory Paths.
Require Import Common.

Set Implicit Arguments.

Section PCategory.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Hint Immediate concatenate_associative.
  Hint Rewrite concatenate_associative.

  Definition PathsCategory : @SpecializedCategory V.
    refine (@Build_SpecializedCategory _
                                       (@path V E)
                                       (@NoEdges _ _)
                                       (fun _ _ _ p p' => concatenate p' p)
                                       _
                                       _
                                       _);
    abstract t_with t'.
  Defined.
End PCategory.
