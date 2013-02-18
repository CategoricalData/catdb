Require Export SpecializedCategory Paths.
Require Import Common.

Set Implicit Arguments.

Section PCategory.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Polymorphic Hint Immediate concatenate_associative.
  Polymorphic Hint Rewrite concatenate_associative.

  Polymorphic Definition PathsCategory : @SpecializedCategory V.
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
