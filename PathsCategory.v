Require Export SpecializedCategory Paths.
Require Import Common.

Set Implicit Arguments.

Section PCategory.
  Variable V : Type.
  Variable E : V -> V -> Type.

  Hint Immediate concatenate_associative.
  Hint Rewrite concatenate_associative.

  Definition PathsCategory : @SpecializedCategory V.
  Proof.
    refine {|
      Morphism' := @path V E;
      Compose' := (fun _ _ _ p p' => concatenate p' p);
      Identity' := @NoEdges _ _
    |};
    abstract t_with t'.
  Defined.
End PCategory.
