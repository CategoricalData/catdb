Require Export SmallCategory SmallNaturalTransformation.
Require Import Common CategoryEquality.

Set Implicit Arguments.

Section OppositeCategory.
  Variable C : SmallCategory.

  Definition OppositeSmallCategory : SmallCategory.
    refine {| SObject := @SObject C;
      SMorphism := (fun s d => C.(SMorphism) d s);
      SIdentity := @SIdentity C;
      SCompose := (fun s d d' m1 m2 => @SCompose C d' d s m2 m1)
      |}; abstract (t; eauto).
  Defined.
End OppositeCategory.

Section DualCategories.
  Variables C D : SmallCategory.

  Lemma op_op_id : OppositeSmallCategory (OppositeSmallCategory C) = C.
    scat_eq.
  Qed.
End DualCategories.
