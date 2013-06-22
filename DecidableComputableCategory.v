Require Export ComputableCategory SigTCategory.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section ComputableCategory.
  Variable I : Type.
  Variable Index2Cat : I -> SpecializedCategory.

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Let eq_dec_on_cat `(C : SpecializedCategory) := forall x y : C, {x = y} + {x <> y}.

  Definition ComputableCategoryDec := @SpecializedCategory_sigT_obj (ComputableCategory Index2Cat) (fun C => eq_dec_on_cat C).
End ComputableCategory.
