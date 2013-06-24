Require Export ComputableCategory SigTCategory.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section ComputableCategory.
  Variable I : Type.
  Variable Index2Cat : I -> Category.

  Local Coercion Index2Cat : I >-> Category.

  Let eq_dec_on_cat (C : Category) := forall x y : C, {x = y} + {x <> y}.

  Definition ComputableCategoryDec := @Category_sigT_obj (ComputableCategory Index2Cat) (fun C => eq_dec_on_cat C).
End ComputableCategory.
