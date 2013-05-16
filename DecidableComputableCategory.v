Require Export ComputableCategory SigTCategory.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Section ComputableCategory.
  Variable I : Type.
  Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i)).

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Let eq_dec_on_cat `(C : @SpecializedCategory objC) := forall x y : objC, {x = y} + {x <> y}.

  Definition ComputableCategoryDec := @SpecializedCategory_sigT_obj _ (@ComputableCategory _ _ Index2Cat) (fun C => eq_dec_on_cat C).
End ComputableCategory.
