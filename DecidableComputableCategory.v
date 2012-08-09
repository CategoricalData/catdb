Require Export ComputableCategory SigTCategory.

Set Implicit Arguments.

Generalizable All Variables.

Section ComputableCategory.
  Variable I : Type.
  Context `(Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i) (@Index2Morphism i)).

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Let eq_dec_on_cat `(C : @SpecializedCategory objC morC) := forall x y : objC, {x = y} + {x <> y}.

  Definition ComputableCategoryDec := @SpecializedCategory_sigT_obj _ _ (@ComputableCategory _ _ _ Index2Cat) (fun C => eq_dec_on_cat C).
End ComputableCategory.
