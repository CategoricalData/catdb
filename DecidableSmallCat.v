Require Export SmallCat SigTCategory.

Set Implicit Arguments.

Generalizable All Variables.

Section SmallCat.
  Let eq_dec_on_cat `(C : @SpecializedCategory objC morC) := forall x y : objC, {x = y} + {x <> y}.

  Definition SmallCatDec := @SpecializedCategory_sigT_obj _ _ SmallCat (fun C => eq_dec_on_cat C).
  Definition LocallySmallCatDec := @SpecializedCategory_sigT_obj _ _ LocallySmallCat (fun C => eq_dec_on_cat C).
End SmallCat.
