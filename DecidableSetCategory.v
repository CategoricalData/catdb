Require Export SetCategory SigTCategory.

Set Implicit Arguments.

(* There is a category [Set], where the objects are sets with decidable equality
   and the morphisms are set morphisms *)
Section CSet.
  Let eq_dec_on T := forall x y : T, {x = y} + {x <> y}.

  Definition TypeCatDec := SpecializedCategory_sigT_obj TypeCat eq_dec_on.
  Definition SetCatDec := SpecializedCategory_sigT_obj SetCat eq_dec_on.
  Definition PropCatDec := SpecializedCategory_sigT_obj PropCat eq_dec_on.
End CSet.
