Require Export Cat SigTCategory.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Cat.
  Let eq_dec_on_cat (C : Category):= forall x y : C, {x = y} + {x <> y}.

  Definition CatDec := Category_sigT_obj Cat (fun C => eq_dec_on_cat C).
End Cat.
