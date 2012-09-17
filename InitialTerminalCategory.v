Require Export SpecializedCategory.
Require Import Common DecidableDiscreteCategory.

Set Implicit Arguments.

Section InitialTerminal.
  Hint Extern 2 (_ = _) => simpl in *; tauto.

  Let decide_empty_equality (a b : Empty_set) : {a = b} + {~a = b} := match a with end.
  Let decide_unit_equality (a b : unit) : {a = b} + {~a = b} := left
    match a with
      | tt =>
        match b with
          | tt => eq_refl
        end
    end.

   Definition InitialCategory : SmallSpecializedCategory _ :=
     Eval cbv beta iota zeta delta [DiscreteCategoryDec DiscreteCategoryDec_Identity DiscreteCategoryDec_Compose] in @DiscreteCategoryDec Empty_set decide_empty_equality.
   Definition TerminalCategory : SmallSpecializedCategory _ :=
     Eval cbv beta iota zeta delta [DiscreteCategoryDec DiscreteCategoryDec_Identity DiscreteCategoryDec_Compose] in @DiscreteCategoryDec unit decide_unit_equality.
End InitialTerminal.
