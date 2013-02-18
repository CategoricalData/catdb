Require Export Products LimitFunctors.
Require Import Common Notations DiscreteCategory DiscreteCategoryFunctors.

Set Implicit Arguments.

Generalizable All Variables.

Section Products.
  Context `{C : @SpecializedCategory objC}.
  Variable I : Type.

  Variable HasLimits : forall F : SpecializedFunctor (DiscreteCategory I) C, Limit F.
  Variable HasColimits : forall F : SpecializedFunctor (DiscreteCategory I) C, Colimit F.

  Polymorphic Definition ProductFunctor := LimitFunctor HasLimits.
  Polymorphic Definition CoproductFunctor := ColimitFunctor HasColimits.
End Products.
