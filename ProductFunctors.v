Require Export Products LimitFunctors.
Require Import Common Notations DiscreteCategory DiscreteCategoryFunctors.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Products.
  Context `{C : @SpecializedCategory objC}.
  Variable I : Type.

  Variable HasLimits : forall F : SpecializedFunctor (DiscreteCategory I) C, Limit F.
  Variable HasColimits : forall F : SpecializedFunctor (DiscreteCategory I) C, Colimit F.

  Definition ProductFunctor := LimitFunctor HasLimits.
  Definition CoproductFunctor := ColimitFunctor HasColimits.
End Products.
