Require Export Category.
Require Import Common.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section DCategory.
  Variable O : Type.

  Local Ltac simpl_eq := subst_body; hnf in *; simpl in *; intros; destruct_type @inhabited; simpl in *;
    repeat constructor;
      repeat subst;
        auto;
          simpl_transitivity.

  Let DiscreteCategory_Morphism (s d : O) := s = d.

  Definition DiscreteCategory_Compose (s d d' : O) (m : DiscreteCategory_Morphism d d') (m' : DiscreteCategory_Morphism s d) :
    DiscreteCategory_Morphism s d'.
    simpl_eq.
  Defined.

  Definition DiscreteCategory_Identity o : DiscreteCategory_Morphism o o.
    simpl_eq.
  Defined.

  Global Arguments DiscreteCategory_Compose [s d d'] m m' /.
  Global Arguments DiscreteCategory_Identity o /.

  Definition DiscreteCategory : Category.
    refine (@Build_Category O
                                       DiscreteCategory_Morphism
                                       DiscreteCategory_Identity
                                       DiscreteCategory_Compose
                                       _
                                       _
                                       _);
    abstract (
        unfold DiscreteCategory_Compose, DiscreteCategory_Identity;
        simpl_eq
      ).
  Defined.
End DCategory.
