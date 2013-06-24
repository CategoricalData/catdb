Require Export Category.
Require Import Bool.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section BoolCat.
  Let obj := bool.
  Let mor s d := if (implb s d) then unit else Empty_set.

  Local Ltac t0 := unfold obj, mor in *; hnf in *; simpl in *; try subst obj mor.
  Local Ltac t1 := intros;
    repeat match goal with
             | [ |- unit ] => exact tt
             | [ H : Empty_set |- _ ] => destruct H
             | [ H : bool |- _ ] => destruct H; simpl in *
           end; trivial.
  Local Ltac t := t0; abstract t1.

  Definition BoolCat_Compose s d d' (m1 : mor d d') (m2 : mor s d) : mor s d'.
    t.
  Defined.

  Definition BoolCat_Identity x : mor x x := if x return mor x x then tt else tt.

  Global Arguments BoolCat_Compose [s d d'] m1 m2 : simpl never.
  Global Arguments BoolCat_Identity x : simpl never.

  Definition BoolCat : Category.
    refine (@Build_Category bool
                                       mor
                                       BoolCat_Identity
                                       BoolCat_Compose
                                       _
                                       _
                                       _);
    t.
  Defined.
End BoolCat.
