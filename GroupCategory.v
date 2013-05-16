Require Export SpecializedCategory Group.
Require Import Notations ComputableCategory SetCategory.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Ltac destruct_first_if_not_second a b :=
  (constr_eq a b; fail 1) || (let H := fresh in set (H := a : unit) in *; destruct H).

Ltac destruct_singleton_constructor c :=
  let t := type of c in
  repeat match goal with
           | [ H : t |- _ ] => destruct H
           | [ H : context[?e] |- _ ] => destruct_first_if_not_second e c
           | [ |- context[?e] ] => destruct_first_if_not_second e c
         end.

Ltac destruct_units := destruct_singleton_constructor tt.
Ltac destruct_Trues := destruct_singleton_constructor I.

Section as_category.
  Definition CategoryOfGroup (G : Group) : SpecializedCategory unit.
    refine (@Build_SpecializedCategory unit
                                       (fun _ _ => G)
                                       (fun _ => @GroupIdentity G)
                                       (fun _ _ _ => @GroupOperation G)
                                       _
                                       _
                                       _);
    abstract (destruct G; intuition).
  Defined.
End as_category.

Coercion CategoryOfGroup : Group >-> SpecializedCategory.

Section category_of_groups.
  Definition GroupCat : SpecializedCategory Group
    := Eval unfold ComputableCategory in ComputableCategory _ CategoryOfGroup.
End category_of_groups.

Section forgetful_functor.
  Definition GroupForgetfulFunctor : SpecializedFunctor GroupCat TypeCat.
    refine (Build_SpecializedFunctor GroupCat TypeCat
                                     GroupObjects
                                     (fun s d m => MorphismOf m (s := tt) (d := tt))
                                     _
                                     _);
    simpl; abstract (intros; destruct_units; reflexivity).
  Defined.
End forgetful_functor.
