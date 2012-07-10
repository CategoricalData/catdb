Require Export SpecializedCategory.
Require Import Common.

(* There is a category [Set], where the objects are sets and the morphisms are set morphisms *)
Section CSet.
  Definition TypeCat : @SpecializedCategory Type (fun s d => s -> d).
    refine {|
      Compose' := fun _ _ _ f g => (fun x => f (g x));
      Identity' := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.

  Definition SetCat : @SpecializedCategory Set (fun s d => s -> d).
    refine {|
      Compose' := fun _ _ _ f g => (fun x => f (g x));
      Identity' := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.

  Definition PropCat : @SpecializedCategory Prop (fun s d => s -> d).
    refine {|
      Compose' := fun _ _ _ f g => (fun x => f (g x));
      Identity' := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.
End CSet.

(* There is a category [Set*], where the objects are sets with a distinguished elements and the morphisms are set morphisms *)
Section PointedSet.
  Definition PointedTypeCat : @SpecializedCategory { A : Type & A } (fun s d => (projT1 s) -> (projT1 d)).
    refine {|
      Compose' := fun _ _ _ f g => (fun x => f (g x));
      Identity' := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.

  Definition PointedSetCat : @SpecializedCategory { A : Set & A } (fun s d => (projT1 s) -> (projT1 d)).
    refine {|
      Compose' := fun _ _ _ f g => (fun x => f (g x));
      Identity' := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.

  Definition PointedPropCat : @SpecializedCategory { A : Prop & A } (fun s d => (projT1 s) -> (projT1 d)).
    refine {|
      Compose' := fun _ _ _ f g => (fun x => f (g x));
      Identity' := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.
End PointedSet.
