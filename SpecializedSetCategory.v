Require Export SpecializedCategory SpecializedFunctor.
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

  Definition PointedTypeProjection : SpecializedFunctor PointedTypeCat TypeCat.
    refine {| ObjectOf' := (fun c => projT1 c);
      MorphismOf' := (fun s d (m : (projT1 s) -> (projT1 d)) => m)
    |}; abstract t.
  Defined.

  Definition PointedSetCat : @SpecializedCategory { A : Set & A } (fun s d => (projT1 s) -> (projT1 d)).
    refine {|
      Compose' := fun _ _ _ f g => (fun x => f (g x));
      Identity' := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.

  Definition PointedSetProjection : SpecializedFunctor PointedSetCat SetCat.
    refine {| ObjectOf' := (fun c : { A : Set & A } => projT1 c);
      MorphismOf' := (fun s d (m : (projT1 s) -> (projT1 d)) => m)
    |}; abstract t.
  Defined.

  Definition PointedPropCat : @SpecializedCategory { A : Prop & A } (fun s d => (projT1 s) -> (projT1 d)).
    refine {|
      Compose' := fun _ _ _ f g => (fun x => f (g x));
      Identity' := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.

  Definition PointedPropProjection : SpecializedFunctor PointedPropCat PropCat.
    refine {| ObjectOf' := (fun c : { A : Prop & A } => projT1 c);
      MorphismOf' := (fun s d (m : (projT1 s) -> (projT1 d)) => m)
    |}; abstract t.
  Defined.
End PointedSet.
