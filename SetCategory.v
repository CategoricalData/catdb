Require Export SpecializedCategory Functor.
Require Import Common.

Set Implicit Arguments.

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

Section SetCoercionsDefinitions.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Definition SpecializedFunctorToProp := SpecializedFunctor C PropCat.
  Definition SpecializedFunctorToSet := SpecializedFunctor C SetCat.
  Definition SpecializedFunctorToType := SpecializedFunctor C TypeCat.

  Definition SpecializedFunctorFromProp := SpecializedFunctor PropCat C.
  Definition SpecializedFunctorFromSet := SpecializedFunctor SetCat C.
  Definition SpecializedFunctorFromType := SpecializedFunctor TypeCat C.
End SetCoercionsDefinitions.

Identity Coercion SpecializedFunctorToProp_Id : SpecializedFunctorToProp >-> SpecializedFunctor.
Identity Coercion SpecializedFunctorToSet_Id : SpecializedFunctorToSet >-> SpecializedFunctor.
Identity Coercion SpecializedFunctorToType_Id : SpecializedFunctorToType >-> SpecializedFunctor.
Identity Coercion SpecializedFunctorFromProp_Id : SpecializedFunctorFromProp >-> SpecializedFunctor.
Identity Coercion SpecializedFunctorFromSet_Id : SpecializedFunctorFromSet >-> SpecializedFunctor.
Identity Coercion SpecializedFunctorFromType_Id : SpecializedFunctorFromType >-> SpecializedFunctor.

Section SetCoercions.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Local Ltac build_functor := hnf in *;
    match goal with
      | [ F : SpecializedFunctor _ _ |- SpecializedFunctor ?C ?D ] =>
        exact (Build_SpecializedFunctor C D
          F.(ObjectOf')
          F.(MorphismOf')
          F.(FCompositionOf')
          F.(FIdentityOf')
        )
    end.

  Definition SpecializedFunctorTo_Prop2Set (F : SpecializedFunctorToProp C) : SpecializedFunctorToSet C. build_functor. Defined.
  Definition SpecializedFunctorTo_Prop2Type (F : SpecializedFunctorToProp C) : SpecializedFunctorToType C. build_functor. Defined.
  Definition SpecializedFunctorTo_Set2Type (F : SpecializedFunctorToSet C) : SpecializedFunctorToType C. build_functor. Defined.

  Definition SpecializedFunctorFrom_Set2Prop (F : SpecializedFunctorFromSet C) : SpecializedFunctorFromProp C. build_functor. Defined.
  Definition SpecializedFunctorFrom_Type2Prop (F : SpecializedFunctorFromType C) : SpecializedFunctorFromProp C. build_functor. Defined.
  Definition SpecializedFunctorFrom_Type2Set (F : SpecializedFunctorFromType C) : SpecializedFunctorFromSet C. build_functor. Defined.
End SetCoercions.

Coercion SpecializedFunctorTo_Prop2Set : SpecializedFunctorToProp >-> SpecializedFunctorToSet.
Coercion SpecializedFunctorTo_Prop2Type : SpecializedFunctorToProp >-> SpecializedFunctorToType.
Coercion SpecializedFunctorTo_Set2Type : SpecializedFunctorToSet >-> SpecializedFunctorToType.
Coercion SpecializedFunctorFrom_Set2Prop : SpecializedFunctorFromSet >-> SpecializedFunctorFromProp.
Coercion SpecializedFunctorFrom_Type2Prop : SpecializedFunctorFromType >-> SpecializedFunctorFromProp.
Coercion SpecializedFunctorFrom_Type2Set : SpecializedFunctorFromType >-> SpecializedFunctorFromSet.

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
