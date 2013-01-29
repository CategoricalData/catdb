Require Export SpecializedCategory Functor.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

(* There is a category [Set], where the objects are sets and the morphisms are set morphisms *)
Section CSet.
  Local Ltac build_set_cat :=
    match goal with
      | [ |- SpecializedCategory ?obj ] =>
        refine (@Build_SpecializedCategory obj
          (fun s d => s -> d)
          (fun _ => (fun x => x))
          (fun _ _ _ f g => (fun x => f (g x)))
          _
          _
          _
        )
    end;
    abstract (firstorder; etransitivity; eauto with morphism; t).

  Definition TypeCat : @SpecializedCategory Type. build_set_cat. Defined.
  Definition SetCat : @SpecializedCategory Set. build_set_cat. Defined.
  Definition PropCat : @SpecializedCategory Prop. build_set_cat. Defined.
End CSet.

Section SetCoercionsDefinitions.
  Context `(C : @SpecializedCategory objC).

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
  Context `(C : @SpecializedCategory objC).

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
  Local Ltac build_pointed_set_cat :=
    match goal with
      | [ |- SpecializedCategory ?obj ] =>
        refine (@Build_SpecializedCategory obj
          (fun s d => (projT1 s) -> (projT1 d))
          (fun _ => (fun x => x))
          (fun _ _ _ f g => (fun x => f (g x)))
          _
          _
          _
        )
    end;
    abstract (firstorder; etransitivity; eauto; t).

  Local Ltac build_pointed_set_cat_projection :=
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (fun c => projT1 c)
          (fun s d (m : (projT1 s) -> (projT1 d)) => m)
          _
          _
        )
    end;
    abstract t.

  Definition PointedTypeCat : @SpecializedCategory { A : Type & A }. build_pointed_set_cat. Defined.
  Definition PointedTypeProjection : SpecializedFunctor PointedTypeCat TypeCat. build_pointed_set_cat_projection. Defined.
  Definition PointedSetCat : @SpecializedCategory { A : Set & A }. build_pointed_set_cat. Defined.
  Definition PointedSetProjection : SpecializedFunctor PointedSetCat SetCat. build_pointed_set_cat_projection. Defined.
  Definition PointedPropCat : @SpecializedCategory { A : Prop & A }. build_pointed_set_cat. Defined.
  Definition PointedPropProjection : SpecializedFunctor PointedPropCat PropCat. build_pointed_set_cat_projection. Defined.
End PointedSet.
