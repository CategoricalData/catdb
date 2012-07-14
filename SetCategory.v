Require Export Category Functor.
Require Import Common.

(* There is a category [Set], where the objects are sets and the morphisms are set morphisms *)
Section CSet.
  Definition TypeCat : Category.
    refine {| Object := Type;
      Morphism := fun s d => s -> d;
      Compose := fun _ _ _ f g => (fun x => f (g x));
      Identity := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.

  Definition SetCat : Category.
    refine {| Object := Set;
      Morphism := fun s d => s -> d;
      Compose := fun _ _ _ f g => (fun x => f (g x));
      Identity := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.

  Definition PropCat : Category.
    refine {| Object := Prop;
      Morphism := fun s d => s -> d;
      Compose := fun _ _ _ f g => (fun x => f (g x));
      Identity := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.
End CSet.

Section SetCoercionsDefinitions.
  Variable C : Category.

  Definition FunctorToProp := Functor C PropCat.
  Definition FunctorToSet := Functor C SetCat.
  Definition FunctorToType := Functor C TypeCat.

  Definition FunctorFromProp := Functor PropCat C.
  Definition FunctorFromSet := Functor SetCat C.
  Definition FunctorFromType := Functor TypeCat C.
End SetCoercionsDefinitions.

Identity Coercion FunctorToProp_Id : FunctorToProp >-> Functor.
Identity Coercion FunctorToSet_Id : FunctorToSet >-> Functor.
Identity Coercion FunctorToType_Id : FunctorToType >-> Functor.
Identity Coercion FunctorFromProp_Id : FunctorFromProp >-> Functor.
Identity Coercion FunctorFromSet_Id : FunctorFromSet >-> Functor.
Identity Coercion FunctorFromType_Id : FunctorFromType >-> Functor.

Section SetCoercions.
  Variable C : Category.

  Local Ltac build_functor := hnf in *;
    match goal with
      | [ F : Functor _ _ |- Functor ?C ?D ] =>
        exact (Build_Functor C D
          F.(ObjectOf)
          F.(MorphismOf)
          F.(FCompositionOf)
          F.(FIdentityOf)
        )
    end.

  Definition FunctorTo_Prop2Set (F : FunctorToProp C) : FunctorToSet C. build_functor. Defined.
  Definition FunctorTo_Prop2Type (F : FunctorToProp C) : FunctorToType C. build_functor. Defined.
  Definition FunctorTo_Set2Type (F : FunctorToSet C) : FunctorToType C. build_functor. Defined.

  Definition FunctorFrom_Set2Prop (F : FunctorFromSet C) : FunctorFromProp C. build_functor. Defined.
  Definition FunctorFrom_Type2Prop (F : FunctorFromType C) : FunctorFromProp C. build_functor. Defined.
  Definition FunctorFrom_Type2Set (F : FunctorFromType C) : FunctorFromSet C. build_functor. Defined.
End SetCoercions.

Coercion FunctorTo_Prop2Set : FunctorToProp >-> FunctorToSet.
Coercion FunctorTo_Prop2Type : FunctorToProp >-> FunctorToType.
Coercion FunctorTo_Set2Type : FunctorToSet >-> FunctorToType.
Coercion FunctorFrom_Set2Prop : FunctorFromSet >-> FunctorFromProp.
Coercion FunctorFrom_Type2Prop : FunctorFromType >-> FunctorFromProp.
Coercion FunctorFrom_Type2Set : FunctorFromType >-> FunctorFromSet.

(* There is a category [Set*], where the objects are sets with a distinguished elements and the morphisms are set morphisms *)
Section PointedSet.
  Definition PointedTypeCat : Category.
    refine {| Object := { A : Type & A };
      Morphism := (fun s d => projT1 s -> projT1 d);
      Compose := (fun _ _ _ f g => (fun x => f (g x)));
      Identity := (fun _ => (fun x => x))
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.

  Definition PointedTypeProjection : Functor PointedTypeCat TypeCat.
    refine {| ObjectOf := (fun c : PointedTypeCat => projT1 c : TypeCat);
      MorphismOf := (fun s d (m : projT1 s -> projT1 d) => m)
    |}; abstract t.
  Defined.

  Definition PointedSetCat : Category.
    refine {| Object := { A : Set & A };
      Morphism := (fun s d => projT1 s -> projT1 d);
      Compose := (fun _ _ _ f g => (fun x => f (g x)));
      Identity := (fun _ => (fun x => x))
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.

  Definition PointedSetProjection : Functor PointedSetCat SetCat.
    refine {| ObjectOf := (fun c : PointedSetCat => projT1 c : SetCat);
      MorphismOf := (fun s d (m : projT1 s -> projT1 d) => m)
    |}; abstract t.
  Defined.

  Definition PointedPropCat : Category.
    refine {| Object := { A : Prop & A };
      Morphism := (fun s d => projT1 s -> projT1 d);
      Compose := (fun _ _ _ f g => (fun x => f (g x)));
      Identity := (fun _ => (fun x => x))
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.

  Definition PointedPropProjection : Functor PointedPropCat PropCat.
    refine {| ObjectOf := (fun c : PointedPropCat => projT1 c : PropCat);
      MorphismOf := (fun s d (m : projT1 s -> projT1 d) => m)
    |}; abstract t.
  Defined.
End PointedSet.
