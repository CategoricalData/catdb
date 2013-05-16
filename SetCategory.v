Require Export SpecializedCategory Functor.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Notation IndexedCatOf obj coerce := (@Build_SpecializedCategory obj
                                                                (fun s d => coerce s -> coerce d)
                                                                (fun _ => (fun x => x))
                                                                (fun _ _ _ f g => (fun x => f (g x)))
                                                                (fun _ _ _ _ _ _ f => eq_refl)
                                                                (fun _ _ f => eq_refl : (fun x => f x) = f)
                                                                (fun _ _ f => eq_refl : (fun x => f x) = f)
                                    ).

Notation CatOf obj := (IndexedCatOf obj (fun x => x)).
Notation CoercedCatOf obj T := (IndexedCatOf obj (fun x => x : T)).

(* There is a category [Set], where the objects are sets and the morphisms are set morphisms *)
Section CSet.
  Definition TypeCat : @SpecializedCategory Type := Eval cbv beta in CatOf Type.
  Definition SetCat : @SpecializedCategory Set := Eval cbv beta in CatOf Set.
  Definition PropCat : @SpecializedCategory Prop := Eval cbv beta in CatOf Prop.

  Definition IndexedTypeCat (Index : Type) (Index2Object : Index -> Type) := Eval cbv beta in IndexedCatOf Index Index2Object.
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

  Local Notation BuildFunctor C D F :=
    (Build_SpecializedFunctor C D
                              (fun x => ObjectOf F%functor x)
                              (fun s d m => MorphismOf F%functor m)
                              (fun s d d' m m' => FCompositionOf F%functor s d d' m m')
                              (fun x => FIdentityOf F%functor x)).

  Definition SpecializedFunctorTo_Prop2Set (F : SpecializedFunctorToProp C) : SpecializedFunctorToSet C := BuildFunctor C SetCat F.
  Definition SpecializedFunctorTo_Prop2Type (F : SpecializedFunctorToProp C) : SpecializedFunctorToType C := BuildFunctor C TypeCat F.
  Definition SpecializedFunctorTo_Set2Type (F : SpecializedFunctorToSet C) : SpecializedFunctorToType C := BuildFunctor C TypeCat F.

  Definition SpecializedFunctorFrom_Set2Prop (F : SpecializedFunctorFromSet C) : SpecializedFunctorFromProp C := BuildFunctor PropCat C F.
  Definition SpecializedFunctorFrom_Type2Prop (F : SpecializedFunctorFromType C) : SpecializedFunctorFromProp C := BuildFunctor PropCat C F.
  Definition SpecializedFunctorFrom_Type2Set (F : SpecializedFunctorFromType C) : SpecializedFunctorFromSet C := BuildFunctor SetCat C F.
End SetCoercions.

Coercion SpecializedFunctorTo_Prop2Set : SpecializedFunctorToProp >-> SpecializedFunctorToSet.
Coercion SpecializedFunctorTo_Prop2Type : SpecializedFunctorToProp >-> SpecializedFunctorToType.
Coercion SpecializedFunctorTo_Set2Type : SpecializedFunctorToSet >-> SpecializedFunctorToType.
Coercion SpecializedFunctorFrom_Set2Prop : SpecializedFunctorFromSet >-> SpecializedFunctorFromProp.
Coercion SpecializedFunctorFrom_Type2Prop : SpecializedFunctorFromType >-> SpecializedFunctorFromProp.
Coercion SpecializedFunctorFrom_Type2Set : SpecializedFunctorFromType >-> SpecializedFunctorFromSet.

(* There is a category [Set*], where the objects are sets with a distinguished elements and the morphisms are set morphisms *)
Section PointedSet.
  Local Notation PointedCatOf obj := (let pointed_set_fun_eta := ((fun _ _ _ _ _ => eq_refl) :
                                                                    forall {T : Type} {proj : T -> Type} (a b : T) (f : proj a -> proj b),
                                                                      (fun x => f x) = f) in
                                      @Build_SpecializedCategory { A : obj & A }
                                                                 (fun s d => (projT1 s) -> (projT1 d))
                                                                 (fun _ => (fun x => x))
                                                                 (fun _ _ _ f g => (fun x => f (g x)))
                                                                 (fun _ _ _ _ _ _ _ => eq_refl)
                                                                 (@pointed_set_fun_eta { A : obj & A } (@projT1 obj _))
                                                                 (@pointed_set_fun_eta { A : obj & A } (@projT1 obj _))).

  Local Notation PointedCatProjectionOf obj := (Build_SpecializedFunctor (PointedCatOf obj) (CatOf obj)
                                                                         (fun c => projT1 c)
                                                                         (fun s d (m : (projT1 s) -> (projT1 d)) => m)
                                                                         (fun _ _ _ _ _ => eq_refl)
                                                                         (fun _ => eq_refl)).

  Definition PointedTypeCat : @SpecializedCategory { A : Type & A } := Eval cbv beta zeta in PointedCatOf Type.
  Definition PointedTypeProjection : SpecializedFunctor PointedTypeCat TypeCat := PointedCatProjectionOf Type.
  Definition PointedSetCat : @SpecializedCategory { A : Set & A } := Eval cbv beta zeta in PointedCatOf Set.
  Definition PointedSetProjection : SpecializedFunctor PointedSetCat SetCat := PointedCatProjectionOf Set.
  Definition PointedPropCat : @SpecializedCategory { A : Prop & A } := Eval cbv beta zeta in PointedCatOf Prop.
  Definition PointedPropProjection : SpecializedFunctor PointedPropCat PropCat := PointedCatProjectionOf Prop.
End PointedSet.
