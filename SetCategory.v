Require Export Category Functor.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Notation IndexedCatOf obj coerce := (@Build_Category obj
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
  Definition TypeCat : Category := Eval cbv beta in CatOf Type.
  Definition SetCat : Category := Eval cbv beta in CatOf Set.
  Definition PropCat : Category := Eval cbv beta in CatOf Prop.

  Definition IndexedTypeCat (Index : Type) (Index2Object : Index -> Type) := Eval cbv beta in IndexedCatOf Index Index2Object.
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

  Local Notation BuildFunctor C D F :=
    (Build_Functor C D
                              (fun x => ObjectOf F%functor x)
                              (fun s d m => MorphismOf F%functor m)
                              (fun s d d' m m' => FCompositionOf F%functor s d d' m m')
                              (fun x => FIdentityOf F%functor x)).

  Definition FunctorTo_Prop2Set (F : FunctorToProp C) : FunctorToSet C := BuildFunctor C SetCat F.
  Definition FunctorTo_Prop2Type (F : FunctorToProp C) : FunctorToType C := BuildFunctor C TypeCat F.
  Definition FunctorTo_Set2Type (F : FunctorToSet C) : FunctorToType C := BuildFunctor C TypeCat F.

  Definition FunctorFrom_Set2Prop (F : FunctorFromSet C) : FunctorFromProp C := BuildFunctor PropCat C F.
  Definition FunctorFrom_Type2Prop (F : FunctorFromType C) : FunctorFromProp C := BuildFunctor PropCat C F.
  Definition FunctorFrom_Type2Set (F : FunctorFromType C) : FunctorFromSet C := BuildFunctor SetCat C F.
End SetCoercions.

Coercion FunctorTo_Prop2Set : FunctorToProp >-> FunctorToSet.
Coercion FunctorTo_Prop2Type : FunctorToProp >-> FunctorToType.
Coercion FunctorTo_Set2Type : FunctorToSet >-> FunctorToType.
Coercion FunctorFrom_Set2Prop : FunctorFromSet >-> FunctorFromProp.
Coercion FunctorFrom_Type2Prop : FunctorFromType >-> FunctorFromProp.
Coercion FunctorFrom_Type2Set : FunctorFromType >-> FunctorFromSet.

(* There is a category [Set*], where the objects are sets with a distinguished elements and the morphisms are set morphisms *)
Section PointedSet.
  Local Notation PointedCatOf obj := (let pointed_set_fun_eta := ((fun _ _ _ _ _ => eq_refl) :
                                                                    forall {T : Type} {proj : T -> Type} (a b : T) (f : proj a -> proj b),
                                                                      (fun x => f x) = f) in
                                      @Build_Category { A : obj & A }
                                                                 (fun s d => (projT1 s) -> (projT1 d))
                                                                 (fun _ => (fun x => x))
                                                                 (fun _ _ _ f g => (fun x => f (g x)))
                                                                 (fun _ _ _ _ _ _ _ => eq_refl)
                                                                 (@pointed_set_fun_eta { A : obj & A } (@projT1 obj _))
                                                                 (@pointed_set_fun_eta { A : obj & A } (@projT1 obj _))).

  Local Notation PointedCatProjectionOf obj := (Build_Functor (PointedCatOf obj) (CatOf obj)
                                                                         (fun c => projT1 c)
                                                                         (fun s d (m : (projT1 s) -> (projT1 d)) => m)
                                                                         (fun _ _ _ _ _ => eq_refl)
                                                                         (fun _ => eq_refl)).

  Definition PointedTypeCat : Category := Eval cbv beta zeta in PointedCatOf Type.
  Definition PointedTypeProjection : Functor PointedTypeCat TypeCat := PointedCatProjectionOf Type.
  Definition PointedSetCat : Category := Eval cbv beta zeta in PointedCatOf Set.
  Definition PointedSetProjection : Functor PointedSetCat SetCat := PointedCatProjectionOf Set.
  Definition PointedPropCat : Category := Eval cbv beta zeta in PointedCatOf Prop.
  Definition PointedPropProjection : Functor PointedPropCat PropCat := PointedCatProjectionOf Prop.
End PointedSet.
