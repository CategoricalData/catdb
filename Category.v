Require Export Morphisms.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Class Category := {
  CategoryComposable :> Composable;
  CategoryHasIdentity :> @HasIdentity CategoryComposable;
  CObject :> _ := Object
}.

Section Specialized.
  (* If we pass objects and morphisms around, then we get sort-polymorphism *)
  Variable obj : Type.
  Variable mor : obj -> obj -> Type.

  Record SpecializedCategory := {
    Object' :> _ := obj;

    Identity' : forall x, mor x x;
    Compose' : forall s d d', mor d d' -> mor s d -> mor s d';

    Associativity' : forall o1 o2 o3 o4 (m1 : mor o1 o2) (m2 : mor o2 o3) (m3 : mor o3 o4),
      Compose' m3 (Compose' m2 m1) = Compose' (Compose' m3 m2) m1;
    LeftIdentity' : forall a b (f : mor a b), Compose' (Identity' b) f = f;
    RightIdentity' : forall a b (f : mor a b), Compose' f (Identity' a) = f
  }.

  Variable C : SpecializedCategory.

  Global Instance SpecializedCategory_Composable : Composable :=
    { Object := obj; Morphism := mor; Compose := Compose' C; Associativity := Associativity' C }.

  Global Instance SpecializedCategory_HasIdentity : HasIdentity :=
    { Identity := Identity' C; LeftIdentity := LeftIdentity' C; RightIdentity := RightIdentity' C }.

  Global Instance GeneralizeCategory : Category :=
    { CategoryComposable := SpecializedCategory_Composable; CategoryHasIdentity := SpecializedCategory_HasIdentity }.
End Specialized.

Coercion GeneralizeCategory : SpecializedCategory >-> Category.

Section MkSpecialized.
  (* we can make a specialized category from anything that is composable and has an identity *)
  Variable C : Category.

  Definition SpecializeCategory : SpecializedCategory Morphism :=
    {|
      Identity' := Identity;
      Compose' := @Compose _;
      Associativity' := Associativity;
      LeftIdentity' := LeftIdentity;
      RightIdentity' := RightIdentity
    |}.
End MkSpecialized.

Coercion SpecializeCategory : Category >-> SpecializedCategory.

Ltac present_spcategory' :=
  change @CObject with (fun C => @Object (@CategoryComposable C)) in *.

Ltac present_spcategory := present_spcategory'; simpl in *.
