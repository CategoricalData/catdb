Require Import Bool Omega Setoid.
Require Export Category.
Require Import Common Functor.

Set Implicit Arguments.

Record SmallCategory := {
  SObject :> Type;
  SMorphism : SObject -> SObject -> Type;

  SIdentity : forall o, SMorphism o o;
  SCompose : forall s d d', SMorphism d d' -> SMorphism s d -> SMorphism s d';

  SAssociativity : forall o1 o2 o3 o4 (m1 : SMorphism o1 o2) (m2 : SMorphism o2 o3) (m3 : SMorphism o3 o4),
    SCompose (SCompose m3 m2) m1 = SCompose m3 (SCompose m2 m1);
  SLeftIdentity : forall a b (f : SMorphism a b), SCompose (SIdentity b) f = f;
  SRightIdentity : forall a b (f : SMorphism a b), SCompose f (SIdentity a) = f
}.

Hint Resolve SAssociativity SLeftIdentity SRightIdentity.

Section SmallCat2Cat.
  Variable C : SmallCategory.

  Definition smallcat2cat : Category.
    refine {| Object := C.(SObject);
      Morphism := C.(SMorphism);
      Compose := C.(SCompose)
    |}; auto.
  Defined.
End SmallCat2Cat.

Coercion smallcat2cat : SmallCategory >-> Category.

Section SmallCat.
  Hint Resolve ComposeFunctorsAssociativity LeftIdentityFunctor RightIdentityFunctor.

  Definition SmallCat : Category.
    refine {| Object := SmallCategory;
      Morphism := @Functor;
      Identity := @IdentityFunctor;
      Compose := @ComposeFunctors
      |}; auto.
  Defined.
End SmallCat.
