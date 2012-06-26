Require Import Bool Omega Setoid.
Require Export SmallCategory Category.
Require Import Common Functor.

Set Implicit Arguments.

(**
   Quoting Wikipedia:
   A locally small category is a category such that for all objects
   [a] and [b], the hom-class hom(a, b) is a set, called a homset.

   I don't impose this restriction, because I want to see if I
   can make it work with just saying that the objects and morphisms
   of a locally small category are no larger than the objects and
   morphisms of a (large) category.
   *)
Record LocallySmallCategory := {
  LSObject :> Type;
  LSMorphism : LSObject -> LSObject -> Type;

  LSIdentity : forall o, LSMorphism o o;
  LSCompose : forall s d d', LSMorphism d d' -> LSMorphism s d -> LSMorphism s d';

  LSAssociativity : forall o1 o2 o3 o4 (m1 : LSMorphism o1 o2) (m2 : LSMorphism o2 o3) (m3 : LSMorphism o3 o4),
    LSCompose (LSCompose m3 m2) m1 = LSCompose m3 (LSCompose m2 m1);
  LSLeftIdentity : forall a b (f : LSMorphism a b), LSCompose (LSIdentity b) f = f;
  LSRightIdentity : forall a b (f : LSMorphism a b), LSCompose f (LSIdentity a) = f
}.

Hint Resolve LSAssociativity LSLeftIdentity LSRightIdentity.

Section SmallCat2LocallySmallCat.
  Variable C : SmallCategory.

  Definition smallcat2locallysmallcat : LocallySmallCategory.
    refine {| LSObject := C.(SObject);
      LSMorphism := C.(SMorphism);
      LSCompose := C.(SCompose)
    |}; auto.
  Defined.
End SmallCat2LocallySmallCat.

Section LocallySmallCat2Cat.
  Variable C : LocallySmallCategory.

  Definition locallysmallcat2cat : Category.
    refine {| Object := C.(LSObject);
      Morphism := C.(LSMorphism);
      Compose := C.(LSCompose)
    |}; auto.
  Defined.
End LocallySmallCat2Cat.

Coercion smallcat2locallysmallcat : SmallCategory >-> LocallySmallCategory.
Coercion locallysmallcat2cat : LocallySmallCategory >-> Category.

Section LocallySmallCat.
  Hint Resolve ComposeFunctorsAssociativity LeftIdentityFunctor RightIdentityFunctor.

  Definition LocallySmallCat : Category.
    refine {| Object := LocallySmallCategory;
      Morphism := @Functor;
      Identity := @IdentityFunctor;
      Compose := @ComposeFunctors
      |}; auto.
  Defined.
End LocallySmallCat.
