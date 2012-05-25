Require Import Bool Omega Setoid.
Require Import EquivalenceRelation Category Functor NaturalTransformation NaturalEquivalence.

Set Implicit Arguments.

Ltac t' := simpl; intuition.

Ltac t := t';
  repeat (match goal with
            | [ H : context[@eq] |- _ ] => rewrite H
            | _ => progress autorewrite with core in *
          end; t').

Record SmallCategory := {
  SObject :> Type;
  SMorphism : SObject -> SObject -> Type;

  SMorphismsEquivalent' : forall o1 o2, SMorphism o1 o2 -> SMorphism o1 o2 -> Prop;
  SMorphismsEquivalent : EquivalenceRelation SMorphismsEquivalent';

  SIdentity : forall o, SMorphism o o;
  SCompose : forall s d d', SMorphism d d' -> SMorphism s d -> SMorphism s d';

  SPreComposeMorphisms : forall s d d' (m : SMorphism d d') (m1 m2 : SMorphism s d),
    SMorphismsEquivalent' m1 m2 -> SMorphismsEquivalent' (SCompose m m1) (SCompose m m2);
  SPostComposeMorphisms : forall s d d' (m1 m2 : SMorphism d d') (m : SMorphism s d),
    SMorphismsEquivalent' m1 m2 -> SMorphismsEquivalent' (SCompose m1 m) (SCompose m2 m);

  SAssociativity : forall o1 o2 o3 o4 (m1 : SMorphism o1 o2) (m2 : SMorphism o2 o3) (m3 : SMorphism o3 o4),
    SMorphismsEquivalent' (SCompose (SCompose m3 m2) m1) (SCompose m3 (SCompose m2 m1));
  SLeftIdentity : forall a b (f : SMorphism a b), SMorphismsEquivalent' (SCompose (SIdentity b) f) f;
  SRightIdentity : forall a b (f : SMorphism a b), SMorphismsEquivalent' (SCompose f (SIdentity a)) f
}.

Section SmallCat2Cat.
  Variable C : SmallCategory.

  Definition smallcat2cat : Category.
    refine {| Object := C.(SObject);
      Morphism := C.(SMorphism);
      MorphismsEquivalent' := C.(SMorphismsEquivalent');
      MorphismsEquivalent := C.(SMorphismsEquivalent);
      Compose := C.(SCompose)
    |}.
    apply SPreComposeMorphisms. apply SPostComposeMorphisms.
    apply SAssociativity. apply SLeftIdentity. apply SRightIdentity.
  Defined.
End SmallCat2Cat.

Coercion smallcat2cat : SmallCategory >-> Category.

Section SmallCat.
(*  Definition SmallCat : Category.
    refine {| Object := SmallCategory;
      Morphism := (fun C D => Functor C D);
      MorphismsEquivalent' := (fun C D => NaturalEquivalence C D)
      |}.*)
End SmallCat.
