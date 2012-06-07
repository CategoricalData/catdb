Require Import Setoid.
Require Export Category Functor.
Require Import NaturalEquivalence.

Section Adjunction.
  Variables C D : Category.

  (**
     Quoting from Awody's "Category Theory",
     An adjunction between categories [C] and [D]
     consists of functors
     [F : C <-> D : G]
     and a natural transformation
     [T : 1_C -> G ○ F]
     with the property:
     (o) For any [c : C], [d : D], and [f : C -> G d], there exists a unique
     [g : F c -> d] such that
     [f = (G g) ○ (T c)]
     as indicated in
                g
     F c ..................> d

                 G g
     G (F c) --------------> G d
       ^                    _
       |                    /|
       |                  /
       |                /
       |              /
       | T c        /
       |          /  f
       |        /
       |      /
       |    /
       |  /
        C

    Terminology and notation:
    * [F] is called the left adjoint, [G] is called the right adjoint, and [T] is called the
    unit of the adjunction.
    * One sometimes writes [F -| G] for ``[F] is left and [G] right adjoint.''
    * The statement (o) is the UMP of the unit [T].
    Note that the situation [F -| G] is a generalization of equivalence of categories,
    in that a pseudo-inverse is an adjoint. In that case, however, it is the relation
    between categories that one is interested in. Here, one is concerned with the
    relation between special functors. That is to say, it is not the relation on
    categories ``there exists an adjunction,'' but rather ``this functor has an adjoint''
    that we are concerned with.
    **)
  Definition Adjunction (F : Functor C D) (G : Functor D C) :=
    { T : NaturalTransformation (IdentityFunctor C) (ComposeFunctors G F) &
      forall (c : C) (d : D) (f : Morphism _ c (G d)),
        { g : Morphism _ (F c) d | is_unique g /\ f = Compose (G.(MorphismOf) g) (T c) }
    }.
End Adjunction.

Implicit Arguments Adjunction [C D].
