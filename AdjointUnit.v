Require Export Category Functor NaturalTransformation.
Require Import Common.

Set Implicit Arguments.

Section Adjunction.
  Variables C D : Category.
  Variable F : Functor C D.
  Variable G : Functor D C.

  (**
     Quoting from Awody's "Category Theory",
     An adjunction between categories [C] and [D]
     consists of functors
     [F : C <-> D : G]
     and a natural transformation
     [T : 1_C -> G ○ F]
     with the property:
     (o) For any [c : C], [d : D], and [f : c -> G d], there exists a unique
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
        c

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
  Definition AdjunctionUnit (F : Functor C D) (G : Functor D C) :=
    { T : NaturalTransformation (IdentityFunctor C) (ComposeFunctors G F) &
      forall (c : C) (d : D) (f : C.(Morphism) c (G d)),
        { g : D.(Morphism) (F c) d | unique (fun g => f = Compose (G.(MorphismOf) g) (T c)) g }
    }.

  (**
     Paraphrasing and quoting from Awody's "SpecializedCategory Theory",
     An adjunction between categories [C] and [D]
     consists of functors
     [F : C <-> D : G]
     and a natural transformation
     [U : F ○ G -> 1_D]
     with the property:
     (o) For any [c : C], [d : D], and [g : F c -> d], there exists a unique
     [f : c -> G d] such that
     [g = (U d) ○ (F f)]
     as indicated in the diagram

                f
     c ..................> G d

               F f
     F c --------------> F (G d)
      \                    |
        \                  |
          \                |
            \              |
              \            | U d
             g  \          |
                  \        |
                    \      |
                      \    |
                       _\| V
                          d

    Terminology and notation:
    * The statement (o) is the UMP of the counit [U].
    **)
  Definition AdjunctionCounit (F : Functor C D) (G : Functor D C) :=
    { U : NaturalTransformation (ComposeFunctors F G) (IdentityFunctor D) &
      forall (c : C) (d : D) (g : D.(Morphism) (F c) d),
        { f : C.(Morphism) c (G d) | unique (fun f => g = Compose (U d) (F.(MorphismOf) f)) f }
    }.
End Adjunction.
