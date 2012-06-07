Require Import Setoid Program.
Require Export Category Functor.
Require Import Common NaturalTransformation NaturalEquivalence FunctorCategory.

Local Notation "C ^ D" := (FunctorCategory D C).

Section DiagonalFunctor.
  Variable C D : Category.

  (**
     Quoting Dwyer and Spalinski:

     There is a diagonal or ``constant diagram'' functor
       Δ : C -> C^D,
     which carries an object [X : C] to the constant functor [Δ X : D -> C] (by definition,
     this ``constant functor'' sends each object of [D] to [X] and each morphism of [D]
     to [Identity X]). The functor Δ assigns to each morphism [f : X -> X'] of [C] the constant
     natural transformation [t(f) : Δ X -> Δ X'] determined by the formula [t(f) d = f] for
     each object [d] of [D].
     **)

  (* TODO: Try to combine these definitions into a single definition. *)
  Definition diagonal_functor_object_of (c : C) : C ^ D.
    refine {| ObjectOf := fun _ => c;
      MorphismOf := (fun _ _ _ => Identity c)
    |}; abstract t.
  Defined.

  Definition diagonal_functor_morphism_of o1 o2 : C.(Morphism) o1 o2 -> (C ^ D).(Morphism) (diagonal_functor_object_of o1) (diagonal_functor_object_of o2).
    simpl; unfold diagonal_functor_object_of; intro m.
    refine {| ComponentsOf := fun d : D => m : Morphism C ((diagonal_functor_object_of o1) d) ((diagonal_functor_object_of o2) d)
      |}; abstract t.
  Defined.

  Hint Unfold diagonal_functor_object_of diagonal_functor_morphism_of ComponentsOf NTComposeT IdentityNaturalTransformation.
  Hint Resolve f_equal f_equal2.
  Hint Extern 1 (_ = _) => apply proof_irrelevance.

  Definition DiagonalFunctor : Functor C (C ^ D).
    refine {| ObjectOf := diagonal_functor_object_of;
      MorphismOf := diagonal_functor_morphism_of
      |}; abstract (simpl; autounfold with core in *; eauto).
  Defined.
End DiagonalFunctor.

Hint Unfold diagonal_functor_object_of diagonal_functor_morphism_of.

Section Limit.
  Variable C D : Category.
  Variable F : Functor D C.

  (**
     Quoting Dwyer and Spalinski:

     Let [D] be a small category and [F : D -> C] a functor. A limit
     for [F] is an object [L] of [C] together with a natural transformation [t : Δ L -> F]
     such that for every object [X] of [C] and every natural transformation [s : Δ X -> F],
     there exists a unique map [s' : X -> L] in [C] such that [t (Δ s') = s].
     **)
  Definition Limit (L : C) :=
    { t : NaturalTransformation ((DiagonalFunctor C D) L) F &
      forall X : C, forall s : NaturalTransformation ((DiagonalFunctor C D) X) F,
        { s' : C.(Morphism) X L | is_unique s' /\
          NTComposeT t ((DiagonalFunctor C D).(MorphismOf) s') = s
        }
    }.

  (**
     Quoting Dwyer and Spalinski:

     Let [D] be a small category and [F : D -> C] a functor. A colimit
     for [F] is an object [c] of [C] together with a natural transformation [t : F -> Δ c]
     such that for every object [X] of [C] and every natural transformation [s : F -> Δ X],
     there exists a unique map [s' : c -> X] in [C] such that [(Δ s') t = s].
     **)
  Definition Colimit (c : C) :=
    { t : NaturalTransformation F ((DiagonalFunctor C D) c) &
      forall X : C, forall s : NaturalTransformation F ((DiagonalFunctor C D) X),
        { s' : C.(Morphism) c X | is_unique s' /\
          NTComposeT ((DiagonalFunctor C D).(MorphismOf) s') t = s
        }
    }.
End Limit.

Implicit Arguments Limit [C D].
Implicit Arguments Colimit [C D].
