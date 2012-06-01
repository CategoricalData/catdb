Require Import Setoid.
Require Import Common EquivalenceRelation Category Functor NaturalTransformation NaturalEquivalence FunctorCategory ComputableCategory.

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
  Definition diagonal_functor_object_of : C -> C ^ D.
    intro c.
    refine {| ObjectOf := fun _ => c;
      MorphismOf := (fun _ _ _ => Identity c)
    |}; abstract t.
  Defined.

  Definition diagonal_functor_morphism_of_components_of o1 o2 (m : C.(Morphism) o1 o2) (d : D) :
    Morphism C ((diagonal_functor_object_of o1) d) ((diagonal_functor_object_of o2) d).
    simpl; assumption.
  Defined.

  Definition diagonal_functor_morphism_of s d : C.(Morphism) s d -> (C ^ D).(Morphism) (diagonal_functor_object_of s) (diagonal_functor_object_of d).
    simpl; unfold diagonal_functor_object_of; intro f.
    refine {| ComponentsOf := fun _ : D => diagonal_functor_morphism_of_components_of _ _ f _
      |}; abstract t.
  Defined.

  Hint Unfold diagonal_functor_object_of diagonal_functor_morphism_of_components_of diagonal_functor_morphism_of.
  Hint Unfold NaturalTransformationsEquivalent.

  Definition DiagonalFunctor : Functor C (C ^ D).
    refine {| ObjectOf := diagonal_functor_object_of;
      MorphismOf := diagonal_functor_morphism_of
      |}; abstract t.
  Defined.
End DiagonalFunctor.

Hint Unfold diagonal_functor_object_of diagonal_functor_morphism_of_components_of diagonal_functor_morphism_of.
