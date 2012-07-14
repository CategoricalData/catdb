Require Import Setoid.
Require Import Common EquivalenceRelation.
Require Export Category.

Section ProductCategory.
  Variables C D : Category.

  Definition ProductCategory : Category.
    refine {| Object := (C * D)%type;
      Morphism := (fun s d => ((C.(Morphism) (fst s) (fst d)) * (D.(Morphism) (snd s) (snd d)))%type);
      Identity := (fun o => (Identity (fst o), Identity (snd o)));
      Compose := (fun s d d' m2 m1 => (Compose (fst m2) (fst m1), Compose (snd m2) (snd m1)))
    |}; abstract (intros; destruct_type @prod; t_with t').
  Defined.
End ProductCategory.
