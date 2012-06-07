Require Export Category.

(* There is a category [Set], where the objects are sets and the morphisms are set morphisms *)
Section CSet.
  Definition TypeCat : Category.
    refine {| Object := Type;
      Morphism := fun s d => s -> d;
      Compose := fun _ _ _ f g => (fun x => f (g x));
      Identity := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.

  Definition SetCat : Category.
    refine {| Object := Set;
      Morphism := fun s d => s -> d;
      Compose := fun _ _ _ f g => (fun x => f (g x));
      Identity := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.

  Definition PropCat : Category.
    refine {| Object := Prop;
      Morphism := fun s d => s -> d;
      Compose := fun _ _ _ f g => (fun x => f (g x));
      Identity := fun _ => (fun x => x)
    |}; abstract (firstorder; etransitivity; eauto; t).
  Defined.
End CSet.
