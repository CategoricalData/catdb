Require Import FunctionalExtensionality.
Require Export Schema.
Require Import Common.

(* There is a category [Set], where the objects are sets and the morphisms are set morphisms *)
Section SSet.
  Local Ltac t_set :=
    unfold id in *; t_with t'; hnf; intros; simpl in *; etransitivity; eauto;
      repeat (apply functional_extensionality_dep; intro; simpl in *); t_with t';
        match goal with
          | [ |- ?f ?x = ?g ?x ] => cut (f = g);
            assumption ||
              solve [ let H := fresh in intro H; rewrite H; reflexivity ]
        end.

  Polymorphic Definition TypeSch : Schema.
    refine {| Vertex := Type;
      Edge := (fun s d => s -> d);
      PathsEquivalent := (fun _ _ p p' => compose _ (fun _ _ => id) p = compose _ (fun _ _ => id) p')
    |};
    abstract t_set.
  Defined.

  Polymorphic Definition SetSch : Schema.
    refine {| Vertex := Set;
      Edge := (fun s d => s -> d);
      PathsEquivalent := (fun _ _ p p' => compose _ (fun _ _ => id) p = compose _ (fun _ _ => id) p')
    |};
    abstract t_set.
  Defined.

  Polymorphic Definition PropSch : Schema.
    refine {| Vertex := Prop;
      Edge := (fun s d => s -> d);
      PathsEquivalent := (fun _ _ p p' => compose _ (fun _ _ => id) p = compose _ (fun _ _ => id) p')
    |};
    abstract t_set.
  Defined.
End SSet.
