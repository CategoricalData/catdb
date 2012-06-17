Require Import FunctionalExtensionality.
Require Export Schema.
Require Import Common.

(* There is a category [Set], where the objects are sets and the morphisms are set morphisms *)
Section SSet.
  Definition TypeSch : Schema.
    refine {| Vertex := Type;
      Edge := (fun s d => s -> d);
      PathsEquivalent' := (fun _ _ p p' => compose _ (fun _ _ => id) p = compose _ (fun _ _ => id) p')
    |}; abstract (
      unfold id in *; firstorder; etransitivity; eauto; repeat (apply functional_extensionality_dep; intro; simpl in *); t_with t';
        match goal with
          | [ |- ?f ?x = ?g ?x ] => cut (f = g);
            assumption ||
              solve [ let H := fresh in intro H; rewrite H; reflexivity ]
        end
    ).
  Defined.

  Definition SetSch : Schema.
    refine {| Vertex := Set;
      Edge := (fun s d => s -> d);
      PathsEquivalent' := (fun _ _ p p' => compose _ (fun _ _ => id) p = compose _ (fun _ _ => id) p')
    |}; abstract (
      unfold id in *; firstorder; etransitivity; eauto; repeat (apply functional_extensionality_dep; intro; simpl in *); t_with t';
        match goal with
          | [ |- ?f ?x = ?g ?x ] => cut (f = g);
            assumption ||
              solve [ let H := fresh in intro H; rewrite H; reflexivity ]
        end
    ).
  Defined.

  Definition PropSch : Schema.
    refine {| Vertex := Prop;
      Edge := (fun s d => s -> d);
      PathsEquivalent' := (fun _ _ p p' => compose _ (fun _ _ => id) p = compose _ (fun _ _ => id) p')
    |}; abstract (
      unfold id in *; firstorder; etransitivity; eauto; repeat (apply functional_extensionality_dep; intro; simpl in *); t_with t';
        match goal with
          | [ |- ?f ?x = ?g ?x ] => cut (f = g);
            assumption ||
              solve [ let H := fresh in intro H; rewrite H; reflexivity ]
        end
    ).
  Defined.
End SSet.
