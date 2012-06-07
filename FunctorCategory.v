Require Import Setoid.
Require Export Category.
Require Import Common Functor NaturalTransformation.

Section FunctorCategory.
  Variable C D : Category.

  (*
     There is a category Fun(C, D) of functors from [C] to [D].
     *)
  Definition FunctorCategory : Category.
    refine {| Object := Functor C D;
      Morphism := @NaturalTransformation C D;
      Compose := @NTComposeT C D;
      Identity := @IdentityNaturalTransformation C D
      |}; intros; unfold NTComposeT; t.
    destruct m1 as [ ComponentsOf1 Commutes1 ].
    destruct m2 as [ ComponentsOf2 Commutes2 ].
    destruct m3 as [ ComponentsOf3 Commutes3 ].
    unfold ComponentsOf in *.
    admit. admit. admit.
(*    destruct_natural_transformations.
    admit.
    Require Import Program.
    match goal with
      | [ |- Build_NaturalTransformation _ _ _ _ ?co ?com = Build_NaturalTransformation _ _ _ _ ?co' ?com' ] =>
        let H := fresh in
          assert (H : co = co') by (apply functional_extensionality_dep; intro; repeat (rewrite Associativity); reflexivity);
            generalize com; generalize com'
    end.
    admit.
    destruct f as [fco fcom].
    match goal with
      | [ |- Build_NaturalTransformation _ _ _ _ ?co ?com = Build_NaturalTransformation _ _ _ _ ?co' ?com' ] =>
        let H := fresh in
          assert (H : co = co')
    end.
    admit.
    rewrite H; intro; unfold ComponentsOf.
    apply f_equal2.
    rewrite <- H.

    Require Import Program.

    nteq. simpl.
    match goal with
      | [ Build_NaturalTransformation
    apply f_equal2.
    repeat (rewrite Associativity)

 t; try simpl_transitivity;
        unfold NTComposeT; unfold NaturalTransformationsEquivalent in *; t).*)
  Defined.
End FunctorCategory.
