Require Export SpecializedCategory SpecializedFunctor SpecializedNaturalTransformation.
Require Import Common.

Set Implicit Arguments.

Section FunctorCategory.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable C : SpecializedCategory morC.
  Variable D : SpecializedCategory morD.

  Hint Resolve Associativity LeftIdentity RightIdentity.

  (*
     There is a category Fun(C, D) of functors from [C] to [D].
     *)
  Definition SpecializedFunctorCategory : @SpecializedCategory (SpecializedFunctor C D) (@SpecializedNaturalTransformation _ _ _ _ C D).
    refine {| Compose' := @SPNTComposeT _ _ _ _ C D;
      Identity' := @IdentitySpecializedNaturalTransformation _ _ _ _ C D
      |}; abstract (spnt_eq; auto).
  Defined.
End FunctorCategory.

Local Notation "C ^ D" := (SpecializedFunctorCategory D C).

Ltac unfold_SpecializedFunctorCategory_of obj mor C D :=
  progress (
    change (@Object obj mor (D ^ C)) with obj in *; simpl in *;
      change (@Morphism obj mor (D ^ C)) with mor in *; simpl in *;
        change (@Identity obj mor (D ^ C)) with (@IdentitySpecializedNaturalTransformation _ _ _ _ C D) in *; simpl in *;
          change (@Compose obj mor (D ^ C)) with (@SPNTComposeT _ _ _ _ C D) in *; simpl in *
  ).

Ltac unfold_SpecializedFunctorCategory :=
  repeat match goal with
           | [ _ : appcontext[@Object ?obj ?mor (?C ^ ?D)] |- _ ] => unfold_SpecializedFunctorCategory_of obj mor D C
           | [ _ : appcontext[@Morphism ?obj ?mor (?C ^ ?D)] |- _ ] => unfold_SpecializedFunctorCategory_of obj mor D C
           | [ _ : appcontext[@Identity ?obj ?mor (?C ^ ?D)] |- _ ] => unfold_SpecializedFunctorCategory_of obj mor D C
           | [ _ : appcontext[@Compose ?obj ?mor (?C ^ ?D)] |- _ ] => unfold_SpecializedFunctorCategory_of obj mor D C
           | [ |- appcontext[@Object ?obj ?mor (?C ^ ?D)] ] => unfold_SpecializedFunctorCategory_of obj mor D C
           | [ |- appcontext[@Morphism ?obj ?mor (?C ^ ?D)] ] => unfold_SpecializedFunctorCategory_of obj mor D C
           | [ |- appcontext[@Identity ?obj ?mor (?C ^ ?D)] ] => unfold_SpecializedFunctorCategory_of obj mor D C
           | [ |- appcontext[@Compose ?obj ?mor (?C ^ ?D)] ] => unfold_SpecializedFunctorCategory_of obj mor D C
         end.

(*Hint Extern 1 => unfold_SpecializedFunctorCategory.*)
