Require Export SpecializedCategory Functor NaturalTransformation.
Require Import Common.

Set Implicit Arguments.

Section FunctorCategory.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.

  Hint Resolve Associativity LeftIdentity RightIdentity.

  (*
     There is a category Fun(C, D) of functors from [C] to [D].
     *)
  Definition FunctorCategory : @SpecializedCategory (SpecializedFunctor C D) (@SpecializedNaturalTransformation _ _ C _ _ D).
    refine {| Compose' := NTComposeT (C := C) (D := D);
      Identity' := IdentityNaturalTransformation (C := C) (D := D)
      |}; abstract (present_spnt; nt_eq; autorewrite with core; auto).
  Defined.
End FunctorCategory.

Local Notation "C ^ D" := (FunctorCategory D C).

Ltac unfold_FunctorCategory_of obj mor C D :=
  progress (
    change (@Object obj mor (D ^ C)) with obj in *; simpl in *;
      change (@Morphism obj mor (D ^ C)) with mor in *; simpl in *;
        change (@Identity obj mor (D ^ C)) with (@IdentityNaturalTransformation _ _ C _ _ D) in *; simpl in *;
          change (@Compose obj mor (D ^ C)) with (@NTComposeT _ _ C _ _ D) in *; simpl in *
  ).

Ltac unfold_FunctorCategory :=
  repeat match goal with
           | [ _ : appcontext[@Object ?obj ?mor (?C ^ ?D)] |- _ ] => unfold_FunctorCategory_of obj mor D C
           | [ _ : appcontext[@Morphism ?obj ?mor (?C ^ ?D)] |- _ ] => unfold_FunctorCategory_of obj mor D C
           | [ _ : appcontext[@Identity ?obj ?mor (?C ^ ?D)] |- _ ] => unfold_FunctorCategory_of obj mor D C
           | [ _ : appcontext[@Compose ?obj ?mor (?C ^ ?D)] |- _ ] => unfold_FunctorCategory_of obj mor D C
           | [ |- appcontext[@Object ?obj ?mor (?C ^ ?D)] ] => unfold_FunctorCategory_of obj mor D C
           | [ |- appcontext[@Morphism ?obj ?mor (?C ^ ?D)] ] => unfold_FunctorCategory_of obj mor D C
           | [ |- appcontext[@Identity ?obj ?mor (?C ^ ?D)] ] => unfold_FunctorCategory_of obj mor D C
           | [ |- appcontext[@Compose ?obj ?mor (?C ^ ?D)] ] => unfold_FunctorCategory_of obj mor D C
         end.

(*Hint Extern 1 => unfold_FunctorCategory.*)
