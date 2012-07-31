Require Export SpecializedCategory Functor.
Require Import Common.

Set Implicit Arguments.

Section ProductCategory.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.

  Definition ProductCategory : @SpecializedCategory (objC * objD)%type (fun s d => (morC (fst s) (fst d) * morD (snd s) (snd d))%type).
    refine {|
      Identity' := (fun o => (Identity (fst o), Identity (snd o)));
(*      Compose' := (fun s d d' m2 m1 => (Compose (fst m2) (fst m1), Compose (snd m2) (snd m1))) (* gives Uncaught exception: Not_found *) *)
      Compose' := (fun (s d d' : (C * D)%type) m2 m1 => (C.(Compose') _ _ _ (fst m2) (fst m1), D.(Compose') _ _ _ (snd m2) (snd m1)))
    |}; abstract (present_spcategory; intros; simpl in *; destruct_type @prod; t).
  Defined.
End ProductCategory.

Infix "*" := ProductCategory : category_scope.

Section ProductCategoryFunctors.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.
  Variable objD : Type.
  Variable morD : objD -> objD -> Type.
  Variable D : SpecializedCategory morD.

  Definition fst_Functor : SpecializedFunctor (C * D) C.
    refine {| ObjectOf' := (@fst _ _);
      MorphismOf' := (fun _ _ => @fst _ _)
    |}; abstract eauto.
  Defined.

  Definition snd_Functor : SpecializedFunctor (C * D) D.
    refine {| ObjectOf' := (@snd _ _);
      MorphismOf' := (fun _ _ => @snd _ _)
    |}; abstract eauto.
  Defined.
End ProductCategoryFunctors.

Arguments fst_Functor {objC morC C objD morD D}.
Arguments snd_Functor {objC morC C objD morD D}.
