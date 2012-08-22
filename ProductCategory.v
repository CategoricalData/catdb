Require Export SpecializedCategory Functor.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Section ProductCategory.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Definition ProductCategory : @SpecializedCategory (objC * objD)%type.
    refine {|
      Morphism' := (fun s d => (C.(Morphism) (fst s) (fst d) * D.(Morphism) (snd s) (snd d))%type);
      Identity' := (fun o => (Identity (fst o), Identity (snd o)));
(*      Compose' := (fun s d d' m2 m1 => (Compose (fst m2) (fst m1), Compose (snd m2) (snd m1))) (* gives Uncaught exception: Not_found *) *)
      Compose' := (fun (s d d' : (C * D)%type) m2 m1 => (C.(Compose') _ _ _ (fst m2) (fst m1), D.(Compose') _ _ _ (snd m2) (snd m1)))
    |}; abstract (present_spcategory; intros; simpl in *; destruct_type @prod; t).
  Defined.
End ProductCategory.

Infix "*" := ProductCategory : category_scope.

Section ProductCategoryFunctors.
  Context `{C : @SpecializedCategory objC}.
  Context `{D : @SpecializedCategory objD}.

  Definition fst_Functor : SpecializedFunctor (C * D) C.
    refine (Build_SpecializedFunctor (C * D) C
      (@fst _ _)
      (fun _ _ => @fst _ _)
      _
      _
    );
    abstract eauto.
  Defined.

  Definition snd_Functor : SpecializedFunctor (C * D) D.
    refine (Build_SpecializedFunctor (C * D) D
      (@snd _ _)
      (fun _ _ => @snd _ _)
      _
      _
    );
    abstract eauto.
  Defined.
End ProductCategoryFunctors.
