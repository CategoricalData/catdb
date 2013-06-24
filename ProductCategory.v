Require Export Category Functor.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section ProductCategory.
  Variable C : Category.
  Variable D : Category.

  Definition ProductCategory : Category.
    refine (@Build_Category (C * D)%type
                                       (fun s d => (C.(Morphism) (fst s) (fst d) * D.(Morphism) (snd s) (snd d))%type)
                                       (fun o => (Identity (fst o), Identity (snd o)))
                                       (fun s d d' m2 m1 => (Compose (fst m2) (fst m1), Compose (snd m2) (snd m1)))
                                       _
                                       _
                                       _);
    abstract (intros; simpl_eq; auto with morphism).
  Defined.
End ProductCategory.

Infix "*" := ProductCategory : category_scope.

Section ProductCategoryFunctors.
  Context `{C : Category}.
  Context `{D : Category}.

  Definition fst_Functor : Functor (C * D) C
    := Build_Functor (C * D) C
                                (@fst _ _)
                                (fun _ _ => @fst _ _)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Definition snd_Functor : Functor (C * D) D
    := Build_Functor (C * D) D
                                (@snd _ _)
                                (fun _ _ => @snd _ _)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).
End ProductCategoryFunctors.
