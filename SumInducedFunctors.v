Require Export SumCategory NaturalTransformation.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section SumCategoryFunctors.
  Section sum_functor.
    Variable C : Category.
    Variable C' : Category.
    Variable D : Category.

    Definition sum_Functor (F : Functor C D) (F' : Functor C' D)
    : Functor (C + C') D.
      match goal with
        | [ |- Functor ?C ?D ] =>
          refine (Build_Functor C D
                                           (fun cc' => match cc' with
                                                         | inl c => F c
                                                         | inr c' => F' c'
                                                       end)
                                           (fun s d => match s, d with
                                                         | inl cs, inl cd => MorphismOf F (s := cs) (d := cd)
                                                         | inr c's, inr c'd => MorphismOf F' (s := c's) (d := c'd)
                                                         | _, _ => fun m => match m with end
                                                       end)
                                           _
                                           _)
      end;
      abstract (
          repeat intros [?|?];
          intros;
          simpl in *;
            destruct_head_hnf Empty_set;
          repeat rewrite FIdentityOf;
          repeat rewrite FCompositionOf;
          reflexivity
        ).
    Defined.

    Definition sum_Functor_Functorial (F G : Functor C D) (F' G' : Functor C' D)
               (T : NaturalTransformation F G)
               (T' : NaturalTransformation F' G')
    : NaturalTransformation (sum_Functor F F') (sum_Functor G G').
      match goal with
        | [ |- NaturalTransformation ?A ?B ] =>
          refine (Build_NaturalTransformation
                    A B
                    (fun x => match x with
                                | inl c => T c
                                | inr c' => T' c'
                              end)
                    _)
      end;
      abstract (
          repeat intros [?|?]; simpl; intros; destruct_head_hnf Empty_set; apply Commutes
        ).
    Defined.
  End sum_functor.

  Section swap_functor.
    Definition sum_swap_Functor
               `(C : Category)
               `(D : Category)
    : Functor (C + D) (D + C)
      := sum_Functor (inr_Functor _ _) (inl_Functor _ _).

    Lemma sum_swap_swap_id
          `(C : Category)
          `(D : Category)
    : ComposeFunctors (sum_swap_Functor C D) (sum_swap_Functor D C) = IdentityFunctor _.
      apply Functor_eq; repeat intros [?|?]; simpl; trivial.
    Qed.
  End swap_functor.
End SumCategoryFunctors.

Notation "F + G" := (sum_Functor F G) : functor_scope.
Notation "T + U" := (sum_Functor_Functorial T U) : natural_transformation_scope.
