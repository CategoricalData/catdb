Require Export SumCategory NaturalTransformation.
Require Import Common Notations.

Set Implicit Arguments.

Generalizable All Variables.

Section SumCategoryFunctors.
  Section sum_functor.
    Context `(C : @SpecializedCategory objC).
    Context `(C' : @SpecializedCategory objC').
    Context `(D : @SpecializedCategory objD).

    Definition sum_Functor (F : SpecializedFunctor C D) (F' : SpecializedFunctor C' D)
    : SpecializedFunctor (C + C') D.
      match goal with
        | [ |- SpecializedFunctor ?C ?D ] =>
          refine (Build_SpecializedFunctor C D
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

    Definition sum_Functor_Functorial (F G : SpecializedFunctor C D) (F' G' : SpecializedFunctor C' D)
               (T : SpecializedNaturalTransformation F G)
               (T' : SpecializedNaturalTransformation F' G')
    : SpecializedNaturalTransformation (sum_Functor F F') (sum_Functor G G').
      match goal with
        | [ |- SpecializedNaturalTransformation ?A ?B ] =>
          refine (Build_SpecializedNaturalTransformation
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
               `(C : @SpecializedCategory objC)
               `(D : @SpecializedCategory objD)
    : SpecializedFunctor (C + D) (D + C)
      := sum_Functor (inr_Functor _ _) (inl_Functor _ _).

    Lemma sum_swap_swap_id
          `(C : @SpecializedCategory objC)
          `(D : @SpecializedCategory objD)
    : ComposeFunctors (sum_swap_Functor C D) (sum_swap_Functor D C) = IdentityFunctor _.
      apply Functor_eq; repeat intros [?|?]; simpl; trivial.
    Qed.
  End swap_functor.
End SumCategoryFunctors.

Notation "F + G" := (sum_Functor F G) : functor_scope.
Notation "T + U" := (sum_Functor_Functorial T U) : natural_transformation_scope.
