Require Import Setoid.
Require Export Category Schema SmallSchema.
Require Import Common SmallTranslation EquivalenceClass.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section ComputableSchema.
  Variable O : Type.
  Variable Object2Sch : O -> SmallSchema.

  Local Coercion Object2Sch : O >-> SmallSchema.

  Hint Resolve LeftIdentitySmallTranslation RightIdentitySmallTranslation f_equal2 ComposeSmallTranslationsAssociativity.

  Hint Resolve PreComposeSmallTranslationsEquivalent PostComposeSmallTranslationsEquivalent.

  Hint Rewrite LeftIdentitySmallTranslation RightIdentitySmallTranslation.
  Hint Rewrite ComposeSmallTranslationsAssociativity.

  (* XXX TODO: Automate this better. *)
  Definition ComputableSchemaCategory : Category (fun s d : O => EquivalenceClass (@SmallTranslationsEquivalent s d)).
    refine (Build_Category (fun s d : O => EquivalenceClass (@SmallTranslationsEquivalent s d))
      (fun o => @classOf _ _ (@SmallTranslationsEquivalent_rel _ _)
        (IdentitySmallTranslation o))
      (fun (s d d' : O) F G => @apply2_to_class _ _ _ _ _ _ (@SmallTranslationsEquivalent_rel _ _)
        (@ComposeSmallTranslations s d d') (@ComposeSmallTranslations_mor s d d') F G)
      _
      _
      _
    );
(*    abstract ( *)
      t_with t'; apply EquivalenceClass_forall__eq; intros; split; intros; simpl in *; destruct_hypotheses; clear_InClass; unfold equiv in *;
        t_with t';
        repeat match goal with
                 | [ |- exists _, _ ] => exists (IdentitySmallTranslation _)
                 | [ |- exists _, _ ] => eexists; eauto; clear_InClass; repeat split; clear_InClass; try reflexivity; eauto
               end; t_with t'; unfold equiv in *; try reflexivity; subst; simpl in *; t_with t'.
    repeat_subst_mor_of_type @SmallTranslation; autorewrite with core in *; eauto; try reflexivity;
      t_with t'. (*
    etransitivity.
        simpl in H2.
        Set Printing Coercions.
        subst.
        rewrite H6.
        pose ({| SVertexOf := x1; SPathOf := x3; STEquivalenceOf := x5 |}) as H10.
        move H10 at top.
        change_in_all ({| SVertexOf := x1; SPathOf := x3; STEquivalenceOf := x5 |}) with H10.
        repeat_subst_mor_of_type @SmallTranslation.
        rewrite H2.
        repeat_subst
        matc
    apply stranslations_equivalent; simpl.
    apply functional_extensionality_dep
        repeat_subst_mor_of_type @SmallTranslation; autorewrite with core in *; eauto; try reflexivity;
          clear_InClass; unfold equiv in *.
          ). *)
  Defined.
End ComputableSchema.

(*Definition Sch := @ComputableSchemaCategory Schema id.*)
