Require Import Setoid.
Require Export Category Schema SmallSchema.
Require Import Common SmallTranslation EquivalenceClass EquivalenceRelation.

Set Implicit Arguments.

Section ComputableSchema.
  Variable O : Type.
  Variable Object2Sch : O -> SmallSchema.

  Coercion Object2Sch : O >-> SmallSchema.

  Hint Resolve LeftIdentitySmallTranslation RightIdentitySmallTranslation f_equal2 ComposeSmallTranslationsAssociativity.

  Hint Resolve PreComposeSmallTranslationsEquivalent PostComposeSmallTranslationsEquivalent.

  Hint Rewrite LeftIdentitySmallTranslation RightIdentitySmallTranslation.
  Hint Rewrite ComposeSmallTranslationsAssociativity.

  (* XXX TODO: Automate this better. *)
  Definition ComputableSchemaCategory : Category.
    refine {| Object := O;
      Morphism := (fun s d : O => EquivalenceClass (@SmallTranslationsEquivalent s d));
      Compose := (fun s d d' F G => @apply2_to_class _ _ _ _ _ _ (@SmallTranslationsEquivalent_refl _ _) (@SmallTranslationsEquivalent_sym _ _) (@SmallTranslationsEquivalent_trans _ _)
        (@ComposeSmallTranslations s d d') (@ComposeSmallTranslations_mor s d d') F G);
      Identity := (fun o => @classOf _ _ (@SmallTranslationsEquivalent_refl _ _) (@SmallTranslationsEquivalent_sym _ _) (@SmallTranslationsEquivalent_trans _ _)
        (IdentitySmallTranslation o))
      |}; abstract (
        t_with t'; apply forall__eq; intros; split; intros; simpl in *; destruct_hypotheses; clear_InClass; unfold equiv in *;
          t_with t';
          repeat match goal with
                   | [ |- exists _, _ ] => exists (IdentitySmallTranslation _)
                   | [ |- exists _, _ ] => eexists; eauto; clear_InClass; repeat split; clear_InClass; try reflexivity; eauto
                 end; t_with t'; unfold equiv in *; try reflexivity;
          repeat_subst_mor_of_type @SmallTranslation; autorewrite with core in *; eauto; try reflexivity;
            clear_InClass; unfold equiv in *; assumption
      ).
  Defined.
End ComputableSchema.

(*Definition Sch := @ComputableSchemaCategory Schema id.*)
