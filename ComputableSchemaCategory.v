Require Import Setoid.
Require Export Category Schema.
Require Import Common Translation EquivalenceClass EquivalenceRelation.

Set Implicit Arguments.

Section ComputableSchema.
  Variable O : Type.
  Variable Object2Sch : O -> Schema.

  Coercion Object2Sch : O >-> Schema.

  Hint Resolve LeftIdentityTranslation RightIdentityTranslation f_equal2 ComposeTranslationsAssociativity.

  Hint Resolve PreComposeTranslationsEquivalent PostComposeTranslationsEquivalent.

  Hint Rewrite LeftIdentityTranslation RightIdentityTranslation.
  Hint Rewrite ComposeTranslationsAssociativity.

  (* XXX TODO: Automate this better. *)
  Definition ComputableSchemaCategory : Category.
    refine {| Object := O;
      Morphism := (fun s d : O => EquivalenceClass (@TranslationsEquivalent s d));
      Compose := (fun s d d' F G => @apply2_to_class _ _ _ _ _ _ (@TranslationsEquivalent_refl _ _) (@TranslationsEquivalent_sym _ _) (@TranslationsEquivalent_trans _ _)
        (@ComposeTranslations s d d') (@ComposeTranslations_mor s d d') F G);
      Identity := (fun o => @classOf _ _ (@TranslationsEquivalent_refl _ _) (@TranslationsEquivalent_sym _ _) (@TranslationsEquivalent_trans _ _)
        (IdentityTranslation o))
      |}; abstract (
        t_with t'; apply forall__eq; intros; split; intros; simpl in *; destruct_hypotheses; clear_InClass; unfold equiv in *;
          t_with t';
          repeat match goal with
                   | [ |- exists _, _ ] => exists (IdentityTranslation _)
                   | [ |- exists _, _ ] => eexists; eauto; clear_InClass; repeat split; clear_InClass; try reflexivity; eauto
                 end; t_with t'; unfold equiv in *; try reflexivity;
          repeat_subst_mor_of_type @Translation; autorewrite with core in *; eauto; try reflexivity;
            clear_InClass; unfold equiv in *; assumption
      ).
  Defined.
End ComputableSchema.

(*Definition Sch := @ComputableSchemaCategory Schema id.*)
