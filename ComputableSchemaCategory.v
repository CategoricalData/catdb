Require Import Setoid.
Require Export Category Schema.
Require Import Common Translation.

Set Implicit Arguments.

Section ComputableSchema.
  Variable O : Type.
  Variable Object2Sch : O -> Schema.

  Coercion Object2Sch : O >-> Schema.

  Hint Resolve LeftIdentityTranslation RightIdentityTranslation f_equal2 ComposeTranslationsAssociativity.

  Definition ComputableSchemaCategory : Category.
    refine {| Object := O;
      Morphism := Translation;
      Compose := (fun _ _ _ F G => ComposeTranslations F G);
      Identity := (fun o => IdentityTranslation o)
      |}; abstract (t; simpl_transitivity).
  Defined.
End ComputableSchema.

Definition Sch := @ComputableSchemaCategory Schema id.
