Require Import ProofIrrelevance.
Require Export SpecializedCategory.
Require Import NatFacts Subcategory DefinitionSimplification.

Set Implicit Arguments.

Section NatCat.
  Definition OmegaCategory : @SpecializedCategory nat.
    refine {|
      Morphism' := le;
      Compose' := (fun _ _ _ H0 H1 => le_trans H1 H0);
      Identity' := le_refl
    |};
    abstract (intros; apply proof_irrelevance).
  Defined.

  Let NatCategory' n : @SpecializedCategory { m | m <= n }.
    simpl_definition_by_tac_and_exact (FullSubcategory OmegaCategory (fun m => m <= n)) ltac:(unfold Subcategory in *).
  Defined.
  Definition NatCategory n := Eval cbv beta iota zeta delta [NatCategory'] in NatCategory' n.
End NatCat.

Notation "[ n ]" := (NatCategory n) : category_scope.
Notation "[ ∞ ]" := (OmegaCategory) : category_scope.
Notation "[ 'ω' ]" := (OmegaCategory) : category_scope.
