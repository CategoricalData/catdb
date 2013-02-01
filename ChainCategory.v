Require Import ProofIrrelevance.
Require Export SpecializedCategory.
Require Import NatFacts Subcategory DefinitionSimplification.

Set Implicit Arguments.

Section ChainCat.
  Definition OmegaCategory : @SpecializedCategory nat.
    refine (@Build_SpecializedCategory _
                                       le
                                       le_refl
                                       (fun _ _ _ H0 H1 => le_trans H1 H0)
                                       _
                                       _
                                       _);
    abstract (intros; apply proof_irrelevance).
  Defined.

  Let ChainCategory' n : @SpecializedCategory { m | m <= n }.
    simpl_definition_by_tac_and_exact (FullSubcategory OmegaCategory (fun m => m <= n)) ltac:(unfold Subcategory in *).
  Defined.
  Definition ChainCategory n := Eval cbv beta iota zeta delta [ChainCategory'] in ChainCategory' n.
End ChainCat.

Notation "[ n ]" := (ChainCategory n) : category_scope.
Notation "[ ∞ ]" := (OmegaCategory) : category_scope.
Notation "[ 'ω' ]" := (OmegaCategory) : category_scope.
