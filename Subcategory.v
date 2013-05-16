Require Export SigCategory.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Definition Subcategory := @SpecializedCategory_sig.
Definition SubcategoryInclusionFunctor := @proj1_sig_functor.
Definition FullSubcategory := @SpecializedCategory_sig_obj.
Definition FullSubcategoryInclusionFunctor := @proj1_sig_obj_functor.
Definition WideSubcategory := @SpecializedCategory_sig_mor.
Definition WideSubcategoryInclusionFunctor := @proj1_sig_mor_functor.
