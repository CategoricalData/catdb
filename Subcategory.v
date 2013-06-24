Require Export SigCategory.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Definition Subcategory := @Category_sig.
Definition SubcategoryInclusionFunctor := @proj1_sig_functor.
Definition FullSubcategory := @Category_sig_obj.
Definition FullSubcategoryInclusionFunctor := @proj1_sig_obj_functor.
Definition WideSubcategory := @Category_sig_mor.
Definition WideSubcategoryInclusionFunctor := @proj1_sig_mor_functor.
