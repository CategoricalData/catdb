Require Export SigCategory.

Set Implicit Arguments.

Polymorphic Definition Subcategory := @SpecializedCategory_sig.
Polymorphic Definition SubcategoryInclusionFunctor := @proj1_sig_functor.
Polymorphic Definition FullSubcategory := @SpecializedCategory_sig_obj.
Polymorphic Definition FullSubcategoryInclusionFunctor := @proj1_sig_obj_functor.
Polymorphic Definition WideSubcategory := @SpecializedCategory_sig_mor.
Polymorphic Definition WideSubcategoryInclusionFunctor := @proj1_sig_mor_functor.
