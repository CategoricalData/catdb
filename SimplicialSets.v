Require Export ChainCategory Duals FunctorCategory.
Require Import Notations ComputableCategory SetCategory.

Generalizable Variables objC.

Set Implicit Arguments.

Section SimplicialSets.
  Polymorphic Definition SimplexCategory := @ComputableCategory nat _ (fun n => [n])%category.
  Local Notation "'Δ'" := SimplexCategory : category_scope.

  Polymorphic Definition SimplicialCategory `(C : SpecializedCategory objC) := (C ^ (OppositeCategory Δ))%category.

  Polymorphic Definition SimplicialSet := SimplicialCategory SetCat.
  Polymorphic Definition SimplicialType := SimplicialCategory TypeCat.
  Polymorphic Definition SimplicialProp := SimplicialCategory PropCat.
End SimplicialSets.

Notation SimplicialOf obj := (let C := CatOf obj in SimplicialCategory C).
