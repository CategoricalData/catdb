Require Export ChainCategory Duals FunctorCategory.
Require Import Notations ComputableCategory SetCategory.

Generalizable Variables objC.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section SimplicialSets.
  Definition SimplexCategory := ComputableCategory (fun n : nat => [n])%category.
  Local Notation Δ := SimplexCategory.

  Definition SimplicialCategory (C : Category) := (C ^ (OppositeCategory Δ))%category.

  Definition SimplicialSet := SimplicialCategory SetCat.
  Definition SimplicialType := SimplicialCategory TypeCat.
  Definition SimplicialProp := SimplicialCategory PropCat.
End SimplicialSets.

Notation SimplicialOf obj := (let C := CatOf obj in SimplicialCategory C).
