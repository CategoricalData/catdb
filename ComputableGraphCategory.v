Require Export SpecializedCategory Graph GraphTranslation.
Require Import Common.

Set Implicit Arguments.

Section ComputableGraphCategory.
  Variable I : Type.
  Variable Index2Vertex : I -> Type.
  Variable Index2Graph : forall i : I, @Graph (@Index2Vertex i).

  Local Coercion Index2Graph : I >-> Graph.

  Definition ComputableGraphCategory : @SpecializedCategory I.
  Proof.
    refine {|
      Morphism' := (fun C D : I => GraphTranslation C D);
      Identity' := (fun o : I => IdentityGraphTranslation o);
      Compose' := (fun C D E : I => ComposeGraphTranslations (C := C) (D := D) (E := E))
    |};
    abstract graph_translation_eq.
  Defined.
End ComputableGraphCategory.
