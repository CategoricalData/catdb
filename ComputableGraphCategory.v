Require Export Category Graph GraphTranslation.
Require Import Common.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section ComputableGraphCategory.
  Variable I : Type.
  Variable Index2Vertex : I -> Type.
  Variable Index2Graph : forall i : I, @Graph (@Index2Vertex i).

  Local Coercion Index2Graph : I >-> Graph.

  Definition ComputableGraphCategory : Category.
    refine (@Build_Category _
                                       (fun C D : I => GraphTranslation C D)
                                       (fun o : I => IdentityGraphTranslation o)
                                       (fun C D E : I => ComposeGraphTranslations (C := C) (D := D) (E := E))
                                       _
                                       _
                                       _);
    abstract graph_translation_eq.
  Defined.
End ComputableGraphCategory.
