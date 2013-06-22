Require Import ProofIrrelevance JMeq.
Require Export Graph Paths.
Require Import Common StructureEquality Notations FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Section Graphs.
  Context `(G : Graph v).
  Context `(H : Graph w).

  Record GraphTranslation := {
    VertexOf' : v -> w;
    EdgeOf' : forall s d, G.(Edge') s d -> H.(Edge') (VertexOf' s) (VertexOf' d)
  }.

  Section GraphInterface.
    Context `(T : GraphTranslation).

    Definition VertexOf : G -> H := Eval cbv beta delta [VertexOf'] in T.(VertexOf').
    Definition EdgeOf : forall s d : G, G.(Edge) s d -> H.(Edge) (VertexOf s) (VertexOf d) :=
      Eval cbv beta delta [EdgeOf'] in T.(EdgeOf').
  End GraphInterface.
End Graphs.

Coercion VertexOf : GraphTranslation >-> Funclass.

Arguments VertexOf {v G w H} T x : simpl nomatch.
Arguments EdgeOf {v G w H} T [s d] p : simpl nomatch.

Section GraphTranslations_Equal.
  Lemma GraphTranslations_Equal v G w H : forall (T U : @GraphTranslation v G w H),
    VertexOf T = VertexOf U
    -> (VertexOf T = VertexOf U -> EdgeOf T == EdgeOf U)
    -> T = U.
  Proof.
    destruct T, U; simpl; intros; specialize_all_ways; repeat subst;
      reflexivity.
  Qed.

  Lemma GraphTranslations_JMeq v G w H v' G' w' H' :
    forall (T : @GraphTranslation v G w H) (U : @GraphTranslation v' G' w' H'),
      v = v'
      -> w = w'
      -> (v = v' -> G == G')
      -> (w = w' -> H == H')
      -> (v = v' -> G == G'
        -> w = w' -> H == H'
        -> VertexOf T == VertexOf U)
      -> (v = v' -> G == G'
        -> w = w' -> H == H'
        -> VertexOf T == VertexOf U
        -> EdgeOf T == EdgeOf U)
      -> T == U.
  Proof.
    simpl; intros; intuition; repeat subst; destruct T, U; simpl in *.
      repeat subst; reflexivity.
  Qed.
End GraphTranslations_Equal.

Ltac graph_translation_eq_step_with tac :=
  structures_eq_step_with_tac ltac:(apply GraphTranslations_Equal || apply GraphTranslations_JMeq) tac.

Ltac graph_translation_eq_with tac := repeat graph_translation_eq_step_with tac.

Ltac graph_translation_eq_step := graph_translation_eq_step_with idtac.
Ltac graph_translation_eq := graph_translation_eq_with idtac.

Section GraphTranslationComposition.
  Context `(B : @Graph vertB).
  Context `(C : @Graph vertC).
  Context `(D : @Graph vertD).
  Context `(E : @Graph vertE).

  Definition ComposeGraphTranslations (G : GraphTranslation D E) (F : GraphTranslation C D) : GraphTranslation C E :=
    {| VertexOf' := (fun c => G (F c));
      EdgeOf' := (fun _ _ m => G.(EdgeOf) (F.(EdgeOf) m)) |}.
End GraphTranslationComposition.

Section IdentityGraphTranslation.
  Context `(C : @Graph vertC).

  (* There is an identity graph translation.  It does the obvious thing. *)
  Definition IdentityGraphTranslation : GraphTranslation C C :=
    {| VertexOf' := (fun x => x);
      EdgeOf' := (fun _ _ x => x) |}.
End IdentityGraphTranslation.

Section GraphTranslationCompositionLemmas.
  Context `(B : @Graph vertB).
  Context `(C : @Graph vertC).
  Context `(D : @Graph vertD).
  Context `(E : @Graph vertE).

  Lemma ComposeGraphTranslationsAssociativity (F : GraphTranslation B C) (G : GraphTranslation C D) (H : GraphTranslation D E) :
    ComposeGraphTranslations (ComposeGraphTranslations H G) F = ComposeGraphTranslations H (ComposeGraphTranslations G F).
  Proof.
    reflexivity.
  Qed.
End GraphTranslationCompositionLemmas.
