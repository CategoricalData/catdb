Require Import ProofIrrelevance.
Require Export SpecializedCategory SpecializedFunctor.
Require Import Common.

Set Implicit Arguments.

Section GroupoidOf.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Inductive GroupoidOf_Morphism (s d : objC) :=
  | hasMorphism : morC s d -> GroupoidOf_Morphism s d
  | hasInverse : morC d s -> GroupoidOf_Morphism s d
  | byComposition : forall e, GroupoidOf_Morphism e d -> GroupoidOf_Morphism s e -> GroupoidOf_Morphism s d.

  Definition GroupoidOf_Compose (s d d' : C) :
    inhabited (GroupoidOf_Morphism d d') ->
    inhabited (GroupoidOf_Morphism s d) ->
    inhabited (GroupoidOf_Morphism s d').
    intros; destruct_type @inhabited; constructor; eapply byComposition; eauto.
  Defined.

  (** Quoting Wikipedia:
     A groupoid is a small category in which every morphism is an isomorphism, and hence invertible.
     *)
  Definition GroupoidOf : @SpecializedCategory objC
    (fun s d => inhabited (GroupoidOf_Morphism s d)).
    refine {|
      Identity' := (fun o : C => inhabits (hasMorphism (Identity o)));
      Compose' := @GroupoidOf_Compose
    |};
    abstract (simpl; intros; apply proof_irrelevance).
  Defined.

  Definition CategoryIsGroupoid : Prop :=
    forall s d : C, forall m : Morphism C s d, IsCategoryIsomorphism m.
End GroupoidOf.

Section Groupoid.
  Variable objC : Type.
  Variable morC : objC -> objC -> Type.
  Variable C : SpecializedCategory morC.

  Lemma GroupoidOf_Groupoid : CategoryIsGroupoid (GroupoidOf C).
    Transparent Morphism.
    hnf; intros s d m; hnf; destruct m as [ m ]; induction m;
      repeat
        match goal with
          | [ H : exists _, _ |- _ ] => destruct H; destruct_type @inhabited
          | [ m : _ |- _ ] => exists m
          | [ m : _ |- _ ] => unique_pose (inhabits (hasMorphism morC _ _ m))
          | [ m : _ |- _ ] => unique_pose (inhabits (hasInverse morC _ _ m))
          | [ m : _, m' : _ |- _ ] => unique_pose (inhabits (byComposition m m'))
        end;
        hnf; repeat split; unfold Morphism; try apply proof_irrelevance.
  Qed.

  Definition Groupoid_Functor : SpecializedFunctor C (GroupoidOf C).
    refine {| ObjectOf' := (fun c => c);
      MorphismOf' := (fun s d m => inhabits (hasMorphism morC s d m))
    |}; abstract (simpl; intros; apply proof_irrelevance).
  Defined.
End Groupoid.
