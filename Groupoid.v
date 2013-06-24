Require Import ProofIrrelevance.
Require Export Category Functor.
Require Import Common CategoryIsomorphisms.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section GroupoidOf.
  Variable C : Category.

  Inductive GroupoidOf_Morphism (s d : C) :=
  | hasMorphism : C.(Morphism) s d -> GroupoidOf_Morphism s d
  | hasInverse : C.(Morphism) d s -> GroupoidOf_Morphism s d
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
  Definition GroupoidOf : Category.
    refine (@Build_Category _
                                       (fun s d => inhabited (GroupoidOf_Morphism s d))
                                       (fun o : C => inhabits (hasMorphism _ _ (Identity o)))
                                       (@GroupoidOf_Compose)
                                       _
                                       _
                                       _);
    abstract (simpl; intros; apply proof_irrelevance).
  Defined.

  Definition CategoryIsGroupoid : Prop :=
    forall s d : C, forall m : Morphism C s d, IsIsomorphism m.
End GroupoidOf.

Hint Constructors GroupoidOf_Morphism : category.

Section Groupoid.
  Variable C : Category.

  Lemma GroupoidOf_Groupoid : CategoryIsGroupoid (GroupoidOf C).
    hnf; intros s d m; hnf; destruct m as [ m ]; induction m;
      repeat
        match goal with
          | [ H : exists _, _ |- _ ] => destruct H; destruct_type @inhabited
          | [ m : _ |- _ ] => exists m
          | [ m : _ |- _ ] => unique_pose (inhabits (hasMorphism C _ _ m))
          | [ m : _ |- _ ] => unique_pose (inhabits (hasInverse C _ _ m))
          | [ m : _, m' : _ |- _ ] => unique_pose (inhabits (byComposition C _ _ _ m m'))
          | [ m : _, m' : _ |- _ ] => unique_pose (Compose m m')
          | [ |- @eq ?T ?a ?b ] => progress let T' := eval hnf in T in change T with T'
          | [ |- _ = _ ] => apply proof_irrelevance
          | _ => progress (hnf; repeat split)
        end.
  Qed.

  Definition Groupoid_Functor : Functor C (GroupoidOf C).
    refine (Build_Functor C (GroupoidOf C)
      (fun c => c)
      (fun s d m => inhabits (hasMorphism C _ _ m))
      _
      _
    );
    abstract (simpl; intros; apply proof_irrelevance).
  Defined.
End Groupoid.
