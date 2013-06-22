Require Import Setoid.
Require Export Translation.
Require Import Common.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section MetaTranslation.
  Variable C D : Schema.
  Variable F G : Translation C D.

  (* See MetaTranslation for documentation *)
  Record MetaTranslation := {
    SComponentsOf :> forall c : C, path D (F c) (G c);
    SCommutes : forall s d (e : C.(Edge) s d),
      PathsEquivalent _ (concatenate (F.(PathOf) _ _ e) (SComponentsOf d)) (concatenate (SComponentsOf s) (G.(PathOf) _ _ e))
  }.

  Hint Rewrite SCommutes.

  Lemma SCommutes_TransferPath MT : forall s d (p : path C s d),
    PathsEquivalent _ (concatenate (F.(TransferPath) p) (MT.(SComponentsOf) d)) (concatenate (MT.(SComponentsOf) s) (G.(TransferPath) p)).
    intros s d p; induction p; t.
    repeat rewrite concatenate_associative.
    rewrite SCommutes.
    repeat rewrite <- concatenate_associative.
    t.
  Qed.

End MetaTranslation.

Section MetaTranslationComposition.
  Variable C D E : Schema.
  Variable F F' F'' : Translation C D.
  Variable G G' : Translation D E.

  Hint Resolve SCommutes f_equal f_equal2.
  Hint Resolve post_concatenate_equivalent pre_concatenate_equivalent.

  (* See NaturalTransformation for documentation *)
  Definition MTComposeMT (T' : MetaTranslation F' F'') (T : MetaTranslation F F') :
    MetaTranslation F F''.
    refine {| SComponentsOf := (fun c => concatenate (T c) (T' c)) |};
      (* XXX TODO: Find a way to get rid of [e] in the transitivity call *)
      abstract (intros; transitivity (concatenate (concatenate (T _) (PathOf F' _ _ e)) (T' _));
        solve_repeat_rewrite concatenate_associative eauto).
  Defined.

  Hint Rewrite SCommutes.

  Ltac strip_concatenate' :=
    match goal with
      | [ |- ?Rel (concatenate _ _) (concatenate _ _) ] => apply pre_concatenate_equivalent || apply post_concatenate_equivalent
    end.
  Ltac strip_concatenate :=
    repeat (repeat strip_concatenate';
      repeat (rewrite concatenate_associative; try strip_concatenate'); repeat strip_concatenate';
        repeat (rewrite <- concatenate_associative; try strip_concatenate'); repeat strip_concatenate').

  Hint Extern 1 => strip_concatenate.

  Hint Extern 1 =>
    match goal with
      | [ |- ?Rel (concatenate (TransferPath _ ?p) _) (concatenate _ (TransferPath _ ?p)) ] =>
        induction p; simpl; try rewrite concatenate_noedges_p; try reflexivity;
          repeat rewrite concatenate_associative; rewrite SCommutes; strip_concatenate; auto
    end.

  Definition MTComposeT (U : MetaTranslation G G') (T : MetaTranslation F F'):
    MetaTranslation (ComposeTranslations G F) (ComposeTranslations G' F').
    refine (Build_MetaTranslation (ComposeTranslations G F) (ComposeTranslations G' F')
      (fun c => concatenate (U.(SComponentsOf) (F c)) (G'.(TransferPath) (T.(SComponentsOf) c)))
      _);
    abstract (
      intros; simpl;
        repeat rewrite concatenate_associative;
          rewrite <- concatenate_TransferPath;
            rewrite <- SCommutes;
              rewrite concatenate_TransferPath;
                auto
    ).
  Defined.
End MetaTranslationComposition.

Section IdentityMetaTranslation.
  Variable C D : Schema.
  Variable F : Translation C D.

  (* There is an identity natrual transformation. *)
  Definition IdentityMetaTranslation : MetaTranslation F F.
    refine {| SComponentsOf := (fun c => NoEdges)
      |};
    abstract t.
  Defined.
End IdentityMetaTranslation.
