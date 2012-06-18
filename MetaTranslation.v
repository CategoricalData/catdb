Require Import Setoid.
Require Export Translation.
Require Import Common.

Set Implicit Arguments.

Section MetaTranslation.
  Variable C D : Schema.
  Variable F G : Translation C D.

  (* See MetaTranslation for documentation *)
  Record MetaTranslation := {
    SComponentsOf :> forall c : C, path D (F c) (G c);
    SCommutes : forall s d (e : C.(Edge) s d),
      concatenate (F.(PathOf) _ _ e) (SComponentsOf d) = concatenate (SComponentsOf s) (G.(PathOf) _ _ e)
  }.
End MetaTranslation.

Section MetaTranslationComposition.
  Variable C D E : Schema.
  Variable F F' F'' : Translation C D.
  Variable G G' : Translation D E.

  Hint Resolve SCommutes f_equal f_equal2.

  (* See NaturalTransformation for documentation *)
  Definition MTComposeMT (T' : MetaTranslation F' F'') (T : MetaTranslation F F') :
    MetaTranslation F F''.
    refine {| SComponentsOf := (fun c => concatenate (T c) (T' c)) |};
      (* XXX TODO: Find a way to get rid of [m] in the transitivity call *)
      intros; transitivity (concatenate (concatenate (T _) (PathOf F' _ _ e)) (T' _));
        solve_repeat_rewrite concatenate_associative eauto.
  Defined.

  Hint Rewrite SCommutes.

  Ltac strip_concatenate' :=
    match goal with
      | [ |- concatenate ?x _ = concatenate ?x _ ] => f_equal
      | [ |- concatenate _ ?x = concatenate _ ?x ] => f_equal
    end.
  Ltac strip_concatenate :=
    repeat (repeat strip_concatenate';
      repeat (rewrite concatenate_associative; try strip_concatenate'); repeat strip_concatenate';
        repeat (rewrite <- concatenate_associative; try strip_concatenate'); repeat strip_concatenate').

  Hint Extern 1 (_ = _) => strip_concatenate.

  Hint Extern 1 (concatenate (TransferPath _ ?p) _ = concatenate _ (TransferPath _ ?p)) =>
    induction p; simpl; try apply concatenate_noedges_p;
      repeat rewrite concatenate_associative; rewrite SCommutes; strip_concatenate; assumption.

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
