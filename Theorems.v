Require Import Program.
Require Import Definitions.

Set Implicit Arguments.


Ltac t := simpl; intuition;
  repeat (match goal with
            | [ H : _ |- _ ] => rewrite H
            | _ => progress autorewrite with core in *
          end; auto).

Section Functor_Instance.
  Variables C D : Category.
  Variable F : Functor C D.
  Variable I : Instance D.

  Lemma compose_prepend : forall s d (p : path D s d) s' (E : D.(Edge) s' s) x,
    compose I (FunctionOf I) (prepend p E) x
    = compose I (FunctionOf I) p (I.(FunctionOf) _ _ E x).
    induction p; t.
  Qed.

  Hint Rewrite compose_prepend.

  Lemma compose_concatenate : forall s d (p : path D s d) d' (p' : path D d d') x,
    compose I (FunctionOf I) (concatenate p p') x
    = compose I (FunctionOf I) p' (compose I (FunctionOf I) p x).
    induction p; t.
  Qed.

  Hint Rewrite compose_concatenate.

  Lemma compose_transferPath : forall s d (p : path C s d) x,
    compose I (FunctionOf I) (transferPath F (PathOf F) p) x
    = compose (fun x0 : C => I (F x0))
    (fun s0 d0 (E : Edge C s0 d0) =>
      compose I (FunctionOf I) (PathOf F s0 d0 E)) p x.
    induction p; t.
  Qed.    

  Hint Rewrite <- compose_transferPath.

  Hint Resolve EquivalenceOf FEquivalenceOf.

  Definition Functor_Instance : Instance C.
    refine {| TypeOf := (fun x => I (F x));
      FunctionOf := (fun _ _ E => compose _ (I.(FunctionOf)) (F.(PathOf) _ _ E)) |};
    abstract t.
  Defined.
End Functor_Instance.
