Require Import JMeq ProofIrrelevance.
Require Export SpecializedCategory Functor SigTCategory.
Require Import Common Notations FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Section sigT_sig_obj_mor.
  Context `(A : @SpecializedCategory objA).
  Variable Pobj : objA -> Type.
  Variable Pmor : forall s d : sigT Pobj, A.(Morphism) (projT1 s) (projT1 d) -> Prop.

  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d', forall m1 m2, @Pmor d d' m1 -> @Pmor s d m2 -> @Pmor s d' (Compose (C := A) m1 m2).

  Definition SpecializedCategory_sigT_sig : @SpecializedCategory (sigT Pobj).
    match goal with
      | [ |- @SpecializedCategory ?obj ] =>
        refine (@Build_SpecializedCategory obj
          (fun s d => sig (@Pmor s d))
          (fun x => existT _ (Identity (C := A) (projT1 x)) (Pidentity x))
          (fun s d d' m1 m2 => existT _ (Compose (C := A) (proj1_sig m1) (proj1_sig m2)) (Pcompose (proj2_sig m1) (proj2_sig m2)))
          _
          _
          _
        )
    end;
    abstract (intros; simpl_eq; auto with category).
  Defined.

  Let SpecializedCategory_sigT_sig_as_sigT : @SpecializedCategory (sigT Pobj).
    apply (@SpecializedCategory_sigT _ A _ _ Pidentity Pcompose);
      abstract (
        simpl; intros;
          match goal with
            | [ |- @JMeq ?Ta ?a ?Tb ?b ] => cut (@eq Prop Ta Tb); [
              generalize Ta Tb a b || generalize Tb Ta b a; intros; repeat subst; JMeq_eq; try apply proof_irrelevance
              | ]
          end;
          rewrite Associativity || rewrite LeftIdentity || rewrite RightIdentity;
            reflexivity
      ).
  Defined.

  Definition sigT_sig_functor_sigT : SpecializedFunctor SpecializedCategory_sigT_sig SpecializedCategory_sigT_sig_as_sigT.
    refine (Build_SpecializedFunctor SpecializedCategory_sigT_sig SpecializedCategory_sigT_sig_as_sigT
      (fun x => x)
      (fun s d m => m)
      _
      _
    );
    abstract (intros; simpl; destruct_sig; reflexivity).
  Defined.

  Definition sigT_functor_sigT_sig : SpecializedFunctor SpecializedCategory_sigT_sig_as_sigT SpecializedCategory_sigT_sig.
    refine (Build_SpecializedFunctor SpecializedCategory_sigT_sig_as_sigT SpecializedCategory_sigT_sig
      (fun x => x)
      (fun s d m => m)
      _
      _
    );
    abstract (intros; simpl; destruct_sig; reflexivity).
  Defined.

  Lemma sigT_sig_sigT_compat :
    ComposeFunctors sigT_sig_functor_sigT sigT_functor_sigT_sig = IdentityFunctor _ /\
    ComposeFunctors sigT_functor_sigT_sig sigT_sig_functor_sigT = IdentityFunctor _.
    split; functor_eq; destruct_sig; reflexivity.
  Qed.

  Definition proj1_functor_sigT_sig : SpecializedFunctor SpecializedCategory_sigT_sig A
    := ComposeFunctors projT1_functor sigT_sig_functor_sigT.
End sigT_sig_obj_mor.
