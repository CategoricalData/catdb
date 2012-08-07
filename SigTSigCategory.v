Require Import JMeq ProofIrrelevance.
Require Export SpecializedCategory Functor SigTCategory.
Require Import Common FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Local Infix "==" := JMeq (at level 70).

Section sigT_sig_obj_mor.
  Local Transparent Morphism Object.

  Context `(A : @SpecializedCategory objA morA).
  Variable Pobj : objA -> Type.
  Variable Pmor : forall s d : sigT Pobj, morA (projT1 s) (projT1 d) -> Prop.

  Variable Pidentity : forall x, @Pmor x x (Identity (C := A) _).
  Variable Pcompose : forall s d d', forall m1 m2, @Pmor d d' m1 -> @Pmor s d m2 -> @Pmor s d' (Compose (C := A) m1 m2).

  Hint Resolve Associativity LeftIdentity RightIdentity.

  Definition SpecializedCategory_sigT_sig : @SpecializedCategory (sigT Pobj) (fun s d => sig (@Pmor s d)).
    match goal with
      | [ |- @SpecializedCategory ?obj ?mor ] =>
        refine (@Build_SpecializedCategory obj mor
          (fun x => existT _ (Identity (C := A) (projT1 x)) (Pidentity x))
          (fun s d d' m1 m2 => existT _ (Compose (C := A) (proj1_sig m1) (proj1_sig m2)) (Pcompose (proj2_sig m1) (proj2_sig m2)))
          _
          _
          _
        )
    end;
    abstract (intros; simpl_eq; present_spcategory_all; trivial).
  Defined.

  Let SpecializedCategory_sigT_sig_as_sigT : @SpecializedCategory (sigT Pobj) (fun s d => sigT (@Pmor s d)).
    apply (@SpecializedCategory_sigT _ _ A _ _ Pidentity Pcompose);
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
