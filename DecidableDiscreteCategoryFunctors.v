Require Import FunctionalExtensionality Eqdep_dec ProofIrrelevance JMeq.
Require Export DiscreteCategoryFunctors DecidableDiscreteCategory DecidableSetCategory DecidableComputableCategory DecidableCat.
Require Import Common Adjoint.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section eq_dec_prop.
  Lemma eq_dec_prop T (eq_dec : forall x y : T, {x = y} + {x <> y}) : forall x y : T, x = y \/ x <> y.
    intros x y; case (eq_dec x y); intuition.
  Qed.
End eq_dec_prop.

Section Obj.
  Local Ltac build_ob_functor Index2Cat :=
    let C := match goal with | [ |- Functor ?C ?D ] => constr:(C) end in
    let D := match goal with | [ |- Functor ?C ?D ] => constr:(D) end in
    refine (Build_Functor C D
                                     (fun C' => existT _ (Object (Index2Cat (projT1 C'))) (projT2 C'))
                                     (fun _ _ F => ObjectOf F)
                                     _
                                     _
           );
      intros; simpl in *; reflexivity.

  Section type.
    Variable I : Type.
    Variable Index2Cat : I -> Category.

    Definition ObjectFunctorDec : Functor (@ComputableCategoryDec _ Index2Cat) TypeCatDec.
      build_ob_functor Index2Cat.
    Defined.
  End type.
End Obj.

Arguments ObjectFunctorDec {I Index2Cat}.

Section InducedFunctor.
  Variable O : Type.
  Variable O' : Category.
  Variable f : O -> O'.
  Variable eq_dec : forall x y : O, {x = y} + {x <> y}.

  Hint Unfold Object.

  Local Ltac t' := intros; simpl in *; autounfold with core in *; repeat subst; trivial.
  Local Ltac t := t';
    repeat match goal with
             | _ => reflexivity
             | _ => apply Identity; assumption
             | [ H : appcontext[eq_dec ?a ?b] |- _ ] => destruct (eq_dec a b); t'
             | [ |- appcontext[eq_dec ?a ?b] ] => destruct (eq_dec a b); t'
             | [ H : _ |- _ ] => specialize (H (eq_refl _)); t'
             | [ H : False |- _ ] => destruct H
             | [ H : Empty_set |- _ ] => destruct H
             | [ H : unit |- _ ] => destruct H
             | [ |- _ = _ ] => progress (repeat rewrite RightIdentity; repeat rewrite LeftIdentity; repeat rewrite Associativity)
             | [ H : ?a = ?a |- _ ] => pose proof (UIP_refl _ _ H); subst H
             | [ H : _ |- _ ] => unique_pose (H eq_refl)
             | [ H : Morphism _ _ _ |- _ ] => hnf in H
             | [ H : _ = _ |- _ ] => case H; try clear H
           end.

  Definition InducedDiscreteFunctorDec_MorphismOf s d (m : Morphism (DiscreteCategoryDec eq_dec) s d) :
    Morphism O' (f s) (f d).
    t.
  Defined.

  Hint Unfold InducedDiscreteFunctorDec_MorphismOf.
  Hint Unfold DiscreteCategoryDec_Compose.
  Hint Unfold eq_rect_r eq_rect eq_sym.

  Local Arguments Compose [C s d d'] / _ _ : rename, simpl nomatch.

  Definition InducedDiscreteFunctorDec : Functor (DiscreteCategoryDec eq_dec) O'.
    match goal with
      | [ |- Functor ?C ?D ] =>
        refine (Build_Functor C D
          f
          InducedDiscreteFunctorDec_MorphismOf
          _
          _
        )
    end;
    t.
  Defined.
End InducedFunctor.

Local Ltac destruct_eq_dec eq_dec a b :=
  match type of eq_dec with
    | forall x y : _, {x = y} + {x <> y} => destruct (eq_dec a b)
    | forall x y : _, {x = y} + {x = y -> False} => destruct (eq_dec a b)
  end;
  repeat subst; trivial; intros.

Local Ltac t_dec := repeat (intros; simpl in *; autounfold with core in *; simpl in *; trivial;
  match goal with
    | [ |- _ = _ ] => apply functional_extensionality_dep; intro
    | _ => progress functor_eq
    | [ H0 : appcontext[?H ?a ?b] |- _ ] => revert H0; destruct_eq_dec H a b
    | [ |- appcontext[?H ?a ?b] ] => destruct_eq_dec H a b
    | _ => progress (unfold Morphism, Object, InducedDiscreteFunctorDec_MorphismOf in *)
    | _ => progress destruct_sig
    | [ H : unit |- _ ] => destruct H
    | [ H : ?a = ?a, eq_dec : _ |- _ ] => pose proof (eq_proofs_unicity (eq_dec_prop eq_dec) H eq_refl); subst H
    | [ H : _ |- _ ] => unique_pose (H eq_refl)
    | _ => progress destruct_to_empty_set
    | [ H0 : appcontext[?H ?a ?b] |- appcontext[?H ?a ?b] ] => revert H0; destruct_eq_dec H a b
    | [ H : ?a = ?b |- _ ] => pose proof H; first [ subst a | subst b ]
  end
).

Section disc.
  Hint Unfold DiscreteCategoryDec_Identity.
  Hint Unfold eq_rect_r eq_rect eq_sym.

  Definition DiscreteFunctorDec : Functor TypeCatDec CatDec.
    refine (Build_Functor TypeCatDec CatDec
      (fun O => existT
        (fun C : Category => forall x y : C, {x = y} + {x <> y})
        (DiscreteCategoryDec (projT2 O) : Category)
        (fun x y => projT2 O x y))
      (fun s d f => InducedDiscreteFunctorDec (DiscreteCategoryDec (projT2 d)) f (projT2 s))
      _
      _
    );
    admit.
    (* t_dec.
    match goal with
      | [ H : if ?eq_dec ?a ?b then unit else Empty_set |- _ ] => cut (JMeq H tt); [ intro | destruct_eq_dec eq_dec a b ]
    end.
    apply JMeq_eq.
    symmetry.
    (*
    Require Import Setoid.
    etransitivity; [ apply H | clear H ].
    compute.
    assert (JMeq match
                s x0 x0 as s0 return (if s0 then unit else Empty_set)
              with
              | left _ => tt
              | right n => match n eq_refl return Empty_set with
                           end
              end tt).
    destruct (s x0 x0); trivial.
    change ((match
        s x x0 as s0
        return
          ((if s0 then unit else Empty_set) ->
           if s x x0 then unit else Empty_set)
      with
      | left e =>
          fun _ : unit =>
          match
            match e in (_ = y) return (y = x) with
            | eq_refl => eq_refl
            end in (_ = y) return (if s y x0 then unit else Empty_set)
          with
          | eq_refl =>
              match
                s x0 x0 as s0 return (if s0 then unit else Empty_set)
              with
              | left _ => tt
              | right n => match n eq_refl return Empty_set with
                           end
              end
          end
      | right _ =>
          fun m : Empty_set =>
          match m return (if s x x0 then unit else Empty_set) with
          end
      end x1)) with ((match
        s x x0 as s0
        return
          ((if s0 then unit else Empty_set) ->
           if s x x0 then unit else Empty_set)
      with
      | left e =>
          fun _ : unit =>
          match
            match e in (_ = y) return (y = x) with
            | eq_refl => eq_refl
            end in (_ = y) return (if s y x0 then unit else Empty_set)
          with
          | eq_refl =>
              match
                s x0 x0 as s0 return (if s0 then unit else Empty_set)
              with
              | left _ => tt
              | right n => match n eq_refl return Empty_set with
                           end
              end
          end
      | right _ =>
          fun m : Empty_set =>
          match m return (if s x x0 then unit else Empty_set) with
          end
       end x1)). *)
    admit. *)
  Defined.

  Definition DiscreteSetFunctorDec : Functor SetCatDec CatDec.
    refine (Build_Functor SetCatDec CatDec
      (fun O => existT
        (fun C : Category => forall x y : C, {x = y} + {x <> y})
        (DiscreteCategoryDec (projT2 O) : Category)
        (fun x y => projT2 O x y))
      (fun s d f => InducedDiscreteFunctorDec (DiscreteCategoryDec (projT2 d)) f (projT2 s))
      _
      _
    );
    admit.
  Defined.
End disc.

Section Adjoints.
  Local Ltac t :=
    repeat match goal with
             | _ => progress trivial
             | _ => progress repeat (apply functional_extensionality_dep; intro)
             | _ => hnf in *;
               match goal with
                 | [ H : _ = _ |- _ ] => destruct H; simpl in *
               end
             | _ => rewrite FIdentityOf
             | _ => progress functor_eq
           end.

  Lemma DiscreteObjectIdentityDec : ComposeFunctors ObjectFunctorDec DiscreteFunctorDec = IdentityFunctor _.
    functor_eq; simpl_eq; reflexivity.
  Qed.

  Definition DiscreteObjectAdjunction : HomAdjunction DiscreteFunctorDec ObjectFunctorDec.
    match goal with
      | [ |- HomAdjunction ?F ?G ] =>
        refine (Build_HomAdjunction F G
          (fun _ _ F => (fun x => F x))
          _
          _
        )
    end;
    try abstract trivial;
      simpl; intros.
    exists (fun f => (InducedDiscreteFunctorDec _ f (projT2 A)));
      (*t.
      unfold InducedDiscreteFunctorDec_MorphismOf.
      destruct A; simpl in *.
      unfold eq_rect_r.
      unfold eq_rect.
      unfold eq_sym.
      apply JMeq_eq.
      revert m.
      destruct A'; simpl in *.
      clear.
      destruct x.
      simpl in *.
      clear.
      destruct x1; simpl in *; clear.
generalize dependent (s0 s d).
      match goal with
        | [ H : if ?x then _ else _ |- _ ] => destruct x
      end. *)
    admit.
  Defined.
End Adjoints.
