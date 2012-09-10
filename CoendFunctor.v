Require Import ProofIrrelevance.
Require Export Coend LimitFunctors.
Require Import Common Notations ChainCategory.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope type_scope.

Section Coend.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Let COp := OppositeCategory C.

  Variable F : SpecializedFunctor (COp * C) D.

  Definition CoendFunctor_Index_Object := { ds : objC * objC & Morphism C (snd ds) (fst ds) } + objC.

  Global Arguments CoendFunctor_Index_Object /.

(*  Let dom_obj : { n | n <= 1 } := exist _ 0 (le_S _ _ (le_n 0)).
  Let cod_obj : { n | n <= 1 } := exist _ 1 (le_n 1).
  Let mor_mor : Morphism [1] dom_obj cod_obj := proj2_sig dom_obj.*)

  Definition CoendFunctor_Index_Morphism (s d : CoendFunctor_Index_Object) : Set :=
    match (s, d) with
      | (inl sdm, inr c) => (fst (projT1 sdm) = c) + (snd (projT1 sdm) = c)
      | _ => (s = d)
    end.

  Global Arguments CoendFunctor_Index_Morphism s d /.

  Definition CoendFunctor_Index_Identity x : CoendFunctor_Index_Morphism x x :=
    match x as s return (CoendFunctor_Index_Morphism s s) with
      | inl s => eq_refl (*identity_dep_refl _*)
      | inr s => eq_refl (*identity_dep_refl _*)
    end.

  Global Arguments CoendFunctor_Index_Identity x /.

  Local Ltac atomic x :=
    match x with
      | ?f _ => fail 1
      | (fun _ => _) => fail 1
      | _ => idtac
    end.

  Local Ltac simpl_identity :=
    repeat match goal with
             | _ => apply proof_irrelevance
             | [ H : ?a = ?a |- _ ] => destruct H
             | [ H : ?a = ?a |- _ ] => replace H with (@eq_refl _ a) in *; [ | apply proof_irrelevance ]; clear H
             | [ |- ?a = ?b ] => cut (@eq Prop a b); [
               let H := fresh in intro H; (rewrite H; reflexivity) || (rewrite <- H; reflexivity)
               | apply proof_irrelevance
             ]
             | [ H : inl _ = inl _ |- _ ] => injection H; clear H; intro H; subst
             | [ H : inr _ = inr _ |- _ ] => injection H; clear H; intro H; subst
             | [ H : inl _ = inr _ |- _ ] => discriminate H
             | [ H : inr _ = inl _ |- _ ] => discriminate H
             | [ H : _ = _ |- _ ] => progress (injection H; intro; subst)
             | [ |- _ = _ ] => constructor
             | _ => progress (repeat subst)
           end.

  Local Ltac simpl_CoendFunctor_index :=
    repeat match goal with
             | _ => progress simpl_identity
             | [ H : (_ + _)%type |- _ ] => destruct H
             | [ H : (_ * _)%type |- _ ] => destruct H
             | _ => progress (hnf in *; trivial)
             | [ |- (_ + _)%type ] => solve [ left; simpl_CoendFunctor_index ] || solve [ right; simpl_CoendFunctor_index ]
           end.

  Definition CoendFunctor_Index_Compose s d d' (m1 : CoendFunctor_Index_Morphism d d') (m2 : CoendFunctor_Index_Morphism s d) :
    CoendFunctor_Index_Morphism s d'.
  Proof.
    destruct s, d, d';
      try solve [ simpl_CoendFunctor_index ].
  Defined.

  Local Ltac destruct_in_eq_type := intros;
    let T' := fresh in
      match goal with
        | [ |- @eq ?T _ _ ] => pose T as T'
      end;
      repeat match eval hnf in T' with
               | match ?x with _ => _ end => destruct x
             end;
      simpl in T';
        match goal with
          | [ |- ?a = ?b ] => change (@eq T' a b); unfold T'; try apply proof_irrelevance
        end.

  Local Ltac destruct_if_atomic_and_sum x := atomic x; let t := type of x in
    match eval hnf in t with
      | (_ + _)%type => let H := fresh in destruct x as [ H | H ];
        try (destruct H; reflexivity)
    end.

  Local Ltac simpl_CoendFunctor_index_quicker :=
    try destruct_in_eq_type;
      try reflexivity;
        try match goal with
              | [ |- ?a = ?b ] => first [ destruct_if_atomic_and_sum a | destruct_if_atomic_and_sum b ]
            end;
        repeat match goal with
                 | _ => reflexivity
                 | [ H : _ |- _ ] => discriminate H || clear H
                 | [ H : _ |- _ ] => hnf in H;
                   match type of H with
                     | _ = _ => progress subst
                     | ?a = ?a => case H; clear H
                     | @eq ?T ?a ?a => replace H with (@eq_refl T a) in *;
                       [ clear H | apply proof_irrelevance ]
                     | inl _ = inl _ => injection H; try clear H; intro; subst
                     | inr _ = inr _ => injection H; try clear H; intro; subst
                     | (_ + _)%type => destruct H
                   end
               end.

  Definition CoendFunctor_Index : SpecializedCategory CoendFunctor_Index_Object.
  Proof.
    refine {|
      Morphism' := CoendFunctor_Index_Morphism;
      Identity' := CoendFunctor_Index_Identity;
      Compose' := CoendFunctor_Index_Compose
    |}; (*
    abstract (
      intros;
        simpl_CoendFunctor_index
    ). *) (* the following cuts off 4 seconds.  not sure if it's worth it *)
    abstract simpl_CoendFunctor_index_quicker.
  Defined.

  Definition CoendFunctor_Diagram_ObjectOf : CoendFunctor_Index -> D :=
    fun x => match x with
               | inl c0c1 => F (projT1 c0c1)
               | inr c => F (c, c)
             end.

  Global Arguments CoendFunctor_Diagram_ObjectOf _ /.

  Definition CoendFunctor_Diagram_MorphismOf s d (m : CoendFunctor_Index_Morphism s d) :
    Morphism D (CoendFunctor_Diagram_ObjectOf s) (CoendFunctor_Diagram_ObjectOf d).
  Proof.
    simpl.
    match goal with
      | [ |- Morphism ?D
        match ?s with
          | inl sa => @?sa' sa
          | inr sb => @?sb' sb
        end
        match ?d with
          | inl da => @?da' da
          | inr db => @?db' db
        end ] =>
      refine (match (s, d) as sd return
                (CoendFunctor_Index_Morphism (fst sd) (snd sd)
                  -> Morphism D
                  match (fst sd) with
                    | inl sa => sa' sa
                    | inr sb => sb' sb
                  end
                  match (snd sd) with
                    | inl da => da' da
                    | inr db => db' db
                  end)
                with
                | (inl s', inl d') => fun m' => F.(MorphismOf) _
                | (inl s', inr d') => fun m' => F.(MorphismOf) _
                | (inr s', inl d') => fun m' => F.(MorphismOf) _
                | (inr s', inr d') => fun m' => F.(MorphismOf) _
              end m)
    end;
    simpl in m' |- *;
      split; present_spcategory;
        try discriminate m';
          try solve [ injection m'; clear m'; intro m'; case m'; apply Identity ];
            destruct m' as [ m' | m' ];
              try solve [ case m'; apply Identity || exact (projT2 s') ].
  Defined.

  Definition CoendFunctor_Diagram : SpecializedFunctor CoendFunctor_Index D.
  Proof.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          CoendFunctor_Diagram_ObjectOf
          CoendFunctor_Diagram_MorphismOf
          _
          _
        )
    end;
    abstract (
      simpl_CoendFunctor_index_quicker;
      present_spcategory;
      unfold CoendFunctor_Diagram_MorphismOf; simpl;
        repeat rewrite FIdentityOf;
          auto
    ).
  Defined.

  Hypothesis HasColimits : forall G : SpecializedFunctor CoendFunctor_Index D, Colimit G.

  Definition CoendFunctor := ColimitFunctor HasColimits.
End Coend.

(* TODO: Figure out why the notation for this is the same as the notation for the Grothendieck construction *)
(*Notation "∫ F" := (Coend F).*)
