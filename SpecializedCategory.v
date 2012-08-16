Require Import ProofIrrelevance.
Require Export Notations.
Require Import Common StructureEquality.

Set Implicit Arguments.

Record SpecializedCategory (obj : Type) (Morphism : obj -> obj -> Type) := {
  Object :> _ := obj;

  Identity' : forall o, Morphism o o;
  Compose' : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d';

  Associativity' : forall o1 o2 o3 o4 (m1 : Morphism o1 o2) (m2 : Morphism o2 o3) (m3 : Morphism o3 o4),
    Compose' (Compose' m3 m2) m1 = Compose' m3 (Compose' m2 m1);
  LeftIdentity' : forall a b (f : Morphism a b), Compose' (Identity' b) f = f;
  RightIdentity' : forall a b (f : Morphism a b), Compose' f (Identity' a) = f
}.

Bind Scope category_scope with SpecializedCategory.

Arguments Object {obj%type mor} C%category : rename.
Arguments Identity' {obj%type mor} C%category o : rename.
Arguments Compose' {obj%type mor} C%category s d d' _ _ : rename.

Section SpecializedCategoryInterface.
  Variable obj : Type.
  Variable mor : obj -> obj -> Type.
  Variable C : @SpecializedCategory obj mor.

  Definition Morphism : forall s d : C, _ := mor.
  Definition Identity : forall o : C, Morphism o o := Eval cbv beta delta [Identity'] in C.(Identity').
  Definition Compose : forall (s d d' : C) (m : Morphism d d') (m0 : Morphism s d), Morphism s d' := Eval cbv beta delta [Compose'] in C.(Compose').
  Definition Associativity : forall (o1 o2 o3 o4 : C) (m1 : Morphism o1 o2) (m2 : Morphism o2 o3) (m3 : Morphism o3 o4),
    Compose (Compose m3 m2) m1 = Compose m3 (Compose m2 m1)
    := C.(Associativity').
  Definition LeftIdentity : forall (a b : C) (f : Morphism a b),
    Compose (Identity b) f = f
    := C.(LeftIdentity').
  Definition RightIdentity : forall (a b : C) (f : Morphism a b),
    Compose f (Identity a) = f
    := C.(RightIdentity').

  Lemma unfold_Object : @Object obj mor C = obj. reflexivity. Qed.
  Lemma unfold_Morphism : Morphism = (mor : Object C -> Object C -> Type). reflexivity. Qed.
  Lemma unfold_Identity : Identity = (C.(Identity') : forall o : C, Morphism o o). reflexivity. Qed.
  Lemma unfold_Compose : Compose = (C.(Compose') : forall (s d d' : C), Morphism d d' -> Morphism s d -> Morphism s d'). reflexivity. Qed.
End SpecializedCategoryInterface.

Arguments Object {obj mor} C : rename, simpl never.
Arguments Morphism {obj mor} C s d : rename, simpl never.
Arguments Compose {obj mor} [C s d d'] m m0 : simpl nomatch.
Arguments Identity {obj mor} [C] o : simpl nomatch.

Global Opaque Associativity LeftIdentity RightIdentity.

Ltac unfold_Object :=
  repeat match goal with
           | [ _ : appcontext[@Object ?obj ?mor ?C] |- _ ] => change (@Object obj mor C) with obj in *
           | [ |- appcontext[@Object ?obj ?mor ?C] ] => change (@Object obj mor C) with obj in *
         end.

Ltac unfold_Morphism :=
  repeat match goal with
           | [ _ : appcontext[@Morphism ?obj ?mor ?C] |- _ ] => change (@Morphism obj mor C) with mor in *
           | [ |- appcontext[@Morphism ?obj ?mor ?C] ] => change (@Morphism obj mor C) with mor in *
         end.

Ltac sanitize_spcategory :=
  repeat match goal with
           | [ _ : appcontext[fun x => ?f x] |- _ ] => progress change (fun x => f x) with f in *
           | [ |- appcontext[fun x => ?f x] ] => progress change (fun x => f x) with f in *
           | [ _ : appcontext [?f (@Morphism ?obj ?mor ?C) ?C] |- _ ] => progress change (f (@Morphism obj mor C) C) with (f mor C) in *
           | [ |- appcontext [?f (@Morphism ?obj ?mor ?C) ?C] ] => progress change (f (@Morphism obj mor C) C) with (f mor C) in *
           | [ _ : appcontext [?f (@Object ?obj ?mor ?C) ?mor ?C] |- _ ] => progress change (f (@Object obj mor C) mor C) with (f obj mor C) in *
           | [ |- appcontext [?f (@Object ?obj ?mor ?C) ?mor ?C] ] => progress change (f (@Object obj mor C) mor C) with (f obj mor C) in *
         end.

Ltac present_mor_all mor_fun cat :=
  repeat match goal with
           | [ _ : appcontext[mor_fun ?s ?d] |- _ ] => progress change (mor_fun s d) with (@Morphism _ mor_fun cat s d) in *
           | [ |- appcontext[mor_fun ?s ?d] ] => progress change (mor_fun s d) with (@Morphism _ mor_fun cat s d) in *
         end.

Ltac present_mor mor_fun cat :=
  repeat match goal with
           | [ _ : mor_fun ?s ?d |- _ ] => progress change (mor_fun s d) with (@Morphism _ mor_fun cat s d) in *
         end.

Ltac present_mor_from_context cmd :=
  repeat match goal with
           | [ _ : appcontext[cmd ?obj ?mor ?C] |- _ ] => progress present_mor mor C
           | [ |- appcontext[cmd ?obj ?mor ?C] ] => progress present_mor mor C
         end.

Ltac present_obj_mor from to :=
  repeat match goal with
           | [ _ : appcontext[from ?obj ?mor ?C] |- _ ] => progress change (from obj mor) with (to obj mor) in *
           | [ |- appcontext[from ?obj ?mor ?C] ] => progress change (from obj mor) with (to obj mor) in *
         end.

Ltac present_spcategory' := present_obj_mor @Identity' @Identity; present_obj_mor @Compose' @Compose;
  repeat match goal with
           | [ C : @SpecializedCategory ?obj ?mor |- _ ] => progress present_mor mor C
         end.

Ltac present_spcategory := present_obj_mor @Identity' @Identity; present_obj_mor @Compose' @Compose;
  repeat match goal with
           | [ C : @SpecializedCategory ?obj ?mor |- _ ] => progress present_mor mor C
         end;
  sanitize_spcategory.

Ltac present_spcategory_all := present_obj_mor @Identity' @Identity; present_obj_mor @Compose' @Compose;
  repeat match goal with
           | [ C : @SpecializedCategory ?obj ?mor |- _ ] => progress (present_mor_all mor C; sanitize_spcategory)
         end;
  sanitize_spcategory.

Ltac present_spcategory_all_obj_mor := present_obj_mor @Identity' @Identity; present_obj_mor @Compose' @Compose;
  repeat match goal with
           | [ C : @SpecializedCategory ?obj ?mor |- _ ] => progress (change_in_all mor with (@Morphism obj mor C); sanitize_spcategory)
           | [ C : @SpecializedCategory ?obj ?mor |- _ ] => progress (change_in_all obj with (@Object obj mor C); sanitize_spcategory)
         end;
  sanitize_spcategory.


Hint Rewrite LeftIdentity RightIdentity.
Hint Resolve LeftIdentity RightIdentity.
Hint Immediate Associativity.

Definition LocallySmallSpecializedCategory (obj : Type) (mor : obj -> obj -> Set) := SpecializedCategory mor.
Definition SmallSpecializedCategory (obj : Set) (mor : obj -> obj -> Set) := SpecializedCategory mor.
Identity Coercion LocallySmallSpecializedCategory_SpecializedCategory_Id : LocallySmallSpecializedCategory >-> SpecializedCategory.
Identity Coercion SmallSpecializedCategory_LocallySmallSpecializedCategory_Id : SmallSpecializedCategory >-> SpecializedCategory.

Section Categories_Equal.
  Lemma SpecializedCategories_Equal obj mor : forall (C D : @SpecializedCategory obj mor),
    @Identity' _ _ C = @Identity' _ _ D
    -> @Compose' _ _ C = @Compose' _ _ D
    -> C = D.
    destruct C, D; repeat rewrite unfold_Object, unfold_Morphism in *; simpl in *; intros; firstorder; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.
End Categories_Equal.

Ltac spcat_eq_step_with tac := structures_eq_step_with SpecializedCategories_Equal tac.

Ltac spcat_eq_with tac := present_spcategory; repeat spcat_eq_step_with tac.

Ltac spcat_eq_step := spcat_eq_step_with idtac.
Ltac spcat_eq := spcat_eq_with idtac.

Ltac solve_for_identity :=
  match goal with
    | [ |- @Compose _ _ ?C ?s ?s ?d ?a ?b = ?b ]
      => cut (a = @Identity C s);
        [ try solve [ let H := fresh in intro H; rewrite H; apply LeftIdentity ] | ]
    | [ |- @Compose _ _ ?C ?s ?d ?d ?a ?b = ?a ]
      => cut (b = @Identity C d );
        [ try solve [ let H := fresh in intro H; rewrite H; apply RightIdentity ] | ]
  end.

(** * Version of [Associativity] that avoids going off into the weeds in the presence of unification variables *)

Definition NoEvar T (_ : T) := True.

Lemma AssociativityNoEvar obj mor (C : @SpecializedCategory obj mor) : forall (o1 o2 o3 o4 : C) (m1 : C.(Morphism) o1 o2)
  (m2 : C.(Morphism) o2 o3) (m3 : C.(Morphism) o3 o4),
  NoEvar (m1, m2) \/ NoEvar (m2, m3) \/ NoEvar (m1, m3)
  -> Compose (Compose m3 m2) m1 = Compose m3 (Compose m2 m1).
  intros; apply Associativity.
Qed.

Ltac noEvar := match goal with
                 | [ |- context[NoEvar ?X] ] => (has_evar X; fail 1) ||
                   cut (NoEvar X); [ intro; tauto | constructor ]
               end.

Hint Rewrite AssociativityNoEvar using noEvar.

Ltac try_associativity_quick tac := try_rewrite Associativity tac.
Ltac try_associativity tac := try_rewrite_by AssociativityNoEvar ltac:(idtac; noEvar) tac.

Ltac find_composition_to_identity :=
  match goal with
    | [ H : @Compose _ _ _ _ _ _ ?a ?b = @Identity _ _ _ _ |- context[@Compose ?A ?B ?C ?D ?E ?F ?c ?d] ]
      => let H' := fresh in
        assert (H' : b = d /\ a = c) by (split; reflexivity); clear H';
          assert (H' : @Compose A B C D E F c d = @Identity _ _ _ _) by (
            exact H ||
              (unfold_Object; simpl in H |- *; exact H || (rewrite H; reflexivity))
          );
          first [
            rewrite H'
            | simpl in H' |- *; rewrite H'
            | let H'T := type of H' in fail 2 "error in rewriting a found identity" H "[" H'T "]"
          ]; clear H'
  end.

(** * Back to the main content.... *)

Section Category.
  Variable obj : Type.
  Variable mor : obj -> obj -> Type.
  Variable C : SpecializedCategory mor.

  (* Quoting Wikipedia,
    In category theory, an epimorphism (also called an epic
    morphism or, colloquially, an epi) is a morphism [f : X → Y]
    which is right-cancellative in the sense that, for all
    morphisms [g, g' : Y → Z],
    [g ○ f = g' ○ f -> g = g']

    Epimorphisms are analogues of surjective functions, but they
    are not exactly the same. The dual of an epimorphism is a
    monomorphism (i.e. an epimorphism in a category [C] is a
    monomorphism in the dual category [OppositeCategory C]).
    *)
  Definition IsEpimorphism' x y (m : mor x y) : Prop :=
    forall z (m1 m2 : mor y z), @Compose _ _ C _ _ _ m1 m = @Compose _ _ C _ _ _ m2 m ->
      m1 = m2.
  Definition IsMonomorphism' x y (m : mor x y) : Prop :=
    forall z (m1 m2 : mor z x), @Compose _ _ C _ _ _ m m1 = @Compose _ _ C _ _ _ m m2 ->
      m1 = m2.
  Definition IsEpimorphism x y (m : C.(Morphism) x y) : Prop :=
    forall z (m1 m2 : C.(Morphism) y z), Compose m1 m = Compose m2 m ->
      m1 = m2.
  Definition IsMonomorphism x y (m : C.(Morphism) x y) : Prop :=
    forall z (m1 m2 : C.(Morphism) z x), Compose m m1 = Compose m m2 ->
      m1 = m2.
End Category.

Arguments IsEpimorphism' {obj mor} [C x y] m.
Arguments IsEpimorphism {obj mor} [C x y] m.
Arguments IsMonomorphism' {obj mor} [C x y] m.
Arguments IsMonomorphism {obj mor} [C x y] m.

Section AssociativityComposition.
  Variable obj : Type.
  Variable mor : obj -> obj -> Type.
  Variable C : SpecializedCategory mor.
  Variables o0 o1 o2 o3 o4 : C.

  Lemma compose4associativity_helper
    (a : Morphism _ o3 o4) (b : Morphism _ o2 o3)
    (c : Morphism _ o1 o2) (d : Morphism _ o0 o1) :
    Compose (Compose a b) (Compose c d) = (Compose a (Compose (Compose b c) d)).
    repeat rewrite Associativity; reflexivity.
  Qed.
End AssociativityComposition.

Ltac compose4associativity' a b c d := transitivity (Compose a (Compose (Compose b c) d)); try solve [ apply compose4associativity_helper ].
Ltac compose4associativity :=
  match goal with
    | [ |- Compose (Compose ?a ?b) (Compose ?c ?d) = _ ] => compose4associativity' a b c d
    | [ |- _ = Compose (Compose ?a ?b) (Compose ?c ?d) ] => compose4associativity' a b c d
  end.
