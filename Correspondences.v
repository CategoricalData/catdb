Require Import ProofIrrelevance FunctionalExtensionality.
Require Export SpecializedCategory Functor SetCategory ProductCategory Duals BoolCategory.
Require Import Common Notations Subcategory.

Set Implicit Arguments.

Generalizable All Variables.

(** Quoting Jacob Lurie in "Higher Topos Theory", section 2.3.1:
   Let [C] and [C'] be categories. A correspondence from [C] to [C']
   is a functor
   [[M: C^{op} × C' → Set.]]
   If [M] is a correspondence from [C] to [C'], we can define a new
   category [C ★^{M} C'] as follows. An object of [C ★^{M} C'] is
   either an object of [C] or an object of [C']. For morphisms, we
   take
   [[
                             Hom_{C}  (X, Y)   if X, Y ∈ C
   Hom_{C ★^{M} C'} (X, Y) = Hom_{C'} (X, Y)   if X, Y ∈ C'
                             M (X, Y)          if X ∈ C, Y ∈ C'
                             ∅                 if X ∈ C', Y ∈ C
   ]]
   Composition of morphisms is defined in the obvious way, using the
   composition laws in [C] and [C'], and the functoriality of
   [M (X, Y)] in [X] and [Y].

   - Remark:
   In the special case where [F : C^{op} × C' → Set] is the constant
   functor taking the value [*], the category [C ★^{F} C'] coincides
   with the ordinary join [C ★ C'].

   For any correspondence [M : C → C'], there is an obvious functor
   [F : C ★^{M} C' → [1] ] (here [1] denotes the linearly ordered set
   {0, 1}, regarded as a category in the obvious way), uniquely
   determined by the condition that [F⁻¹ {0} = C] and [F⁻¹ {1} = C'].
   Conversely, given any category [M] equipped with a functor
   [F : M → [1] ], we can define [C = F⁻¹ {0}], [C' = F⁻¹ {1}], and a
   correspondence [M : C → C'] by the formula
   [M (X, Y) = Hom_{M} (X, Y)]. We may summarize the situation as
   follows:

   Fact:
   Giving a pair of categories [C], [C'] and a correspondence between
   them is equivalent to giving a category [M] equipped with a functor
   [M → [1] ].

   Given this reformulation, it is clear how to generalize the notion
   of a correspondence to the ∞-categorical setting.

   Definition:
   Let [C] and [C'] be ∞-categories. A correspondence from [C] to [C']
   is a ∞-category [M] equipped with a map [F : M → ∆¹] and
   identifications [C ≃ F⁻¹ {0}], [C' ≃ F⁻¹ {1}].

   Remark:
   Let [C] and [C'] be ∞-categories. The fact above generalizes to the
   ∞-categorical setting in the following way: there is a canonical
   bijection between equivalence classes of correspondences from [C]
   to [C'] and equivalence classes of functors [C^{op} × C' → S],
   where [S] denotes the ∞-category of spaces.
   In fact, it is possible to prove a more precise result (a Quillen
   equivalence between certain model categories), but we will not need
   this.
   *)
Section CorrespondenceCategory.
  (*
     Let [C] and [C'] be categories. A correspondence from [C] to [C']
     is a functor
     [[M: C^{op} × C' → Set.]]
     *)
  Context `(C : @SpecializedCategory objC).
  Context `(C' : @SpecializedCategory objC').

  Let COp := OppositeCategory C.

  Variable M : SpecializedFunctor (COp * C') TypeCat. (* the correspondence *)

  (*
     If [M] is a correspondence from [C] to [C'], we can define a new
     category [C ★^{M} C'] as follows. An object of [C ★^{M} C'] is
     either an object of [C] or an object of [C']. For morphisms, we
     take
     [[
                               Hom_{C}  (X, Y)   if X, Y ∈ C
     Hom_{C ★^{M} C'} (X, Y) = Hom_{C'} (X, Y)   if X, Y ∈ C'
                               M (X, Y)          if X ∈ C, Y ∈ C'
                               ∅                 if X ∈ C', Y ∈ C
     ]]
     *)
  Definition CorrespondenceCategory_Morphism (s d : (C + C')%type) : Type :=
    match (s, d) with
      | (inl X, inl Y) => Morphism C X Y
      | (inr X, inr Y) => Morphism C' X Y
      | (inl X, inr Y) => M (X, Y)
      | (inr X, inl Y) => Empty_set
    end.

  Definition CorrespondenceCategory_Identity x : CorrespondenceCategory_Morphism x x :=
    match x as s return (CorrespondenceCategory_Morphism s s) with
      | inl X => Identity X
      | inr X => Identity X
    end.

  Definition CorrespondenceCategory_Compose s d d' (m1 : CorrespondenceCategory_Morphism d d') (m2 : CorrespondenceCategory_Morphism s d) :
    CorrespondenceCategory_Morphism s d'.
    destruct s as [ X | X ], d as [ Y | Y ], d' as [ Z | Z ];
      unfold CorrespondenceCategory_Morphism in *; simpl in *; trivial;
        try exact (Compose m1 m2);
          destruct_type @Empty_set.
    exact (M.(MorphismOf) (s := (Y, _)) (d := (X, _)) (m2, Identity Z) m1).
    exact (M.(MorphismOf) (s := (_, Y)) (d := (_, Z)) (Identity X, m1) m2).
  Defined.

  Hint Resolve Associativity LeftIdentity RightIdentity.

  (* TODO: Figure out how to get Coq to do automatic type inference
     here, and simplify this proof *)
  Definition CorrespondenceCategory : @SpecializedCategory (C + C')%type.
    refine {|
      Morphism' := CorrespondenceCategory_Morphism;
      Identity' := CorrespondenceCategory_Identity;
      Compose' := CorrespondenceCategory_Compose
    |};
    abstract (
      intros; destruct_type @sum;
        unfold CorrespondenceCategory_Identity, CorrespondenceCategory_Compose, CorrespondenceCategory_Morphism in *;
          destruct_type @Empty_set; trivial; t_with t';
            try match goal with
                  | [ |- appcontext[(Compose (C := ?A) ?a ?b, Identity (C := ?B) ?c)] ] =>
                    replace (Compose a b, Identity c) with
                      (Compose (C := A * B) (s := (_, c)) (d := (_, c)) (d' := (_, c)) (a, Identity c) (b, Identity c));
                      [
                        let H := fresh in
                          pose proof (FCompositionOf' M (_, c) (_, c) (_, c) (a, Identity c) (b, Identity c)) as H; present_spfunctor;
                            conv_rewrite H
                        | simpl; repeat rewrite LeftIdentity; try reflexivity
                      ]
                  | [ |- appcontext[(Identity (C := ?B) ?c, Compose (C := ?A) ?a ?b)] ] =>
                    replace (Identity c, Compose a b) with
                      (Compose (C := B * A) (s := (c, _)) (d := (c, _)) (d' := (c, _)) (Identity c, a) (Identity c, b));
                      [
                        let H := fresh in
                          pose proof (FCompositionOf' M (c, _) (c, _) (c, _) (Identity c, b) (Identity c, a)) as H;
                            conv_rewrite H
                        | simpl; repeat rewrite LeftIdentity; try reflexivity
                      ]
                  | [ |- ?f (?g ?x) = ?f' (?g' ?x') ] => change (Compose f g x = Compose f' g' x');
                    repeat rewrite <- FCompositionOf; simpl; present_spcategory;
                      repeat rewrite LeftIdentity; repeat rewrite RightIdentity
                end;
            repeat rewrite FIdentityOf;
              repeat rewrite FCompositionOf;
                try solve [ simpl; trivial ]
    ).
  Defined.
End CorrespondenceCategory.

Notation "C ★^ M D" := (CorrespondenceCategory (C := C) (C' := D) M) : category_scope.
(* XXX: [Reserved Notation] doesn't work here? *)
Notation "C ★^{ M } D" := (CorrespondenceCategory (C := C) (C' := D) M) (at level 70, no associativity) : category_scope.

(* We use {false, true} instead of {0, 1}, because it's more convenient, and slightly faster *)
Local Notation "[ 1 ]" := BoolCat : category_scope.

Section Functor_to_1.
  (*
     For any correspondence [M : C → C'], there is an obvious functor
     [F : C ★^{M} C' → [1] ] (here [1] denotes the linearly ordered set
     {0, 1}, regarded as a category in the obvious way), uniquely
     determined by the condition that [F⁻¹ {0} = C] and [F⁻¹ {1} = C'].
     *)
  Context `(dummy : @CorrespondenceCategory objC C objC' C' M).

  Let CorrespondenceCategoryFunctor_ObjectOf (x : C + C') : Object [1] := if x then false else true. (*
    match x with
      | inl _ => exist _ 0 (le_S 0 0 (le_n 0))
      | inr _ => exist _ 1 (le_n 1)
    end. *)
  Definition CorrespondenceCategoryFunctor_MorphismOf (s d : C + C') (m : CorrespondenceCategory_Morphism M s d) :
    Morphism [1] (CorrespondenceCategoryFunctor_ObjectOf s) (CorrespondenceCategoryFunctor_ObjectOf d).
    subst_body; abstract (
      destruct s, d; hnf in *; simpl in *; intuition
    ).
  Defined.

  Definition CorrespondenceCategoryFunctor : SpecializedFunctor (C ★^{M} C') [1].
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          CorrespondenceCategoryFunctor_ObjectOf
          CorrespondenceCategoryFunctor_MorphismOf
          _
          _
        )
    end;
    unfold CorrespondenceCategoryFunctor_MorphismOf; subst_body;
      abstract (
        repeat (let H := fresh in intro H; destruct H; simpl in *);
          unfold Morphism; simpl;
            intros; trivial;
              apply proof_irrelevance
      ).
  Defined.
End Functor_to_1.

Section From_Functor_to_1.
  (* Conversely, given any category [M] equipped with a functor
     [F : M → [1] ], we can define [C = F⁻¹ {0}], [C' = F⁻¹ {1}], and a
     correspondence [M : C → C'] by the formula
     [M (X, Y) = Hom_{M} (X, Y)]. *)
  Context `(M : @SpecializedCategory objM).
  Variable F : SpecializedFunctor M [1].

  (* Comments after these two are for if we want to use [NatCategory] instead of [BoolCat]. *)
  Definition CorrespondenceCategory0 := FullSubcategory M (fun x => F x = false). (* proj1_sig (F x) = 0).*)
  Definition CorrespondenceCategory1 := FullSubcategory M (fun x => F x = true). (* proj1_sig (F x) = 1).*)

  Let C := CorrespondenceCategory0.
  Let C' := CorrespondenceCategory1.
  Let COp := OppositeCategory C.

  Definition Correspondence : SpecializedFunctor (COp * C') TypeCat.
    subst_body.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (fun cc' => Morphism M (proj1_sig (fst cc')) (proj1_sig (snd cc')))
          (fun s d m => fun m0 => Compose (C := M) (snd m) (Compose m0 (fst m)))
          _
          _
        )
    end;
    simpl in *; present_spfunctor; subst_body;
      abstract (
        intros; destruct_hypotheses;
          apply functional_extensionality_dep; intro;
            repeat rewrite Associativity;
              repeat rewrite LeftIdentity;
                repeat rewrite RightIdentity;
                  reflexivity
      ).
  Defined.
End From_Functor_to_1.
