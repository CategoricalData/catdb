Require Import Setoid.
Require Import Common EquivalenceRelation Category Functor.

Section Categories_NaturalTransformation.
  Variable C D : Category.
  Variable F G : Functor C D.

  (**
     Quoting from the lecture notes for 18.705, Commutative Algebra:

     A map of functors is known as a natural transformation. Namely, given two functors
     [F : C -> D], [G : C -> D], a natural transformation [T: F -> G] is a collection of maps
     [T A : F A -> G A], one for each object [A] of [C], such that [(T B) ○ (F m) = (G m) ○ (T A)]
     for every map [m : A -> B] of [C]; that is, the following diagram is commutative:

           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    G m     V
     G A --------> G B
     **)
  Record NaturalTransformation := {
    ComponentsOf :> forall c : C.(Object), Morphism _ (F c) (G c);
    Commutes : forall s d (m : Morphism C s d),
      MorphismsEquivalent _ _ _
      (Compose (ComponentsOf d) (F.(MorphismOf) m))
      (Compose (G.(MorphismOf) m) (ComponentsOf s))
  }.
End Categories_NaturalTransformation.

Implicit Arguments NaturalTransformation [C D].
Implicit Arguments ComponentsOf [C D F G].
Implicit Arguments Commutes [C D F G].

Section NaturalTransformationComposition.
  Variable C D E : Category.
  Variable F F' F'' : Functor C D.
  Variable G G' : Functor D E.

  Hint Resolve Commutes.

  (*
     We have the diagram
          F
     C -------> D
          |
          |
          | T
          |
          V
     C -------> D
          F'
          |
          | T'
          |
          V
     C ------> D
          F''

     And we want the commutative diagram
           F m
     F A -------> F B
      |            |
      |            |
      | T A        | T B
      |            |
      V    F' m    V
     F' A -------> F' B
      |            |
      |            |
      | T' A       | T' B
      |            |
      V    F'' m   V
     F'' A ------> F'' B

  *)
  Definition NTComposeT (T : NaturalTransformation F F') (T' : NaturalTransformation F' F'') :
    NaturalTransformation F F''.
    refine {| ComponentsOf := (fun c => Compose (T'.(ComponentsOf) c) (T.(ComponentsOf) c))
      |}.
    (* XXX TODO: Find a way to get rid of [m] in the transitivity call *)
    abstract (t; transitivity (Compose (T' _) (Compose (MorphismOf F' m) (T _))); t).
  Defined.

  (*
     We have the diagram
          F          G
     C -------> D -------> E
          |          |
          |          |
          | T        | U
          |          |
          V          V
     C -------> D -------> E
          F'         G'

     And we want the commutative diagram
             G (F m)
     G (F A) -------> G (F B)
        |                |
        |                |
        | U (T A)        | U (T B)
        |                |
        V     G' (F' m)  V
     G' (F' A) -----> G' (F' B)

  *)
  (* Coq is silly about types *)
  Definition nt_compose_f_components_of (T : NaturalTransformation F F') (U : NaturalTransformation G G') c : Morphism _ ((ComposeFunctor F G) c) ((ComposeFunctor F' G') c) :=
    (Compose (G'.(MorphismOf) (T.(ComponentsOf) c)) (U.(ComponentsOf) (F c))).
  (* XXX TODO: Automate this better *)
  Definition NTComposeF (T : NaturalTransformation F F') (U : NaturalTransformation G G') :
    NaturalTransformation (ComposeFunctor F G) (ComposeFunctor F' G').
    refine {| ComponentsOf := (nt_compose_f_components_of T U)
      |}; unfold nt_compose_f_components_of.
    t.
    repeat (rewrite <- U.(Commutes)).
    repeat (rewrite Associativity).
    repeat (rewrite <- FCompositionOf).
    transitivity (Compose (U (F' d)) (G.(MorphismOf) (Compose (F'.(MorphismOf) m) (T s)))).
  Admitted.
  (* Broke this stuff with changes to [Category]; will revisit.
    apply PreComposeMorphisms.
    apply FEquivalenceOf. apply Commutes.

    repeat (rewrite FCompositionOf).
    repeat (rewrite <- Associativity).
    apply PostComposeMorphisms.
    apply Commutes.
  Defined.*)
End NaturalTransformationComposition.

Implicit Arguments NTComposeT [C D F F' F''].
Implicit Arguments NTComposeF [C D E F F' G G'].

Section IdentityNaturalTransformation.
  Variable C D : Category.
  Variable F : Functor C D.

  (* There is an identity natrual transformation. *)
  Definition IdentityNaturalTransformation : NaturalTransformation F F.
    refine {| ComponentsOf := (fun c => Identity (F c))
      |};
    abstract t.
  Defined.
End IdentityNaturalTransformation.

Implicit Arguments IdentityNaturalTransformation [C D].
