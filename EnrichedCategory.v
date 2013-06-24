Require Export Category MonoidalCategory.
Require Import Common Notations DefinitionSimplification.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section EnrichedCategory.
  (** Quoting Wikipedia:
     Let [(M, ⊗, I, α, λ, ρ)] be a monoidal category.
     *)
  Context `(M : MonoidalCategory).

  Let src `{C : Category} s d (_ : Morphism C s d) := s.
  Let dst `{C : Category} s d (_ : Morphism C s d) := d.

  Arguments src [C s d] _.
  Arguments dst [C s d] _.

  Local Notation "A ⊗ B" := (M.(TensorProduct) (A, B)).
  Local Notation "A ⊗m B" := (M.(TensorProduct).(MorphismOf) (s := (src A, src B)) (d := (dst A, dst B)) (A, B)%morphism).
  Let I : M := M.(IdentityObject).
  Let α := M.(Associator).
  Let λ := M.(LeftUnitor).
  Let ρ := M.(RightUnitor).

  (**
     Then an enriched category [C] (alternatively, in situations where
     the choice of monoidal category needs to be explicit, a category
     enriched over [M], or [M]-category), consists of
     * a class [ob C] of objects of C,
     * an object [C(a, b)] of [M] for every pair of objects [(a, b)]
         in [C],
     * an arrow [id a : I -> C(a, a)] in [M] designating an identity
         for every object [a] in [C], and
     * an arrow [○ a b c : C(b, c) ⊗ C(a, b) -> C(a, c)] in [M]
         designating a composition for each triple of objects
         [(a, b, c)] in [C],
     such that the following three diagrams commute:
     [[
                                        ○_{b, c, d} ⊗ 1
       (C(c, d) ⊗ C(b, c)) ⊗ C(a, b) ---------------------> C(b, d) ⊗ C(a, b)
                     |                                              |
                     |                                              |
                     |                                              | ○_{a, b, d}
                     |                                              |
                     |                                              ↓
                     | α                                         C(a, d)
                     |                                              ↑
                     |                                              |
                     |                                              | ○_{a, c, d}
                     |                                              |
                     ↓                                              |
       C(c, d) ⊗ (C(b, c) ⊗ C(a, b)) ---------------------> C(b, d) ⊗ C(a, b)
                                        1 ⊗ ○_{a, b, c}
     ]]
     The first diagram expresses the associativity of composition.

     Should it be the case that [M] is a category of sets and
     functions and [(⊗, I, α, λ, ρ)] is the usual monoidal structure
     (cartesian product, single-point set, etc.), each [C(a,b)] would
     then be a set whose elements are best thought of as ``individual
     morphisms'' of [C] while [○], now a function, defines how
     consecutive such morphisms compose.  In this case, each path
     leading to [C(a,d)] in the first diagram corresponds to one of
     the two ways of composing three consecutive individual morphisms
     from [a → b → c → d] from [C(a,b)], [C(b,c)], and [C(c,d)].
     Commutativity of the diagram is then merely the statement that
     both orders of composition give the same result, exactly
     as required for ordinary categories.

     What is new here is that we have expressed this requirement
     without any explicit reference to individual morphisms in
     [C] --- again, these diagrams are of morphisms in [M], not
     [C] --- thus making the concept of associativity of composition
     meaningful in the more general case where the hom-objects
     [C(a,b)] are abstract and [C] itself need not even have any
     notion of individual morphism.

     Similarly, the second and third diagrams express the
     corresponding identity rules:
     [[
                      id b ⊗ 1
       I ⊗ C(a, b) --------------> C(b, b) ⊗ C(a, b)
           \                               /
             \                           /
               \                       /
               λ \                   / ○_{a, b, b}
                   \               /
                     \           /
                       \       /
                         ↘   ↙
                        C(a, b)
     ]]
     [[
                      1 ⊗ id a
       C(a, b) ⊗ I --------------> C(a, b) ⊗ C(a, a)
           \                               /
             \                           /
               \                       /
               ρ \                   / ○_{a, a, b}
                   \               /
                     \           /
                       \       /
                         ↘   ↙
                        C(a, b)
     ]]
     If we again restrict ourselves to the case where [M] is a
     monoidal category of sets and functions, the morphisms
     [id a : I -> C(a, a)] become functions from the one-point set [I]
     and must then, for any given object [a], identify a particular
     element of each set [C(a, a)], something we can then think of as
     the ``identity morphism for [a] in [C]''.  Commutativity of the
     latter two diagrams is then the statement that compositions (as
     defined by the functions [○]) involving these distinguished
     individual ``identity morphisms in [C]'' behave exactly as per
     the identity rules for ordinary categories.

     One should be careful to distinguish the different notions of
     ``identity'' being referenced here, e.g.,
     * the monoidal identity [I] is an object of [M], being an
         identity for [⊗] only in the monoid-theoretic sense, and
         even then only up to canonical isomorphism [(λ, ρ)].
     * the identity morphisms [1_{C(a, b)} : C(a, b) -> C(a, b)]
         which are actual morphisms that [M] has for each of its
         objects by virtue of it being (at least) an ordinary
         category.
     from the morphisms [id a : I -> C(a, a)] that define the notion
     of identity for objects in the enriched category [C], whether or
     not [C] can be considered to have individual morphisms of its own.
     *)

  Local Reserved Notation "'C' ( a , b )".
  Local Reserved Notation "'id'".
  Local Reserved Notation "○_{ a , b , c }".

  Local Notation "x ~> y" := (M.(Morphism) x y).

  Record EnrichedCategory := {
    EnrichedObject :> Type;

    EnrichedMorphism : EnrichedObject -> EnrichedObject -> M where "'C' ( A , B )" := (@EnrichedMorphism A B);
    EnrichedIdentity : forall a, I ~> C (a, a) where "'id'" := EnrichedIdentity;
    EnrichedCompose : forall a b c, C(b, c) ⊗ C(a, b) ~> C(a, c) where "○_{ a , b , c }" := (@EnrichedCompose a b c);

  (*
     [[
                                        ○_{b, c, d} ⊗ 1
       (C(c, d) ⊗ C(b, c)) ⊗ C(a, b) ---------------------> C(b, d) ⊗ C(a, b)
                     |                                              |
                     |                                              |
                     |                                              | ○_{a, b, d}
                     |                                              |
                     |                                              ↓
                     | α                                         C(a, d)
                     |                                              ↑
                     |                                              |
                     |                                              | ○_{a, c, d}
                     |                                              |
                     ↓                                              |
       C(c, d) ⊗ (C(b, c) ⊗ C(a, b)) ---------------------> C(b, d) ⊗ C(a, b)
                                        1 ⊗ ○_{a, b, c}
     ]]
     *)
    EnrichedAssociativity : forall a b c d, (
      (Compose ○_{a, b, d} (○_{b, c, d} ⊗m @Identity M C(a, b))) =
      (Compose ○_{a, c, d}
        (Compose ((@Identity M C(c, d)) ⊗m ○_{a, b, c})
          (α (C(c, d), C(b, c), C(a, b)))
        )
      )
    );
    (*
       [[
                      id b ⊗ 1
       I ⊗ C(a, b) --------------> C(b, b) ⊗ C(a, b)
           \                               /
             \                           /
               \                       /
               λ \                   / ○_{a, b, b}
                   \               /
                     \           /
                       \       /
                         ↘   ↙
                        C(a, b)
     ]]
     *)
    EnrichedLeftIdentity : forall a b, (
      Compose ○_{a, b, b} ((id b) ⊗m (@Identity M C(a, b))) =
      λ C(a, b)
    );
    (*
     [[
                      1 ⊗ id a
       C(a, b) ⊗ I --------------> C(a, b) ⊗ C(a, a)
           \                               /
             \                           /
               \                       /
               ρ \                   / ○_{a, a, b}
                   \               /
                     \           /
                       \       /
                         ↘   ↙
                        C(a, b)
     ]]
     *)
    EnrichedRightIdentity : forall a b, (
      Compose ○_{a, a, b} ((@Identity M C(a, b)) ⊗m (id a)) =
      ρ C(a, b)
    )
  }.
End EnrichedCategory.
(*
Section nCategories.
  Check @EnrichedCategory.
  Require Import DiscreteCategory.
  Definition TerminalMonoidalCategory : @MonoidalCategory unit (fun _ _ => unit).
    Hint Extern 1 => repeat esplit; unfold Morphism, Object; intros; simpl; trivial.
    refine {| MonoidalUnderlyingCategory := TerminalCategory |};
      eauto.
    Grab Existential Variables.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    Grab Existential Variables.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    Grab Existential Variables.
    eauto.
    eauto.
    eauto.
  Defined.
  Require Import ComputableCategory.
  Print ComputableCategory.
  Section m2Cat.
    Definition m2Cat := @ComputableCategory unit _ _ (fun _ => TerminalCategory).

    Local Ltac ex_unit_fun := first [
      exists tt
      | exists (fun _ : unit => tt)
      | exists (fun _ : unit * unit => tt)
      | exists (fun _ : unit * unit * unit => tt)
      | exists (fun _ => tt)
      | exists (IdentityFunctor TerminalCategory)
      | exists (fun _ : unit => IdentityFunctor TerminalCategory)
      | exists (fun _ : unit * unit => IdentityFunctor TerminalCategory)
      | exists (fun _ : unit * unit * unit => IdentityFunctor TerminalCategory)
      | exists (fun _ => IdentityFunctor TerminalCategory)
    ].
    Local Ltac define_unit_nt := try unfold TriMonoidalProductL, TriMonoidalProductR;
      simpl;
        subst_body;
        repeat (unfold Morphism, Object; simpl);
          ex_unit_fun;
          abstract (
            repeat (
              repeat (unfold Morphism, Object; simpl);
                intros;
                  trivial;
                    functor_eq
            )
          ).

    Let TensorProduct : Functor (m2Cat * m2Cat) m2Cat.
      eexists (fun _ => tt) (fun _ _ _ => _);
        repeat (unfold Morphism, Object; simpl);
          simpl; intros;
            try reflexivity;
              abstract functor_eq.
    Defined.

    Let Associator' : NaturalTransformation (TriMonoidalProductL TensorProduct) (TriMonoidalProductR TensorProduct).
      define_unit_nt.
    Defined.

    Let Associator : NaturalIsomorphism (TriMonoidalProductL TensorProduct) (TriMonoidalProductR TensorProduct).
      exists Associator'.
      define_unit_nt.
    Defined.

    Let LeftUnitor' : NaturalTransformation (LeftUnitorFunctor TensorProduct tt) (IdentityFunctor _).
      define_unit_nt.
    Defined.

    Let RightUnitor' : NaturalTransformation (RightUnitorFunctor TensorProduct tt) (IdentityFunctor _).
      define_unit_nt.
    Defined.

    Let LeftUnitor : NaturalIsomorphism (LeftUnitorFunctor TensorProduct tt) (IdentityFunctor _).
      exists LeftUnitor'.
      define_unit_nt.
    Defined.

    Let RightUnitor : NaturalIsomorphism (RightUnitorFunctor TensorProduct tt) (IdentityFunctor _).
      exists RightUnitor'.
      define_unit_nt.
    Defined.

    Definition m2MonoidalCat : @MonoidalCategory unit (fun _ _ => Functor TerminalCategory TerminalCategory).
      refine (@Build_MonoidalCategory _ _
        m2Cat
        TensorProduct tt Associator LeftUnitor RightUnitor
        _ _
      );
      abstract (
        repeat (unfold Morphism, Object; simpl); intros; functor_eq
      ).
    Defined.
  End m2Cat.

  Definition m1Cat : EnrichedCategory m2MonoidalCat.
Print EnrichedCategory.
  Definition m2Category : EnrichedCategory TerminalMonoidalCategory .
End nCategories.
*)
