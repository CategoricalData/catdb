Reserved Notation "x == y" (at level 70, no associativity).
Reserved Notation "x == y == z" (at level 70, no associativity, y at next level).

Reserved Notation "x ~= y" (at level 70, no associativity).
Reserved Notation "x ~= y ~= z" (at level 70, no associativity, y at next level).

Reserved Notation "i ⁻¹" (at level 10).
Reserved Notation "C ᵒᵖ" (at level 10).

Reserved Notation "C ★^ M D" (at level 70, no associativity).
Reserved Notation "C ★^{ M } D" (at level 70, no associativity).

Reserved Notation "S ↓ T" (at level 70, no associativity).

Reserved Notation "S ⇑ T" (at level 70, no associativity).
Reserved Notation "S ⇓ T" (at level 70, no associativity).
Reserved Notation "'CAT' ⇑ D" (at level 70, no associativity).
Reserved Notation "'CAT' ⇓ D" (at level 70, no associativity).

Reserved Notation "x ⊗ y" (at level 40, left associativity).
Reserved Notation "x ⊗m y" (at level 40, left associativity).

Reserved Notation "f ○ g" (at level 70, right associativity).

Reserved Notation "x ~> y" (at level 99, right associativity, y at level 200).

Reserved Notation "x ∏ y" (at level 40, left associativity).
Reserved Notation "x ∐ y" (at level 50, left associativity).

Reserved Notation "∏_{ x } f" (at level 0, x at level 99).
Reserved Notation "∏_{ x : A } f" (at level 0, x at level 99).
Reserved Notation "∐_{ x } f" (at level 0, x at level 99).
Reserved Notation "∐_{ x : A } f" (at level 0, x at level 99).

(* I'm not terribly happy with this notation, but '('s don't work
   because they interfere with things like [prod]s and grouping,
   and '['s interfere with list notation in Program. *)
Reserved Notation "F ⟨ c , - ⟩" (at level 70, no associativity).
Reserved Notation "F ⟨ - , d ⟩" (at level 70, no associativity).

(* Forced by the notation in Program *)
Reserved Notation "[ x ]" (at level 0, x at level 200).

Reserved Notation "∫ F" (at level 0).

Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope functor_scope with functor.
Delimit Scope natural_transformation_scope with natural_transformation.

Delimit Scope graph_scope with graph.
Delimit Scope vertex_scope with vertex.
Delimit Scope edge_scope with edge.
