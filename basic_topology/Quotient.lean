import basic_topology.Topology

set_option linter.style.commandStart false

variable {X Y: Type*} {T: Family X}

-- Show that the quotient by an equivalence relation is a topology.

example {X: Type u} (r: X → X → Prop) (hr: Equivalence r): Type u :=
  Quotient ⟨r, hr⟩

-- Lift a family to the quotient.
def quotient_family (T: Family X) (r: X → X → Prop) (hr: Equivalence r): Family (Quotient ⟨r, hr⟩) :=
  {A | A ∘ Quotient.mk ⟨r, hr⟩ ∈ T}

theorem quotient_is_topology (hT: IsTopology T) {r: X → X → Prop} (hr: Equivalence r): IsTopology T := {
  sUnion := by
    intro 𝒰 h𝒰
    sorry
  finite_sInter := by
    intro 𝒰 h𝒰₁ h𝒰₂
    sorry
}

-- Given a space X and two points x₀ x₁ glues them together.
def glue_two_relation (x₀ x₁: X): X → X → Prop :=
  fun x y => (x = y) ∨ (x = x₀ ∧ y = x₁) ∨ (x = x₁ ∧ y = x₀)

theorem glue_two_equivalence (x₀ x₁: X): Equivalence (glue_two_relation x₀ x₁) := {
  refl := by simp [glue_two_relation]
  symm := by
    intro x y h
    by_cases hxy: x = y <;> by_cases x = x₀ <;> by_cases x = x₁
    repeat simp_all [glue_two_relation]
  trans := by
    intro x y z h1 h2
    simp_all [glue_two_relation]
    match h1 with
    | Or.inl h1 => repeat simp_all
    | Or.inr h1 => match h2 with
      | Or.inl h2 => repeat simp_all
      | Or.inr h2 => match h1 with
        | Or.inl h1 => match h2 with
          | Or.inl h2 => repeat simp_all
          | Or.inr h2 => repeat simp_all
        | Or.inr h1 => match h2 with
          | Or.inl h2 => repeat simp_all
          | Or.inr h2 => repeat simp_all
}
