import basic_topology.Munkres.Ch12_TopologicalSpaces

variable {X: Type u}

structure isBasis (ℬ: Family X) where
  basis₁: ∀ x, ∃ B ∈ ℬ, x ∈ B
  basis₂: ∀ x, ∀ B₁ ∈ ℬ, ∀ B₂ ∈ ℬ, x ∈ B₁ ∩ B₂ → ∃ B₃ ∈ ℬ, B₃ ⊆ B₁ ∩ B₂

structure Basis (X: Type u) where
  basis: Family X
  isBasis: isBasis basis

instance: Membership (Set X) (Basis X) := {
  mem := fun ℬ B => B ∈ ℬ.basis
}

def Basis.generate (ℬ: Basis X): Topology X := {
  Open := {U | ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ U}
  isTopology := {
    union := sorry
    inter := sorry
  }
}

def Basis.singletons (X: Type u): Basis X := {
  basis := Set.range (fun x => {x})
  isBasis := {
    basis₁ := sorry
    basis₂ := sorry
  }
}

-- TODO: how to show two topologies are equal in this setup...?
theorem Basis.discrete (X: Type u): (Basis.singletons X).generate.Open = (DiscreteTopology X).Open := by
  ext U
  constructor
  sorry
  sorry
