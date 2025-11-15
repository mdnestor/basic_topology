import basic_topology.Munkres.Ch12_TopologicalSpaces

variable {X: Type u}

structure isBasis (ℬ: Family X): Prop where
  basis₁: ∀ x, ∃ B ∈ ℬ, x ∈ B
  basis₂: ∀ x, ∀ B₁ ∈ ℬ, ∀ B₂ ∈ ℬ, x ∈ B₁ ∩ B₂ → ∃ B₃ ∈ ℬ, B₃ ⊆ B₁ ∩ B₂

def Basis.generate (ℬ: Family X): Family X :=
  {U | ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ U}

def Basis.singleton (X: Type u): Family X :=
  Set.range fun x => {x}

def isBasis.singleton (X: Type u): isBasis (Basis.singleton X) := {
  basis₁ := sorry
  basis₂ := sorry
}

-- TODO: Example 1, Example 2.

-- Example 3
theorem Basis.discrete (X: Type u): Basis.generate (Basis.singleton X)= Set.univ := by
  ext U
  constructor
  · intro; trivial
  · intro _ x hx
    exists {x}
    repeat' constructor
    exact Set.singleton_subset_iff.mpr hx

theorem Basis.generate_isTopology {ℬ: Family X} (h: isBasis ℬ): isTopology (Basis.generate ℬ) := {
  union := sorry
  inter := sorry
}

-- TODO: Lemma 13.1, 13.2, 13.3

-- The basis of open interals is defined here, but we may reserve that for next chapter.

-- TODO: Definition of a subbasis.
