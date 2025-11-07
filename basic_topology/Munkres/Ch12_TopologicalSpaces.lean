/-

Chapter 12 covers:
- Definition of a top. space
- Example 2: Discrete and indiscrete topology
- Example 3: Finite complement topology
- Finer/coarser

-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice

abbrev Family (X: Type u): Type u :=
  Set (Set X)

structure isTopology {X: Type u} (𝒯: Family X): Prop where
  union: ∀ U ⊆ 𝒯, ⋃₀ U ∈ 𝒯
  inter: ∀ U ⊆ 𝒯, Finite U → ⋂₀ U ∈ 𝒯

class Topology (X: Type u) where
  Open: Family X
  isTopology: isTopology Open

export Topology (Open)

structure TopologicalSpace where
  points: Type u
  topology: Topology points

variable {X: Type u}

theorem open_empty {𝒯: Topology X}: Open (∅: Set X) := by
  rw [←Set.sUnion_empty]
  apply 𝒯.isTopology.union
  apply Set.empty_subset

theorem open_univ {𝒯: Topology X}: Open (Set.univ: Set X) := by
  rw [←Set.sInter_empty]
  apply 𝒯.isTopology.inter
  · apply Set.empty_subset
  · exact Finite.of_subsingleton

def DiscreteTopology (X: Type u): Topology X := {
  Open := Set.univ
  isTopology := {
    union := by intros; trivial
    inter := by intros; trivial
  }
}

def IndiscreteTopology (X: Type u): Topology X := {
  Open := {∅, Set.univ}
  isTopology := {
    union := by
      intro U hU
      exact Set.sUnion_mem_empty_univ hU
    inter := by
      intro U hU₁ _
      by_cases hU₂: ∅ ∈ U
      · left
        exact Set.subset_eq_empty (fun _ h ↦ h _ hU₂) rfl
      · right
        sorry
  }
}

-- T ≤ T' says T' is finer than T,
-- equivalently T is coarser than T'.
instance (X: Type u): LE (Topology X) := {
  le := fun 𝒯 𝒯' => 𝒯.Open ⊆ 𝒯'.Open
}

instance (X: Type u): LT (Topology X) := {
  lt := fun 𝒯 𝒯' => 𝒯.Open ⊂ 𝒯'.Open
}
