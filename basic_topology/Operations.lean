import basic_topology.Basis
import basic_topology.Neighborhood

variable {X Y: Type*}

-- TODO: rename boundary to boundary.

-- def Interior (𝒯: Family X) (A: Set X): Set X :=
--   ⋃₀ {U | U ∈ 𝒯 ∧ U ⊆ A}

-- theorem Interior.sup (𝒯: Family X) (A: Set X) {U: Set X} (h₁: U ∈ 𝒯) (h₂: U ⊆ A): U ⊆ Interior 𝒯 A := by
--   simp [Interior]


-- theorem Interior.open (𝒯: Family X) (h: IsTopology 𝒯) (A: Set X): Interior 𝒯 A ∈ 𝒯 := by
--   apply h.sUnion
--   apply Set.sep_subset

-- theorem Interior.monotone (𝒯: Family X) {A B: Set X} (h: A ⊆ B): Interior 𝒯 A ⊆ Interior 𝒯 B := by
--   simp [Interior]
--   intro U h1 h2
--   apply Set.subset_sUnion_of_subset _ _ (fun _ h => h)
--   apply Set.mem_sep
--   · exact h1
--   · exact le_trans h2 h

-- theorem Interior.empty (𝒯: Family X): Interior 𝒯 ∅ = ∅ := by
--   simp [Interior]

-- theorem Interior.univ {𝒯: Family X} (h: IsTopology 𝒯): Interior 𝒯 Set.univ = Set.univ := by
--   simp [Interior]
--   apply Set.eq_univ_of_univ_subset
--   intro _ _
--   exists Set.univ
--   constructor
--   · exact univ_open h
--   · simp

def interior (𝒯: Family X) (A: Set X): Set X :=
 {x | Nbhd 𝒯 x A}

-- Interior is monotone: if A ⊆ B then interior(A) ⊆ interior(B)
theorem interior_monotone (𝒯: Family X) {A B: Set X} (h: A ⊆ B): interior 𝒯 A ⊆ interior 𝒯 B := by
  simp [interior]
  intro x hx
  exact neighborhood_upward_closed x hx h

-- Interior of the empty set is empty
theorem interior_empty (𝒯: Family X): interior 𝒯 ∅ = ∅ := by
  ext x
  simp
  intro ⟨U, hU₁, hU₂, hU₃⟩
  exact hU₃ hU₂


-- Interior of the universe is itself
theorem interior_univ {𝒯: Family X} (h: IsTopology 𝒯): interior 𝒯 Set.univ = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  intro _ _
  apply neighborhood_univ h

-- Interior is a subset of the original set
theorem interior_subset_self (𝒯: Family X) (A: Set X): interior 𝒯 A ⊆ A := by
  exact fun _ => neighborhood_mem

-- Interior is idempotent: interior(interior(A)) = interior(A)
theorem interior_idempotent (𝒯: Family X) (A: Set X): interior 𝒯 (interior 𝒯 A) = interior 𝒯 A := by
  apply le_antisymm
  · apply interior_subset_self
  · intro _ hx
    simp_all [interior, Nbhd]
    obtain ⟨U, _, _, _⟩ := hx
    exists U
    repeat' constructor; simp_all
    intro _ _
    exists U

-- The interior is open
theorem interior_open {𝒯: Family X} (h: IsTopology 𝒯) (A: Set X): interior 𝒯 A ∈ 𝒯 := by
  apply (open_iff_neighborhood_of_all_points h (interior 𝒯 A)).mpr
  intro _ hx
  obtain ⟨U, hU₁, hU₂, _⟩ := hx
  exists U
  repeat' constructor
  · exact hU₁
  · exact hU₂
  · intro _ _
    exists U

-- The interior of A is largest open subset of A
theorem interior_largest_open_subset {𝒯: Family X} {A U: Set X} (h1: U ∈ 𝒯) (h2: U ⊆ A): U ⊆ interior 𝒯 A := by
  rw [interior]
  intro y hy
  apply Set.mem_setOf.mpr
  rw [Nbhd]
  use U

-- The interior of A is the union of all open subsets of A.
-- (Is this proof beautiful or ugly?)
theorem interior_eq_union_open_subsets {𝒯: Family X} {A: Set X}: interior 𝒯 A = ⋃₀ {U ∈ 𝒯 | U ⊆ A} := by
  ext
  constructor
  · intro ⟨U, _, _, _⟩
    exists U
  · intro ⟨U, ⟨_, _⟩, _⟩
    exists U

-- A set is open iff. it is its own interior
theorem open_iff_eq_interior {𝒯: Family X} (h𝒯: IsTopology 𝒯) (A: Set X): Open 𝒯 A ↔ A = interior 𝒯 A := by
  constructor
  · intro h
    apply Set.Subset.antisymm_iff.mpr
    constructor
    · apply interior_largest_open_subset h; rfl
    · apply interior_subset_self
  · intro h
    rw [h]
    apply interior_open h𝒯

theorem interior_iff_basis_element {ℬ 𝒯: Family X} (Bbase: base 𝒯 ℬ )(A: Set X)(x: X): x∈ interior 𝒯 A ↔ ∃ B∈ ℬ, x∈ B ∧ B⊆ A := by
  rw[base] at Bbase
  constructor
  · rw [interior]
    intro h_int
    simp at h_int
    rw[Nbhd] at h_int
    obtain ⟨ U,⟨hU1,hU2,hU3⟩⟩  := h_int
    apply Bbase.2 at hU1
    obtain ⟨ 𝒞, ⟨ hc1,hc2⟩⟩  := hU1
    rw[hc2] at hU2
    have: ∃ B∈ 𝒞 , x∈ B := by exact hU2
    obtain ⟨ B,⟨ hB1,hB2⟩ ⟩ := this
    use B
    constructor
    · apply hc1 at hB1
      exact hB1
    · subst hc2
      simp_all only [Set.mem_sUnion, Set.sUnion_subset_iff, and_self]
  · intro hB
    simp [interior,Nbhd]
    obtain ⟨left, right⟩ := Bbase
    obtain ⟨w, h⟩ := hB
    obtain ⟨left_1, right_1⟩ := h
    obtain ⟨left_2, right_1⟩ := right_1
    apply Exists.intro
    · apply And.intro
      apply left -- spacing..
      on_goal 2 => apply And.intro
      on_goal 2 => { exact left_2
      }
      simp_all only
      · simp_all only

-- interior (A ∩ B) = interior A ∩ interior B
theorem interior_inter_eq {𝒯: Family X} (h𝒯: IsTopology 𝒯) (A B: Set X): interior 𝒯 (A ∩ B) = interior 𝒯 A ∩ interior 𝒯 B := by
  ext
  constructor
  · intro hx
    constructor
    · exact interior_monotone 𝒯 Set.inter_subset_left hx
    · exact interior_monotone 𝒯 Set.inter_subset_right hx
  · intro ⟨hA, hB⟩
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := hA
    obtain ⟨V, hV₁, hV₂, hV₃⟩ := hB
    exists U ∩ V
    repeat' constructor
    · exact binary_inter_open h𝒯 hU₁ hV₁
    · exact hU₂
    · exact hV₂
    · exact Set.inter_subset_inter hU₃ hV₃

-- in the discrete topology, the interior of any set is itself
theorem discrete_interior (A: Set X): interior Set.univ A = A := by
  apply le_antisymm
  · apply interior_subset_self
  · intro
    apply (discrete_neighborhood_iff _ _).mpr

def adherent (𝒯: Family X) (A: Set X) (x: X): Prop :=
  ∀ N ∈ Nbhd 𝒯 x, Set.Nonempty (N ∩ A)

def closure (𝒯: Family X) (A: Set X): Set X :=
 {x | adherent 𝒯 A x}

-- Duality: closure(A) = interior(Aᶜ)ᶜ
-- Lets us prove results about closure in terms of interior
-- TODO: this proof is ugly!
theorem closure_eq (𝒯: Family X) (A: Set X): closure 𝒯 A = (interior 𝒯 Aᶜ)ᶜ := by
  ext x
  constructor
  · intro hx h
    have := hx Aᶜ h
    simp_all
  · intro hx N hN
    simp_all [interior]
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := hN
    sorry
    -- simp [Nbhd] at hx
    -- have := hx U hU₁ hU₂
    -- have: ∃ x, x ∈ U ∧ x ∉ Aᶜ := by exact Set.not_subset.mp (hx U hU₁ hU₂)
    -- obtain ⟨x, hx1, hx2⟩ := this
    -- exists x
    -- constructor
    -- · exact hU₃ hx1
    -- · exact Set.not_notMem.mp hx2

theorem closure_empty {𝒯: Family X} (h: IsTopology 𝒯): closure 𝒯 ∅ = ∅ := by
  simp [closure_eq, interior_univ h]

theorem closure_univ (𝒯: Family X): closure 𝒯 Set.univ = Set.univ := by
  simp [closure_eq, interior_empty]

theorem closure_compl_eq_compl_interior (𝒯: Family X) (A: Set X): closure 𝒯 Aᶜ = (interior 𝒯 A)ᶜ := by
  simp [closure_eq]

theorem compl_closure_eq_interior_compl (𝒯: Family X) (A: Set X): (closure 𝒯 A)ᶜ = interior 𝒯 Aᶜ := by
  simp [closure_eq]

theorem closure_monotone (𝒯: Family X) (A B: Set X){h :A⊆ B}: closure 𝒯 A ⊆ closure 𝒯 B := by
simp[closure, adherent]
intro x hx
intro U hU
apply hx at hU
have h1: U ∩ A ⊆ U ∩ B := by
  exact Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) h
exact Set.Nonempty.mono h1 hU

theorem closure_interior (𝒯: Family X) (A: Set X): closure 𝒯 (interior 𝒯 A) ⊆ closure 𝒯 A := by
  apply closure_monotone
  apply interior_subset_self

theorem closure_idempotent (𝒯: Family X) (A: Set X): closure 𝒯 (closure 𝒯 A) = closure 𝒯 A := by
  simp [closure_eq, interior_idempotent]

-- the closure is closed
theorem closure_closed {𝒯: Family X} (h𝒯: IsTopology 𝒯) (A: Set X): Closed 𝒯 (closure 𝒯 A) := by
  simp [closure_eq, Closed]
  apply interior_open h𝒯

-- closure is a superset of the original
theorem closure_supset_self (𝒯: Family X) (A: Set X): A ⊆ closure 𝒯 A := by
  simp [closure_eq]
  apply Set.subset_compl_comm.mpr
  apply interior_subset_self

-- The closure of A is smallest closed supset of A
theorem closure_smallest_closed_supset {𝒯: Family X} {A U: Set X} (h1: Uᶜ ∈ 𝒯) (h2: A ⊆ U): closure 𝒯 A ⊆ U := by
  simp [closure_eq]
  have: Uᶜ ⊆ Aᶜ := Set.compl_subset_compl_of_subset h2
  have := interior_largest_open_subset h1 this
  exact Set.compl_subset_comm.mp this

theorem closure_eq_inter_closed_supsets {𝒯: Family X} {A: Set X}: closure 𝒯 A = ⋂₀ {U | Uᶜ ∈ 𝒯 ∧ A ⊆ U} := by
  simp [closure_eq]
  apply compl_inj_iff.mp
  simp
  rw [interior_eq_union_open_subsets]
  sorry

theorem closed_iff_eq_closure {𝒯: Family X} (h𝒯: IsTopology 𝒯) (A: Set X): Closed 𝒯 A ↔ A = closure 𝒯 A := by
  simp [closure_eq, Closed]
  calc
    Aᶜ ∈ 𝒯 ↔ Aᶜ  = interior 𝒯 Aᶜ      := by apply open_iff_eq_interior h𝒯
         _ ↔ Aᶜᶜ = (interior 𝒯 Aᶜ)ᶜ   := by apply symm compl_inj_iff
         _ ↔ A   = (interior 𝒯 Aᶜ)ᶜ   := by rw [compl_compl]

-- closure (A ∪ B) = (closure A) ∪ (closure B)
theorem closure_union_eq {𝒯: Family X} (h𝒯: IsTopology 𝒯) (A B: Set X): closure 𝒯 (A ∪ B) = closure 𝒯 A ∪ closure 𝒯 B := by
  simp [closure_eq]
  apply compl_inj_iff.mp
  simp
  apply interior_inter_eq h𝒯

-- in the discrete topology, the closure of any set is itself
theorem discrete_closure (A: Set X): closure Set.univ A = A := by
  simp [closure_eq, discrete_interior]



def boundary (𝒯: Family X) (A: Set X): Set X :=
  {x | ∀ N ∈ Nbhd 𝒯 x, Set.Nonempty (N ∩ A) ∧ Set.Nonempty (N ∩ Aᶜ)}

theorem boundary_eq (𝒯: Family X) (A: Set X): boundary 𝒯 A = closure 𝒯 A ∩ closure 𝒯 Aᶜ := by
  simp [boundary, closure, adherent]
  ext
  exact forall₂_and

-- the boundary of the closure is the same as the boundary
theorem boundary_closure_eq (𝒯: Family X) (A: Set X): boundary 𝒯 (closure 𝒯 A) = boundary 𝒯 A := by
  calc
    boundary 𝒯 (closure 𝒯 A) = closure 𝒯 (closure 𝒯 A) ∩ closure 𝒯 (closure 𝒯 A)ᶜ := by rw [boundary_eq]
                           _ = closure 𝒯 A ∩ closure 𝒯 (closure 𝒯 A)ᶜ := by rw [closure_idempotent]
                           _ = closure 𝒯 A ∩ closure 𝒯 (interior 𝒯 Aᶜ) := by rw [compl_closure_eq_interior_compl]
                           _ = closure 𝒯 A ∩ closure 𝒯 Aᶜ := sorry
                           _ = boundary 𝒯 A := by rw [boundary_eq]

theorem boundary_closed (𝒯: Family X) (A: Set X): Closed 𝒯 (boundary 𝒯 A) := by
  sorry

-- TODO: is basic neighborhood worth defining?
theorem boundary_mem_iff {𝒯 ℬ: Family X} (h: base 𝒯 ℬ) (A: Set X) (x: X): x ∈ boundary 𝒯 A ↔ ∀ N ∈ Nbhd 𝒯 x ∩ ℬ, N ∩ A = ∅ ∧ N ∩ Aᶜ = ∅ := by
  sorry

theorem boundary_univ {𝒯: Family X} (h𝒯: IsTopology 𝒯): boundary 𝒯 Set.univ = ∅ := by
  simp [boundary_eq, closure_empty h𝒯]

theorem boundary_empty {𝒯: Family X} (h𝒯: IsTopology 𝒯): boundary 𝒯 ∅ = ∅ := by
  simp [boundary_eq, closure_empty h𝒯]

-- in the discrete topology, the boundary of every set is empty
theorem discrete_boundary (A: Set X): boundary Set.univ A = ∅ := by
  simp [boundary_eq, discrete_closure]

def exterior_point (𝒯: Family X) (A: Set X) (x: X): Prop :=
  x ∈ interior 𝒯 Aᶜ

def exterior (𝒯: Family X) (A: Set X): Set X :=
  {x | exterior_point 𝒯 A x}

theorem exterior_eq (𝒯: Family X) (A: Set X): exterior 𝒯 A = (closure 𝒯 A)ᶜ := by
  simp [exterior, exterior_point, compl_closure_eq_interior_compl]

-- TODO this is clunky
-- the interior, boundary, and exterior form a disjoint union of the whole space.
theorem boundary_partition (𝒯: Family X) (A: Set X) :
  (interior 𝒯 A ∪ boundary 𝒯 A ∪ exterior 𝒯 A = X) ∧ (interior 𝒯 A ∩ boundary 𝒯 A = ∅) ∧ (interior 𝒯 A ∩ exterior 𝒯 A = ∅) ∧ (boundary 𝒯 A ∩ exterior 𝒯 A = ∅) := by
  repeat' constructor
  · sorry
  · sorry
  · sorry
  · sorry

-- in the discrete topology, the exterior of a set is its complement
theorem discrete_exterior (A: Set X): exterior Set.univ A = Aᶜ := by
  simp [exterior_eq, closure_eq, discrete_interior]

theorem closure_eq_interior_union_boundary (𝒯: Family X) (A: Set X): closure 𝒯 A = interior 𝒯 A ∪ boundary 𝒯 A := by
  sorry

theorem interior_eq_set_minus_boundary (𝒯: Family X) (A: Set X): interior 𝒯 A = A \ boundary 𝒯 A := by
  sorry
