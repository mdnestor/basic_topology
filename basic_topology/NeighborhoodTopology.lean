import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Lattice

set_option linter.style.commandStart false

variable {X Y: Type*}

/-

Definition of topological space. Like for metric spaces :
- Given a type X and a collection of subsets 𝒯, `IsTopology 𝒯` is the statement that 𝒯 forms a topology.
- `Topology X` is the type of all topologies on `X`.
- `TopologicalSpace` is the type of all topological spaces.

For simplicity I guess we will work with `IsTopology` mostly.

-/

abbrev Family (X: Type u): Type u :=
  Set (Set X)

class Nbhds (X: Type u) where
  Nbhd: X → Family X
  mem: ∀ x, ∀ U ∈ Nbhd x, x ∈ U
  inter: ∀ x, ∀ U ∈ Nbhd x, ∀ V ∈ Nbhd x, U ∩ V ∈ Nbhd x
  upper: ∀ x, ∀ U ∈ Nbhd x, ∀ V, U ⊆ V → V ∈ Nbhd x
  link: ∀ x, ∀ U ∈ Nbhd x, ∃ V ∈ Nbhd x, ∀ y ∈ V, U ∈ Nbhd y

export Nbhds (Nbhd)

def Open [Nbhds X]: Family X :=
  {A | ∀ x ∈ A, ∃ N ∈ Nbhd x, N ⊆ A}

def Closed [Nbhds X]: Family X :=
  {A | Open Aᶜ}

def Clopen [Nbhds X]: Family X :=
  Open ∩ Closed

theorem open_empty [Nbhds X]: Open (∅: Set X) := by
  intro _ _; contradiction

theorem open_union [Nbhds X] (𝒰: Set (Set X)) (h: 𝒰 ⊆ Open): Open (⋃₀ 𝒰) := by
  intro x hx
  simp_all [Open]
  obtain ⟨U, hU₁, hU₂⟩ := hx
  have := h hU₁
  simp at this
  have := this x hU₂
  obtain ⟨N, hN⟩ := this
  exists N
  constructor
  exact hN.left
  intro x hx
  exists U
  constructor
  exact hU₁
  exact hN.right hx

theorem open_inter [Nbhds X] (𝒰: Set (Set X)) (h: 𝒰 ⊆ Open) (h2: 𝒰.Finite): Open (⋂₀ 𝒰) := by
  intro x hx
  -- uselemma finite neighborhod intersection is neighborhood
  sorry




def Interior [Nbhds X] (A: Set X): Set X :=
  {x | Nbhd x A}

theorem Interior.mono [Nbhds X] {A B: Set X} (h: A ⊆ B): Interior A ⊆ Interior B := by
  intro x hx
  exact Nbhds.upper x A hx B h

theorem Interior.empty [Nbhds X]: Interior (∅: Set X) = ∅ := by
  ext; simp
  apply Nbhds.mem

def Adherent [Nbhds X] (A: Set X) (x: X): Prop :=
  ∀ U ∈ Nbhd x, (A ∩ U).Nonempty

def Closure [Nbhds X] (A: Set X): Set X :=
 {x | Adherent A x}

def Boundary [Nbhds X] (A: Set X): Set X :=
  {x | ∀ U ∈ Nbhd x, (A ∩ U).Nonempty ∧ (Aᶜ ∩ U).Nonempty}

theorem boundary_eq [Nbhds X] (A: Set X): Boundary A = Closure A ∩ Closure Aᶜ := by
  ext; constructor
  · intro h
    constructor <;> intro U hU
    · exact (h U hU).left
    · exact (h U hU).right
  · intro h U hU
    constructor
    · exact h.left U hU
    · exact h.right U hU

def Dense [Nbhds X] (A: Set X): Prop :=
  ∀ x, ∀ U ∈ Nbhd x, (A ∩ U).Nonempty

theorem dense_iff_closure_univ [Nbhds X] (A: Set X): Dense A ↔ Closure A = ⊤ := by
  constructor
  · intro h
    ext x
    constructor
    · intro; trivial
    · intro; exact h x
  · intro h x
    have: x ∈ Closure A := by rw [h]; trivial
    exact this

def ContinuousAt [Nbhds X] [Nbhds Y] (f: X → Y) (x: X): Prop :=
  ∀ V ∈ Nbhd (f x), ∃ U ∈ Nbhd x, f '' U ⊆ V

def Continuous [Nbhds X] [Nbhds Y] (f: X → Y): Prop :=
  ∀ x, ContinuousAt f x
