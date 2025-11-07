/-

Connectedness in a topological space.

"We have a saying in Bosnia..."

-/

import basic_topology.Continuity
import basic_topology.Dense
import basic_topology.Subspace

variable {X Y: Type*} {T: Family X}

def Connected (T: Family X): Prop :=
  ∀ {U V}, Open T U → Open T V → U.Nonempty → V.Nonempty → U ∪ V = ⊤ → (U ∩ V).Nonempty

-- A space is connected iff. only ∅ and X are clopen.
-- Proof: Suppose bwoc. exist clopen A with ∅ ⊊ A ⊊ X. Then X = A ⊔ Aᶜ, contradiction.
-- TODO: perhaps it is easier to work with the condition that `A.Nonempty ∧ Aᶜ.Nonempty`.
theorem connected_iff [Nonempty X] (hT: IsTopology T):
  Connected T ↔ ∀ U, Clopen T U ↔ U = ∅ ∨ U = ⊤ := by
  constructor
  · intro h U
    constructor
    · intro ⟨hU₁, hU₂⟩
      have := h hU₁ hU₂
      simp_all
      sorry
    · intro h; match h with
      | Or.inl h => rw [h]; exact empty_clopen hT
      | Or.inr h => rw [h]; exact univ_clopen hT
  · intro h₀ U V h₁ h₂ h₃ h₄ h₅
    by_contra
    have: V = Uᶜ := by sorry

    sorry

-- X is connected iff. every continuous map to trivial space with > 1 point is constant.
/-

Suppose bwoc a non-constant map f: X → Y.
Then exist y such that f⁻¹({y}) and f⁻¹(Y \ {y}) are open nonempty
and partition X.

Now suppose every continuous map f: X → Y is constant.
Suppose bwoc A ∪ B is an open partition of X.
Then take the map sending A -> 0 and B -> 1.

-/
-- TODO: maybe easier to show for codomain = 2 first.
theorem connected_iff' (T: Family X) [Nonempty X] [Nonempty Y] [Nontrivial Y]:
  Connected T ↔ ∀ {f: X → Y}, Continuous T (DiscreteTopology Y) f → ∃ y, ∀ x, f x = y := by
  constructor
  intro h₀ f h₁
  let x₀: X := Classical.ofNonempty
  exists f x₀
  intro x
  by_contra
  sorry
  intro h₀

  sorry

def ConnectedSpace (X: TopologicalSpace): Prop :=
  Connected X.topology.Open


-- If X is connected and X is homeomorphic to Y then Y is connected.
-- TODO: maybe just show for continuous surjection first.
theorem homeomorphic_connected {T: Family X} {T': Family Y} (f: Homeomorphic T T') (h: Connected T): Connected T' := by
  sorry

-- connectedness is a topological property
theorem connected_topological_property: TopologicalProperty ConnectedSpace := by
  exact homeomorphic_connected

-- A ⊆ X is called a connected set if it's connected as a subspace.
def ConnectedSet (T: Family X) (A: Set X): Prop :=
  Connected (subspace T A)

-- A more convenient condition.
theorem ConnectedSet.iff {T: Family X} {A: Set X}:
  ConnectedSet T A ↔ ∀ {U V}, Open T U → Open T V → (A ∩ U).Nonempty → (A ∩ V).Nonempty → A ⊆ U ∪ V → (U ∩ V).Nonempty := by
  constructor
  · intro h₁ U V h₂ h₃ h₄ h₅ h₆
    sorry
  · intro h U V h₁ h₂ h₃ h₄ h₅
    sorry

-- TODO: a set A is connected if ∀ coverings of A by C₁,C₂ s.t. A∩C₁, A∩C₂ nonempty
-- then A∩C₁∩C₂ nonempty.


-- Any empty set and singleton are connected
example: ConnectedSpace EmptySpace := by
  sorry

example: ConnectedSpace SingletonSpace := by
  sorry

-- TODO: In a Hausdorff space every finite set of > 1 point is not connected.

-- If A is dense and A is a connected set then X is connected.
/-
Proof idea: suppose X is disconnected with X = U ⊔ V.
Since A is dense, both A ∩ U and A ∩ V are both nonempty, implying A is disconnected.
-/
theorem dense_connected {A: Set X} (h₁: dense T A) (h₂: ConnectedSet T A): Connected T := by
  intro U V hU₁ hV₁ hU₂ hV₂ h₃
  apply ConnectedSet.iff.mp h₂ hU₁ hV₁
  · exact h₁ U hU₁ hU₂
  · exact h₁ V hV₁ hV₂
  · exact subset_of_subset_of_eq (fun ⦃a⦄ a ↦ trivial) (Eq.symm h₃) -- `exact?` GOAT

--  Let A connected set and A ⊆ B ⊆ Closure(A). Then B is connected.
example (h₁: ConnectedSet T A) (h₂: A ⊆ B) (h₃: B ⊆ closure T A): ConnectedSet T B := by
  apply ConnectedSet.iff.mpr
  intro U V hU₁ hV₁ hU₂ hV₂ h₄
  apply ConnectedSet.iff.mp h₁ hU₁ hV₁
  sorry
  sorry
  exact le_trans h₂ h₄

-- TODO: If B is a connected set s.t. A ∩ B and Aᶜ ∩ B are nonempty then B ∩ Boundary(A).

-- TODO: In a connected space every nonempty set other than X has a nonempty boundary.
example (h1: Connected T) (h2: A.Nonempty) (h3: Aᶜ.Nonempty): (frontier T A).Nonempty := by
  sorry

-- TODO: A union of connected sets with nonempty intersection is connected.
/-

Proof: let {A i | i ∈ I} connected and let A = ⋃ (i: I), A i. Suppose ⋂ (i: I), A i is nonempty.

Let f: A → {0, 1} be continuous. WTS f is constant.

Since each A i is connected then the restriction f|(A i) is constant and the value agrees on the intersection.

Hence f is constant.

-/

-- TODO: let A_n be a sequence of connected sets s.t. A_n ∩ A_(n + 1) is nonempty. Then the union is connected.

theorem connected_sequence (A: Nat → Set X) (h: ∀ n, ConnectedSet T (A n)) (h2: ∀ n, (A n ∩ A n.succ).Nonempty): ConnectedSet T (⋃ n, A n) := by
  sorry


-- TODO: a continuous image of connected is connected,
-- i.e. if X is connected and f: X → Y is continuous and surjective then Y is connected.

theorem continuous_image_conected {TX: Family X} {TY: Family Y} (hTX: IsTopology TX) (hTY: IsTopology TY) (f: X → Y) (hf: Function.Surjective f) (hX: Connected TX): Connected TY := by
  sorry

-- The connected component
def ConnectedComponent (T: Family X) (x: X): Set X :=
  Set.sUnion {U | x ∈ U ∧ ConnectedSet T U}

theorem component_connected (T: Family X) (x: X):
  ConnectedSet T (ConnectedComponent T x) := by
  sorry

theorem component_closed (T: Family X) (x: X):
  Closed T (ConnectedComponent T x) := by
  sorry

theorem connected_component_univ (T: Family X) (hT: Connected T)
  (x: X): ConnectedComponent T x = Set.univ := by
  sorry

example (h: ∀ x y, ∃ U, ConnectedSet T U ∧ x ∈ U ∧ y ∈ U): Connected T := by
  sorry

-- Connected components form an equivalence relation
example: Equivalence (fun x y => ConnectedComponent T x = ConnectedComponent T y) := by
  sorry

def TotallyDisconnected (T: Family X): Prop :=
  ∀ x, ConnectedComponent T x = {x}

-- The discrete topology is totally disconnected.
example: TotallyDisconnected (DiscreteTopology X) := by
  intro x
  sorry

-- #check Discrete

-- TODO product connected iff components
