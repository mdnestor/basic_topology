import basic_topology.Quotient
import basic_topology.Continuity
import basic_topology.Connected
import basic_topology.Product

variable {I X Y: Type*} {T: Family X}

/-

A somewhat clunky axiomatization of the unit interval as a topological space I with
- two distinguished points 0, 1 ∈ I.
- a continuous involution i: I → I with i(0) = 1 and i(1) = 0.

-/

axiom Interval: TopologicalSpace

variable [Zero Interval.points] [One Interval.points]

axiom Interval.inv: Interval.points → Interval.points

axiom Interval.inv_continuous: Continuous Interval.topology.Open Interval.topology.Open Interval.inv

axiom Interval.inv_zero: Interval.inv 0 = 1

axiom Interval.inv_one: Interval.inv 1 = 0



class Path (T: Family X) (x y: X) where
  map: Interval.points → X
  continuous: Continuous Interval.topology.Open T map
  zero: map 0 = x
  one: map 1 = y

def Path.const (T: Family X) (x: X): Path T x x := {
  map := fun _ => x
  continuous := by exact Continuous.const Interval.topology.is_topology x
  zero := by rfl
  one := by rfl
}

noncomputable def Path.reverse {x y: X} (p: Path T x y): Path T y x := {
  map := p.map ∘ Interval.inv
  continuous := by
    apply Continuous.comp
    · exact Interval.inv_continuous
    · exact p.continuous
  zero := by simp [Interval.inv_zero, p.one]
  one := by simp [Interval.inv_one, p.zero]
}

noncomputable def Path.comp {x y z: X} (p: Path T x y) (q: Path T y z): Path T x z :=
  sorry

def Path.exists (T: Family X): Endorelation X :=
  fun x y => Nonempty (Path T x y)

theorem Path.equivalence (T: Family X): Equivalence (Path.exists T) := {
  refl := by
    intro x
    constructor
    exact Path.const T x
  symm := by
    intro x y h
    constructor
    exact Path.reverse (Classical.choice h)
  trans := by
    intro x y z h₁ h₂
    constructor
    exact Path.comp (Classical.choice h₁) (Classical.choice h₂)
}

def Path.components {X: Type u} (T: Family X): Type u :=
  Quotient ⟨Path.exists T, Path.equivalence T⟩

def PathConnected (T: Family X): Prop :=
  ∀ x y, Path.exists T x y

theorem Path.connected_components_subsingleton (T: Family X) (h: PathConnected T): Subsingleton (Path.components T) := by
  constructor
  intro x y
  sorry
  
theorem PathConnected.connected (T: Family X) (h: PathConnected T): Connected T := by
  sorry

class Homotopy (T₁: Family X) (T₂: Family Y) (f g: X → Y) where
  map: X × Interval.points → Y
  continuous: Continuous (product_topology T₁ Interval.topology.Open) T₂ map
  zero: ∀ x, map (x, 0) = f x
  one: ∀ x, map (x, 1) = g x

example (p: Path T x y): Homotopy (Set.univ: Family Unit) T (fun _ => x) (fun _ => y) := {
  map := fun (_, t) => p.map t
  continuous := sorry
  zero := by intro; exact p.zero
  one := by intro; exact p.one
}


def Homotopy.const (T₁: Family X) (T₂: Family Y) (f: X → Y): Homotopy T₁ T₂ f f := {
  map := fun (x, _) => f x
  continuous := by sorry
  zero := by intro; rfl
  one := by intro; rfl
}

noncomputable def Homotopy.reverse (T₁: Family X) (T₂: Family Y) (h: Homotopy T₁ T₂ f g): Homotopy T₁ T₂ g f :=
  sorry

noncomputable def Homotopy.comp (T₁: Family X) (T₂: Family Y) (h₁: Homotopy T₁ T₂ e f) (h₂: Homotopy T₁ T₂ f g): Homotopy T₁ T₂ e g :=
  sorry

