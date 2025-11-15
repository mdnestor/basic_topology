import basic_topology.Quotient
import basic_topology.Continuity

variable {I X Y: Type*}



class Bipointed (X: Type u) extends Topology X where
  zero: X
  one: X

def Bipointed.flip (T: Bipointed X): Bipointed X := {
  Open := T.Open
  is_topology := T.is_topology
  zero := one
  one := zero
}

class Bipointed.hom (TX: Bipointed X) (TY: Bipointed Y) where
  map: X → Y
  continuous: Continuous TX.Open TY.Open map
  source: map zero = zero
  target: map one = one

-- class Path (TI: Family I) [Zero I] [One I] (T: Family X) (x y: X) where
--   path: I → X
--   continuous: Continuous TI T path
--   source: path 0 = x
--   target: path 1 = x

def Bipointed.single (T: Topology X) (x: X): Bipointed X := {
  Open := T.Open
  is_topology := T.is_topology
  zero := x
  one := x
}

def Bipointed.const (TI: Bipointed I) (T: Topology X): Bipointed.hom TI (Bipointed.single T x) := {
  map := fun _ => x
  continuous := Continuous.const TI.is_topology x
  source := rfl
  target := rfl
}

def Bipointed.symm (TI: Bipointed I) (i: Bipointed.hom TI TI) (h0: i.map TI.zero = TI.one) (h1: i.map TI.one = TI.zero) (T: Bipointed X): Bipointed.hom TI T := {
  map := fun _ => x
  continuous := Continuous.const TI.is_topology x
  source := rfl
  target := rfl
}

class Bipointed.hom [Zero X] [One X] [Zero Y] [One Y] (TX: Family X) (TY: Family Y) (f: X → Y) where
  continuous: Continuous TX TY f
  zero: f 0 = 0
  one: f 1 = 1

class Bipointed.inv (i: I → I) where


def Path.symm {TI: Family I} (hTI: IsTopology TI) [Zero I] [One I] (T: Family X) (i: I → I) (hi: Continuous TI TI i) (h0: i 0 = 1) (h1: i 1 = 0) (x y: X) (p: Path TI T x y): Path TI T y x := {
  path := p.path ∘ i

}
