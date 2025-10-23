import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Int.Even

abbrev Node := {n : Nat // n ≠ 0}

structure GaussSegment where
  private mk ::
  n : Node
  ou : Bool

instance : Repr GaussSegment where
  reprPrec
    | ⟨n, ou⟩, _ => s!"{if ou then "O" else "U"}{n}"

namespace GaussSegment

def mkSegmentFromInt (n : Int) (h : n ≠ 0 := by decide) : GaussSegment :=
  let h1 : n.natAbs ≠ 0 := by simp [Int.natAbs_eq_zero]; tauto
  {n := ⟨n.natAbs, h1⟩, ou := n > 0}

def toInt (self : GaussSegment) : Int :=
  (self.ou.toInt * 2 - 1) * self.n

theorem segment_to_int_ne_zero (self : GaussSegment) : self.toInt ≠ 0 := by
  simp [toInt]
  constructor
  · rw [Int.mul_comm, ← Int.zero_dvd]
    have h : (2: Int) ∣ 0 := by simp
    intro x
    have i := Int.dvd_trans h x
    have y := Int.two_not_dvd_two_mul_add_one (self.ou.toInt - 1)
    have z : (2: Int) - 1 = 1 := by simp
    rw [Int.mul_sub, sub_add, mul_one, z] at y
    tauto
  have x := self.n.prop
  tauto

end GaussSegment

structure GaussComponent where
  segments : Array GaussSegment

namespace GaussComponent

def incidence (self : GaussComponent) (node : Node) (ou : Bool) : Nat :=
  (self.segments.map (fun s => (s.n == node).toNat * (s.ou == ou).toNat)).sum

end GaussComponent

structure VirtualLinkDiagram where
  nodes : Finset Node
  components : Array GaussComponent
  compatible : ∀ c ∈ components, ∀ s ∈ c.segments, s.n ∈ nodes
  complete_over : ∀ n ∈ nodes, (components.map (·.incidence n true)).sum = 1
  complete_under : ∀ n ∈ nodes, (components.map (·.incidence n false)).sum = 1
