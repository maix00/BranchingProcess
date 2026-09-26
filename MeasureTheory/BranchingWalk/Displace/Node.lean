import MeasureTheory.BranchingWalk.Step.Slot
import MeasureTheory.UlamHarris.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Node displacement on the pre-sampled marked tree

An address specifies child slots along a path. Its displacement is the sum of
the slot values in the marks of its strict ancestors. This total function is
defined even for addresses whose optional child slot is absent; a later
particle-system construction must restrict to realized addresses. The value
type is arbitrary; the paper's case is `X = ℝ`.
-/

open MeasureTheory

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris



/-- Every child slot follows its presence flag; in particular slot zero may
be absent and the child point process may be empty. -/
def childRealized {X : Type*} (i : ℕ) : Set (NatStep X) :=
  childPresent i

theorem childRealized_measurable {X : Type*} [MeasurableSpace X] (i : ℕ) :
    MeasurableSet (childRealized (X := X) i) :=
  childPresent_measurable i

/-- The displacement of a Ulam--Harris address, regardless of its
realization. -/
def nodeDisplacement {X : Type*} [AddCommMonoid X]
    (ω : Mark ℕ (NatStep X)) (u : 𝕍) : X :=
  ∑ j ∈ Finset.range u.length,
    value (ω (u.take j)) (u[j]!)

theorem nodeDisplacement_append_singleton {X : Type*} [AddCommMonoid X]
    (ω : Mark ℕ (NatStep X)) (u : 𝕍) (i : ℕ) :
    nodeDisplacement ω (u ++ [i]) =
      nodeDisplacement ω u + value (ω u) i := by
  simp only [nodeDisplacement, List.length_append, List.length_singleton,
    Finset.sum_range_succ]
  have hlast : (u ++ [i]).take u.length = u := by simp
  have hslot : (u ++ [i])[u.length]! = i := by simp
  rw [hlast, hslot]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < u.length := Finset.mem_range.mp hj
  simp [List.take_append_of_le_length (Nat.le_of_lt hjlt),
    List.getElem?_append_left hjlt]

/-- An address is realized exactly when every child slot along its path is
present in the corresponding ancestor mark. -/
def realizedNodeSet {X : Type*} (u : 𝕍) : Set (Mark ℕ (NatStep X)) :=
  {ω | ∀ j ∈ Finset.range u.length,
    ω (u.take j) ∈ childRealized (u[j]!)}

end BranchingWalk

end MeasureTheory
