import MeasureTheory.BranchingWalk.Slot.Basic
import MeasureTheory.UlamHarris.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Path positions on the pre-sampled marked tree

An address specifies child slots along a path. Its position is the sum of
displacements in the marks of its strict ancestors. This total function is
defined even for addresses whose optional child slot is absent; a later
particle-system construction must restrict to realized addresses.
-/

open MeasureTheory

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris



/-- Every child slot follows its presence flag; in particular slot zero may
be absent and the child point process may be empty. -/
def childRealized (i : ℕ) : Set NatRealStep :=
  childPresent i

theorem childRealized_measurable (i : ℕ) :
    MeasurableSet (childRealized i) := by
  exact childPresent_measurable i

/-- The position at a Ulam--Harris address, regardless of its realization. -/
def vertexPosition (ω : Mark ℕ NatRealStep) (u : 𝕍) : ℝ :=
  ∑ j ∈ Finset.range u.length,
    childStep (ω (u.take j)) (u[j]!)

def pathMark (ω : Mark ℕ NatRealStep) (u : 𝕍) : ℝ :=
  vertexPosition ω u

theorem pathMark_eq_vertexPosition (ω : Mark ℕ NatRealStep) (u : 𝕍) :
    pathMark ω u = vertexPosition ω u := rfl

theorem vertexPosition_append_singleton
    (ω : Mark ℕ NatRealStep) (u : 𝕍) (i : ℕ) :
    vertexPosition ω (u ++ [i]) =
      vertexPosition ω u + childStep (ω u) i := by
  simp only [vertexPosition, List.length_append, List.length_singleton,
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
def realizedNodeSet (u : 𝕍) : Set (Mark ℕ NatRealStep) :=
  {ω | ∀ j ∈ Finset.range u.length,
    ω (u.take j) ∈ childRealized (u[j]!)}

end BranchingWalk

end MeasureTheory
