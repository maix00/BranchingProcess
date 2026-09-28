import Combinatorics.BranchingWalk.Walk.Path.Basic
import Mathlib.Algebra.Order.Interval.Finset.Basic

/-!
# Blocks of walk increments

Deterministic sums over consecutive half-open intervals of an increment path.
-/

open MeasureTheory
open scoped BigOperators

namespace Combinatorics.Branching.Walk

/-- The finite vector of consecutive coordinates starting at `start`. -/
def blockCoordinates {E : Type*} (start length : ℕ)
    (increment : ℕ → E) : Fin length → E :=
  fun k => increment (start + k)

theorem blockCoordinates_measurable {E : Type*} [MeasurableSpace E]
    (start length : ℕ) :
    Measurable (blockCoordinates (E := E) start length) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_pi_apply (start + k)

variable {E : Type*} [AddCommMonoid E]

/-- Sum of `length` consecutive increments starting at `start`. -/
def blockSum (start length : ℕ) (increment : ℕ → E) : E :=
  ∑ k ∈ Finset.Ico start (start + length), increment k

@[simp] theorem blockSum_zero (start : ℕ) (increment : ℕ → E) :
    blockSum start 0 increment = 0 := by
  simp [blockSum]

@[simp] theorem blockSum_zero_start (length : ℕ) (increment : ℕ → E) :
    blockSum 0 length increment = partialSum length increment := by
  simp [blockSum, partialSum]

/-- A block sum is a partial sum of the increment path with its prefix
removed. -/
theorem blockSum_eq_partialSum_natAdd (start length : ℕ)
    (increment : ℕ → E) :
    blockSum start length increment =
      partialSum length (fun k => increment (start + k)) := by
  have hmap : (Finset.Ico 0 length).map (addLeftEmbedding start) =
      Finset.Ico start (start + length) := by
    simpa using Finset.map_add_left_Ico 0 length start
  rw [blockSum, partialSum, ← hmap]
  simp

/-- Consecutive blocks concatenate. -/
theorem blockSum_add (start m n : ℕ) (increment : ℕ → E) :
    blockSum start (m + n) increment =
      blockSum start m increment + blockSum (start + m) n increment := by
  rw [blockSum_eq_partialSum_natAdd start (m + n),
    blockSum_eq_partialSum_natAdd start m,
    blockSum_eq_partialSum_natAdd (start + m) n, partialSum_add]
  simp only [partialSum, Nat.add_assoc]

/-- A position at a time inside a block is the position at the block start
plus the corresponding block displacement. -/
theorem partialSum_add_eq_add_blockSum (start length : ℕ)
    (increment : ℕ → E) :
    partialSum (start + length) increment =
      partialSum start increment + blockSum start length increment := by
  rw [partialSum_add, blockSum_eq_partialSum_natAdd]

/-- A fixed block sum is measurable whenever addition on the state space is
measurable. -/
theorem blockSum_measurable [MeasurableSpace E] [MeasurableAdd₂ E]
    (start length : ℕ) : Measurable (blockSum (E := E) start length) := by
  have hfun : blockSum (E := E) start length =
      partialSum length ∘ fun increment => fun k => increment (start + k) := by
    funext increment
    exact blockSum_eq_partialSum_natAdd start length increment
  rw [hfun]
  exact (partialSum_measurable length).comp (measurable_natAdd start)

end Combinatorics.Branching.Walk
