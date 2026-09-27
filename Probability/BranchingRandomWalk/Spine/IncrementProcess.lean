import Probability.BranchingRandomWalk.Spine.TiltedLaw
import Mathlib.Probability.Independence.InfinitePi

/-!
# The independent tilted increment process

Under boundary normalization the integrated tilted potential law is a
probability measure.  Its countable product is the canonical spine increment
process.  This file records the coordinate laws, independence, and measurable
partial-sum positions used in the path form of the many-to-one formula.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching MeasureTheory

noncomputable def tiltedIncrementFieldLaw {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X)) :
    Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => tiltedPotentialLaw φ (-1) μ)

theorem tiltedIncrementFieldLaw_isProbability {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) := by
  let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
    tiltedPotentialLaw_isProbability φ μ hboundary
  unfold tiltedIncrementFieldLaw
  infer_instance

theorem tiltedIncrementFieldLaw_coordinate {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) (n : ℕ) :
    (tiltedIncrementFieldLaw φ μ).map (fun increment => increment n) =
      tiltedPotentialLaw φ (-1) μ := by
  let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
    tiltedPotentialLaw_isProbability φ μ hboundary
  unfold tiltedIncrementFieldLaw
  exact Measure.infinitePi_map_eval
    (fun _ : ℕ => tiltedPotentialLaw φ (-1) μ) n

theorem tiltedIncrementFieldLaw_independent {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    iIndepFun (fun n (increment : ℕ → ℝ) => increment n)
      (tiltedIncrementFieldLaw φ μ) := by
  let _ : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
    tiltedPotentialLaw_isProbability φ μ hboundary
  unfold tiltedIncrementFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : ℕ => tiltedPotentialLaw φ (-1) μ)
    (X := fun _ : ℕ => id) (fun _ => measurable_id))

/-- Position after `n` tilted increments, with time zero equal to zero. -/
def tiltedPosition (n : ℕ) (increment : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, increment k

@[simp] theorem tiltedPosition_zero (increment : ℕ → ℝ) :
    tiltedPosition 0 increment = 0 := by
  simp [tiltedPosition]

theorem tiltedPosition_succ (n : ℕ) (increment : ℕ → ℝ) :
    tiltedPosition (n + 1) increment =
      tiltedPosition n increment + increment n := by
  simp [tiltedPosition, Finset.sum_range_succ]

theorem tiltedPosition_measurable (n : ℕ) :
    Measurable (tiltedPosition n) := by
  unfold tiltedPosition
  exact Finset.measurable_sum (Finset.range n)
    (fun k _ => measurable_pi_apply k)

end ProbabilityTheory.BranchingRandomWalk.Spine
