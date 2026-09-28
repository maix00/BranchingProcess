import Combinatorics.BranchingWalk.Walk.Path.Basic
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Assumptions

/-!
# Rescaled step paths

Mogulskii's path is the right-continuous step path obtained by dividing the
first `⌊nt⌋` increments by the spatial scale.  The ambient Skorokhod topology
and corridor classes are developed separately from this pointwise path.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- The normalized step path used in Mogulskii's theorem.  Its intended time
domain is `[0,1]`; defining it on all reals makes endpoint evaluation and
composition easier. -/
noncomputable def normalizedStepPath (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) (t : ℝ) : ℝ :=
  (scale n)⁻¹ * partialSum ⌊(n : ℝ) * t⌋₊ increment

@[simp] theorem normalizedStepPath_zero (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) :
    normalizedStepPath scale n increment 0 = 0 := by
  simp [normalizedStepPath]

/-- Evaluation of the normalized path at a fixed time is a random variable. -/
theorem normalizedStepPath_measurable (scale : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    Measurable (fun increment : ℕ → ℝ =>
      normalizedStepPath scale n increment t) := by
  exact measurable_const.mul (partialSum_measurable _)

/-- At time one, the normalized path is the normalized `n`-step sum. -/
@[simp] theorem normalizedStepPath_one (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) :
    normalizedStepPath scale n increment 1 =
      (scale n)⁻¹ * partialSum n increment := by
  simp [normalizedStepPath]

/-- Evaluation on the `n`-step time grid recovers the corresponding partial
sum. -/
theorem normalizedStepPath_grid (scale : ℕ → ℝ) {n k : ℕ}
    (hn : 0 < n) (increment : ℕ → ℝ) :
    normalizedStepPath scale n increment ((k : ℝ) / n) =
      (scale n)⁻¹ * partialSum k increment := by
  rw [normalizedStepPath]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hgrid : (n : ℝ) * ((k : ℝ) / n) = k := by
    field_simp
  rw [hgrid, Nat.floor_natCast]

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
