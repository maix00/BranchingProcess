import Probability.BranchingRandomWalk.Walk.Law
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Assumptions for the variance-one Mogulskii theorem

These predicates record the hypotheses of the `α = 2` theorem without
bundling a new random-walk type.
-/

open Filter MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

/-- A one-step law has mean zero and second moment one. -/
def IsCenteredUnitSecondMoment (ν : Measure ℝ) : Prop :=
  (∫ x, x ∂ν) = 0 ∧ (∫ x, x ^ 2 ∂ν) = 1

/-- A spatial scale diverges while remaining negligible compared with the
diffusive scale. -/
def IsMogulskiiScale (scale : ℕ → ℝ) : Prop :=
  Tendsto scale atTop atTop ∧
    Tendsto (fun n => scale n / Real.sqrt n) atTop (nhds 0)

theorem IsMogulskiiScale.eventually_pos {scale : ℕ → ℝ}
    (hscale : IsMogulskiiScale scale) :
    ∀ᶠ n in atTop, 0 < scale n :=
  hscale.1.eventually (eventually_gt_atTop 0)

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
