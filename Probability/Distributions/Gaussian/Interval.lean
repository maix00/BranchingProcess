module

public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Gaussian interval positivity

The nondegenerate real Gaussian law gives positive mass to every nonempty open
interval.  This is a distribution-level fact and is independent of any random
walk or small-deviation construction.
-/

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

/-- A real Gaussian law with nonzero variance assigns positive mass to every
nonempty open interval. -/
theorem gaussianReal_Ioo_pos {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {a b : ℝ} (hab : a < b) :
    0 < gaussianReal μ v (Ioo a b) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hac := gaussianReal_absolutelyContinuous' μ hv
  have hvolume : (volume : Measure ℝ) (Ioo a b) = 0 := hac hzero
  have hpositive : 0 < (volume : Measure ℝ) (Ioo a b) :=
    (Measure.measure_Ioo_pos (volume : Measure ℝ)).2 hab
  exact hpositive.ne' hvolume

end ProbabilityTheory
