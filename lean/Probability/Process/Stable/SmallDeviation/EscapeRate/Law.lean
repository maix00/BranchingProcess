/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.Stable.SmallDeviation.EscapeRate
import Probability.Process.Stable.Corridor.Law

/-!
# Law invariance of stable-process escape rates

The range tube is defined by rational-time coordinates. Equal stable
increment specifications therefore give equal range-tube probabilities and,
consequently, the same escape-rate constant.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter MeasureTheory
open scoped NNReal Topology

/-- Whenever the normalized rational range log probabilities for two stable
processes have limits, the limits agree if their stable increment laws agree.
In particular, the escape-rate constant depends only on the stable law. -/
theorem IsStableLevyProcess.escapeRate_constant_eq_of_same_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {α C D : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
    {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X P)
    (hY : IsStableLevyProcess α μ Y Q)
    (hC : Tendsto (stableRangeLogRate P X α)
      (𝓝[>] (0 : ℝ)) (𝓝 C))
    (hD : Tendsto (stableRangeLogRate Q Y α)
      (𝓝[>] (0 : ℝ)) (𝓝 D)) :
    C = D := by
  have hrate : stableRangeLogRate P X α = stableRangeLogRate Q Y α := by
    funext a
    simp only [stableRangeLogRate]
    rw [hX.rationalRangeProbability_eq_of_same_law hY a]
  rw [hrate] at hC
  exact tendsto_nhds_unique hC hD

end ProbabilityTheory

end
