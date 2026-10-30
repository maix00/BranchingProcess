/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.CDF
public import Probability.Process.Corridor.Segment
public import Probability.Process.Stable.Levy
import Probability.Process.Stable.SmallDeviation.Blocks.Lower.Entrance.PoissonModel
import Probability.Process.Stable.SmallDeviation.Blocks.Lower.Entrance.Feedback.AboveOne
import Probability.Process.Stable.SmallDeviation.Blocks.Lower.Entrance.Feedback.IndexOne

/-!
# Stable entrance positivity across indices

Public theorem:

- `ProbabilityTheory.IsStableLevyProcess.measure_fullEntrance_pos_of_cdfAtZero_allIndices`:
  if `0 < F_μ(0) < 1`, `-1 < b,c < 1`, and `ε > 0`, then the probability of
  the unit-time corridor event with terminal window `(c-b-ε,c-b+ε)` is
  positive for every strictly stable index `0 < α < 2`.

The proof combines the centered-corridor argument for `α > 1`, the index-one
linear-tube argument, and the finite-variation Poisson construction for
`α < 1`.
## Public declarations

- `measure_fullEntrance_pos_of_cdfAtZero_allIndices` proves that, if
  $0<F_\mu(0)<1$, $b,c\in(-1,1)$, and $\epsilon>0$, then
  $\mathbb P(X_{[0,1]}\subset(c-1,c+1),\ X_1\in(c-b-\epsilon,c-b+\epsilon))>0$
  for every strictly stable index $0<\alpha<2$.

-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- If `0 < F_μ(0) < 1`, the unit-time corridor event with terminal window
`(c-b-ε,c-b+ε)` has positive probability for every strictly stable index
`0 < α < 2`. -/
theorem IsStableLevyProcess.measure_fullEntrance_pos_of_cdfAtZero_allIndices
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε) :
    0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
  rcases lt_trichotomy α 1 with hα | hα | hα
  · exact h.measure_fullEntrance_pos_indexLTOne hα hcdf b c ε hb hc hε
  · subst α
    exact h.measure_fullEntrance_pos_indexOne b c ε hb hc hε
  · exact h.measure_fullEntrance_pos_of_cdfAtZero hα hcdf b c ε hb hc hε

end ProbabilityTheory
