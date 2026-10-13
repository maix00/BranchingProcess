/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Upper

/-!
# Small deviations in a tube with positive linear drift

The public theorem in this file is:

- `driftedTubeEvent_subset_noLargeDropEndpointBelowEvent`:
  for `a ∈ [-Δ,0]` and nonnegative drift `c`, a path in
  `a + cj/Δ² ≤ Y_j ≤ a + cj/Δ² + Δ` for `1 ≤ j ≤ L` has drawdowns at most
  `Δ` and endpoint at most `Δ + cL/Δ²`.

This is the first event inclusion in the proof of Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, Lemma 3.4.
-/

open MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

/-- The path event for a linearly rising tube of width `width`. -/
def driftedTubeEvent (horizon : ℕ) (width drift lower : ℝ) :
    Set (ℕ → ℝ) :=
  {increment | ∀ j : ℕ, 1 ≤ j → j ≤ horizon →
    lower + drift * (j : ℝ) / width ^ 2 ≤
        AdditivePath.displacement j increment ∧
      AdditivePath.displacement j increment ≤
        lower + drift * (j : ℝ) / width ^ 2 + width}

/-- On a tube with nonnegative drift, the upper constraint at time `i`
and lower constraint at time `j ≥ i` bound the drawdown by its width. -/
theorem driftedTubeEvent_subset_noLargeDropEndpointBelowEvent
    (horizon : ℕ) {width drift lower : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hlower : -width ≤ lower) (hupper : lower ≤ 0) :
    driftedTubeEvent horizon width drift lower ⊆
      noLargeDropEndpointBelowEvent horizon width
        (width + drift * (horizon : ℝ) / width ^ 2) := by
  intro increment hpath
  have hslope : 0 ≤ drift / width ^ 2 := div_nonneg hdrift (sq_nonneg width)
  have htube (j : ℕ) (hj : 1 ≤ j) (horizonBound : j ≤ horizon) :=
    hpath j hj horizonBound
  constructor
  · intro i j hij hj
    by_cases hjzero : j = 0
    · have hizero : i = 0 := by omega
      subst i
      subst j
      simp [AdditivePath.displacement_zero, hwidth.le]
    have hjpos : 1 ≤ j := by omega
    have hjtube := htube j hjpos hj
    by_cases hi : i = 0
    · subst i
      have hterm : 0 ≤ drift * (j : ℝ) / width ^ 2 := by positivity
      simpa [AdditivePath.displacement_zero] using
        (show (0 : ℝ) - AdditivePath.displacement j increment ≤ width by
          linarith [hjtube.1])
    · have hipos : 1 ≤ i := by omega
      have hitube := htube i hipos (by omega)
      have htime : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      have hnonneg :
          drift * (i : ℝ) / width ^ 2 ≤
            drift * (j : ℝ) / width ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left htime hslope
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
      linarith [hitube.2, hjtube.1]
  · by_cases hzero : horizon = 0
    · subst horizon
      simp [AdditivePath.displacement_zero]
      linarith
    · have hpos : 1 ≤ horizon := by omega
      have hend := htube horizon hpos le_rfl
      linarith [hend.2]

end ProbabilityTheory.RandomWalk.SmallDeviation
