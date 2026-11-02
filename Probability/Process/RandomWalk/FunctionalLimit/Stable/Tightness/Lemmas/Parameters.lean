/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Parameter choice for stable compact-range bounds

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_stableRangeParameters`:
  given $0<\alpha<2$, $\varepsilon>0$, and a real bias bound $b(r)$, choose
  $r,\theta>0$ such that
  \[
   b(r)<\frac{\theta}{2},\qquad
   \frac{2-\alpha}{\alpha}r^{-\alpha}+\frac{\varepsilon}{4}
     +\frac{4(r^{2-\alpha}+1)}{\theta^2}<\varepsilon.
  \]

This scalar parameter selection is used only by the stable compact-range
proof in the sibling `Range.lean` module.
-/

open Filter

section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- Choose a truncation radius and excursion threshold so that the bias and
tail-plus-moment contributions fit a prescribed positive error budget. -/
lemma exists_stableRangeParameters
    {α ε : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) (hε : 0 < ε)
    (biasBound : ℝ → ℝ) :
    ∃ radiusMultiplier thresholdMultiplier : ℝ,
      0 < radiusMultiplier ∧ biasBound radiusMultiplier < thresholdMultiplier / 2 ∧
      0 < thresholdMultiplier ∧
        (((2 - α) / α) * radiusMultiplier ^ (-α) + ε / 4) +
            4 * (radiusMultiplier ^ (2 - α) + 1) / thresholdMultiplier ^ 2 < ε := by
  let tailCoefficient : ℝ := (2 - α) / α
  have htailCoefficient : 0 < tailCoefficient := by
    dsimp [tailCoefficient]
    positivity
  have htailTendsto : Tendsto (fun r : ℝ => tailCoefficient * r ^ (-α))
    atTop (nhds 0) := by
    have hpow := tendsto_rpow_neg_atTop hα₀
    simpa using tendsto_const_nhds.mul hpow
  have htailEventually : ∀ᶠ r : ℝ in atTop,
      tailCoefficient * r ^ (-α) < ε / 4 :=
    htailTendsto.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨lower, hlower⟩ := eventually_atTop.1 htailEventually
  let radiusMultiplier : ℝ := max lower 1 + 1
  have hradius : 0 < radiusMultiplier := by
    dsimp [radiusMultiplier]
    positivity
  have htailSmall : tailCoefficient * radiusMultiplier ^ (-α) < ε / 4 := by
    apply hlower radiusMultiplier
    dsimp [radiusMultiplier]
    calc
      lower ≤ max lower 1 := le_max_left _ _
      _ ≤ max lower 1 + 1 := by norm_num
  let momentBound : ℝ := radiusMultiplier ^ (2 - α) + 1
  have hmomentBound : 0 < momentBound := by
    dsimp [momentBound]
    positivity
  let thresholdLower : ℝ := max
    (2 * biasBound radiusMultiplier)
    (max 1 (8 * momentBound / ε))
  obtain ⟨m, hm⟩ := exists_nat_gt thresholdLower
  let thresholdMultiplier : ℝ := m
  have hthresholdLower : thresholdLower < thresholdMultiplier := by
    exact_mod_cast hm
  have hthresholdPositive : 0 < thresholdMultiplier := by
    have honeLower : 1 ≤ thresholdLower := by
      dsimp [thresholdLower]
      exact le_trans (le_max_left 1 (8 * momentBound / ε)) (le_max_right _ _)
    linarith
  have hbiasSmall : biasBound radiusMultiplier < thresholdMultiplier / 2 := by
    have hle : 2 * biasBound radiusMultiplier ≤ thresholdLower :=
      le_max_left _ _
    linarith
  have hlarge : 8 * momentBound / ε < thresholdMultiplier := by
    have hle : 8 * momentBound / ε ≤ thresholdLower := by
      dsimp [thresholdLower]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact lt_of_le_of_lt hle hthresholdLower
  have hlargeMul : 8 * momentBound < thresholdMultiplier * ε :=
    (div_lt_iff₀ hε).mp hlarge
  have honeLower : 1 ≤ thresholdLower := by
    dsimp [thresholdLower]
    exact le_trans (le_max_left 1 (8 * momentBound / ε)) (le_max_right _ _)
  have hone : 1 ≤ thresholdMultiplier := le_trans honeLower hthresholdLower.le
  have hthresholdSq : thresholdMultiplier ≤ thresholdMultiplier ^ 2 := by
    nlinarith [sq_nonneg (thresholdMultiplier - 1)]
  have hinv : (thresholdMultiplier ^ 2)⁻¹ ≤ thresholdMultiplier⁻¹ :=
    (inv_le_inv₀ (sq_pos_of_pos hthresholdPositive) hthresholdPositive).2
      hthresholdSq
  have hmomentFrac :
      4 * momentBound / thresholdMultiplier ^ 2 ≤
        4 * momentBound / thresholdMultiplier := by
    calc
      4 * momentBound / thresholdMultiplier ^ 2 =
          4 * momentBound * (thresholdMultiplier ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 4 * momentBound * thresholdMultiplier⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 4 * momentBound / thresholdMultiplier := by rw [div_eq_mul_inv]
  have hmomentSmall :
      4 * momentBound / thresholdMultiplier < ε / 2 := by
    rw [div_lt_iff₀ hthresholdPositive]
    nlinarith [hlargeMul]
  refine ⟨radiusMultiplier, thresholdMultiplier, hradius, hbiasSmall,
    hthresholdPositive, ?_⟩
  dsimp [tailCoefficient] at htailSmall
  linarith

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
