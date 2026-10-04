/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Distributions.Stable.LevyMeasure.Cutoff
import Probability.Distributions.Stable.LevyMeasure.Windows
import Probability.Process.Levy.Jump.Intensity.Entrance

/-!
# Positive stable jump windows after a finite-variation cutoff

For `0 < α < 1`, either positive or negative Lévy tail mass supplies every
bounded window on that side. The same deterministic cutoff controls the
small-jump first moment and leaves that window in the finite-activity part.
-/

namespace ProbabilityTheory

open MeasureTheory

theorem IsStrictlyAlphaStable.exists_positiveWindow_cutoff_intensities
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hαpos : 0 < α) (hαlt : α < 1)
    (htail : 0 < T.levyMeasure (Set.Ioi 1))
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (hδr : δ ≤ r) :
    ∃ n : ℕ,
      (∫⁻ z : unitInterval × ℝ, ENNReal.ofReal |z.2|
        ∂((volume : Measure unitInterval).prod
          (T.levyMeasure.restrict (smallJumpBand n)))) < ENNReal.ofReal ρ ∧
      0 < ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n)))
          (Set.univ ×ˢ Set.Ioo r R) ∧
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n))) Set.univ < ⊤ := by
  let : SigmaFinite T.levyMeasure := T.isLevyMeasure.sigmaFinite
  apply exists_unitTime_cutoff_intensities T.levyMeasure
    (h.levyMeasure_smallJumpMoment_lt_top T hT hαlt).ne
    T.levyMeasure_largeJumpBand_lt_top measurableSet_Ioo
    (h.levyMeasure_Ioo_pos_of_pos_tail T hT hαpos hr hrR htail)
    ρ δ hρ hδ
  intro x hx
  have hx0 : 0 ≤ x := by linarith [hx.1]
  rw [abs_of_nonneg hx0]
  exact hδr.trans hx.1.le

theorem IsStrictlyAlphaStable.exists_negativeWindow_cutoff_intensities
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hαpos : 0 < α) (hαlt : α < 1)
    (htail : 0 < T.levyMeasure (Set.Iio (-1)))
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (hδr : δ ≤ r) :
    ∃ n : ℕ,
      (∫⁻ z : unitInterval × ℝ, ENNReal.ofReal |z.2|
        ∂((volume : Measure unitInterval).prod
          (T.levyMeasure.restrict (smallJumpBand n)))) < ENNReal.ofReal ρ ∧
      0 < ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n)))
          (Set.univ ×ˢ Set.Ioo (-R) (-r)) ∧
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n))) Set.univ < ⊤ := by
  let : SigmaFinite T.levyMeasure := T.isLevyMeasure.sigmaFinite
  apply exists_unitTime_cutoff_intensities T.levyMeasure
    (h.levyMeasure_smallJumpMoment_lt_top T hT hαlt).ne
    T.levyMeasure_largeJumpBand_lt_top measurableSet_Ioo
    (h.levyMeasure_neg_Ioo_pos_of_neg_tail T hT hαpos hr hrR htail)
    ρ δ hρ hδ
  intro x hx
  have hx0 : x ≤ 0 := by linarith [hx.2]
  rw [abs_of_nonpos hx0]
  linarith [hx.2]

end ProbabilityTheory
