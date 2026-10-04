/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Distributions.Stable.LevyMeasure.Tails

/-!
# Positive jump windows for homogeneous Lévy measures

The power-law tail identities imply positive mass in every window on a side
whose unit tail has positive mass. This does not require a density formula or
an atomlessness theorem.
-/

namespace ProbabilityTheory

open MeasureTheory Set

private theorem measure_Ioo_pos_of_tail_gt (ν : Measure ℝ)
    {r s R : ℝ} (hsR : s < R)
    (htail : ν (Ioi s) < ν (Ioi r)) :
    0 < ν (Ioo r R) := by
  by_contra hzero
  have hzero' : ν (Ioo r R) = 0 := le_antisymm (le_of_not_gt hzero) zero_le
  have hsubset : Ioi r ⊆ Ioo r R ∪ Ioi s := by
    intro x hx
    by_cases hxR : x < R
    · exact Or.inl ⟨hx, hxR⟩
    · exact Or.inr (by simp only [mem_Ioi] at hx ⊢; linarith)
  have hle := (measure_mono hsubset).trans
    (measure_union_le (μ := ν) (Ioo r R) (Ioi s))
  rw [hzero', zero_add] at hle
  exact (not_lt_of_ge hle) htail

private theorem measure_neg_Ioo_pos_of_tail_gt (ν : Measure ℝ)
    {r s R : ℝ} (hsR : s < R)
    (htail : ν (Iio (-s)) < ν (Iio (-r))) :
    0 < ν (Ioo (-R) (-r)) := by
  by_contra hzero
  have hzero' : ν (Ioo (-R) (-r)) = 0 :=
    le_antisymm (le_of_not_gt hzero) zero_le
  have hsubset : Iio (-r) ⊆ Ioo (-R) (-r) ∪ Iio (-s) := by
    intro x hx
    by_cases hxR : -R < x
    · exact Or.inl ⟨hxR, hx⟩
    · exact Or.inr (by simp only [mem_Iio] at hx ⊢; linarith)
  have hle := (measure_mono hsubset).trans
    (measure_union_le (μ := ν) (Ioo (-R) (-r)) (Iio (-s)))
  rw [hzero', zero_add] at hle
  exact (not_lt_of_ge hle) htail

/-- If the positive unit tail has positive mass, every bounded positive
window has positive Lévy mass. -/
theorem IsStrictlyAlphaStable.levyMeasure_Ioo_pos_of_pos_tail
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : 0 < α)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hC : 0 < T.levyMeasure (Ioi 1)) :
    0 < T.levyMeasure (Ioo r R) := by
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  have hs : 0 < s := lt_trans hr hrs
  have hinv : 1 / s < 1 / r := one_div_lt_one_div_of_lt hr hrs
  have hpow : (1 / s) ^ α < (1 / r) ^ α :=
    Real.rpow_lt_rpow (le_of_lt (one_div_pos.mpr hs)) hinv hα
  have hcast : ENNReal.ofReal ((1 / s) ^ α) <
      ENNReal.ofReal ((1 / r) ^ α) :=
    (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos (one_div_pos.mpr hr) α)).2 hpow
  have hCfin : T.levyMeasure (Ioi 1) < ⊤ := by
    apply (measure_mono _).trans_lt
      (T.isLevyMeasure.measure_setOf_abs_ge_lt_top one_pos)
    intro x hx
    simp only [mem_Ioi, mem_ofPred_eq] at hx ⊢
    rw [abs_of_nonneg (by linarith)]
    linarith
  have htail : T.levyMeasure (Ioi s) < T.levyMeasure (Ioi r) := by
    rw [h.levyMeasure_Ioi T hT hs, h.levyMeasure_Ioi T hT hr]
    exact ENNReal.mul_lt_mul_left hC.ne' hCfin.ne hcast
  exact measure_Ioo_pos_of_tail_gt T.levyMeasure hsR htail

/-- If the negative unit tail has positive mass, every bounded negative
window has positive Lévy mass. -/
theorem IsStrictlyAlphaStable.levyMeasure_neg_Ioo_pos_of_neg_tail
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : 0 < α)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hC : 0 < T.levyMeasure (Iio (-1))) :
    0 < T.levyMeasure (Ioo (-R) (-r)) := by
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  have hs : 0 < s := lt_trans hr hrs
  have hinv : 1 / s < 1 / r := one_div_lt_one_div_of_lt hr hrs
  have hpow : (1 / s) ^ α < (1 / r) ^ α :=
    Real.rpow_lt_rpow (le_of_lt (one_div_pos.mpr hs)) hinv hα
  have hcast : ENNReal.ofReal ((1 / s) ^ α) <
      ENNReal.ofReal ((1 / r) ^ α) :=
    (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos (one_div_pos.mpr hr) α)).2 hpow
  have hCfin : T.levyMeasure (Iio (-1)) < ⊤ := by
    apply (measure_mono _).trans_lt
      (T.isLevyMeasure.measure_setOf_abs_ge_lt_top one_pos)
    intro x hx
    simp only [mem_Iio, mem_ofPred_eq] at hx ⊢
    rw [abs_of_nonpos (by linarith)]
    linarith
  have htail : T.levyMeasure (Iio (-s)) < T.levyMeasure (Iio (-r)) := by
    rw [h.levyMeasure_Iio_neg T hT hs, h.levyMeasure_Iio_neg T hT hr]
    exact ENNReal.mul_lt_mul_left hC.ne' hCfin.ne hcast
  exact measure_neg_Ioo_pos_of_tail_gt T.levyMeasure hsR htail

end ProbabilityTheory
