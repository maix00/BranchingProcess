/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.LevyMeasure.Scaling

/-!
# Homogeneous tails of the stable Lévy measure

The positive and negative tail identities retain their constants as the
actual Lévy masses outside `[-1,1]`; no density classification is needed.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Set ENNReal

/-- Positive-tail mass under a reciprocal spatial scale. -/
theorem IsStrictlyAlphaStable.levyMeasure_Ioi_inv
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    {a : ℝ} (ha : 0 < a) :
    T.levyMeasure (Ioi (1 / a)) =
      ENNReal.ofReal (a ^ α) * T.levyMeasure (Ioi 1) := by
  have hscale := h.levyMeasure_map_mul T hT ha
  have hmass := congrArg (fun ν : Measure ℝ => ν (Ioi 1)) hscale
  have hf : Measurable (fun x : ℝ => a * x) := by fun_prop
  rw [Measure.map_apply hf measurableSet_Ioi, Measure.smul_apply] at hmass
  have hpre : (fun x : ℝ => a * x) ⁻¹' Ioi 1 = Ioi (1 / a) := by
    ext x
    simp only [mem_preimage, mem_Ioi]
    simpa only [mul_comm] using (div_lt_iff₀ ha).symm
  rw [hpre] at hmass
  simpa only [smul_eq_mul] using hmass

/-- Negative-tail mass under a reciprocal spatial scale. -/
theorem IsStrictlyAlphaStable.levyMeasure_Iio_neg_inv
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    {a : ℝ} (ha : 0 < a) :
    T.levyMeasure (Iio (-1 / a)) =
      ENNReal.ofReal (a ^ α) * T.levyMeasure (Iio (-1)) := by
  have hscale := h.levyMeasure_map_mul T hT ha
  have hmass := congrArg (fun ν : Measure ℝ => ν (Iio (-1))) hscale
  have hf : Measurable (fun x : ℝ => a * x) := by fun_prop
  rw [Measure.map_apply hf measurableSet_Iio, Measure.smul_apply] at hmass
  have hpre : (fun x : ℝ => a * x) ⁻¹' Iio (-1) = Iio (-1 / a) := by
    ext x
    simp only [mem_preimage, mem_Iio]
    simpa only [mul_comm] using (lt_div_iff₀ ha).symm
  rw [hpre] at hmass
  simpa only [smul_eq_mul] using hmass

/-- Positive-tail mass at an arbitrary positive threshold. -/
theorem IsStrictlyAlphaStable.levyMeasure_Ioi
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    {r : ℝ} (hr : 0 < r) :
    T.levyMeasure (Ioi r) =
      ENNReal.ofReal ((1 / r) ^ α) * T.levyMeasure (Ioi 1) := by
  simpa only [one_div_one_div] using h.levyMeasure_Ioi_inv T hT (one_div_pos.mpr hr)

/-- Negative-tail mass at an arbitrary positive threshold. -/
theorem IsStrictlyAlphaStable.levyMeasure_Iio_neg
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    {r : ℝ} (hr : 0 < r) :
    T.levyMeasure (Iio (-r)) =
      ENNReal.ofReal ((1 / r) ^ α) * T.levyMeasure (Iio (-1)) := by
  simpa only [neg_div, one_div_one_div] using h.levyMeasure_Iio_neg_inv T hT
    (one_div_pos.mpr hr)

/-- The two-sided tail is the sum of the negative and positive tails. -/
theorem IsStrictlyAlphaStable.levyMeasure_abs_tail
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    {r : ℝ} (hr : 0 < r) :
    T.levyMeasure {x : ℝ | r < |x|} =
      ENNReal.ofReal ((1 / r) ^ α) *
        (T.levyMeasure (Iio (-1)) + T.levyMeasure (Ioi 1)) := by
  have hset : {x : ℝ | r < |x|} = Iio (-r) ∪ Ioi r := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      constructor
      · intro hh; exact Or.inr hh
      · rintro (hh | hh)
        · linarith
        · exact hh
    · rw [abs_of_nonpos hx]
      constructor
      · intro hh; exact Or.inl (by linarith)
      · rintro (hh | hh)
        · linarith
        · linarith
  rw [hset, measure_union, h.levyMeasure_Iio_neg T hT hr,
    h.levyMeasure_Ioi T hT hr, mul_add]
  · apply disjoint_left.mpr
    intro x hx hy
    simp only [Set.mem_Iio] at hx
    simp only [Set.mem_Ioi] at hy
    linarith
  · exact measurableSet_Ioi

end ProbabilityTheory
