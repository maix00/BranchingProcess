/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Support of a nondegenerate strictly stable law at index one

The strict stability identity at index one says that the sum of two
independent samples has the law of twice one sample. If a nonzero exponential
of the sample is square integrable, its first and second moments therefore
have zero variance. This forces degeneracy, contradicting strict stability.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

theorem IsStrictlyAlphaStable.not_memLp_exp_mul_indexOne
    {μ : Measure ℝ} (h : IsStrictlyAlphaStable 1 μ)
    (s : ℝ) (hs : s ≠ 0) :
    ¬ MemLp (fun x : ℝ => Real.exp (s * x)) 2 μ := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  intro hf
  let f : ℝ → ℝ := fun x => Real.exp (s * x)
  have hfmeas : Measurable f := by fun_prop
  have hscale : alphaStableScale 1 1 1 = 2 := by
    norm_num [alphaStableScale]
  have hstable :
      (μ.prod μ).map (fun p : ℝ × ℝ => p.1 + p.2) =
        μ.map (fun x : ℝ => 2 * x) := by
    have hst := h.2.2.2.2 1 1 (by norm_num) (by norm_num)
    unfold weightedSum at hst
    simpa only [one_mul, hscale] using hst
  have hmoment : (∫ x, f x ^ 2 ∂μ) = (∫ x, f x ∂μ) ^ 2 := by
    have heq := congrArg (fun ν : Measure ℝ => ∫ x, f x ∂ν) hstable
    rw [integral_map (by fun_prop : AEMeasurable
        (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod μ)) hfmeas.aestronglyMeasurable,
      integral_map (by fun_prop : AEMeasurable
        (fun x : ℝ => 2 * x) μ) hfmeas.aestronglyMeasurable] at heq
    have hprod : (∫ p : ℝ × ℝ, f (p.1 + p.2) ∂μ.prod μ) =
        (∫ x, f x ∂μ) * (∫ x, f x ∂μ) := by
      have hpoint (p : ℝ × ℝ) : f (p.1 + p.2) = f p.1 * f p.2 := by
        dsimp [f]
        rw [mul_add, Real.exp_add]
      simp_rw [hpoint]
      exact integral_prod_mul f f
    have hdouble : (∫ x, f (2 * x) ∂μ) = ∫ x, f x ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [f]
      rw [show s * (2 * x) = s * x + s * x by ring, Real.exp_add, pow_two]
    rw [hprod, hdouble] at heq
    simpa [pow_two] using heq.symm
  have hvar : Var[f; μ] = 0 := by
    rw [variance_eq_sub hf]
    exact sub_eq_zero.mpr hmoment
  have hae := ae_eq_integral_of_variance_eq_zero hf hvar
  obtain ⟨y, hy⟩ := hae.exists
  have haeId : (fun x : ℝ => x) =ᵐ[μ] (fun _ => y) := by
    filter_upwards [hae] with x hx
    exact mul_left_cancel₀ hs (Real.exp_injective (hx.trans hy.symm))
  have hdirac : μ = Measure.dirac y := by
    have hm : Measure.map (fun x : ℝ => x) μ =
        Measure.map (fun _ : ℝ => y) μ :=
      Measure.map_congr haeId
    simpa [Measure.map_id, Measure.map_const, measure_univ] using hm
  exact h.nondegenerate ⟨y, hdirac⟩

/-- A nondegenerate strictly 1-stable law charges every open left half-line.
Otherwise `exp (-x)` is bounded almost everywhere, contradicting the
preceding variance argument. -/
theorem IsStrictlyAlphaStable.measure_Iio_pos_indexOne
    {μ : Measure ℝ} (h : IsStrictlyAlphaStable 1 μ) (v : ℝ) :
    0 < μ (Set.Iio v) := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  by_contra hnonpos
  have hzero : μ (Set.Iio v) = 0 :=
    nonpos_iff_eq_zero.mp (le_of_not_gt hnonpos)
  have hae : ∀ᵐ x : ℝ ∂μ, v ≤ x := by
    rw [ae_iff]
    simpa [Set.Iio, Set.compl_ofPred, not_le] using hzero
  have hbounded : ∀ᵐ x : ℝ ∂μ,
      Real.exp (-x) ∈ Set.Icc 0 (Real.exp (-v)) := by
    filter_upwards [hae] with x hx
    exact ⟨(Real.exp_pos _).le,
      Real.exp_le_exp.mpr (neg_le_neg hx)⟩
  have hf : MemLp (fun x : ℝ => Real.exp (-x)) 2 μ :=
    memLp_of_bounded hbounded (by fun_prop) 2
  exact (h.not_memLp_exp_mul_indexOne (-1) (by norm_num))
    (by simpa only [neg_one_mul] using hf)

/-- A nondegenerate strictly 1-stable law charges every open right half-line.
Otherwise `exp x` is bounded almost everywhere. -/
theorem IsStrictlyAlphaStable.measure_Ioi_pos_indexOne
    {μ : Measure ℝ} (h : IsStrictlyAlphaStable 1 μ) (v : ℝ) :
    0 < μ (Set.Ioi v) := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  by_contra hnonpos
  have hzero : μ (Set.Ioi v) = 0 :=
    nonpos_iff_eq_zero.mp (le_of_not_gt hnonpos)
  have hae : ∀ᵐ x : ℝ ∂μ, x ≤ v := by
    rw [ae_iff]
    simpa [Set.Ioi, Set.compl_ofPred, not_le] using hzero
  have hbounded : ∀ᵐ x : ℝ ∂μ,
      Real.exp x ∈ Set.Icc 0 (Real.exp v) := by
    filter_upwards [hae] with x hx
    exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr hx⟩
  have hf : MemLp (fun x : ℝ => Real.exp x) 2 μ :=
    memLp_of_bounded hbounded (by fun_prop) 2
  exact (h.not_memLp_exp_mul_indexOne 1 (by norm_num))
    (by simpa only [one_mul] using hf)

end ProbabilityTheory

end
