/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Frequency averages for the cosine defect

The average of the squared cosine defect over a compact interval of
frequencies is uniformly positive away from zero. This is the coercivity
input for recovering tails from a regular-variation limit of the cosine
defect.
-/

open MeasureTheory Set
open Filter
open scoped Interval

@[expose] public section

namespace Analysis.Fourier.CosineTauberian

/-- Average squared cosine defect over the frequency interval `[1, 2]`. -/
noncomputable def cosineSquareFrequencyAverage (z : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..2, (1 - Real.cos (t * z)) ^ 2

theorem continuous_cosineSquareFrequencyAverage :
    Continuous cosineSquareFrequencyAverage := by
  change Continuous fun z : ℝ =>
    ∫ t in (1 : ℝ)..2, (1 - Real.cos (t * z)) ^ 2
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) 1 2

private theorem cosineSquareFrequencyAverage_pos_of_one_le {z : ℝ}
    (hz : 1 ≤ z) : 0 < cosineSquareFrequencyAverage z := by
  let f : ℝ → ℝ := fun t => (1 - Real.cos (t * z)) ^ 2
  have hfcont : Continuous f := by fun_prop
  have hfi : IntervalIntegrable f volume 1 2 := hfcont.intervalIntegrable 1 2
  have hnonneg : 0 ≤ᵐ[volume] f := by
    filter_upwards [] with t
    exact sq_nonneg _
  let t₁ : ℝ := 1 + 1 / (4 * z)
  let t₂ : ℝ := 1 + 1 / (2 * z)
  have ht₁ : t₁ ∈ Ioo (1 : ℝ) 2 := by
    have hzpos : 0 < z := by linarith
    constructor
    · dsimp [t₁]
      exact lt_add_of_pos_right _ (one_div_pos.mpr (mul_pos (by norm_num) hzpos))
    · dsimp [t₁]
      have hden : 1 < 4 * z := by nlinarith
      have hfrac : 1 / (4 * z) < 1 := (div_lt_one (by positivity)).2 hden
      linarith
  have ht₂ : t₂ ∈ Ioo (1 : ℝ) 2 := by
    have hzpos : 0 < z := by linarith
    constructor
    · dsimp [t₂]
      exact lt_add_of_pos_right _ (one_div_pos.mpr (mul_pos (by norm_num) hzpos))
    · dsimp [t₂]
      have hden : 1 < 2 * z := by nlinarith
      have hfrac : 1 / (2 * z) < 1 := (div_lt_one (by positivity)).2 hden
      linarith
  have hnotzero : ∃ t ∈ Ioo (1 : ℝ) 2, f t ≠ 0 := by
    by_contra h
    push Not at h
    have h₁zero : f t₁ = 0 := h t₁ ht₁
    have h₂zero : f t₂ = 0 := h t₂ ht₂
    have h₁cos : Real.cos (t₁ * z) = 1 := by
      dsimp [f] at h₁zero
      have hbase := sq_eq_zero_iff.mp h₁zero
      linarith
    have h₂cos : Real.cos (t₂ * z) = 1 := by
      dsimp [f] at h₂zero
      have hbase := sq_eq_zero_iff.mp h₂zero
      linarith
    obtain ⟨k₁, hk₁⟩ := (Real.cos_eq_one_iff (t₁ * z)).mp h₁cos
    obtain ⟨k₂, hk₂⟩ := (Real.cos_eq_one_iff (t₂ * z)).mp h₂cos
    have hdiff : ((k₂ - k₁ : ℤ) : ℝ) * (2 * Real.pi) = 1 / 4 := by
      calc
        ((k₂ - k₁ : ℤ) : ℝ) * (2 * Real.pi) =
            (k₂ : ℝ) * (2 * Real.pi) - (k₁ : ℝ) * (2 * Real.pi) := by
              rw [Int.cast_sub]
              ring
        _ = t₂ * z - t₁ * z := by rw [hk₂, hk₁]
        _ = 1 / 4 := by
          dsimp [t₁, t₂]
          field_simp
          ring
    have hk0 : k₂ - k₁ ≠ 0 := by
      intro hk
      rw [hk] at hdiff
      norm_num at hdiff
    have hk : k₂ - k₁ ≤ -1 ∨ 1 ≤ k₂ - k₁ := by
      rcases lt_or_gt_of_ne hk0 with hk' | hk'
      · left
        omega
      · right
        omega
    have hfactor : 0 < 2 * Real.pi := by nlinarith [Real.two_le_pi]
    rcases hk with hk | hk
    · have hk' : ((k₂ - k₁ : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hk
      have hle : ((k₂ - k₁ : ℤ) : ℝ) * (2 * Real.pi) ≤ -(2 * Real.pi) :=
        by simpa using mul_le_mul_of_nonneg_right hk' hfactor.le
      nlinarith [Real.two_le_pi]
    · have hk' : (1 : ℝ) ≤ ((k₂ - k₁ : ℤ) : ℝ) := by exact_mod_cast hk
      have hle : 2 * Real.pi ≤ ((k₂ - k₁ : ℤ) : ℝ) * (2 * Real.pi) :=
        by simpa using mul_le_mul_of_nonneg_right hk' hfactor.le
      nlinarith [Real.two_le_pi]
  rcases hnotzero with ⟨t₀, ht₀, hft₀⟩
  have hmeasure : 0 < volume (Function.support f ∩ Ioc (1 : ℝ) 2) := by
    have hopen : IsOpen (Function.support f ∩ Ioo (1 : ℝ) 2) :=
      hfcont.isOpen_support.inter isOpen_Ioo
    have hpos := IsOpen.measure_pos volume hopen ⟨t₀, hft₀, ht₀⟩
    exact hpos.trans_le (measure_mono (by
      intro t ht
      exact ⟨ht.1, Ioo_subset_Ioc_self ht.2⟩))
  have hnonneg' : 0 ≤ᵐ[volume.restrict (uIoc (1 : ℝ) 2)] f :=
    ae_mono Measure.restrict_le_self hnonneg
  have hpos :=
    (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hnonneg' hfi).2
      ⟨by norm_num, hmeasure⟩
  simpa [cosineSquareFrequencyAverage, f] using hpos

/-- Explicit antiderivative formula for the squared-defect frequency average. -/
theorem cosineSquareFrequencyAverage_eq_of_pos {z : ℝ} (hz : 0 < z) :
    cosineSquareFrequencyAverage z =
      3 / 2 - 2 * (Real.sin (2 * z) - Real.sin z) / z +
        (Real.sin (4 * z) - Real.sin (2 * z)) / (4 * z) := by
  have hcosGen {w : ℝ} (hw : w ≠ 0) :
      (∫ t in (1 : ℝ)..2, Real.cos (t * w)) =
        (Real.sin (2 * w) - Real.sin w) / w := by
    have hchange := intervalIntegral.integral_comp_mul_right
      (f := Real.cos) (a := (1 : ℝ)) (b := 2) (c := w) hw
    rw [integral_cos] at hchange
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hchange
  have hcos₁ := hcosGen hz.ne'
  have hcos₂ : (∫ t in (1 : ℝ)..2, Real.cos (2 * (t * z))) =
      (Real.sin (4 * z) - Real.sin (2 * z)) / (2 * z) := by
    have h2z : 0 < 2 * z := mul_pos (by norm_num) hz
    have hchange := hcosGen h2z.ne'
    have hfun : (fun t : ℝ => Real.cos (2 * (t * z))) =
        fun t => Real.cos (t * (2 * z)) := by
      funext t
      congr 1
      ring
    rw [hfun]
    have harg : 2 * (2 * z) = 4 * z := by ring
    rw [harg] at hchange
    exact hchange
  have hExpanded : (fun t : ℝ => (1 - Real.cos (t * z)) ^ 2) =
      fun t => (3 / 2 : ℝ) - 2 * Real.cos (t * z) +
        (1 / 2 : ℝ) * Real.cos (2 * (t * z)) := by
    funext t
    rw [Real.cos_two_mul]
    ring
  have hsub : IntervalIntegrable
      (fun t : ℝ => (3 / 2 : ℝ) - 2 * Real.cos (t * z)) volume 1 2 :=
    (by fun_prop : Continuous fun t : ℝ => (3 / 2 : ℝ) -
      2 * Real.cos (t * z)).intervalIntegrable 1 2
  have hadd : IntervalIntegrable
      (fun t : ℝ => (1 / 2 : ℝ) * Real.cos (2 * (t * z))) volume 1 2 :=
    (by fun_prop : Continuous fun t : ℝ => (1 / 2 : ℝ) *
      Real.cos (2 * (t * z))).intervalIntegrable 1 2
  have hconst : IntervalIntegrable (fun _ : ℝ => (3 / 2 : ℝ)) volume 1 2 :=
    intervalIntegrable_const
  have hcos : IntervalIntegrable
      (fun t : ℝ => 2 * Real.cos (t * z)) volume 1 2 :=
    (by fun_prop : Continuous fun t : ℝ => 2 * Real.cos (t * z)).intervalIntegrable 1 2
  rw [cosineSquareFrequencyAverage, hExpanded]
  rw [intervalIntegral.integral_add hsub hadd,
      intervalIntegral.integral_sub hconst hcos,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, hcos₁, hcos₂]
  field_simp
  ring

/-- The squared-defect frequency average converges to `3/2` at high
frequencies. -/
theorem tendsto_cosineSquareFrequencyAverage_atTop :
    Tendsto cosineSquareFrequencyAverage atTop (nhds (3 / 2 : ℝ)) := by
  have hterm (a b : ℝ) : Tendsto (fun z : ℝ => (a * Real.sin (b * z)) / z)
      atTop (nhds 0) := by
    have hbound : ∀ᶠ z : ℝ in atTop,
        ‖(a * Real.sin (b * z)) / z‖ ≤ |a| / z := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
      calc
        ‖(a * Real.sin (b * z)) / z‖ =
            |a * Real.sin (b * z)| / |z| := by rw [Real.norm_eq_abs, abs_div]
        _ = |a| * |Real.sin (b * z)| / z := by rw [abs_mul, abs_of_pos hz]
        _ ≤ |a| / z := by
          apply div_le_div_of_nonneg_right _ hz.le
          calc
            |a| * |Real.sin (b * z)| ≤ |a| * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg a)
            _ = |a| := by ring
    have hzero : Tendsto (fun z : ℝ => |a| / z) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
          Tendsto (fun z : ℝ => |a| * z⁻¹) atTop (nhds (|a| * 0)))
    have hnorm : Tendsto (fun z : ℝ => ‖(a * Real.sin (b * z)) / z‖)
        atTop (nhds 0) := by
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hzero
      filter_upwards [hbound] with z hz
      exact hz
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hnorm
  have hsin1 := hterm (-2) 2
  have hsin2 := hterm 2 1
  have hsin3 := hterm (1 / 4) 4
  have hsin4 := hterm (-(1 / 4)) 2
  have hsum0 : Tendsto (fun z : ℝ =>
      (-2 * Real.sin (2 * z)) / z + (2 * Real.sin z) / z +
        ((1 / 4 : ℝ) * Real.sin (4 * z)) / z +
        (-(1 / 4 : ℝ) * Real.sin (2 * z)) / z)
      atTop (nhds 0) := by
    simpa [add_assoc] using hsin1.add (hsin2.add (hsin3.add hsin4))
  have hsum : Tendsto (fun z : ℝ =>
      (3 / 2 : ℝ) + (-2 * Real.sin (2 * z)) / z +
        (2 * Real.sin z) / z + ((1 / 4 : ℝ) * Real.sin (4 * z)) / z +
        (-(1 / 4 : ℝ) * Real.sin (2 * z)) / z)
      atTop (nhds (3 / 2)) := by
    have hconst : Tendsto (fun _ : ℝ => (3 / 2 : ℝ)) atTop (nhds (3 / 2)) :=
      tendsto_const_nhds
    have h := hconst.add hsum0
    have hfun : (fun z : ℝ =>
        (3 / 2 : ℝ) + (-2 * Real.sin (2 * z)) / z +
          (2 * Real.sin z) / z + ((1 / 4 : ℝ) * Real.sin (4 * z)) / z +
          (-(1 / 4 : ℝ) * Real.sin (2 * z)) / z) =
        fun z => (3 / 2 : ℝ) +
          ((-2 * Real.sin (2 * z)) / z +
            ((2 * Real.sin z) / z +
              (((1 / 4 : ℝ) * Real.sin (4 * z)) / z +
                (-(1 / 4 : ℝ) * Real.sin (2 * z)) / z))) := by
      funext z
      ring
    rw [hfun]
    simpa only [add_assoc, add_zero] using h
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  rw [cosineSquareFrequencyAverage_eq_of_pos hz]
  field_simp
  ring

/-- A uniform positive lower bound for the averaged squared cosine defect on
all frequencies whose absolute value is at least one. -/
theorem exists_pos_cosineSquareFrequencyAverage_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℝ, 1 ≤ |z| →
      c ≤ cosineSquareFrequencyAverage z := by
  have hlarge : ∀ z : ℝ, 10 ≤ z → 1 ≤ cosineSquareFrequencyAverage z := by
    intro z hz
    have hzpos : 0 < z := by linarith
    rw [cosineSquareFrequencyAverage_eq_of_pos hzpos]
    have hsin12 : |Real.sin (2 * z) - Real.sin z| ≤ 2 := by
      calc
        |Real.sin (2 * z) - Real.sin z| ≤
            |Real.sin (2 * z)| + |Real.sin z| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
        _ = 2 := by norm_num
    have hsin24 : |Real.sin (4 * z) - Real.sin (2 * z)| ≤ 2 := by
      calc
        |Real.sin (4 * z) - Real.sin (2 * z)| ≤
            |Real.sin (4 * z)| + |Real.sin (2 * z)| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
        _ = 2 := by norm_num
    have he₁ : |2 * (Real.sin (2 * z) - Real.sin z) / z| ≤ 4 / z := by
      rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hzpos]
      calc
        2 * |Real.sin (2 * z) - Real.sin z| / z ≤ 2 * 2 / z :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsin12 (by norm_num)) hzpos.le
        _ = 4 / z := by ring
    have he₂ : |(Real.sin (4 * z) - Real.sin (2 * z)) / (4 * z)| ≤
        1 / (2 * z) := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 4 * z)]
      calc
        |Real.sin (4 * z) - Real.sin (2 * z)| / (4 * z) ≤ 2 / (4 * z) :=
          div_le_div_of_nonneg_right hsin24 (by positivity)
        _ = 1 / (2 * z) := by field_simp; ring
    have hlow : 3 / 2 - 4 / z - 1 / (2 * z) ≤
        3 / 2 - 2 * (Real.sin (2 * z) - Real.sin z) / z +
          (Real.sin (4 * z) - Real.sin (2 * z)) / (4 * z) := by
      have h₁ := abs_le.mp he₁
      have h₂ := abs_le.mp he₂
      linarith
    have hzbound : 4 / z ≤ 2 / 5 := by
      rw [div_le_iff₀ hzpos]
      nlinarith
    have htermBound : 1 / (2 * z) ≤ 1 / 20 := by
      have h2z : 0 < 2 * z := by positivity
      rw [div_le_iff₀ h2z]
      nlinarith
    linarith
  have hKcompact : IsCompact (Icc (1 : ℝ) 10) := isCompact_Icc
  obtain ⟨z₀, hz₀, hmin⟩ := hKcompact.exists_isMinOn
    ⟨1, by norm_num, by norm_num⟩
    continuous_cosineSquareFrequencyAverage.continuousOn
  have hmin' : ∀ y ∈ Icc (1 : ℝ) 10,
      cosineSquareFrequencyAverage z₀ ≤ cosineSquareFrequencyAverage y := by
    simpa only [IsMinOn, IsMinFilter, Filter.eventually_principal] using hmin
  have hc₀ : 0 < cosineSquareFrequencyAverage z₀ :=
    cosineSquareFrequencyAverage_pos_of_one_le hz₀.1
  refine ⟨min (cosineSquareFrequencyAverage z₀) 1, lt_min hc₀ (by norm_num), ?_⟩
  intro z hzabs
  by_cases hzpos : 0 ≤ z
  · have hz : 1 ≤ z := by simpa [abs_of_nonneg hzpos] using hzabs
    by_cases hlarge' : 10 ≤ z
    · exact (min_le_right _ _).trans (hlarge z hlarge')
    · have hzle : z ≤ 10 := le_of_not_ge hlarge'
      exact (min_le_left _ _).trans (hmin' z ⟨hz, hzle⟩)
  · have hzneg : z < 0 := lt_of_not_ge hzpos
    have hw : 1 ≤ -z := by simpa [abs_of_neg hzneg] using hzabs
    have hKneg : cosineSquareFrequencyAverage z =
        cosineSquareFrequencyAverage (-z) := by
      unfold cosineSquareFrequencyAverage
      apply intervalIntegral.integral_congr
      intro t ht
      simp [mul_neg, Real.cos_neg]
    rw [hKneg]
    by_cases hlarge' : 10 ≤ -z
    · exact (min_le_right _ _).trans (hlarge (-z) hlarge')
    · have hwle : -z ≤ 10 := le_of_not_ge hlarge'
      exact (min_le_left _ _).trans (hmin' (-z) ⟨hw, hwle⟩)

end Analysis.Fourier.CosineTauberian


end
