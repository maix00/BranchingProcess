/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Attraction.Norming.Inverse
public import Probability.Distributions.Stable.Attraction.NormingRatios.Tauberian
public import Probability.Distributions.DomainOfAttraction.Centering

/-!
# Sublinear stable normalizations above index one

For stable index greater than one, the regularly varying truncated second
moment grows slower than linearly. Potter's bound therefore shows that the
stable time scale divided by space tends to infinity. Along a stable norming,
this implies that the spatial normalization is sublinear in the number of
steps.
-/

open Filter MeasureTheory

@[expose] public section

namespace ProbabilityTheory

/-- Above index one, the stable time scale per unit space diverges. The proof
uses the monotone Potter upper bound for the truncated second moment, whose
regular-variation index is `2 - α < 1`. -/
theorem stableScaleTime_div_self_tendsto_atTop_of_stableSlowVariation
    {α : ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hα₁ : 1 < α) (hα₂ : α < 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν)) :
    Tendsto (fun u : ℝ => stableScaleTime α ν u / u) atTop atTop := by
  let β : ℝ := 2 - α
  let ε : ℝ := (1 - β) / 2
  let p : ℝ := β + ε
  let V : ℝ → ℝ := truncatedSecondMoment ν
  have hβ₀ : 0 ≤ β := by dsimp [β]; linarith
  have hβ₁ : β < 1 := by dsimp [β]; linarith
  have hε : 0 < ε := by dsimp [ε, β]; linarith
  have hp₁ : p < 1 := by dsimp [p, ε]; linarith
  have hVreg : Asymptotics.IsRegularlyVaryingAtTop V β := by
    simpa [V, β] using
      truncatedSecondMoment_isRegularlyVarying_of_stableSlowVariation hslow
  have hVmono : Asymptotics.IsEventuallyMonotoneAtTop V := by
    simpa [V] using truncatedSecondMoment_isEventuallyMonotone ν
  obtain ⟨R₀, hR₀, hpotter⟩ := hVreg.exists_potter_upper_bound hVmono hβ₀ hε
  obtain ⟨Rpos, hRpos⟩ := eventually_atTop.1 hVreg.eventually_pos
  let R : ℝ := max R₀ (max Rpos 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hRpot : R₀ ≤ R := by dsimp [R]; exact le_max_left _ _
  have hRpositive : Rpos ≤ R := by
    dsimp [R]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hV_R : 0 < V R := hRpos R hRpositive
  have hVRV : ∀ ⦃u : ℝ⦄, R ≤ u → V u / V R ≤
      2 ^ p * (u / R) ^ p := by
    intro u hu
    exact hpotter hRpot hu
  have hbound : ∀ᶠ u : ℝ in atTop,
      (2 ^ p * V R)⁻¹ * R ^ p * u ^ (1 - p) ≤
        stableScaleTime α ν u / u := by
    filter_upwards [eventually_ge_atTop R, hVreg.eventually_pos,
      eventually_gt_atTop (0 : ℝ)] with u hu hVu hupos
    have hVu' : 0 < V u := hVu
    have hpot := hVRV hu
    have hVubound : V u ≤ V R * (2 ^ p * (u / R) ^ p) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_le_iff₀ hV_R).mp hpot
    have hscaleEq : stableScaleTime α ν u / u = u / V u := by
      rw [stableScaleTime_eq_square_div_truncatedSecondMoment hupos
        (by simpa [V] using hVu')]
      simp only [V]
      field_simp [ne_of_gt hupos]
    rw [hscaleEq]
    have hinv : (V R * (2 ^ p * (u / R) ^ p))⁻¹ ≤ (V u)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hVu' hVubound
    have hlower : (V R * (2 ^ p * (u / R) ^ p))⁻¹ * u ≤ u / V u := by
      calc
        (V R * (2 ^ p * (u / R) ^ p))⁻¹ * u ≤ (V u)⁻¹ * u :=
          mul_le_mul_of_nonneg_right hinv hupos.le
        _ = u / V u := by rw [div_eq_mul_inv]; ring
    have hrewrite :
        (V R * (2 ^ p * (u / R) ^ p))⁻¹ * u =
          (2 ^ p * V R)⁻¹ * R ^ p * u ^ (1 - p) := by
      have hRpos : 0 < R := hR
      have huR : 0 < u / R := div_pos hupos hRpos
      have hpow : (u / R) ^ p = u ^ p / R ^ p := by
        rw [div_eq_mul_inv, Real.mul_rpow hupos.le (inv_nonneg.mpr hRpos.le)]
        rw [Real.inv_rpow hRpos.le]
        ring
      rw [hpow]
      have hRpow : R ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hRpos p)
      have huPow : u ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hupos p)
      field_simp [hRpow, huPow]
      calc
        u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
        _ = u ^ p * u ^ (1 - p) := by
          rw [← Real.rpow_add hupos]
          congr 1
          ring
    rw [← hrewrite]
    exact hlower
  have hpow : Tendsto (fun u : ℝ => u ^ (1 - p)) atTop atTop :=
    tendsto_rpow_atTop (by dsimp [p, ε, β]; linarith)
  have hconst : 0 < (2 ^ p * V R)⁻¹ * R ^ p := by positivity
  have hlowerTop : Tendsto
      (fun u : ℝ => (2 ^ p * V R)⁻¹ * R ^ p * u ^ (1 - p)) atTop atTop :=
    (hpow.const_mul_atTop hconst)
  exact tendsto_atTop_mono' atTop hbound hlowerTop

/-- The normalization in a stable domain with index in `(1, 2)` is
sublinear in the number of increments, once `L*` is slowly varying. -/
theorem IsStableNorming.tendsto_normalization_div_nat_of_index_gt_one
    {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hα₁ : 1 < α) (hα₂ : α < 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν)) :
    Tendsto (fun n : ℕ => normalization n / (n : ℝ)) atTop (nhds 0) := by
  have hspace := hnorm.2.1
  have hclock : Tendsto (fun n : ℕ =>
      stableScaleTime α ν (normalization n) / (n : ℝ)) atTop (nhds 1) := by
    simpa only [stableScaleTime] using hnorm.2.2
  have hclockSpace : Tendsto (fun n : ℕ =>
      stableScaleTime α ν (normalization n) / normalization n) atTop atTop :=
    stableScaleTime_div_self_tendsto_atTop_of_stableSlowVariation
      hα₁ hα₂ hslow |>.comp hspace
  have hclockSpacePos : ∀ᶠ n : ℕ in atTop,
      0 < stableScaleTime α ν (normalization n) / normalization n :=
    hclockSpace.eventually (eventually_gt_atTop 0)
  have hBPos : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    (eventually_gt_atTop (0 : ℕ)).mono fun n hn => hnorm.1 n hn
  have hreciprocal : Tendsto (fun n : ℕ =>
      (stableScaleTime α ν (normalization n) / normalization n)⁻¹)
      atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp hclockSpace
  have hproduct := hreciprocal.mul hclock
  have heq : (fun n : ℕ =>
      (stableScaleTime α ν (normalization n) / normalization n)⁻¹ *
        (stableScaleTime α ν (normalization n) / (n : ℝ))) =ᶠ[atTop]
      fun n => normalization n / (n : ℝ) := by
    filter_upwards [hBPos, hspace.eventually (eventually_gt_atTop 0),
      hclockSpacePos] with n hB hn hK
    have hKne : stableScaleTime α ν (normalization n) ≠ 0 := by
      intro hzero
      rw [hzero, zero_div] at hK
      exact (lt_irrefl 0) hK
    field_simp [ne_of_gt hB, ne_of_gt hn, hKne]
  simpa using hproduct.congr' heq

/-- Tail regular variation supplies the slowly varying truncated-moment
factor needed to conclude sublinearity from the stable norming relation. -/
theorem IsStableNorming.tendsto_normalization_div_nat_of_index_gt_one_of_regularlyVaryingTail
    {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hα₁ : 1 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α)) :
    Tendsto (fun n : ℕ => normalization n / (n : ℝ)) atTop (nhds 0) := by
  have hslow := stableSlowVariation_isSlowlyVarying_of_regularlyVaryingTail
    (ν := ν) (α := α) (by linarith : 0 < α) hα₂ htail
  exact hnorm.tendsto_normalization_div_nat_of_index_gt_one hα₁ hα₂ hslow

/-- In an uncentered scalar domain of attraction to a stable law of index in
`(1, 2)`, finite first moment forces the increment mean to be zero. The
regularly varying tail needed for the sublinear normalization is derived from
the scalar attraction hypothesis by the stable Tauberian theorem; the first
moment assumption is kept explicit here. -/
theorem IsInDomainOfAttractionAlong.integral_eq_zero_of_index_gt_one
    {α : ℝ} {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {normalization : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hlimit : IsAlphaStable α μ)
    (hnorm : IsStableNorming α ν normalization)
    (hα₁ : 1 < α) (hα₂ : α < 2)
    (hint : Integrable (fun x : ℝ => x) ν) :
    (∫ x : ℝ, x ∂ν) = 0 := by
  have htail := hDOA.isRegularlyVarying_twoSidedTail hlimit (by linarith) hα₂
  have hsublinear := hnorm.tendsto_normalization_div_nat_of_index_gt_one_of_regularlyVaryingTail
    hα₁ hα₂ htail
  exact integral_eq_zero_of_uncenteredAttraction_of_sublinearNormalization
    hDOA hint hsublinear

end ProbabilityTheory

end
