module

public import Analysis.Fourier.CosineTauberian.Mellin
public import Probability.Distributions.Stable.Attraction.CharacteristicFunction
public import Probability.Distributions.Stable.Attraction.Norming
public import Probability.Distributions.Stable.Attraction.NormingRatios.Tauberian
public import Probability.Distributions.Stable.Scaling

/-!
# Compatibility of stable norming constants

This file connects the one-step characteristic-function defect and truncated
second-moment asymptotics to the normalization sequence used in a stable
domain-of-attraction limit.
-/

open Filter MeasureTheory
open scoped Topology
open Analysis.Fourier.CosineTauberian

@[expose] public section

namespace ProbabilityTheory

/-- The time-scale compatibility constant determined by the stable limit's
characteristic-function coefficient. -/
noncomputable def stableNormingTimeConstant (α c : ℝ) : ℝ :=
  (2 - α) * cosineTauberianCosineMoment α / c

/-- The spatial factor that changes a domain-of-attraction normalization to
the convention `κν (B n) / n → 1`. -/
noncomputable def stableNormingSpatialFactor (α c : ℝ) : ℝ :=
  Real.rpow (stableNormingTimeConstant α c)⁻¹ α⁻¹

theorem stableNormingTimeConstant_pos {α c : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2) (hc : 0 < c) :
    0 < stableNormingTimeConstant α c := by
  unfold stableNormingTimeConstant
  exact div_pos (mul_pos (by linarith)
    (cosineTauberianCosineMoment_pos hα₀ hα₂)) hc

theorem stableNormingSpatialFactor_pos {α c : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2) (hc : 0 < c) :
    0 < stableNormingSpatialFactor α c := by
  exact Real.rpow_pos_of_pos
    (inv_pos.mpr (stableNormingTimeConstant_pos hα₀ hα₂ hc)) _

theorem stableNormingSpatialFactor_rpow {α c : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2) (hc : 0 < c) :
    (stableNormingSpatialFactor α c) ^ α =
      (stableNormingTimeConstant α c)⁻¹ := by
  have hα : α ≠ 0 := hα₀.ne'
  have hd : 0 < stableNormingTimeConstant α c :=
    stableNormingTimeConstant_pos hα₀ hα₂ hc
  unfold stableNormingSpatialFactor
  calc
    Real.rpow (Real.rpow (stableNormingTimeConstant α c)⁻¹ α⁻¹) α =
        Real.rpow (stableNormingTimeConstant α c)⁻¹ (α⁻¹ * α) := by
          exact (Real.rpow_mul (inv_pos.mpr hd).le α⁻¹ α).symm
    _ = Real.rpow (stableNormingTimeConstant α c)⁻¹ 1 := by
          rw [inv_mul_cancel₀ hα]
    _ = (stableNormingTimeConstant α c)⁻¹ := Real.rpow_one _

set_option linter.style.haveILetI false in
/-- The inverse stable scale evaluated on a domain-of-attraction normalization
has a finite, strictly positive asymptotic constant. The proof combines the
truncated-second-moment/characteristic-defect ratio with the one-step defect
limit supplied by stable attraction. -/
theorem IsInDomainOfAttractionAlong.exists_pos_tendsto_stableScaleTime_div
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    (hα₂ : α < 2) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => stableScaleTime α ν (scale n) / (n : ℝ)) atTop
        (nhds ((2 - α) * cosineTauberianCosineMoment α / c)) := by
  letI : IsProbabilityMeasure limit := hlimit.isProbabilityMeasure
  obtain ⟨c, hc, _, hdefect⟩ :=
    h.exists_pos_tendsto_log_norm_charFun_and_norm_defect hlimit
  let J : ℝ := cosineTauberianCosineMoment α
  let ψ : ℝ → ℝ := fun x => 1 - ‖charFun ν x⁻¹‖ ^ 2
  let V : ℝ → ℝ := truncatedSecondMoment ν
  let q : ℕ → ℝ := fun n => (n : ℝ) * V (scale n) / (scale n) ^ 2
  have hα₀ : 0 < α := hlimit.alpha_pos
  have hJ : 0 < J := by
    dsimp [J]
    exact cosineTauberianCosineMoment_pos hα₀ hα₂
  have htimeDefect : Tendsto (fun x : ℝ => V x / (x ^ 2 * ψ x)) atTop
      (nhds (1 / (2 * (2 - α) * J))) := by
    simpa [V, ψ, J] using
      h.tendsto_truncatedSecondMoment_div_scaledCosineDefect
        hlimit hα₀ hα₂
  have htimeDefectSeq : Tendsto
      (fun n : ℕ => V (scale n) / ((scale n) ^ 2 * ψ (scale n))) atTop
      (nhds (1 / (2 * (2 - α) * J)) ) := by
    exact htimeDefect.comp (h.tendsto_scale_atTop hlimit)
  have hdefectSeq : Tendsto (fun n : ℕ => (n : ℝ) * ψ (scale n)) atTop
      (nhds (2 * c)) := by
    have h' := hdefect 1
    simpa [ψ, abs_one] using h'
  have hproduct := htimeDefectSeq.mul hdefectSeq
  have hconst : (1 / (2 * (2 - α) * J)) * (2 * c) =
      c / ((2 - α) * J) := by
    have hden : 0 < (2 - α) * J := mul_pos (by linarith) hJ
    field_simp [ne_of_gt hden]
  have hq : Tendsto q atTop (nhds (c / ((2 - α) * J))) := by
    have heq : (fun n : ℕ =>
        V (scale n) / ((scale n) ^ 2 * ψ (scale n)) *
          ((n : ℝ) * ψ (scale n))) =ᶠ[atTop] q := by
      have hscalePos := h.eventually_scale_pos
      have hnPos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
        exact (eventually_gt_atTop 0).mono fun n hn => by exact_mod_cast hn
      have hpsiPos : ∀ᶠ n : ℕ in atTop, 0 < ψ (scale n) := by
        filter_upwards [hdefectSeq.eventually (Ioi_mem_nhds (by positivity)), hnPos]
          with n hprod hn
        exact (mul_pos_iff_of_pos_left hn).mp hprod
      filter_upwards [hscalePos, hnPos, hpsiPos] with n hscale hn hψ
      dsimp [q]
      field_simp [ne_of_gt hscale, ne_of_gt hψ]
    have hprod' := hproduct.congr' heq
    rw [hconst] at hprod'
    simpa [q] using hprod'
  have hqLimitPos : 0 < c / ((2 - α) * J) :=
    div_pos hc (mul_pos (by linarith) hJ)
  have hqPos : ∀ᶠ n : ℕ in atTop, 0 < q n :=
    hq.eventually (Ioi_mem_nhds hqLimitPos)
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := h.eventually_scale_pos
  have hnPos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    exact (eventually_gt_atTop 0).mono fun n hn => by exact_mod_cast hn
  have hVne : ∀ᶠ n : ℕ in atTop, V (scale n) ≠ 0 := by
    filter_upwards [hqPos] with n hn
    intro hzero
    have : q n = 0 := by simp [q, V, hzero]
    rw [this] at hn
    exact (lt_irrefl 0 hn)
  have htimeEq : (fun n : ℕ => stableScaleTime α ν (scale n) / (n : ℝ)) =ᶠ[atTop]
      fun n => (q n)⁻¹ := by
    filter_upwards [hscalePos, hnPos, hVne] with n hscale hn hV
    have hpow : (scale n) ^ (α - 2) = (scale n) ^ α / (scale n) ^ 2 := by
      calc
        (scale n) ^ (α - 2) = (scale n) ^ α / (scale n) ^ (2 : ℝ) :=
          Real.rpow_sub hscale α 2
        _ = (scale n) ^ α / (scale n) ^ 2 :=
          congrArg (fun z : ℝ => (scale n) ^ α / z)
            (Real.rpow_natCast (scale n) 2)
    have hκ : stableScaleTime α ν (scale n) =
        (scale n) ^ 2 / V (scale n) := by
      rw [stableScaleTime, stableSlowVariation, hpow]
      have hpowPos : 0 < (scale n) ^ α := Real.rpow_pos_of_pos hscale α
      field_simp [ne_of_gt hpowPos, hV, hscale.ne', V]
      rfl
    rw [hκ]
    dsimp [q]
    have hnNe : (n : ℝ) ≠ 0 := ne_of_gt hn
    field_simp [hnNe, hscale.ne', hV]
  have hinv := hq.inv₀ (ne_of_gt hqLimitPos)
  have hresult : Tendsto
      (fun n : ℕ => stableScaleTime α ν (scale n) / (n : ℝ)) atTop
      (nhds (((c / ((2 - α) * J))⁻¹))) := by
    exact hinv.congr' htimeEq.symm
  have hfinal : (c / ((2 - α) * J))⁻¹ = (2 - α) * J / c := by
    field_simp [ne_of_gt hc, ne_of_gt hJ, ne_of_gt (show 0 < 2 - α by linarith)]
  exact ⟨c, hc, by simpa [J, hfinal] using hresult⟩

set_option linter.style.haveILetI false in
/-- A stable domain-of-attraction normalization can be rescaled so that the
inverse stable scale satisfies `κν (B n) / n → 1`. The limiting stable law is
rescaled at the same time. A finite prefix is repaired to keep the resulting
norming positive at every positive index, as required by `IsStableNorming`. -/
theorem IsInDomainOfAttractionAlong.exists_stableNorming_rescaling
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    (hα₂ : α < 2) :
    ∃ c : ℝ, 0 < c ∧
      ∃ normalizedScale : ℕ → ℝ,
        IsStableNorming α ν normalizedScale ∧
        ∃ hmap : IsProbabilityMeasure
          (limit.map fun x => (stableNormingSpatialFactor α c)⁻¹ * x),
          IsAlphaStable α
            (limit.map fun x => (stableNormingSpatialFactor α c)⁻¹ * x) ∧
          @IsInDomainOfAttractionAlong ν
            (limit.map fun x => (stableNormingSpatialFactor α c)⁻¹ * x)
            inferInstance hmap normalizedScale center := by
  letI : IsProbabilityMeasure limit := hlimit.isProbabilityMeasure
  obtain ⟨c, hc, htime⟩ :=
    h.exists_pos_tendsto_stableScaleTime_div hlimit hα₂
  let J : ℝ := cosineTauberianCosineMoment α
  let d : ℝ := stableNormingTimeConstant α c
  let factor : ℝ := stableNormingSpatialFactor α c
  have hα₀ : 0 < α := hlimit.alpha_pos
  have hJ : 0 < J := by
    dsimp [J]
    exact cosineTauberianCosineMoment_pos hα₀ hα₂
  have hd : 0 < d := stableNormingTimeConstant_pos hα₀ hα₂ hc
  have hfactor : 0 < factor := stableNormingSpatialFactor_pos hα₀ hα₂ hc
  have hfactorpow : factor ^ α = d⁻¹ := by
    simpa [factor, d] using stableNormingSpatialFactor_rpow hα₀ hα₂ hc
  have hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν) :=
    h.isSlowlyVarying_stableSlowVariation hlimit hα₀ hα₂
  have hκreg : Asymptotics.IsRegularlyVaryingAtTop
      (stableScaleTime α ν) α :=
    stableScaleTime_isRegularlyVaryingAtTop hslow
  have hκseqPos : ∀ᶠ n : ℕ in atTop,
      0 < stableScaleTime α ν (scale n) :=
    (h.tendsto_scale_atTop hlimit).eventually hκreg.eventually_pos
  have hκratio : Tendsto
      (fun n : ℕ => stableScaleTime α ν (factor * scale n) /
        stableScaleTime α ν (scale n)) atTop (nhds (factor ^ α)) := by
    exact (hκreg.ratio_tendsto hfactor).comp (h.tendsto_scale_atTop hlimit)
  have htimeD : Tendsto
      (fun n : ℕ => stableScaleTime α ν (scale n) / (n : ℝ)) atTop
      (nhds d) := by
    simpa [d, stableNormingTimeConstant] using htime
  have htime' : Tendsto
      (fun n : ℕ => stableScaleTime α ν (factor * scale n) / (n : ℝ)) atTop
      (nhds 1) := by
    have hprod := hκratio.mul htimeD
    have hconst : factor ^ α * d = 1 := by
      rw [hfactorpow]
      exact inv_mul_cancel₀ hd.ne'
    have heq : (fun n : ℕ =>
        stableScaleTime α ν (factor * scale n) /
          stableScaleTime α ν (scale n) *
          (stableScaleTime α ν (scale n) / (n : ℝ))) =ᶠ[atTop]
        fun n => stableScaleTime α ν (factor * scale n) / (n : ℝ) := by
      filter_upwards [hκseqPos, eventually_gt_atTop 0] with n hκpos hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp [hκpos.ne', hnR]
    have hprod' := hprod.congr' heq
    rw [hconst] at hprod'
    simpa [d] using hprod'
  obtain ⟨N, hN⟩ := (eventually_atTop.1 h.eventually_scale_pos)
  let normalizedScale : ℕ → ℝ := fun n =>
    if N ≤ n then factor * scale n else 1
  have hnormalizedPos : ∀ n, 0 < n → 0 < normalizedScale n := by
    intro n hn
    dsimp [normalizedScale]
    split_ifs with hNn
    · exact mul_pos hfactor (hN n hNn)
    · norm_num
  have hnormalizedEq : (fun n => normalizedScale n) =ᶠ[atTop]
      fun n => factor * scale n := by
    filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    simp [normalizedScale, hn]
  have hnormalizedTop : Tendsto normalizedScale atTop atTop := by
    have hscaledTop : Tendsto (fun n => factor * scale n) atTop atTop :=
      (h.tendsto_scale_atTop hlimit).const_mul_atTop hfactor
    exact hscaledTop.congr' hnormalizedEq.symm
  have hnormalizedTime : Tendsto
      (fun n => stableScaleTime α ν (normalizedScale n) / (n : ℝ)) atTop
      (nhds 1) := by
    exact htime'.congr' (by
      filter_upwards [hnormalizedEq] with n hn
      rw [hn])
  have hnorming : IsStableNorming α ν normalizedScale := by
    refine ⟨hnormalizedPos, hnormalizedTop, ?_⟩
    simpa [stableScaleTime] using hnormalizedTime
  have hlimit' : IsAlphaStable α
      (limit.map fun x => factor⁻¹ * x) :=
    hlimit.map_mul factor⁻¹ (inv_pos.mpr hfactor)
  letI : IsProbabilityMeasure (limit.map fun x => factor⁻¹ * x) :=
    hlimit'.isProbabilityMeasure
  have hrescaled := h.rescale factor⁻¹ (inv_pos.mpr hfactor)
  have hrescaledScaleEq : (fun n => (factor⁻¹)⁻¹ * scale n) =ᶠ[atTop]
      fun n => factor * scale n := by
    filter_upwards [] with n
    simp
  have hrescaledScale : TendstoInDistribution
      (fun n => normalizedIidSum (fun k => (factor⁻¹)⁻¹ * scale k) center n)
      atTop id (fun _ => iidSequenceLaw ν)
      (limit.map fun x => factor⁻¹ * x) := by
    exact hrescaled.2
  have hnormalizedAemeasurable : ∀ n,
      AEMeasurable (normalizedIidSum normalizedScale center n)
        (iidSequenceLaw ν) := by
    intro n
    exact (normalizedIidSum_measurable normalizedScale center n).aemeasurable
  have hnormalizedConvergence : TendstoInDistribution
      (normalizedIidSum normalizedScale center) atTop id
      (fun _ => iidSequenceLaw ν) (limit.map fun x => factor⁻¹ * x) := by
    apply hrescaledScale.congr_eventually ?_ hnormalizedAemeasurable
    filter_upwards [hnormalizedEq, hrescaledScaleEq] with n hnorm hrescale
    filter_upwards [] with ω
    simp only [normalizedIidSum]
    rw [hnorm, hrescale]
  have hmap : IsProbabilityMeasure (limit.map fun x => factor⁻¹ * x) :=
    hlimit'.isProbabilityMeasure
  have hdomain : @IsInDomainOfAttractionAlong ν
      (limit.map fun x => factor⁻¹ * x) inferInstance hmap normalizedScale center :=
    ⟨by
      filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
      simpa [normalizedScale, hn] using mul_pos hfactor (hN n hn),
      hnormalizedConvergence⟩
  exact ⟨c, hc, normalizedScale, hnorming, hmap, hlimit', hdomain⟩

end ProbabilityTheory

end
