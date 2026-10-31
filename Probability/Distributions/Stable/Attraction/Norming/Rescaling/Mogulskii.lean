/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Attraction.Norming.Rescaling.Compatibility
public import Probability.Distributions.Stable.Attraction.NormingRatios.Index
import Probability.Distributions.DomainOfAttraction.Normalization
import all Probability.Distributions.Stable.Attraction.Norming.Rescaling.Lemmas.Index
import Analysis.Fourier.CosineTauberian.Mellin

/-!
# Mogulskii-compatible stable norming

## Public declarations

For an attraction normalization $a_n$ with stable time constant $d>0$, this
result gives an index sequence $m_n$ and a source normalization $a'_n$ such
that $m_n/n\to d^{-1}$, $a'_n=a_{m_n}$ eventually, and
$a_n/a'_n\to d^{1/\alpha}$. The limiting law is rescaled by
$x\mapsto d^{1/\alpha}x$, and the centering sequence is preserved.

- `ProbabilityTheory.IsInDomainOfAttractionAlong.exists_source_stable_norming`:
  from attraction along an arbitrary normalization, obtain a reindexed
  normalization with unit stable time constant and the corresponding rescaled
  limiting law.

The internal index sequence matches the time constant used in A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; see also the English
translation, “Small Deviations in a Space of Trajectories,” *Theory of
Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory
open Analysis.Fourier.CosineTauberian
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- Reindex a raw stable-domain normalization at its asymptotic inverse time
constant. The new sequence is a stable norming with unit time constant, the
limiting law is rescaled consistently, and the original centering sequence is
preserved. -/
theorem IsInDomainOfAttractionAlong.exists_source_stable_norming
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {normalization center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure normalization center)
    (hα₂ : α < 2) :
    ∃ d : ℝ, 0 < d ∧
      ∃ m : ℕ → ℕ,
        (∀ n, 0 < m n) ∧
        Tendsto (fun n => (m n : ℝ) / (n : ℝ)) atTop (nhds d⁻¹) ∧
      ∃ sourceNormalization : ℕ → ℝ,
        IsStableNorming α ν sourceNormalization ∧
        sourceNormalization =ᶠ[atTop] (fun n => normalization (m n)) ∧
        Tendsto (fun n => normalization n / sourceNormalization n) atTop
          (nhds (d ^ (1 / α))) ∧
      ∃ hmap : IsProbabilityMeasure
          (limit.map fun x => d ^ (1 / α) * x),
          IsAlphaStable α (limit.map fun x => d ^ (1 / α) * x) ∧
          @IsInDomainOfAttractionAlong ν
            (limit.map fun x => d ^ (1 / α) * x)
            inferInstance hmap sourceNormalization center := by
  letI : IsProbabilityMeasure limit := hlimit.isProbabilityMeasure
  have hα₀ : 0 < α := hlimit.alpha_pos
  obtain ⟨c, hc, htime⟩ :=
    h.exists_pos_tendsto_stableScaleTime_div hlimit hα₂
  let d : ℝ := stableNormingTimeConstant α c
  let m : ℕ → ℕ := stableNormingIndex d
  have hd : 0 < d := by
    dsimp [d, stableNormingTimeConstant]
    exact div_pos (mul_pos (by linarith)
      (cosineTauberianCosineMoment_pos hα₀ hα₂)) hc
  have hmratio : Tendsto (fun n => (m n : ℝ) / (n : ℝ)) atTop
      (nhds d⁻¹) := by
    simpa [m] using stableNormingIndex_ratio hd
  have hm : Tendsto m atTop atTop := by
    simpa [m] using stableNormingIndex_tendsto_atTop hd
  have htimeD : Tendsto
      (fun n => stableScaleTime α ν (normalization n) / (n : ℝ))
      atTop (nhds d) := by
    simpa [d, stableNormingTimeConstant] using htime
  have htimeM : Tendsto
      (fun n => stableScaleTime α ν (normalization (m n)) / (m n : ℝ))
      atTop (nhds d) := htimeD.comp hm
  have htimeNormalized : Tendsto
      (fun n => stableScaleTime α ν (normalization (m n)) / (n : ℝ))
      atTop (nhds 1) := by
    have hprod := htimeM.mul hmratio
    have heq : (fun n =>
        stableScaleTime α ν (normalization (m n)) / (m n : ℝ) *
          ((m n : ℝ) / (n : ℝ))) =ᶠ[atTop]
        fun n => stableScaleTime α ν (normalization (m n)) / (n : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ),
        (hm.eventually_gt_atTop 0)] with n hn hmn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hmR : (m n : ℝ) ≠ 0 := by exact_mod_cast hmn.ne'
      field_simp
    have hprod' := hprod.congr' heq
    have hdconst : d * d⁻¹ = (1 : ℝ) := mul_inv_cancel₀ hd.ne'
    simpa [hdconst] using hprod'
  have hrawRatio := h.tendsto_norming_ratio hlimit m d⁻¹ (inv_pos.mpr hd) hmratio
  have hscaleLimit : 0 < Real.rpow d⁻¹ α⁻¹ :=
    Real.rpow_pos_of_pos (inv_pos.mpr hd) _
  have hscaleInv : Tendsto
      (fun n => normalization n / normalization (m n)) atTop
        (nhds ((Real.rpow d⁻¹ α⁻¹)⁻¹)) := by
    have hinv := hrawRatio.inv₀ hscaleLimit.ne'
    have heq : (fun n => (normalization (m n) / normalization n)⁻¹) =ᶠ[atTop]
        fun n => normalization n / normalization (m n) := by
      filter_upwards [h.eventually_scale_pos, hm.eventually h.eventually_scale_pos] with n hn hmn
      simp [div_eq_mul_inv]
    exact hinv.congr' heq
  have hratioStable : Tendsto
      (fun n => normalization n / normalization (m n)) atTop
        (nhds (d ^ (1 / α))) := by
    have heq : (Real.rpow d⁻¹ α⁻¹)⁻¹ = d ^ (1 / α) := by
      have hpow : d⁻¹ ^ α⁻¹ = (d ^ α⁻¹)⁻¹ :=
        Real.inv_rpow (le_of_lt hd) α⁻¹
      calc
        (Real.rpow d⁻¹ α⁻¹)⁻¹ = (d⁻¹ ^ α⁻¹)⁻¹ := rfl
        _ = d ^ α⁻¹ := by rw [hpow, inv_inv]
        _ = d ^ (1 / α) := by rw [one_div]
    rw [heq] at hscaleInv
    exact hscaleInv
  have hnormEventualPos : ∀ᶠ n : ℕ in atTop,
      0 < normalization (m n) := hm.eventually h.eventually_scale_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnormEventualPos
  let sourceNormalization : ℕ → ℝ := fun n =>
    if N ≤ n then normalization (m n) else 1
  have hsourcePos : ∀ n, 0 < sourceNormalization n := by
    intro n
    by_cases hNn : N ≤ n
    · simpa [sourceNormalization, hNn] using hN n hNn
    · simp [sourceNormalization, hNn]
  have hsourceEq : sourceNormalization =ᶠ[atTop]
      fun n => normalization (m n) := by
    filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    simp [sourceNormalization, hn]
  have hsourceTop : Tendsto sourceNormalization atTop atTop := by
    have hrawTop : Tendsto (fun n => normalization (m n)) atTop atTop :=
      (h.tendsto_scale_atTop hlimit).comp hm
    exact hrawTop.congr' hsourceEq.symm
  have hsourceTime : Tendsto
      (fun n => stableScaleTime α ν (sourceNormalization n) / (n : ℝ))
      atTop (nhds 1) := by
    exact htimeNormalized.congr' (by
      filter_upwards [hsourceEq] with n hn
      rw [hn])
  have hnorm : IsStableNorming α ν sourceNormalization := by
    refine ⟨fun n _ => hsourcePos n, hsourceTop, ?_⟩
    simpa [stableScaleTime] using hsourceTime
  have hmPos : ∀ n, 0 < m n := by
    intro n
    dsimp [m, stableNormingIndex]
    omega
  have hr : 0 < d ^ (1 / α) := Real.rpow_pos_of_pos hd _
  have hratioStableSource : Tendsto
      (fun n => normalization n / sourceNormalization n) atTop
        (nhds (d ^ (1 / α))) := by
    have heq : (fun n => normalization n / sourceNormalization n) =ᶠ[atTop]
        fun n => normalization n / normalization (m n) := by
      filter_upwards [hsourceEq] with n hn
      rw [hn]
    exact hratioStable.congr' heq.symm
  have hsourcePosEvent : ∀ᶠ n : ℕ in atTop, 0 < sourceNormalization n := by
    filter_upwards [] with n
    exact hsourcePos n
  have hdoa := h.changeNormalization hsourcePosEvent hratioStableSource
  have hstable : IsAlphaStable α (limit.map fun x => d ^ (1 / α) * x) := by
    exact hlimit.map_mul (d ^ (1 / α)) (ne_of_gt hr)
  letI hmap : IsProbabilityMeasure
      (limit.map fun x => d ^ (1 / α) * x) := hstable.isProbabilityMeasure
  have hdoa' : @IsInDomainOfAttractionAlong ν
      (limit.map fun x => d ^ (1 / α) * x) inferInstance hmap
      sourceNormalization center := by
    simpa only [Function.comp_def] using hdoa
  exact ⟨d, hd, m, hmPos, hmratio, sourceNormalization, hnorm, hsourceEq,
    hratioStableSource, hmap, hstable, hdoa'⟩


end ProbabilityTheory

end
