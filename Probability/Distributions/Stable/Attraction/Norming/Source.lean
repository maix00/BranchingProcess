/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.BlockScale
public import Probability.Distributions.Stable.Attraction.Norming.Compatibility
public import Probability.Distributions.Stable.Attraction.NormingRatios.Index
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.Centering

/-!
# Source-compatible stable norming

This file converts a stable domain-of-attraction normalization to the time
constant used by the source small-deviation theorem. The index-one sine
centering is transferred by reindexing the normalization, rather than by
assuming a scale-invariance property of the sine transform.
-/

open Filter MeasureTheory
open scoped Topology
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

@[expose] public section

namespace ProbabilityTheory

/-- A deterministic convergent sequence, viewed as constant random variables,
converges in measure to its limit. -/
private theorem tendstoInMeasure_const_of_tendsto_real
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    {f : ι → ℝ} {c : ℝ} (hf : Tendsto f l (nhds c)) :
    TendstoInMeasure μ (fun i _ => f i) l (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hzero : (fun i => μ {ω | ε ≤ dist (f i) c}) =ᶠ[l] fun _ => 0 := by
    filter_upwards [hf.eventually (Metric.ball_mem_nhds c hε)] with i hi
    have hdist : dist (f i) c < ε := by
      simpa [Metric.mem_ball, dist_comm] using hi
    have hset : {ω : Ω | ε ≤ dist (f i) c} = ∅ := by
      ext ω
      simp [not_le_of_gt hdist]
    simp [hset]
  exact tendsto_const_nhds.congr' hzero.symm

/-- If two eventually positive normalization sequences have an asymptotic
ratio, replacing the denominator in a domain-of-attraction limit changes the
limiting law by the reciprocal ratio. This is Slutsky's theorem applied to a
deterministic multiplier, using Mathlib's convergence-in-distribution API. -/
theorem IsInDomainOfAttractionAlong.changeNormalization
    {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center scale' : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit scale center)
    (hscale' : ∀ᶠ n : ℕ in atTop, 0 < scale' n)
    {r : ℝ} (_hr : 0 < r)
    (hratio : Tendsto (fun n => scale n / scale' n) atTop (nhds r)) :
    IsInDomainOfAttractionAlong ν (limit.map fun x => r * x) scale' center := by
  let q : ℕ → ℝ := fun n => scale n / scale' n
  let target : Measure ℝ := limit.map fun x => r * x
  letI : IsProbabilityMeasure target := by
    dsimp [target]
    infer_instance
  have hq : TendstoInMeasure (iidSequenceLaw ν)
      (fun n _ => q n) atTop (fun _ => r) := by
    exact tendstoInMeasure_const_of_tendsto_real hratio
  have hjoint := h.tendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
    (X := normalizedIidSum scale center)
    (Y := fun n _ => q n) (Z := id) (c := r)
    (g := fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop) hq
    (fun _ => measurable_const.aemeasurable)
  have hreplace : ∀ᶠ n : ℕ in atTop,
      (fun ω => normalizedIidSum scale center n ω * q n) =ᵐ[iidSequenceLaw ν]
        normalizedIidSum scale' center n := by
    filter_upwards [h.eventually_scale_pos, hscale'] with n hn hn'
    filter_upwards [] with ω
    simp only [normalizedIidSum, q]
    field_simp [ne_of_gt hn, ne_of_gt hn']
  have hchanged := hjoint.congr_eventually hreplace
    (fun n => (normalizedIidSum_measurable scale' center n).aemeasurable)
  have hmap : limit.map (fun x => x * r) = target.map id := by
    dsimp [target]
    rw [Measure.map_id]
    congr 1
    funext x
    ring
  have hchanged' := hchanged.congr_limit aemeasurable_id hmap
  exact ⟨hscale', hchanged'⟩

/-- The rounded time indices associated with a positive asymptotic time
constant. The added one keeps every index positive. -/
noncomputable def stableNormingIndex (d : ℝ) (n : ℕ) : ℕ :=
  Asymptotics.floorBlockLength (fun n => (n : ℝ) / d) n + 1

theorem stableNormingIndex_ratio {d : ℝ} (hd : 0 < d) :
    Tendsto (fun n => (stableNormingIndex d n : ℝ) / (n : ℝ)) atTop
      (nhds d⁻¹) := by
  let argument : ℕ → ℝ := fun n => (n : ℝ) / d
  let denominator : ℕ → ℝ := fun n => (n : ℝ)
  have hargument : Tendsto argument atTop atTop := by
    simpa [argument, div_eq_mul_inv, mul_comm] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (inv_pos.mpr hd)
  have hdenominator : Tendsto denominator atTop atTop := by
    simpa [denominator] using (tendsto_natCast_atTop_atTop : Tendsto
      (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hratio : Tendsto (fun n => argument n / denominator n) atTop
      (nhds d⁻¹) := by
    have heq : (fun n => argument n / denominator n) =ᶠ[atTop]
        fun _ => d⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      dsimp [argument, denominator]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp [hnR]
    exact tendsto_const_nhds.congr' heq.symm
  simpa [stableNormingIndex, argument, denominator] using
    Asymptotics.tendsto_floorBlockLength_add_nat_div_of_argument_ratio
      1 hargument hdenominator hratio

theorem stableNormingIndex_tendsto_atTop {d : ℝ} (hd : 0 < d) :
    Tendsto (stableNormingIndex d) atTop atTop := by
  have hratio := stableNormingIndex_ratio hd
  have hbound : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / (2 * d) ≤ (stableNormingIndex d n : ℝ) := by
    have hhalf : d⁻¹ / 2 < d⁻¹ := by
      have hinv : 0 < d⁻¹ := inv_pos.mpr hd
      linarith
    filter_upwards [hratio.eventually
        (Ioi_mem_nhds hhalf),
      eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
    have hnratio : d⁻¹ / 2 <
        (stableNormingIndex d n : ℝ) / (n : ℝ) := hn
    have hmul : d⁻¹ / 2 * (n : ℝ) < (stableNormingIndex d n : ℝ) :=
      (lt_div_iff₀ hnR).mp hnratio
    have hcoef : d⁻¹ / 2 * (n : ℝ) = (n : ℝ) / (2 * d) := by
      field_simp [hd.ne']
    rw [← hcoef]
    exact hmul.le
  have hlinear : Tendsto (fun n : ℕ => (n : ℝ) / (2 * d)) atTop atTop := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity :
        0 < (2 * d)⁻¹))
  have hreal : Tendsto (fun n => (stableNormingIndex d n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hbound hlinear
  refine tendsto_atTop.2 ?_
  intro k
  filter_upwards [hreal.eventually (eventually_gt_atTop (k : ℝ))] with n hn
  exact_mod_cast hn.le

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
      ∃ sourceNormalization : ℕ → ℝ,
        IsStableNorming α ν sourceNormalization ∧
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
    dsimp [d]
    exact stableNormingTimeConstant_pos hα₀ hα₂ hc
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
  have hdoa := h.changeNormalization hsourcePosEvent hr hratioStableSource
  have hstable : IsAlphaStable α (limit.map fun x => d ^ (1 / α) * x) := by
    exact hlimit.map_mul (d ^ (1 / α)) hr
  letI hmap : IsProbabilityMeasure
      (limit.map fun x => d ^ (1 / α) * x) := hstable.isProbabilityMeasure
  have hdoa' : @IsInDomainOfAttractionAlong ν
      (limit.map fun x => d ^ (1 / α) * x) inferInstance hmap
      sourceNormalization center := by
    simpa only [Function.comp_def] using hdoa
  exact ⟨d, hd, sourceNormalization, hnorm, hmap, hstable, hdoa'⟩

/-- Reindexing the normalization preserves the index-one sine-centering
condition. -/
theorem IsMogulskiiIndexOneCentered.of_reindexedNorming
    {ν : Measure ℝ} {normalization sourceNormalization : ℕ → ℝ}
    {d : ℝ} (hd : 0 < d)
    (m : ℕ → ℕ)
    (hmratio : Tendsto (fun n => (m n : ℝ) / (n : ℝ)) atTop (nhds d⁻¹))
    (hmPos : ∀ n, 0 < m n)
    (heq : sourceNormalization =ᶠ[atTop] fun n => normalization (m n))
    (hcenter : IsMogulskiiIndexOneCentered ν normalization) :
    IsMogulskiiIndexOneCentered ν sourceNormalization := by
  have hmPosEvent : ∀ᶠ n : ℕ in atTop, 0 < m n :=
    Eventually.of_forall hmPos
  have hsin : Tendsto (fun n : ℕ => (m n : ℝ) *
      (∫ x, Real.sin (x / normalization (m n)) ∂ν)) atTop (nhds 0) := by
    have hmTendsto : Tendsto m atTop atTop := by
      have hhalf : d⁻¹ / 2 < d⁻¹ := by
        have hinv : 0 < d⁻¹ := inv_pos.mpr hd
        linarith
      have hbound : ∀ᶠ n : ℕ in atTop, (n : ℝ) / (2 * d) ≤ (m n : ℝ) := by
        filter_upwards [hmratio.eventually (Ioi_mem_nhds hhalf),
          eventually_gt_atTop (0 : ℕ)] with n hn hn0
        have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
        have hmul : d⁻¹ / 2 * (n : ℝ) < (m n : ℝ) :=
          (lt_div_iff₀ hnR).mp hn
        have hcoef : d⁻¹ / 2 * (n : ℝ) = (n : ℝ) / (2 * d) := by
          field_simp [hd.ne']
        rw [← hcoef]
        exact hmul.le
      have hlinear : Tendsto (fun n : ℕ => (n : ℝ) / (2 * d)) atTop atTop := by
        simpa only [div_eq_mul_inv, mul_comm] using
          (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity :
            0 < (2 * d)⁻¹))
      have hreal : Tendsto (fun n => (m n : ℝ)) atTop atTop :=
        tendsto_atTop_mono' atTop hbound hlinear
      refine tendsto_atTop.2 ?_
      intro k
      filter_upwards [hreal.eventually (eventually_gt_atTop (k : ℝ))] with n hn
      exact_mod_cast hn.le
    simpa only [Function.comp_def] using hcenter.comp
      hmTendsto
  have hnm : Tendsto (fun n : ℕ => (n : ℝ) / (m n : ℝ)) atTop (nhds d) := by
    have hinv := hmratio.inv₀ (by positivity : d⁻¹ ≠ 0)
    have heq' : (fun n => ((m n : ℝ) / (n : ℝ))⁻¹) =ᶠ[atTop]
        fun n => (n : ℝ) / (m n : ℝ) := by
      filter_upwards [hmPosEvent, eventually_gt_atTop (0 : ℕ)] with n hm hn
      have hmR : (m n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    have h := hinv.congr' heq'
    have hconst : (d⁻¹)⁻¹ = d := inv_inv d
    simpa [hconst] using h
  have hprod := hnm.mul hsin
  have heventualEq : (fun n : ℕ =>
      (n : ℝ) * (∫ x, Real.sin (x / normalization (m n)) ∂ν)) =ᶠ[atTop]
      fun n : ℕ => (n : ℝ) / (m n : ℝ) *
        ((m n : ℝ) * (∫ x, Real.sin (x / normalization (m n)) ∂ν)) := by
    filter_upwards [hmPosEvent, eventually_gt_atTop (0 : ℕ)] with n hm hn
    have hmR : (m n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hresult := hprod.congr' heventualEq.symm
  have heqSource : (fun n : ℕ => (n : ℝ) *
      (∫ x, Real.sin (x / normalization (m n)) ∂ν)) =ᶠ[atTop]
      fun n : ℕ => (n : ℝ) * (∫ x, Real.sin (x / sourceNormalization n) ∂ν) := by
    filter_upwards [heq] with n hn
    rw [hn]
  change Tendsto (fun n : ℕ => (n : ℝ) *
    (∫ x, Real.sin (x / sourceNormalization n) ∂ν)) atTop (nhds 0)
  simpa only [Function.comp_def, mul_zero] using hresult.congr' heqSource

end ProbabilityTheory

end
