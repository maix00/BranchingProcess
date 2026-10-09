/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale
public import Probability.Distributions.Stable.Attraction.Norming.Source
public import Probability.Distributions.Stable.Attraction.Normal.TruncatedMoment
public import Probability.Distributions.Stable.Scaling
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale
public import Probability.Process.Stable.Levy

/-!
# Stable inputs from a raw domain-of-attraction normalization

The raw normalization may have a non-unit stable time constant. Reindexing
its sequence produces a stable norming with unit time constant; the increment
law and any given reference process are rescaled by the matching positive
spatial factor. This module packages that shared conversion for probability
and inner/outer path-rate theorems.
-/

open Filter MeasureTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- From a raw domain-of-attraction normalization and a smaller corridor
scale, construct the canonical stable Mogul'skii inputs. The reindexing data
are returned because the index-one sine-centering condition must be transferred
along the same time change. -/
theorem exists_source_reindexed_mogulskii_inputs
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hα₂ : α < 2) :
    ∃ d q : ℝ, 0 < d ∧ q = d ^ (1 / α) ∧ 0 < q ∧
      ∃ m : ℕ → ℕ,
        (∀ n, 0 < m n) ∧
        Tendsto (fun n => (m n : ℝ) / (n : ℝ)) atTop (𝓝 d⁻¹) ∧
        ∃ normalization' : ℕ → ℝ,
          IsStableMogulskiiScale α ν normalization' scale ∧
          normalization' =ᶠ[atTop] (fun n => normalization (m n)) ∧
          ∃ hmap : IsProbabilityMeasure (μ.map fun x => q * x),
            IsAlphaStable α (μ.map fun x => q * x) ∧
            IsStableLevyProcess α (μ.map fun x => q * x)
              (fun t ω => q * X t ω) Q ∧
            @IsInDomainOfAttractionAlong ν (μ.map fun x => q * x)
              inferInstance hmap normalization' (fun _ => 0) := by
  have hlimit : IsAlphaStable α μ := hX.increments.strictlyStable.isAlphaStable
  obtain ⟨d, hd, m, hmPos, hmratio, normalization', hnorm, heq,
      hratio, hmap, hlimit', hDOA'⟩ :=
    hDOA.exists_source_stable_norming hlimit hα₂
  let q : ℝ := d ^ (1 / α)
  have hq : 0 < q := Real.rpow_pos_of_pos hd _
  have hnormPos : ∀ᶠ n : ℕ in atTop, 0 < normalization' n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact hnorm.1 n hn
  have hsourceRatio : Tendsto
      (fun n => normalization' n / normalization n) atTop (𝓝 (q⁻¹)) := by
    have hinv := hratio.inv₀ hq.ne'
    have heqInv : (fun n => (normalization n / normalization' n)⁻¹) =ᶠ[atTop]
        fun n => normalization' n / normalization n := by
      filter_upwards [hDOA.eventually_scale_pos, hnormPos] with n hn hn'
      have hn'0 : normalization' n ≠ 0 := ne_of_gt hn'
      field_simp [ne_of_gt hn, hn'0]
    simpa [q] using hinv.congr' heqInv
  have hsmall' := hsmall.of_tendsto_normalization_ratio
    hDOA.eventually_scale_pos hsourceRatio (inv_pos.mpr hq)
  have hscale' : IsStableMogulskiiScale α ν normalization' scale :=
    ⟨hnorm, hsmall'⟩
  have hX' : IsStableLevyProcess α (μ.map fun x => q * x)
      (fun t ω => q * X t ω) Q := by
    simpa [q] using hX.spatialScale q hq
  exact ⟨d, q, hd, rfl, hq, m, hmPos, hmratio, normalization', hscale', heq,
    hmap, hlimit', hX', hDOA'⟩

/-- The Gaussian-domain counterpart of
`exists_source_reindexed_mogulskii_inputs`.  At index two, the source
normalization is already a stable norming.  We repair only its finite prefix
so positivity holds at every positive index, retaining the same sequence
eventually and therefore the same small-deviation comparison. -/
theorem exists_source_gaussian_mogulskii_inputs
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0)) :
    ∃ normalization' : ℕ → ℝ,
      IsStableMogulskiiScale 2 ν normalization' scale ∧
      normalization' =ᶠ[atTop] normalization ∧
      IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
        normalization' (fun _ => 0) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hDOA.eventually_scale_pos
  let normalization' : ℕ → ℝ := fun n =>
    if N ≤ n then normalization n else 1
  have hnormalization'pos : ∀ n, 0 < normalization' n := by
    intro n
    by_cases hn : N ≤ n
    · simpa [normalization', hn] using hN n hn
    · simp [normalization', hn]
  have hnormalization'eventually : normalization' =ᶠ[atTop] normalization := by
    filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    simp [normalization', hn]
  have hDOA' : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization' (fun _ => 0) := by
    refine ⟨Filter.Eventually.of_forall hnormalization'pos, ?_⟩
    have hsumEq : ∀ᶠ n : ℕ in atTop,
        (fun ω => normalizedIidSum normalization (fun _ => 0) n ω) =ᵐ[iidSequenceLaw ν]
          normalizedIidSum normalization' (fun _ => 0) n := by
      filter_upwards [hnormalization'eventually] with n hn
      filter_upwards [] with ω
      simp [normalizedIidSum, hn]
    exact hDOA.tendstoInDistribution.congr_eventually hsumEq
      (fun n => (normalizedIidSum_measurable normalization' (fun _ => 0) n).aemeasurable)
  have hnorm : IsStableNorming 2 ν normalization' :=
    hDOA'.isStableNorming_two_of_gaussian (fun n _ => hnormalization'pos n)
  have hsmall' := hsmall.of_tendsto_normalization_ratio
    hDOA.eventually_scale_pos
    (by
      have heq : (fun n => normalization' n / normalization n) =ᶠ[atTop]
          fun _ => 1 := by
        filter_upwards [hDOA.eventually_scale_pos,
          hnormalization'eventually] with n hpos hn
        rw [hn]
        exact div_self (ne_of_gt hpos)
      exact tendsto_const_nhds.congr' heq.symm)
    one_pos
  exact ⟨normalization', ⟨hnorm, hsmall'⟩, hnormalization'eventually, hDOA'⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
