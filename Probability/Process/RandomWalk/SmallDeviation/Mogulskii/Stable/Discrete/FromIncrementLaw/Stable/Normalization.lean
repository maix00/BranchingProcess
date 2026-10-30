/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.Basic
public import Probability.Distributions.Stable.Attraction.Norming.Rescaling.Mogulskii
import Probability.Distributions.Stable.Attraction.Normal.Norming
public import Probability.Distributions.Stable.Operations.Scaling
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Basic
public import Probability.Process.Stable.Levy

/-!
# Stable inputs from a raw domain-of-attraction normalization

The raw normalization may have a non-unit stable time constant. Reindexing
its sequence produces a stable norming with unit time constant; the increment
law and any given reference process are rescaled by the matching positive
spatial factor. This module packages that shared conversion for probability
and inner/outer path-rate theorems.

## Public declarations

- `exists_source_reindexed_mogulskii_data`: for $0<\alpha<2$, a raw stable
  domain-of-attraction normalization and a smaller deviation scale produce
  $d,q>0$ with $q=d^{1/\alpha}$, a time change $m_n$ with
  $m_n/n\to d^{-1}$, and a reindexed normalization $a'_n=a_{m_n}$ eventually
  for the spatially scaled limit law.
- `exists_source_reindexed_mogulskii_inputs`: the same reindexing while also
  transporting a stable Lévy process $X$ with law $\mu$ to $qX$ with law
  $(x\mapsto qx)_\#\mu$ and preserving the attraction relation.

For $0<\alpha<2$, these inputs supply the path-rate assumptions in Theorem 1,
equation (15), of A. A. Mogul'skii, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.
-/

open Filter MeasureTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Reindex a raw stable domain-of-attraction normalization without choosing
an underlying stable Lévy process. The source time constant determines a
positive spatial rescaling of the stable law; the centered attraction limit
and the small-deviation scale transfer to the reindexed normalization. -/
theorem exists_source_reindexed_mogulskii_data
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hStable : IsStrictlyAlphaStable α μ)
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
            IsStrictlyAlphaStable α (μ.map fun x => q * x) ∧
            @IsInDomainOfAttractionAlong ν (μ.map fun x => q * x)
              inferInstance hmap normalization' (fun _ => 0) := by
  have hlimit : IsAlphaStable α μ := hStable.isAlphaStable
  obtain ⟨d, hd, m, hmPos, hmratio, normalization', hnorm, heq,
      hratio, hmap, _hlimit', hDOA'⟩ :=
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
  have hStable' : IsStrictlyAlphaStable α (μ.map fun x => q * x) := by
    simpa [q] using hStable.map_mul q (ne_of_gt hq)
  exact ⟨d, q, hd, rfl, hq, m, hmPos, hmratio, normalization', hscale', heq,
    hmap, hStable', hDOA'⟩

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
  obtain ⟨d, q, hd, hqEq, hq, m, hmPos, hmratio, normalization', hscale',
      heq, hmap, hlimit', hDOA'⟩ :=
    exists_source_reindexed_mogulskii_data hsmall hX.increments.strictlyStable
      hDOA hα₂
  have hX' : IsStableLevyProcess α (μ.map fun x => q * x)
      (fun t ω => q * X t ω) Q :=
    hX.spatialScale q hq
  exact ⟨d, q, hd, hqEq, hq, m, hmPos, hmratio, normalization', hscale', heq,
    hmap, hlimit'.isAlphaStable, hX', hDOA'⟩


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
