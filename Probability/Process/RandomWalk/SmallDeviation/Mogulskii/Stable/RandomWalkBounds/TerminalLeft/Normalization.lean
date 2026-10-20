/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.TerminalLeft.Inputs
public import Probability.Process.Stable.PathLaw.UnitInterval
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer

/-!
# Escape-rate normalization for raw stable attraction scales

The public theorem is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.exists_source_reindexed_mogulskii_inputs_with_escape_rate`:
  from a raw small-deviation scale and stable domain-of-attraction
  normalization, together with an actual stable Lévy process and its escape
  rate $C$, obtain a reindexed unit-time normalization and spatial factor
  $q=d^{1/\alpha}$ whose scaled process has escape rate $dC$.

Reindexing a raw domain-of-attraction normalization produces a stable norming
with time constant one. If the raw time constant is `d`, the associated
spatial rescaling is `q = d ^ (1 / α)`. The stable path escape constant then
changes from `C` to `q ^ α * C = d * C`.

These normalization identities supply the hypotheses for the stable
small-deviation rate of A. A. Mogul'skii, Theorem 3, Section 4, p. 764,
“Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations
in a Space of Trajectories,” *Theory of Probability and Its Applications*
19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory

namespace HasStableProcessEscapeRate

variable {α C d q : ℝ} {μ : Measure ℝ}
variable {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]

/-- Express a stable process escape rate after the spatial rescaling used to
reindex a raw stable domain-of-attraction normalization. The identity
`q ^ α = d` turns the general scaling law into the source normalization
`d * C`. -/
private theorem sourceNormalization
    (h : HasStableProcessEscapeRate α μ P C)
    (hd : 0 < d) (hα : 0 < α) (hq : q = d ^ (1 / α)) :
    HasStableProcessEscapeRate α (μ.map fun x => q * x)
      (P.map (Skorokhod.scalePath q)) (d * C) := by
  have hqpos : 0 < q := by
    rw [hq]
    exact Real.rpow_pos_of_pos hd _
  have hqpow : q ^ α = d := by
    rw [hq]
    simpa [one_div] using Real.rpow_inv_rpow hd.le hα.ne'
  have hscaled := h.spatialScale hqpos
  simpa only [hqpow] using hscaled

end HasStableProcessEscapeRate

namespace RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- For a raw stable domain-of-attraction normalization, expose the escape
constant in the original normalization alongside the reindexed Mogul'skii
inputs. If the raw time constant is `d`, the scaled reference process has
escape constant exactly `d * C`.

This theorem packages the existing norming reindexing with the path-law
scaling identity; it does not assume a new stable-process construction. -/
theorem exists_source_reindexed_mogulskii_inputs_with_escape_rate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    {XΩ : Type*} [MeasurableSpace XΩ]
    {X : ℝ≥0 → XΩ → ℝ} {Q : Measure XΩ} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hα₂ : α < 2) :
    ∃ C d q : ℝ,
      HasStableProcessEscapeRate α μ hX.unitIntervalPathLaw C ∧
      0 < d ∧ q = d ^ (1 / α) ∧
      ∃ hq : 0 < q,
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
              inferInstance hmap normalization' (fun _ => 0) ∧
            HasStableProcessEscapeRate α (μ.map fun x => q * x)
              ((hX.spatialScale q hq).unitIntervalPathLaw) (d * C) := by
  obtain ⟨C, hEscape⟩ :=
    hX.isStableClockProcessLaw_unitIntervalPathLaw
      |>.hasStableProcessEscapeRate_of_isStableLevyProcess hX hcdf
  obtain ⟨d, q, hd, hqEq, hq, m, hmPos, hmratio, normalization', hscale',
      hnormEq, hmap, hlimit', hX', hDOA'⟩ :=
    exists_source_reindexed_mogulskii_inputs hsmall hX hDOA hα₂
  have hα : 0 < α := hX.increments.strictlyStable.1
  have hEscapeMapped := hEscape.sourceNormalization hd hα hqEq
  let Y : unitInterval → XΩ → ℝ :=
    fun t ω => X (UnitInterval.toNNReal t) ω
  have hY : ∀ t, AEMeasurable (Y t) Q := by
    intro t
    exact hX.increments.aemeasurable_eval (UnitInterval.toNNReal t)
  have htime : Monotone UnitInterval.toNNReal := fun _ _ h => h
  have hYcadlag : ∀ᵐ ω ∂Q, IsCadlag (fun t => Y t ω) := by
    filter_upwards [hX.ae_cadlag] with ω hω
    exact hω.comp_monotone_continuous htime UnitInterval.continuous_toNNReal
  have hPathLaw := Process.Path.Cadlag.pathLaw_smul Y hY hYcadlag q
  have hPathLaw' :
      ((hX.spatialScale q hq).unitIntervalPathLaw :
        Measure (CadlagPath unitInterval ℝ)) =
      ((hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ)).map
        (Skorokhod.scalePath q)) := by
    simpa [IsStableLevyProcess.unitIntervalPathLaw, Y] using hPathLaw
  have hEscape' : HasStableProcessEscapeRate α (μ.map fun x => q * x)
      ((hX.spatialScale q hq).unitIntervalPathLaw) (d * C) := by
    simpa only [hPathLaw'] using hEscapeMapped
  exact ⟨C, d, q, hEscape, hd, hqEq, hq, m, hmPos, hmratio,
    normalization', hscale', hnormEq, hmap, hlimit', hX', hDOA', hEscape'⟩

end RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end ProbabilityTheory

end
