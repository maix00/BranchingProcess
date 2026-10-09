/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceInputs
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer

/-!
# Escape-rate normalization for raw stable attraction scales

Reindexing a raw domain-of-attraction normalization produces a stable norming
with time constant one. If the raw time constant is `d`, the associated
spatial rescaling is `q = d ^ (1 / α)`. The stable path escape constant then
changes from `C` to `q ^ α * C = d * C`.
-/

open Filter MeasureTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory

private theorem pathMap_eq_of_cadlag {Ω : Type*} [MeasurableSpace Ω]
    (Y : unitInterval → Ω → ℝ) (ω : Ω)
    (hω : IsCadlag (fun t => Y t ω)) :
    Process.Path.Cadlag.pathMap Y ω = ⟨fun t => Y t ω, hω⟩ := by
  let p : CadlagPath unitInterval ℝ := ⟨fun t => Y t ω, hω⟩
  have hcoords :
      (fun r : RationalCoordinate.UnitInterval =>
        Y (RationalCoordinate.toUnitInterval r) ω) =
        MeasureTheory.CadlagPath.denseEvaluation
          RationalCoordinate.toUnitInterval p := by
    funext r
    rfl
  change Function.extend
      (MeasureTheory.CadlagPath.denseEvaluation
        RationalCoordinate.toUnitInterval)
      id (fun _ => Skorokhod.ofContinuousMap
        (ContinuousMap.const unitInterval 0))
      (fun r : RationalCoordinate.UnitInterval =>
        Y (RationalCoordinate.toUnitInterval r) ω) = p
  rw [hcoords]
  exact Process.Path.Cadlag.rationalEvaluationEmbedding.injective.extend_apply
    _ _ _

/-- The canonical path law commutes with spatial scaling of a stable Lévy
process. This identifies the scaled process's path law with the pushforward
of the original law, rather than merely a measure having the same increment
specification. -/
theorem IsStableLevyProcess.unitIntervalPathLaw_spatialScale
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsStableLevyProcess α μ X Q)
    (q : ℝ) (hq : 0 < q) :
    (hX.spatialScale q hq).unitIntervalPathLaw =
      ((hX.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ)).map
        (Skorokhod.scalePath q)) := by
  let Y : unitInterval → Ω → ℝ :=
    fun t ω => X (UnitInterval.toNNReal t) ω
  let Yq : unitInterval → Ω → ℝ := fun t ω => q * Y t ω
  have htime : Monotone UnitInterval.toNNReal := fun _ _ h => h
  have hcadlag : ∀ᵐ ω ∂Q, IsCadlag (fun t => Y t ω) := by
    filter_upwards [hX.ae_cadlag] with ω hω
    exact hω.comp_monotone_continuous htime UnitInterval.continuous_toNNReal
  have hpathMapEq (ω : Ω) (hω : IsCadlag (fun t => Y t ω)) :
      Process.Path.Cadlag.pathMap Yq ω =
        Skorokhod.scalePath q (Process.Path.Cadlag.pathMap Y ω) := by
    have hωq : IsCadlag (fun t => Yq t ω) := by
      exact hω.const_smul q
    rw [pathMap_eq_of_cadlag Yq ω hωq,
      pathMap_eq_of_cadlag Y ω hω]
    rfl
  have hae : Process.Path.Cadlag.pathMap Yq =ᵐ[Q]
      Skorokhod.scalePath q ∘ Process.Path.Cadlag.pathMap Y := by
    filter_upwards [hcadlag] with ω hω
    exact hpathMapEq ω hω
  have hY : AEMeasurable (Process.Path.Cadlag.pathMap Y) Q := by
    apply Process.Path.Cadlag.aemeasurable_pathMap
    intro t
    exact hX.increments.aemeasurable_eval (UnitInterval.toNNReal t)
  have hscaleCont : Continuous (fun f : CadlagPath unitInterval ℝ =>
      Skorokhod.scalePath q f) := by
    have hp : Continuous (fun f : CadlagPath unitInterval ℝ => (q, f)) := by
      fun_prop
    exact Skorokhod.continuous_scalePath.comp hp
  have hmeasure : Q.map (Process.Path.Cadlag.pathMap Yq) =
      (Q.map (Process.Path.Cadlag.pathMap Y)).map (Skorokhod.scalePath q) := by
    calc
      Q.map (Process.Path.Cadlag.pathMap Yq) =
          Q.map (Skorokhod.scalePath q ∘ Process.Path.Cadlag.pathMap Y) :=
        Measure.map_congr hae
      _ = (Q.map (Process.Path.Cadlag.pathMap Y)).map
          (Skorokhod.scalePath q) :=
        (AEMeasurable.map_map_of_aemeasurable
          hscaleCont.aemeasurable hY).symm
  change Q.map (Process.Path.Cadlag.pathMap Yq) =
    (Q.map (Process.Path.Cadlag.pathMap Y)).map (Skorokhod.scalePath q)
  exact hmeasure

namespace HasStableProcessEscapeRate

variable {α C d q : ℝ} {μ : Measure ℝ}
variable {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]

/-- Express a stable process escape rate after the spatial rescaling used to
reindex a raw stable domain-of-attraction normalization. The identity
`q ^ α = d` turns the general scaling law into the source normalization
`d * C`. -/
theorem sourceNormalization
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
  have hPathLaw := hX.unitIntervalPathLaw_spatialScale q hq
  have hEscape' : HasStableProcessEscapeRate α (μ.map fun x => q * x)
      ((hX.spatialScale q hq).unitIntervalPathLaw) (d * C) := by
    simpa only [hPathLaw] using hEscapeMapped
  exact ⟨C, d, q, hEscape, hd, hqEq, hq, m, hmPos, hmratio,
    normalization', hscale', hnormEq, hmap, hlimit', hX', hDOA', hEscape'⟩

end RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end ProbabilityTheory

end
