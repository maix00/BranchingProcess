/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Partition.UpperEnergyRate
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.FiniteUnionNullMeasurable
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Approximation
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.InnerOuter
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Normalization
public import Topology.Cadlag.Skorokhod.Scaling

/-!
# Stable-process rates for `M₂` and `M₃`

The exact partition estimate gives the source-normalized rate for every
admissible `M₂` corridor. This file converts the scale-parameter limit to the
negative normalization used by the finite-union and approximation theorems,
then applies the existing finite-union argument to `M₃`.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor

/-- Every admissible `M₂` corridor has the source-normalized stable-process
rate. The exact corridor event is null-measurable under the path law, and its
probability is eventually positive, so all logarithms are genuine. -/
theorem HasStableProcessEscapeRate.stepCorridor_rate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (c : ContinuousAdmissibleStepCorridor) :
    Tendsto (fun scale : ℝ => -(scale ^ α)) atTop atBot ∧
    (∀ scale : ℝ, NullMeasurableSet
      ((Skorokhod.scalePath scale) ⁻¹' c.toSet) P) ∧
    (∀ᶠ scale : ℝ in atTop,
      0 < (P ((Skorokhod.scalePath scale) ⁻¹' c.toSet)).toReal) ∧
    Tendsto
      (fun scale : ℝ => Real.log
        ((P ((Skorokhod.scalePath scale) ⁻¹' c.toSet)).toReal) / (-(scale ^ α)))
      atTop (𝓝 (rateCoefficient α C * (c.energy α).toReal)) := by
  have hα : 0 < α := hEscape.isStableClockProcessLaw.strictlyStable.1
  have hsource := HasStableProcessEscapeRate.tendsto_scaledCorridorLog_eq_energyRate
    hEscape hX hcdf c
  have hg : Tendsto (fun scale : ℝ => -(scale ^ α)) atTop atBot := by
    exact tendsto_neg_atTop_atBot.comp (tendsto_rpow_atTop hα)
  have hnull : ∀ scale : ℝ,
      NullMeasurableSet ((Skorokhod.scalePath scale) ⁻¹' c.toSet) P := by
    intro scale
    apply ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.ContinuousAdmissibleStepCorridor.nullMeasurableSet_preimage_toSet_of_aemeasurable c P
    have hcontinuous : Continuous
        (fun f : CadlagPath unitInterval ℝ => Skorokhod.scalePath scale f) := by
      exact Skorokhod.continuous_scalePath.comp
        (continuous_const.prodMk continuous_id)
    exact hcontinuous.measurable.aemeasurable
  let target : ℝ := C * 2 ^ α * (c.energy α).toReal
  have hrate : Tendsto
      (fun scale : ℝ => Real.log
        ((P ((Skorokhod.scalePath scale) ⁻¹' c.toSet)).toReal) / (-(scale ^ α)))
      atTop (𝓝 (rateCoefficient α C * (c.energy α).toReal)) := by
    have hnegative := hsource.2.neg
    have heq : (fun scale : ℝ => Real.log
        ((P ((Skorokhod.scalePath scale) ⁻¹' c.toSet)).toReal) / (-(scale ^ α))) =ᶠ[atTop]
      (fun scale : ℝ => -(scale⁻¹ ^ α * Real.log
        ((P ((Skorokhod.scalePath scale) ⁻¹' c.toSet)).toReal))) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with scale hscale
      calc
        _ = -(Real.log
            ((P ((Skorokhod.scalePath scale) ⁻¹' c.toSet)).toReal) *
              (scale ^ α)⁻¹) := by
          rw [div_eq_mul_inv, inv_neg]
          ring
        _ = -(scale⁻¹ ^ α * Real.log
            ((P ((Skorokhod.scalePath scale) ⁻¹' c.toSet)).toReal)) := by
          rw [Real.inv_rpow hscale.le α]
          ring
    have hnegative' := Filter.Tendsto.congr' heq.symm hnegative
    have htarget : -target =
        rateCoefficient α C * (c.energy α).toReal := by
      dsimp [target, rateCoefficient]
      ring
    simpa [htarget, rateCoefficient] using hnegative'
  exact ⟨hg, hnull, hsource.1, hrate⟩

/-- The exact stable-process rate for a finite union of admissible corridors.
This is the `M₃` theorem: the minimum corridor energy determines the rate. -/
theorem HasStableProcessEscapeRate.finiteCorridorUnion_rate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (G : FiniteCorridorUnion α) :
    (∀ scale : ℝ, NullMeasurableSet
      {ω | Skorokhod.scalePath scale ω ∈ G.toSet} P) ∧
    (∀ᶠ scale : ℝ in atTop,
      0 < (P {ω | Skorokhod.scalePath scale ω ∈ G.toSet}).toReal) ∧
    Tendsto
      (fun scale : ℝ => Real.log
        ((P {ω | Skorokhod.scalePath scale ω ∈ G.toSet}).toReal) /
          (-(scale ^ α)))
      atTop (𝓝 (rateCoefficient α C * G.realEnergy)) := by
  let paths : ℝ → CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ :=
    fun scale => Skorokhod.scalePath scale
  let g : ℝ → ℝ := fun scale => -(scale ^ α)
  have hα : 0 < α := hEscape.isStableClockProcessLaw.strictlyStable.1
  have hκ : 0 < rateCoefficient α C :=
    rateCoefficient_pos hEscape.negative
  have hg : Tendsto g atTop atBot := by
    change Tendsto (fun scale : ℝ => -(scale ^ α)) atTop atBot
    exact tendsto_neg_atTop_atBot.comp (tendsto_rpow_atTop hα)
  have hpieces := fun i : Fin G.count =>
    HasStableProcessEscapeRate.stepCorridor_rate hEscape hX hcdf (G.pieces i)
  have hevent (i : Fin G.count) (scale : ℝ) :
      (Skorokhod.scalePath scale) ⁻¹' (G.pieces i).toSet =
        {ω | paths scale ω ∈ (G.pieces i).toSet} := by
    ext ω
    rfl
  have hmain := tendsto_log_finiteCorridorUnion_preimage_probability_ratio_of_nullMeasurable
    P G paths g hg hκ
    (fun scale i => by
      rw [← hevent i scale]
      exact (hpieces i).2.1 scale)
    (fun i => by
      filter_upwards [(hpieces i).2.2.1] with scale hscale
      rw [hevent i scale] at hscale
      exact hscale)
    (fun i => by
      have heq : (fun scale : ℝ => Real.log
          ((P {ω | paths scale ω ∈ (G.pieces i).toSet}).toReal) / g scale) =ᶠ[atTop]
        (fun scale : ℝ => Real.log
          ((P ((Skorokhod.scalePath scale) ⁻¹' (G.pieces i).toSet)).toReal) /
            (-(scale ^ α))) := by
        filter_upwards [] with scale
        rw [← hevent i scale]
      exact Filter.Tendsto.congr' heq.symm (hpieces i).2.2.2)
  exact hmain

/-- The process-level theorem for Mogul'skii's approximation class `M`.
Measurability of the exact target event is explicit, as required to interpret
its probability; the finite `M₃` approximants provide the asymptotic squeeze. -/
theorem HasStableProcessEscapeRate.approximableSet_rate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G)
    (hGnull : ∀ scale : ℝ,
      NullMeasurableSet {ω | Skorokhod.scalePath scale ω ∈ G} P) :
    (∀ᶠ scale : ℝ in atTop,
      0 < (P {ω | Skorokhod.scalePath scale ω ∈ G}).toReal) ∧
    ∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
      Tendsto
        (fun scale : ℝ => Real.log
          ((P {ω | Skorokhod.scalePath scale ω ∈ G}).toReal) / (-(scale ^ α)))
        atTop (𝓝 (rateCoefficient α C * hLimits.commonEnergy)) := by
  classical
  rcases hG with ⟨A⟩
  let paths : ℝ → CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ :=
    fun scale => Skorokhod.scalePath scale
  let g : ℝ → ℝ := fun scale => -(scale ^ α)
  have hα : 0 < α := hEscape.isStableClockProcessLaw.strictlyStable.1
  have hκ : 0 < rateCoefficient α C :=
    rateCoefficient_pos hEscape.negative
  have hg : Tendsto g atTop atBot := by
    change Tendsto (fun scale : ℝ => -(scale ^ α)) atTop atBot
    exact tendsto_neg_atTop_atBot.comp (tendsto_rpow_atTop hα)
  have hFiniteUnionRate : ∀ C₃ : FiniteCorridorUnion α,
      (∀ scale, NullMeasurableSet
        {ω | paths scale ω ∈ C₃.toSet} P) ∧
      (∀ᶠ scale : ℝ in atTop,
        0 < (P {ω | paths scale ω ∈ C₃.toSet}).toReal) ∧
      Tendsto (fun scale => Real.log
        ((P {ω | paths scale ω ∈ C₃.toSet}).toReal) / g scale)
        atTop (𝓝 (rateCoefficient α C * C₃.realEnergy)) := by
    intro C₃
    have hC₃ := HasStableProcessEscapeRate.finiteCorridorUnion_rate hEscape hX hcdf C₃
    refine ⟨?_, ?_, ?_⟩
    · intro scale
      simpa only [Set.preimage] using hC₃.1 scale
    · simpa [g] using hC₃.2.1
    · simpa [g] using hC₃.2.2
  have htargetNull : ∀ scale,
      NullMeasurableSet {ω | paths scale ω ∈ G} P := by
    intro scale
    exact hGnull scale
  have hfiniteG (scale : ℝ) : P {ω | paths scale ω ∈ G} ≠ ⊤ := by
    apply ne_of_lt
    calc
      P {ω | paths scale ω ∈ G} ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hGpositive : ∀ᶠ scale : ℝ in atTop,
      0 < (P {ω | paths scale ω ∈ G}).toReal := by
    filter_upwards [(hFiniteUnionRate (A.inner 0)).2.1] with scale hinner
    have hmeasure : P {ω | paths scale ω ∈ FiniteCorridorUnion.toSet (A.inner 0)} ≤
        P {ω | paths scale ω ∈ G} := by
      apply measure_mono
      intro ω hω
      exact A.inner_subset 0 hω
    have hreal := ENNReal.toReal_mono (hfiniteG scale) hmeasure
    exact lt_of_lt_of_le hinner hreal
  have hassembled := tendsto_log_probability_ratio_of_FiniteCorridorUnionApproximation
    P paths g hg hκ A htargetNull hFiniteUnionRate
  rcases hassembled with ⟨_, hlimits⟩
  exact ⟨hGpositive, A, hlimits⟩

/-- For every source-class `M` target, the stable-process theorem gives the
same logarithmic rate for inner and outer probabilities. This does not assume
that the target itself is measurable or null-measurable. -/
theorem HasStableProcessEscapeRate.approximableSet_innerOuterRate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G) :
    ∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
      (∀ᶠ scale : ℝ in atTop,
        0 < (P.innerMeasure
          {ω | Skorokhod.scalePath scale ω ∈ G}).toReal) ∧
      (∀ᶠ scale : ℝ in atTop,
        0 < (P {ω | Skorokhod.scalePath scale ω ∈ G}).toReal) ∧
      Tendsto
        (fun scale : ℝ => Real.log
          ((P.innerMeasure
            {ω | Skorokhod.scalePath scale ω ∈ G}).toReal) /
              (-(scale ^ α)))
        atTop (𝓝 (rateCoefficient α C * hLimits.commonEnergy)) ∧
      Tendsto
        (fun scale : ℝ => Real.log
          ((P {ω | Skorokhod.scalePath scale ω ∈ G}).toReal) /
            (-(scale ^ α)))
        atTop (𝓝 (rateCoefficient α C * hLimits.commonEnergy)) ∧
      0 < hLimits.commonEnergy ∧ hLimits.commonEnergy ≤ FiniteCorridorUnion.realEnergy (A.inner 0) := by
  let paths : ℝ → CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ :=
    fun scale => Skorokhod.scalePath scale
  let g : ℝ → ℝ := fun scale => -(scale ^ α)
  have hα : 0 < α := hEscape.isStableClockProcessLaw.strictlyStable.1
  have hκ : 0 < rateCoefficient α C := rateCoefficient_pos hEscape.negative
  have hg : Tendsto g atTop atBot := by
    change Tendsto (fun scale : ℝ => -(scale ^ α)) atTop atBot
    exact tendsto_neg_atTop_atBot.comp (tendsto_rpow_atTop hα)
  have hFiniteUnionRate : ∀ C₃ : FiniteCorridorUnion α,
      (∀ scale, NullMeasurableSet
        {ω | paths scale ω ∈ C₃.toSet} P) ∧
      (∀ᶠ scale : ℝ in atTop,
        0 < (P {ω | paths scale ω ∈ C₃.toSet}).toReal) ∧
      Tendsto (fun scale => Real.log
        ((P {ω | paths scale ω ∈ C₃.toSet}).toReal) / g scale)
        atTop (𝓝 (rateCoefficient α C * C₃.realEnergy)) := by
    intro C₃
    have hC₃ := HasStableProcessEscapeRate.finiteCorridorUnion_rate hEscape hX hcdf C₃
    refine ⟨?_, ?_, ?_⟩
    · intro scale
      simpa only [Set.preimage] using hC₃.1 scale
    · simpa [g] using hC₃.2.1
    · simpa [g] using hC₃.2.2
  obtain ⟨A, hLimits, hInnerPos, hOuterPos, hInnerRate, hOuterRate,
      hEnergyBounds⟩ :=
    exists_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation P paths g hg hκ hG hFiniteUnionRate
  refine ⟨A, hLimits, hInnerPos, hOuterPos, ?_, ?_, hEnergyBounds⟩
  · simpa [paths, g] using hInnerRate
  · simpa [paths, g] using hOuterRate

/-- The process-level `M` theorem for a measurable target set. Continuity of
spatial scaling supplies the measurability premise required by the exact-set
approximation argument. -/
theorem HasStableProcessEscapeRate.approximableSet_measurableRate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G)
    (hGmeas : MeasurableSet G) :
    (∀ᶠ scale : ℝ in atTop,
      0 < (P {ω | Skorokhod.scalePath scale ω ∈ G}).toReal) ∧
    ∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
      Tendsto
        (fun scale : ℝ => Real.log
          ((P {ω | Skorokhod.scalePath scale ω ∈ G}).toReal) / (-(scale ^ α)))
        atTop (𝓝 (rateCoefficient α C * hLimits.commonEnergy)) := by
  apply HasStableProcessEscapeRate.approximableSet_rate hEscape hX hcdf hG
  intro scale
  have hcontinuous : Continuous
      (fun f : CadlagPath unitInterval ℝ => Skorokhod.scalePath scale f) := by
    exact Skorokhod.continuous_scalePath.comp
      (continuous_const.prodMk continuous_id)
  exact (hcontinuous.measurable hGmeas).nullMeasurableSet

end ProbabilityTheory

end
