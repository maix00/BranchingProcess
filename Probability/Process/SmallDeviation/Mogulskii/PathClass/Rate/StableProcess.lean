/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.SmallDeviation.Mogulskii.PathClass.Partition.UpperEnergy
import Probability.Process.SmallDeviation.Mogulskii.PathClass.Rate.FiniteUnionNullMeasurable
import Probability.Process.SmallDeviation.Mogulskii.PathClass.Rate.Approximation
import Topology.Cadlag.Skorokhod.Scaling

/-!
# Stable-process rates for `M₂` and `M₃`

The exact partition estimate gives the source-normalized rate for every
admissible `M₂` corridor. This file converts the scale-parameter limit to the
negative normalization used by the finite-union and approximation theorems,
then applies the existing finite-union argument to `M₃`.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- The positive rate coefficient corresponding to the negative stable
escape constant in Lemma 1(I). -/
noncomputable def stableProcessMogulskiiCoefficient (α C : ℝ) : ℝ :=
  -(C * 2 ^ α)

theorem stableProcessMogulskiiCoefficient_pos {α C : ℝ}
    (hC : C < 0) : 0 < stableProcessMogulskiiCoefficient α C := by
  rw [stableProcessMogulskiiCoefficient]
  have hpow : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  exact neg_pos.mpr (mul_neg_of_neg_of_pos hC hpow)

/-- Every admissible `M₂` corridor has the source-normalized stable-process
rate. The exact corridor event is null-measurable under the path law, and its
probability is eventually positive, so all logarithms are genuine. -/
theorem HasStableProcessEscapeRate.m2_rate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (c : M2Corridor) :
    Tendsto (fun scale : ℝ => -(scale ^ α)) atTop atBot ∧
    (∀ scale : ℝ, NullMeasurableSet
      ((Skorokhod.scalePath scale) ⁻¹' c.toSet) P) ∧
    (∀ᶠ scale : ℝ in atTop,
      0 < (P ((Skorokhod.scalePath scale) ⁻¹' c.toSet)).toReal) ∧
    Tendsto
      (fun scale : ℝ => Real.log
        ((P ((Skorokhod.scalePath scale) ⁻¹' c.toSet)).toReal) / (-(scale ^ α)))
      atTop (𝓝 (stableProcessMogulskiiCoefficient α C * (c.energy α).toReal)) := by
  have hα : 0 < α := hEscape.isStableClockProcessLaw.strictlyStable.1
  have hsource := HasStableProcessEscapeRate.tendsto_scaledCorridorLog_eq_energyRate
    hEscape hX hcdf c
  have hg : Tendsto (fun scale : ℝ => -(scale ^ α)) atTop atBot := by
    exact tendsto_neg_atTop_atBot.comp (tendsto_rpow_atTop hα)
  have hnull : ∀ scale : ℝ,
      NullMeasurableSet ((Skorokhod.scalePath scale) ⁻¹' c.toSet) P := by
    intro scale
    apply c.nullMeasurableSet_preimage_toSet_of_aemeasurable P
    have hcontinuous : Continuous
        (fun f : CadlagPath unitInterval ℝ => Skorokhod.scalePath scale f) := by
      exact Skorokhod.continuous_scalePath.comp
        (continuous_const.prodMk continuous_id)
    exact hcontinuous.measurable.aemeasurable
  let target : ℝ := C * 2 ^ α * (c.energy α).toReal
  have hrate : Tendsto
      (fun scale : ℝ => Real.log
        ((P ((Skorokhod.scalePath scale) ⁻¹' c.toSet)).toReal) / (-(scale ^ α)))
      atTop (𝓝 (stableProcessMogulskiiCoefficient α C * (c.energy α).toReal)) := by
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
        stableProcessMogulskiiCoefficient α C * (c.energy α).toReal := by
      dsimp [target, stableProcessMogulskiiCoefficient]
      ring
    simpa [htarget, stableProcessMogulskiiCoefficient] using hnegative'
  exact ⟨hg, hnull, hsource.1, hrate⟩

/-- The exact stable-process rate for a finite union of admissible corridors.
This is the `M₃` theorem: the minimum corridor energy determines the rate. -/
theorem HasStableProcessEscapeRate.m3_rate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (G : M3 α) :
    (∀ scale : ℝ, NullMeasurableSet
      {ω | Skorokhod.scalePath scale ω ∈ G.toSet} P) ∧
    (∀ᶠ scale : ℝ in atTop,
      0 < (P {ω | Skorokhod.scalePath scale ω ∈ G.toSet}).toReal) ∧
    Tendsto
      (fun scale : ℝ => Real.log
        ((P {ω | Skorokhod.scalePath scale ω ∈ G.toSet}).toReal) /
          (-(scale ^ α)))
      atTop (𝓝 (stableProcessMogulskiiCoefficient α C * G.hAlpha)) := by
  let paths : ℝ → CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ :=
    fun scale => Skorokhod.scalePath scale
  let g : ℝ → ℝ := fun scale => -(scale ^ α)
  have hα : 0 < α := hEscape.isStableClockProcessLaw.strictlyStable.1
  have hκ : 0 < stableProcessMogulskiiCoefficient α C :=
    stableProcessMogulskiiCoefficient_pos hEscape.negative
  have hg : Tendsto g atTop atBot := by
    change Tendsto (fun scale : ℝ => -(scale ^ α)) atTop atBot
    exact tendsto_neg_atTop_atBot.comp (tendsto_rpow_atTop hα)
  have hpieces := fun i : Fin G.count =>
    HasStableProcessEscapeRate.m2_rate hEscape hX hcdf (G.pieces i)
  have hevent (i : Fin G.count) (scale : ℝ) :
      (Skorokhod.scalePath scale) ⁻¹' (G.pieces i).toSet =
        {ω | paths scale ω ∈ (G.pieces i).toSet} := by
    ext ω
    rfl
  have hmain := tendsto_log_m3_preimage_probability_ratio_of_nullMeasurable
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
theorem HasStableProcessEscapeRate.isM_approximation_rate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : IsM α G)
    (hGnull : ∀ scale : ℝ,
      NullMeasurableSet {ω | Skorokhod.scalePath scale ω ∈ G} P) :
    (∀ᶠ scale : ℝ in atTop,
      0 < (P {ω | Skorokhod.scalePath scale ω ∈ G}).toReal) ∧
    ∃ A : M3Approximation α G, ∃ hLimits : M3EnergyLimits A,
      Tendsto
        (fun scale : ℝ => Real.log
          ((P {ω | Skorokhod.scalePath scale ω ∈ G}).toReal) / (-(scale ^ α)))
        atTop (𝓝 (stableProcessMogulskiiCoefficient α C * hLimits.hAlpha)) := by
  classical
  rcases hG with ⟨A⟩
  let paths : ℝ → CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ :=
    fun scale => Skorokhod.scalePath scale
  let g : ℝ → ℝ := fun scale => -(scale ^ α)
  have hα : 0 < α := hEscape.isStableClockProcessLaw.strictlyStable.1
  have hκ : 0 < stableProcessMogulskiiCoefficient α C :=
    stableProcessMogulskiiCoefficient_pos hEscape.negative
  have hg : Tendsto g atTop atBot := by
    change Tendsto (fun scale : ℝ => -(scale ^ α)) atTop atBot
    exact tendsto_neg_atTop_atBot.comp (tendsto_rpow_atTop hα)
  have hM3rate : ∀ C₃ : M3 α,
      (∀ scale, NullMeasurableSet
        {ω | paths scale ω ∈ C₃.toSet} P) ∧
      (∀ᶠ scale : ℝ in atTop,
        0 < (P {ω | paths scale ω ∈ C₃.toSet}).toReal) ∧
      Tendsto (fun scale => Real.log
        ((P {ω | paths scale ω ∈ C₃.toSet}).toReal) / g scale)
        atTop (𝓝 (stableProcessMogulskiiCoefficient α C * C₃.hAlpha)) := by
    intro C₃
    have hC₃ := HasStableProcessEscapeRate.m3_rate hEscape hX hcdf C₃
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
    filter_upwards [(hM3rate (A.inner 0)).2.1] with scale hinner
    have hmeasure : P {ω | paths scale ω ∈ M3.toSet (A.inner 0)} ≤
        P {ω | paths scale ω ∈ G} := by
      apply measure_mono
      intro ω hω
      exact A.inner_subset 0 hω
    have hreal := ENNReal.toReal_mono (hfiniteG scale) hmeasure
    exact lt_of_lt_of_le hinner hreal
  have hassembled := tendsto_log_probability_ratio_of_M3Approximation
    P paths g hg hκ A htargetNull hM3rate
  rcases hassembled with ⟨_, hlimits⟩
  exact ⟨hGpositive, A, hlimits⟩

/-- The process-level `M` theorem for a measurable target set. Continuity of
spatial scaling supplies the measurability premise required by the exact-set
approximation argument. -/
theorem HasStableProcessEscapeRate.isM_measurable_rate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : IsM α G)
    (hGmeas : MeasurableSet G) :
    (∀ᶠ scale : ℝ in atTop,
      0 < (P {ω | Skorokhod.scalePath scale ω ∈ G}).toReal) ∧
    ∃ A : M3Approximation α G, ∃ hLimits : M3EnergyLimits A,
      Tendsto
        (fun scale : ℝ => Real.log
          ((P {ω | Skorokhod.scalePath scale ω ∈ G}).toReal) / (-(scale ^ α)))
        atTop (𝓝 (stableProcessMogulskiiCoefficient α C * hLimits.hAlpha)) := by
  apply HasStableProcessEscapeRate.isM_approximation_rate hEscape hX hcdf hG
  intro scale
  have hcontinuous : Continuous
      (fun f : CadlagPath unitInterval ℝ => Skorokhod.scalePath scale f) := by
    exact Skorokhod.continuous_scalePath.comp
      (continuous_const.prodMk continuous_id)
  exact (hcontinuous.measurable hGmeas).nullMeasurableSet

end ProbabilityTheory.Process.SmallDeviation.Mogulskii

end
