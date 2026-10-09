/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourceUpper
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourcePartitionLower.EnergyLower
import Probability.Process.SmallDeviation.Mogulskii.PathClass.Partition.UpperEnergy

/-!
# Exact discrete upper rate for finite-partition corridors

The finite-width cell estimates converge to the exact corridor energy as
their relative enlargement and exponential slack vanish. Cells with infinite
width are omitted, since they contribute zero to the energy.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

private theorem tendsto_relativeCellUpperRate
    {C α width : ℝ} (hwidth : 0 < width) :
    Tendsto (fun δ : ℝ =>
      C / (((width + δ * width) / 2) ^ α) + 2 * δ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (C / ((width / 2) ^ α))) := by
  have hδ : Tendsto (fun δ : ℝ => δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hproduct : Tendsto (fun δ : ℝ => δ * width)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 * width)) := hδ.mul_const width
  have hnumerator : Tendsto (fun δ : ℝ => width + δ * width)
      (𝓝[>] (0 : ℝ)) (𝓝 width) := by
    simpa using tendsto_const_nhds.add hproduct
  have hbase : Tendsto (fun δ : ℝ => (width + δ * width) / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (width / 2)) := by
    simpa using hnumerator.div_const (2 : ℝ)
  have hhalf : 0 < width / 2 := by positivity
  have hpow : Tendsto (fun δ : ℝ => ((width + δ * width) / 2) ^ α)
      (𝓝[>] (0 : ℝ)) (𝓝 ((width / 2) ^ α)) :=
    (Real.continuousAt_rpow_const (width / 2) α
      (Or.inl (ne_of_gt hhalf))).tendsto.comp hbase
  have hden : 0 < (width / 2) ^ α := Real.rpow_pos_of_pos hhalf α
  have hquot : Tendsto (fun δ : ℝ => C / (((width + δ * width) / 2) ^ α))
      (𝓝[>] (0 : ℝ)) (𝓝 (C / ((width / 2) ^ α)) : Filter ℝ) := by
    exact tendsto_const_nhds.div hpow (ne_of_gt hden)
  have hslack : Tendsto (fun δ : ℝ => 2 * δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hδ.const_mul (2 : ℝ)
  simpa using hquot.add hslack

private theorem tendsto_finiteCellUpperRateEnvelope
    {ι : Type*} [Fintype ι]
    (s : Finset ι) (duration width : ι → ℝ)
    {C α : ℝ} (hwidth : ∀ i ∈ s, 0 < width i) :
    Tendsto
      (fun δ : ℝ =>
        (∑ i ∈ s, duration i *
          (C / (((width i + δ * width i) / 2) ^ α) + 2 * δ)) + δ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (C * 2 ^ α * ∑ i ∈ s, duration i / width i ^ α)) := by
  have hδ : Tendsto (fun δ : ℝ => δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hbase' (i : ι) (hi : i ∈ s) : Tendsto
      (fun δ : ℝ => duration i *
        (C / (((width i + δ * width i) / 2) ^ α)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (duration i * (C / ((width i / 2) ^ α))) : Filter ℝ) := by
    have hslack : Tendsto (fun δ : ℝ => 2 * δ)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using hδ.const_mul (2 : ℝ)
    have hrateNoSlack :=
      (tendsto_relativeCellUpperRate (C := C) (α := α) (hwidth i hi)).sub hslack
    simpa using tendsto_const_nhds.mul hrateNoSlack
  have herror (i : ι) (hi : i ∈ s) : Tendsto
      (fun δ : ℝ => duration i * (2 * δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := hδ.const_mul (2 * duration i)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hsumBase : Tendsto
      (fun δ : ℝ => ∑ i ∈ s, duration i *
        (C / (((width i + δ * width i) / 2) ^ α)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ i ∈ s, duration i * (C / ((width i / 2) ^ α))) : Filter ℝ) := by
    apply tendsto_finsetSum
    intro i hi
    exact hbase' i hi
  have hsumError : Tendsto
      (fun δ : ℝ => ∑ i ∈ s, duration i * (2 * δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := tendsto_finsetSum s (fun i hi => herror i hi)
    simpa using h
  have hsum : Tendsto
      (fun δ : ℝ =>
        (∑ i ∈ s, duration i *
          (C / (((width i + δ * width i) / 2) ^ α))) +
          ((∑ i ∈ s, duration i * (2 * δ)) + δ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ i ∈ s, duration i * (C / ((width i / 2) ^ α))) : Filter ℝ) := by
    have h := hsumBase.add (hsumError.add hδ)
    simpa using h
  have hsumEq : ∑ i ∈ s, duration i * (C / ((width i / 2) ^ α)) =
      C * 2 ^ α * ∑ i ∈ s, duration i / width i ^ α := by
    calc
      _ = ∑ i ∈ s, C * 2 ^ α * (duration i / width i ^ α) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hw := hwidth i hi
        have hdiv : (width i / 2) ^ α = width i ^ α / (2 : ℝ) ^ α :=
          Real.div_rpow hw.le (by norm_num) α
        rw [hdiv]
        have hwidthPow : width i ^ α ≠ 0 :=
          (Real.rpow_pos_of_pos hw α).ne'
        have htwoPow : (2 : ℝ) ^ α ≠ 0 :=
          (Real.rpow_pos_of_pos (by norm_num) α).ne'
        field_simp [hwidthPow, htwoPow]
      _ = C * 2 ^ α * ∑ i ∈ s, duration i / width i ^ α := by
        rw [Finset.mul_sum]
  have hrewrite (δ : ℝ) :
      (∑ i ∈ s, duration i *
        (C / (((width i + δ * width i) / 2) ^ α) + 2 * δ)) + δ =
      (∑ i ∈ s, duration i *
        (C / (((width i + δ * width i) / 2) ^ α))) +
        ((∑ i ∈ s, duration i * (2 * δ)) + δ) := by
    calc
      _ = (∑ i ∈ s, (duration i *
          (C / (((width i + δ * width i) / 2) ^ α)) +
          duration i * (2 * δ))) + δ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i ∈ s, duration i *
          (C / (((width i + δ * width i) / 2) ^ α))) +
          (∑ i ∈ s, duration i * (2 * δ)) + δ := by
        rw [Finset.sum_add_distrib]
      _ = _ := by ring
  have hsum' : Tendsto
      (fun δ : ℝ =>
        (∑ i ∈ s, duration i *
          (C / (((width i + δ * width i) / 2) ^ α) + 2 * δ)) + δ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (C * 2 ^ α * ∑ i ∈ s, duration i / width i ^ α)) := by
    have heq : (fun δ : ℝ =>
        (∑ i ∈ s, duration i *
          (C / (((width i + δ * width i) / 2) ^ α))) +
          ((∑ i ∈ s, duration i * (2 * δ)) + δ)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ : ℝ =>
        (∑ i ∈ s, duration i *
          (C / (((width i + δ * width i) / 2) ^ α) + 2 * δ)) + δ) := by
      filter_upwards [] with δ
      exact (hrewrite δ).symm
    have h := Filter.Tendsto.congr' heq hsum
    rw [← hsumEq]
    exact h
  exact hsum'

/-- The finite-width cell range bounds yield the exact upper logarithmic
rate for an `M₂` corridor. The cell enlargement is chosen relatively to its
width; this makes its limiting rate exactly the finite-partition energy. -/
theorem limsup_scaledLog_sourceNormalizedStepCorridor_le_energyRate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (c : M2Corridor) :
    atTop.limsup (fun n => stableSmallDeviationRate α ν scale n * Real.log
      (iidSequenceLaw ν {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
          ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet
            c.upper c.lower}).toReal) ≤
      C * 2 ^ α * (c.energy α).toReal := by
  classical
  let cellIndex := Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1)
  let s : Finset cellIndex := Finset.univ.filter fun i =>
    c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) ≠ ⊤ ∧
    c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) ≠ ⊥
  let lo : cellIndex → ℝ := fun i =>
    (c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal
  let hi : cellIndex → ℝ := fun i =>
    (c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal
  let width : cellIndex → ℝ := fun i => hi i - lo i
  let duration : cellIndex → ℝ := fun i => commonPartitionCellLength c.upper c.lower i
  have hstartSep :=
    ProbabilityTheory.Process.SmallDeviation.Mogulskii.hasContinuousAdmissiblePath_implies_startAndTraceSeparated
      c.hasContinuousAdmissiblePath
  have hsep : TraceSeparated c.upper c.lower := hstartSep.2
  have henergy : (c.energy α).toReal = ∑ i ∈ s, duration i / width i ^ α := by
    simpa [s, lo, hi, width, duration] using
      c.energy_toReal_eq_finiteCellRate α hsep
  have hwidth : ∀ i ∈ s, 0 < width i := by
    intro i hiMem
    have htrace := rightTrace_lt_of_traceSeparated c.upper c.lower hsep
      (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
    have hmem := Finset.mem_filter.mp hiMem
    have hL : (lo i : EReal) =
        c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) := by
      exact EReal.coe_toReal (by
        intro h
        rw [h] at htrace
        exact (not_lt_of_ge le_top) htrace) hmem.2.2
    have hU : (hi i : EReal) =
        c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) := by
      exact EReal.coe_toReal hmem.2.1 (by
        intro h
        rw [h] at htrace
        exact (not_lt_of_ge bot_le) htrace)
    have hreal : lo i < hi i := by
      exact EReal.coe_lt_coe_iff.mp (by simpa [hL, hU] using htrace)
    dsimp [width]
    exact sub_pos.mpr hreal
  have hfiniteEnergyEnvelope := tendsto_finiteCellUpperRateEnvelope
    (C := C) (α := α) (s := s) (duration := duration) (width := width) hwidth
  have hfiniteEnergyEnvelope' : Tendsto
      (fun δ : ℝ =>
        (∑ i ∈ s, duration i *
          (C / (((width i + δ * width i) / 2) ^ α) + 2 * δ)) + δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (C * 2 ^ α * (c.energy α).toReal) : Filter ℝ) := by
    simpa [henergy] using hfiniteEnergyEnvelope
  have hnegative : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ i ∈ s,
        C / (((width i + δ * width i) / 2) ^ α) + 2 * δ < 0 := by
    apply (Finset.eventually_all s).2
    intro i hiMem
    have hrate := tendsto_relativeCellUpperRate (C := C) (α := α)
      (hwidth i hiMem)
    have hlimit : C / ((width i / 2) ^ α) < 0 :=
      div_neg_of_neg_of_pos hEscape.negative
        (Real.rpow_pos_of_pos (div_pos (hwidth i hiMem) (by norm_num)) α)
    exact hrate.eventually (Iio_mem_nhds hlimit)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hnear := hfiniteEnergyEnvelope'.eventually
    (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  obtain ⟨δ, ⟨hδnegative, hδnear⟩, hδpos⟩ :=
    ((hnegative.and hnear).and self_mem_nhdsWithin).exists
  let margin : cellIndex → ℝ := fun i => δ * width i
  let cellSlack : cellIndex → ℝ := fun _ => δ
  have hmargin : ∀ i ∈ s, 0 < margin i := by
    intro i hiMem
    exact mul_pos hδpos (hwidth i hiMem)
  have hcellSlack : ∀ i ∈ s, 0 < cellSlack i := by
    intro i hiMem
    exact hδpos
  have hnegative' : ∀ i ∈ s,
      C / (((hi i - lo i + margin i) / 2) ^ α) + 2 * cellSlack i < 0 := by
    intro i hiMem
    simpa [margin, cellSlack, width] using hδnegative i hiMem
  have hupper := limsup_scaledLog_sourceNormalizedStepCorridor_le_selectedCellRates_of_M2
    hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase c s lo hi
    (by
      intro i hiMem
      have hmem := Finset.mem_filter.mp hiMem
      have htrace := rightTrace_lt_of_traceSeparated c.upper c.lower hsep
        (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
      have hLtop : c.lower.rightTrace
          (StepBoundary.commonPartitionGrid c.upper c.lower i.val) ≠ ⊤ := by
        intro h
        rw [h] at htrace
        exact (not_lt_of_ge le_top) htrace
      exact (EReal.coe_toReal hLtop hmem.2.2).symm)
    (by
      intro i hiMem
      have hmem := Finset.mem_filter.mp hiMem
      have htrace := rightTrace_lt_of_traceSeparated c.upper c.lower hsep
        (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
      have hUbot : c.upper.rightTrace
          (StepBoundary.commonPartitionGrid c.upper c.lower i.val) ≠ ⊥ := by
        intro h
        rw [h] at htrace
        exact (not_lt_of_ge bot_le) htrace
      exact (EReal.coe_toReal hmem.2.1 hUbot).symm)
    margin cellSlack hmargin hcellSlack hδpos hwidth hnegative'
  have hupper' : atTop.limsup (fun n => stableSmallDeviationRate α ν scale n * Real.log
      (iidSequenceLaw ν {increment : ℕ → ℝ |
        RandomWalk.sourceNormalizedStepCadlagPathIcc scale n increment ∈
          ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet
            c.upper c.lower}).toReal) ≤
      (∑ i ∈ s, duration i *
        (C / (((width i + δ * width i) / 2) ^ α) + 2 * δ)) + δ := by
    simpa [margin, cellSlack, width, duration,
      ProbabilityTheory.Process.SmallDeviation.Mogulskii.commonPartitionCellLength] using hupper
  exact hupper'.trans (hδnear.le)

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
