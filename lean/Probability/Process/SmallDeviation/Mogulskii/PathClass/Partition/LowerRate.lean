/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.MeasureTheory.FiniteProduct
import Probability.Process.SmallDeviation.Mogulskii.PathClass.Partition.LowerAssembly

/-!
# Logarithmic lower rate for a fixed inner partition corridor

The endpoint-return kernels have separate stable escape rates. This file
adds those rates over a finite partition and transfers the sum to the whole
corridor using the product lower bound. The result is for a fixed finite
inner corridor; approximating infinite or boundary-valued cells is a separate
geometric limit and is intentionally not hidden in this theorem.
-/

open Filter MeasureTheory
open scoped NNReal Topology

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- For a fixed finite inner corridor on every partition cell, the scaled
logarithmic probability of the whole step corridor is eventually bounded
below by the sum of the individual stable cell rates. -/
theorem HasStableProcessEscapeRate.eventually_scaledCorridorLog_ge_innerPartitionRate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (upper lower : StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (innerLower innerUpper :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hcenter0 : center ⟨0, by
      have hcard := Finset.card_pos.mpr
        (StepBoundary.commonKnots_nonempty upper lower)
      omega⟩ = 0)
    (hradius0 : radius ⟨0, by
      have hcard := Finset.card_pos.mpr
        (StepBoundary.commonKnots_nonempty upper lower)
      omega⟩ = 0)
    (hcores : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      center j - radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val) ∧
      center j + radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val))
    (hradiusStep : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      radius (commonPartitionCellLeftKnotIndex upper lower i) <
        radius (commonPartitionCellRightKnotIndex upper lower i))
    (hgeometry : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) <
          innerLower i ∧
        innerLower i <
          center (commonPartitionCellLeftKnotIndex upper lower i) -
            radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
        innerLower i <
          center (commonPartitionCellRightKnotIndex upper lower i) -
            radius (commonPartitionCellRightKnotIndex upper lower i) ∧
        center (commonPartitionCellLeftKnotIndex upper lower i) +
            radius (commonPartitionCellLeftKnotIndex upper lower i) <
          innerUpper i ∧
        center (commonPartitionCellRightKnotIndex upper lower i) +
            radius (commonPartitionCellRightKnotIndex upper lower i) <
          innerUpper i ∧
        innerUpper i <
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val))
    (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ scale : ℝ in atTop,
      0 < P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower) ∧
      (∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        C * commonPartitionCellLength upper lower i /
          ((((innerUpper i - innerLower i) -
            2 * radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2) ^ α)) - ε ≤
        scale⁻¹ ^ α * Real.log
          ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower)).toReal) := by
  let localEvent : ℝ → Fin ((StepBoundary.commonKnots upper lower).card - 1) →
      Set (CadlagPath unitInterval ℝ) := fun scale i =>
    commonPartitionCellCoreReturnEvent (α := α) scale upper lower center radius
      innerLower innerUpper i
  let localRate : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ :=
    fun i => C * commonPartitionCellLength upper lower i /
      ((((innerUpper i - innerLower i) -
        2 * radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2) ^ α)
  have hcellRate (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
      Tendsto (fun scale : ℝ => scale⁻¹ ^ α * Real.log
        ((P (localEvent scale i)).toReal)) atTop (𝓝 (localRate i)) := by
    let i₀ := commonPartitionCellLeftKnotIndex upper lower i
    let i₁ := commonPartitionCellRightKnotIndex upper lower i
    let lo := innerLower i + radius i₀ - center i₀
    let hi := innerUpper i - radius i₀ - center i₀
    let band := (radius i₁ - radius i₀) / 2
    let coreLo := center i₁ - center i₀ - band
    let coreHi := center i₁ - center i₀ + band
    have hbounds := commonPartitionCellCoreReturnBounds upper lower center radius
      innerLower innerUpper i (hgeometry i) (hradiusStep i)
    have hlo : lo < 0 := by simpa [lo, i₀] using hbounds.1
    have hhi : 0 < hi := by simpa [hi, i₀] using hbounds.2.1
    have hcoreLo : lo < coreLo := by
      simpa [lo, coreLo, band, i₀, i₁] using hbounds.2.2.1
    have hcore : coreLo < coreHi := by
      simpa [coreLo, coreHi, band, i₀, i₁] using hbounds.2.2.2.1
    have hcoreHi : coreHi ≤ hi := by
      have hstrict : coreHi < hi := by
        simpa [hi, coreHi, band, i₀, i₁] using hbounds.2.2.2.2
      exact hstrict.le
    have hrate :=
      ProbabilityTheory.Process.SmallDeviation.Mogulskii.HasStableProcessEscapeRate.tendsto_inv_rpow_mul_log_scaledNormalizedCellIocReturnEvent_of_cell
        hEscape hX hcdf upper lower i hlo hhi hcoreLo hcore hcoreHi hα
    have hwidth : (hi - lo) / 2 =
        ((innerUpper i - innerLower i - 2 * radius i₀) / 2) := by
      dsimp [lo, hi]
      ring_nf
    rw [hwidth] at hrate
    simpa [localEvent, commonPartitionCellCoreReturnEvent, lo, hi, coreLo,
      coreHi, band, i₀, i₁, localRate] using hrate
  have hlocalRateNeg (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
      localRate i < 0 := by
    let i₀ := commonPartitionCellLeftKnotIndex upper lower i
    let i₁ := commonPartitionCellRightKnotIndex upper lower i
    let lo := innerLower i + radius i₀ - center i₀
    let hi := innerUpper i - radius i₀ - center i₀
    let band := (radius i₁ - radius i₀) / 2
    let coreLo := center i₁ - center i₀ - band
    let coreHi := center i₁ - center i₀ + band
    have hgeom := commonPartitionCellCoreReturnBounds upper lower center radius
      innerLower innerUpper i (hgeometry i) (hradiusStep i)
    have hlocalWidth : 0 < (hi - lo) / 2 := by
      have hloCore : lo < coreLo := by
        simpa [lo, coreLo, band, i₀, i₁] using hgeom.2.2.1
      have hcore : coreLo < coreHi := by
        simpa [coreLo, coreHi, band, i₀, i₁] using hgeom.2.2.2.1
      have hcoreHi : coreHi < hi := by
        simpa [hi, coreHi, band, i₀, i₁] using hgeom.2.2.2.2
      have hlohi : lo < hi := hloCore.trans (hcore.trans hcoreHi)
      linarith
    have hwidth : 0 <
        ((innerUpper i - innerLower i - 2 * radius i₀) / 2) := by
      have hwidthEq : (hi - lo) / 2 =
          ((innerUpper i - innerLower i - 2 * radius i₀) / 2) := by
        dsimp [lo, hi]
        ring_nf
      rw [← hwidthEq]
      exact hlocalWidth
    have hdenom : 0 <
        ((innerUpper i - innerLower i - 2 * radius i₀) / 2) ^ α :=
      Real.rpow_pos_of_pos hwidth α
    have hlength : 0 < commonPartitionCellLength upper lower i :=
      commonPartitionCellLength_pos upper lower i
    dsimp [localRate]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos hEscape.negative hlength) hdenom
  have hfactorPositive : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      ∀ᶠ scale : ℝ in atTop, 0 < P (localEvent scale i) := by
    intro i
    have hnegative : ∀ᶠ scale : ℝ in atTop,
        scale⁻¹ ^ α * Real.log ((P (localEvent scale i)).toReal) < 0 :=
      (hcellRate i).eventually
        (Iio_mem_nhds (hlocalRateNeg i))
    filter_upwards [hnegative, eventually_gt_atTop (0 : ℝ)] with scale hneg hscale
    have hcoef : 0 < scale⁻¹ ^ α :=
      Real.rpow_pos_of_pos (inv_pos.mpr hscale) α
    have hlog : Real.log ((P (localEvent scale i)).toReal) < 0 := by
      by_contra hnot
      have hnonneg : 0 ≤ Real.log ((P (localEvent scale i)).toReal) :=
        le_of_not_gt hnot
      have hmul : 0 ≤ scale⁻¹ ^ α *
          Real.log ((P (localEvent scale i)).toReal) :=
        mul_nonneg hcoef.le hnonneg
      linarith
    have htoReal : 0 < (P (localEvent scale i)).toReal := by
      by_contra hnot
      have hzero : (P (localEvent scale i)).toReal = 0 :=
        le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
      rw [hzero, Real.log_zero] at hlog
      exact (lt_irrefl 0) hlog
    exact (ENNReal.toReal_pos_iff.mp htoReal).1
  have hallPositive : ∀ᶠ scale : ℝ in atTop,
      ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        0 < P (localEvent scale i) := by
    have h' : ∀ᶠ scale : ℝ in atTop,
        ∀ i ∈ (Finset.univ : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1))),
          0 < P (localEvent scale i) := by
      apply Finset.univ.eventually_all.2
      intro i hi
      exact hfactorPositive i
    filter_upwards [h'] with scale h scaleIndex
    exact h scaleIndex (Finset.mem_univ scaleIndex)
  have hsumRate : Tendsto (fun scale : ℝ =>
      ∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        scale⁻¹ ^ α * Real.log ((P (localEvent scale i)).toReal))
      atTop (𝓝 (∑ i, localRate i)) := by
    apply tendsto_finsetSum Finset.univ
    intro i hi
    exact hcellRate i
  have hsumEventually : ∀ᶠ scale : ℝ in atTop,
      (∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        scale⁻¹ ^ α * Real.log ((P (localEvent scale i)).toReal)) >
          (∑ i, localRate i) - ε := by
    have hnbhd : (∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        localRate i) - ε < ∑ i, localRate i := by linarith
    exact hsumRate.eventually (Ioi_mem_nhds hnbhd)
  have hscalePositive : ∀ᶠ scale : ℝ in atTop, 0 < scale :=
    eventually_gt_atTop 0
  filter_upwards [hallPositive, hsumEventually, hscalePositive]
    with scale hpositive hsum hscale
  have hproductPositive : 0 < ∏ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      P (localEvent scale i) := by
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pos_iff_ne_zero.mp (hpositive i)
  have hlower := measure_scalePath_preimage_corridorSet_ge_coreReturnProduct
    hEscape.isStableClockProcessLaw upper lower center radius innerLower innerUpper
    hcenter0 hradius0 hscale hcores hradiusStep hgeometry
  have hcorridorPositive : 0 < P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower) :=
    lt_of_lt_of_le hproductPositive hlower
  have hlogBound := ProbabilityTheory.sum_log_toReal_le_measure_log_toReal_of_finsetProduct_le
    P Finset.univ _ (localEvent scale) hlower hproductPositive
  have hcoef : 0 < scale⁻¹ ^ α := by
    exact Real.rpow_pos_of_pos (inv_pos.mpr hscale) α
  have hscaledBound := mul_le_mul_of_nonneg_left hlogBound hcoef.le
  have hsumEq : scale⁻¹ ^ α *
      (∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        Real.log ((P (localEvent scale i)).toReal)) =
      ∑ i, scale⁻¹ ^ α * Real.log ((P (localEvent scale i)).toReal) := by
    rw [Finset.mul_sum]
  rw [hsumEq] at hscaledBound
  have htarget : ∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      localRate i = ∑ i, C * commonPartitionCellLength upper lower i /
        ((((innerUpper i - innerLower i) -
          2 * radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2) ^ α) := by
    rfl
  rw [← htarget]
  exact ⟨hcorridorPositive, le_of_lt (hsum.trans_le hscaledBound)⟩

/-- As the incoming endpoint-core radii are uniformly contracted to zero,
the finite sum of the fixed-inner-corridor cell rates converges to the rate
with the uncontracted inner widths. -/
theorem tendsto_scaledCore_innerPartitionRate
    {α C : ℝ} (upper lower : StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (innerLower innerUpper :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hradiusNonneg : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      0 ≤ radius j)
    (hgeometry : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) <
          innerLower i ∧
        innerLower i <
          center (commonPartitionCellLeftKnotIndex upper lower i) -
            radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
        innerLower i <
          center (commonPartitionCellRightKnotIndex upper lower i) -
            radius (commonPartitionCellRightKnotIndex upper lower i) ∧
        center (commonPartitionCellLeftKnotIndex upper lower i) +
            radius (commonPartitionCellLeftKnotIndex upper lower i) <
          innerUpper i ∧
        center (commonPartitionCellRightKnotIndex upper lower i) +
            radius (commonPartitionCellRightKnotIndex upper lower i) <
          innerUpper i ∧
        innerUpper i <
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)) :
    Tendsto (fun θ : ℝ =>
      ∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        C * commonPartitionCellLength upper lower i /
          (((innerUpper i - innerLower i -
            2 * θ * radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2) ^ α))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        C * commonPartitionCellLength upper lower i /
          (((innerUpper i - innerLower i) / 2) ^ α))) := by
  have hterm (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
      Tendsto (fun θ : ℝ =>
        C * commonPartitionCellLength upper lower i /
          (((innerUpper i - innerLower i -
            2 * θ * radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2) ^ α))
        (𝓝[>] (0 : ℝ))
        (𝓝 (C * commonPartitionCellLength upper lower i /
          (((innerUpper i - innerLower i) / 2) ^ α))) := by
    let i₀ := commonPartitionCellLeftKnotIndex upper lower i
    let width := (innerUpper i - innerLower i) / 2
    let r := radius i₀
    have hwidth : 0 < width := by
      have hlow := (hgeometry i).2.1
      have hhigh := (hgeometry i).2.2.2.1
      dsimp [width]
      have hr := hradiusNonneg i₀
      linarith
    have hid : Tendsto (fun θ : ℝ => θ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hlinear : Tendsto (fun θ : ℝ => width - θ * r)
        (𝓝[>] (0 : ℝ)) (𝓝 width) := by
      simpa [sub_zero] using
        (tendsto_const_nhds.sub (hid.mul_const r) :
          Tendsto (fun θ : ℝ => width - θ * r)
            (𝓝[>] (0 : ℝ)) (𝓝 (width - 0 * r)))
    have hpow :=
      (Real.continuousAt_rpow_const width α (Or.inl (ne_of_gt hwidth))).tendsto.comp hlinear
    have hpowPos : 0 < width ^ α := Real.rpow_pos_of_pos hwidth α
    have hquotient : Tendsto
        (fun θ : ℝ =>
          (C * commonPartitionCellLength upper lower i) / (width - θ * r) ^ α)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((C * commonPartitionCellLength upper lower i) / width ^ α)) :=
      tendsto_const_nhds.div hpow (ne_of_gt hpowPos)
    have hwidthEq (θ : ℝ) :
        (innerUpper i - innerLower i -
          2 * θ * radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2 =
        width - θ * r := by
      dsimp [width, r, i₀]
      ring
    have hfunctionEq :
        (fun θ : ℝ =>
          C * commonPartitionCellLength upper lower i /
            (((innerUpper i - innerLower i -
              2 * θ * radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2) ^ α)) =
        fun θ => C * commonPartitionCellLength upper lower i /
          (width - θ * r) ^ α := by
      funext θ
      rw [hwidthEq]
    rw [hfunctionEq]
    simpa [width] using hquotient
  have hsum := tendsto_finsetSum
    (Finset.univ : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (by
      intro i hi
      exact hterm i)
  simpa using hsum

/-- Letting the endpoint cores shrink removes their width loss from the
finite-partition lower bound. The finite inner corridor is fixed throughout;
only after this theorem does one need to approximate its boundaries. -/
theorem HasStableProcessEscapeRate.eventually_scaledCorridorLog_ge_fixedInnerRate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (upper lower : StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (innerLower innerUpper :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hcenter0 : center ⟨0, by
      have hcard := Finset.card_pos.mpr
        (StepBoundary.commonKnots_nonempty upper lower)
      omega⟩ = 0)
    (hradius0 : radius ⟨0, by
      have hcard := Finset.card_pos.mpr
        (StepBoundary.commonKnots_nonempty upper lower)
      omega⟩ = 0)
    (hcores : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      center j - radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val) ∧
      center j + radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val))
    (hradiusNonneg : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      0 ≤ radius j)
    (hradiusStep : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      radius (commonPartitionCellLeftKnotIndex upper lower i) <
        radius (commonPartitionCellRightKnotIndex upper lower i))
    (hgeometry : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) <
          innerLower i ∧
        innerLower i <
          center (commonPartitionCellLeftKnotIndex upper lower i) -
            radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
        innerLower i <
          center (commonPartitionCellRightKnotIndex upper lower i) -
            radius (commonPartitionCellRightKnotIndex upper lower i) ∧
        center (commonPartitionCellLeftKnotIndex upper lower i) +
            radius (commonPartitionCellLeftKnotIndex upper lower i) <
          innerUpper i ∧
        center (commonPartitionCellRightKnotIndex upper lower i) +
            radius (commonPartitionCellRightKnotIndex upper lower i) <
          innerUpper i ∧
        innerUpper i <
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val))
    (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ scale : ℝ in atTop,
      0 < P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower) ∧
      (∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        C * commonPartitionCellLength upper lower i /
          (((innerUpper i - innerLower i) / 2) ^ α)) - ε ≤
        scale⁻¹ ^ α * Real.log
          ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower)).toReal) := by
  let rateAt (θ : ℝ) :=
    ∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      C * commonPartitionCellLength upper lower i /
        (((innerUpper i - innerLower i -
          2 * θ * radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2) ^ α)
  let rateZero :=
    ∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      C * commonPartitionCellLength upper lower i /
        (((innerUpper i - innerLower i) / 2) ^ α)
  have hrateTendsto : Tendsto rateAt (𝓝[>] (0 : ℝ)) (𝓝 rateZero) := by
    simpa [rateAt, rateZero] using
      tendsto_scaledCore_innerPartitionRate (α := α) (C := C) upper lower
        center radius innerLower innerUpper hradiusNonneg hgeometry
  have hclose : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), rateZero - ε / 2 < rateAt θ :=
    hrateTendsto.eventually (Ioi_mem_nhds (by linarith))
  have hpositive : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), 0 < θ := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    simpa using hθ
  have hsmall : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), θ < 1 := by
    have hid : Tendsto (fun θ : ℝ => θ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    exact hid.eventually (Iio_mem_nhds one_pos)
  obtain ⟨θ, hθconditions⟩ := ((hclose.and hpositive).and hsmall).exists
  rcases hθconditions with ⟨⟨hθclose, hθpos⟩, hθsmall⟩
  have hθle : θ ≤ 1 := hθsmall.le
  let radius' : Fin (StepBoundary.commonKnots upper lower).card → ℝ :=
    fun j => θ * radius j
  have hshrink := commonPartitionLowerGeometry_shrinkCore upper lower center radius
    innerLower innerUpper hcores hradiusNonneg hradiusStep hgeometry hθpos hθle
  have hradius0' : radius' ⟨0, by
      have hcard := Finset.card_pos.mpr
        (StepBoundary.commonKnots_nonempty upper lower)
      omega⟩ = 0 := by
    simp [radius', hradius0]
  have hfixed :=
    HasStableProcessEscapeRate.eventually_scaledCorridorLog_ge_innerPartitionRate
      hEscape hX hcdf upper lower center radius' innerLower innerUpper
      hcenter0 hradius0' hshrink.2.1 hshrink.1 hshrink.2.2 hα (ε := ε / 2)
      (by linarith)
  have hrateCompare : rateZero - ε ≤ rateAt θ - ε / 2 := by
    dsimp [rateAt, rateZero]
    linarith
  filter_upwards [hfixed] with scale hresult
  have hscale : rateAt θ - ε / 2 ≤
      scale⁻¹ ^ α * Real.log
        ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower)).toReal) := by
    have hscale0 :
        (∑ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
          C * commonPartitionCellLength upper lower i /
            (((innerUpper i - innerLower i -
              2 * θ * radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2) ^ α)) -
            ε / 2 ≤
          scale⁻¹ ^ α * Real.log
            ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet upper lower)).toReal) := by
      simpa [radius', mul_assoc] using hresult.2
    dsimp [rateAt]
    exact hscale0
  exact ⟨hresult.1, hrateCompare.trans hscale⟩

end ProbabilityTheory.Process.SmallDeviation.Mogulskii
