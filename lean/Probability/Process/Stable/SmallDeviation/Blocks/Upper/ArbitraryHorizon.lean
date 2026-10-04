/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.Blocks.Upper.Scale
public import Probability.Process.Corridor.Range
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stable range-tube upper bounds at arbitrary short horizons

The uniform partition theorem uses blocks of length `1 / n`. Stable scaling
compares that block with any shorter prescribed horizon, so the bound applies
to the stated exponent `⌊1 / c⌋₊` without identifying `c` with `1 / n`.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The unit-time range tube is bounded by the power of the range tube on a
shorter prescribed horizon. The proof first partitions into `blocks` equal
pieces and then uses stable scaling and monotonicity in the tube width. -/
theorem IsStableLevyProcess.measure_rationalTube_le_pow_shorterHorizon
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (shortHorizon : ℝ≥0) (hshort : 0 < shortHorizon)
    (hshorter : shortHorizon ≤ rationalUniformBlockBoundary blocks 1 hblocks)
    (width : ℝ) (hwidth : 0 ≤ width) :
    P (rationalHorizonTubeEvent X 1 width) ≤
      (P (rationalHorizonTubeEvent X shortHorizon width)) ^ blocks := by
  have hblock : 0 < rationalUniformBlockBoundary blocks 1 hblocks := by
    apply NNReal.coe_pos.mp
    simp only [rationalUniformBlockBoundary, Nat.cast_one]
    have hb : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
    change 0 < (1 : ℝ) / (blocks : ℝ)
    positivity
  let blockHorizon := rationalUniformBlockBoundary blocks 1 hblocks
  have hupper := h.measure_rationalTube_le_pow_scaledBlock blocks hblocks width
  have hupper' : P (rationalHorizonTubeEvent X 1 width) ≤
      (P (rationalHorizonTubeEvent X 1
        (width * ((blockHorizon : ℝ) ^ (-(1 / α))))) ^ blocks) := by
    simpa [blockHorizon] using hupper
  rw [← h.rationalTube_timeSpaceScale_inv blockHorizon hblock width] at hupper'
  have hp : 0 < α := h.increments.strictlyStable.1
  have hexp : 0 < 1 / α := by positivity
  have hshorter' : (shortHorizon : ℝ) ≤ (blockHorizon : ℝ) := by
    exact_mod_cast hshorter
  have hscale :
      (blockHorizon : ℝ) ^ (-(1 / α)) ≤
        (shortHorizon : ℝ) ^ (-(1 / α)) := by
    rw [Real.rpow_neg (NNReal.coe_nonneg blockHorizon) (1 / α),
      Real.rpow_neg (NNReal.coe_nonneg shortHorizon) (1 / α)]
    exact (inv_le_inv₀
      (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hblock) _)
      (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hshort) _)).2
        (Real.rpow_le_rpow (by positivity) hshorter' hexp.le)
  have hwidth' : width * ((blockHorizon : ℝ) ^ (-(1 / α))) ≤
      width * ((shortHorizon : ℝ) ^ (-(1 / α))) :=
    mul_le_mul_of_nonneg_left hscale hwidth
  have hmono : rationalHorizonTubeEvent X 1
      (width * ((blockHorizon : ℝ) ^ (-(1 / α)))) ⊆
      rationalHorizonTubeEvent X 1
        (width * ((shortHorizon : ℝ) ^ (-(1 / α)))) := by
    apply Set.preimage_mono
    intro f hf
    rcases hf with ⟨margin, hmargin, hbound⟩
    exact ⟨margin, hmargin, fun s t =>
      (hbound s t).trans (sub_le_sub_right hwidth' _)⟩
  have hprob :
      P (rationalHorizonTubeEvent X blockHorizon width) ≤
        P (rationalHorizonTubeEvent X shortHorizon width) := by
    rw [h.rationalTube_timeSpaceScale_inv blockHorizon hblock width,
      h.rationalTube_timeSpaceScale_inv shortHorizon hshort width]
    exact measure_mono hmono
  exact hupper'.trans (pow_le_pow_left' hprob blocks)

/-- Lemma 2(c), equation (23), with its stated exponent
`⌊1 / c⌋₊`. -/
theorem IsStableLevyProcess.measure_rationalTube_le_pow_floor_inv_horizon
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1) :
    P (rationalHorizonTubeEvent X 1 (2 * a)) ≤
      (P (rationalHorizonTubeEvent X ⟨c, hc.le⟩ (2 * a))) ^ ⌊c⁻¹⌋₊ := by
  let blocks : ℕ := ⌊c⁻¹⌋₊
  have hcinv : 1 ≤ c⁻¹ := (one_le_inv₀ hc).2 hc1
  have hblocks : 0 < blocks := by
    dsimp [blocks]
    exact Nat.floor_pos.mpr hcinv
  have hfloor : (blocks : ℝ) ≤ c⁻¹ := by
    dsimp [blocks]
    exact Nat.floor_le (by positivity)
  have hfloor' : (blocks : ℝ) ≤ 1 / c := by
    simpa [one_div] using hfloor
  have hcblock : c ≤ 1 / (blocks : ℝ) := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hblocks)).2
    have hmul := (le_div_iff₀ hc).mp hfloor'
    nlinarith
  have hshorter : (⟨c, hc.le⟩ : ℝ≥0) ≤
      rationalUniformBlockBoundary blocks 1 hblocks := by
    have hboundary : (rationalUniformBlockBoundary blocks 1 hblocks : ℝ) =
        1 / (blocks : ℝ) := by
      simp [rationalUniformBlockBoundary]
      rfl
    apply NNReal.coe_le_coe.mpr
    change c ≤ (rationalUniformBlockBoundary blocks 1 hblocks : ℝ)
    rw [hboundary]
    exact hcblock
  simpa [blocks] using h.measure_rationalTube_le_pow_shorterHorizon
    blocks hblocks ⟨c, hc.le⟩ hc hshorter (2 * a) (by positivity)

/-- The complete-path left corridor in (23) is bounded by the short-horizon
range event with the original path-set semantics. -/
theorem IsStableLevyProcess.measure_fullCorridor_le_pow_floor_inv_horizon
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1) :
    P (fullSegmentCorridorEvent X 0 1 (-a) a) ≤
      (P (rationalHorizonTubeEvent X ⟨c, hc.le⟩ (2 * a))) ^ ⌊c⁻¹⌋₊ := by
  have hbridge : fullSegmentCorridorEvent X 0 1 (-a) a ⊆
      rationalHorizonTubeEvent X 1 (2 * a) := by
    simpa [two_mul] using
      (fullSegmentCorridorEvent_subset_rationalHorizonTubeEvent_exact X (-a) a)
  exact (measure_mono hbridge).trans
    (h.measure_rationalTube_le_pow_floor_inv_horizon a c ha hc hc1)

end ProbabilityTheory

end
