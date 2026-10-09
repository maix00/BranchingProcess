/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.Blocks.Factorization
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Probability

/-!
# Uniform-block upper bound for stable processes

The prefix factorization gives the full finite product. Equal translated-block
laws then turn the product into the power in the Mogulskii upper estimate.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The first `m` tube events factor into the probabilities of individual
blocks. This is proved from stopped-prefix independence, not assumed as a
finite-family independence hypothesis. -/
theorem IsStableLevyProcess.measure_rationalPrefixTube_eq_prod
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (width : ℝ) (m : ℕ) (hm : m ≤ blocks) :
    P (rationalUniformPrefixTubeEvent X width hblocks m) =
      ∏ k ∈ Finset.range m,
        rationalUniformBlockTubeProbability P X width hblocks k := by
  induction m with
  | zero =>
      simp [measure_univ]
  | succ m ih =>
      have hmlt : m < blocks := by omega
      rw [rationalUniformPrefixTubeEvent_succ X width hblocks m hmlt]
      rw [h.measure_prefixTube_inter_nextBlock blocks hblocks ⟨m, hmlt⟩ width]
      rw [ih (by omega)]
      simp [Finset.prod_range_succ, rationalUniformBlockTubeProbability, hmlt]

/-- The original stable-process block upper inequality follows directly from
independent increments and equality of translated-block laws. -/
theorem IsStableLevyProcess.measure_rationalTube_le_pow_uniformBlocks
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (width : ℝ) :
    P ((fun ω q => X (RationalCoordinate.toNNReal q) ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) ≤
      (P (rationalUniformBlockTubeEvent X width hblocks ⟨0, hblocks⟩)) ^ blocks := by
  let Xq : ↑RationalCoordinate.UnitInterval → Ω → ℝ :=
    fun q ω => X (RationalCoordinate.toNNReal q) ω
  have hindep : iIndepFun (rationalUniformBlockProcess Xq hblocks) P := by
    convert h.iIndepFun_rationalUniformBlocks blocks hblocks using 1
    funext j ω q
    simp [Xq, rationalUniformBlockProcess, rationalTubeBlockIncrement,
      rationalUniformBlockProcessFromTime, rationalUniformBlockAbsoluteTime]
  exact ProbabilityTheory.measure_rationalTube_le_pow_of_iIndep_uniformBlocks
    P Xq hblocks width hindep (fun j =>
      h.rationalUniformBlockProcess_identDistrib blocks hblocks j ⟨0, hblocks⟩)

/-- Rational-coordinate counterpart of Lemma 2(c), equation (23): a full
unit-time range tube is bounded by a power of the short-block tube. The
paper's statement is on càdlàg path sets and uses `X(0,c) J₁`; that bridge
is separate. -/
theorem IsStableLevyProcess.measure_rationalHorizonTube_le_pow_shortHorizon
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (width : ℝ) :
    P (rationalHorizonTubeEvent X 1 width) ≤
      (P (rationalHorizonTubeEvent X
        (rationalUniformBlockBoundary blocks 1 hblocks) width)) ^ blocks := by
  have hone : rationalHorizonTubeEvent X 1 width =
      (fun ω q => X (RationalCoordinate.toNNReal q) ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width := by
    ext ω
    change (fun q => X (1 * RationalCoordinate.toNNReal q) ω) ∈
      Skorokhod.rationalCoordinateOscillationTube width ↔
      (fun q => X (RationalCoordinate.toNNReal q) ω) ∈
        Skorokhod.rationalCoordinateOscillationTube width
    simp
  rw [hone, ← rationalUniformBlockTubeEvent_zero_eq_horizon X width hblocks]
  exact h.measure_rationalTube_le_pow_uniformBlocks blocks hblocks width

end ProbabilityTheory
