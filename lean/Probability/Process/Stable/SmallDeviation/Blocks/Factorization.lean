module

public import Probability.Process.Stable.SmallDeviation.Blocks.Prefix

/-!
# Probability factorization across stable-process blocks

The stopped prefix path is independent of the next translated block. This
supports an induction over the number of blocks in the tube event.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

def rationalUniformBlockTubeEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (width : ℝ) {blocks : ℕ} (hblocks : 0 < blocks) (j : Fin blocks) : Set Ω :=
  (fun ω q => rationalUniformBlockProcessFromLevy X hblocks j q ω) ⁻¹'
    Skorokhod.rationalCoordinateOscillationTube width

def rationalUniformPrefixTubeEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (width : ℝ) {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) : Set Ω :=
  ⋂ k : Fin blocks,
    if k.val < m then rationalUniformBlockTubeEvent X width hblocks k else Set.univ

theorem rationalUniformPrefixTubeEvent_eq_preimage
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (width : ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) :
    rationalUniformPrefixTubeEvent X width hblocks m =
      rationalUniformPrefixPath X blocks m hblocks ⁻¹'
        rationalUniformPrefixTubeSet width hblocks m := by
  exact (rationalUniformPrefixTubeSet_preimage X width hblocks m).symm

/-- All information in the stopped prefix path is independent of the entire
next translated block path. -/
theorem IsStableLevyProcess.indepFun_rationalPrefix_nextBlock
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (j : Fin blocks) :
    (rationalUniformPrefixPath X blocks j.val hblocks) ⟂ᵢ[P]
      (fun ω q => rationalUniformBlockProcessFromLevy X hblocks j q ω) := by
  let b := rationalUniformBlockBoundary blocks j.val hblocks
  let c := rationalUniformBlockAbsoluteTime hblocks j ⊤
  have hleft (q : ↑Skorokhod.RationalunitInterval) :
      (0 : ℝ≥0) ≤ min (rationalUnitTime q) b ∧
        min (rationalUnitTime q) b ≤ b :=
    ⟨bot_le, min_le_right _ _⟩
  have hright (q : ↑Skorokhod.RationalunitInterval) :
      b ≤ rationalUniformBlockAbsoluteTime hblocks j q ∧
        rationalUniformBlockAbsoluteTime hblocks j q ≤ c := by
    dsimp [b, c]
    rw [rationalUniformBlockBoundary_eq_start hblocks j]
    exact ⟨monotone_rationalUniformBlockAbsoluteTime hblocks j bot_le,
      monotone_rationalUniformBlockAbsoluteTime hblocks j le_top⟩
  have hindep := h.increments.indepIncrements.indepFun_adjacentPaths
    (fun t => h.increments.aemeasurable_eval t) (0 : ℝ≥0) b c
    (fun q => min (rationalUnitTime q) b)
    (rationalUniformBlockAbsoluteTime hblocks j) hleft hright
  convert hindep using 1
  · rfl
  · funext ω q
    simp [rationalUniformBlockProcessFromLevy, b,
      rationalUniformBlockBoundary_eq_start hblocks j]

/-- The event for all previous block tubes factors from the next block tube.
This gives the exact induction step for the multi-block probability product. -/
theorem IsStableLevyProcess.measure_prefixTube_inter_nextBlock
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (j : Fin blocks) (width : ℝ) :
    P (rationalUniformPrefixTubeEvent X width hblocks j.val ∩
        rationalUniformBlockTubeEvent X width hblocks j) =
      P (rationalUniformPrefixTubeEvent X width hblocks j.val) *
        P (rationalUniformBlockTubeEvent X width hblocks j) := by
  have hindep := h.indepFun_rationalPrefix_nextBlock blocks hblocks j
  have hfactor := hindep.measure_inter_preimage_eq_mul
    (rationalUniformPrefixTubeSet width hblocks j.val)
    (Skorokhod.rationalCoordinateOscillationTube width)
    (measurableSet_rationalUniformPrefixTubeSet width hblocks j.val)
    (Skorokhod.measurableSet_rationalCoordinateOscillationTube width)
  simpa [rationalUniformPrefixTubeEvent_eq_preimage, rationalUniformBlockTubeEvent]
    using hfactor

end ProbabilityTheory
