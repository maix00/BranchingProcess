module

public import Probability.Process.Stable.SmallDeviation.Blocks.Independence
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Prefix

/-!
# Prefix paths for uniform block partitions

The path up to a block boundary contains every earlier block increment path.
This deterministic observation is the bridge from two-interval independence to
factorization over an arbitrary finite number of blocks.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- An earlier translated block path is a measurable coordinate expression
in the prefix path. -/
theorem rationalUniformPrefixPath_blockIncrement_eq
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) (k : Fin blocks)
    (hkm : k.val < m) (ω : Ω) :
    rationalTubeBlockIncrement hblocks k
      (rationalUniformPrefixPath X blocks m hblocks ω) =
      fun q => rationalUniformBlockProcessFromLevy X hblocks k q ω := by
  funext q
  have hq := rationalUniformBlockAbsoluteTime_le_boundary hblocks k m hkm q
  have hzero := rationalUniformBlockAbsoluteTime_le_boundary hblocks k m hkm ⊥
  change rationalUnitTime (rationalUniformBlockTime hblocks k q) ≤ _ at hq
  change rationalUnitTime (rationalUniformBlockTime hblocks k ⊥) ≤ _ at hzero
  simp only [rationalTubeBlockIncrement, rationalUniformPrefixPath,
    rationalUniformBlockProcessFromLevy, rationalUniformBlockAbsoluteTime]
  rw [min_eq_left hq, min_eq_left hzero]
  ring

/-- The event for the first `m` blocks is the pullback of a measurable set
through the stopped prefix path. -/
theorem rationalUniformPrefixTubeSet_preimage
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (width : ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) :
    rationalUniformPrefixPath X blocks m hblocks ⁻¹'
      rationalUniformPrefixTubeSet width hblocks m =
      ⋂ k : Fin blocks,
        if k.val < m then
          ((fun ω q => rationalUniformBlockProcessFromLevy X hblocks k q ω) ⁻¹'
            Skorokhod.rationalCoordinateOscillationTube width)
        else Set.univ := by
  ext ω
  simp only [Set.mem_preimage, rationalUniformPrefixTubeSet, Set.mem_iInter]
  apply forall_congr'
  intro k
  by_cases hk : k.val < m
  · simp only [hk, ↓reduceIte, rationalTubeBlockEvent, Set.mem_preimage]
    rw [rationalUniformPrefixPath_blockIncrement_eq X hblocks m k hk ω]
  · simp [hk]

end ProbabilityTheory
