module

public import Probability.Process.Stable.SmallDeviation.Blocks.Independence

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

/-- The real time at the boundary after `m` uniform blocks. -/
noncomputable def rationalUniformBlockBoundary (blocks m : ℕ) (hblocks : 0 < blocks) : ℝ≥0 :=
  ⟨(m : ℝ) / (blocks : ℝ), by positivity⟩

theorem rationalUniformBlockBoundary_eq_start {blocks : ℕ}
    (hblocks : 0 < blocks) (j : Fin blocks) :
    rationalUniformBlockBoundary blocks j.val hblocks =
      rationalUniformBlockAbsoluteTime hblocks j ⊥ := by
  apply NNReal.coe_injective
  simp only [rationalUniformBlockBoundary, rationalUniformBlockAbsoluteTime,
    rationalUnitTime_coe, rationalUniformBlockTime_bot]
  change (j.val : ℝ) / (blocks : ℝ) =
    (((j.val : ℚ) / (blocks : ℚ) : ℚ) : ℝ)
  push_cast
  rfl

/-- Every point in block `k` precedes boundary `m` when `k < m`. -/
theorem rationalUniformBlockAbsoluteTime_le_boundary {blocks : ℕ}
    (hblocks : 0 < blocks) (k : Fin blocks) (m : ℕ)
    (hkm : k.val < m) (q : ↑Skorokhod.RationalunitInterval) :
    rationalUniformBlockAbsoluteTime hblocks k q ≤
      rationalUniformBlockBoundary blocks m hblocks := by
  apply NNReal.coe_le_coe.mp
  change ((((k.val : ℚ) + (q : ℚ)) / (blocks : ℚ) : ℚ) : ℝ) ≤
    (m : ℝ) / (blocks : ℝ)
  have hden : 0 < (blocks : ℚ) := by exact_mod_cast hblocks
  have hq : (q : ℚ) ≤ 1 := q.property.2
  have hkmQ : (k.val : ℚ) + 1 ≤ (m : ℚ) := by
    exact_mod_cast (Nat.succ_le_of_lt hkm)
  have hrat : ((k.val : ℚ) + (q : ℚ)) / (blocks : ℚ) ≤
      (m : ℚ) / (blocks : ℚ) :=
    (div_le_div_iff_of_pos_right hden).2 (by linarith)
  calc
    ((((k.val : ℚ) + (q : ℚ)) / (blocks : ℚ) : ℚ) : ℝ) ≤
        (((m : ℚ) / (blocks : ℚ) : ℚ) : ℝ) := by exact_mod_cast hrat
    _ = (m : ℝ) / (blocks : ℝ) := by push_cast; rfl

/-- The stopped rational-time path containing all information up to boundary
`m`, normalized to start at zero. -/
noncomputable def rationalUniformPrefixPath {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (blocks m : ℕ) (hblocks : 0 < blocks) :
    Ω → ↑Skorokhod.RationalunitInterval → ℝ :=
  fun ω q => X (min (rationalUnitTime q)
      (rationalUniformBlockBoundary blocks m hblocks)) ω - X 0 ω

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

/-- The measurable event on a rational-coordinate path that its first `m`
uniform blocks all lie in the requested oscillation tube. -/
def rationalUniformPrefixTubeSet (width : ℝ) {blocks : ℕ}
    (hblocks : 0 < blocks) (m : ℕ) :
    Set (↑Skorokhod.RationalunitInterval → ℝ) :=
  ⋂ k : Fin blocks,
    if k.val < m then rationalTubeBlockEvent width hblocks k else Set.univ

theorem measurableSet_rationalUniformPrefixTubeSet (width : ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) :
    MeasurableSet (rationalUniformPrefixTubeSet width hblocks m) := by
  unfold rationalUniformPrefixTubeSet
  apply MeasurableSet.iInter
  intro k
  split_ifs
  · exact measurableSet_rationalTubeBlockEvent width hblocks k
  · exact MeasurableSet.univ

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
