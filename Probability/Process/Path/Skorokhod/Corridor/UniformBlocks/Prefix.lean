/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks
import Topology.Order.UnitInterval.Rational

/-!
# Prefix paths for uniform block partitions

This module contains the deterministic prefix path and prefix tube set for a
uniform rational partition.  Process laws and independence are supplied by
the layers that instantiate this construction.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The rational boundary after `k` uniform blocks, clamped at the final
boundary so it is defined for every natural index. -/
def rationalUniformBlockBoundaryTime {blocks : ℕ} (hblocks : 0 < blocks)
    (k : ℕ) : ↑RationalCoordinate.UnitInterval :=
  ⟨(min k blocks : ℚ) / (blocks : ℚ), by
    constructor
    · positivity
    · rw [div_le_iff₀ (by exact_mod_cast hblocks : 0 < (blocks : ℚ))]
      simpa only [one_mul] using
        (show (min k blocks : ℚ) ≤ (blocks : ℚ) by
          exact_mod_cast min_le_right k blocks)⟩

@[simp] theorem rationalUniformBlockBoundaryTime_zero {blocks : ℕ}
    (hblocks : 0 < blocks) :
    rationalUniformBlockBoundaryTime hblocks 0 = ⊥ := by
  apply Subtype.ext
  simp [rationalUniformBlockBoundaryTime]

theorem rationalUniformBlockBoundaryTime_eq_blockStart {blocks : ℕ}
    (hblocks : 0 < blocks) (j : Fin blocks) :
    rationalUniformBlockBoundaryTime hblocks j.val =
      rationalUniformBlockTime hblocks j ⊥ := by
  apply Subtype.ext
  simp [rationalUniformBlockBoundaryTime, rationalUniformBlockTime]

theorem rationalUniformBlockBoundaryTime_succ_eq_blockEnd {blocks : ℕ}
    (hblocks : 0 < blocks) (j : Fin blocks) :
    rationalUniformBlockBoundaryTime hblocks (j.val + 1) =
      rationalUniformBlockTime hblocks j ⊤ := by
  have hmin : min (j.val + 1) blocks = j.val + 1 :=
    min_eq_left (Nat.succ_le_of_lt j.isLt)
  have hminQ : min ((j.val : ℚ) + 1) (blocks : ℚ) =
      (j.val : ℚ) + 1 := min_eq_left (by exact_mod_cast j.isLt :
        (j.val : ℚ) + 1 ≤ (blocks : ℚ))
  apply Subtype.ext
  simp [rationalUniformBlockBoundaryTime, rationalUniformBlockTime,
    hminQ, Nat.cast_add]

/-- The stopped rational-time path containing all information up to boundary
`m`, normalized to start at zero. -/
noncomputable def rationalUniformPrefixPath {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (blocks m : ℕ) (hblocks : 0 < blocks) :
    Ω → ↑RationalCoordinate.UnitInterval → ℝ :=
  fun ω q => X (min (RationalCoordinate.toNNReal q)
      (rationalUniformBlockBoundary blocks m hblocks)) ω - X 0 ω

/-- The stopped prefix path evaluates at its block boundary when queried at
the right endpoint of the rational unit interval. -/
theorem rationalUniformPrefixPath_top
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) (hm : m ≤ blocks) (ω : Ω) :
    rationalUniformPrefixPath X blocks m hblocks ω ⊤ =
      X (rationalUniformBlockBoundary blocks m hblocks) ω - X 0 ω := by
  have hboundary : rationalUniformBlockBoundary blocks m hblocks ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    change (m : ℝ) / (blocks : ℝ) ≤ 1
    apply (div_le_one (by positivity)).2
    exact_mod_cast hm
  have htop : RationalCoordinate.toNNReal ⊤ = 1 := by
    apply NNReal.coe_injective
    norm_num [RationalCoordinate.toNNReal, RationalCoordinate.toUnitInterval]
    rfl
  simp [rationalUniformPrefixPath, htop, min_eq_right hboundary]

/-- An earlier translated block path is the corresponding block increment of
the stopped prefix path. -/
theorem rationalUniformPrefixPath_blockIncrement_eq
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) (k : Fin blocks)
    (hkm : k.val < m) (ω : Ω) :
    rationalTubeBlockIncrement hblocks k
      (rationalUniformPrefixPath X blocks m hblocks ω) =
      fun q => rationalUniformBlockProcessFromTime X hblocks k q ω := by
  funext q
  have hq := rationalUniformBlockAbsoluteTime_le_boundary hblocks k m hkm q
  have hzero := rationalUniformBlockAbsoluteTime_le_boundary hblocks k m hkm ⊥
  change RationalCoordinate.toNNReal (rationalUniformBlockTime hblocks k q) ≤ _ at hq
  change RationalCoordinate.toNNReal (rationalUniformBlockTime hblocks k ⊥) ≤ _ at hzero
  simp only [rationalTubeBlockIncrement, rationalUniformPrefixPath,
    rationalUniformBlockProcessFromTime, rationalUniformBlockAbsoluteTime]
  rw [min_eq_left hq, min_eq_left hzero]
  ring

/-- The measurable event on a rational-coordinate path that its first `m`
uniform blocks all lie in the requested oscillation tube. -/
def rationalUniformPrefixTubeSet (width : ℝ) {blocks : ℕ}
    (hblocks : 0 < blocks) (m : ℕ) :
    Set (↑RationalCoordinate.UnitInterval → ℝ) :=
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

end ProbabilityTheory

end
