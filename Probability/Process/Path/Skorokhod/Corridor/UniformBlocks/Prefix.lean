module

public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks

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

/-- The stopped rational-time path containing all information up to boundary
`m`, normalized to start at zero. -/
noncomputable def rationalUniformPrefixPath {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (blocks m : ℕ) (hblocks : 0 < blocks) :
    Ω → ↑Skorokhod.RationalunitInterval → ℝ :=
  fun ω q => X (min (rationalUnitTime q)
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
  have htop : rationalUnitTime ⊤ = 1 := by
    apply NNReal.coe_injective
    norm_num [rationalUnitTime, Skorokhod.rationalunitIntervalCoe]
    rfl
  simp [rationalUniformPrefixPath, htop, min_eq_right hboundary]

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

end ProbabilityTheory

end
