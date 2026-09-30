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
