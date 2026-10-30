/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Compactness.Basic
public import Topology.Cadlag.Skorokhod.Compactness.StepPath
import Topology.Cadlag.Skorokhod.Compactness.MovingPartition

/-!
# Step approximations and total boundedness in `J₁`

## Public declarations

- `Skorokhod.totallyBounded_of_uniform_admitsOscillationPartition`: if all
  paths in `K` take values in a common compact set and for every `ε > 0` admit
  a common partition gap `δ > 0` with oscillation below `ε`, then
  `TotallyBounded K` in `J₁`.
- `Skorokhod.isCompact_iff_isComplete_rangeBounded_uniformAdmitsOscillationPartition`:
  `IsCompact K ↔ IsComplete K ∧ (∃ R ≥ 0, ∀ f ∈ K, ∀ t, |f t| ≤ R) ∧`
  `∀ ε > 0, ∃ δ > 0, ∀ f ∈ K, f` admits a `δ`-gap partition with oscillation
  below `ε`.
- `Skorokhod.isCompact_closure_iff_isComplete_closure_rangeBounded_uniformAdmitsOscillationPartition`:
  `IsCompact (closure K) ↔ IsComplete (closure K) ∧ (∃ R ≥ 0, ∀ f ∈ K,
  ∀ t, |f t| ≤ R) ∧ ∀ ε > 0, ∃ δ > 0, ∀ f ∈ K, f` admits a `δ`-gap
  partition with oscillation below `ε`.

Uniform oscillation partitions approximate paths by step paths. When the
number of cells and value range are uniformly bounded, these approximants lie
in a compact family. This proves a deterministic total-boundedness criterion
without assuming completeness of the path metric.
-/

@[expose] public section

namespace Skorokhod

/-- A family of càdlàg paths whose ranges lie in a common compact set and
which have uniformly fine oscillation partitions is totally bounded in the
`J₁` metric.

The proof approximates each path by a step path. A common positive cell gap
bounds the number of cells, so at each accuracy all approximants lie in a
finite union of compact moving-partition step-path families. -/
theorem totallyBounded_of_uniform_admitsOscillationPartition
    {E : Type*} [MetricSpace E] {K : Set (CadlagPath unitInterval E)}
    (hrange : ∃ range : Set E, IsCompact range ∧
      ∀ path ∈ K, ∀ t, path t ∈ range)
    (hpartitions : ∀ tolerance > 0, ∃ gap > 0, ∀ path ∈ K,
      ∃ partition : OscillationPartition, gap < partition.mesh ∧
        ∃ oscillation < tolerance,
          OscillationBoundedOnPartition partition path oscillation) :
    TotallyBounded K := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨rangeSet, hrangeCompact, hrange⟩ := hrange
  let radius := ε / 3
  have hradius : 0 < radius := by dsimp [radius]; linarith
  obtain ⟨gap, hgap, hpartitions⟩ := hpartitions radius hradius
  let maxCells := ⌊1 / gap⌋₊
  let approximants := compactRangeMovingPartitionStepPathFamily
    gap rangeSet hgap maxCells
  have hcompact : IsCompact approximants := by
    exact isCompact_compactRangeMovingPartitionStepPathFamily gap rangeSet
      hrangeCompact hgap maxCells
  have htotallyBounded : TotallyBounded approximants := hcompact.totallyBounded
  obtain ⟨centers, hcentersFinite, hcover⟩ :=
    (Metric.totallyBounded_iff.mp htotallyBounded) radius hradius
  refine ⟨centers, hcentersFinite, ?_⟩
  intro path hpath
  obtain ⟨partition, hmesh, oscillation, hoscillation, hosc⟩ :=
    hpartitions path hpath
  have hsizeGap : (partition.size : ℝ) * gap ≤ 1 := by
    calc
      (partition.size : ℝ) * gap ≤ partition.size * partition.mesh :=
        mul_le_mul_of_nonneg_left (le_of_lt hmesh) (Nat.cast_nonneg _)
      _ ≤ 1 := partition.size_mul_mesh_le_one
  have hsizeDiv : (partition.size : ℝ) ≤ 1 / gap :=
    (le_div_iff₀ hgap).2 hsizeGap
  have hsize : partition.size ≤ maxCells := by
    dsimp [maxCells]
    exact Nat.le_floor hsizeDiv
  have happ : partition.stepApproximation path ∈ approximants := by
    exact partition.stepApproximation_mem_compactRangeMovingPartitionStepPathFamily
      path rangeSet hgap hmesh (hrange path hpath) hsize
  have hoscNonneg : 0 ≤ oscillation := by
    have hself := hosc ⊥ ⊥ (ne_of_lt bot_lt_top) (ne_of_lt bot_lt_top) rfl
    simpa using hself
  have hstepDist : dist path (partition.stepApproximation path) ≤ oscillation := by
    calc
      dist path (partition.stepApproximation path) =
          (j1EDist path (partition.stepApproximation path)).toReal := by
        rw [dist_edist, edist_cadlagPath_eq_j1EDist]
      _ ≤ (ENNReal.ofReal oscillation).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top
          (partition.j1EDist_stepApproximation_le path hosc)
      _ = oscillation := ENNReal.toReal_ofReal hoscNonneg
  rcases Set.mem_iUnion.mp (hcover happ) with ⟨center, hcenterCover⟩
  rcases Set.mem_iUnion.mp hcenterCover with ⟨hcenter, hcenterBall⟩
  have hcenterDist : dist (partition.stepApproximation path) center < radius :=
    Metric.mem_ball.mp hcenterBall
  refine Set.mem_iUnion.mpr ⟨center, Set.mem_iUnion.mpr ⟨hcenter, ?_⟩⟩
  rw [Metric.mem_ball]
  calc
    dist path center ≤ dist path (partition.stepApproximation path) +
        dist (partition.stepApproximation path) center := dist_triangle _ _ _
    _ < radius + radius :=
      add_lt_add_of_le_of_lt (hstepDist.trans hoscillation.le) hcenterDist
    _ < ε := by dsimp [radius]; linarith

/-- Compactness of a càdlàg path family is characterized by completeness,
uniform range boundedness, and uniform small-oscillation partitions with a
positive common gap at each tolerance.

Completeness is stated for the family as a subspace. This theorem does not
assume that the ambient `J₁` metric is complete. -/
theorem isCompact_iff_isComplete_rangeBounded_uniformAdmitsOscillationPartition
    {K : Set (CadlagPath unitInterval ℝ)} :
    IsCompact K ↔
      IsComplete K ∧
        ((∃ bound : ℝ, 0 ≤ bound ∧ ∀ path ∈ K, ∀ t, |path t| ≤ bound) ∧
          ∀ tolerance > 0, ∃ gap > 0, ∀ path ∈ K,
            ∃ partition : OscillationPartition, gap < partition.mesh ∧
              ∃ oscillation < tolerance,
                OscillationBoundedOnPartition partition path oscillation) := by
  constructor
  · intro hK
    refine ⟨hK.isComplete, ?_, ?_⟩
    · obtain ⟨bound, hbound, hrange⟩ := isBounded_pathRange_of_isCompact hK 0
      exact ⟨bound, hbound, fun path hpath t => by
        simpa [Real.dist_eq] using hrange path hpath t⟩
    · intro tolerance htolerance
      obtain ⟨gap, hgap, hpartitions⟩ :=
        exists_uniform_admitsOscillationPartition_of_isCompact_of_pos hK htolerance
      refine ⟨gap, hgap, ?_⟩
      intro path hpath
      obtain ⟨partition, hmesh, oscillation, hoscil, hbound⟩ := hpartitions path hpath
      exact ⟨partition, hmesh, oscillation, hoscil, hbound⟩
  · rintro ⟨hcomplete, ⟨hrange, hpartitions⟩⟩
    obtain ⟨bound, hbound, hpathBound⟩ := hrange
    let rangeSet : Set ℝ := Set.Icc (-bound) bound
    have hrangeSet : IsCompact rangeSet := isCompact_Icc
    have hpathRange : ∀ path ∈ K, ∀ t, path t ∈ rangeSet := by
      intro path hpath t
      exact abs_le.mp (hpathBound path hpath t)
    have htotallyBounded : TotallyBounded K :=
      totallyBounded_of_uniform_admitsOscillationPartition
        ⟨rangeSet, hrangeSet, hpathRange⟩ hpartitions
    exact (isCompact_iff_totallyBounded_isComplete).2 ⟨htotallyBounded, hcomplete⟩

/-- Relative compactness of an arbitrary path family is characterized by
completeness of its closure, uniformly bounded ranges, and uniform
small-oscillation partitions with positive common gaps. -/
theorem isCompact_closure_iff_isComplete_closure_rangeBounded_uniformAdmitsOscillationPartition
    {K : Set (CadlagPath unitInterval ℝ)} :
    IsCompact (closure K) ↔
      IsComplete (closure K) ∧
        ((∃ bound : ℝ, 0 ≤ bound ∧ ∀ path ∈ K, ∀ t, |path t| ≤ bound) ∧
          ∀ tolerance > 0, ∃ gap > 0, ∀ path ∈ K,
            ∃ partition : OscillationPartition, gap < partition.mesh ∧
              ∃ oscillation < tolerance,
                OscillationBoundedOnPartition partition path oscillation) := by
  constructor
  · intro hK
    refine ⟨hK.isComplete, ?_, ?_⟩
    · obtain ⟨bound, hbound, hrange⟩ := isBounded_pathRange_of_isCompact hK 0
      exact ⟨bound, hbound, fun path hpath t => by
        simpa [Real.dist_eq] using hrange path (subset_closure hpath) t⟩
    · intro tolerance htolerance
      obtain ⟨gap, hgap, hpartitions⟩ :=
        exists_uniform_admitsOscillationPartition_of_isCompact_of_pos hK htolerance
      refine ⟨gap, hgap, ?_⟩
      intro path hpath
      exact hpartitions path (subset_closure hpath)
  · rintro ⟨hcomplete, ⟨hrange, hpartitions⟩⟩
    obtain ⟨bound, hbound, hpathBound⟩ := hrange
    let rangeSet : Set ℝ := Set.Icc (-bound) bound
    have hrangeSet : IsCompact rangeSet := isCompact_Icc
    have hpathRange : ∀ path ∈ K, ∀ t, path t ∈ rangeSet := by
      intro path hpath t
      exact abs_le.mp (hpathBound path hpath t)
    have htotallyBounded : TotallyBounded K :=
      totallyBounded_of_uniform_admitsOscillationPartition
        ⟨rangeSet, hrangeSet, hpathRange⟩ hpartitions
    exact isCompact_iff_totallyBounded_isComplete.mpr
      ⟨htotallyBounded.closure, hcomplete⟩

end Skorokhod

end
