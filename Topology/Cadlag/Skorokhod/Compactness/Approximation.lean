/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Compactness
public import Topology.Cadlag.Skorokhod.Compactness.StepPath

/-!
# Step approximations and total boundedness in `J₁`

Uniform oscillation partitions approximate paths by step paths. When the
number of cells and value range are uniformly bounded, these approximants lie
in a compact family. This proves a deterministic total-boundedness criterion
without assuming completeness of the path metric.
-/

@[expose] public section

namespace Skorokhod

/-- Sampling an existing oscillation partition agrees with rebuilding its step
path from the ordered vector of its partition points. -/
theorem OscillationPartition.stepApproximation_eq_ofPoints_stepPath
    {E : Type*} [TopologicalSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E) :
    partition.stepApproximation path =
      (TimeChange.FinitePartition.ofPoints partition.size_pos partition.points
        partition.first partition.last partition.strictMono_points).stepPath
        (Fin.lastCases (path ⊤)
          (fun i => path (partition.points i.castSucc))) := by
  ext t
  by_cases htop : t = ⊤
  · subst t
    simp [OscillationPartition.stepApproximation, OscillationPartition.stepPath]
  · let rebuilt := TimeChange.FinitePartition.ofPoints partition.size_pos
      partition.points partition.first partition.last partition.strictMono_points
    have hindex : rebuilt.index t = partition.index t := by
      exact rebuilt.index_eq_of_cell (partition.index t) t
        (partition.index_lower t) (partition.index_upper t)
    change (partition.stepPath
        (Fin.lastCases (path ⊤) (fun i => path (partition.points i.castSucc)))) t =
      (rebuilt.stepPath
        (Fin.lastCases (path ⊤) (fun i => path (partition.points i.castSucc)))) t
    simp only [OscillationPartition.stepPath, ite_eq_right htop]
    rw [← hindex]
    rfl

/-- Step paths represented with at most `maxCells` cells, a common positive
gap, and values in a fixed compact subset of the state space form a compact
family. -/
def compactRangeMovingPartitionStepPathFamily {E : Type*} [MetricSpace E]
    (gap : ℝ) (range : Set E) (hgap : 0 < gap)
    (maxCells : ℕ) : Set (CadlagPath unitInterval E) :=
  ⋃ n : {n : ℕ // n ∈ Set.Icc 1 maxCells},
    Set.range (stepPathOfParameters (E := E) (n := n.1)
      (by
        have hn := n.2
        simp only [Set.mem_Icc] at hn
        omega)
      range hgap)

/-- Compactness for the finite union over all allowed partition sizes. -/
theorem isCompact_compactRangeMovingPartitionStepPathFamily
    {E : Type*} [MetricSpace E] (gap : ℝ) (range : Set E)
    (hrange : IsCompact range) (hgap : 0 < gap) (maxCells : ℕ) :
    IsCompact (compactRangeMovingPartitionStepPathFamily gap range hgap maxCells) := by
  let Index := {n : ℕ // n ∈ Set.Icc 1 maxCells}
  have hfinite : Finite Index := (Set.finite_Icc 1 maxCells).to_subtype
  change IsCompact (⋃ n : Index,
    Set.range (stepPathOfParameters (E := E) (n := n.1)
      (by
        have hn := n.2
        simp only [Set.mem_Icc] at hn
        omega)
      range hgap))
  exact @isCompact_iUnion _ _ Index
    (fun n => Set.range (stepPathOfParameters (E := E) (n := n.1)
      (by
        have hn := n.2
        simp only [Set.mem_Icc] at hn
        omega)
      range hgap))
    hfinite (fun n => isCompact_stepPathOfParameters_image (n := n.1)
      (by
        have hn := n.2
        simp only [Set.mem_Icc] at hn
        omega)
      range hrange hgap)

/-- The step approximation from an oscillation partition belongs to the
compact finite union of moving-partition step paths whenever its cell values
lie in the common compact range and its cell count is bounded. -/
theorem OscillationPartition.stepApproximation_mem_compactRangeMovingPartitionStepPathFamily
    {E : Type*} [MetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    {gap : ℝ} (range : Set E) (hgap : 0 < gap) (hmesh : gap < partition.mesh)
    (hrange : ∀ t, path t ∈ range) {maxCells : ℕ}
    (hsize : partition.size ≤ maxCells) :
    partition.stepApproximation path ∈
      compactRangeMovingPartitionStepPathFamily gap range hgap maxCells := by
  let values : Fin (partition.size + 1) → E := Fin.lastCases (path ⊤)
    (fun i => path (partition.points i.castSucc))
  have hpoints : IsSeparatedPartitionPoints gap partition.points := by
    refine ⟨partition.first, partition.last, ?_⟩
    intro i
    refine ⟨le_of_lt (partition.strictMono_points i.castSucc_lt_succ), ?_⟩
    exact (le_of_lt hmesh).trans (partition.gap_lower i)
  have hvalues : values ∈
      Set.pi Set.univ (fun _ : Fin (partition.size + 1) => range) := by
    rw [Set.mem_pi]
    intro i _
    refine Fin.lastCases ?_ ?_ i
    · simpa [values] using hrange ⊤
    · intro i
      simpa [values] using hrange (partition.points i.castSucc)
  have hparameters : StepPathParameters gap range (partition.points, values) :=
    ⟨hpoints, hvalues⟩
  have hmem : partition.stepApproximation path ∈
      ⋃ n : {n : ℕ // n ∈ Set.Icc 1 maxCells},
        Set.range (stepPathOfParameters (E := E) (n := n.1)
          (by
            have hn := n.2
            simp only [Set.mem_Icc] at hn
            omega)
          range hgap) := by
    refine Set.mem_iUnion.mpr ⟨⟨partition.size, ?_⟩, ?_⟩
    · exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt partition.size_pos), hsize⟩
    · apply Set.mem_range.mpr
      let parameter : {p : (Fin (partition.size + 1) → unitInterval) ×
          (Fin (partition.size + 1) → E) // StepPathParameters gap range p} :=
        ⟨(partition.points, values), hparameters⟩
      refine ⟨parameter, ?_⟩
      exact (partition.stepApproximation_eq_ofPoints_stepPath path).symm
  exact hmem

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
    · exact isBounded_pathRange_of_isCompact hK
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
    · obtain ⟨bound, hbound, hrange⟩ := isBounded_pathRange_of_isCompact hK
      exact ⟨bound, hbound, fun path hpath => hrange path (subset_closure hpath)⟩
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
