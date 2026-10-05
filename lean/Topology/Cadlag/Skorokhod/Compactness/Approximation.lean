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
    (partition : OscillationPartition) (path : CadlagPath unitInterval ℝ) :
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
gap, and values in a fixed compact interval form a compact family. -/
def boundedMovingPartitionStepPathFamily (gap bound : ℝ) (hgap : 0 < gap)
    (maxCells : ℕ) : Set (CadlagPath unitInterval ℝ) :=
  ⋃ n : {n : ℕ // n ∈ Set.Icc 1 maxCells},
    Set.range (stepPathOfParameters (n := n.1)
      (by
        have hn := n.2
        simp only [Set.mem_Icc] at hn
        omega)
      (gap := gap) (bound := bound) hgap)

/-- Compactness for the finite union over all allowed partition sizes. -/
theorem isCompact_boundedMovingPartitionStepPathFamily (gap bound : ℝ)
    (hgap : 0 < gap) (maxCells : ℕ) :
    IsCompact (boundedMovingPartitionStepPathFamily gap bound hgap maxCells) := by
  let Index := {n : ℕ // n ∈ Set.Icc 1 maxCells}
  have hfinite : Finite Index := (Set.finite_Icc 1 maxCells).to_subtype
  change IsCompact (⋃ n : Index,
    Set.range (stepPathOfParameters (n := n.1)
      (by
        have hn := n.2
        simp only [Set.mem_Icc] at hn
        omega)
      (gap := gap) (bound := bound) hgap))
  exact @isCompact_iUnion _ _ Index
    (fun n => Set.range (stepPathOfParameters (n := n.1)
      (by
        have hn := n.2
        simp only [Set.mem_Icc] at hn
        omega)
      (gap := gap) (bound := bound) hgap))
    hfinite (fun n => isCompact_stepPathOfParameters_image (n := n.1)
      (by
        have hn := n.2
        simp only [Set.mem_Icc] at hn
        omega)
      hgap)

/-- The step approximation from an oscillation partition belongs to the
compact finite union of moving-partition step paths whenever its cell values
are uniformly bounded and its cell count is bounded. -/
theorem OscillationPartition.stepApproximation_mem_boundedMovingPartitionStepPathFamily
    (partition : OscillationPartition) (path : CadlagPath unitInterval ℝ)
    {gap bound : ℝ} (hgap : 0 < gap) (hmesh : gap < partition.mesh)
    (hrange : ∀ t, |path t| ≤ bound) {maxCells : ℕ}
    (hsize : partition.size ≤ maxCells) :
    partition.stepApproximation path ∈
      boundedMovingPartitionStepPathFamily gap bound hgap maxCells := by
  let values : Fin (partition.size + 1) → ℝ := Fin.lastCases (path ⊤)
    (fun i => path (partition.points i.castSucc))
  have hpoints : IsSeparatedPartitionPoints gap partition.points := by
    refine ⟨partition.first, partition.last, ?_⟩
    intro i
    refine ⟨le_of_lt (partition.strictMono_points i.castSucc_lt_succ), ?_⟩
    exact (le_of_lt hmesh).trans (partition.gap_lower i)
  have hvalues : values ∈
      Set.pi Set.univ (fun _ : Fin (partition.size + 1) => Set.Icc (-bound) bound) := by
    rw [Set.mem_pi]
    intro i _
    refine Fin.lastCases ?_ ?_ i
    · simpa [values] using (abs_le.mp (hrange ⊤))
    · intro i
      simpa [values] using (abs_le.mp (hrange (partition.points i.castSucc)))
  have hparameters : StepPathParameters gap bound (partition.points, values) :=
    ⟨hpoints, hvalues⟩
  have hmem : partition.stepApproximation path ∈
      ⋃ n : {n : ℕ // n ∈ Set.Icc 1 maxCells},
        Set.range (stepPathOfParameters (n := n.1)
          (by
            have hn := n.2
            simp only [Set.mem_Icc] at hn
            omega)
          (gap := gap) (bound := bound) hgap) := by
    refine Set.mem_iUnion.mpr ⟨⟨partition.size, ?_⟩, ?_⟩
    · exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt partition.size_pos), hsize⟩
    · apply Set.mem_range.mpr
      let parameter : {p : (Fin (partition.size + 1) → unitInterval) ×
          (Fin (partition.size + 1) → ℝ) // StepPathParameters gap bound p} :=
        ⟨(partition.points, values), hparameters⟩
      refine ⟨parameter, ?_⟩
      exact (partition.stepApproximation_eq_ofPoints_stepPath path).symm
  exact hmem

/-- A family of càdlàg paths with uniformly bounded ranges and uniformly
fine oscillation partitions is totally bounded in the `J₁` metric.

The proof approximates each path by a step path. A common positive cell gap
bounds the number of cells, so at each accuracy all approximants lie in a
finite union of compact moving-partition step-path families. -/
theorem totallyBounded_of_uniform_admitsOscillationPartition
    {K : Set (CadlagPath unitInterval ℝ)}
    (hrange : ∃ bound : ℝ, 0 ≤ bound ∧ ∀ path ∈ K, ∀ t, |path t| ≤ bound)
    (hpartitions : ∀ tolerance > 0, ∃ gap > 0, ∀ path ∈ K,
      ∃ partition : OscillationPartition, gap < partition.mesh ∧
        ∃ oscillation < tolerance,
          OscillationBoundedOnPartition partition path oscillation) :
    TotallyBounded K := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨rangeBound, hrangeBound, hrange⟩ := hrange
  let radius := ε / 3
  have hradius : 0 < radius := by dsimp [radius]; linarith
  obtain ⟨gap, hgap, hpartitions⟩ := hpartitions radius hradius
  let maxCells := ⌊1 / gap⌋₊
  let approximants := boundedMovingPartitionStepPathFamily gap rangeBound hgap maxCells
  have hcompact : IsCompact approximants := by
    exact isCompact_boundedMovingPartitionStepPathFamily gap rangeBound hgap maxCells
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
    exact partition.stepApproximation_mem_boundedMovingPartitionStepPathFamily
      path hgap hmesh (hrange path hpath) hsize
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


end Skorokhod

end
