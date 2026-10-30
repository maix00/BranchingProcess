/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Compactness.Compact
public import Topology.Cadlag.Skorokhod.Compactness.Basic
public import Topology.Cadlag.Skorokhod.Compactness.StepPath

/-!
# Compact families of step paths with moving partitions

## Public declarations

- `Skorokhod.OscillationPartition.stepApproximation_eq_ofPoints_stepPath`:
  identifies the step approximation of an oscillation partition with the
  step path determined by its ordered knots and sampled values.
- `Skorokhod.compactRangeMovingPartitionStepPathFamily`: the set of step paths
  with at most a prescribed number of cells, a uniform positive knot gap, and
  values in a given range.
- `Skorokhod.isCompact_compactRangeMovingPartitionStepPathFamily`: this family
  is compact when the value range is compact.
- `Skorokhod.OscillationPartition.stepApproximation_mem_compactRangeMovingPartitionStepPathFamily`:
  places a path's partition approximation in that family when its values lie
  in the range and its cell count is bounded.

These interfaces are reusable for compactness and approximation arguments on
Skorokhod path space. The compact family is used by both total-boundedness and
compact-range criteria; the approximation identity also supports path-space
separability.
-/

open Set

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

end Skorokhod
