/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Analytic.LargeDrawdown

/-!
# Finite-horizon Aïdékon--Hu endpoint estimate

The event that the first-`N` population from `m` roots has a generation-`H`
endpoint below a threshold splits into a large ancestral drawdown and a
surviving selected endpoint with no such drawdown.  The first term is bounded
by the selected-population drawdown estimate, and the second by the
many-to-one estimate for a single root.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Analytic

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- Some particle in the generation-`H` first-`N` selected population from
`m` roots has position at most `threshold`.  As elsewhere in the selected
population API, an address is a pair consisting of its initial root and its
Ulam--Harris address. -/
def firstNSelectedEndpointBelow (m N H : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] (threshold : ℝ) :
    Set (FiniteRootStepField m ℕ ℝ) :=
  {field | ∃ p : RootIndexed.TreeNode (Fin m) ℕ,
    p ∈ firstNSelectedPopulation m N H field ∧
      RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1 p.2 ≤
        threshold}

theorem measurableSet_firstNSelectedEndpointBelow (m N H : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] (threshold : ℝ) :
    MeasurableSet (firstNSelectedEndpointBelow m N H threshold) := by
  classical
  have hpopulation : Measurable (firstNSelectedPopulation m N H) :=
    firstNSelectedPopulation_measurable m N H
  rw [show firstNSelectedEndpointBelow m N H threshold =
      ⋃ p : RootIndexed.TreeNode (Fin m) ℕ,
        {field | p ∈ firstNSelectedPopulation m N H field ∧
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1 p.2 ≤
            threshold} by
    ext field
    simp [firstNSelectedEndpointBelow]]
  apply MeasurableSet.iUnion
  intro p
  have hmem : MeasurableSet
      {field : FiniteRootStepField m ℕ ℝ |
        p ∈ firstNSelectedPopulation m N H field} :=
    hpopulation (measurableSet_mem_finset p)
  have hposition : Measurable
      (fun field : FiniteRootStepField m ℕ ℝ =>
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1 p.2) := by
    exact (RootIndexed.position_measurable (fun _ : Fin m => (0 : ℝ)) id
      measurable_id p.1 p.2).mono
        (Filtration.le (RootIndexed.stepFiltration
          (Root := Fin m) (α := ℕ) (X := ℝ)) p.2.length)
        le_rfl
  have hendpoint : MeasurableSet
      {field : FiniteRootStepField m ℕ ℝ |
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1 p.2 ≤
          threshold} :=
    measurableSet_Iic.preimage hposition
  rw [show {field : FiniteRootStepField m ℕ ℝ |
      p ∈ firstNSelectedPopulation m N H field ∧
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1 p.2 ≤
          threshold} =
      {field | p ∈ firstNSelectedPopulation m N H field} ∩
        {field | RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field
          p.1 p.2 ≤ threshold} by
    ext field
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]]
  exact hmem.inter hendpoint

private theorem rootPosition_eq_pathPotential (m : ℕ)
    (field : FiniteRootStepField m ℕ ℝ) (r : Fin m) (u : TreeNode ℕ) :
    RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field r u =
      Spine.pathPotential realPotential (field r) u := by
  simp [RootIndexed.position, RootIndexed.displace, Spine.pathPotential,
    realPotential]

private theorem pathHistory_coordinate_eq_rootPosition (m H : ℕ)
    (field : FiniteRootStepField m ℕ ℝ) (p : RootIndexed.TreeNode (Fin m) ℕ)
    (k : Fin (H + 1)) :
    Spine.pathHistory realPotential H 0 (field p.1) p.2 k =
      RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
        (p.2.take k.val) := by
  simp [Spine.pathHistory, rootPosition_eq_pathPotential]

/-- Pathwise decomposition of a selected low endpoint.  If it is not in the
raw large-drop event, ancestor closure of first-`N` selection lets us apply
the raw event to every pair of prefixes.  Since the exceptional event uses
strict `> B`, its complement gives exactly the non-strict `≤ B` condition in
the no-large-drop event. -/
theorem firstNSelectedEndpointBelow_subset_rawFirstNSelectedLargeDrop_union_noLargeDrop
    (m N H : ℕ) (B threshold : ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] (hB : 0 < B) :
    firstNSelectedEndpointBelow m N H threshold ⊆
      rawFirstNSelectedLargeDrop m N H B ∪
        firstNSelectedNoLargeDropEndpointBelow m N H B threshold := by
  classical
  intro field hendpoint
  obtain ⟨p, hp, hlow⟩ := hendpoint
  by_cases hlarge : field ∈ rawFirstNSelectedLargeDrop m N H B
  · exact Or.inl hlarge
  · right
    have hpRaw : p ∈ largeDrawdownPopulation m N H field := by
      simpa [largeDrawdownPopulation, firstNSelectedPopulation] using hp
    have hdepth : p.2.length = H :=
      firstNSelectedPopulation_depth m N H field p hp
    have hsurvive : surviveAlong (field p.1) [] p.2 :=
      firstNSelectedPopulation_surviveAlong m N H field p hp
    have hnoDrop : historyHasNoLargeDrop B
        (Spine.pathHistory realPotential H 0 (field p.1) p.2) := by
      intro i j hij
      have hjH : j.val ≤ H := by omega
      have hselectedJ := largeDrawdownPopulation_prefix_mem
        m N H field p hpRaw j.val hjH
      have hposition :
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
              (p.2.take i.val) -
            RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
              (p.2.take j.val) ≤ B := by
        by_cases hijlt : i.val < j.val
        · by_contra hnot
          have hgt : B <
              RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
                  (p.2.take i.val) -
                RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
                  (p.2.take j.val) := lt_of_not_ge hnot
          apply hlarge
          refine ⟨⟨j.val, by omega⟩,
            (p.1, p.2.take j.val), hselectedJ, i.val, hijlt, ?_⟩
          change
            RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
                ((p.2.take j.val).take i.val) -
              RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
                (p.2.take j.val) > B
          rw [List.take_take, min_eq_left (show i.val ≤ j.val by omega)]
          exact hgt
        · have hijEq : i = j := Fin.ext (by omega)
          subst j
          simp only [sub_self]
          exact le_of_lt hB
      simpa only [pathHistory_coordinate_eq_rootPosition] using hposition
    have hendpointHistory :
        Spine.pathHistory realPotential H 0 (field p.1) p.2
          ⟨H, Nat.lt_succ_self H⟩ ≤ threshold := by
      rw [Spine.pathHistory_last realPotential H 0 (field p.1) p.2 hdepth]
      simpa [rootPosition_eq_pathPotential] using hlow
    refine ⟨p, hp, hdepth, hsurvive, ?_⟩
    exact ⟨hnoDrop, hendpointHistory⟩

/-- Finite-horizon Aïdékon--Hu (4.16) estimate for the first-`N` selected
population from `m` initial roots.  It is obtained by the pathwise split into
a raw large drawdown and a no-large-drop endpoint event, followed by the two
separate estimates already proved for those events. -/
theorem measure_firstNSelectedEndpointBelow_le_ah416
    (m N H : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hmN : m ≤ N) (B threshold : ℝ) (hB : 0 < B)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) :
    (finiteRootStepFieldLaw μ m)
        (firstNSelectedEndpointBelow m N H threshold) ≤
      (N : ℝ≥0∞) *
          (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) +
        (m : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp threshold) *
            (tiltedIncrementFieldLaw realPotential μ)
              (spineNoLargeDropEndpointBelowEvent H B threshold)) := by
  calc
    (finiteRootStepFieldLaw μ m)
        (firstNSelectedEndpointBelow m N H threshold) ≤
      (finiteRootStepFieldLaw μ m)
        (rawFirstNSelectedLargeDrop m N H B ∪
          firstNSelectedNoLargeDropEndpointBelow m N H B threshold) :=
      measure_mono
        (firstNSelectedEndpointBelow_subset_rawFirstNSelectedLargeDrop_union_noLargeDrop
          m N H B threshold hB)
    _ ≤
      (finiteRootStepFieldLaw μ m) (rawFirstNSelectedLargeDrop m N H B) +
        (finiteRootStepFieldLaw μ m)
          (firstNSelectedNoLargeDropEndpointBelow m N H B threshold) :=
      measure_union_le _ _
    _ ≤
      (N : ℝ≥0∞) *
          (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) +
        (m : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp threshold) *
            (tiltedIncrementFieldLaw realPotential μ)
              (spineNoLargeDropEndpointBelowEvent H B threshold)) := by
      apply add_le_add
      · exact measure_rawFirstNSelectedLargeDrop_le m N H hmN B hB μ hboundary
      · exact measure_firstNSelectedNoLargeDropEndpointBelow_le
          m N H B threshold μ hboundary

end ProbabilityTheory.BranchingRandomWalk.Analytic
