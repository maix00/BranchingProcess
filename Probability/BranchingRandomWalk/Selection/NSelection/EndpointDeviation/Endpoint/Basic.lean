/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Large
public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Theorems
/-!
# Finite-horizon Aïdékon--Hu endpoint estimate

## Public declarations

The declarations are in
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation`.

- `firstNSelectedEndpointBelow m N H threshold` defines the event
  \(E_{m,N,H}(x)\) that a generation-`H` selected endpoint is at most `x`.
- `measurableSet_firstNSelectedEndpointBelow` proves that this event is
  measurable when the root-indexed address space is countable and measurable.
- `firstNSelectedEndpointBelow_subset_rawFirstNSelectedLargeDrop_union_noLargeDrop`
  gives the pathwise decomposition
  \(E_{m,N,H}(x)\subset D_{m,N,H}(B)\cup E^{\le B}_{m,N,H}(x)\), where
  `D` is the raw large-drawdown event and `E^{≤B}` is the selected event with
  no drawdown greater than `B`.
- `measure_firstNSelectedEndpointBelow_le_of_drawdown` proves, when
  `m ≤ N`, `0 < B`, and the boundary is normalized,
  \[
  \mathbb P(E_{m,N,H}(x))\le
  N(H+1)^2e^{-B}+m e^x\,Q_{H,B,x},
  \]
  where \(Q_{H,B,x}\) is the tilted one-spine probability of no drawdown
  greater than `B` and endpoint at most `x`.
- `measure_firstNSelectedEndpointBelow_le_of_iidSpineBound` replaces
  \(Q_{H,B,x}\) in the same estimate by any supplied upper bound on the
  corresponding i.i.d. spine event. Both probability bounds use the
  finite-root product field law and the theorem's boundary-normalization
  hypothesis.

The event $E_{m,N,H}(x)$ that the first-`N` population from `m` roots has a
generation-`H` endpoint at most $x$ splits into a large ancestral drawdown and
a surviving selected endpoint with no such drawdown.  The public declarations
give measurability of $E_{m,N,H}(x)$, the pathwise split, the bound
\[
\mathbb P(E_{m,N,H}(x))\le
N(H+1)^2e^{-B}+m e^x\,\mathbb P(\text{one spine has no drop above }B
\text{ and ends at most }x),
\]
and its input-law form, which replaces the last probability by any supplied
i.i.d. spine bound.  The first term uses the selected-population drawdown
estimate, and the second uses the many-to-one estimate for a single root.

This finite-horizon decomposition follows equation (4.16) in the proof of
Proposition 3.1 of Elie Aïdékon and Yueyun Hu, *Average-weight percolation on
the complete graph*, arXiv:2512.23266 (2025).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown
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

private lemma rootPosition_eq_pathPotential (m : ℕ)
    (field : FiniteRootStepField m ℕ ℝ) (r : Fin m) (u : TreeNode ℕ) :
    RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field r u =
      Spine.pathPotential realPotential (field r) u := by
  simp [RootIndexed.position, RootIndexed.displace, Spine.pathPotential,
    realPotential]

private lemma pathHistory_coordinate_eq_rootPosition (m H : ℕ)
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
    have hdepth : p.2.length = H :=
      firstNSelectedPopulation_depth m N H field p hp
    have hsurvive : surviveAlong (field p.1) [] p.2 :=
      firstNSelectedPopulation_surviveAlong m N H field p hp
    have hnoDrop : historyHasNoLargeDrop B
        (Spine.pathHistory realPotential H 0 (field p.1) p.2) := by
      intro i j hij
      have hjH : j.val ≤ H := by omega
      have hselectedJ := firstNSelectedPopulation_prefix_mem
        m N H field p hp j.val hjH
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
theorem measure_firstNSelectedEndpointBelow_le_of_drawdown
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

/-- The spine's finite-history definition agrees with the natural-time
drawdown event used by the one-walk estimate. -/
private lemma spineNoLargeDropEndpointBelowEvent_eq_randomWalkEvent
    (n : ℕ) (delta threshold : ℝ) :
    spineNoLargeDropEndpointBelowEvent n delta threshold =
      noLargeDropEndpointBelowEvent n delta threshold := by
  ext increment
  change ProbabilityTheory.RandomWalk.historyNoLargeDropAndEndpointBelow
      delta threshold (ProbabilityTheory.RandomWalk.history n 0 increment) ↔
    (∀ i j : ℕ, i ≤ j → j ≤ n →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ delta) ∧
      AdditivePath.displacement n increment ≤ threshold
  constructor
  · rintro ⟨hdrop, hendpoint⟩
    refine ⟨?_, ?_⟩
    · intro i j hij hj
      let i' : Fin (n + 1) := ⟨i, by omega⟩
      let j' : Fin (n + 1) := ⟨j, by omega⟩
      have h := hdrop i' j' (by simp [i', j', hij])
      simpa [i', j', ProbabilityTheory.RandomWalk.history_apply] using h
    · simpa [ProbabilityTheory.RandomWalk.history_last,
        AdditivePath.fromIncrements, AdditivePath.displacement] using hendpoint
  · rintro ⟨hdrop, hendpoint⟩
    refine ⟨?_, ?_⟩
    · intro i j hij
      have h := hdrop i.val j.val hij (by omega)
      simpa [ProbabilityTheory.RandomWalk.history_apply] using h
    · simpa [ProbabilityTheory.RandomWalk.history_last,
        AdditivePath.fromIncrements, AdditivePath.displacement] using hendpoint

/-- The Aïdékon--Hu finite-horizon endpoint estimate with an external
i.i.d. spine bound supplied as input.  This form separates the branching
decomposition from the one-walk estimate used for its surviving term. -/
theorem measure_firstNSelectedEndpointBelow_le_of_iidSpineBound
    (m N H : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hmN : m ≤ N) (B threshold : ℝ) (hB : 0 < B)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    (bound : ℝ≥0∞)
    (hwalk : iidSequenceLaw ν
        (noLargeDropEndpointBelowEvent H B threshold) ≤ bound) :
    (finiteRootStepFieldLaw μ m)
        (firstNSelectedEndpointBelow m N H threshold) ≤
      (N : ℝ≥0∞) *
          (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) +
        (m : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp threshold) * bound) := by
  have hspine : (tiltedIncrementFieldLaw realPotential μ)
      (spineNoLargeDropEndpointBelowEvent H B threshold) ≤ bound := by
    rw [show tiltedIncrementFieldLaw realPotential μ = iidSequenceLaw ν by
      rw [hν]
      rfl,
      spineNoLargeDropEndpointBelowEvent_eq_randomWalkEvent]
    exact hwalk
  have hdecomp := measure_firstNSelectedEndpointBelow_le_of_drawdown
    m N H hmN B threshold hB μ hboundary
  calc
    (finiteRootStepFieldLaw μ m)
        (firstNSelectedEndpointBelow m N H threshold) ≤
      (N : ℝ≥0∞) *
          (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) +
        (m : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp threshold) *
            (tiltedIncrementFieldLaw realPotential μ)
              (spineNoLargeDropEndpointBelowEvent H B threshold)) := hdecomp
    _ ≤ (N : ℝ≥0∞) *
          (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) +
        (m : ℝ≥0∞) * (ENNReal.ofReal (Real.exp threshold) * bound) := by
      have htail :
          (m : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp threshold) *
                (tiltedIncrementFieldLaw realPotential μ)
                  (spineNoLargeDropEndpointBelowEvent H B threshold)) ≤
            (m : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp threshold) * bound) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hspine (by positivity)) (by positivity)
      simpa [add_comm] using add_le_add_left htail
        ((N : ℝ≥0∞) * (((H : ℝ≥0∞) + 1) ^ 2 *
          ENNReal.ofReal (Real.exp (-B))))

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
