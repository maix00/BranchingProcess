/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.Success.GoodSplit
import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Causal
import Probability.BranchingRandomWalk.Restart.SelectedPath.Path
import Probability.BranchingRandomWalk.Spine.Generation
import Probability.BranchingRandomWalk.Spine.GenerationBranching.Decomposition

/-!
# Positive-part bound for the selected-path BRW population

The selected-path BRW population contains its live selected path at every
generation.
At a split, the truncated selector chooses both selected edges with
potential at most the cutoff. At a nonsplit, it chooses only the original
first selected child.  The selected path position is therefore bounded by a
linear cutoff term plus the positive parts of the original first-child marks
sampled along that selected path.

This pathwise estimate concerns `Restart.SelectedPath.Population.slice`
and its live selected path. The retrospectively restarted BRW and the law of
adaptively sampled marks are handled separately.

## Internal proof declarations

For a live selected path with nonempty ordered offspring through generation
\(n\), the pathwise positive-part estimate is

\[\max\{0,S_n\}
  \le Mn+\sum_{k=0}^{n-1}
    \max\{0,\,\phi(\text{first selected edge at }k)\}.\]

- `potential_eq_sum_edges` gives the selected-path potential as the sum of its
  edge potentials; `positivePart_le_cutoff_add_firstSelectedChildSum` proves
  \[
    (S_n)^+\le Mn+\sum_{k<n}(\phi(\text{first selected edge at }k))^+.
  \]
- `minPosition_positivePart_le` transfers this estimate to the minimum position
  of the selected-path BRW population slice.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection

attribute [local instance] Classical.propDecidable Classical.decEq

section PathwiseBound

variable {Root α X : Type*} [LinearOrder α] [OrderBot α]
  [MeasurableSpace X]

/-- The potential of the edge selected by the selected-path rule at time `n`.
-/
private noncomputable def edgePotential
    (S : Step.FiniteSelection α X) (φ : Potential X) (r : Root)
    (n : ℕ) : RootIndexed.StepField Root α X → ℝ :=
  fun ω => (ω r (Restart.selectedPath S r n ω)).potentialValue' φ
    (selectedContinuationSlot S (ω r (Restart.selectedPath S r n ω)))

/-- The path potential is the sum of the selected-path edge potentials.
-/
lemma potential_eq_sum_edges
    (S : Step.FiniteSelection α X) (φ : Potential X) (r : Root)
    (n : ℕ) (ω : RootIndexed.StepField Root α X) :
    Spine.pathPotential φ (ω r) (Restart.selectedPath S r n ω) =
      ∑ k ∈ Finset.range n, edgePotential S φ r k ω := by
  induction n with
  | zero => simp [edgePotential, Restart.selectedPath,
      Spine.pathPotential]
  | succ n ih =>
      rw [show Restart.selectedPath S r (n + 1) ω =
        Restart.selectedPath S r n ω ++
          [selectedContinuationSlot S (ω r (Restart.selectedPath S r n ω))] by rfl]
      rw [Spine.pathPotential_append]
      simp only [Spine.pathPotential_singleton, subtreeStepField,
        List.append_nil]
      rw [Finset.sum_range_succ]
      simpa [edgePotential] using congrArg
        (fun x : ℝ => x +
          (ω r (Restart.selectedPath S r n ω)).potentialValue' φ
            (selectedContinuationSlot S (ω r (Restart.selectedPath S r n ω)))
        ) ih

/-- Pathwise positive-part bound for the selected path associated with the
truncated selector.  The terms on the right are the raw first-child marks at
the adaptively visited selected path vertices; no independence is asserted here.
-/
lemma positivePart_le_cutoff_add_firstSelectedChildSum
    (R : Step.FiniteSelection α X) (hR : R.IsBoundedBy 2)
    (φ : Potential X) (M : ℝ) (hM : 0 ≤ M) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hordered : ∀ k < n,
      (ω r (Restart.selectedPath
        (reserveSelectionBelowPotential R φ M) r k ω)).IsOrderedBy φ)
    (hnonempty : ∀ k < n,
      (R (ω r (Restart.selectedPath
        (reserveSelectionBelowPotential R φ M) r k ω))).Nonempty) :
    max 0 (Spine.pathPotential φ (ω r)
      (Restart.selectedPath (reserveSelectionBelowPotential R φ M) r n ω)) ≤
        M * n + ∑ k ∈ Finset.range n,
          max 0 ((ω r (Restart.selectedPath
            (reserveSelectionBelowPotential R φ M) r k ω)).potentialValue' φ
              (firstSelectedSlot R (ω r (Restart.selectedPath
                (reserveSelectionBelowPotential R φ M) r k ω)))) := by
  let S := reserveSelectionBelowPotential R φ M
  let edge := edgePotential S φ r
  let rawPositive := fun k => max 0 ((ω r (Restart.selectedPath S r k ω)).potentialValue' φ
    (firstSelectedSlot R (ω r (Restart.selectedPath S r k ω))))
  have hsum : (∑ k ∈ Finset.range n, edge k ω) ≤
      ∑ k ∈ Finset.range n, (M + rawPositive k) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    simpa [edge, rawPositive, edgePotential, S,
      firstSelectedSlotPositivePotential] using
      potentialValue'_selectedContinuationSlot_le_cutoff_add_firstSelectedSlotPositive
        R hR φ M hM (ω r (Restart.selectedPath S r k ω))
        (hordered k hk') (hnonempty k hk')
  have hright : (∑ k ∈ Finset.range n, (M + rawPositive k)) =
      M * n + ∑ k ∈ Finset.range n, rawPositive k := by
    simp [Finset.sum_add_distrib, rawPositive]
    ring
  have hterms : ∀ k ∈ Finset.range n, 0 ≤ M + rawPositive k := by
    intro k hk
    exact add_nonneg hM (le_max_left 0 _)
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range n, (M + rawPositive k) :=
    Finset.sum_nonneg hterms
  rw [potential_eq_sum_edges]
  calc
    max 0 (∑ k ∈ Finset.range n, edge k ω) ≤
        ∑ k ∈ Finset.range n, (M + rawPositive k) :=
      max_le hnonneg hsum
    _ = M * n + ∑ k ∈ Finset.range n, rawPositive k := hright

end PathwiseBound

section SelectedPathMinimum

variable {Root α X : Type*} [Countable α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
  [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]

/-- Minimum potential in the implemented selected-path BRW slice, with
the empty slice totalized to zero. -/
private noncomputable def minPosition
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (φ : Potential X) (cap duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) : ℝ :=
  let values := (Restart.SelectedPath.Population.slice R growth hR cap duration
      r n ω).image (fun q => Spine.pathPotential φ (ω q.1) q.2)
  if h : values.Nonempty then values.min' h else 0

/-- The implemented selected BRW population has the same positive-part estimate as its
live selected path. This bound is pathwise; it makes no iid claim about the
adaptive first-child marks and the retrospectively restarted BRW is treated separately. -/
lemma minPosition_positivePart_le
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hRcap : R.IsBoundedBy 2) (φ : Potential X) (M : ℝ) (hM : 0 ≤ M)
    (cap duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hordered : ∀ k < n,
      (ω r (Restart.selectedPath
        (reserveSelectionBelowPotential R φ M) r k ω)).IsOrderedBy φ)
    (hnonempty : ∀ k < n,
      (R (ω r (Restart.selectedPath
        (reserveSelectionBelowPotential R φ M) r k ω))).Nonempty) :
    max 0 (minPosition
      (reserveSelectionBelowPotential R φ M) growth
      (reserveSelectionBelowPotential_measurable R hR φ M) φ cap duration
      r n ω) ≤
        M * n + ∑ k ∈ Finset.range n,
          max 0 ((ω r (Restart.selectedPath
            (reserveSelectionBelowPotential R φ M) r k ω)).potentialValue' φ
              (firstSelectedSlot R (ω r (Restart.selectedPath
                (reserveSelectionBelowPotential R φ M) r k ω)))) := by
  let S := reserveSelectionBelowPotential R φ M
  have hS : Measurable S.select := by
    simpa [S] using reserveSelectionBelowPotential_measurable R hR φ M
  have halive : Restart.SelectedPath.isAlive S r n ω := by
    induction n with
    | zero => simp [Restart.SelectedPath.isAlive]
    | succ n ih =>
        have horderedPrev : ∀ k < n,
            (ω r (Restart.selectedPath S r k ω)).IsOrderedBy φ := by
          intro k hk
          exact hordered k (by omega)
        have hnonemptyPrev : ∀ k < n,
            (R (ω r (Restart.selectedPath S r k ω))).Nonempty := by
          intro k hk
          exact hnonempty k (by omega)
        have hprev : Restart.SelectedPath.isAlive S r n ω :=
          ih horderedPrev hnonemptyPrev
        have hlastRaw :
            (R (ω r (Restart.selectedPath S r n ω))).Nonempty :=
          hnonempty n (by omega)
        have hlast := reserveSelectionBelowPotential_nonempty_of_selected_nonempty
          R φ M (ω r (Restart.selectedPath S r n ω)) hlastRaw
        exact ⟨hprev, hlast⟩
  let values := (Restart.SelectedPath.Population.slice S growth hS cap duration
      r n ω).image (fun q => Spine.pathPotential φ (ω q.1) q.2)
  have hmem : Spine.pathPotential φ (ω r)
      (Restart.selectedPath S r n ω) ∈ values := by
    apply Finset.mem_image.mpr
    refine ⟨(r, Restart.selectedPath S r n ω), ?_, rfl⟩
    exact Restart.SelectedPath.Population.slice_contains_selectedPath
      S growth hS cap duration r n ω halive
  have hvalues : values.Nonempty := ⟨_, hmem⟩
  have hminimum : minPosition S growth hS φ
      cap duration r n ω ≤ Spine.pathPotential φ (ω r)
        (Restart.selectedPath S r n ω) := by
    unfold minPosition
    dsimp only
    rw [dite_eq_left hvalues]
    exact Finset.min'_le values _ hmem
  have hpath := positivePart_le_cutoff_add_firstSelectedChildSum
    R hRcap φ M hM r n ω (by simpa [S] using hordered)
    (by simpa [S] using hnonempty)
  calc
    max 0 (minPosition S growth hS φ cap
        duration r n ω) ≤
      max 0 (Spine.pathPotential φ (ω r) (Restart.selectedPath S r n ω)) :=
        max_le_max le_rfl hminimum
    _ ≤ M * n + ∑ k ∈ Finset.range n,
        max 0 ((ω r (Restart.selectedPath S r k ω)).potentialValue' φ
          (firstSelectedSlot R (ω r (Restart.selectedPath S r k ω)))) := by
        simpa [S] using hpath

end SelectedPathMinimum

end ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Lemmas
