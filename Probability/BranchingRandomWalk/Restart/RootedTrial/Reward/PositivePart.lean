/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.Success.GoodSplit
import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
import Probability.BranchingRandomWalk.Restart.RootedTrial.Spine.ReservePath
import Probability.BranchingRandomWalk.Spine.Generation
import Probability.BranchingRandomWalk.Spine.GenerationBranching.Decomposition

/-!
# Positive-part bound for the causal reserve source

The causal reserve source contains its live reserve spine at every generation.
At a split, both edges retained by the truncated reserve selector have
potential at most the cutoff.  At a nonsplit, its only retained edge is the
original first selected child.  The spine position is therefore bounded by a
linear cutoff term plus the positive parts of the original first-child marks
sampled along that spine.

This is a pathwise estimate for `selectedReserveSpineRestartSourceSlice`.  It
does not identify that causal source with the retrospectively restarted
process,
and it does not assert that the adaptively sampled marks have the iid
`Xi₁` law.

## Public declarations

For a live reserve spine with nonempty ordered offspring through generation
\(n\), the pathwise positive-part estimate is

\[\max\{0,S_n\}
  \le Mn+\sum_{k=0}^{n-1}
    \max\{0,\,\phi(\text{first selected edge at }k)\}.\]

- `selectedReserveSpineEdgePotential`,
  `selectedReserveSpinePath_potential_eq_sum_edges`, and
  `selectedReserveSpinePath_positivePart_le_cutoff_add_firstChildSum`:
  pathwise edge decomposition and positive-part bound for the reserve spine.
- `selectedReserveSpineRestartSourceMinPosition`,
  `selectedReserveSpineRestartSourceMinPosition_positivePart_le`: the live
  spine belongs to the restart-source slice, whose minimum position satisfies
  the cutoff-plus-positive-increments estimate.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection

attribute [local instance] Classical.propDecidable Classical.decEq

section PathwiseBound

variable {Root α X : Type*} [LinearOrder α] [OrderBot α]
  [MeasurableSpace X]

/-- The potential of the edge selected by the reserve-spine rule at time `n`.
-/
noncomputable def selectedReserveSpineEdgePotential
    (S : Step.FiniteSelection α X) (φ : Potential X) (r : Root)
    (n : ℕ) : RootIndexed.StepField Root α X → ℝ :=
  fun ω => (ω r (selectedReserveSpinePath S r n ω)).potentialValue' φ
    (reserveSpineSlot S (ω r (selectedReserveSpinePath S r n ω)))

/-- The path potential is the sum of the reserve-spine edge potentials.
-/
theorem selectedReserveSpinePath_potential_eq_sum_edges
    (S : Step.FiniteSelection α X) (φ : Potential X) (r : Root)
    (n : ℕ) (ω : RootIndexed.StepField Root α X) :
    Spine.pathPotential φ (ω r) (selectedReserveSpinePath S r n ω) =
      ∑ k ∈ Finset.range n, selectedReserveSpineEdgePotential S φ r k ω := by
  induction n with
  | zero => simp [selectedReserveSpineEdgePotential, selectedReserveSpinePath,
      Spine.pathPotential]
  | succ n ih =>
      rw [show selectedReserveSpinePath S r (n + 1) ω =
        selectedReserveSpinePath S r n ω ++
          [reserveSpineSlot S (ω r (selectedReserveSpinePath S r n ω))] by rfl]
      rw [Spine.pathPotential_append]
      simp only [Spine.pathPotential_singleton, subtreeStepField,
        List.append_nil]
      rw [Finset.sum_range_succ]
      simpa [selectedReserveSpineEdgePotential] using congrArg
        (fun x : ℝ => x +
          (ω r (selectedReserveSpinePath S r n ω)).potentialValue' φ
            (reserveSpineSlot S (ω r (selectedReserveSpinePath S r n ω)))
        ) ih

/-- Pathwise positive-part bound for the reserve spine associated with the
truncated selector.  The terms on the right are the raw first-child marks at
the adaptively visited spine vertices; no independence is asserted here.
-/
theorem selectedReserveSpinePath_positivePart_le_cutoff_add_firstChildSum
    (R : Step.FiniteSelection α X) (hR : R.IsBoundedBy 2)
    (φ : Potential X) (M : ℝ) (hM : 0 ≤ M) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hordered : ∀ k < n,
      (ω r (selectedReserveSpinePath
        (reserveSelectionBelowPotential R φ M) r k ω)).IsOrderedBy φ)
    (hnonempty : ∀ k < n,
      (R (ω r (selectedReserveSpinePath
        (reserveSelectionBelowPotential R φ M) r k ω))).Nonempty) :
    max 0 (Spine.pathPotential φ (ω r)
      (selectedReserveSpinePath (reserveSelectionBelowPotential R φ M) r n ω)) ≤
        M * n + ∑ k ∈ Finset.range n,
          max 0 ((ω r (selectedReserveSpinePath
            (reserveSelectionBelowPotential R φ M) r k ω)).potentialValue' φ
              (firstSelectedSlot R (ω r (selectedReserveSpinePath
                (reserveSelectionBelowPotential R φ M) r k ω)))) := by
  let S := reserveSelectionBelowPotential R φ M
  let edge := selectedReserveSpineEdgePotential S φ r
  let rawPositive := fun k => max 0 ((ω r (selectedReserveSpinePath S r k ω)).potentialValue' φ
    (firstSelectedSlot R (ω r (selectedReserveSpinePath S r k ω))))
  have hsum : (∑ k ∈ Finset.range n, edge k ω) ≤
      ∑ k ∈ Finset.range n, (M + rawPositive k) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    simpa [edge, rawPositive, selectedReserveSpineEdgePotential, S,
      firstSelectedSlotPositivePotential] using
      potentialValue'_reserveSpineSlot_le_cutoff_add_firstSelectedSlotPositive
        R hR φ M hM (ω r (selectedReserveSpinePath S r k ω))
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
  rw [selectedReserveSpinePath_potential_eq_sum_edges]
  calc
    max 0 (∑ k ∈ Finset.range n, edge k ω) ≤
        ∑ k ∈ Finset.range n, (M + rawPositive k) :=
      max_le hnonneg hsum
    _ = M * n + ∑ k ∈ Finset.range n, rawPositive k := hright

end PathwiseBound

section CausalSourceMinimum

variable {Root α X : Type*} [Countable α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
  [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]

/-- Minimum potential in the implemented causal reserve-source slice, with
the empty slice totalized to zero. -/
noncomputable def selectedReserveSpineRestartSourceMinPosition
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (φ : Potential X) (cap duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) : ℝ :=
  let values := (selectedReserveSpineRestartSourceSlice R growth hR cap duration
      r n ω).image (fun q => Spine.pathPotential φ (ω q.1) q.2)
  if h : values.Nonempty then values.min' h else 0

/-- The implemented causal source has the same positive-part estimate as its
live reserve spine. This bound is pathwise; it makes no iid claim about the
adaptive first-child marks and does not identify the source with the
retrospectively restarted process. -/
theorem selectedReserveSpineRestartSourceMinPosition_positivePart_le
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hRcap : R.IsBoundedBy 2) (φ : Potential X) (M : ℝ) (hM : 0 ≤ M)
    (cap duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hordered : ∀ k < n,
      (ω r (selectedReserveSpinePath
        (reserveSelectionBelowPotential R φ M) r k ω)).IsOrderedBy φ)
    (hnonempty : ∀ k < n,
      (R (ω r (selectedReserveSpinePath
        (reserveSelectionBelowPotential R φ M) r k ω))).Nonempty) :
    max 0 (selectedReserveSpineRestartSourceMinPosition
      (reserveSelectionBelowPotential R φ M) growth
      (reserveSelectionBelowPotential_measurable R hR φ M) φ cap duration
      r n ω) ≤
        M * n + ∑ k ∈ Finset.range n,
          max 0 ((ω r (selectedReserveSpinePath
            (reserveSelectionBelowPotential R φ M) r k ω)).potentialValue' φ
              (firstSelectedSlot R (ω r (selectedReserveSpinePath
                (reserveSelectionBelowPotential R φ M) r k ω)))) := by
  let S := reserveSelectionBelowPotential R φ M
  have hS : Measurable S.select := by
    simpa [S] using reserveSelectionBelowPotential_measurable R hR φ M
  have halive : selectedReserveSpineAlive S r n ω := by
    induction n with
    | zero => simp [selectedReserveSpineAlive]
    | succ n ih =>
        have horderedPrev : ∀ k < n,
            (ω r (selectedReserveSpinePath S r k ω)).IsOrderedBy φ := by
          intro k hk
          exact hordered k (by omega)
        have hnonemptyPrev : ∀ k < n,
            (R (ω r (selectedReserveSpinePath S r k ω))).Nonempty := by
          intro k hk
          exact hnonempty k (by omega)
        have hprev : selectedReserveSpineAlive S r n ω :=
          ih horderedPrev hnonemptyPrev
        have hlastRaw :
            (R (ω r (selectedReserveSpinePath S r n ω))).Nonempty :=
          hnonempty n (by omega)
        have hlast := reserveSelectionBelowPotential_nonempty_of_selected_nonempty
          R φ M (ω r (selectedReserveSpinePath S r n ω)) hlastRaw
        exact ⟨hprev, hlast⟩
  let values := (selectedReserveSpineRestartSourceSlice S growth hS cap duration
      r n ω).image (fun q => Spine.pathPotential φ (ω q.1) q.2)
  have hmem : Spine.pathPotential φ (ω r)
      (selectedReserveSpinePath S r n ω) ∈ values := by
    apply Finset.mem_image.mpr
    refine ⟨(r, selectedReserveSpinePath S r n ω), ?_, rfl⟩
    exact selectedReserveSpineRestartSourceSlice_contains_live_spine
      S growth hS cap duration r n ω halive
  have hvalues : values.Nonempty := ⟨_, hmem⟩
  have hminimum : selectedReserveSpineRestartSourceMinPosition S growth hS φ
      cap duration r n ω ≤ Spine.pathPotential φ (ω r)
        (selectedReserveSpinePath S r n ω) := by
    unfold selectedReserveSpineRestartSourceMinPosition
    dsimp only
    rw [dite_eq_left hvalues]
    exact Finset.min'_le values _ hmem
  have hpath := selectedReserveSpinePath_positivePart_le_cutoff_add_firstChildSum
    R hRcap φ M hM r n ω (by simpa [S] using hordered)
    (by simpa [S] using hnonempty)
  calc
    max 0 (selectedReserveSpineRestartSourceMinPosition S growth hS φ cap
        duration r n ω) ≤
      max 0 (Spine.pathPotential φ (ω r) (selectedReserveSpinePath S r n ω)) :=
        max_le_max le_rfl hminimum
    _ ≤ M * n + ∑ k ∈ Finset.range n,
        max 0 ((ω r (selectedReserveSpinePath S r k ω)).potentialValue' φ
          (firstSelectedSlot R (ω r (selectedReserveSpinePath S r k ω)))) := by
        simpa [S] using hpath

end CausalSourceMinimum

end ProbabilityTheory.BranchingRandomWalk
