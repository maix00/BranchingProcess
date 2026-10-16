/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.Success.GoodSplit
import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
import Probability.BranchingRandomWalk.Spine.Generation

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
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris

section PathwiseBound

variable {Root α X : Type*} [LinearOrder α] [OrderBot α]
  [MeasurableSpace X]

/-- Appending one slot adds the potential of the edge at the current address.
-/
theorem spinePathPotential_append_singleton
    (φ : Potential X) (ω : StepField α X) (p : TreeNode α) (i : α) :
    Spine.pathPotential φ ω (p ++ [i]) =
      Spine.pathPotential φ ω p +
        (ω p).potentialValue' φ i := by
  unfold Spine.pathPotential Combinatorics.Branching.displaceWith
  rw [Combinatorics.Branching.displace_append]
  simp [Combinatorics.Branching.displace,
    Step.potentialValue', Step.potentialAt?, value']

/-- The potential of the edge selected by the reserve-spine rule at time `n`.
-/
noncomputable def selectedReserveSpineEdgePotential
    (S : Step.FiniteSelection α X) (φ : Potential X) (r : Root)
    (n : ℕ) : RootIndexed.StepField Root α X → ℝ :=
  fun ω => (ω r (selectedReserveSpinePath S r n ω)).potentialValue' φ
    (reserveSpineSlot S (ω r (selectedReserveSpinePath S r n ω)))

/-- At one reserve step, a split edge is cutoff-bounded; if there is no split,
the chosen edge is the original first selected child. -/
theorem reserveSpineSlot_potential_le_cutoff_add_firstChildPositive
    (R : Step.FiniteSelection α X) (hR : R.IsBoundedBy 2)
    (φ : Potential X) (M : ℝ) (hM : 0 ≤ M) (ξ : Step α X)
    (hordered : ξ.IsOrderedBy φ) (hne : (R ξ).Nonempty) :
    (ξ.potentialValue' φ
      (reserveSpineSlot (reserveSelectionBelowPotential R φ M) ξ)) ≤
        M + max 0 (ξ.potentialValue' φ (firstSelectedSlot R ξ)) := by
  let S := reserveSelectionBelowPotential R φ M
  have hfirstR : firstSelectedSlot R ξ ∈ R ξ :=
    firstSelectedSlot_mem R ξ hne
  have hfirstOnly : firstSelectedSlot R ξ ∈ firstOnlySelectedChild R ξ := by
    rw [firstOnlySelectedChild, Step.FiniteSelection.mem_filter]
    exact ⟨hfirstR, rfl⟩
  have hfirstS : firstSelectedSlot R ξ ∈ S ξ := by
    change firstSelectedSlot R ξ ∈ reserveSelectionBelowPotential R φ M ξ
    rw [reserveSelectionBelowPotential]
    exact Finset.mem_union.mpr (Or.inl hfirstOnly)
  have hS_nonempty : (S ξ).Nonempty := ⟨firstSelectedSlot R ξ, hfirstS⟩
  by_cases hsplit : 2 ≤ (S ξ).card
  · have hsplit' : ξ ∈ splitBy S := hsplit
    rw [reserveSpineSlot_eq_second_of_split S ξ hsplit]
    obtain ⟨_, hsecond⟩ :=
      reserveSelectionBelowPotential_split_edgePotentials_le_of_ordered
        R hR φ M ξ hordered hsplit'
    exact hsecond.trans (le_add_of_nonneg_right (le_max_left 0
      (ξ.potentialValue' φ (firstSelectedSlot R ξ))))
  · have hcard : (S ξ).card = 1 := by
      have hpos : 0 < (S ξ).card := Finset.card_pos.mpr hS_nonempty
      omega
    rw [reserveSpineSlot_eq_first_of_singleton S ξ hcard]
    have hfirstS_mem := firstSelectedSlot_mem S ξ hS_nonempty
    have hfirstEq : firstSelectedSlot S ξ = firstSelectedSlot R ξ := by
      by_contra hne'
      have htwo : 1 < (S ξ).card :=
        Finset.one_lt_card_iff.mpr
          ⟨firstSelectedSlot S ξ, firstSelectedSlot R ξ,
            hfirstS_mem, hfirstS, hne'⟩
      omega
    rw [hfirstEq]
    exact le_trans (le_max_right _ _) (le_add_of_nonneg_left hM)

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
      rw [spinePathPotential_append_singleton]
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
    simpa [edge, rawPositive, selectedReserveSpineEdgePotential, S] using
      reserveSpineSlot_potential_le_cutoff_add_firstChildPositive
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

theorem selectedReserveSpineRestartSourceSlice_contains_live_spine
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (halive : selectedReserveSpineAlive R r n ω) :
    (r, selectedReserveSpinePath R r n ω) ∈
      selectedReserveSpineRestartSourceSlice R growth hR cap duration r n ω := by
  simp [selectedReserveSpineRestartSourceSlice, halive]

theorem selectedReserveSpineRestartSourceMinPosition_le_live_spine
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (φ : Potential X) (cap duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (halive : selectedReserveSpineAlive R r n ω) :
    selectedReserveSpineRestartSourceMinPosition R growth hR φ cap duration
      r n ω ≤ Spine.pathPotential φ (ω r)
        (selectedReserveSpinePath R r n ω) := by
  let values := (selectedReserveSpineRestartSourceSlice R growth hR cap duration
      r n ω).image (fun q => Spine.pathPotential φ (ω q.1) q.2)
  have hmem : Spine.pathPotential φ (ω r)
      (selectedReserveSpinePath R r n ω) ∈ values := by
    apply Finset.mem_image.mpr
    refine ⟨(r, selectedReserveSpinePath R r n ω), ?_, rfl⟩
    exact selectedReserveSpineRestartSourceSlice_contains_live_spine
      R growth hR cap duration r n ω halive
  have hne : values.Nonempty := ⟨_, hmem⟩
  unfold selectedReserveSpineRestartSourceMinPosition
  dsimp only
  rw [dif_pos hne]
  exact Finset.min'_le values _ hmem

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
  have hminimum := selectedReserveSpineRestartSourceMinPosition_le_live_spine
    S growth hS φ cap duration r n ω halive
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
