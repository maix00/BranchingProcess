/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Tree.Line.Information.Localization
public import Probability.Process.Tree.Line.Information.Coordinates

/-!
# Birth states observed on an optional line

## Public declarations

In `ProbabilityTheory.Tree`, for `past = linePast initial coordinate`:

* `IsOptionalLine.measurableSet_inter_mem_of_ancestralPast`: an event `A`
  observable at the birth of `u` satisfies `A ∩ {u ∈ L} ∈ F_L`.
* `IsOptionalLine.measurable_boundary_state`: `X_u` on `{u ∈ L}` and a
  fixed default elsewhere is measurable in `F_L`; the line may be empty.
* `IsOptionalLine.measurable_selected_state`: if `R ∈ L` is chosen measurably
  from `F_L`, with countable range, and each `X_u` is measurable at the birth
  of `u`, then `ω ↦ X_(R(ω))(ω)` is measurable in `F_L`.

The birth information is `ancestralPast`: it includes initial information and
strict ancestors' reproduction observations. It contains the node's inherited
state, without exposing its own reproduction or later descendants. The line
itself is merely optional; its membership need not be ancestrally determined.
Only the selected node needs countable range, not the entire optional line or
its node space. There is no probability law or standard-Borel assumption.

This is the boundary-state measurability needed in the conditional product
formula of P. Jagers and A. N. Lagerås, *General branching processes conditioned
on extinction are still branching processes* (2008), §2.2–2.3, pp. 542–543,
DOI 10.1214/ECP.v13-1419, following P. Jagers, *General branching processes as
Markov fields* (1989), Theorem 4.14, DOI 10.1016/0304-4149(89)90075-6.
It does not assume or establish conditional independence of descendant trees.
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open Classical MeasureTheory Combinatorics.UlamHarris

variable {Ω Root α : Type*}
  (initial : MeasurableSpace Ω)
  (coordinate : RootIndexed.TreeNode Root α → MeasurableSpace Ω)
  [mΩ : MeasurableSpace Ω]
  (hi : initial ≤ mΩ) (hc : ∀ u, coordinate u ≤ mΩ)
  {L : Ω → Set (RootIndexed.TreeNode Root α)}

include hi hc in
/-- A birth-observable event restricted to membership in an optional line is known at that line. -/
theorem IsOptionalLine.measurableSet_inter_mem_of_ancestralPast
    (h : @IsOptionalLine Ω Root α mΩ (linePast initial coordinate) L)
    (u : RootIndexed.TreeNode Root α) {A : Set Ω}
    (hA : MeasurableSet[ancestralPast initial coordinate u] A) :
    MeasurableSet[h.measurableSpace] (A ∩ {ω | u ∈ L ω}) := by
  have hAm : MeasurableSet[mΩ] A := ancestralPast_le initial coordinate hi hc u _ hA
  refine ⟨hAm.inter (h.toIsRandomLine.measurableSet_mem u), fun q hq => ?_⟩
  by_cases hex : ∃ v ∈ q, RootIndexed.IsAncestor v u ∧ v ≠ u
  · obtain ⟨v, hv, hvu, hne⟩ := hex
    have heq : (A ∩ {ω | u ∈ L ω}) ∩
        {ω | RootIndexed.Line.Precedes (L ω) q} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨⟨_, hu⟩, hp⟩
      obtain ⟨w, hw, hwv⟩ := hp v hv
      have hwu : w = u := (h.isLine ω).eq hw hu (hwv.trans hvu)
      subst w
      exact hne (hvu.antisymm hwv)
    rw [heq]
    exact @MeasurableSet.empty Ω (linePast initial coordinate q)
  · have hno : ∀ v ∈ q, RootIndexed.IsAncestor v u → v = u := by
      intro v hv hvu
      by_contra hne
      exact hex ⟨v, hv, hvu, hne⟩
    have hAq := ancestralPast_le_linePast_of_no_strict_ancestor initial coordinate hno _ hA
    have hm := h.measurableSet_subset_stopped
      (fun _ _ hp => linePast_mono initial coordinate hp) {u} (Set.countable_singleton u)
    have hmem : MeasurableSet[linePast initial coordinate q]
        ({ω | u ∈ L ω} ∩ {ω | RootIndexed.Line.Precedes (L ω) q}) := by
      simpa only [Set.singleton_subset_iff] using hm.2 q hq
    rw [Set.inter_assoc]
    exact hAq.inter hmem

include hi hc in
/-- A fixed node's birth state, censored outside the optional line, is observable
without an enumeration or a fixed cardinality of the random line. -/
theorem IsOptionalLine.measurable_boundary_state
    {S : Type*} [MeasurableSpace S]
    (h : @IsOptionalLine Ω Root α mΩ (linePast initial coordinate) L)
    (u : RootIndexed.TreeNode Root α) (state : Ω → S)
    (hstate : Measurable[ancestralPast initial coordinate u] state) (default : S) :
    Measurable[h.measurableSpace] (fun ω => if u ∈ L ω then state ω else default) := by
  classical
  have hmem : MeasurableSet[h.measurableSpace] {ω | u ∈ L ω} := by
    simpa only [Set.singleton_subset_iff] using h.measurableSet_subset_stopped
      (fun _ _ hp => linePast_mono initial coordinate hp) {u} (Set.countable_singleton u)
  intro B hB
  have hb := h.measurableSet_inter_mem_of_ancestralPast initial coordinate hi hc u (hstate hB)
  by_cases hdefault : default ∈ B
  · have heq : (fun ω => if u ∈ L ω then state ω else default) ⁻¹' B =
        (state ⁻¹' B ∩ {ω | u ∈ L ω}) ∪ {ω | u ∈ L ω}ᶜ := by
      ext ω
      by_cases hu : u ∈ L ω <;> simp [hu, hdefault]
    rw [heq]
    exact hb.union hmem.compl
  · have heq : (fun ω => if u ∈ L ω then state ω else default) ⁻¹' B =
        state ⁻¹' B ∩ {ω | u ∈ L ω} := by
      ext ω
      by_cases hu : u ∈ L ω <;> simp [hu, hdefault]
    rw [heq]
    exact hb

include hi hc in
/-- A countable-range observed choice of a vertex on the optional line has its
inherited state observable in the stopped information. -/
theorem IsOptionalLine.measurable_selected_state
    {S : Type*} [MeasurableSpace S]
    (h : @IsOptionalLine Ω Root α mΩ (linePast initial coordinate) L)
    (state : RootIndexed.TreeNode Root α → Ω → S)
    (hstate : ∀ u, Measurable[ancestralPast initial coordinate u] (state u))
    (choice : Ω → RootIndexed.TreeNode Root α) (hcount : (Set.range choice).Countable)
    (hchoice : ∀ u, MeasurableSet[h.measurableSpace] {ω | choice ω = u})
    (hmem : ∀ ω, choice ω ∈ L ω) :
    Measurable[h.measurableSpace] (fun ω => state (choice ω) ω) := by
  intro B hB
  have hcell (u : RootIndexed.TreeNode Root α) : MeasurableSet[h.measurableSpace]
      ({ω | choice ω = u} ∩ (state u ⁻¹' B ∩ {ω | u ∈ L ω})) :=
    (hchoice u).inter (h.measurableSet_inter_mem_of_ancestralPast initial coordinate hi hc
      u ((hstate u) hB))
  have heq : (fun ω => state (choice ω) ω) ⁻¹' B =
      ⋃ u ∈ Set.range choice, {ω | choice ω = u} ∩ (state u ⁻¹' B ∩ {ω | u ∈ L ω}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hω
      exact ⟨choice ω, ⟨ω, rfl⟩, rfl, hω, hmem ω⟩
    · rintro ⟨u, _, he, hB, _⟩
      simpa only [he] using hB
  rw [heq]
  exact MeasurableSet.biUnion hcount (fun u _ => hcell u)

end ProbabilityTheory.Tree

end
