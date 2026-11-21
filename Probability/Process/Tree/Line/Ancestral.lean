/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Tree.Line.Optional
public import Probability.Process.Tree.Line.Information.Coordinates

/-!
# Stopping lines decided along ancestral paths

## Public declarations

In `ProbabilityTheory.Tree`:

* `IsAncestralStoppingLine history L` is a random line with `{ω | u ∈ L ω}`
  measurable in the explicitly supplied ancestral information `history u`.
* `IsAncestralStoppingLine.const` constructs constant stopping lines;
  `IsAncestralStoppingLine.mono` enlarges the nodewise information.
* `IsAncestralStoppingLine.inter` and `IsAncestralStoppingLine.restrict`
  preserve the property under intersection with another such line or a fixed set.
* `IsAncestralStoppingLine.measurableSet_precedes` proves measurability of
  `{L ≼ ℓ}` for a countable test set `ℓ`, if `history u ≤ past` for every
  ancestor `u` of each `v ∈ ℓ`. Each node has finitely many ancestors, so no
  countability assumption on the whole address space is needed here.
* `IsAncestralStoppingLine.isOptionalLine` assembles this criterion for all
  test lines when `Root` and `α` are countable.
* `IsAncestralStoppingLine.isOptionalLine_linePast` specializes it to
  `history = ancestralPast initial coordinate` and
  `past = linePast initial coordinate`, with countable roots and child indices.

A. E. Kyprianou, *Martingale convergence and the stopped branching random walk*
(2000), §2, Definition 1, p. 408,
[DOI:10.1007/s004409900036](https://doi.org/10.1007/s004409900036), uses an
inclusive ancestral history. It is instantiated here by `ancestralHistory`.
The last theorem instead explicitly uses strict ancestral information
`ancestralPast`, available before the stopping node reproduces. It makes no
claim that adding the node's own future reproduction preserves optionality.
No probability law, moment, or independence assumptions are imposed.
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open MeasureTheory Combinatorics.UlamHarris

variable {Ω Root α : Type*} [mΩ : MeasurableSpace Ω]

/-- Nodewise stopping decisions with the available ancestral information stated explicitly. -/
structure IsAncestralStoppingLine
    (history : RootIndexed.TreeNode Root α → MeasurableSpace Ω)
    (L : Ω → Set (RootIndexed.TreeNode Root α)) : Prop extends IsRandomLine L where
  measurableSet_mem : ∀ u, MeasurableSet[history u] {ω | u ∈ L ω}

theorem IsAncestralStoppingLine.const
    (history : RootIndexed.TreeNode Root α → MeasurableSpace Ω)
    {ℓ : Set (RootIndexed.TreeNode Root α)} (hℓ : RootIndexed.IsLine ℓ) :
    IsAncestralStoppingLine history (fun _ : Ω => ℓ) :=
  ⟨IsRandomLine.const hℓ, fun _ => MeasurableSet.const _⟩

theorem IsAncestralStoppingLine.mono
    {history history' : RootIndexed.TreeNode Root α → MeasurableSpace Ω}
    {L : Ω → Set (RootIndexed.TreeNode Root α)} (h : IsAncestralStoppingLine history L)
    (hle : ∀ u, history u ≤ history' u) : IsAncestralStoppingLine history' L :=
  ⟨h.toIsRandomLine, fun u => hle u _ (h.measurableSet_mem u)⟩

theorem IsAncestralStoppingLine.inter
    {history : RootIndexed.TreeNode Root α → MeasurableSpace Ω}
    {L M : Ω → Set (RootIndexed.TreeNode Root α)}
    (hL : IsAncestralStoppingLine history L) (hM : IsAncestralStoppingLine history M) :
    IsAncestralStoppingLine history (fun ω => L ω ∩ M ω) :=
  ⟨hL.toIsRandomLine.inter hM.toIsRandomLine,
    fun u => (hL.measurableSet_mem u).inter (hM.measurableSet_mem u)⟩

theorem IsAncestralStoppingLine.restrict
    {history : RootIndexed.TreeNode Root α → MeasurableSpace Ω}
    {L : Ω → Set (RootIndexed.TreeNode Root α)}
    (hL : IsAncestralStoppingLine history L) (C : Set (RootIndexed.TreeNode Root α)) :
    IsAncestralStoppingLine history (fun ω => L ω ∩ C) := by
  refine ⟨hL.toIsRandomLine.restrict C, fun u => ?_⟩
  by_cases hu : u ∈ C
  · simpa only [Set.mem_inter_iff, hu, and_true] using hL.measurableSet_mem u
  · simp only [Set.mem_inter_iff, hu, and_false, Set.ofPred_false, MeasurableSet.empty]

/-- Countably many tested paths, each with finitely many possible stopping ancestors. -/
theorem IsAncestralStoppingLine.measurableSet_precedes
    {history : RootIndexed.TreeNode Root α → MeasurableSpace Ω}
    {L : Ω → Set (RootIndexed.TreeNode Root α)} (h : IsAncestralStoppingLine history L)
    (ℓ : Set (RootIndexed.TreeNode Root α)) (hcount : ℓ.Countable)
    (past : MeasurableSpace Ω)
    (hinfo : ∀ u v, v ∈ ℓ → RootIndexed.IsAncestor u v → history u ≤ past) :
    MeasurableSet[past] {ω | RootIndexed.Line.Precedes (L ω) ℓ} := by
  have heq : {ω | RootIndexed.Line.Precedes (L ω) ℓ} =
      ⋂ v ∈ ℓ, ⋃ n : ℕ, {ω | n ≤ v.2.length ∧ (v.1, v.2.take n) ∈ L ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, RootIndexed.Line.precedes_iff_prefix,
      Set.mem_iInter, Set.mem_iUnion]
  rw [heq]
  apply MeasurableSet.biInter hcount
  intro v hv
  apply MeasurableSet.iUnion
  intro n
  by_cases hn : n ≤ v.2.length
  · have hm0 := @IsAncestralStoppingLine.measurableSet_mem Ω Root α mΩ
      history L h (v.1, v.2.take n)
    have hm := hinfo (v.1, v.2.take n) v hv ⟨rfl, List.take_prefix n v.2⟩ _
      hm0
    simpa only [hn, true_and] using hm
  · simp only [hn, false_and, Set.ofPred_false, MeasurableSet.empty]

/-- Ancestral decisions imply optionality when their information is available at every test cut. -/
theorem IsAncestralStoppingLine.isOptionalLine [Countable Root] [Countable α]
    {history : RootIndexed.TreeNode Root α → MeasurableSpace Ω}
    {L : Ω → Set (RootIndexed.TreeNode Root α)} (h : IsAncestralStoppingLine history L)
    (past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω)
    (hinfo : ∀ ℓ, RootIndexed.IsLine ℓ → ∀ u v, v ∈ ℓ →
      RootIndexed.IsAncestor u v → history u ≤ past ℓ) : IsOptionalLine past L :=
  ⟨h.toIsRandomLine, fun ℓ hℓ =>
    h.measurableSet_precedes ℓ (Set.to_countable ℓ) (past ℓ) (hinfo ℓ hℓ)⟩

/-- Strict ancestral decisions are optional for the coordinate-generated line past. -/
theorem IsAncestralStoppingLine.isOptionalLine_linePast [Countable Root] [Countable α]
    (initial : MeasurableSpace Ω)
    (coordinate : RootIndexed.TreeNode Root α → MeasurableSpace Ω)
    {L : Ω → Set (RootIndexed.TreeNode Root α)}
    (h : @IsAncestralStoppingLine Ω Root α mΩ (ancestralPast initial coordinate) L) :
    @IsOptionalLine Ω Root α mΩ (linePast initial coordinate) L := by
  apply IsAncestralStoppingLine.isOptionalLine (mΩ := mΩ) h
  intro ℓ hℓ u v hv huv
  exact ancestralPast_le_linePast initial coordinate hℓ hv huv

end ProbabilityTheory.Tree

end
