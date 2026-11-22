/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Tree.Line.Optional
public import Probability.Process.Tree.Line.Information.Coordinates

/-!
# Optionality from observable ancestral membership decisions

## Public declarations

In `ProbabilityTheory.Tree`:

* `measurableSet_precedes_of_mem` proves `{L ≼ ℓ}` measurable
  for a countable test set `ℓ`, provided `{u ∈ L}` is measurable in `history u`
  and `history u ≤ past` whenever `u ≼ v ∈ ℓ`. A node has finitely many
  ancestors, so the whole address space need not be countable here.
* `IsRandomLine.isOptionalLine_of_mem` applies this criterion to every
  deterministic line, assuming the address space itself is countable and
  the corresponding information-containment hypothesis.
* `IsRandomLine.isOptionalLine_of_ancestral_mem` specializes it to membership
  observable from strict ancestors' reproduction information and the initial
  information: `∀ u, {u ∈ L} ∈ ancestralPast initial coordinate u` implies
  `IsOptionalLine (linePast initial coordinate) L` for a countable address space.

Membership measurability is a hypothesis about the single random-line object,
not a separate stopping-line type. The public stopping criterion is
`IsOptionalLine`, following the optional-line convention in J. D. Biggins and
A. E. Kyprianou, *Measure change in multitype branching* (2004), §6, pp. 556–557,
[DOI:10.1239/aap/1086957585](https://doi.org/10.1239/aap/1086957585).
The observation conventions and state interpretation are specified in
`Information/Coordinates.lean` and `Information/Observations.lean`.
No implication from a node's complete post-reproduction information is assumed.
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open MeasureTheory Combinatorics.UlamHarris

variable {Ω Root α : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- Countably many tested paths, each with finitely many possible stopping ancestors. -/
theorem measurableSet_precedes_of_mem
    {history : RootIndexed.TreeNode Root α → MeasurableSpace Ω}
    {L : Ω → Set (RootIndexed.TreeNode Root α)}
    (hmem : ∀ u, MeasurableSet[history u] {ω | u ∈ L ω})
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
  · have hm0 := hmem (v.1, v.2.take n)
    have hm := hinfo (v.1, v.2.take n) v hv ⟨rfl, List.take_prefix n v.2⟩ _
      hm0
    simpa only [hn, true_and] using hm
  · simp only [hn, false_and, Set.ofPred_false, MeasurableSet.empty]

/-- Ancestral decisions imply optionality when their information is available at every test cut. -/
theorem IsRandomLine.isOptionalLine_of_mem
    [Countable (RootIndexed.TreeNode Root α)]
    {history : RootIndexed.TreeNode Root α → MeasurableSpace Ω}
    {L : Ω → Set (RootIndexed.TreeNode Root α)} (h : IsRandomLine L)
    (hmem : ∀ u, MeasurableSet[history u] {ω | u ∈ L ω})
    (past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω)
    (hinfo : ∀ ℓ, RootIndexed.IsLine ℓ → ∀ u v, v ∈ ℓ →
      RootIndexed.IsAncestor u v → history u ≤ past ℓ) : IsOptionalLine past L :=
  ⟨h, fun ℓ hℓ =>
    measurableSet_precedes_of_mem hmem ℓ (Set.to_countable ℓ) (past ℓ) (hinfo ℓ hℓ)⟩

/-- Strict ancestral decisions are optional for the coordinate-generated line past. -/
theorem IsRandomLine.isOptionalLine_of_ancestral_mem
    [Countable (RootIndexed.TreeNode Root α)]
    (initial : MeasurableSpace Ω)
    (coordinate : RootIndexed.TreeNode Root α → MeasurableSpace Ω)
    {L : Ω → Set (RootIndexed.TreeNode Root α)}
    (h : @IsRandomLine Ω Root α mΩ L)
    (hmem : ∀ u, MeasurableSet[ancestralPast initial coordinate u] {ω | u ∈ L ω}) :
    @IsOptionalLine Ω Root α mΩ (linePast initial coordinate) L := by
  apply IsRandomLine.isOptionalLine_of_mem (mΩ := mΩ) h hmem
  intro ℓ hℓ u v hv huv
  exact ancestralPast_le_linePast initial coordinate hℓ hv huv

end ProbabilityTheory.Tree

end
