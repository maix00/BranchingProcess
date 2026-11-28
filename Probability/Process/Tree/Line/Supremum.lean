/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Line.Supremum
public import Probability.Process.Tree.Line.FirstEntrance
public import Probability.Process.Tree.Line.Information.Stopped

/-!
# Countable suprema of optional lines

## Public declarations

In `ProbabilityTheory.Tree`:

* `IsRandomLine.supremum` proves that the pointwise ancestral supremum of a
  countable family of random lines is a random line.
* `IsOptionalLine.supremum` proves optionality using
  `{sup_i L_i ≼ ℓ} = ⋂ i, {L_i ≼ ℓ}`.
* `IsOptionalLine.measurableSpace_iSup_le_supremum` proves
  `⨆ i, F_(L_i) ≤ F_(sup_i L_i)`.

The optional-line condition is that of A. E. Kyprianou, *Martingale convergence
and the stopped branching random walk* (2000), §2, p. 408,
DOI 10.1007/s004409900036. The closure result is derived from that condition
and the deterministic supremum's universal property. Countability is imposed
on the family index, not on the node space. No branching law, exhaustion, or
monotonicity of the indexed family is required. Equality of the limiting
stopped information with the supremum-line information is not asserted.
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open MeasureTheory Combinatorics.UlamHarris

variable {Ω I Root α : Type*} [MeasurableSpace Ω] [Countable I]
  {L : I → Ω → Set (RootIndexed.TreeNode Root α)}

/-- Countable intersections of descendant regions give measurable frontier membership. -/
theorem IsRandomLine.supremum (h : ∀ i, IsRandomLine (L i)) :
    IsRandomLine (fun ω => RootIndexed.Line.supremum (fun i => L i ω)) := by
  apply isRandomLine_firstEntrance
  intro u
  have hdesc (i : I) : MeasurableSet
      {ω | u ∈ RootIndexed.Line.descendantClosure (L i ω)} := by
    have he : {ω | u ∈ RootIndexed.Line.descendantClosure (L i ω)} =
        ⋃ k : ℕ, {ω | k ≤ u.2.length ∧ (u.1, u.2.take k) ∈ L i ω} := by
      ext ω
      have hp := RootIndexed.Line.precedes_iff_prefix
        (L := L i ω) (M := {u})
      simpa only [RootIndexed.Line.precedes_iff_subset_descendantClosure,
        Set.singleton_subset_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
        Set.mem_singleton_iff, forall_eq] using hp
    rw [he]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : k ≤ u.2.length
    · simpa only [hk, true_and] using (h i).measurableSet_mem (u.1, u.2.take k)
    · simp only [hk, false_and, Set.ofPred_false]
      exact MeasurableSet.empty
  simpa only [Set.mem_iInter, Set.ofPred_forall] using MeasurableSet.iInter hdesc

/-- Countable ancestral suprema preserve the optional-line condition. -/
theorem IsOptionalLine.supremum
    {past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω}
    (h : ∀ i, IsOptionalLine past (L i)) :
    IsOptionalLine past (fun ω => RootIndexed.Line.supremum (fun i => L i ω)) := by
  refine ⟨IsRandomLine.supremum (fun i => (h i).toIsRandomLine), ?_⟩
  intro ℓ hℓ
  have he : {ω | RootIndexed.Line.Precedes
      (RootIndexed.Line.supremum (fun i => L i ω)) ℓ} =
      ⋂ i, {ω | RootIndexed.Line.Precedes (L i ω) ℓ} := by
    ext ω
    simp only [Set.mem_ofPred_eq, RootIndexed.Line.supremum_precedes_iff, Set.mem_iInter]
  rw [he]
  exact MeasurableSet.iInter fun i => (h i).measurableSet_precedes ℓ hℓ

/-- Each stopped information space embeds in the supremum-line information space. -/
theorem IsOptionalLine.measurableSpace_iSup_le_supremum
    {past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω}
    (h : ∀ i, IsOptionalLine past (L i)) :
    (⨆ i, (h i).measurableSpace) ≤ (IsOptionalLine.supremum h).measurableSpace := by
  apply iSup_le
  intro i
  exact (h i).measurableSpace_mono (IsOptionalLine.supremum h)
    (fun ω => RootIndexed.Line.precedes_supremum (fun j => L j ω) i)

end ProbabilityTheory.Tree

end
