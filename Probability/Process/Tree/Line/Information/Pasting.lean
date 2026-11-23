/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Tree.Line.Pasting

/-!
# Information at a pasted optional line

## Public declarations

In `ProbabilityTheory.Tree`:

* `IsOptionalLine.measurableSet_ite_of_precedes`: if `L ≼ M`, `A ∈ F_L`,
  and `N = L` on `A`, `N = M` on `Aᶜ`, then
  `B ∈ F_N ↔ B ∩ A ∈ F_L ∧ B ∩ Aᶜ ∈ F_M`.

This derives the stopped-information identity for the existing optional-line
pasting construction. It uses the optional-line information of
J. D. Biggins and A. E. Kyprianou, *Measure change in multitype branching*
(2004), §6, pp. 556–557, DOI 10.1239/aap/1086957585.
No branching law, countability of nodes, or exhaustion of rays is assumed.
The information sigma algebras and the pasted optional line are reused.
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open Classical MeasureTheory Combinatorics.UlamHarris

/-- The stopped information of an ordered pasting is determined on its two decision cells. -/
theorem IsOptionalLine.measurableSet_ite_of_precedes {Ω Root α : Type*}
    [MeasurableSpace Ω]
    {past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω}
    {L M : Ω → Set (RootIndexed.TreeNode Root α)}
    (hL : IsOptionalLine past L) (hM : IsOptionalLine past M)
    (hLM : ∀ ω, RootIndexed.Line.Precedes (L ω) (M ω))
    {A : Set Ω} (hA : MeasurableSet[hL.measurableSpace] A) (B : Set Ω) :
    MeasurableSet[(hL.ite_of_precedes hM hLM hA).measurableSpace] B ↔
      MeasurableSet[hL.measurableSpace] (B ∩ A) ∧
        MeasurableSet[hM.measurableSpace] (B ∩ Aᶜ) := by
  let N := fun ω => if ω ∈ A then L ω else M ω
  constructor
  · intro hB
    constructor
    · refine ⟨hB.1.inter hA.1, fun ℓ hℓ => ?_⟩
      have heq : (B ∩ A) ∩ {ω | RootIndexed.Line.Precedes (L ω) ℓ} =
          (B ∩ {ω | RootIndexed.Line.Precedes (N ω) ℓ}) ∩
            (A ∩ {ω | RootIndexed.Line.Precedes (L ω) ℓ}) := by
        ext ω
        by_cases hω : ω ∈ A <;> simp [N, hω]
      rw [heq]
      exact (hB.2 ℓ hℓ).inter (hA.2 ℓ hℓ)
    · refine ⟨hB.1.inter hA.1.compl, fun ℓ hℓ => ?_⟩
      have heq : (B ∩ Aᶜ) ∩ {ω | RootIndexed.Line.Precedes (M ω) ℓ} =
          (B ∩ {ω | RootIndexed.Line.Precedes (N ω) ℓ}) \
            (A ∩ {ω | RootIndexed.Line.Precedes (L ω) ℓ}) := by
        ext ω
        by_cases hω : ω ∈ A <;> simp [N, hω]
      rw [heq]
      exact (hB.2 ℓ hℓ).diff (hA.2 ℓ hℓ)
  · rintro ⟨hBA, hBcA⟩
    have hsplit : B = (B ∩ A) ∪ (B ∩ Aᶜ) := by
      rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
    refine ⟨hsplit ▸ hBA.1.union hBcA.1, fun ℓ hℓ => ?_⟩
    have heq : B ∩ {ω | RootIndexed.Line.Precedes (N ω) ℓ} =
        ((B ∩ A) ∩ {ω | RootIndexed.Line.Precedes (L ω) ℓ}) ∪
          ((B ∩ Aᶜ) ∩ {ω | RootIndexed.Line.Precedes (M ω) ℓ}) := by
      ext ω
      by_cases hω : ω ∈ A <;> simp [N, hω]
    rw [heq]
    exact (hBA.2 ℓ hℓ).union (hBcA.2 ℓ hℓ)

end ProbabilityTheory.Tree

end
