/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Tree.Line.Information.Stopped

/-!
# Pasting optional lines at an observed decision

## Public declarations

In `ProbabilityTheory.Tree`:

* `IsOptionalLine.ite_of_precedes` states: if `L ≼ M` pointwise and
  `A ∈ F_L`, then `L` on `A` and `M` on `Aᶜ` define an optional line.
* `isOptionalLine_ite_of_precedes` gives its deterministic-line specialization:
  `a ≼ b`, `A ∈ past a`, ambient measurability of `A`, and monotonicity of
  `past` suffice to choose `a` on `A` and `b` otherwise.

These are direct closure consequences of the optional-line and stopped-past
conditions in J. D. Biggins and A. E. Kyprianou, *Measure change in multitype
branching* (2004), §6, pp. 556–557,
[DOI:10.1239/aap/1086957585](https://doi.org/10.1239/aap/1086957585).
The key identity is `{mixture ≼ ℓ} = (A ∩ {L ≼ ℓ}) ∪
({M ≼ ℓ} ∖ (A ∩ {L ≼ ℓ}))`. No independence or law is required.
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open Classical MeasureTheory Combinatorics.UlamHarris

variable {Ω Root α : Type*} [mΩ : MeasurableSpace Ω]

/-- A decision available at the earlier optional line may select the later line instead. -/
theorem IsOptionalLine.ite_of_precedes
    {past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω}
    {L M : Ω → Set (RootIndexed.TreeNode Root α)}
    (hL : IsOptionalLine past L) (hM : IsOptionalLine past M)
    (hLM : ∀ ω, RootIndexed.Line.Precedes (L ω) (M ω))
    {A : Set Ω} (hA : MeasurableSet[hL.measurableSpace] A) :
    IsOptionalLine past (fun ω => if ω ∈ A then L ω else M ω) := by
  refine ⟨hL.toIsRandomLine.ite hM.toIsRandomLine hA.1, fun ℓ hℓ => ?_⟩
  have heq : {ω | RootIndexed.Line.Precedes (if ω ∈ A then L ω else M ω) ℓ} =
      (A ∩ {ω | RootIndexed.Line.Precedes (L ω) ℓ}) ∪
        ({ω | RootIndexed.Line.Precedes (M ω) ℓ} \
          (A ∩ {ω | RootIndexed.Line.Precedes (L ω) ℓ})) := by
    ext ω
    by_cases hω : ω ∈ A
    · have hle : RootIndexed.Line.Precedes (M ω) ℓ →
          RootIndexed.Line.Precedes (L ω) ℓ := fun h => (hLM ω).trans h
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_sdiff, hω, true_and]
      tauto
    · simp [hω]
  rw [heq]
  exact (hA.2 ℓ hℓ).union ((hM.measurableSet_precedes ℓ hℓ).diff (hA.2 ℓ hℓ))

/-- The constant-line case of optional pasting, using the same construction. -/
theorem isOptionalLine_ite_of_precedes
    (past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω)
    (hmono : ∀ {a b}, RootIndexed.IsLine a → RootIndexed.IsLine b →
      RootIndexed.Line.Precedes a b → past a ≤ past b)
    {a b : Set (RootIndexed.TreeNode Root α)}
    (ha : RootIndexed.IsLine a) (hb : RootIndexed.IsLine b)
    (hab : RootIndexed.Line.Precedes a b) {A : Set Ω}
    (hA : MeasurableSet A) (hAa : MeasurableSet[past a] A) :
    IsOptionalLine past (fun ω => if ω ∈ A then a else b) := by
  apply (IsOptionalLine.const past ha).ite_of_precedes (IsOptionalLine.const past hb)
    (fun _ => hab)
  refine ⟨hA, fun ℓ hℓ => ?_⟩
  by_cases haℓ : RootIndexed.Line.Precedes a ℓ
  · simpa only [haℓ, Set.ofPred_true, Set.inter_univ] using hmono ha hℓ haℓ _ hAa
  · simp only [haℓ, Set.ofPred_false, Set.inter_empty]
    exact @MeasurableSet.empty Ω (past ℓ)

end ProbabilityTheory.Tree

end
