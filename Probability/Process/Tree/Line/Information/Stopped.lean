/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Tree.Line.Optional

/-!
# Information at an optional random line

## Public declarations

In `ProbabilityTheory.Tree`:

* `IsOptionalLine.measurableSpace` defines the stopped sigma algebra by
  `A ∈ F_L ↔ A ∈ F ∧ ∀ ℓ, IsLine ℓ → A ∩ {L ≼ ℓ} ∈ past ℓ`.
* `IsOptionalLine.measurableSet` gives this defining equivalence;
  `IsOptionalLine.measurableSpace_le` states `F_L ≤ F`.
* `IsOptionalLine.measurableSpace_mono` states `L ≼ M` pointwise implies
  `F_L ≤ F_M`, for optional `L` and `M` with the same deterministic-line past.

This is the tree-order version of Mathlib's stopped-information construction
`MeasureTheory.IsStoppingTime.measurableSpace` in
`Mathlib.Probability.Process.Stopping`. It uses the optional-line condition
stated in A. E. Kyprianou, *Martingale convergence and the stopped branching
random walk* (2000), §2, p. 408,
[DOI:10.1007/s004409900036](https://doi.org/10.1007/s004409900036).
The ambient measurability requirement is explicit, so the resulting sigma
algebra is a sub-sigma-algebra of the ambient space even for a non-exhaustive line.
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open MeasureTheory Combinatorics.UlamHarris

variable {Ω Root α : Type*} [mΩ : MeasurableSpace Ω]
  {past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω}
  {L M : Ω → Set (RootIndexed.TreeNode Root α)}

/-- The information available at an optional random line. -/
@[instance_reducible]
protected def IsOptionalLine.measurableSpace (h : IsOptionalLine past L) :
    MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet[mΩ] A ∧ ∀ ℓ, RootIndexed.IsLine ℓ →
    MeasurableSet[past ℓ] (A ∩ {ω | RootIndexed.Line.Precedes (L ω) ℓ})
  measurableSet_empty := by
    refine ⟨MeasurableSet.empty, fun ℓ _ => ?_⟩
    rw [Set.empty_inter]
    exact @MeasurableSet.empty Ω (past ℓ)
  measurableSet_compl A hA := by
    refine ⟨hA.1.compl, fun ℓ hℓ => ?_⟩
    have heq : Aᶜ ∩ {ω | RootIndexed.Line.Precedes (L ω) ℓ} =
        {ω | RootIndexed.Line.Precedes (L ω) ℓ} \
          (A ∩ {ω | RootIndexed.Line.Precedes (L ω) ℓ}) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
      tauto
    rw [heq]
    exact (h.measurableSet_precedes ℓ hℓ).diff (hA.2 ℓ hℓ)
  measurableSet_iUnion A hA := by
    refine ⟨MeasurableSet.iUnion (fun n => (hA n).1), fun ℓ hℓ => ?_⟩
    rw [Set.iUnion_inter]
    exact MeasurableSet.iUnion (fun n => (hA n).2 ℓ hℓ)

protected theorem IsOptionalLine.measurableSet (h : IsOptionalLine past L) (A : Set Ω) :
    MeasurableSet[h.measurableSpace] A ↔ MeasurableSet[mΩ] A ∧
      ∀ ℓ, RootIndexed.IsLine ℓ →
        MeasurableSet[past ℓ] (A ∩ {ω | RootIndexed.Line.Precedes (L ω) ℓ}) := Iff.rfl

theorem IsOptionalLine.measurableSpace_le (h : IsOptionalLine past L) :
    h.measurableSpace ≤ mΩ := fun _ hA => hA.1

theorem IsOptionalLine.measurableSpace_mono
    (hL : IsOptionalLine past L) (hM : IsOptionalLine past M)
    (hle : ∀ ω, RootIndexed.Line.Precedes (L ω) (M ω)) :
    hL.measurableSpace ≤ hM.measurableSpace := by
  intro A hA
  refine ⟨hA.1, fun ℓ hℓ => ?_⟩
  have heq : A ∩ {ω | RootIndexed.Line.Precedes (M ω) ℓ} =
      (A ∩ {ω | RootIndexed.Line.Precedes (L ω) ℓ}) ∩
        {ω | RootIndexed.Line.Precedes (M ω) ℓ} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hω
      exact ⟨⟨hω.1, (hle ω).trans hω.2⟩, hω.2⟩
    · exact fun hω => ⟨hω.1.1, hω.2⟩
  rw [heq]
  exact (hA.2 ℓ hℓ).inter (hM.measurableSet_precedes ℓ hℓ)

end ProbabilityTheory.Tree

end
