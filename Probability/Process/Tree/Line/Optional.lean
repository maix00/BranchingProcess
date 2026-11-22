/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Tree.Line.Basic

/-!
# Optional random lines

## Public declarations

In `ProbabilityTheory.Tree`:

* `IsOptionalLine past L` is a random line with
  `{ω | RootIndexed.Line.Precedes (L ω) ℓ}` measurable in `past ℓ` for every
  deterministic line `ℓ`. The information family `past` is an explicit input.
* `IsOptionalLine.const` makes every deterministic line optional.
* `IsOptionalLine.mono` enlarges the information at every deterministic line.
* `isOptionalLine_ite_of_precedes` chooses an earlier deterministic line `a`
  on an event `A` measurable in `past a`, and a later line `b` otherwise,
  provided `a ≼ b`, the ambient measurability of `A`, and monotonicity of
  `past` along ancestral precedence. The conclusion holds against every
  test line, including lines mixing arbitrarily many generations.

The definition is Jagers' optional-line condition as stated in A. E.
Kyprianou, *Martingale convergence and the stopped branching random walk*
(2000), §2, p. 408, [DOI:10.1007/s004409900036](https://doi.org/10.1007/s004409900036).
It generalizes the event `{τ ≤ t}` in Mathlib's `IsStoppingTime`: it tests
precedence, not equality with a proposed value of the random line.
No law, independence, coverage, or countability assumption enters the definition.
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open Classical MeasureTheory Combinatorics.UlamHarris

variable {Ω Root α : Type*} [MeasurableSpace Ω]

/-- Optionality relative to the explicitly supplied past of each deterministic line. -/
structure IsOptionalLine
    (past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω)
    (L : Ω → Set (RootIndexed.TreeNode Root α)) : Prop extends IsRandomLine L where
  measurableSet_precedes : ∀ ℓ, RootIndexed.IsLine ℓ →
    MeasurableSet[past ℓ] {ω | RootIndexed.Line.Precedes (L ω) ℓ}

theorem IsOptionalLine.const
    (past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω)
    {ℓ : Set (RootIndexed.TreeNode Root α)} (hℓ : RootIndexed.IsLine ℓ) :
    IsOptionalLine past (fun _ : Ω => ℓ) :=
  ⟨IsRandomLine.const hℓ, fun _ _ => MeasurableSet.const _⟩

theorem IsOptionalLine.mono
    {past past' : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω}
    {L : Ω → Set (RootIndexed.TreeNode Root α)} (h : IsOptionalLine past L)
    (hle : ∀ ℓ, RootIndexed.IsLine ℓ → past ℓ ≤ past' ℓ) :
    IsOptionalLine past' L :=
  ⟨h.toIsRandomLine, fun ℓ hℓ => hle ℓ hℓ _ (h.measurableSet_precedes ℓ hℓ)⟩

/-- A decision known at the earlier of two ordered deterministic lines defines an optional line. -/
theorem isOptionalLine_ite_of_precedes
    (past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω)
    (hmono : ∀ {a b}, RootIndexed.IsLine a → RootIndexed.IsLine b →
      RootIndexed.Line.Precedes a b → past a ≤ past b)
    {a b : Set (RootIndexed.TreeNode Root α)}
    (ha : RootIndexed.IsLine a) (hb : RootIndexed.IsLine b)
    (hab : RootIndexed.Line.Precedes a b) {A : Set Ω}
    (hA : MeasurableSet A) (hAa : MeasurableSet[past a] A) :
    IsOptionalLine past (fun ω => if ω ∈ A then a else b) := by
  refine ⟨(IsRandomLine.const ha).ite (IsRandomLine.const hb) hA, ?_⟩
  intro ℓ hℓ
  by_cases haℓ : RootIndexed.Line.Precedes a ℓ
  · by_cases hbℓ : RootIndexed.Line.Precedes b ℓ
    · have heq : {ω | RootIndexed.Line.Precedes (if ω ∈ A then a else b) ℓ} = Set.univ := by
        ext ω
        by_cases hω : ω ∈ A <;> simp [hω, haℓ, hbℓ]
      rw [heq]
      exact @MeasurableSet.univ Ω (past ℓ)
    · have heq : {ω | RootIndexed.Line.Precedes (if ω ∈ A then a else b) ℓ} = A := by
        ext ω
        by_cases hω : ω ∈ A <;> simp [hω, haℓ, hbℓ]
      rw [heq]
      exact hmono ha hℓ haℓ _ hAa
  · have hbℓ : ¬ RootIndexed.Line.Precedes b ℓ := fun h => haℓ (hab.trans h)
    have heq : {ω | RootIndexed.Line.Precedes (if ω ∈ A then a else b) ℓ} = ∅ := by
      ext ω
      by_cases hω : ω ∈ A <;> simp [hω, haℓ, hbℓ]
    rw [heq]
    exact @MeasurableSet.empty Ω (past ℓ)

end ProbabilityTheory.Tree

end
