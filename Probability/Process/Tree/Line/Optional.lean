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


end ProbabilityTheory.Tree

end
