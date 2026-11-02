/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Basic

/-!
# Sibling-closed steps

The surviving slots of a step form an initial segment of the slot order. This
is a presence condition only; mark relations live in `Step.Relation`, and the
support-preserving relabeling condition lives in
`Step.Ordering.Sibling.Closable`.

## Public declarations

The present slots form an initial segment of the slot order: whenever a later
slot is present, every earlier slot is present as well:

\[
\operatorname{IsSiblingClosed}(\xi)
\Longleftrightarrow
\forall i<j,\quad
\xi(j)\ne\mathrm{none}\Longrightarrow\xi(i)\ne\mathrm{none}.
\]

- `Combinatorics.Branching.Step.IsSiblingClosed ξ` means
  `∀ i j, i < j → ξ i = none → ξ j = none`.
- `Combinatorics.Branching.Step.IsSiblingClosed.survive_of_lt` derives
  `survive ξ i` from `i < j` and `survive ξ j`.
- `Combinatorics.Branching.Step.IsSiblingClosed.survive_of_le` derives
  `survive ξ i` from `i ≤ j` and `survive ξ j` under `[PartialOrder ι]`.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

/-- An absent slot cannot be followed by a surviving slot. -/
def Step.IsSiblingClosed {ι X : Type*} [LT ι]
    (ξ : Step ι X) : Prop :=
  ∀ i j, i < j → ξ i = none → ξ j = none

/-- A surviving slot forces every earlier slot to survive. -/
theorem Step.IsSiblingClosed.survive_of_lt {ι X : Type*} [LT ι] {ξ : Step ι X}
    (h : Step.IsSiblingClosed ξ) {i j : ι} (hij : i < j) (hj : survive ξ j) : survive ξ i := by
  classical
  by_contra hi
  simp only [survive, not_exists] at hi
  have hnone : ξ i = none := by
    cases hxi : ξ i with
    | none => simp
    | some x => exact (hi x hxi).elim
  obtain ⟨y, hy⟩ := hj
  have hjnone := h i j hij hnone
  rw [hy] at hjnone
  cases hjnone

/-- The same closure consequence at the non-strict slot order. -/
theorem Step.IsSiblingClosed.survive_of_le {ι X : Type*} [PartialOrder ι] {ξ : Step ι X}
    (h : Step.IsSiblingClosed ξ) {i j : ι} (hij : i ≤ j) (hj : survive ξ j) : survive ξ i := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact hj
  · exact h.survive_of_lt hlt hj

end Branching

end Combinatorics

end
