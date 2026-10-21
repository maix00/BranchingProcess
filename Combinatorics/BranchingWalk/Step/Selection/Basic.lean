/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.Mechanism.Infinite
public import Combinatorics.BranchingWalk.Step.Measure.ExponentialWeight

/-!
# Selecting particles from an infinite branching step

A step may have infinitely many surviving slots.  This file connects its set
of surviving slots to the abstract first-`N` selection interface.  No finite
support assumption is introduced: it is enough that every lower potential
level contains finitely many children.

## Public declarations

- `Step.IsLowerFiniteBy φ ξ` means every set of surviving slots whose dynamic
  key `(φ (value' ξ i), i)` is at most the key of a fixed surviving slot is
  finite.
- `Step.isLowerFiniteBy_of_level_finite` derives that condition from
  finiteness of `{i | survive ξ i ∧ φ (value' ξ i) ≤ a}` for every `a`.
- `Step.admitsFirstNBy` turns lower finiteness into
  `Selection.NSelection.AdmitsFirstNBy N (fun i => φ (value' ξ i)) (support ξ)`.
- `Step.admitsFirstNBy_of_totalChildWeight_ne_top` applies this to real marks:
  finite total exponential child weight implies existence of the leftmost
  `N` surviving children under the displacement order.
-/

@[expose] public section

namespace Combinatorics.Branching

open Selection.NSelection

variable {ι X Value : Type*}

/-- Directional local finiteness of a step under an ordered observation. -/
def Step.IsLowerFiniteBy [Zero X] [LinearOrder ι] [LinearOrder Value]
    (φ : X → Value) (ξ : Step ι X) : Prop :=
  Selection.NSelection.IsLowerFiniteBy
    (fun i => φ (value' ξ i)) (support ξ)

/-- Finite lower potential levels imply lower finiteness for the full dynamic
key `(potential, slot label)`. -/
theorem Step.isLowerFiniteBy_of_level_finite
    [Zero X] [LinearOrder ι] [LinearOrder Value]
    (φ : X → Value) (ξ : Step ι X)
    (hlevel : ∀ a,
      {i | survive ξ i ∧ φ (value' ξ i) ≤ a}.Finite) :
    ξ.IsLowerFiniteBy φ := by
  intro p hp
  apply (hlevel (φ (value' ξ p))).subset
  intro q hq
  refine ⟨hq.1, ?_⟩
  exact (Prod.Lex.le_iff.mp hq.2).elim le_of_lt (fun h => h.1.le)

/-- A lower-finite step admits its first `N` surviving child slots, even when
its total offspring population is infinite. -/
theorem Step.admitsFirstNBy
    [Zero X] [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (φ : X → Value) (ξ : Step ι X)
    (hlower : ξ.IsLowerFiniteBy φ) :
    Selection.NSelection.AdmitsFirstNBy N
      (fun i => φ (value' ξ i)) (support ξ) :=
  Selection.NSelection.admitsFirstNBy_of_lowerFinite N _ hlower

/-- In the real displacement model, finiteness of the total exponential
weight supplies directional local finiteness and hence existence of the
leftmost `N` children. -/
theorem Step.admitsFirstNBy_of_totalChildWeight_ne_top
    [LinearOrder ι] (N : ℕ) (ξ : Step ι ℝ)
    (hsum : totalChildWeight ξ ≠ ⊤) :
    Selection.NSelection.AdmitsFirstNBy N
      (fun i => value' ξ i) (support ξ) := by
  apply ξ.admitsFirstNBy N id
  apply ξ.isLowerFiniteBy_of_level_finite id
  simpa using finite_realized_children_below ξ hsum

end Combinatorics.Branching
