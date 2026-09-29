module

public import Combinatorics.BranchingWalk.Selection.NSelection.Infinite
public import Combinatorics.BranchingWalk.Step.ExponentialWeight

@[expose] public section

/-!
# Selecting particles from an infinite branching step

A step may have infinitely many surviving slots.  This file connects its set
of surviving slots to the abstract first-`N` selection interface.  No finite
support assumption is introduced: it is enough that every lower potential
level contains finitely many children.
-/

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
