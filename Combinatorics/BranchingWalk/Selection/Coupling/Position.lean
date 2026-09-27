import Combinatorics.BranchingWalk.Basic.Position
import Combinatorics.BranchingWalk.Selection.Coupling.Offspring

/-!
# Propagating position order through shared offspring

This file instantiates the abstract multi-root offspring matching with the
actual one-step position update.  Raw child marks, accumulated positions, and
the ordered observed values remain separate types.
-/

namespace Combinatorics.Branching.Selection.Coupling

open Combinatorics.UlamHarris

variable {Root α Mark Position Value Time : Type*}

/-- The observed position of the child in slot `i` of `p`.  The zero-defaulted
increment is taken only after mapping the raw mark into the additive position
space.  Membership in the finite slot set separately records that the child
is present. -/
def childValue [AddCommMonoid Position]
    (φ : Position → Value) (d : Mark → Position)
    (position : RootIndexed.TreeNode Root α → Position)
    (step : RootIndexed.TreeNode Root α → Step α Mark)
    (p : RootIndexed.TreeNode Root α) (i : α) : Value :=
  φ (position p + value' ((step p).map d) i)

/-- Adding the same mapped offspring increment to matched parents preserves
all offspring lower-tail counts.  This is the spatial specialization of
`offspringPairs_filter_card_le_of_rankwiseDominatesBy`.

The order compatibility is stated only after observation by `φ`; neither the
raw mark space nor the position space itself needs an order. -/
theorem childValue_filter_card_le_of_injectivelyDominatesBy
    [AddCommMonoid Position]
    [Preorder Value]
    [DecidableRel (· ≤ · : Value → Value → Prop)]
    (φ : Position → Value) (d : Mark → Position)
    {C D : Cloud Time Root α Position} (t : Time)
    (hCfinite : (C.particles t).Finite)
    (hDfinite : (D.particles t).Finite)
    (hdom : C.InjectivelyDominatesBy φ D t)
    (sourceSlots targetSlots : RootIndexed.TreeNode Root α → Finset α)
    (sourceStep targetStep : RootIndexed.TreeNode Root α → Step α Mark)
    (hslots : ∀ p ∈ C.particles t, ∀ q ∈ D.particles t,
      φ (D.position q.1 q.2) ≤ φ (C.position p.1 p.2) →
      sourceSlots p ⊆ targetSlots q)
    (hsharedIncrement : ∀ p ∈ C.particles t, ∀ q ∈ D.particles t,
      φ (D.position q.1 q.2) ≤ φ (C.position p.1 p.2) →
      ∀ i ∈ sourceSlots p,
        value' ((targetStep q).map d) i =
          value' ((sourceStep p).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (a : Value) :
    ((offspringPairs hCfinite.toFinset sourceSlots).filter fun
        (pi : RootIndexed.TreeNode Root α × α) =>
        childValue φ d (fun p => C.position p.1 p.2) sourceStep
          pi.1 pi.2 ≤ a).card ≤
      ((offspringPairs hDfinite.toFinset targetSlots).filter fun
        (qi : RootIndexed.TreeNode Root α × α) =>
        childValue φ d (fun q => D.position q.1 q.2) targetStep
          qi.1 qi.2 ≤ a).card := by
  apply offspringPairs_filter_card_le_of_injectivelyDominatesBy φ t
    hCfinite hDfinite hdom sourceSlots targetSlots
  intro p hp q hq hleft i hi
  refine ⟨hslots p hp q hq hleft hi, ?_⟩
  unfold childValue
  rw [hsharedIncrement p hp q hq hleft i hi]
  exact htranslate (C.position p.1 p.2) (D.position q.1 q.2)
    (value' ((sourceStep p).map d) i) hleft

/-- The abstract child-value update agrees definitionally with the position
of an actual child in a root-indexed branching walk. -/
theorem childValue_eq_branchingWalk_position_child
    [AddCommMonoid Position]
    (φ : Position → Value) (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (p : RootIndexed.TreeNode Root α) (i : α) :
    childValue φ d (fun q => β.position d q.1 q.2)
        (fun q => β.step q.1 q.2) p i =
      φ (β.position d p.1 (p.2 ++ [i])) := by
  unfold childValue
  rw [β.position_child]

end Combinatorics.Branching.Selection.Coupling
