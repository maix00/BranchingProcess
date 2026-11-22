/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Position.Basic
public import Combinatorics.BranchingWalk.Selection.Coupling.Offspring.Cloud

/-!
# Propagating position order through shared offspring

## Public declarations

For a parent \(p\) and surviving child slot \(i\), the observed child value is
the observation of the updated position. Under a finite parent injection,
matched slots and increments preserve the lower-tail count comparison:

\[
\psi_{\mathrm{o}}(p,i)=\phi\!\left(x_C(p)+\xi_C(p,i)\right),\qquad
\bigl|\{(p,i)\in P_{\mathrm{o}}:\psi_{\mathrm{o}}(p,i)\le a\}\bigr|
\le
\bigl|\{(q,i)\in P_{\mathrm{p}}:\psi_{\mathrm{p}}(q,i)\le a\}\bigr|.
\]

The declarations are in namespace
`Combinatorics.Branching.Selection.Coupling`.

- `childValue`: the observed position after one step,
  `φ (position p + value' ((step p).map d) i)`.
- `childValue_filter_card_le_of_injectivelyDominatesBy`: under a finite
  slice-dominating parent injection, inclusion of matched slot sets, equality
  of mapped increments, and translation monotonicity,
  `card (P_{\mathrm{o}}.filter (childValue_C ≤ a)) ≤
  card (P_{\mathrm{p}}.filter (childValue_D ≤ a))`, where `P_{\mathrm{o}}` and `P_{\mathrm{p}}` are the
  offspring-pair sets built from the object and partner slices.
- `childValue_eq_branchingWalk_position_child`: the abstract update equals
  `φ (β.position d p.1 (p.2 ++ [i]))` for a child of a branching walk.

This file instantiates the abstract multi-root offspring matching with the
actual one-step position update.  Raw child marks, accumulated positions, and
the ordered observed values remain separate types.
-/

@[expose] public section

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
    {objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position} (t : Time)
    (hobjectsToMatchFinite : (objectsToMatchCloud.particles t).Finite)
    (havailablePartnersFinite : (availablePartnersCloud.particles t).Finite)
    (hobjectCloudDominatesPartnerCloud : objectsToMatchCloud.InjectivelyDominatesBy φ availablePartnersCloud t)
    (objectSlots partnerSlots : RootIndexed.TreeNode Root α → Finset α)
    (objectStep partnerStep : RootIndexed.TreeNode Root α → Step α Mark)
    (hmatchedSlotSubset : ∀ p ∈ objectsToMatchCloud.particles t, ∀ q ∈ availablePartnersCloud.particles t,
      φ (availablePartnersCloud.position q.1 q.2) ≤ φ (objectsToMatchCloud.position p.1 p.2) →
      objectSlots p ⊆ partnerSlots q)
    (hmatchedSlotIncrement : ∀ p ∈ objectsToMatchCloud.particles t, ∀ q ∈ availablePartnersCloud.particles t,
      φ (availablePartnersCloud.position q.1 q.2) ≤ φ (objectsToMatchCloud.position p.1 p.2) →
      ∀ i ∈ objectSlots p,
        value' ((partnerStep q).map d) i =
          value' ((objectStep p).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (a : Value) :
    ((offspringPairs hobjectsToMatchFinite.toFinset objectSlots).filter fun
        (pi : RootIndexed.TreeNode Root α × α) =>
        childValue φ d (fun p => objectsToMatchCloud.position p.1 p.2) objectStep
          pi.1 pi.2 ≤ a).card ≤
      ((offspringPairs havailablePartnersFinite.toFinset partnerSlots).filter fun
        (qi : RootIndexed.TreeNode Root α × α) =>
        childValue φ d (fun q => availablePartnersCloud.position q.1 q.2) partnerStep
          qi.1 qi.2 ≤ a).card := by
  apply offspringPairs_filter_card_le_of_injectivelyDominatesBy φ t
    hobjectsToMatchFinite havailablePartnersFinite hobjectCloudDominatesPartnerCloud objectSlots partnerSlots
  intro p hp q hq hleft i hi
  refine ⟨hmatchedSlotSubset p hp q hq hleft hi, ?_⟩
  unfold childValue
  rw [hmatchedSlotIncrement p hp q hq hleft i hi]
  exact htranslate (objectsToMatchCloud.position p.1 p.2) (availablePartnersCloud.position q.1 q.2)
    (value' ((objectStep p).map d) i) hleft

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

end
