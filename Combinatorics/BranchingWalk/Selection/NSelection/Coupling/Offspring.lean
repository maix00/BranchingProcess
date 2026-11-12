/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.Coupling.Cloud
public import Combinatorics.BranchingWalk.Selection.Coupling.Offspring.Cloud

/-!
# Offspring propagation for the multi-root spatial coupling

## Public declarations

If `nSelectedBranchingWalkParentMatching` spatially matches every
`selectedBranchingWalkParents` parent to an
`nSelectedBranchingWalkParents` parent, the corresponding child-slot sets
are included, and shared increments agree, then every threshold count of
offspring addresses of `selectedBranchingWalk` is bounded by that of
`nSelectedBranchingWalk`:

\[
\begin{aligned}
&\#\left\{q\in\operatorname{offspringAddresses}
  (\texttt{selectedBranchingWalkParents},
   \texttt{selectedBranchingWalkChildSlots}):
  \phi\bigl(\operatorname{position}(\texttt{selectedBranchingWalk},d,q.1,q.2)\bigr)\le a\right\}\\
&\qquad\le
\#\left\{q\in\operatorname{offspringAddresses}
  (\texttt{nSelectedBranchingWalkParents},
   \texttt{nSelectedBranchingWalkChildSlots}):
  \phi\bigl(\operatorname{position}(\texttt{nSelectedBranchingWalk},d,q.1,q.2)\bigr)\le a\right\}.
\end{aligned}
\]

This file propagates parent domination to threshold-count domination of genuine offspring
addresses.  Child slots remain arbitrary finite sets or sets; no enumeration
of roots or offspring slots is assumed.

The public API is `offspringAddresses_filter_card_le_of_injection`: spatial
domination by `nSelectedBranchingWalkParentMatching`, child-slot inclusion,
and equality of shared increments imply
`((offspringAddresses selectedBranchingWalkParents selectedBranchingWalkChildSlots).filter
(fun q => φ (selectedBranchingWalk.position d q.1 q.2) ≤ a)).card ≤
((offspringAddresses nSelectedBranchingWalkParents nSelectedBranchingWalkChildSlots).filter
(fun q => φ (nSelectedBranchingWalk.position d q.1 q.2) ≤ a)).card` for every `a`.
`offspringAddresses_filter_card_le_of_parent_matching` gives the same bound
from the corresponding injective-domination relation when slot inclusion and
increment equality are assumed for every eligible `nSelectedBranchingWalk` parent.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.Coupling

open Combinatorics.UlamHarris
open _root_.Combinatorics.Selection.NSelection

variable {Root α Mark Position OrderKey : Type*}

/-- Parent domination propagates to threshold-count domination of genuine offspring
addresses. The two branching walks may use different underlying step fields;
the coupling hypothesis identifies the mapped increment of every shared
child slot. -/
theorem offspringAddresses_filter_card_le_of_injection
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position)
    (selectedBranchingWalk nSelectedBranchingWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkParents nSelectedBranchingWalkParents : Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots : RootIndexed.TreeNode Root α → Finset α)
    (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
      (populationCloud d selectedBranchingWalk selectedBranchingWalkParents)
      (populationCloud d nSelectedBranchingWalk nSelectedBranchingWalkParents) ())
    (hchildSlots_mono_under_parentMatching : ∀ p ∈ selectedBranchingWalkParents,
      selectedBranchingWalkChildSlots p ⊆ nSelectedBranchingWalkChildSlots (nSelectedBranchingWalkParentMatching p))
    (hmatchedParents_sharedIncrement : ∀ p ∈ selectedBranchingWalkParents, ∀ i ∈ selectedBranchingWalkChildSlots p,
        value' ((nSelectedBranchingWalk.step (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2).map d) i =
          value' ((selectedBranchingWalk.step p.1 p.2).map d) i)
    (horderKey_translation_mono : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (a : OrderKey) :
    ((offspringAddresses selectedBranchingWalkParents selectedBranchingWalkChildSlots).filter fun q =>
        φ (selectedBranchingWalk.position d q.1 q.2) ≤ a).card ≤
      ((offspringAddresses nSelectedBranchingWalkParents nSelectedBranchingWalkChildSlots).filter fun q =>
        φ (nSelectedBranchingWalk.position d q.1 q.2) ≤ a).card := by
  classical
  have hmem : ∀ p ∈ selectedBranchingWalkParents, nSelectedBranchingWalkParentMatching.toFun p ∈ nSelectedBranchingWalkParents := by
    intro p hp
    simpa using nSelectedBranchingWalkParentMatching.mapsTo (by simpa using hp)
  have hinj : Set.InjOn nSelectedBranchingWalkParentMatching.toFun (↑selectedBranchingWalkParents : Set _) := by
    intro p hp q hq hpq
    exact nSelectedBranchingWalkParentMatching.injOn (by simpa using hp) (by simpa using hq) hpq
  have hpairs := offspringPairs_filter_card_le selectedBranchingWalkParents nSelectedBranchingWalkParents
    selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots nSelectedBranchingWalkParentMatching.toFun hmem hinj
    hchildSlots_mono_under_parentMatching
    (fun p i => φ (selectedBranchingWalk.position d p.1 (p.2 ++ [i])))
    (fun q i => φ (nSelectedBranchingWalk.position d q.1 (q.2 ++ [i])))
    (by
      intro p hp i hi
      rw [selectedBranchingWalk.position_child, nSelectedBranchingWalk.position_child,
        hmatchedParents_sharedIncrement p hp i hi]
      exact horderKey_translation_mono (selectedBranchingWalk.position d p.1 p.2)
        (nSelectedBranchingWalk.position d (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2)
        (value' ((selectedBranchingWalk.step p.1 p.2).map d) i)
        (by simpa using nSelectedBranchingWalkParentMatching.dominates p (by simpa using hp))) a
  rw [card_filter_offspringAddresses, card_filter_offspringAddresses]
  convert hpairs using 1 <;> rfl

/-- Compatibility form with a proposition-valued parent domination and
shared-step hypotheses stated for every eligible `nSelectedBranchingWalk` parent. -/
theorem offspringAddresses_filter_card_le_of_parent_matching
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position)
    (selectedBranchingWalk nSelectedBranchingWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkParents nSelectedBranchingWalkParents : Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots : RootIndexed.TreeNode Root α → Finset α)
    (hselectedParents_injectivelyDominate_nSelectedParents : (populationCloud d selectedBranchingWalk selectedBranchingWalkParents).InjectivelyDominatesBy φ
      (populationCloud d nSelectedBranchingWalk nSelectedBranchingWalkParents) ())
    (hchildSlots_mono_under_parentMatching : ∀ p ∈ selectedBranchingWalkParents, ∀ q ∈ nSelectedBranchingWalkParents,
      φ (nSelectedBranchingWalk.position d q.1 q.2) ≤
          φ (selectedBranchingWalk.position d p.1 p.2) →
      selectedBranchingWalkChildSlots p ⊆ nSelectedBranchingWalkChildSlots q)
    (hmatchedParents_sharedIncrement : ∀ p ∈ selectedBranchingWalkParents, ∀ q ∈ nSelectedBranchingWalkParents,
      φ (nSelectedBranchingWalk.position d q.1 q.2) ≤
          φ (selectedBranchingWalk.position d p.1 p.2) →
      ∀ i ∈ selectedBranchingWalkChildSlots p,
        value' ((nSelectedBranchingWalk.step q.1 q.2).map d) i =
          value' ((selectedBranchingWalk.step p.1 p.2).map d) i)
    (horderKey_translation_mono : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (a : OrderKey) :
    ((offspringAddresses selectedBranchingWalkParents selectedBranchingWalkChildSlots).filter fun q =>
        φ (selectedBranchingWalk.position d q.1 q.2) ≤ a).card ≤
      ((offspringAddresses nSelectedBranchingWalkParents nSelectedBranchingWalkChildSlots).filter fun q =>
        φ (nSelectedBranchingWalk.position d q.1 q.2) ≤ a).card := by
  let nSelectedBranchingWalkParentMatching := Cloud.SliceDominatingMap.ofInjectivelyDominatesBy hselectedParents_injectivelyDominate_nSelectedParents
  apply offspringAddresses_filter_card_le_of_injection φ d selectedBranchingWalk
    nSelectedBranchingWalk selectedBranchingWalkParents nSelectedBranchingWalkParents selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots nSelectedBranchingWalkParentMatching
  · intro p hp i hi
    exact hchildSlots_mono_under_parentMatching p hp (nSelectedBranchingWalkParentMatching p)
      (by simpa using nSelectedBranchingWalkParentMatching.mapsTo (by simpa using hp))
      (by simpa using nSelectedBranchingWalkParentMatching.dominates p (by simpa using hp)) hi
  · intro p hp i hi
    exact hmatchedParents_sharedIncrement p hp (nSelectedBranchingWalkParentMatching p)
      (by simpa using nSelectedBranchingWalkParentMatching.mapsTo (by simpa using hp))
      (by simpa using nSelectedBranchingWalkParentMatching.dominates p (by simpa using hp)) i hi
  · exact horderKey_translation_mono


end Combinatorics.Branching.Selection.Coupling

end
