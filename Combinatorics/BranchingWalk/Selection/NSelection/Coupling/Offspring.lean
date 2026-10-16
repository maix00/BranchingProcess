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

This file propagates parent domination to lower-tail domination of genuine child
addresses.  Child slots remain arbitrary finite sets or sets; no enumeration
of roots or offspring slots is assumed.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.Coupling

open Combinatorics.UlamHarris
open Selection.NSelection

variable {Root α Mark Position Value : Type*}

/-- Parent domination propagates to lower-tail domination of genuine child
addresses.  The two walks may use different underlying step fields; the
coupling hypothesis identifies the mapped increment of every shared slot of
matched parents. -/
theorem offspringAddresses_filter_card_le_of_injection
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (sourceParents targetParents : Finset (RootIndexed.TreeNode Root α))
    (sourceSlots targetSlots : RootIndexed.TreeNode Root α → Finset α)
    (parents : Cloud.SliceDominatingMap φ
      (populationCloud d sourceWalk sourceParents)
      (populationCloud d targetWalk targetParents) ())
    (hslots : ∀ p ∈ sourceParents,
      sourceSlots p ⊆ targetSlots (parents p))
    (hsharedIncrement : ∀ p ∈ sourceParents, ∀ i ∈ sourceSlots p,
        value' ((targetWalk.step (parents p).1 (parents p).2).map d) i =
          value' ((sourceWalk.step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (a : Value) :
    ((offspringAddresses sourceParents sourceSlots).filter fun q =>
        φ (sourceWalk.position d q.1 q.2) ≤ a).card ≤
      ((offspringAddresses targetParents targetSlots).filter fun q =>
        φ (targetWalk.position d q.1 q.2) ≤ a).card := by
  classical
  have hmem : ∀ p ∈ sourceParents, parents.toFun p ∈ targetParents := by
    intro p hp
    simpa using parents.mapsTo (by simpa using hp)
  have hinj : Set.InjOn parents.toFun (↑sourceParents : Set _) := by
    intro p hp q hq hpq
    exact parents.injOn (by simpa using hp) (by simpa using hq) hpq
  have hpairs := offspringPairs_filter_card_le sourceParents targetParents
    sourceSlots targetSlots parents.toFun hmem hinj
    hslots
    (fun p i => φ (sourceWalk.position d p.1 (p.2 ++ [i])))
    (fun q i => φ (targetWalk.position d q.1 (q.2 ++ [i])))
    (by
      intro p hp i hi
      rw [sourceWalk.position_child, targetWalk.position_child,
        hsharedIncrement p hp i hi]
      exact htranslate (sourceWalk.position d p.1 p.2)
        (targetWalk.position d (parents p).1 (parents p).2)
        (value' ((sourceWalk.step p.1 p.2).map d) i)
        (by simpa using parents.dominates p (by simpa using hp))) a
  rw [card_filter_offspringAddresses, card_filter_offspringAddresses]
  convert hpairs using 1 <;> rfl

/-- Compatibility form with a proposition-valued parent domination and
shared-step hypotheses stated for every eligible target parent. -/
theorem offspringAddresses_filter_card_le_of_parent_matching
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (sourceParents targetParents : Finset (RootIndexed.TreeNode Root α))
    (sourceSlots targetSlots : RootIndexed.TreeNode Root α → Finset α)
    (hparents : (populationCloud d sourceWalk sourceParents).InjectivelyDominatesBy φ
      (populationCloud d targetWalk targetParents) ())
    (hslots : ∀ p ∈ sourceParents, ∀ q ∈ targetParents,
      φ (targetWalk.position d q.1 q.2) ≤
          φ (sourceWalk.position d p.1 p.2) →
      sourceSlots p ⊆ targetSlots q)
    (hsharedIncrement : ∀ p ∈ sourceParents, ∀ q ∈ targetParents,
      φ (targetWalk.position d q.1 q.2) ≤
          φ (sourceWalk.position d p.1 p.2) →
      ∀ i ∈ sourceSlots p,
        value' ((targetWalk.step q.1 q.2).map d) i =
          value' ((sourceWalk.step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (a : Value) :
    ((offspringAddresses sourceParents sourceSlots).filter fun q =>
        φ (sourceWalk.position d q.1 q.2) ≤ a).card ≤
      ((offspringAddresses targetParents targetSlots).filter fun q =>
        φ (targetWalk.position d q.1 q.2) ≤ a).card := by
  let parents := Cloud.SliceDominatingMap.ofInjectivelyDominatesBy hparents
  apply offspringAddresses_filter_card_le_of_injection φ d sourceWalk
    targetWalk sourceParents targetParents sourceSlots targetSlots parents
  · intro p hp i hi
    exact hslots p hp (parents p)
      (by simpa using parents.mapsTo (by simpa using hp))
      (by simpa using parents.dominates p (by simpa using hp)) hi
  · intro p hp i hi
    exact hsharedIncrement p hp (parents p)
      (by simpa using parents.mapsTo (by simpa using hp))
      (by simpa using parents.dominates p (by simpa using hp)) i hi
  · exact htranslate


end Combinatorics.Branching.Selection.Coupling

end
