import Combinatorics.BranchingWalk.Cloud.Order.DynamicSelection
import Combinatorics.BranchingWalk.Selection.Coupling.Position

/-!
# One generation of the multi-root spatial coupling

This file packages the deterministic induction step on genuine child
addresses.  It starts from an injective matching of two finite multi-root
parent populations, propagates the matching through shared child increments,
and applies dynamic leftmost selection to obtain the next matching.
-/

namespace Combinatorics.Branching.Selection.Coupling

open Combinatorics.UlamHarris
open Selection.NSelection

variable {Root α Mark Position Value : Type*}

/-- A finite labelled population presented as a constant-time cloud with the
position function of a root-indexed branching walk. -/
def populationCloud [AddCommMonoid Position]
    (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (population : Finset (RootIndexed.TreeNode Root α)) :
    Cloud PUnit Root α Position where
  particles _ := ↑population
  position := β.position d

@[simp] theorem populationCloud_particles [AddCommMonoid Position]
    (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (population : Finset (RootIndexed.TreeNode Root α)) (t : PUnit) :
    (populationCloud d β population).particles t = ↑population :=
  rfl

@[simp] theorem populationCloud_position [AddCommMonoid Position]
    (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (population : Finset (RootIndexed.TreeNode Root α))
    (p : RootIndexed.TreeNode Root α) :
    (populationCloud d β population).position p.1 p.2 =
      β.position d p.1 p.2 :=
  rfl

/-- Parent domination propagates to lower-tail domination of genuine child
addresses.  The two walks may use different underlying step fields; the
coupling hypothesis identifies the mapped increment of every shared slot of
matched parents. -/
theorem offspringAddresses_filter_card_le_of_parent_matching
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (sourceParents targetParents : Finset (RootIndexed.TreeNode Root α))
    (sourceSlots targetSlots : RootIndexed.TreeNode Root α → Finset α)
    (hparents : (populationCloud d sourceWalk sourceParents).InjectivelyDominatesBy φ
      (populationCloud d targetWalk targetParents) PUnit.unit)
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
  classical
  obtain ⟨matchParticle, hmem, hinj, hleft⟩ := hparents
  have hpairs := offspringPairs_filter_card_le sourceParents targetParents
    sourceSlots targetSlots matchParticle
    (by intro p hp; simpa using hmem (by simpa using hp))
    (by intro p hp q hq hpq; exact hinj (by simpa using hp) (by simpa using hq) hpq)
    (by
      intro p hp i hi
      exact hslots p hp (matchParticle p)
        (by simpa using hmem (by simpa using hp))
        (by simpa using hleft p (by simpa using hp)) hi)
    (fun p i => φ (sourceWalk.position d p.1 (p.2 ++ [i])))
    (fun q i => φ (targetWalk.position d q.1 (q.2 ++ [i])))
    (by
      intro p hp i hi
      rw [sourceWalk.position_child, targetWalk.position_child,
        hsharedIncrement p hp (matchParticle p)
          (by simpa using hmem (by simpa using hp))
          (by simpa using hleft p (by simpa using hp)) i hi]
      exact htranslate (sourceWalk.position d p.1 p.2)
        (targetWalk.position d (matchParticle p).1 (matchParticle p).2)
        (value' ((sourceWalk.step p.1 p.2).map d) i)
        (by simpa using hleft p (by simpa using hp))) a
  rw [card_filter_offspringAddresses, card_filter_offspringAddresses]
  convert hpairs using 1 <;> rfl

/-- Complete one-generation induction step.  Any retained subset of the
source offspring population with at most `N` particles is injectively
dominated by the dynamic leftmost `N` target offspring population. -/
theorem nextGeneration_injectivelyDominatesBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (sourceParents targetParents : Finset (RootIndexed.TreeNode Root α))
    (sourceSlots targetSlots : RootIndexed.TreeNode Root α → Finset α)
    (retainedChildren : Finset (RootIndexed.TreeNode Root α))
    (hretained : retainedChildren ⊆ offspringAddresses sourceParents sourceSlots)
    (hcard : retainedChildren.card ≤ N)
    (hparents : (populationCloud d sourceWalk sourceParents).InjectivelyDominatesBy φ
      (populationCloud d targetWalk targetParents) PUnit.unit)
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
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    (populationCloud d sourceWalk retainedChildren).InjectivelyDominatesBy φ
      (populationCloud d targetWalk
        (selectFirstNBy N
          (fun q => φ (targetWalk.position d q.1 q.2))
          (offspringAddresses targetParents targetSlots))) PUnit.unit := by
  classical
  let sourceCandidates := offspringAddresses sourceParents sourceSlots
  let targetCandidates := offspringAddresses targetParents targetSlots
  have hthreshold : ∀ a : Value,
      (sourceCandidates.filter fun p =>
        φ (sourceWalk.position d p.1 p.2) ≤ a).card ≤
      (targetCandidates.filter fun q =>
        φ (targetWalk.position d q.1 q.2) ≤ a).card := by
    intro a
    exact offspringAddresses_filter_card_le_of_parent_matching φ d
      sourceWalk targetWalk sourceParents targetParents sourceSlots targetSlots
      hparents hslots hsharedIncrement htranslate a
  obtain ⟨f, hfmem, hfle, hfinj⟩ :=
    exists_injective_le_selectFirstNBy N
      (fun p => φ (sourceWalk.position d p.1 p.2))
      (fun q => φ (targetWalk.position d q.1 q.2))
      retainedChildren sourceCandidates targetCandidates
      (by simpa [sourceCandidates] using hretained) hcard hthreshold
  let matchParticle : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α :=
    fun p => if hp : p ∈ retainedChildren then f p hp else p
  refine ⟨matchParticle, ?_, ?_, ?_⟩
  · intro p hp
    have hpr : p ∈ retainedChildren := by simpa using hp
    simpa [populationCloud, matchParticle, hpr, targetCandidates] using hfmem p hpr
  · intro p hp q hq heq
    have hpr : p ∈ retainedChildren := by simpa using hp
    have hqr : q ∈ retainedChildren := by simpa using hq
    apply hfinj p hpr q hqr
    simpa [matchParticle, hpr, hqr] using heq
  · intro p hp
    have hpr : p ∈ retainedChildren := by simpa using hp
    simpa [populationCloud, matchParticle, hpr] using hfle p hpr

end Combinatorics.Branching.Selection.Coupling
