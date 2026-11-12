/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Population.Offspring

public import Combinatorics.BranchingWalk.Selection.NSelection.Coupling.Offspring
public import Combinatorics.Selection.NSelection.Matching.SelectedPopulation

/-!
# One-generation first-N coupling

## Public declarations

After one branching step, each child retained by
`selectedBranchingWalk` is matched to a child retained by
`nSelectedBranchingWalk` with no larger order key. In particular, for the
child sets \(P_{\mathrm{sel}}\) and \(P_{\mathrm{nSel}}\),

\[
\exists\,\varphi:P_{\mathrm{sel}}\hookrightarrow P_{\mathrm{nSel}},\qquad
\phi\!\left(\operatorname{position}(\texttt{nSelectedBranchingWalk},
  \varphi(p))\right)
\le \phi\!\left(\operatorname{position}(\texttt{selectedBranchingWalk},p)\right).
\]

This file performs the capacity selection step after parent and offspring
domination have been established.  It provides both a data-valued injection
and the final injective-domination theorem used by the pathwise iteration.

The public API includes `nextGenerationInjection_of_isFirstNBy`, which
constructs `matchedNSelectedChild`, and
`nextGeneration_injectivelyDominatesBy_of_isFirstNBy`, which packages its
properties as injective cloud domination. The theorem
`nextGeneration_injectivelyDominatesBy` specializes `nSelectedBranchingWalk`
to dynamic leftmost `N` selection and proves the same domination from parent
matching, child-slot inclusion, shared increments, and translation
monotonicity.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.Coupling

open Combinatorics.UlamHarris
open _root_.Combinatorics.Selection.NSelection

variable {Root α Mark Position OrderKey : Type*}

/-- One-generation coupling with arbitrary offspring sets. The parent
populations and `selectedBranchingWalkChildren` are finite because of the
capacity bound, while each parent may have an uncountable set of child slots. -/
theorem nextGeneration_injectivelyDominatesBy_of_isFirstNBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (selectedBranchingWalk nSelectedBranchingWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkParents nSelectedBranchingWalkParents : Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots : RootIndexed.TreeNode Root α → Set α)
    (selectedBranchingWalkChildren nSelectedBranchingWalkChildren :
      Finset (RootIndexed.TreeNode Root α))
    (hselectedChildren_subset_offspring : ↑selectedBranchingWalkChildren ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑selectedBranchingWalkParents) selectedBranchingWalkChildSlots)
    (hselectedChildren_card_le_N : selectedBranchingWalkChildren.card ≤ N)
    (hnSelectedChildren_isFirstNBy : IsFirstNBy N
      (fun q => φ (nSelectedBranchingWalk.position d q.1 q.2))
      (Combinatorics.Branching.Population.offspringAddressSet (↑nSelectedBranchingWalkParents) nSelectedBranchingWalkChildSlots) nSelectedBranchingWalkChildren)
    (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
      (populationCloud d selectedBranchingWalk selectedBranchingWalkParents)
      (populationCloud d nSelectedBranchingWalk nSelectedBranchingWalkParents) ())
    (hchildSlots_mono_under_parentMatching : ∀ p ∈ selectedBranchingWalkParents,
      selectedBranchingWalkChildSlots p ⊆ nSelectedBranchingWalkChildSlots (nSelectedBranchingWalkParentMatching p))
    (hmatchedParents_sharedIncrement : ∀ p ∈ selectedBranchingWalkParents, ∀ i ∈ selectedBranchingWalkChildSlots p,
        value' ((nSelectedBranchingWalk.step (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2).map d) i =
          value' ((selectedBranchingWalk.step p.1 p.2).map d) i)
    (horderKey_translation_mono : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    (populationCloud d selectedBranchingWalk selectedBranchingWalkChildren).InjectivelyDominatesBy φ
      (populationCloud d nSelectedBranchingWalk nSelectedBranchingWalkChildren) () := by
  classical
  let selectedBranchingWalkChildParentSlot (child : RootIndexed.TreeNode Root α)
      (hchild : child ∈ selectedBranchingWalkChildren) :
      RootIndexed.TreeNode Root α × α :=
    Classical.choose (hselectedChildren_subset_offspring hchild)
  have selectedBranchingWalkChildParentSlot_spec (child : RootIndexed.TreeNode Root α)
      (hchild : child ∈ selectedBranchingWalkChildren) :
      selectedBranchingWalkChildParentSlot child hchild ∈
          Combinatorics.Branching.Population.offspringPairSet (↑selectedBranchingWalkParents) selectedBranchingWalkChildSlots ∧
        RootIndexed.childAddress (selectedBranchingWalkChildParentSlot child hchild).1
          (selectedBranchingWalkChildParentSlot child hchild).2 = child :=
    Classical.choose_spec (hselectedChildren_subset_offspring hchild)
  let nSelectedOffspringCorrespondingToSelectedChild (child : RootIndexed.TreeNode Root α)
      (hchild : child ∈ selectedBranchingWalkChildren) :
      RootIndexed.TreeNode Root α :=
    RootIndexed.childAddress (nSelectedBranchingWalkParentMatching (selectedBranchingWalkChildParentSlot child hchild).1)
      (selectedBranchingWalkChildParentSlot child hchild).2
  have hembedMem : ∀ child hchild,
      nSelectedOffspringCorrespondingToSelectedChild child hchild ∈
        Combinatorics.Branching.Population.offspringAddressSet (↑nSelectedBranchingWalkParents) nSelectedBranchingWalkChildSlots := by
    intro child hchild
    have hpair := (selectedBranchingWalkChildParentSlot_spec child hchild).1
    exact Combinatorics.Branching.Population.mem_offspringAddressSet.mpr
      ⟨nSelectedBranchingWalkParentMatching (selectedBranchingWalkChildParentSlot child hchild).1,
        (by simpa using nSelectedBranchingWalkParentMatching.mapsTo (by simpa using hpair.1)),
        (selectedBranchingWalkChildParentSlot child hchild).2,
        hchildSlots_mono_under_parentMatching _ hpair.1 hpair.2, rfl⟩
  have hembedInj : ∀ child hchild child' hchild',
      nSelectedOffspringCorrespondingToSelectedChild child hchild = nSelectedOffspringCorrespondingToSelectedChild child' hchild' → child = child' := by
    intro child hchild child' hchild' heq
    change RootIndexed.childAddress (nSelectedBranchingWalkParentMatching (selectedBranchingWalkChildParentSlot child hchild).1)
        (selectedBranchingWalkChildParentSlot child hchild).2 =
      RootIndexed.childAddress (nSelectedBranchingWalkParentMatching (selectedBranchingWalkChildParentSlot child' hchild').1)
        (selectedBranchingWalkChildParentSlot child' hchild').2 at heq
    have hpairs :
        (nSelectedBranchingWalkParentMatching (selectedBranchingWalkChildParentSlot child hchild).1,
            (selectedBranchingWalkChildParentSlot child hchild).2) =
          (nSelectedBranchingWalkParentMatching (selectedBranchingWalkChildParentSlot child' hchild').1,
            (selectedBranchingWalkChildParentSlot child' hchild').2) := by
      apply RootIndexed.childAddress_joint_injective
      exact heq
    obtain ⟨hmatchedParents, hslotsEq⟩ := Prod.ext_iff.mp hpairs
    have hpair : selectedBranchingWalkChildParentSlot child hchild = selectedBranchingWalkChildParentSlot child' hchild' := by
      have hparentsEq : (selectedBranchingWalkChildParentSlot child hchild).1 =
          (selectedBranchingWalkChildParentSlot child' hchild').1 :=
        nSelectedBranchingWalkParentMatching.injOn
          (by simpa using (selectedBranchingWalkChildParentSlot_spec child hchild).1.1)
          (by simpa using (selectedBranchingWalkChildParentSlot_spec child' hchild').1.1)
          hmatchedParents
      exact Prod.ext
        hparentsEq hslotsEq
    rw [← (selectedBranchingWalkChildParentSlot_spec child hchild).2,
      ← (selectedBranchingWalkChildParentSlot_spec child' hchild').2, hpair]
  have hembedLeft : ∀ child hchild,
      φ (nSelectedBranchingWalk.position d (nSelectedOffspringCorrespondingToSelectedChild child hchild).1
          (nSelectedOffspringCorrespondingToSelectedChild child hchild).2) ≤
        φ (selectedBranchingWalk.position d child.1 child.2) := by
    intro child hchild
    have hpair := (selectedBranchingWalkChildParentSlot_spec child hchild).1
    have hselectedBranchingWalkPosition :
        selectedBranchingWalk.position d (selectedBranchingWalkChildParentSlot child hchild).1.1
            ((selectedBranchingWalkChildParentSlot child hchild).1.2 ++ [(selectedBranchingWalkChildParentSlot child hchild).2]) =
          selectedBranchingWalk.position d child.1 child.2 := by
      exact congrArg (fun q : RootIndexed.TreeNode Root α =>
        selectedBranchingWalk.position d q.1 q.2) (selectedBranchingWalkChildParentSlot_spec child hchild).2
    change φ (nSelectedBranchingWalk.position d (nSelectedBranchingWalkParentMatching (selectedBranchingWalkChildParentSlot child hchild).1).1
        ((nSelectedBranchingWalkParentMatching (selectedBranchingWalkChildParentSlot child hchild).1).2 ++
          [(selectedBranchingWalkChildParentSlot child hchild).2])) ≤
      φ (selectedBranchingWalk.position d child.1 child.2)
    rw [← hselectedBranchingWalkPosition, selectedBranchingWalk.position_child, nSelectedBranchingWalk.position_child,
      hmatchedParents_sharedIncrement _ hpair.1 _ hpair.2]
    exact horderKey_translation_mono _ _ _
      (by simpa using nSelectedBranchingWalkParentMatching.dominates _ (by simpa using hpair.1))
  obtain ⟨matchedNSelectedChild, hfmem, hfle, hfinj⟩ :=
    exists_injective_le_of_partnerAssignment_into_firstNBy N
      (fun p => φ (selectedBranchingWalk.position d p.1 p.2))
      (fun q => φ (nSelectedBranchingWalk.position d q.1 q.2))
      selectedBranchingWalkChildren (Combinatorics.Branching.Population.offspringAddressSet (↑nSelectedBranchingWalkParents) nSelectedBranchingWalkChildSlots)
      nSelectedBranchingWalkChildren hnSelectedChildren_isFirstNBy hselectedChildren_card_le_N
      (fun child : {child : RootIndexed.TreeNode Root α // child ∈ selectedBranchingWalkChildren} =>
        nSelectedOffspringCorrespondingToSelectedChild child.1 child.2)
      (by intro child; exact hembedMem child.1 child.2)
      (by
        intro child child' heq
        exact Subtype.ext (hembedInj child.1 child.2 child'.1 child'.2 heq))
      (by intro child; exact hembedLeft child.1 child.2)
  let matchedNSelectedChildOrSelf :
      RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α :=
    fun p => if hp : p ∈ selectedBranchingWalkChildren then
      matchedNSelectedChild p hp else p
  refine ⟨matchedNSelectedChildOrSelf, ?_, ?_, ?_⟩
  · intro p hp
    have hpr : p ∈ selectedBranchingWalkChildren := by simpa using hp
    simpa [populationCloud, matchedNSelectedChildOrSelf, hpr] using
      hfmem p hpr
  · intro p hp q hq heq
    have hpr : p ∈ selectedBranchingWalkChildren := by simpa using hp
    have hqr : q ∈ selectedBranchingWalkChildren := by simpa using hq
    apply hfinj p hpr q hqr
    simpa [matchedNSelectedChildOrSelf, hpr, hqr] using heq
  · intro p hp
    have hpr : p ∈ selectedBranchingWalkChildren := by simpa using hp
    simpa [populationCloud, matchedNSelectedChildOrSelf, hpr] using
      hfle p hpr

/-- Data-valued form of the one-generation coupling.  The returned injection
can be carried into the next generation instead of being immediately hidden
under an existential quantifier. -/
noncomputable def nextGenerationInjection_of_isFirstNBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (selectedBranchingWalk nSelectedBranchingWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkParents nSelectedBranchingWalkParents : Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots : RootIndexed.TreeNode Root α → Set α)
    (selectedBranchingWalkChildren nSelectedBranchingWalkChildren :
      Finset (RootIndexed.TreeNode Root α))
    (hselectedChildren_subset_offspring : ↑selectedBranchingWalkChildren ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑selectedBranchingWalkParents) selectedBranchingWalkChildSlots)
    (hselectedChildren_card_le_N : selectedBranchingWalkChildren.card ≤ N)
    (hnSelectedChildren_isFirstNBy : IsFirstNBy N
      (fun q => φ (nSelectedBranchingWalk.position d q.1 q.2))
      (Combinatorics.Branching.Population.offspringAddressSet (↑nSelectedBranchingWalkParents) nSelectedBranchingWalkChildSlots) nSelectedBranchingWalkChildren)
    (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
      (populationCloud d selectedBranchingWalk selectedBranchingWalkParents)
      (populationCloud d nSelectedBranchingWalk nSelectedBranchingWalkParents) ())
    (hchildSlots_mono_under_parentMatching : ∀ p ∈ selectedBranchingWalkParents,
      selectedBranchingWalkChildSlots p ⊆ nSelectedBranchingWalkChildSlots (nSelectedBranchingWalkParentMatching p))
    (hmatchedParents_sharedIncrement : ∀ p ∈ selectedBranchingWalkParents, ∀ i ∈ selectedBranchingWalkChildSlots p,
        value' ((nSelectedBranchingWalk.step (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2).map d) i =
          value' ((selectedBranchingWalk.step p.1 p.2).map d) i)
    (horderKey_translation_mono : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    Cloud.SliceDominatingMap φ
      (populationCloud d selectedBranchingWalk selectedBranchingWalkChildren)
      (populationCloud d nSelectedBranchingWalk nSelectedBranchingWalkChildren) () := by
  classical
  have hdom := nextGeneration_injectivelyDominatesBy_of_isFirstNBy
      φ d N selectedBranchingWalk nSelectedBranchingWalk selectedBranchingWalkParents nSelectedBranchingWalkParents
      selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots selectedBranchingWalkChildren nSelectedBranchingWalkChildren
      hselectedChildren_subset_offspring hselectedChildren_card_le_N hnSelectedChildren_isFirstNBy nSelectedBranchingWalkParentMatching
      hchildSlots_mono_under_parentMatching hmatchedParents_sharedIncrement horderKey_translation_mono
  let prior := Cloud.SliceDominatingMap.ofInjectivelyDominatesBy hdom
  have hcardSelected : selectedBranchingWalkChildren.card ≤ nSelectedBranchingWalkChildren.card := by
    apply Finset.card_le_card_of_injOn prior
    · intro p hp
      simpa [populationCloud] using
        prior.mapsTo (by simpa [populationCloud] using hp)
    · intro p hp q hq hpq
      exact prior.injOn (by simpa [populationCloud] using hp)
        (by simpa [populationCloud] using hq) hpq
  let selectedBranchingWalkOrderKey : RootIndexed.TreeNode Root α → OrderKey :=
    fun p => φ (selectedBranchingWalk.position d p.1 p.2)
  let nSelectedBranchingWalkOrderKey : RootIndexed.TreeNode Root α → OrderKey :=
    fun q => φ (nSelectedBranchingWalk.position d q.1 q.2)
  have hthresholdCount : ∀ a : OrderKey,
      (selectedBranchingWalkChildren.filter fun p => selectedBranchingWalkOrderKey p ≤ a).card ≤
        (nSelectedBranchingWalkChildren.filter fun q => nSelectedBranchingWalkOrderKey q ≤ a).card := by
    intro a
    simpa [selectedBranchingWalkOrderKey, nSelectedBranchingWalkOrderKey, populationCloud] using
      prior.card_filter_le selectedBranchingWalkChildren.finite_toSet
        nSelectedBranchingWalkChildren.finite_toSet a
  let matchedNSelectedChildOrSelf : RootIndexed.TreeNode Root α →
      RootIndexed.TreeNode Root α :=
    matchByRankOrSelf selectedBranchingWalkOrderKey nSelectedBranchingWalkOrderKey selectedBranchingWalkChildren nSelectedBranchingWalkChildren
      hcardSelected
  refine ⟨matchedNSelectedChildOrSelf, ?_, ?_, ?_⟩
  · intro p hp
    have hpr : p ∈ selectedBranchingWalkChildren := by simpa [populationCloud] using hp
    change matchedNSelectedChildOrSelf p ∈ nSelectedBranchingWalkChildren
    exact matchByRankOrSelf_mem selectedBranchingWalkOrderKey nSelectedBranchingWalkOrderKey selectedBranchingWalkChildren
      nSelectedBranchingWalkChildren hcardSelected hpr
  · intro p hp q hq hpq
    apply matchByRankOrSelf_injOn selectedBranchingWalkOrderKey nSelectedBranchingWalkOrderKey selectedBranchingWalkChildren
      nSelectedBranchingWalkChildren hcardSelected
    · simpa [populationCloud] using hp
    · simpa [populationCloud] using hq
    · exact hpq
  · intro p hp
    have hpr : p ∈ selectedBranchingWalkChildren := by simpa [populationCloud] using hp
    exact matchByRankOrSelf_partnerOrderKey_le selectedBranchingWalkOrderKey nSelectedBranchingWalkOrderKey selectedBranchingWalkChildren
      nSelectedBranchingWalkChildren hcardSelected hthresholdCount hpr

/-- Complete one-generation induction step. Any retained subset of the
`selectedBranchingWalk` offspring population with at most `N` particles is
injectively dominated by the dynamic leftmost `N` offspring population of
`nSelectedBranchingWalk`. -/
theorem nextGeneration_injectivelyDominatesBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (selectedBranchingWalk nSelectedBranchingWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkParents nSelectedBranchingWalkParents : Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots : RootIndexed.TreeNode Root α → Finset α)
    (selectedBranchingWalkChildren : Finset (RootIndexed.TreeNode Root α))
    (hselectedChildren_subset_offspring : selectedBranchingWalkChildren ⊆ offspringAddresses selectedBranchingWalkParents selectedBranchingWalkChildSlots)
    (hselectedChildren_card_le_N : selectedBranchingWalkChildren.card ≤ N)
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
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    (populationCloud d selectedBranchingWalk selectedBranchingWalkChildren).InjectivelyDominatesBy φ
      (populationCloud d nSelectedBranchingWalk
        (selectFirstNBy N
          (fun q => φ (nSelectedBranchingWalk.position d q.1 q.2))
          (offspringAddresses nSelectedBranchingWalkParents nSelectedBranchingWalkChildSlots))) () := by
  classical
  let selectedBranchingWalkCandidateChildren := offspringAddresses selectedBranchingWalkParents selectedBranchingWalkChildSlots
  let nSelectedBranchingWalkCandidateChildren := offspringAddresses nSelectedBranchingWalkParents nSelectedBranchingWalkChildSlots
  have hthresholdCount : ∀ a : OrderKey,
      (selectedBranchingWalkCandidateChildren.filter fun p =>
        φ (selectedBranchingWalk.position d p.1 p.2) ≤ a).card ≤
      (nSelectedBranchingWalkCandidateChildren.filter fun q =>
        φ (nSelectedBranchingWalk.position d q.1 q.2) ≤ a).card := by
    intro a
    exact offspringAddresses_filter_card_le_of_parent_matching φ d
      selectedBranchingWalk nSelectedBranchingWalk selectedBranchingWalkParents nSelectedBranchingWalkParents selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots
      hselectedParents_injectivelyDominate_nSelectedParents hchildSlots_mono_under_parentMatching hmatchedParents_sharedIncrement horderKey_translation_mono a
  obtain ⟨matchedNSelectedChild, hfmem, hfle, hfinj⟩ :=
    exists_injective_le_selectFirstNBy N
      (fun p => φ (selectedBranchingWalk.position d p.1 p.2))
      (fun q => φ (nSelectedBranchingWalk.position d q.1 q.2))
      selectedBranchingWalkChildren selectedBranchingWalkCandidateChildren nSelectedBranchingWalkCandidateChildren
      (by simpa [selectedBranchingWalkCandidateChildren] using hselectedChildren_subset_offspring) hselectedChildren_card_le_N hthresholdCount
  let matchedNSelectedChildOrSelf :
      RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α :=
    fun p => if hp : p ∈ selectedBranchingWalkChildren then
      matchedNSelectedChild p hp else p
  refine ⟨matchedNSelectedChildOrSelf, ?_, ?_, ?_⟩
  · intro p hp
    have hpr : p ∈ selectedBranchingWalkChildren := by simpa using hp
    simpa [populationCloud, matchedNSelectedChildOrSelf, hpr,
      nSelectedBranchingWalkCandidateChildren] using hfmem p hpr
  · intro p hp q hq heq
    have hpr : p ∈ selectedBranchingWalkChildren := by simpa using hp
    have hqr : q ∈ selectedBranchingWalkChildren := by simpa using hq
    apply hfinj p hpr q hqr
    simpa [matchedNSelectedChildOrSelf, hpr, hqr] using heq
  · intro p hp
    have hpr : p ∈ selectedBranchingWalkChildren := by simpa using hp
    simpa [populationCloud, matchedNSelectedChildOrSelf, hpr] using
      hfle p hpr

end Combinatorics.Branching.Selection.Coupling

end
