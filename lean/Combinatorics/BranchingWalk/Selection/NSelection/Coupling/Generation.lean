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
    Cloud Unit Root α Position where
  particles _ := ↑population
  position := β.position d

@[simp] theorem populationCloud_particles [AddCommMonoid Position]
    (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (population : Finset (RootIndexed.TreeNode Root α)) (t : Unit) :
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

theorem population_card_le_of_injection
    [AddCommMonoid Position]
    [Preorder Value]
    (φ : Position → Value) (d : Mark → Position)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (source target : Finset (RootIndexed.TreeNode Root α))
    (prior : Cloud.DominatingInjection φ
      (populationCloud d sourceWalk source)
      (populationCloud d targetWalk target) ()) :
    source.card ≤ target.card := by
  apply Finset.card_le_card_of_injOn prior
  · intro p hp
    simpa [populationCloud] using
      prior.mapsTo (by simpa [populationCloud] using hp)
  · intro p hp q hq hpq
    exact prior.injOn (by simpa [populationCloud] using hp)
      (by simpa [populationCloud] using hq) hpq

/-- Replace any finite spatial domination witness by the canonical
equal-dynamic-rank injection. -/
noncomputable def canonicalInjection
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (source target : Finset (RootIndexed.TreeNode Root α))
    (prior : Cloud.DominatingInjection φ
      (populationCloud d sourceWalk source)
      (populationCloud d targetWalk target) ()) :
    Cloud.DominatingInjection φ
      (populationCloud d sourceWalk source)
      (populationCloud d targetWalk target) () := by
  classical
  have hcard := population_card_le_of_injection φ d sourceWalk targetWalk
    source target prior
  let sourceValue : RootIndexed.TreeNode Root α → Value :=
    fun p => φ (sourceWalk.position d p.1 p.2)
  let targetValue : RootIndexed.TreeNode Root α → Value :=
    fun q => φ (targetWalk.position d q.1 q.2)
  have hthreshold : ∀ a : Value,
      (source.filter fun p => sourceValue p ≤ a).card ≤
        (target.filter fun q => targetValue q ≤ a).card := by
    intro a
    simpa [sourceValue, targetValue, populationCloud] using
      Cloud.filter_card_le_of_injectivelyDominatesBy φ ()
        source.finite_toSet target.finite_toSet
        prior.injectivelyDominatesBy a
  let matchParticle : RootIndexed.TreeNode Root α →
      RootIndexed.TreeNode Root α :=
    matchByRankOrSelf sourceValue targetValue source target hcard
  refine ⟨matchParticle, ?_, ?_, ?_⟩
  · intro p hp
    have hpr : p ∈ source := by simpa [populationCloud] using hp
    change matchParticle p ∈ target
    exact matchByRankOrSelf_mem sourceValue targetValue source target hcard hpr
  · intro p hp q hq hpq
    apply matchByRankOrSelf_injOn sourceValue targetValue source target hcard
    · simpa [populationCloud] using hp
    · simpa [populationCloud] using hq
    · exact hpq
  · intro p hp
    have hpr : p ∈ source := by simpa [populationCloud] using hp
    exact matchByRankOrSelf_value_le sourceValue targetValue source target
      hcard hthreshold hpr

@[simp] theorem canonicalInjection_apply
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (source target : Finset (RootIndexed.TreeNode Root α))
    (prior : Cloud.DominatingInjection φ
      (populationCloud d sourceWalk source)
      (populationCloud d targetWalk target) ())
    (p : RootIndexed.TreeNode Root α) :
    canonicalInjection φ d sourceWalk targetWalk source target prior p =
      matchByRankOrSelf
        (fun q => φ (sourceWalk.position d q.1 q.2))
        (fun q => φ (targetWalk.position d q.1 q.2))
        source target
        (population_card_le_of_injection φ d sourceWalk targetWalk
          source target prior) p := by
  rfl

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
    (parents : Cloud.DominatingInjection φ
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
  let parents := Cloud.DominatingInjection.ofInjectivelyDominatesBy hparents
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

/-- One-generation coupling with arbitrary offspring sets.  Parent populations
and retained populations are finite because they come from a capacity
selection, while every parent may have an uncountable set of child slots. -/
theorem nextGeneration_injectivelyDominatesBy_of_isFirstNBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (sourceParents targetParents : Finset (RootIndexed.TreeNode Root α))
    (sourceSlots targetSlots : RootIndexed.TreeNode Root α → Set α)
    (retainedChildren selectedTarget :
      Finset (RootIndexed.TreeNode Root α))
    (hretained : ↑retainedChildren ⊆
      offspringAddressSet (↑sourceParents) sourceSlots)
    (hcard : retainedChildren.card ≤ N)
    (hselected : IsFirstNBy N
      (fun q => φ (targetWalk.position d q.1 q.2))
      (offspringAddressSet (↑targetParents) targetSlots) selectedTarget)
    (parents : Cloud.DominatingInjection φ
      (populationCloud d sourceWalk sourceParents)
      (populationCloud d targetWalk targetParents) ())
    (hslots : ∀ p ∈ sourceParents,
      sourceSlots p ⊆ targetSlots (parents p))
    (hsharedIncrement : ∀ p ∈ sourceParents, ∀ i ∈ sourceSlots p,
        value' ((targetWalk.step (parents p).1 (parents p).2).map d) i =
          value' ((sourceWalk.step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    (populationCloud d sourceWalk retainedChildren).InjectivelyDominatesBy φ
      (populationCloud d targetWalk selectedTarget) () := by
  classical
  let sourcePair (child : RootIndexed.TreeNode Root α)
      (hchild : child ∈ retainedChildren) :
      RootIndexed.TreeNode Root α × α :=
    Classical.choose (hretained hchild)
  have sourcePair_spec (child : RootIndexed.TreeNode Root α)
      (hchild : child ∈ retainedChildren) :
      sourcePair child hchild ∈
          offspringPairSet (↑sourceParents) sourceSlots ∧
        childAddress (sourcePair child hchild).1
          (sourcePair child hchild).2 = child :=
    Classical.choose_spec (hretained hchild)
  let embedChild (child : RootIndexed.TreeNode Root α)
      (hchild : child ∈ retainedChildren) :
      RootIndexed.TreeNode Root α :=
    childAddress (parents (sourcePair child hchild).1)
      (sourcePair child hchild).2
  have hembedMem : ∀ child hchild,
      embedChild child hchild ∈
        offspringAddressSet (↑targetParents) targetSlots := by
    intro child hchild
    have hpair := (sourcePair_spec child hchild).1
    exact mem_offspringAddressSet.mpr
      ⟨parents (sourcePair child hchild).1,
        (by simpa using parents.mapsTo (by simpa using hpair.1)),
        (sourcePair child hchild).2,
        hslots _ hpair.1 hpair.2, rfl⟩
  have hembedInj : ∀ child hchild child' hchild',
      embedChild child hchild = embedChild child' hchild' → child = child' := by
    intro child hchild child' hchild' heq
    change childAddress (parents (sourcePair child hchild).1)
        (sourcePair child hchild).2 =
      childAddress (parents (sourcePair child' hchild').1)
        (sourcePair child' hchild').2 at heq
    have hpairs :
        (parents (sourcePair child hchild).1,
            (sourcePair child hchild).2) =
          (parents (sourcePair child' hchild').1,
            (sourcePair child' hchild').2) := by
      apply childAddress_joint_injective
      exact heq
    obtain ⟨hmatchedParents, hslotsEq⟩ := Prod.ext_iff.mp hpairs
    have hpair : sourcePair child hchild = sourcePair child' hchild' := by
      have hparentsEq : (sourcePair child hchild).1 =
          (sourcePair child' hchild').1 :=
        parents.injOn
          (by simpa using (sourcePair_spec child hchild).1.1)
          (by simpa using (sourcePair_spec child' hchild').1.1)
          hmatchedParents
      exact Prod.ext
        hparentsEq hslotsEq
    rw [← (sourcePair_spec child hchild).2,
      ← (sourcePair_spec child' hchild').2, hpair]
  have hembedLeft : ∀ child hchild,
      φ (targetWalk.position d (embedChild child hchild).1
          (embedChild child hchild).2) ≤
        φ (sourceWalk.position d child.1 child.2) := by
    intro child hchild
    have hpair := (sourcePair_spec child hchild).1
    have hsourcePosition :
        sourceWalk.position d (sourcePair child hchild).1.1
            ((sourcePair child hchild).1.2 ++ [(sourcePair child hchild).2]) =
          sourceWalk.position d child.1 child.2 := by
      exact congrArg (fun q : RootIndexed.TreeNode Root α =>
        sourceWalk.position d q.1 q.2) (sourcePair_spec child hchild).2
    change φ (targetWalk.position d (parents (sourcePair child hchild).1).1
        ((parents (sourcePair child hchild).1).2 ++
          [(sourcePair child hchild).2])) ≤
      φ (sourceWalk.position d child.1 child.2)
    rw [← hsourcePosition, sourceWalk.position_child, targetWalk.position_child,
      hsharedIncrement _ hpair.1 _ hpair.2]
    exact htranslate _ _ _
      (by simpa using parents.dominates _ (by simpa using hpair.1))
  obtain ⟨f, hfmem, hfle, hfinj⟩ :=
    exists_injective_le_of_dependent_embedding_of_isFirstNBy N
      (fun p => φ (sourceWalk.position d p.1 p.2))
      (fun q => φ (targetWalk.position d q.1 q.2))
      retainedChildren (offspringAddressSet (↑targetParents) targetSlots)
      selectedTarget hselected hcard embedChild hembedMem hembedInj hembedLeft
  let matchParticle : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α :=
    fun p => if hp : p ∈ retainedChildren then f p hp else p
  refine ⟨matchParticle, ?_, ?_, ?_⟩
  · intro p hp
    have hpr : p ∈ retainedChildren := by simpa using hp
    simpa [populationCloud, matchParticle, hpr] using hfmem p hpr
  · intro p hp q hq heq
    have hpr : p ∈ retainedChildren := by simpa using hp
    have hqr : q ∈ retainedChildren := by simpa using hq
    apply hfinj p hpr q hqr
    simpa [matchParticle, hpr, hqr] using heq
  · intro p hp
    have hpr : p ∈ retainedChildren := by simpa using hp
    simpa [populationCloud, matchParticle, hpr] using hfle p hpr

/-- Data-valued form of the one-generation coupling.  The returned injection
can be carried into the next generation instead of being immediately hidden
under an existential quantifier. -/
noncomputable def nextGenerationInjection_of_isFirstNBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (sourceParents targetParents : Finset (RootIndexed.TreeNode Root α))
    (sourceSlots targetSlots : RootIndexed.TreeNode Root α → Set α)
    (retainedChildren selectedTarget :
      Finset (RootIndexed.TreeNode Root α))
    (hretained : ↑retainedChildren ⊆
      offspringAddressSet (↑sourceParents) sourceSlots)
    (hcard : retainedChildren.card ≤ N)
    (hselected : IsFirstNBy N
      (fun q => φ (targetWalk.position d q.1 q.2))
      (offspringAddressSet (↑targetParents) targetSlots) selectedTarget)
    (parents : Cloud.DominatingInjection φ
      (populationCloud d sourceWalk sourceParents)
      (populationCloud d targetWalk targetParents) ())
    (hslots : ∀ p ∈ sourceParents,
      sourceSlots p ⊆ targetSlots (parents p))
    (hsharedIncrement : ∀ p ∈ sourceParents, ∀ i ∈ sourceSlots p,
        value' ((targetWalk.step (parents p).1 (parents p).2).map d) i =
          value' ((sourceWalk.step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    Cloud.DominatingInjection φ
      (populationCloud d sourceWalk retainedChildren)
      (populationCloud d targetWalk selectedTarget) () := by
  classical
  have hdom := nextGeneration_injectivelyDominatesBy_of_isFirstNBy
      φ d N sourceWalk targetWalk sourceParents targetParents
      sourceSlots targetSlots retainedChildren selectedTarget
      hretained hcard hselected parents
      hslots hsharedIncrement htranslate
  let prior := Cloud.DominatingInjection.ofInjectivelyDominatesBy hdom
  have hcardSelected : retainedChildren.card ≤ selectedTarget.card := by
    apply Finset.card_le_card_of_injOn prior
    · intro p hp
      simpa [populationCloud] using
        prior.mapsTo (by simpa [populationCloud] using hp)
    · intro p hp q hq hpq
      exact prior.injOn (by simpa [populationCloud] using hp)
        (by simpa [populationCloud] using hq) hpq
  let sourceValue : RootIndexed.TreeNode Root α → Value :=
    fun p => φ (sourceWalk.position d p.1 p.2)
  let targetValue : RootIndexed.TreeNode Root α → Value :=
    fun q => φ (targetWalk.position d q.1 q.2)
  have hthreshold : ∀ a : Value,
      (retainedChildren.filter fun p => sourceValue p ≤ a).card ≤
        (selectedTarget.filter fun q => targetValue q ≤ a).card := by
    intro a
    simpa [sourceValue, targetValue, populationCloud] using
      Cloud.filter_card_le_of_injectivelyDominatesBy φ ()
        retainedChildren.finite_toSet selectedTarget.finite_toSet hdom a
  let matchParticle : RootIndexed.TreeNode Root α →
      RootIndexed.TreeNode Root α :=
    matchByRankOrSelf sourceValue targetValue retainedChildren selectedTarget
      hcardSelected
  refine ⟨matchParticle, ?_, ?_, ?_⟩
  · intro p hp
    have hpr : p ∈ retainedChildren := by simpa [populationCloud] using hp
    change matchParticle p ∈ selectedTarget
    exact matchByRankOrSelf_mem sourceValue targetValue retainedChildren
      selectedTarget hcardSelected hpr
  · intro p hp q hq hpq
    apply matchByRankOrSelf_injOn sourceValue targetValue retainedChildren
      selectedTarget hcardSelected
    · simpa [populationCloud] using hp
    · simpa [populationCloud] using hq
    · exact hpq
  · intro p hp
    have hpr : p ∈ retainedChildren := by simpa [populationCloud] using hp
    exact matchByRankOrSelf_value_le sourceValue targetValue retainedChildren
      selectedTarget hcardSelected hthreshold hpr

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
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    (populationCloud d sourceWalk retainedChildren).InjectivelyDominatesBy φ
      (populationCloud d targetWalk
        (selectFirstNBy N
          (fun q => φ (targetWalk.position d q.1 q.2))
          (offspringAddresses targetParents targetSlots))) () := by
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
