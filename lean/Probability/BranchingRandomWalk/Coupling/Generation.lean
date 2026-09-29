module

public import Combinatorics.BranchingWalk.Selection.NSelection.Coupling.Generation

/-!
# Pathwise iteration of the multi-root selection coupling

Random branching walks and their selected populations are functions of an
ambient sample `ω`.  The deterministic one-generation theorem can therefore
be iterated pointwise.  This file records that iteration without imposing a
countability assumption on either the root labels or the child slots.

Measurability of a concrete population process is a separate obligation: it
is supplied by the causal-selection interfaces.  The spatial comparison
below is a pathwise statement and consequently needs no measurable structure.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.UlamHarris
open Combinatorics.Branching
open Combinatorics.Branching.Selection
open Combinatorics.Branching.Selection.Coupling
open Combinatorics.Branching.Selection.NSelection

variable {Ω Root α Mark Position Value : Type*}

/-- Pathwise one-generation coupling with arbitrary, possibly uncountable,
offspring-slot sets.  Randomness only indexes the deterministic objects; the
selected target population is certified by the abstract first-`N` property. -/
theorem nextGeneration_injectivelyDominatesBy_of_isFirstNBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (sourceWalk targetWalk : Ω → RootIndexed.BranchingWalk Root α Mark Position)
    (sourceParents targetParents : Ω → Finset (RootIndexed.TreeNode Root α))
    (sourceSlots targetSlots : Ω → RootIndexed.TreeNode Root α → Set α)
    (retainedChildren selectedTarget :
      Ω → Finset (RootIndexed.TreeNode Root α))
    (hretained : ∀ ω, ↑(retainedChildren ω) ⊆
      offspringAddressSet (↑(sourceParents ω)) (sourceSlots ω))
    (hcard : ∀ ω, (retainedChildren ω).card ≤ N)
    (hselected : ∀ ω, IsFirstNBy N
      (fun q => φ ((targetWalk ω).position d q.1 q.2))
      (offspringAddressSet (↑(targetParents ω)) (targetSlots ω))
      (selectedTarget ω))
    (parents : ∀ ω, Cloud.SliceDominatingMap φ
      (populationCloud d (sourceWalk ω) (sourceParents ω))
      (populationCloud d (targetWalk ω) (targetParents ω)) ())
    (hslots : ∀ ω p, p ∈ sourceParents ω →
      sourceSlots ω p ⊆ targetSlots ω (parents ω p))
    (hsharedIncrement : ∀ ω p, p ∈ sourceParents ω →
      ∀ i ∈ sourceSlots ω p,
        value' (((targetWalk ω).step (parents ω p).1 (parents ω p).2).map d) i =
          value' (((sourceWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ ω,
      (populationCloud d (sourceWalk ω) (retainedChildren ω)).InjectivelyDominatesBy φ
        (populationCloud d (targetWalk ω) (selectedTarget ω)) () := by
  intro ω
  exact Combinatorics.Branching.Selection.Coupling.nextGeneration_injectivelyDominatesBy_of_isFirstNBy
      φ d N (sourceWalk ω) (targetWalk ω)
      (sourceParents ω) (targetParents ω)
      (sourceSlots ω) (targetSlots ω)
      (retainedChildren ω) (selectedTarget ω)
      (hretained ω) (hcard ω) (hselected ω) (parents ω)
      (hslots ω) (hsharedIncrement ω) htranslate

/-- Iterate the arbitrary-offspring coupling through all generations.  The
target population at each successor generation may be any measurable or
nonmeasurable realization satisfying `IsFirstNBy`; measurability is a separate
probability-layer obligation. -/
theorem injectivelyDominatesBy_all_generations_of_isFirstNBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (sourceWalk targetWalk : Ω → RootIndexed.BranchingWalk Root α Mark Position)
    (sourcePopulation targetPopulation :
      ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (sourceSlots targetSlots :
      ℕ → Ω → RootIndexed.TreeNode Root α → Set α)
    (hinitial : ∀ ω,
      (populationCloud d (sourceWalk ω) (sourcePopulation 0 ω)).InjectivelyDominatesBy φ
        (populationCloud d (targetWalk ω) (targetPopulation 0 ω)) ())
    (hsourceSubset : ∀ n ω, ↑(sourcePopulation (n + 1) ω) ⊆
      offspringAddressSet (↑(sourcePopulation n ω)) (sourceSlots n ω))
    (hsourceCard : ∀ n ω, (sourcePopulation (n + 1) ω).card ≤ N)
    (htarget : ∀ n ω, IsFirstNBy N
      (fun q => φ ((targetWalk ω).position d q.1 q.2))
      (offspringAddressSet (↑(targetPopulation n ω)) (targetSlots n ω))
      (targetPopulation (n + 1) ω))
    (hslots : ∀ n ω (parents : Cloud.SliceDominatingMap φ
        (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
        (populationCloud d (targetWalk ω) (targetPopulation n ω)) ()),
      ∀ p ∈ sourcePopulation n ω,
        sourceSlots n ω p ⊆ targetSlots n ω (parents p))
    (hsharedIncrement : ∀ n ω (parents : Cloud.SliceDominatingMap φ
        (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
        (populationCloud d (targetWalk ω) (targetPopulation n ω)) ()),
      ∀ p ∈ sourcePopulation n ω, ∀ i ∈ sourceSlots n ω p,
        value' (((targetWalk ω).step (parents p).1 (parents p).2).map d) i =
          value' (((sourceWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ n ω,
      (populationCloud d (sourceWalk ω) (sourcePopulation n ω)).InjectivelyDominatesBy φ
        (populationCloud d (targetWalk ω) (targetPopulation n ω)) () := by
  intro n
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      let parents : ∀ ω, Cloud.SliceDominatingMap φ
          (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
          (populationCloud d (targetWalk ω) (targetPopulation n ω)) () :=
        fun ω => Cloud.SliceDominatingMap.ofInjectivelyDominatesBy (ih ω)
      apply nextGeneration_injectivelyDominatesBy_of_isFirstNBy
        φ d N sourceWalk targetWalk
        (sourcePopulation n) (targetPopulation n)
        (sourceSlots n) (targetSlots n)
        (sourcePopulation (n + 1)) (targetPopulation (n + 1))
        (hsourceSubset n) (hsourceCard n) (htarget n) parents
      · intro ω p hp i hi
        exact hslots n ω (parents ω) p hp hi
      · intro ω p hp i hi
        exact hsharedIncrement n ω (parents ω) p hp i hi
      · exact htranslate

/-- A pathwise coupling state at every generation.  In contrast with
`injectivelyDominatesBy_all_generations_of_isFirstNBy`, this construction
retains the actual particle injection produced at each induction step. -/
noncomputable def generationInjection_of_isFirstNBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (sourceWalk targetWalk : Ω → RootIndexed.BranchingWalk Root α Mark Position)
    (sourcePopulation targetPopulation :
      ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (sourceSlots targetSlots :
      ℕ → Ω → RootIndexed.TreeNode Root α → Set α)
    (initial : ∀ ω, Cloud.SliceDominatingMap φ
      (populationCloud d (sourceWalk ω) (sourcePopulation 0 ω))
      (populationCloud d (targetWalk ω) (targetPopulation 0 ω)) ())
    (hsourceSubset : ∀ n ω, ↑(sourcePopulation (n + 1) ω) ⊆
      offspringAddressSet (↑(sourcePopulation n ω)) (sourceSlots n ω))
    (hsourceCard : ∀ n ω, (sourcePopulation (n + 1) ω).card ≤ N)
    (htarget : ∀ n ω, IsFirstNBy N
      (fun q => φ ((targetWalk ω).position d q.1 q.2))
      (offspringAddressSet (↑(targetPopulation n ω)) (targetSlots n ω))
      (targetPopulation (n + 1) ω))
    (hslots : ∀ n ω (parents : Cloud.SliceDominatingMap φ
        (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
        (populationCloud d (targetWalk ω) (targetPopulation n ω)) ()),
      ∀ p ∈ sourcePopulation n ω,
        sourceSlots n ω p ⊆ targetSlots n ω (parents p))
    (hsharedIncrement : ∀ n ω (parents : Cloud.SliceDominatingMap φ
        (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
        (populationCloud d (targetWalk ω) (targetPopulation n ω)) ()),
      ∀ p ∈ sourcePopulation n ω, ∀ i ∈ sourceSlots n ω p,
        value' (((targetWalk ω).step (parents p).1 (parents p).2).map d) i =
          value' (((sourceWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : Ω) :
    Cloud.SliceDominatingMap φ
      (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
      (populationCloud d (targetWalk ω) (targetPopulation n ω)) () :=
  Nat.rec (motive := fun n => Cloud.SliceDominatingMap φ
      (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
      (populationCloud d (targetWalk ω) (targetPopulation n ω)) ())
    (initial ω)
    (fun k parents =>
      Combinatorics.Branching.Selection.Coupling.nextGenerationInjection_of_isFirstNBy
        φ d N (sourceWalk ω) (targetWalk ω)
        (sourcePopulation k ω) (targetPopulation k ω)
        (sourceSlots k ω) (targetSlots k ω)
        (sourcePopulation (k + 1) ω) (targetPopulation (k + 1) ω)
        (hsourceSubset k ω) (hsourceCard k ω) (htarget k ω) parents
        (hslots k ω parents) (hsharedIncrement k ω parents) htranslate)
    n

/-- Forgetting the data-valued recursive coupling recovers domination at
every generation. -/
theorem generationInjection_of_isFirstNBy_injectivelyDominatesBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (sourceWalk targetWalk : Ω → RootIndexed.BranchingWalk Root α Mark Position)
    (sourcePopulation targetPopulation :
      ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (sourceSlots targetSlots :
      ℕ → Ω → RootIndexed.TreeNode Root α → Set α)
    (initial : ∀ ω, Cloud.SliceDominatingMap φ
      (populationCloud d (sourceWalk ω) (sourcePopulation 0 ω))
      (populationCloud d (targetWalk ω) (targetPopulation 0 ω)) ())
    (hsourceSubset : ∀ n ω, ↑(sourcePopulation (n + 1) ω) ⊆
      offspringAddressSet (↑(sourcePopulation n ω)) (sourceSlots n ω))
    (hsourceCard : ∀ n ω, (sourcePopulation (n + 1) ω).card ≤ N)
    (htarget : ∀ n ω, IsFirstNBy N
      (fun q => φ ((targetWalk ω).position d q.1 q.2))
      (offspringAddressSet (↑(targetPopulation n ω)) (targetSlots n ω))
      (targetPopulation (n + 1) ω))
    (hslots : ∀ n ω (parents : Cloud.SliceDominatingMap φ
        (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
        (populationCloud d (targetWalk ω) (targetPopulation n ω)) ()),
      ∀ p ∈ sourcePopulation n ω,
        sourceSlots n ω p ⊆ targetSlots n ω (parents p))
    (hsharedIncrement : ∀ n ω (parents : Cloud.SliceDominatingMap φ
        (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
        (populationCloud d (targetWalk ω) (targetPopulation n ω)) ()),
      ∀ p ∈ sourcePopulation n ω, ∀ i ∈ sourceSlots n ω p,
        value' (((targetWalk ω).step (parents p).1 (parents p).2).map d) i =
          value' (((sourceWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : Ω) :
    (populationCloud d
      (sourceWalk ω) (sourcePopulation n ω)).InjectivelyDominatesBy φ
      (populationCloud d
        (targetWalk ω) (targetPopulation n ω)) () :=
  (generationInjection_of_isFirstNBy φ d N sourceWalk targetWalk
    sourcePopulation targetPopulation sourceSlots targetSlots initial
    hsourceSubset hsourceCard htarget hslots hsharedIncrement htranslate
    n ω).injectivelyDominatesBy

/-- One pathwise generation of a random multi-root coupling.  All random
objects are evaluated at the same sample, so the result is exactly the
deterministic generation theorem with no additional probability assumptions.
-/
theorem nextGeneration_injectivelyDominatesBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (sourceWalk targetWalk : Ω → RootIndexed.BranchingWalk Root α Mark Position)
    (sourceParents targetParents : Ω → Finset (RootIndexed.TreeNode Root α))
    (sourceSlots targetSlots : Ω → RootIndexed.TreeNode Root α → Finset α)
    (retainedChildren : Ω → Finset (RootIndexed.TreeNode Root α))
    (hretained : ∀ ω, retainedChildren ω ⊆
      offspringAddresses (sourceParents ω) (sourceSlots ω))
    (hcard : ∀ ω, (retainedChildren ω).card ≤ N)
    (hparents : ∀ ω,
      (populationCloud d (sourceWalk ω) (sourceParents ω)).InjectivelyDominatesBy φ
        (populationCloud d (targetWalk ω) (targetParents ω)) ())
    (hslots : ∀ ω p, p ∈ sourceParents ω → ∀ q, q ∈ targetParents ω →
      φ ((targetWalk ω).position d q.1 q.2) ≤
          φ ((sourceWalk ω).position d p.1 p.2) →
      sourceSlots ω p ⊆ targetSlots ω q)
    (hsharedIncrement : ∀ ω p, p ∈ sourceParents ω →
      ∀ q, q ∈ targetParents ω →
      φ ((targetWalk ω).position d q.1 q.2) ≤
          φ ((sourceWalk ω).position d p.1 p.2) →
      ∀ i ∈ sourceSlots ω p,
        value' (((targetWalk ω).step q.1 q.2).map d) i =
          value' (((sourceWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ ω,
      (populationCloud d (sourceWalk ω) (retainedChildren ω)).InjectivelyDominatesBy φ
        (populationCloud d (targetWalk ω)
          (selectFirstNBy N
            (fun q => φ ((targetWalk ω).position d q.1 q.2))
            (offspringAddresses (targetParents ω) (targetSlots ω)))) () := by
  intro ω
  exact Combinatorics.Branching.Selection.Coupling.nextGeneration_injectivelyDominatesBy
    φ d N (sourceWalk ω) (targetWalk ω)
    (sourceParents ω) (targetParents ω) (sourceSlots ω) (targetSlots ω)
    (retainedChildren ω) (hretained ω) (hcard ω) (hparents ω)
    (hslots ω) (hsharedIncrement ω) htranslate

/-- Iteration of the pathwise multi-root coupling through every generation.

The target population at generation `n + 1` is the dynamic leftmost `N`
selection from its actual children, ordered by the observed value `φ` at that
sample.  The source may use any (possibly random and causal) retained subset
of its children, provided its cardinality is at most `N`. -/
theorem injectivelyDominatesBy_all_generations
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (sourceWalk targetWalk : Ω → RootIndexed.BranchingWalk Root α Mark Position)
    (sourcePopulation targetPopulation :
      ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (sourceSlots targetSlots :
      ℕ → Ω → RootIndexed.TreeNode Root α → Finset α)
    (hinitial : ∀ ω,
      (populationCloud d (sourceWalk ω) (sourcePopulation 0 ω)).InjectivelyDominatesBy φ
        (populationCloud d (targetWalk ω) (targetPopulation 0 ω)) ())
    (hsourceSubset : ∀ n ω, sourcePopulation (n + 1) ω ⊆
      offspringAddresses (sourcePopulation n ω) (sourceSlots n ω))
    (hsourceCard : ∀ n ω, (sourcePopulation (n + 1) ω).card ≤ N)
    (htarget : ∀ n ω, targetPopulation (n + 1) ω =
      selectFirstNBy N
        (fun q => φ ((targetWalk ω).position d q.1 q.2))
        (offspringAddresses (targetPopulation n ω) (targetSlots n ω)))
    (hslots : ∀ n ω p, p ∈ sourcePopulation n ω →
      ∀ q, q ∈ targetPopulation n ω →
      φ ((targetWalk ω).position d q.1 q.2) ≤
          φ ((sourceWalk ω).position d p.1 p.2) →
      sourceSlots n ω p ⊆ targetSlots n ω q)
    (hsharedIncrement : ∀ n ω p, p ∈ sourcePopulation n ω →
      ∀ q, q ∈ targetPopulation n ω →
      φ ((targetWalk ω).position d q.1 q.2) ≤
          φ ((sourceWalk ω).position d p.1 p.2) →
      ∀ i ∈ sourceSlots n ω p,
        value' (((targetWalk ω).step q.1 q.2).map d) i =
          value' (((sourceWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ n ω,
      (populationCloud d (sourceWalk ω) (sourcePopulation n ω)).InjectivelyDominatesBy φ
        (populationCloud d (targetWalk ω) (targetPopulation n ω)) () := by
  intro n
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      intro ω
      rw [htarget n ω]
      exact Combinatorics.Branching.Selection.Coupling.nextGeneration_injectivelyDominatesBy
        φ d N (sourceWalk ω) (targetWalk ω)
        (sourcePopulation n ω) (targetPopulation n ω)
        (sourceSlots n ω) (targetSlots n ω)
        (sourcePopulation (n + 1) ω)
        (hsourceSubset n ω) (hsourceCard n ω) (ih ω)
        (hslots n ω) (hsharedIncrement n ω) htranslate

end ProbabilityTheory.BranchingRandomWalk.Coupling
