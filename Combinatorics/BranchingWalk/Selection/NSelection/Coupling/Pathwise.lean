/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Population.Offspring

public import Combinatorics.BranchingWalk.Selection.NSelection.Coupling.Step

/-!
# Pathwise iteration of the multi-root selection coupling

## Public declarations

At every sample \(\omega\) and generation \(n\), let
`selectedBranchingWalkChildren n ω` be the children retained by the general
selection process and `nSelectedBranchingWalkChildren n ω` the children
retained by \(N\)-selection. Under the one-generation coupling hypotheses,
there is a spatially dominating injection at every generation:

\[
\forall n,\omega,\quad
\exists\,\varphi_{n,\omega}:
  \texttt{selectedBranchingWalkChildren}(n,\omega)\hookrightarrow
  \texttt{nSelectedBranchingWalkChildren}(n,\omega),\\
\forall p\in\texttt{selectedBranchingWalkChildren}(n,\omega),\quad
\texttt{nSelectedBranchingWalkOrderKey}(\varphi_{n,\omega}(p))
\le \texttt{selectedBranchingWalkOrderKey}(p).
\]

Random branching walks and their selected populations are functions of an
ambient sample `ω`.  The deterministic one-generation theorem can therefore
be iterated pointwise.  This file records that iteration without imposing a
countability assumption on either the root labels or the child slots.

Measurability of a concrete population process is a separate obligation: it
is supplied by the causal-selection interfaces.  The spatial comparison
below is a pathwise statement and consequently needs no measurable structure.

The public API gives pointwise one-step and all-generation forms of
`InjectivelyDominatesBy`: `nextGeneration_injectivelyDominatesBy_of_isFirstNBy`
and `injectivelyDominatesBy_all_generations_of_isFirstNBy` assume an arbitrary
first-`N` certificate for each sample; `nextGeneration_injectivelyDominatesBy`
and `injectivelyDominatesBy_all_generations` use dynamic leftmost selection.
The all-generation conclusion has the form
`∀ n ω, selectedBranchingWalkChildren n ω.InjectivelyDominatesBy φ
(nSelectedBranchingWalkChildren n ω) ()`.
`generationInjection_of_isFirstNBy` and
`generationInjection_of_isFirstNBy_injectivelyDominatesBy` construct the
corresponding maps for every generation and sample, with membership,
injectivity, and non-increasing observed-position properties.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.Coupling.Pathwise

open Combinatorics.UlamHarris
open Combinatorics.Branching
open _root_.Combinatorics.Selection
open Combinatorics.Branching.Selection
open Combinatorics.Branching.Selection.Coupling
open _root_.Combinatorics.Selection.NSelection

variable {Ω Root α Mark Position OrderKey : Type*}

/-- Pathwise one-generation coupling with arbitrary, possibly uncountable,
offspring-slot sets. Randomness only indexes the deterministic objects; the
`nSelectedBranchingWalkChildren` are certified by the abstract first-`N`
property. -/
theorem nextGeneration_injectivelyDominatesBy_of_isFirstNBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (selectedBranchingWalk nSelectedBranchingWalk : Ω → RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkParents nSelectedBranchingWalkParents : Ω → Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots : Ω → RootIndexed.TreeNode Root α → Set α)
    (selectedBranchingWalkChildren nSelectedBranchingWalkChildren :
      Ω → Finset (RootIndexed.TreeNode Root α))
    (hselectedChildren_subset_offspring : ∀ ω, ↑(selectedBranchingWalkChildren ω) ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑(selectedBranchingWalkParents ω)) (selectedBranchingWalkChildSlots ω))
    (hselectedChildren_card_le_N : ∀ ω, (selectedBranchingWalkChildren ω).card ≤ N)
    (hnSelectedChildren_isFirstNBy : ∀ ω, IsFirstNBy N
      (fun q => φ ((nSelectedBranchingWalk ω).position d q.1 q.2))
      (Combinatorics.Branching.Population.offspringAddressSet (↑(nSelectedBranchingWalkParents ω)) (nSelectedBranchingWalkChildSlots ω))
      (nSelectedBranchingWalkChildren ω))
    (nSelectedBranchingWalkParentMatching : ∀ ω, Cloud.SliceDominatingMap φ
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkParents ω))
      (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkParents ω)) ())
    (hchildSlots_mono_under_parentMatching : ∀ ω p, p ∈ selectedBranchingWalkParents ω →
      selectedBranchingWalkChildSlots ω p ⊆ nSelectedBranchingWalkChildSlots ω (nSelectedBranchingWalkParentMatching ω p))
    (hmatchedParents_sharedIncrement : ∀ ω p, p ∈ selectedBranchingWalkParents ω →
      ∀ i ∈ selectedBranchingWalkChildSlots ω p,
        value' (((nSelectedBranchingWalk ω).step (nSelectedBranchingWalkParentMatching ω p).1 (nSelectedBranchingWalkParentMatching ω p).2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (horderKey_translation_mono : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren ω)).InjectivelyDominatesBy φ
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren ω)) () := by
  intro ω
  exact Combinatorics.Branching.Selection.Coupling.nextGeneration_injectivelyDominatesBy_of_isFirstNBy
      φ d N (selectedBranchingWalk ω) (nSelectedBranchingWalk ω)
      (selectedBranchingWalkParents ω) (nSelectedBranchingWalkParents ω)
      (selectedBranchingWalkChildSlots ω) (nSelectedBranchingWalkChildSlots ω)
      (selectedBranchingWalkChildren ω) (nSelectedBranchingWalkChildren ω)
      (hselectedChildren_subset_offspring ω) (hselectedChildren_card_le_N ω) (hnSelectedChildren_isFirstNBy ω) (nSelectedBranchingWalkParentMatching ω)
      (hchildSlots_mono_under_parentMatching ω) (hmatchedParents_sharedIncrement ω) horderKey_translation_mono

/-- Iterate the arbitrary-offspring coupling through all generations. The
`nSelectedBranchingWalk` population at each successor generation may be any
realization satisfying `IsFirstNBy`; measurability is a separate
probability-layer obligation. -/
theorem injectivelyDominatesBy_all_generations_of_isFirstNBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (selectedBranchingWalk nSelectedBranchingWalk : Ω → RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkChildren nSelectedBranchingWalkChildren :
      ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots :
      ℕ → Ω → RootIndexed.TreeNode Root α → Set α)
    (hinitialSelectedPopulation_dominates_nSelectedPopulation : ∀ ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren 0 ω)).InjectivelyDominatesBy φ
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren 0 ω)) ())
    (hselectedChildren_subset_offspring : ∀ n ω, ↑(selectedBranchingWalkChildren (n + 1) ω) ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑(selectedBranchingWalkChildren n ω)) (selectedBranchingWalkChildSlots n ω))
    (hselectedChildren_card_le_N : ∀ n ω, (selectedBranchingWalkChildren (n + 1) ω).card ≤ N)
    (hnSelectedChildren_isFirstNBy : ∀ n ω, IsFirstNBy N
      (fun q => φ ((nSelectedBranchingWalk ω).position d q.1 q.2))
      (Combinatorics.Branching.Population.offspringAddressSet (↑(nSelectedBranchingWalkChildren n ω)) (nSelectedBranchingWalkChildSlots n ω))
      (nSelectedBranchingWalkChildren (n + 1) ω))
    (hchildSlots_mono_under_parentMatching : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω,
        selectedBranchingWalkChildSlots n ω p ⊆ nSelectedBranchingWalkChildSlots n ω (nSelectedBranchingWalkParentMatching p))
    (hmatchedParents_sharedIncrement : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω, ∀ i ∈ selectedBranchingWalkChildSlots n ω p,
        value' (((nSelectedBranchingWalk ω).step (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (horderKey_translation_mono : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ n ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω)).InjectivelyDominatesBy φ
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) () := by
  intro n
  induction n with
  | zero => exact hinitialSelectedPopulation_dominates_nSelectedPopulation
  | succ n ih =>
      let nSelectedBranchingWalkParentMatching : ∀ ω, Cloud.SliceDominatingMap φ
          (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
          (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) () :=
        fun ω => Cloud.SliceDominatingMap.ofInjectivelyDominatesBy (ih ω)
      apply nextGeneration_injectivelyDominatesBy_of_isFirstNBy
        φ d N selectedBranchingWalk nSelectedBranchingWalk
        (selectedBranchingWalkChildren n) (nSelectedBranchingWalkChildren n)
        (selectedBranchingWalkChildSlots n) (nSelectedBranchingWalkChildSlots n)
        (selectedBranchingWalkChildren (n + 1)) (nSelectedBranchingWalkChildren (n + 1))
        (hselectedChildren_subset_offspring n) (hselectedChildren_card_le_N n) (hnSelectedChildren_isFirstNBy n) nSelectedBranchingWalkParentMatching
      · intro ω p hp i hi
        exact hchildSlots_mono_under_parentMatching n ω (nSelectedBranchingWalkParentMatching ω) p hp hi
      · intro ω p hp i hi
        exact hmatchedParents_sharedIncrement n ω (nSelectedBranchingWalkParentMatching ω) p hp i hi
      · exact horderKey_translation_mono

/-- A pathwise coupling state at every generation.  In contrast with
`injectivelyDominatesBy_all_generations_of_isFirstNBy`, this construction
retains the actual particle injection produced at each induction step. -/
noncomputable def generationInjection_of_isFirstNBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (selectedBranchingWalk nSelectedBranchingWalk : Ω → RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkChildren nSelectedBranchingWalkChildren :
      ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots :
      ℕ → Ω → RootIndexed.TreeNode Root α → Set α)
    (hinitialSelectedPopulation_dominates_nSelectedPopulation : ∀ ω, Cloud.SliceDominatingMap φ
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren 0 ω))
      (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren 0 ω)) ())
    (hselectedChildren_subset_offspring : ∀ n ω, ↑(selectedBranchingWalkChildren (n + 1) ω) ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑(selectedBranchingWalkChildren n ω)) (selectedBranchingWalkChildSlots n ω))
    (hselectedChildren_card_le_N : ∀ n ω, (selectedBranchingWalkChildren (n + 1) ω).card ≤ N)
    (hnSelectedChildren_isFirstNBy : ∀ n ω, IsFirstNBy N
      (fun q => φ ((nSelectedBranchingWalk ω).position d q.1 q.2))
      (Combinatorics.Branching.Population.offspringAddressSet (↑(nSelectedBranchingWalkChildren n ω)) (nSelectedBranchingWalkChildSlots n ω))
      (nSelectedBranchingWalkChildren (n + 1) ω))
    (hchildSlots_mono_under_parentMatching : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω,
        selectedBranchingWalkChildSlots n ω p ⊆ nSelectedBranchingWalkChildSlots n ω (nSelectedBranchingWalkParentMatching p))
    (hmatchedParents_sharedIncrement : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω, ∀ i ∈ selectedBranchingWalkChildSlots n ω p,
        value' (((nSelectedBranchingWalk ω).step (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (horderKey_translation_mono : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : Ω) :
    Cloud.SliceDominatingMap φ
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
      (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) () :=
  Nat.rec (motive := fun n => Cloud.SliceDominatingMap φ
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
      (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ())
    (hinitialSelectedPopulation_dominates_nSelectedPopulation ω)
    (fun k nSelectedBranchingWalkParentMatching =>
      Combinatorics.Branching.Selection.Coupling.nextGenerationInjection_of_isFirstNBy
        φ d N (selectedBranchingWalk ω) (nSelectedBranchingWalk ω)
        (selectedBranchingWalkChildren k ω) (nSelectedBranchingWalkChildren k ω)
        (selectedBranchingWalkChildSlots k ω) (nSelectedBranchingWalkChildSlots k ω)
        (selectedBranchingWalkChildren (k + 1) ω) (nSelectedBranchingWalkChildren (k + 1) ω)
        (hselectedChildren_subset_offspring k ω) (hselectedChildren_card_le_N k ω) (hnSelectedChildren_isFirstNBy k ω) nSelectedBranchingWalkParentMatching
        (hchildSlots_mono_under_parentMatching k ω nSelectedBranchingWalkParentMatching) (hmatchedParents_sharedIncrement k ω nSelectedBranchingWalkParentMatching) horderKey_translation_mono)
    n

/-- Forgetting the data-valued recursive coupling recovers domination at
every generation. -/
theorem generationInjection_of_isFirstNBy_injectivelyDominatesBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (selectedBranchingWalk nSelectedBranchingWalk : Ω → RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkChildren nSelectedBranchingWalkChildren :
      ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots :
      ℕ → Ω → RootIndexed.TreeNode Root α → Set α)
    (hinitialSelectedPopulation_dominates_nSelectedPopulation : ∀ ω, Cloud.SliceDominatingMap φ
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren 0 ω))
      (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren 0 ω)) ())
    (hselectedChildren_subset_offspring : ∀ n ω, ↑(selectedBranchingWalkChildren (n + 1) ω) ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑(selectedBranchingWalkChildren n ω)) (selectedBranchingWalkChildSlots n ω))
    (hselectedChildren_card_le_N : ∀ n ω, (selectedBranchingWalkChildren (n + 1) ω).card ≤ N)
    (hnSelectedChildren_isFirstNBy : ∀ n ω, IsFirstNBy N
      (fun q => φ ((nSelectedBranchingWalk ω).position d q.1 q.2))
      (Combinatorics.Branching.Population.offspringAddressSet (↑(nSelectedBranchingWalkChildren n ω)) (nSelectedBranchingWalkChildSlots n ω))
      (nSelectedBranchingWalkChildren (n + 1) ω))
    (hchildSlots_mono_under_parentMatching : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω,
        selectedBranchingWalkChildSlots n ω p ⊆ nSelectedBranchingWalkChildSlots n ω (nSelectedBranchingWalkParentMatching p))
    (hmatchedParents_sharedIncrement : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω, ∀ i ∈ selectedBranchingWalkChildSlots n ω p,
        value' (((nSelectedBranchingWalk ω).step (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (horderKey_translation_mono : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : Ω) :
    (populationCloud d
      (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω)).InjectivelyDominatesBy φ
      (populationCloud d
        (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) () :=
  (generationInjection_of_isFirstNBy φ d N selectedBranchingWalk nSelectedBranchingWalk
    selectedBranchingWalkChildren nSelectedBranchingWalkChildren selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots hinitialSelectedPopulation_dominates_nSelectedPopulation
    hselectedChildren_subset_offspring hselectedChildren_card_le_N hnSelectedChildren_isFirstNBy hchildSlots_mono_under_parentMatching hmatchedParents_sharedIncrement horderKey_translation_mono
    n ω).injectivelyDominatesBy

/-- One pathwise generation of a random multi-root coupling.  All random
objects are evaluated at the same sample, so the result is exactly the
deterministic generation theorem with no additional probability assumptions.
-/
theorem nextGeneration_injectivelyDominatesBy
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (selectedBranchingWalk nSelectedBranchingWalk : Ω → RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkParents nSelectedBranchingWalkParents : Ω → Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots : Ω → RootIndexed.TreeNode Root α → Finset α)
    (selectedBranchingWalkChildren : Ω → Finset (RootIndexed.TreeNode Root α))
    (hselectedChildren_subset_offspring : ∀ ω, selectedBranchingWalkChildren ω ⊆
      offspringAddresses (selectedBranchingWalkParents ω) (selectedBranchingWalkChildSlots ω))
    (hselectedChildren_card_le_N : ∀ ω, (selectedBranchingWalkChildren ω).card ≤ N)
    (hselectedParents_injectivelyDominate_nSelectedParents : ∀ ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkParents ω)).InjectivelyDominatesBy φ
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkParents ω)) ())
    (hchildSlots_mono_under_parentMatching : ∀ ω p, p ∈ selectedBranchingWalkParents ω → ∀ q, q ∈ nSelectedBranchingWalkParents ω →
      φ ((nSelectedBranchingWalk ω).position d q.1 q.2) ≤
          φ ((selectedBranchingWalk ω).position d p.1 p.2) →
      selectedBranchingWalkChildSlots ω p ⊆ nSelectedBranchingWalkChildSlots ω q)
    (hmatchedParents_sharedIncrement : ∀ ω p, p ∈ selectedBranchingWalkParents ω →
      ∀ q, q ∈ nSelectedBranchingWalkParents ω →
      φ ((nSelectedBranchingWalk ω).position d q.1 q.2) ≤
          φ ((selectedBranchingWalk ω).position d p.1 p.2) →
      ∀ i ∈ selectedBranchingWalkChildSlots ω p,
        value' (((nSelectedBranchingWalk ω).step q.1 q.2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (horderKey_translation_mono : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren ω)).InjectivelyDominatesBy φ
        (populationCloud d (nSelectedBranchingWalk ω)
          (selectFirstNBy N
            (fun q => φ ((nSelectedBranchingWalk ω).position d q.1 q.2))
            (offspringAddresses (nSelectedBranchingWalkParents ω) (nSelectedBranchingWalkChildSlots ω)))) () := by
  intro ω
  exact Combinatorics.Branching.Selection.Coupling.nextGeneration_injectivelyDominatesBy
    φ d N (selectedBranchingWalk ω) (nSelectedBranchingWalk ω)
    (selectedBranchingWalkParents ω) (nSelectedBranchingWalkParents ω) (selectedBranchingWalkChildSlots ω) (nSelectedBranchingWalkChildSlots ω)
    (selectedBranchingWalkChildren ω) (hselectedChildren_subset_offspring ω) (hselectedChildren_card_le_N ω) (hselectedParents_injectivelyDominate_nSelectedParents ω)
    (hchildSlots_mono_under_parentMatching ω) (hmatchedParents_sharedIncrement ω) horderKey_translation_mono

/-- Iteration of the pathwise multi-root coupling through every generation.

The `nSelectedBranchingWalk` population at generation `n + 1` is the dynamic
leftmost `N` selection from its actual children, ordered by the observed key
`φ` at that sample. The `selectedBranchingWalk` may use any (possibly random
and causal) retained subset of its children, provided its cardinality is at
most `N`. -/
theorem injectivelyDominatesBy_all_generations
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (selectedBranchingWalk nSelectedBranchingWalk : Ω → RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkChildren nSelectedBranchingWalkChildren :
      ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots :
      ℕ → Ω → RootIndexed.TreeNode Root α → Finset α)
    (hinitialSelectedPopulation_dominates_nSelectedPopulation : ∀ ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren 0 ω)).InjectivelyDominatesBy φ
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren 0 ω)) ())
    (hselectedChildren_subset_offspring : ∀ n ω, selectedBranchingWalkChildren (n + 1) ω ⊆
      offspringAddresses (selectedBranchingWalkChildren n ω) (selectedBranchingWalkChildSlots n ω))
    (hselectedChildren_card_le_N : ∀ n ω, (selectedBranchingWalkChildren (n + 1) ω).card ≤ N)
    (hnSelectedChildren_eq_selectFirstNBy : ∀ n ω, nSelectedBranchingWalkChildren (n + 1) ω =
      selectFirstNBy N
        (fun q => φ ((nSelectedBranchingWalk ω).position d q.1 q.2))
        (offspringAddresses (nSelectedBranchingWalkChildren n ω) (nSelectedBranchingWalkChildSlots n ω)))
    (hchildSlots_mono_under_parentMatching : ∀ n ω p, p ∈ selectedBranchingWalkChildren n ω →
      ∀ q, q ∈ nSelectedBranchingWalkChildren n ω →
      φ ((nSelectedBranchingWalk ω).position d q.1 q.2) ≤
          φ ((selectedBranchingWalk ω).position d p.1 p.2) →
      selectedBranchingWalkChildSlots n ω p ⊆ nSelectedBranchingWalkChildSlots n ω q)
    (hmatchedParents_sharedIncrement : ∀ n ω p, p ∈ selectedBranchingWalkChildren n ω →
      ∀ q, q ∈ nSelectedBranchingWalkChildren n ω →
      φ ((nSelectedBranchingWalk ω).position d q.1 q.2) ≤
          φ ((selectedBranchingWalk ω).position d p.1 p.2) →
      ∀ i ∈ selectedBranchingWalkChildSlots n ω p,
        value' (((nSelectedBranchingWalk ω).step q.1 q.2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (horderKey_translation_mono : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ n ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω)).InjectivelyDominatesBy φ
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) () := by
  intro n
  induction n with
  | zero => exact hinitialSelectedPopulation_dominates_nSelectedPopulation
  | succ n ih =>
      intro ω
      rw [hnSelectedChildren_eq_selectFirstNBy n ω]
      exact Combinatorics.Branching.Selection.Coupling.nextGeneration_injectivelyDominatesBy
        φ d N (selectedBranchingWalk ω) (nSelectedBranchingWalk ω)
        (selectedBranchingWalkChildren n ω) (nSelectedBranchingWalkChildren n ω)
        (selectedBranchingWalkChildSlots n ω) (nSelectedBranchingWalkChildSlots n ω)
        (selectedBranchingWalkChildren (n + 1) ω)
        (hselectedChildren_subset_offspring n ω) (hselectedChildren_card_le_N n ω) (ih ω)
        (hchildSlots_mono_under_parentMatching n ω) (hmatchedParents_sharedIncrement n ω) horderKey_translation_mono

end Combinatorics.Branching.Selection.Coupling.Pathwise
