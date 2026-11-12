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
    (hretained : ∀ ω, ↑(selectedBranchingWalkChildren ω) ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑(selectedBranchingWalkParents ω)) (selectedBranchingWalkChildSlots ω))
    (hcard : ∀ ω, (selectedBranchingWalkChildren ω).card ≤ N)
    (hselected : ∀ ω, IsFirstNBy N
      (fun q => φ ((nSelectedBranchingWalk ω).position d q.1 q.2))
      (Combinatorics.Branching.Population.offspringAddressSet (↑(nSelectedBranchingWalkParents ω)) (nSelectedBranchingWalkChildSlots ω))
      (nSelectedBranchingWalkChildren ω))
    (nSelectedBranchingWalkParentMatching : ∀ ω, Cloud.SliceDominatingMap φ
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkParents ω))
      (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkParents ω)) ())
    (hslots : ∀ ω p, p ∈ selectedBranchingWalkParents ω →
      selectedBranchingWalkChildSlots ω p ⊆ nSelectedBranchingWalkChildSlots ω (nSelectedBranchingWalkParentMatching ω p))
    (hsharedIncrement : ∀ ω p, p ∈ selectedBranchingWalkParents ω →
      ∀ i ∈ selectedBranchingWalkChildSlots ω p,
        value' (((nSelectedBranchingWalk ω).step (nSelectedBranchingWalkParentMatching ω p).1 (nSelectedBranchingWalkParentMatching ω p).2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
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
      (hretained ω) (hcard ω) (hselected ω) (nSelectedBranchingWalkParentMatching ω)
      (hslots ω) (hsharedIncrement ω) htranslate

/-- Iterate the arbitrary-offspring coupling through all generations.  The
target population at each successor generation may be any measurable or
nonmeasurable realization satisfying `IsFirstNBy`; measurability is a separate
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
    (hinitial : ∀ ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren 0 ω)).InjectivelyDominatesBy φ
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren 0 ω)) ())
    (hselectedBranchingWalkChildrenSubset : ∀ n ω, ↑(selectedBranchingWalkChildren (n + 1) ω) ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑(selectedBranchingWalkChildren n ω)) (selectedBranchingWalkChildSlots n ω))
    (hselectedBranchingWalkChildrenCard : ∀ n ω, (selectedBranchingWalkChildren (n + 1) ω).card ≤ N)
    (hnSelectedBranchingWalkChildren : ∀ n ω, IsFirstNBy N
      (fun q => φ ((nSelectedBranchingWalk ω).position d q.1 q.2))
      (Combinatorics.Branching.Population.offspringAddressSet (↑(nSelectedBranchingWalkChildren n ω)) (nSelectedBranchingWalkChildSlots n ω))
      (nSelectedBranchingWalkChildren (n + 1) ω))
    (hslots : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω,
        selectedBranchingWalkChildSlots n ω p ⊆ nSelectedBranchingWalkChildSlots n ω (nSelectedBranchingWalkParentMatching p))
    (hsharedIncrement : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω, ∀ i ∈ selectedBranchingWalkChildSlots n ω p,
        value' (((nSelectedBranchingWalk ω).step (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ n ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω)).InjectivelyDominatesBy φ
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) () := by
  intro n
  induction n with
  | zero => exact hinitial
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
        (hselectedBranchingWalkChildrenSubset n) (hselectedBranchingWalkChildrenCard n) (hnSelectedBranchingWalkChildren n) nSelectedBranchingWalkParentMatching
      · intro ω p hp i hi
        exact hslots n ω (nSelectedBranchingWalkParentMatching ω) p hp hi
      · intro ω p hp i hi
        exact hsharedIncrement n ω (nSelectedBranchingWalkParentMatching ω) p hp i hi
      · exact htranslate

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
    (initial : ∀ ω, Cloud.SliceDominatingMap φ
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren 0 ω))
      (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren 0 ω)) ())
    (hselectedBranchingWalkChildrenSubset : ∀ n ω, ↑(selectedBranchingWalkChildren (n + 1) ω) ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑(selectedBranchingWalkChildren n ω)) (selectedBranchingWalkChildSlots n ω))
    (hselectedBranchingWalkChildrenCard : ∀ n ω, (selectedBranchingWalkChildren (n + 1) ω).card ≤ N)
    (hnSelectedBranchingWalkChildren : ∀ n ω, IsFirstNBy N
      (fun q => φ ((nSelectedBranchingWalk ω).position d q.1 q.2))
      (Combinatorics.Branching.Population.offspringAddressSet (↑(nSelectedBranchingWalkChildren n ω)) (nSelectedBranchingWalkChildSlots n ω))
      (nSelectedBranchingWalkChildren (n + 1) ω))
    (hslots : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω,
        selectedBranchingWalkChildSlots n ω p ⊆ nSelectedBranchingWalkChildSlots n ω (nSelectedBranchingWalkParentMatching p))
    (hsharedIncrement : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω, ∀ i ∈ selectedBranchingWalkChildSlots n ω p,
        value' (((nSelectedBranchingWalk ω).step (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : Ω) :
    Cloud.SliceDominatingMap φ
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
      (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) () :=
  Nat.rec (motive := fun n => Cloud.SliceDominatingMap φ
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
      (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ())
    (initial ω)
    (fun k nSelectedBranchingWalkParentMatching =>
      Combinatorics.Branching.Selection.Coupling.nextGenerationInjection_of_isFirstNBy
        φ d N (selectedBranchingWalk ω) (nSelectedBranchingWalk ω)
        (selectedBranchingWalkChildren k ω) (nSelectedBranchingWalkChildren k ω)
        (selectedBranchingWalkChildSlots k ω) (nSelectedBranchingWalkChildSlots k ω)
        (selectedBranchingWalkChildren (k + 1) ω) (nSelectedBranchingWalkChildren (k + 1) ω)
        (hselectedBranchingWalkChildrenSubset k ω) (hselectedBranchingWalkChildrenCard k ω) (hnSelectedBranchingWalkChildren k ω) nSelectedBranchingWalkParentMatching
        (hslots k ω nSelectedBranchingWalkParentMatching) (hsharedIncrement k ω nSelectedBranchingWalkParentMatching) htranslate)
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
    (initial : ∀ ω, Cloud.SliceDominatingMap φ
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren 0 ω))
      (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren 0 ω)) ())
    (hselectedBranchingWalkChildrenSubset : ∀ n ω, ↑(selectedBranchingWalkChildren (n + 1) ω) ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑(selectedBranchingWalkChildren n ω)) (selectedBranchingWalkChildSlots n ω))
    (hselectedBranchingWalkChildrenCard : ∀ n ω, (selectedBranchingWalkChildren (n + 1) ω).card ≤ N)
    (hnSelectedBranchingWalkChildren : ∀ n ω, IsFirstNBy N
      (fun q => φ ((nSelectedBranchingWalk ω).position d q.1 q.2))
      (Combinatorics.Branching.Population.offspringAddressSet (↑(nSelectedBranchingWalkChildren n ω)) (nSelectedBranchingWalkChildSlots n ω))
      (nSelectedBranchingWalkChildren (n + 1) ω))
    (hslots : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω,
        selectedBranchingWalkChildSlots n ω p ⊆ nSelectedBranchingWalkChildSlots n ω (nSelectedBranchingWalkParentMatching p))
    (hsharedIncrement : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω, ∀ i ∈ selectedBranchingWalkChildSlots n ω p,
        value' (((nSelectedBranchingWalk ω).step (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : Ω) :
    (populationCloud d
      (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω)).InjectivelyDominatesBy φ
      (populationCloud d
        (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) () :=
  (generationInjection_of_isFirstNBy φ d N selectedBranchingWalk nSelectedBranchingWalk
    selectedBranchingWalkChildren nSelectedBranchingWalkChildren selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots initial
    hselectedBranchingWalkChildrenSubset hselectedBranchingWalkChildrenCard hnSelectedBranchingWalkChildren hslots hsharedIncrement htranslate
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
    (hretained : ∀ ω, selectedBranchingWalkChildren ω ⊆
      offspringAddresses (selectedBranchingWalkParents ω) (selectedBranchingWalkChildSlots ω))
    (hcard : ∀ ω, (selectedBranchingWalkChildren ω).card ≤ N)
    (hparents : ∀ ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkParents ω)).InjectivelyDominatesBy φ
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkParents ω)) ())
    (hslots : ∀ ω p, p ∈ selectedBranchingWalkParents ω → ∀ q, q ∈ nSelectedBranchingWalkParents ω →
      φ ((nSelectedBranchingWalk ω).position d q.1 q.2) ≤
          φ ((selectedBranchingWalk ω).position d p.1 p.2) →
      selectedBranchingWalkChildSlots ω p ⊆ nSelectedBranchingWalkChildSlots ω q)
    (hsharedIncrement : ∀ ω p, p ∈ selectedBranchingWalkParents ω →
      ∀ q, q ∈ nSelectedBranchingWalkParents ω →
      φ ((nSelectedBranchingWalk ω).position d q.1 q.2) ≤
          φ ((selectedBranchingWalk ω).position d p.1 p.2) →
      ∀ i ∈ selectedBranchingWalkChildSlots ω p,
        value' (((nSelectedBranchingWalk ω).step q.1 q.2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
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
    (selectedBranchingWalkChildren ω) (hretained ω) (hcard ω) (hparents ω)
    (hslots ω) (hsharedIncrement ω) htranslate

/-- Iteration of the pathwise multi-root coupling through every generation.

The target population at generation `n + 1` is the dynamic leftmost `N`
selection from its actual children, ordered by the observed value `φ` at that
sample.  The source may use any (possibly random and causal) retained subset
of its children, provided its cardinality is at most `N`. -/
theorem injectivelyDominatesBy_all_generations
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (selectedBranchingWalk nSelectedBranchingWalk : Ω → RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkChildren nSelectedBranchingWalkChildren :
      ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots nSelectedBranchingWalkChildSlots :
      ℕ → Ω → RootIndexed.TreeNode Root α → Finset α)
    (hinitial : ∀ ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren 0 ω)).InjectivelyDominatesBy φ
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren 0 ω)) ())
    (hselectedBranchingWalkChildrenSubset : ∀ n ω, selectedBranchingWalkChildren (n + 1) ω ⊆
      offspringAddresses (selectedBranchingWalkChildren n ω) (selectedBranchingWalkChildSlots n ω))
    (hselectedBranchingWalkChildrenCard : ∀ n ω, (selectedBranchingWalkChildren (n + 1) ω).card ≤ N)
    (hnSelectedBranchingWalkChildren : ∀ n ω, nSelectedBranchingWalkChildren (n + 1) ω =
      selectFirstNBy N
        (fun q => φ ((nSelectedBranchingWalk ω).position d q.1 q.2))
        (offspringAddresses (nSelectedBranchingWalkChildren n ω) (nSelectedBranchingWalkChildSlots n ω)))
    (hslots : ∀ n ω p, p ∈ selectedBranchingWalkChildren n ω →
      ∀ q, q ∈ nSelectedBranchingWalkChildren n ω →
      φ ((nSelectedBranchingWalk ω).position d q.1 q.2) ≤
          φ ((selectedBranchingWalk ω).position d p.1 p.2) →
      selectedBranchingWalkChildSlots n ω p ⊆ nSelectedBranchingWalkChildSlots n ω q)
    (hsharedIncrement : ∀ n ω p, p ∈ selectedBranchingWalkChildren n ω →
      ∀ q, q ∈ nSelectedBranchingWalkChildren n ω →
      φ ((nSelectedBranchingWalk ω).position d q.1 q.2) ≤
          φ ((selectedBranchingWalk ω).position d p.1 p.2) →
      ∀ i ∈ selectedBranchingWalkChildSlots n ω p,
        value' (((nSelectedBranchingWalk ω).step q.1 q.2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ n ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω)).InjectivelyDominatesBy φ
        (populationCloud d (nSelectedBranchingWalk ω) (nSelectedBranchingWalkChildren n ω)) () := by
  intro n
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      intro ω
      rw [hnSelectedBranchingWalkChildren n ω]
      exact Combinatorics.Branching.Selection.Coupling.nextGeneration_injectivelyDominatesBy
        φ d N (selectedBranchingWalk ω) (nSelectedBranchingWalk ω)
        (selectedBranchingWalkChildren n ω) (nSelectedBranchingWalkChildren n ω)
        (selectedBranchingWalkChildSlots n ω) (nSelectedBranchingWalkChildSlots n ω)
        (selectedBranchingWalkChildren (n + 1) ω)
        (hselectedBranchingWalkChildrenSubset n ω) (hselectedBranchingWalkChildrenCard n ω) (ih ω)
        (hslots n ω) (hsharedIncrement n ω) htranslate

end Combinatorics.Branching.Selection.Coupling.Pathwise
