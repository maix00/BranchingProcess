/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Population.Offspring

public import Combinatorics.BranchingWalk.Selection.NSelection.Coupling.Pathwise
public import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed

/-!
# Coupling to a causal root-indexed selected population

This instantiates the abstract all-generation offspring coupling with the
selected population constructed directly from a pre-sampled step field.
Offspring sets may be infinite.

For \(W^{\mathrm{sel}}_\omega=\texttt{selectedBranchingWalk}\,\omega\),
\(P^{\mathrm{sel}}_{n,\omega}=\texttt{selectedBranchingWalkChildren}\,n\,\omega\), and
\(P^N_{n,\omega}=\texttt{RootIndexed.selectedPopulation}\,N\,
\texttt{nSelectedBranchingWalkRoots}\,\texttt{initial}\,d\,\varphi\,
\texttt{nSelectedBranchingWalkAdmitsFirstNBy}\,n\,\omega\), write
\[
  C_n^{\mathrm{sel}}(\omega)
    :=\operatorname{populationCloud}\,d\,W^{\mathrm{sel}}_\omega\,
      P^{\mathrm{sel}}_{n,\omega},
  \qquad
  C_n^N(\omega)
    :=\operatorname{populationCloud}\,d\,
      \bigl(\operatorname{RootIndexed.BranchingWalk.ofStepField}
        \,\texttt{initial}\,\omega\bigr)\,P^N_{n,\omega}.
\]
`generationInjection_selectedPopulation` constructs a witnessing slice map
\[
  J_{n,\omega}\in
    \operatorname{SliceDominatingMap}_{\varphi}
      \bigl(C_n^{\mathrm{sel}}(\omega),C_n^N(\omega),()\bigr).
\]
If `selectedBranchingWalkChildren` are offspring subsets of size at most
\(N\), and `nSelectedBranchingWalkParentMatching` preserves selected slots
and mapped increments, then
`injectivelyDominatesBy_selectedPopulation` propagates initial domination to
every generation:
\[
  \left(\forall\omega,\ C_0^{\mathrm{sel}}(\omega)
      \preceq_{\varphi} C_0^N(\omega)\right)
  \Longrightarrow
  \left(\forall n,\omega,\ C_n^{\mathrm{sel}}(\omega)
      \preceq_{\varphi} C_n^N(\omega)\right),
\]
where \(C\preceq_{\varphi}D\) abbreviates
`Cloud.InjectivelyDominatesBy φ C D ()`.

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Selection.Coupling.generationInjection_selectedPopulation`:
  for each generation and field sample, constructs an injective slice map
  from the `selectedBranchingWalkChildren` cloud into the
  `nSelectedBranchingWalkChildren` cloud on a pre-sampled root-indexed field.
- `ProbabilityTheory.BranchingRandomWalk.Selection.Coupling.injectivelyDominatesBy_selectedPopulation`:
  if the initial `selectedBranchingWalkChildren` cloud is dominated, each
  successor satisfies the offspring-subset and cardinality bounds, and
  `nSelectedBranchingWalkParentMatching` preserves child slots and increments,
  then it is dominated by `nSelectedBranchingWalkChildren` at every generation.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Coupling

open Combinatorics.Branching.Selection.Coupling.Pathwise

open Combinatorics.UlamHarris
open Combinatorics.Branching
open Combinatorics.Branching.Selection.Coupling
open _root_.Combinatorics.Selection.NSelection

variable {Root α Mark Position OrderKey : Type*}

/-- For each generation, construct the canonical equal-dynamic-rank injection
from `selectedBranchingWalkChildren` into the causal `N`-selected population. -/
noncomputable def generationInjection_selectedPopulation
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    [AddCommMonoid Position]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (nSelectedBranchingWalkRoots : Finset Root) (initial : Root → Position)
    (selectedBranchingWalk : RootIndexed.StepField Root α Mark →
      RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkChildren : ℕ → RootIndexed.StepField Root α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots : ℕ → RootIndexed.StepField Root α Mark →
      RootIndexed.TreeNode Root α → Set α)
    (nSelectedBranchingWalkAdmitsFirstNBy : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (nSelectedBranchingWalkParents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (n + 1) ω)
        (Combinatorics.Branching.Population.childrenAtGeneration n nSelectedBranchingWalkParents ω))
    (initialInjection : ∀ ω, Cloud.SliceDominatingMap φ
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren 0 ω))
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial ω)
        (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy 0 ω)) ())
    (hselectedBranchingWalkChildrenSubset : ∀ n ω, ↑(selectedBranchingWalkChildren (n + 1) ω) ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑(selectedBranchingWalkChildren n ω)) (selectedBranchingWalkChildSlots n ω))
    (hselectedBranchingWalkChildrenCard : ∀ n ω, (selectedBranchingWalkChildren (n + 1) ω).card ≤ N)
    (hslots : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω,
        selectedBranchingWalkChildSlots n ω p ⊆ {i | survive (ω (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2) i})
    (hsharedIncrement : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω, ∀ i ∈ selectedBranchingWalkChildSlots n ω p,
        value' ((ω (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark) :
    Cloud.SliceDominatingMap φ
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial ω)
        (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy n ω)) () :=
  generationInjection_of_isFirstNBy φ d N selectedBranchingWalk
    (fun ω => RootIndexed.BranchingWalk.ofStepField initial ω)
    selectedBranchingWalkChildren
    (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy)
    selectedBranchingWalkChildSlots (fun _ ω p => {i | survive (ω p.1 p.2) i})
    initialInjection hselectedBranchingWalkChildrenSubset hselectedBranchingWalkChildrenCard
    (fun k sample => RootIndexed.selectedPopulation_succ_spec_position
      N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy k sample)
    hslots hsharedIncrement htranslate n ω

/-- At every generation, `selectedBranchingWalkChildren` is dominated by the
causal `N`-selected population formed from all surviving offspring of the
root-indexed pre-sampled field. -/
theorem injectivelyDominatesBy_selectedPopulation
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    [AddCommMonoid Position]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (nSelectedBranchingWalkRoots : Finset Root) (initial : Root → Position)
    (selectedBranchingWalk : RootIndexed.StepField Root α Mark →
      RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkChildren : ℕ → RootIndexed.StepField Root α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (selectedBranchingWalkChildSlots : ℕ → RootIndexed.StepField Root α Mark →
      RootIndexed.TreeNode Root α → Set α)
    (nSelectedBranchingWalkAdmitsFirstNBy : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (nSelectedBranchingWalkParents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (n + 1) ω)
        (Combinatorics.Branching.Population.childrenAtGeneration n nSelectedBranchingWalkParents ω))
    (hinitial : ∀ ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren 0 ω)).InjectivelyDominatesBy φ
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy 0 ω))
        ())
    (hselectedBranchingWalkChildrenSubset : ∀ n ω, ↑(selectedBranchingWalkChildren (n + 1) ω) ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑(selectedBranchingWalkChildren n ω)) (selectedBranchingWalkChildSlots n ω))
    (hselectedBranchingWalkChildrenCard : ∀ n ω, (selectedBranchingWalkChildren (n + 1) ω).card ≤ N)
    (hslots : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω,
        selectedBranchingWalkChildSlots n ω p ⊆ {i | survive (ω (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2) i})
    (hsharedIncrement : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω))
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy n ω)) ()),
      ∀ p ∈ selectedBranchingWalkChildren n ω, ∀ i ∈ selectedBranchingWalkChildSlots n ω p,
        value' ((ω (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2).map d) i =
          value' (((selectedBranchingWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ n ω,
      (populationCloud d (selectedBranchingWalk ω) (selectedBranchingWalkChildren n ω)).InjectivelyDominatesBy φ
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy n ω))
        () := by
  apply injectivelyDominatesBy_all_generations_of_isFirstNBy
    φ d N selectedBranchingWalk
    (fun ω => RootIndexed.BranchingWalk.ofStepField initial ω)
    selectedBranchingWalkChildren
    (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy)
    selectedBranchingWalkChildSlots
    (fun _ ω p => {i | survive (ω p.1 p.2) i})
    hinitial hselectedBranchingWalkChildrenSubset hselectedBranchingWalkChildrenCard
  · exact fun n ω => RootIndexed.selectedPopulation_succ_spec_position
      N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy n ω
  · exact hslots
  · exact hsharedIncrement
  · exact htranslate

end ProbabilityTheory.BranchingRandomWalk.Selection.Coupling

end
