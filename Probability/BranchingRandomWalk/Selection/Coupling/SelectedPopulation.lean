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

For \(W_\omega=\texttt{sourceWalk}\,\omega\),
\(S_{n,\omega}=\texttt{sourcePopulation}\,n\,\omega\), and
\(T_{n,\omega}=\texttt{RootIndexed.selectedPopulation}\,N\,\texttt{roots}\,
\texttt{initial}\,d\,\varphi\,\texttt{hadmits}\,n\,\omega\), write
\[
  C_n^{\mathrm{src}}(\omega)
    :=\operatorname{populationCloud}\,d\,W_\omega\,S_{n,\omega},
  \qquad
  C_n^N(\omega)
    :=\operatorname{populationCloud}\,d\,
      \bigl(\operatorname{RootIndexed.BranchingWalk.ofStepField}
        \,\texttt{initial}\,\omega\bigr)\,T_{n,\omega}.
\]
`generationInjection_selectedPopulation` constructs a witnessing slice map
\[
  J_{n,\omega}\in
    \operatorname{SliceDominatingMap}_{\varphi}
      \bigl(C_n^{\mathrm{src}}(\omega),C_n^N(\omega),()\bigr).
\]
If the source generations are offspring subsets of size at most \(N\), and
matched parents have the same selected slots and mapped increments, then
`injectivelyDominatesBy_selectedPopulation` propagates initial domination to
every generation:
\[
  \left(\forall\omega,\ C_0^{\mathrm{src}}(\omega)
      \preceq_{\varphi} C_0^N(\omega)\right)
  \Longrightarrow
  \left(\forall n,\omega,\ C_n^{\mathrm{src}}(\omega)
      \preceq_{\varphi} C_n^N(\omega)\right),
\]
where \(C\preceq_{\varphi}D\) abbreviates
`Cloud.InjectivelyDominatesBy φ C D ()`.

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Selection.Coupling.generationInjection_selectedPopulation`:
  for each generation and field sample, constructs an injective slice map
  from a capacity-bounded source cloud into the causal first-$N$ cloud on a
  pre-sampled root-indexed field.
- `ProbabilityTheory.BranchingRandomWalk.Selection.Coupling.injectivelyDominatesBy_selectedPopulation`:
  if the source cloud is initially dominated, its next generations satisfy
  the offspring-subset and cardinality bounds, and matched parents share
  selected slots and mapped increments, then the source cloud is
  injectively dominated by the first-$N$ cloud at every generation.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Coupling

open Combinatorics.Branching.Selection.Coupling.Pathwise

open Combinatorics.UlamHarris
open Combinatorics.Branching
open Combinatorics.Branching.Selection.Coupling
open _root_.Combinatorics.Selection.NSelection

variable {Root α Mark Position Value : Type*}

/-- Concrete canonical coupling state between an arbitrary capacity-bounded
source process and the causal first-`N` population.  Its particle map is the
equal-dynamic-rank map retained by `generationInjection_of_isFirstNBy`. -/
noncomputable def generationInjection_selectedPopulation
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (roots : Finset Root) (initial : Root → Position)
    (sourceWalk : RootIndexed.StepField Root α Mark →
      RootIndexed.BranchingWalk Root α Mark Position)
    (sourcePopulation : ℕ → RootIndexed.StepField Root α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (sourceSlots : ℕ → RootIndexed.StepField Root α Mark →
      RootIndexed.TreeNode Root α → Set α)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (n + 1) ω)
        (Combinatorics.Branching.Population.childrenAtGeneration n parents ω))
    (initialInjection : ∀ ω, Cloud.SliceDominatingMap φ
      (populationCloud d (sourceWalk ω) (sourcePopulation 0 ω))
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial ω)
        (RootIndexed.selectedPopulation N roots initial d φ hadmits 0 ω)) ())
    (hsourceSubset : ∀ n ω, ↑(sourcePopulation (n + 1) ω) ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑(sourcePopulation n ω)) (sourceSlots n ω))
    (hsourceCard : ∀ n ω, (sourcePopulation (n + 1) ω).card ≤ N)
    (hslots : ∀ n ω (parents : Cloud.SliceDominatingMap φ
        (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N roots initial d φ hadmits n ω)) ()),
      ∀ p ∈ sourcePopulation n ω,
        sourceSlots n ω p ⊆ {i | survive (ω (parents p).1 (parents p).2) i})
    (hsharedIncrement : ∀ n ω (parents : Cloud.SliceDominatingMap φ
        (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N roots initial d φ hadmits n ω)) ()),
      ∀ p ∈ sourcePopulation n ω, ∀ i ∈ sourceSlots n ω p,
        value' ((ω (parents p).1 (parents p).2).map d) i =
          value' (((sourceWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark) :
    Cloud.SliceDominatingMap φ
      (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial ω)
        (RootIndexed.selectedPopulation N roots initial d φ hadmits n ω)) () :=
  generationInjection_of_isFirstNBy φ d N sourceWalk
    (fun ω => RootIndexed.BranchingWalk.ofStepField initial ω)
    sourcePopulation
    (RootIndexed.selectedPopulation N roots initial d φ hadmits)
    sourceSlots (fun _ ω p => {i | survive (ω p.1 p.2) i})
    initialInjection hsourceSubset hsourceCard
    (fun k sample => RootIndexed.selectedPopulation_succ_spec_position
      N roots initial d φ hadmits k sample)
    hslots hsharedIncrement htranslate n ω

/-- An arbitrary capacity-bounded source process is dominated at every
generation by the causal first-`N` population formed from all surviving
offspring of a root-indexed pre-sampled field. -/
theorem injectivelyDominatesBy_selectedPopulation
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (roots : Finset Root) (initial : Root → Position)
    (sourceWalk : RootIndexed.StepField Root α Mark →
      RootIndexed.BranchingWalk Root α Mark Position)
    (sourcePopulation : ℕ → RootIndexed.StepField Root α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (sourceSlots : ℕ → RootIndexed.StepField Root α Mark →
      RootIndexed.TreeNode Root α → Set α)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (n + 1) ω)
        (Combinatorics.Branching.Population.childrenAtGeneration n parents ω))
    (hinitial : ∀ ω,
      (populationCloud d (sourceWalk ω) (sourcePopulation 0 ω)).InjectivelyDominatesBy φ
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N roots initial d φ hadmits 0 ω))
        ())
    (hsourceSubset : ∀ n ω, ↑(sourcePopulation (n + 1) ω) ⊆
      Combinatorics.Branching.Population.offspringAddressSet (↑(sourcePopulation n ω)) (sourceSlots n ω))
    (hsourceCard : ∀ n ω, (sourcePopulation (n + 1) ω).card ≤ N)
    (hslots : ∀ n ω (parents : Cloud.SliceDominatingMap φ
        (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N roots initial d φ hadmits n ω)) ()),
      ∀ p ∈ sourcePopulation n ω,
        sourceSlots n ω p ⊆ {i | survive (ω (parents p).1 (parents p).2) i})
    (hsharedIncrement : ∀ n ω (parents : Cloud.SliceDominatingMap φ
        (populationCloud d (sourceWalk ω) (sourcePopulation n ω))
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N roots initial d φ hadmits n ω)) ()),
      ∀ p ∈ sourcePopulation n ω, ∀ i ∈ sourceSlots n ω p,
        value' ((ω (parents p).1 (parents p).2).map d) i =
          value' (((sourceWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ n ω,
      (populationCloud d (sourceWalk ω) (sourcePopulation n ω)).InjectivelyDominatesBy φ
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N roots initial d φ hadmits n ω))
        () := by
  apply injectivelyDominatesBy_all_generations_of_isFirstNBy
    φ d N sourceWalk
    (fun ω => RootIndexed.BranchingWalk.ofStepField initial ω)
    sourcePopulation
    (RootIndexed.selectedPopulation N roots initial d φ hadmits)
    sourceSlots
    (fun _ ω p => {i | survive (ω p.1 p.2) i})
    hinitial hsourceSubset hsourceCard
  · exact fun n ω => RootIndexed.selectedPopulation_succ_spec_position
      N roots initial d φ hadmits n ω
  · exact hslots
  · exact hsharedIncrement
  · exact htranslate

end ProbabilityTheory.BranchingRandomWalk.Selection.Coupling

end
