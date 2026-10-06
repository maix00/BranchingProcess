/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Lineage.MultiRoot
public import Probability.BranchingRandomWalk.Restart.FailureEstimate

/-!
# First-moment restart bounds for pre-sampled reserve lineages

This module instantiates the root-indexed restart factorization with the
observable completion times of a pre-sampled multi-root reserve family.
Candidate outcomes are tested at their `sigma` completion generations, so the
failure event is measurable in the domain filtration while the selected
frontier subtrees remain independent of that filtration.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

/-- The continuation's absolute first moment factors exactly over failure of
all successful candidates, when candidate tests are evaluated at the
observable `sigma` completions of a pre-sampled root/trial lineage family. -/
theorem RootIndexed.ReserveLineages.integral_selectedSubtree_abs_on_candidateFailure
    {Root Trial κ α X : Type*} [Countable α] [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (test : Root → Trial → ℕ → Set (RootIndexed.StepField Root α X))
    (htest : ∀ r i n, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] (test r i n))
    (candidates : Set (Root × Trial)) (hcandidates : candidates.Countable)
    (T : ℕ)
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hchosenRangeCountable : (Set.range chosen).Countable)
    (hchosenFiberMeasurable : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) T] {ω | chosen ω = roots})
    (hchosenDepth : ∀ ω i, (chosen ω i).2.length = T)
    (hchosenInjective : ∀ ω, Function.Injective (chosen ω))
    (g : (κ → TreeNode α → Step α X) → ℝ) (hg : Measurable g)
    (hint : Integrable
      (fun ω => g (RootIndexed.selectedSubtreeStepFieldVector chosen ω))
      (RootIndexed.stepFieldLaw (Root := Root) μ)) :
    let completion : Root × Trial → RootIndexed.StepField Root α X → WithTop ℕ :=
      fun p => lineages.sigma splitMark p.1 p.2
    let success : Root × Trial → Set (RootIndexed.StepField Root α X) :=
      fun p => successAtCompletion (completion p) (fun n => test p.1 p.2 n)
    let failure := (successfulCandidateWithin completion success candidates T)ᶜ
    (∫ ω, |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)| *
        failure.indicator (fun _ => (1 : ℝ)) ω
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) =
      (∫ ω, |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)|
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) *
        (RootIndexed.stepFieldLaw (Root := Root) μ).real failure := by
  dsimp only
  exact @RootIndexed.integral_reserve_abs_on_candidateFailure
    Root κ α X (Root × Trial) _ μ inferInstance T
    (fun (p : Root × Trial) => lineages.sigma splitMark p.1 p.2)
    (fun (p : Root × Trial) => successAtCompletion
      (lineages.sigma splitMark p.1 p.2)
      (fun n => test p.1 p.2 n))
    (successAtCompletion_observable
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (fun (p : Root × Trial) => lineages.sigma splitMark p.1 p.2)
      (fun (p : Root × Trial) n => test p.1 p.2 n)
      (lineages.all_sigma_isStoppingTime splitMark hsplit)
      (fun (p : Root × Trial) n => htest p.1 p.2 n))
    candidates hcandidates chosen hchosenRangeCountable
    hchosenFiberMeasurable hchosenDepth hchosenInjective g hg hint

/-- A bound on the continuation's first moment and a bound on the probability
of candidate failure give the usual product estimate, with no second-moment
assumption. -/
theorem RootIndexed.ReserveLineages.integral_selectedSubtree_abs_on_candidateFailure_le
    {Root Trial κ α X : Type*} [Countable α] [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (test : Root → Trial → ℕ → Set (RootIndexed.StepField Root α X))
    (htest : ∀ r i n, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] (test r i n))
    (candidates : Set (Root × Trial)) (hcandidates : candidates.Countable)
    (T : ℕ)
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hchosenRangeCountable : (Set.range chosen).Countable)
    (hchosenFiberMeasurable : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) T] {ω | chosen ω = roots})
    (hchosenDepth : ∀ ω i, (chosen ω i).2.length = T)
    (hchosenInjective : ∀ ω, Function.Injective (chosen ω))
    (g : (κ → TreeNode α → Step α X) → ℝ) (hg : Measurable g)
    (hint : Integrable
      (fun ω => g (RootIndexed.selectedSubtreeStepFieldVector chosen ω))
      (RootIndexed.stepFieldLaw (Root := Root) μ))
    (B p : ℝ) (hB : 0 ≤ B)
    (hmoment : (∫ ω,
        |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)|
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤ B)
    (hprob : (RootIndexed.stepFieldLaw (Root := Root) μ).real
      (successfulCandidateWithin
        (fun p => lineages.sigma splitMark p.1 p.2)
        (fun p => successAtCompletion (lineages.sigma splitMark p.1 p.2)
          (fun n => test p.1 p.2 n)) candidates T)ᶜ ≤ p) :
    (∫ ω, |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)| *
        (successfulCandidateWithin
          (fun p => lineages.sigma splitMark p.1 p.2)
          (fun p => successAtCompletion (lineages.sigma splitMark p.1 p.2)
            (fun n => test p.1 p.2 n)) candidates T)ᶜ.indicator
          (fun _ => (1 : ℝ)) ω
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤ B * p := by
  rw [lineages.integral_selectedSubtree_abs_on_candidateFailure
    μ splitMark hsplit test htest candidates hcandidates T chosen
    hchosenRangeCountable hchosenFiberMeasurable hchosenDepth
    hchosenInjective g hg hint]
  exact mul_le_mul hmoment hprob (by positivity) hB

end ProbabilityTheory.BranchingRandomWalk

end
