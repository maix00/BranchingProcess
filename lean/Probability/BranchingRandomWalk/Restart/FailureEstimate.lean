/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.Reserve
public import Probability.Process.HittingTime.ObservableCandidates

/-!
# First-moment error on a failed restart event

This file composes the two independent obligations in a restart argument:
candidate successes are observable in the generation domain flow, and the
continuation is read from a fresh selected subtree family.  The resulting
factorization is the direct `L¹` replacement for a Cauchy--Schwarz bound.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- A fresh reserve observable on the failure of any selected countable
candidate family gains the failure probability exactly.  Neither the initial
root type, the reserve-family index, nor the offspring-slot type is finite or
countable here; countability is needed only for the candidate declarations
whose union defines the event. -/
theorem RootIndexed.integral_reserve_abs_on_candidateFailure
    {Root κ α X ι : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {T : ℕ}
    (completion : ι → RootIndexed.StepField Root α X → WithTop ℕ)
    (success : ι → Set (RootIndexed.StepField Root α X))
    (hobservable : CandidateObservable
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X)) completion success)
    (candidates : Set ι)
    (hcandidates : candidates.Countable)
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) T] {ω | chosen ω = roots})
    (hdepth : ∀ ω i, (chosen ω i).2.length = T)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (g : (κ → TreeNode α → Step α X) → ℝ) (hg : Measurable g)
    (hint : Integrable
      (fun ω => g (RootIndexed.selectedSubtreeStepFieldVector chosen ω))
      (RootIndexed.stepFieldLaw (Root := Root) μ)) :
    let failure :=
      (successfulCandidateWithin completion success candidates T)ᶜ
    (∫ ω, |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)| *
        failure.indicator (fun _ => (1 : ℝ)) ω
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) =
      (∫ ω, |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)|
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) *
        (RootIndexed.stepFieldLaw (Root := Root) μ).real failure := by
  dsimp only
  apply RootIndexed.integral_reserve_abs_on_event μ chosen hcount hfiber
    hdepth hinj g hg _ _ hint
  exact (successfulCandidateWithin_measurable
    (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X)) completion success
      hobservable candidates hcandidates T).compl

/-- The same statement for the bounded natural-number event used in restart
estimates: one of candidates `0, ..., K` succeeds by generation `T`. -/
theorem RootIndexed.integral_reserve_abs_on_boundedCandidateFailure
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {T : ℕ}
    (completion : ℕ → RootIndexed.StepField Root α X → WithTop ℕ)
    (success : ℕ → Set (RootIndexed.StepField Root α X))
    (hobservable : CandidateObservable
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X)) completion success)
    (K : ℕ)
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) T] {ω | chosen ω = roots})
    (hdepth : ∀ ω i, (chosen ω i).2.length = T)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (g : (κ → TreeNode α → Step α X) → ℝ) (hg : Measurable g)
    (hint : Integrable
      (fun ω => g (RootIndexed.selectedSubtreeStepFieldVector chosen ω))
      (RootIndexed.stepFieldLaw (Root := Root) μ)) :
    let failure := (successfulCandidateBy completion success K T)ᶜ
    (∫ ω, |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)| *
        failure.indicator (fun _ => (1 : ℝ)) ω
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) =
      (∫ ω, |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)|
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) *
        (RootIndexed.stepFieldLaw (Root := Root) μ).real failure := by
  dsimp only
  apply RootIndexed.integral_reserve_abs_on_event μ chosen hcount hfiber
    hdepth hinj g hg _ _ hint
  exact (successfulCandidateBy_measurable
    (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X)) completion success
      hobservable K T).compl

/-- Quantitative form consumed by a speed proof.  A first-moment bound `B`
and a failure-probability bound `p` give the product bound `B * p`; no second
moment is involved. -/
theorem RootIndexed.integral_reserve_abs_on_boundedCandidateFailure_le
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {T : ℕ}
    (completion : ℕ → RootIndexed.StepField Root α X → WithTop ℕ)
    (success : ℕ → Set (RootIndexed.StepField Root α X))
    (hobservable : CandidateObservable
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X)) completion success)
    (K : ℕ)
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) T] {ω | chosen ω = roots})
    (hdepth : ∀ ω i, (chosen ω i).2.length = T)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (g : (κ → TreeNode α → Step α X) → ℝ) (hg : Measurable g)
    (hint : Integrable
      (fun ω => g (RootIndexed.selectedSubtreeStepFieldVector chosen ω))
      (RootIndexed.stepFieldLaw (Root := Root) μ))
    (B p : ℝ) (hB : 0 ≤ B)
    (hmoment : (∫ ω,
        |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)|
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤ B)
    (hprob : (RootIndexed.stepFieldLaw (Root := Root) μ).real
      (successfulCandidateBy completion success K T)ᶜ ≤ p) :
    (∫ ω, |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)| *
        (successfulCandidateBy completion success K T)ᶜ.indicator
          (fun _ => (1 : ℝ)) ω
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤ B * p := by
  rw [RootIndexed.integral_reserve_abs_on_boundedCandidateFailure μ
    completion success hobservable K chosen hcount hfiber hdepth hinj
    g hg hint]
  exact mul_le_mul hmoment hprob (by positivity) hB

/-- Failure of trials confined to one initial-root set is independent of an
entire fixed forest carried by disjoint reserve roots.  The trial and reserve
trees are pre-sampled together in the same root-indexed field. -/
theorem RootIndexed.integral_reserveRoot_abs_on_candidateFailure
    {Root κ α X ι : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (trials : Set Root) (reserve : κ → Root)
    (hdisjoint : Disjoint trials (Set.range reserve)) {T : ℕ}
    (completion : ι → RootIndexed.StepField Root α X → WithTop ℕ)
    (success : ι → Set (RootIndexed.StepField Root α X))
    (hobservable : CandidateObservable
      (RootIndexed.rootFiltration (α := α) (X := X) trials)
      completion success)
    (candidates : Set ι)
    (hcandidates : candidates.Countable)
    (g : (κ → TreeNode α → Step α X) → ℝ) (hg : Measurable g)
    (hint : Integrable (fun ω => g (fun i => ω (reserve i)))
      (RootIndexed.stepFieldLaw (Root := Root) μ)) :
    let failure :=
      (successfulCandidateWithin completion success candidates T)ᶜ
    (∫ ω, |g (fun i => ω (reserve i))| *
        failure.indicator (fun _ => (1 : ℝ)) ω
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) =
      (∫ ω, |g (fun i => ω (reserve i))|
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) *
        (RootIndexed.stepFieldLaw (Root := Root) μ).real failure := by
  dsimp only
  apply RootIndexed.integral_reserveRoot_abs_on_event μ trials reserve
    hdisjoint T g hg _ _ hint
  exact (successfulCandidateWithin_measurable
    (RootIndexed.rootFiltration (α := α) (X := X) trials)
    completion success hobservable candidates hcandidates T).compl

/-- Quantitative first-moment restart error for a disjoint pre-sampled
reserve forest. -/
theorem RootIndexed.integral_reserveRoot_abs_on_candidateFailure_le
    {Root κ α X ι : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (trials : Set Root) (reserve : κ → Root)
    (hdisjoint : Disjoint trials (Set.range reserve)) {T : ℕ}
    (completion : ι → RootIndexed.StepField Root α X → WithTop ℕ)
    (success : ι → Set (RootIndexed.StepField Root α X))
    (hobservable : CandidateObservable
      (RootIndexed.rootFiltration (α := α) (X := X) trials)
      completion success)
    (candidates : Set ι)
    (hcandidates : candidates.Countable)
    (g : (κ → TreeNode α → Step α X) → ℝ) (hg : Measurable g)
    (hint : Integrable (fun ω => g (fun i => ω (reserve i)))
      (RootIndexed.stepFieldLaw (Root := Root) μ))
    (B p : ℝ) (hB : 0 ≤ B)
    (hmoment : (∫ ω, |g (fun i => ω (reserve i))|
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤ B)
    (hprob : (RootIndexed.stepFieldLaw (Root := Root) μ).real
      (successfulCandidateWithin completion success candidates T)ᶜ ≤ p) :
    (∫ ω, |g (fun i => ω (reserve i))| *
        (successfulCandidateWithin completion success candidates T)ᶜ.indicator
          (fun _ => (1 : ℝ)) ω
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤ B * p := by
  rw [RootIndexed.integral_reserveRoot_abs_on_candidateFailure μ trials
    reserve hdisjoint completion success hobservable candidates hcandidates
    g hg hint]
  exact mul_le_mul hmoment hprob (by positivity) hB

end ProbabilityTheory.BranchingRandomWalk

end
