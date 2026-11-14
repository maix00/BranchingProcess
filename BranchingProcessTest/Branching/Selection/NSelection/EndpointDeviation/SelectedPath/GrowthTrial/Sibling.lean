import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.GrowthTrial.Sibling
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.GrowthTrial.Recursive
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Lemmas.FirstSplit.Finite
import Probability.BranchingRandomWalk.Step.Selection.BoundedSplit

/-!
# Selected-path sibling growth-trial API checks

The finite first-split factorization applies to the growth event on the first
selected child and any measurable observable of the continuation subtree
rooted at the second selected child. The event is conditioned on the stopped
domain past at the observable split completion.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.GrowthTrial.siblingField_factorization

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.GrowthTrial.selectedPopulationFirstSplitSubtrees_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.GrowthTrial.selectedPopulationFirstSplitSubtrees_map_eq_product

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.GrowthTrial.recursiveFailure_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.GrowthTrial.measure_recursiveFailure_succ

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.GrowthTrial.measure_recursiveFailure_eq_pow

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Step.Selection.exists_positive_selectedSplit

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Step.Selection.exists_nat_cutoff_positive_boundedSelectedSplit

#print axioms
  ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Lemmas.FirstSplit.selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos

/-! The concrete first-or-below-potential selector receives the nonempty-offspring and
supercriticality assumptions separately. Its positive split mass is provided
by `GoodSplit`. This closes the `hfinite` input to the recursive product-law
theorem for the actual ordered offspring law. -/

section ConcreteFiniteSplit

open MeasureTheory ProbabilityTheory
open Combinatorics.Branching

variable {ι α X : Type*} [MeasurableSpace X] [Countable ι]
  [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]

theorem concrete_firstOrBelowPotential_split_completion_ae_finite
    (L : ProbabilityTheory.BranchingRandomWalk.StepLaw ι α X)
    [IsProbabilityMeasure L.raw]
    (hnonempty : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ :
        ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι X))
    (hsupercritical : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ :
        ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι X)) :
    ∃ M : ℕ,
      ∀ᵐ ω ∂ProbabilityTheory.BranchingProcess.offspringFieldLaw L.sorted,
        ProbabilityTheory.BranchingRandomWalk.StepSelection.SplitTime.selectedPopulationSplitCompletion
          (Combinatorics.Branching.Step.FiniteSelection.firstOrBelowPotential
            (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
            L.potential (M : ℝ)) ω ≠ ⊤ := by
  letI : IsProbabilityMeasure L.sorted := inferInstance
  obtain ⟨M, hpositive, hsplitMeas⟩ :=
    ProbabilityTheory.BranchingRandomWalk.Step.Selection.exists_nat_cutoff_positive_firstOrBelowPotentialSplit
      L hsupercritical
  let R : Step.FiniteSelection α X :=
    Combinatorics.Branching.Step.FiniteSelection.firstOrBelowPotential
      (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
      L.potential (M : ℝ)
  have hR : Measurable R.select := by
    simpa [R] using
      Combinatorics.Branching.Step.FiniteSelection.firstOrBelowPotential_measurable
        (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
        (Combinatorics.Branching.Step.FiniteSelection.firstTwoBySlotOrder_measurable
          (α := α) (X := X)) L.potential (M : ℝ)
  have hnonemptyAE : ∀ᵐ ξ ∂L.sorted, (R ξ).Nonempty := by
    simpa [R] using
      ProbabilityTheory.BranchingRandomWalk.Step.Selection.firstOrBelowPotential_nonempty_ae
        L hnonempty (M : ℝ)
  have hnonemptyMeas : Measurable (fun ξ : Step α X => (R ξ).Nonempty) := by
    exact (measurable_of_countable fun s : Finset α => s.Nonempty).comp hR
  have hnonempty : L.sorted {ξ | (R ξ).Nonempty} = 1 :=
    (ae_iff_prob_eq_one hnonemptyMeas).mp hnonemptyAE
  have hsplit : MeasurableSet {ξ : Step α X | 2 ≤ (R ξ).card} := by
    simpa [R, Combinatorics.Branching.Step.FiniteSelection.splitBy] using hsplitMeas
  have hpositive' : 0 < L.sorted {ξ : Step α X | 2 ≤ (R ξ).card} := by
    simpa [R, Combinatorics.Branching.Step.FiniteSelection.splitBy] using hpositive
  refine ⟨M, ?_⟩
  exact ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Lemmas.FirstSplit.selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos
    L.sorted R hR hnonempty hsplit hpositive'

#print axioms concrete_firstOrBelowPotential_split_completion_ae_finite

end ConcreteFiniteSplit
