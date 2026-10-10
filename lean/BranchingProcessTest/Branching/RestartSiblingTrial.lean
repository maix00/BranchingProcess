import Probability.BranchingRandomWalk.Restart.RootedTrial.SiblingTrial
import Probability.BranchingRandomWalk.Restart.RootedTrial.RecursiveReserve
import Probability.BranchingRandomWalk.Restart.RootedTrial.FiniteSplitCompletion
import Probability.BranchingRandomWalk.Restart.GoodSplit

/-!
# Restart sibling trial API checks

The finite first-split factorization applies to the actual thesis growth
event on the first selected child and any measurable reserve observable on
the second selected child.  The event is conditioned on the stopped domain
past at the observable split completion.
-/

#print axioms
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.ReserveLineages.sigma_firstGrowth_secondReserve_factorization

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedPopulationFirstSplitSubtrees_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedPopulationFirstSplitSubtrees_map_eq_product

#print axioms
  ProbabilityTheory.BranchingRandomWalk.recursiveReserveFailure_measurable

#print axioms
  ProbabilityTheory.BranchingRandomWalk.measure_recursiveReserveFailure_succ

#print axioms
  ProbabilityTheory.BranchingRandomWalk.measure_recursiveReserveFailure_eq_pow

#print axioms
  ProbabilityTheory.BranchingRandomWalk.BasicBranchingAssumptions.rawSplitEvent_measure_pos

#print axioms
  ProbabilityTheory.BranchingRandomWalk.exists_nat_cutoff_positive_boundedSelectedSplit

#print axioms
  ProbabilityTheory.BranchingRandomWalk.selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos

/-! The concrete thesis reserve selector inherits the nonempty-a.s.
assumption from `BasicBranchingAssumptions`, while its positive split mass is
provided by `GoodSplit`. This closes the `hfinite` input to the recursive
product-law theorem for the actual ordered offspring law. -/

section ConcreteFiniteSplit

open MeasureTheory ProbabilityTheory
open Combinatorics.Branching

variable {ι α X : Type*} [MeasurableSpace X] [Countable ι]
  [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]

theorem concrete_reserve_split_completion_ae_finite
    (L : ProbabilityTheory.BranchingRandomWalk.StepLaw ι α X)
    (h : ProbabilityTheory.BranchingRandomWalk.BasicBranchingAssumptions L) :
    ∃ M : ℕ,
      ∀ᵐ ω ∂ProbabilityTheory.BranchingRandomWalk.stepFieldLaw L.sorted,
        ProbabilityTheory.BranchingRandomWalk.selectedPopulationSplitCompletion
          (ProbabilityTheory.BranchingRandomWalk.reserveSelectionBelowPotential
            (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
            L.potential (M : ℝ)) ω ≠ ⊤ := by
  letI : IsProbabilityMeasure L.raw := h.rawProbability
  letI : IsProbabilityMeasure L.sorted := inferInstance
  obtain ⟨M, hpositive, hsplitMeas⟩ :=
    ProbabilityTheory.BranchingRandomWalk.exists_nat_cutoff_positive_reserveSplit
      L h
  let R : Step.FiniteSelection α X :=
    ProbabilityTheory.BranchingRandomWalk.reserveSelectionBelowPotential
      (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
      L.potential (M : ℝ)
  have hR : Measurable R.select := by
    simpa [R] using
      ProbabilityTheory.BranchingRandomWalk.reserveSelectionBelowPotential_measurable
        (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
        (ProbabilityTheory.BranchingRandomWalk.firstTwoBySlotOrder_measurable
          (α := α) (X := X)) L.potential (M : ℝ)
  have hnonemptyAE : ∀ᵐ ξ ∂L.sorted, (R ξ).Nonempty := by
    simpa [R] using
      ProbabilityTheory.BranchingRandomWalk.reserveSelectionBelowPotential_nonempty_ae
        L h (M : ℝ)
  have hnonemptyMeas : Measurable (fun ξ : Step α X => (R ξ).Nonempty) := by
    exact (measurable_of_countable fun s : Finset α => s.Nonempty).comp hR
  have hnonempty : L.sorted {ξ | (R ξ).Nonempty} = 1 :=
    (ae_iff_prob_eq_one hnonemptyMeas).mp hnonemptyAE
  have hsplit : MeasurableSet {ξ : Step α X | 2 ≤ (R ξ).card} := by
    simpa [R, ProbabilityTheory.BranchingRandomWalk.splitBy] using hsplitMeas
  have hpositive' : 0 < L.sorted {ξ : Step α X | 2 ≤ (R ξ).card} := by
    simpa [R, ProbabilityTheory.BranchingRandomWalk.splitBy] using hpositive
  refine ⟨M, ?_⟩
  exact ProbabilityTheory.BranchingRandomWalk.selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos
    L.sorted R hR hnonempty hsplit hpositive'

#print axioms concrete_reserve_split_completion_ae_finite

end ConcreteFiniteSplit
