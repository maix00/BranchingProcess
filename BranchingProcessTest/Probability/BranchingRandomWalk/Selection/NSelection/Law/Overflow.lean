import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Overflow

-- The stopped endpoint comparison has no FiniteSlices or boundary-normalization
-- hypothesis, for deterministic as well as jointly random initial positions.
open MeasureTheory ProbabilityTheory Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

example
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0 < N) (roots : Finset Root) (initial : Root → ℝ)
    (hleftFinite : ∀ᵐ ξ ∂μ, ξ.IsLeftLocallyFinite)
    (P : RootIndexed.CausalPopulation (RootIndexed.StepField Root α ℝ) Root α ℝ
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)) id)
    (initialOrder : ∀ field, Order.DominatingMap (P 0 field)
      (↑(RootIndexed.initialPopulation (α := α) roots) : Set (RootIndexed.TreeNode Root α))
      (fun p => initial p.1) (fun q => initial q.1))
    (n : ℕ) (x : ℝ) :
    let Q := RootIndexed.stepFieldLaw (Root := Root) μ
    Q {field | (n : WithTop ℕ) ≤ populationOverflowTime P N field ∧
      ∃ p ∈ P n field, RootIndexed.position initial id field p.1 p.2 ≤ x} ≤
    Q {field | (RootIndexed.selectedPopulationTotalized N roots initial id id n field).inf
      (fun q => ((RootIndexed.position initial id field q.1 q.2 : ℝ) : WithTop ℝ)) ≤ x} := by
  exact RootIndexed.measure_selectedPopulation_lowerTail_le_firstN μ N hN roots initial hleftFinite P initialOrder n x

example
    {Initial Root α : Type*} [MeasurableSpace Initial] [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (initialLaw : Measure Initial) [IsProbabilityMeasure initialLaw]
    (N : ℕ) (hN : 0 < N) (roots : Finset Root)
    (initial : Initial → Root → ℝ) (hinitial : Measurable initial)
    (P : Initial → RootIndexed.CausalPopulation (RootIndexed.StepField Root α ℝ) Root α ℝ
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)) id)
    (hpopulation : ∀ k, Measurable
      (fun sample : Initial × RootIndexed.StepField Root α ℝ => P sample.1 k sample.2))
    (hleftFinite : ∀ᵐ ξ ∂μ, ξ.IsLeftLocallyFinite)
    (initialOrder : ∀ᵐ a ∂initialLaw, ∀ field, Nonempty (Order.DominatingMap
      (P a 0 field)
      (↑(RootIndexed.initialPopulation (α := α) roots) : Set (RootIndexed.TreeNode Root α))
      (fun p => initial a p.1) (fun q => initial a q.1)))
    (n : ℕ) (x : ℝ) :
    let Q := RootIndexed.stepFieldLaw (Root := Root) μ
    let population := fun k (sample : Initial × RootIndexed.StepField Root α ℝ) =>
      P sample.1 k sample.2
    (initialLaw.prod Q) {sample |
      (n : WithTop ℕ) ≤ populationOverflowTime population N sample ∧
      ∃ p ∈ population n sample,
        RootIndexed.position (initial sample.1) id sample.2 p.1 p.2 ≤ x} ≤
    (initialLaw.prod Q) {sample |
      (RootIndexed.selectedPopulationTotalized N roots (initial sample.1) id id n sample.2).inf
        (fun q => ((RootIndexed.position (initial sample.1) id sample.2 q.1 q.2 : ℝ) : WithTop ℝ)) ≤ x} := by
  exact RootIndexed.measure_selectedPopulation_lowerTail_le_firstN_of_randomInitial μ initialLaw N hN roots initial hinitial P hpopulation hleftFinite initialOrder n x

#print axioms RootIndexed.measure_selectedPopulation_lowerTail_le_firstN
#print axioms RootIndexed.measure_selectedPopulation_lowerTail_le_firstN_of_randomInitial
