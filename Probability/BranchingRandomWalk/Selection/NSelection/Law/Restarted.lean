import Probability.BranchingRandomWalk.Selection.NSelection.Law.CausalPopulation
import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity
import Probability.BranchingRandomWalk.Population.Processes.Causal.RelativePosition.Real

/-!
# Coupling a restarted killed population to first-N selection

The killed source is constructed from relative-position windows on the left
half of one common pre-sampled field.  Rank installation then produces a
second field with the original product law, on which first-`N` selection is
run.  The result is a measure-level coupling with both marginals verified.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- The restarted killed population, realized on the left half of the common
two-copy pre-sampled field used by rank installation. -/
noncomputable def RootIndexed.restartedRealPositionSource
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k)) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark))
      RootIndexed.StepField.left := by
  let killed := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
    initialPosition d hd initial hinitialDepth cutoff window hwindow upper hupper
  have hleft : ∀ k, @Measurable
      (RootIndexed.StepField (Root ⊕ Root) α Mark)
      (RootIndexed.StepField Root α Mark)
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) k)
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark) k)
      RootIndexed.StepField.left := by
    intro k
    rw [show RootIndexed.StepField.left =
      (RootIndexed.StepField.reindex Sum.inl :
        RootIndexed.StepField (Root ⊕ Root) α Mark →
          RootIndexed.StepField Root α Mark) by rfl]
    exact RootIndexed.StepField.reindex_filtration_measurable
      (X := Mark) Sum.inl k
  exact killed.pullback RootIndexed.StepField.left
    hleft
    (by rfl)

theorem RootIndexed.restartedRealPositionSource_finiteSlices
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k)) :
    (RootIndexed.restartedRealPositionSource initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper).FiniteSlices := by
  intro n field
  unfold RootIndexed.restartedRealPositionSource
  rw [RootIndexed.CausalPopulation.pullback_population]
  exact RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
    initialPosition d hd initial hinitialDepth cutoff window hwindow upper hupper
    n (RootIndexed.StepField.left field)

/-- The finite presentation of one killed source slice used by the concrete
first-`N` coupling algorithm.  Finiteness remains a theorem about the
set-valued source rather than part of the population type. -/
noncomputable def RootIndexed.restartedRealPositionSourceSlice
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark) :
    Finset (RootIndexed.TreeNode Root α) :=
  (RootIndexed.restartedRealPositionSource_finiteSlices initialPosition d hd
    initial hinitialDepth cutoff window hwindow upper hupper).toFinset n field

@[simp] theorem RootIndexed.mem_restartedRealPositionSourceSlice
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark)
    (p : RootIndexed.TreeNode Root α) :
    p ∈ RootIndexed.restartedRealPositionSourceSlice initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper n field ↔
    p ∈ RootIndexed.restartedRealPositionSource initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper n field :=
  RootIndexed.CausalPopulation.FiniteSlices.mem_toFinset _ _ _ _

@[simp] theorem RootIndexed.restartedRealPositionSource_zero
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (field : RootIndexed.StepField (Root ⊕ Root) α Mark) :
    RootIndexed.restartedRealPositionSource initialPosition d hd initial
        hinitialDepth cutoff window hwindow upper hupper 0 field = initial := by
  unfold RootIndexed.restartedRealPositionSource
  rw [RootIndexed.CausalPopulation.pullback_population]
  ext p
  simp [
    RootIndexed.CausalPopulation.ofRestartedRealPositionSets,
    RootIndexed.CausalPopulation.ofPredicate]

@[simp] theorem RootIndexed.restartedRealPositionSourceSlice_zero
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (field : RootIndexed.StepField (Root ⊕ Root) α Mark) :
    RootIndexed.restartedRealPositionSourceSlice initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper 0 field = initial := by
  ext p
  simp

/-- The canonical product-law coupling for a restarted real-valued killed
population.  Spatial domination is a separate pathwise theorem about this
coupling; it is not built into the definition of a coupling. -/
noncomputable def RootIndexed.restartedRealPositionCoupling
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (hadmits : ∀ (k : ℕ) (field : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initialPosition d id
          (k + 1) field)
        (RootIndexed.childrenAtGeneration k parents field))
    (n : ℕ) :
    ProbabilityTheory.Coupling
      (RootIndexed.stepFieldLaw (Root := Root) μ)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  let source := RootIndexed.restartedRealPositionSource initialPosition d hd
    initial hinitialDepth cutoff window hwindow upper hupper
  exact RootIndexed.causalPopulationCoupling μ N roots initialPosition d hd
    id measurable_id hadmits source
    (RootIndexed.restartedRealPositionSource_finiteSlices initialPosition d hd
      initial hinitialDepth cutoff window hwindow upper hupper) n

/-- On every sample where the restarted killed population stays below
capacity, rank installation supplies an explicit dominating injection into
the first-`N` population.  The initial-slice witness is kept explicit so this
statement also supports nonstandard finite initial populations. -/
noncomputable def RootIndexed.restartedRealPositionCoupledInjection
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (hadmits : ∀ (k : ℕ) (field : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initialPosition d id
          (k + 1) field)
        (RootIndexed.childrenAtGeneration k parents field))
    (initialInjection : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        ((RootIndexed.restartedRealPositionSourceSlice initialPosition d hd initial
          hinitialDepth cutoff window hwindow upper hupper) 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.coupledPopulation N roots (fun _ => initialPosition) d id
          (fun _ => hadmits) RootIndexed.StepField.left
          RootIndexed.StepField.right
          (RootIndexed.restartedRealPositionSourceSlice initialPosition d hd initial
            hinitialDepth cutoff window hwindow upper hupper) 0 field)) ())
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark)
    (hcapacity : ∀ k < n,
      ((RootIndexed.restartedRealPositionSourceSlice initialPosition d hd initial
        hinitialDepth cutoff window hwindow upper hupper) (k + 1) field).card ≤ N) :
    Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        ((RootIndexed.restartedRealPositionSourceSlice initialPosition d hd initial
          hinitialDepth cutoff window hwindow upper hupper) n field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.coupledField N roots (fun _ => initialPosition) d id
            (fun _ => hadmits) RootIndexed.StepField.left
            RootIndexed.StepField.right
            (RootIndexed.restartedRealPositionSourceSlice initialPosition d hd initial
              hinitialDepth cutoff window hwindow upper hupper) n field))
        (RootIndexed.coupledPopulation N roots (fun _ => initialPosition) d id
          (fun _ => hadmits) RootIndexed.StepField.left
          RootIndexed.StepField.right
          (RootIndexed.restartedRealPositionSourceSlice initialPosition d hd initial
            hinitialDepth cutoff window hwindow upper hupper) n field)) () := by
  apply RootIndexed.causalPopulationCoupledInjection N roots initialPosition d id
    hadmits
    (RootIndexed.restartedRealPositionSource initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper)
    (RootIndexed.restartedRealPositionSource_finiteSlices initialPosition d hd
      initial hinitialDepth cutoff window hwindow upper hupper)
    initialInjection
  · intro x y z hyx
    simpa only [id_eq, add_comm] using add_le_add_right hyx z
  · exact hcapacity

/-- Standard multi-root form, started from the empty address at every root in
`roots`.  The generation-zero injection is canonical and therefore requires
no additional hypothesis. -/
noncomputable def RootIndexed.restartedRealPositionCoupledInjectionOnRoots
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ) (hd : Measurable d)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (hadmits : ∀ (k : ℕ) (field : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initialPosition d id
          (k + 1) field)
        (RootIndexed.childrenAtGeneration k parents field))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark)
    (hcapacity : field ∈
      (RootIndexed.restartedRealPositionSource initialPosition d hd
        (RootIndexed.initialPopulation (α := α) roots)
        (by simp [RootIndexed.mem_initialPopulation_iff])
        cutoff window hwindow upper hupper).capacityEvent N n) :
    let source := RootIndexed.restartedRealPositionSourceSlice initialPosition d hd
      (RootIndexed.initialPopulation (α := α) roots)
      (by simp [RootIndexed.mem_initialPopulation_iff])
      cutoff window hwindow upper hupper
    Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (source n field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.coupledField N roots (fun _ => initialPosition) d id
            (fun _ => hadmits) RootIndexed.StepField.left
            RootIndexed.StepField.right source n field))
        (RootIndexed.coupledPopulation N roots (fun _ => initialPosition) d id
          (fun _ => hadmits) RootIndexed.StepField.left
          RootIndexed.StepField.right source n field)) () := by
  dsimp only
  apply RootIndexed.restartedRealPositionCoupledInjection N roots
    initialPosition d hd (RootIndexed.initialPopulation (α := α) roots)
    (by simp [RootIndexed.mem_initialPopulation_iff]) cutoff window hwindow
    upper hupper hadmits
  · intro sample
    simpa only [RootIndexed.restartedRealPositionSourceSlice_zero,
      RootIndexed.coupledPopulation, RootIndexed.coupledField,
      RootIndexed.selectedPopulation] using
      (RootIndexed.initialPopulationInjection id d roots initialPosition
        (RootIndexed.StepField.left sample)
        (RootIndexed.StepField.right sample))
  · intro k hk
    exact RootIndexed.CausalPopulation.FiniteSlices.card_succ_le_of_mem_capacityEvent
      _ (RootIndexed.restartedRealPositionSource_finiteSlices initialPosition d hd
        (RootIndexed.initialPopulation (α := α) roots)
        (by simp [RootIndexed.mem_initialPopulation_iff]) cutoff window hwindow
        upper hupper) N n hcapacity k hk

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
