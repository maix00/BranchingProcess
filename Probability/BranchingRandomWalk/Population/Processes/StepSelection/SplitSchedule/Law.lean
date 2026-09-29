module

public import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Success
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law

/-!
# Laws of fixed-age population success

Population success at a fixed age is an observation of one pre-sampled root.
Hence injectively assigned roots give independent success indicators under the
root-indexed product law, and every indicator has the same marginal law.

Countability is used only to observe the cardinality of a finite population.
Neither the root type nor the family of trials is required to be countable.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The event that one pre-sampled selected population reaches the target at
the specified age. -/
def successSet
    {α X : Type*} (R : Step.FiniteSelection α X)
    (duration target : ℕ) : Set (Mark α (Step α X)) :=
  {ω | target ≤
    (ProbabilityTheory.BranchingRandomWalk.StepSelection.population
      R duration ω).card}

theorem measurableSet_successSet
    {α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (duration target : ℕ) :
    MeasurableSet (successSet R duration target) := by
  have hpopulation : Measurable
      (ProbabilityTheory.BranchingRandomWalk.StepSelection.population
        R duration) :=
    (ProbabilityTheory.BranchingRandomWalk.StepSelection.population_adapted
      R hR duration).mono (generationFiltration.le duration) le_rfl
  have hcard : Measurable (fun ω : Mark α (Step α X) =>
      (ProbabilityTheory.BranchingRandomWalk.StepSelection.population
        R duration ω).card) :=
    (measurable_of_countable
      (fun s : Finset (TreeNode α) => s.card)).comp hpopulation
  exact hcard measurableSet_Ici

/-- Fixed-age success for the root assigned to a trial. -/
def successEvent
    {I Root α X : Type*} (R : Step.FiniteSelection α X)
    (root : I → Root) (duration target : ℕ) (i : I) :
    Set (RootIndexed.StepField Root α X) :=
  {ω | target ≤ (RootIndexed.StepSelection.population
    R duration ω (root i)).card}

theorem successEvent_eq_preimage
    {I Root α X : Type*} (R : Step.FiniteSelection α X)
    (root : I → Root) (duration target : ℕ) (i : I) :
    successEvent R root duration target i =
      (fun ω : RootIndexed.StepField Root α X => ω (root i)) ⁻¹'
      successSet R duration target :=
  rfl

/-- Fixed-age success is observable from the generation domain flow at that
age.  Countability is used only for the discrete space of finite address
sets whose cardinality is tested; neither roots nor trials are enumerated. -/
theorem measurableSet_successEvent_adapted
    {I Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : I → Root) (duration target : ℕ) (i : I) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) duration]
      (successEvent R root duration target i) := by
  have hpopulation : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) duration]
      (fun ω : RootIndexed.StepField Root α X =>
        RootIndexed.StepSelection.population R duration ω (root i)) :=
    (measurable_pi_apply (root i)).comp
      (RootIndexed.StepSelection.population_adapted R hR duration)
  have hcard : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) duration]
      (fun ω : RootIndexed.StepField Root α X =>
        (RootIndexed.StepSelection.population R duration ω (root i)).card) :=
    (measurable_of_countable
      (fun s : Finset (TreeNode α) => s.card)).comp hpopulation
  exact hcard measurableSet_Ici

theorem measurableSet_successEvent
    {I Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : I → Root) (duration target : ℕ) (i : I) :
    MeasurableSet (successEvent R root duration target i) := by
  exact RootIndexed.stepFiltration.le duration
    (successEvent R root duration target i)
    (measurableSet_successEvent_adapted R hR root duration target i)

/-- Boolean observation of fixed-age success. -/
noncomputable def successIndicator
    {α X : Type*} (R : Step.FiniteSelection α X)
    (duration target : ℕ) (ω : Mark α (Step α X)) : Bool :=
  decide (ω ∈ successSet R duration target)

@[simp] theorem successIndicator_eq_true_iff
    {α X : Type*} (R : Step.FiniteSelection α X)
    (duration target : ℕ) (ω : Mark α (Step α X)) :
    successIndicator R duration target ω = true ↔
      ω ∈ successSet R duration target := by
  simp [successIndicator]

@[simp] theorem successIndicator_eq_false_iff
    {α X : Type*} (R : Step.FiniteSelection α X)
    (duration target : ℕ) (ω : Mark α (Step α X)) :
    successIndicator R duration target ω = false ↔
      ω ∉ successSet R duration target := by
  simp [successIndicator]

theorem successIndicator_preimage_true
    {α X : Type*} (R : Step.FiniteSelection α X)
    (duration target : ℕ) :
    successIndicator R duration target ⁻¹' {true} =
      successSet R duration target := by
  ext ω
  simp

theorem successIndicator_measurable
    {α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (duration target : ℕ) :
    Measurable (successIndicator R duration target) := by
  apply measurable_to_bool
  rw [successIndicator_preimage_true]
  exact measurableSet_successSet R hR duration target

theorem successIndicator_root_preimage_true
    {I Root α X : Type*} (R : Step.FiniteSelection α X)
    (root : I → Root) (duration target : ℕ) (i : I) :
    (fun ω : RootIndexed.StepField Root α X =>
      successIndicator R duration target (ω (root i))) ⁻¹' {true} =
        successEvent R root duration target i := by
  ext ω
  simp [successEvent, successSet]

/-- Failure is the complement of fixed-age success. -/
def failureEvent
    {I Root α X : Type*} (R : Step.FiniteSelection α X)
    (root : I → Root) (duration target : ℕ) (i : I) :
    Set (RootIndexed.StepField Root α X) :=
  (successEvent R root duration target i)ᶜ

theorem measurableSet_failureEvent
    {I Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : I → Root) (duration target : ℕ) (i : I) :
    MeasurableSet (failureEvent R root duration target i) :=
  (measurableSet_successEvent R hR root duration target i).compl

theorem successIndicator_root_preimage_false
    {I Root α X : Type*} (R : Step.FiniteSelection α X)
    (root : I → Root) (duration target : ℕ) (i : I) :
    (fun ω : RootIndexed.StepField Root α X =>
      successIndicator R duration target (ω (root i))) ⁻¹' {false} =
        failureEvent R root duration target i := by
  ext ω
  simp [failureEvent, successEvent, successSet]

/-- Success indicators attached to distinct pre-sampled roots are mutually
independent. The trial index and root types may both be arbitrary. -/
theorem successIndicators_independent
    {I Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : I → Root) (hroot : Function.Injective root)
    (duration target : ℕ) (μ : Measure (Step α X))
    [IsProbabilityMeasure μ] :
    iIndepFun
      (fun i (ω : RootIndexed.StepField Root α X) =>
        successIndicator R duration target (ω (root i)))
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  have hfields :=
    (RootIndexed.stepFieldLaw_roots_independent μ).precomp hroot
  simpa [Function.comp_def] using hfields.comp
    (fun _ => successIndicator R duration target)
    (fun _ => successIndicator_measurable R hR duration target)

/-- The success events themselves are mutually independent. -/
theorem successEvents_independent
    {I Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : I → Root) (hroot : Function.Injective root)
    (duration target : ℕ) (μ : Measure (Step α X))
    [IsProbabilityMeasure μ] :
    iIndepSet (successEvent R root duration target)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  apply (iIndepSet_iff_meas_biInter
    (fun i => measurableSet_successEvent R hR root duration target i)).2
  intro s
  have h := iIndepFun.measure_inter_preimage_eq_mul
    (successIndicators_independent R hR root hroot duration target μ)
      s (sets := fun _ => {true})
      (fun _ _ => MeasurableSet.singleton true)
  simpa only [successIndicator_root_preimage_true] using h

/-- Every assigned root has the same fixed-age success probability. -/
theorem measure_successEvent
    {I Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : I → Root) (duration target : ℕ) (i : I)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    RootIndexed.stepFieldLaw (Root := Root) μ
        (successEvent R root duration target i) =
      ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
        (α := α) μ (successSet R duration target) := by
  have heval : Measurable
      (fun ω : RootIndexed.StepField Root α X => ω (root i)) :=
    measurable_pi_apply (root i)
  rw [successEvent_eq_preimage, ← Measure.map_apply heval
    (measurableSet_successSet R hR duration target),
    RootIndexed.stepFieldLaw_root_marginal μ (root i)]

/-- Every assigned root has the complementary fixed-age failure
probability. -/
theorem measure_failureEvent
    {I Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : I → Root) (duration target : ℕ) (i : I)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    RootIndexed.stepFieldLaw (Root := Root) μ
        (failureEvent R root duration target i) =
      1 - ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
        (α := α) μ (successSet R duration target) := by
  rw [failureEvent, measure_compl
    (measurableSet_successEvent R hR root duration target i) (by finiteness),
    measure_univ, measure_successEvent R hR root duration target i μ]

/-- The probability that every trial in a finite injectively rooted family
fails is the corresponding power of the one-root failure probability. -/
theorem measure_iInter_failureEvent
    {I Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : I → Root) (hroot : Function.Injective root)
    (duration target : ℕ) (μ : Measure (Step α X))
    [IsProbabilityMeasure μ] (s : Finset I) :
    RootIndexed.stepFieldLaw (Root := Root) μ
        (⋂ i ∈ s, failureEvent R root duration target i) =
      (1 - ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
        (α := α) μ (successSet R duration target)) ^ s.card := by
  have h := iIndepFun.measure_inter_preimage_eq_mul
    (successIndicators_independent R hR root hroot duration target μ)
      s (sets := fun _ => {false})
      (fun _ _ => MeasurableSet.singleton false)
  simpa only [successIndicator_root_preimage_false,
    measure_failureEvent R hR root duration target,
    Finset.prod_const] using h

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk
