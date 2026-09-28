import Probability.BranchingRandomWalk.Population.Processes.Causal
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Capacity events for causal populations

The capacity event is defined for an arbitrary causal population.  A
finite union bound and Markov's inequality reduce its failure probability to
first moments of the generation sizes.  No independence, offspring order, or
second moment is used.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk

namespace RootIndexed.CausalPopulation

open Combinatorics.UlamHarris Combinatorics.Branching

variable {Ω Root α X : Type*} [MeasurableSpace Ω]
    {ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {stepField : Ω → RootIndexed.StepField Root α X}

/-- Extended generation size. Infinite populations have size `∞`; no
finiteness assumption is hidden in the definition. -/
noncomputable def size
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (n : ℕ) (ω : Ω) : ENNReal :=
  (P n ω).encard.toENNReal

theorem population_measurable [Countable (RootIndexed.TreeNode Root α)]
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (n : ℕ) (hℱ : ℱ n ≤ ‹MeasurableSpace Ω›) :
    Measurable (P n) := by
  rw [measurable_set_iff]
  intro p
  exact (P.measurable_mem n p).mono hℱ le_rfl

theorem encard_measurable [Countable (RootIndexed.TreeNode Root α)]
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (n : ℕ) (hℱ : ℱ n ≤ ‹MeasurableSpace Ω›) :
    Measurable fun ω => (P n ω).encard :=
  measurable_encard.comp (P.population_measurable n hℱ)

theorem size_measurable [Countable (RootIndexed.TreeNode Root α)]
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (n : ℕ) (hℱ : ℱ n ≤ ‹MeasurableSpace Ω›) :
    Measurable (P.size n) :=
  (measurable_of_countable ENat.toENNReal).comp
    (P.encard_measurable n hℱ)

/-- Every generation through `T` has extended cardinality at most `N`.
Infinite slices therefore fail the event automatically. -/
def capacityEvent
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (N T : ℕ) : Set Ω :=
  ⋂ k : Fin (T + 1), {ω | (P k ω).encard ≤ N}

theorem mem_capacityEvent_iff
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (N T : ℕ) (ω : Ω) :
    ω ∈ P.capacityEvent N T ↔ ∀ k ≤ T, (P k ω).encard ≤ N := by
  simp only [capacityEvent, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h k hk
    exact h ⟨k, Nat.lt_succ_iff.mpr hk⟩
  · intro h k
    exact h k (Nat.le_of_lt_succ k.2)

theorem FiniteSlices.card_succ_le_of_mem_capacityEvent
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (hP : P.FiniteSlices) (N n : ℕ) {ω : Ω}
    (hω : ω ∈ P.capacityEvent N n) (k : ℕ) (hk : k < n) :
    (hP.toFinset (k + 1) ω).card ≤ N := by
  have h := (P.mem_capacityEvent_iff N n ω).mp hω (k + 1)
    (Nat.succ_le_iff.mpr hk)
  rw [(hP (k + 1) ω).encard_eq_coe_toFinset_card] at h
  exact_mod_cast h

theorem measurableSet_capacityEvent
    [Countable (RootIndexed.TreeNode Root α)]
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (N T : ℕ) (hℱ : ∀ n, ℱ n ≤ ‹MeasurableSpace Ω›) :
    MeasurableSet (P.capacityEvent N T) := by
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_setOfPred.mpr
    ((measurable_of_countable (fun m : ℕ∞ => m ≤ N)).comp
      (P.encard_measurable k (hℱ k)))

theorem capacityEvent_compl_eq_iUnion
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (N T : ℕ) :
    (P.capacityEvent N T)ᶜ =
      ⋃ k : Fin (T + 1), {ω | (N : ℕ∞) < (P k ω).encard} := by
  ext ω
  simp [capacityEvent]

theorem measure_capacityEvent_compl_le_sum
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (μ : Measure Ω) (N T : ℕ) :
    μ (P.capacityEvent N T)ᶜ ≤
      ∑ k : Fin (T + 1), μ {ω | (N : ℕ∞) < (P k ω).encard} := by
  rw [P.capacityEvent_compl_eq_iUnion N T]
  exact measure_iUnion_fintype_le μ _

/-- The capacity estimate is valid for an arbitrary set-valued population.
Finiteness is neither assumed nor encoded in its type. -/
theorem measure_capacityEvent_compl_le_lintegral
    [Countable (RootIndexed.TreeNode Root α)]
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (μ : Measure Ω) (N T : ℕ)
    (hℱ : ∀ n, ℱ n ≤ ‹MeasurableSpace Ω›) :
    μ (P.capacityEvent N T)ᶜ ≤
      ∑ k : Fin (T + 1),
        (∫⁻ ω, P.size k ω ∂μ) / (N + 1 : ℕ) := by
  refine (P.measure_capacityEvent_compl_le_sum μ N T).trans ?_
  apply Finset.sum_le_sum
  intro k _
  have hmarkov := meas_ge_le_lintegral_div (μ := μ)
    (P.size_measurable k (hℱ k)).aemeasurable
    (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N))
    (ENNReal.natCast_ne_top (N + 1))
  have hevent : {ω | (N : ℕ∞) < (P k ω).encard} =
      {ω | ((N + 1 : ℕ) : ENNReal) ≤ P.size k ω} := by
    ext ω
    simp only [size, Set.mem_ofPred_eq]
    norm_cast
    exact (ENat.add_one_le_iff (ENat.natCast_ne_top N)).symm
  rw [hevent]
  exact hmarkov

end RootIndexed.CausalPopulation

end ProbabilityTheory.BranchingRandomWalk
