import Probability.BranchingRandomWalk.Population.Processes.Causal
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Capacity events for causal finite populations

The capacity event is defined for an arbitrary causal finite population.  A
finite union bound and Markov's inequality reduce its failure probability to
first moments of the generation sizes.  No independence, offspring order, or
second moment is used.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed.CausalFinitePopulation

open Combinatorics.UlamHarris Combinatorics.Branching

variable {Ω Root α X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    {ℱ : ℕ → MeasurableSpace Ω}
    {stepField : Ω → RootIndexed.StepField Root α X}

/-- Generation size as an extended nonnegative random variable. -/
noncomputable def size
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField)
    (n : ℕ) (ω : Ω) : ENNReal :=
  ((P n ω).card : ENNReal)

theorem card_measurable
    [Countable (RootIndexed.TreeNode Root α)]
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField)
    (n : ℕ) (hℱ : ℱ n ≤ ‹MeasurableSpace Ω›) :
    Measurable fun ω => (P n ω).card := by
  have hpopulation : Measurable (P n) :=
    (P.adapted n).mono hℱ le_rfl
  have hset : Measurable fun ω =>
      (↑(P n ω) : Set (RootIndexed.TreeNode Root α)) :=
    measurable_finset_iff_measurable_set.mp hpopulation
  rw [show (fun ω => (P n ω).card) =
      (fun ω => (↑(P n ω) : Set (RootIndexed.TreeNode Root α)).ncard) by
    funext ω
    exact (Set.ncard_coe_finset (P n ω)).symm]
  exact measurable_ncard.comp hset

theorem size_measurable
    [Countable (RootIndexed.TreeNode Root α)]
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField)
    (n : ℕ) (hℱ : ℱ n ≤ ‹MeasurableSpace Ω›) :
    Measurable (P.size n) :=
  (measurable_of_countable (fun k : ℕ => (k : ENNReal))).comp
    (P.card_measurable n hℱ)

/-- Every generation through `T` contains at most `N` retained particles. -/
def capacityEvent
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField)
    (N T : ℕ) : Set Ω :=
  ⋂ k : Fin (T + 1), {ω | (P k ω).card ≤ N}

theorem mem_capacityEvent_iff
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField)
    (N T : ℕ) (ω : Ω) :
    ω ∈ P.capacityEvent N T ↔ ∀ k ≤ T, (P k ω).card ≤ N := by
  simp only [capacityEvent, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h k hk
    exact h ⟨k, Nat.lt_succ_iff.mpr hk⟩
  · intro h k
    exact h k (Nat.le_of_lt_succ k.2)

theorem card_succ_le_of_mem_capacityEvent
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField)
    (N n : ℕ) {ω : Ω} (hω : ω ∈ P.capacityEvent N n)
    (k : ℕ) (hk : k < n) :
    (P (k + 1) ω).card ≤ N :=
  (P.mem_capacityEvent_iff N n ω).mp hω (k + 1)
    (Nat.succ_le_iff.mpr hk)

theorem measurableSet_capacityEvent
    [Countable (RootIndexed.TreeNode Root α)]
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField)
    (N T : ℕ) (hℱ : ∀ n, ℱ n ≤ ‹MeasurableSpace Ω›) :
    MeasurableSet (P.capacityEvent N T) := by
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_setOfPred.mpr
    ((measurable_of_countable (fun m : ℕ => m ≤ N)).comp
      (P.card_measurable k (hℱ k)))

theorem capacityEvent_compl_eq_iUnion
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField)
    (N T : ℕ) :
    (P.capacityEvent N T)ᶜ =
      ⋃ k : Fin (T + 1), {ω | N < (P k ω).card} := by
  ext ω
  simp [capacityEvent]

/-- Finite-horizon capacity failure is bounded by the sum of its generation
failure probabilities. -/
theorem measure_capacityEvent_compl_le_sum
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField)
    (μ : Measure Ω) (N T : ℕ) :
    μ (P.capacityEvent N T)ᶜ ≤
      ∑ k : Fin (T + 1), μ {ω | N < (P k ω).card} := by
  rw [P.capacityEvent_compl_eq_iUnion N T]
  exact measure_iUnion_fintype_le μ _

/-- First-moment capacity bound.  This is the form used by the one-sided
`L¹` proof: each generation enters only through its expected population
size. -/
theorem measure_capacityEvent_compl_le_lintegral
    [Countable (RootIndexed.TreeNode Root α)]
    (P : RootIndexed.CausalFinitePopulation Ω Root α X ℱ stepField)
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
  have hevent : {ω | N < (P k ω).card} =
      {ω | (N + 1 : ℕ) ≤ P.size k ω} := by
    ext ω
    change N < (P k ω).card ↔
      ((N + 1 : ℕ) : ENNReal) ≤ ((P k ω).card : ENNReal)
    norm_cast
  rw [hevent]
  exact hmarkov

end RootIndexed.CausalFinitePopulation
end ProbabilityTheory.BranchingRandomWalk
