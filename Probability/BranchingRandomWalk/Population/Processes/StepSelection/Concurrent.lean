import Probability.BranchingRandomWalk.Population.Processes.Concurrent.Finite
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.RootIndexed

/-!
# Concurrent root-indexed step selections

Each root of a pre-sampled field supplies one age-indexed selected branching
population. Observable start times embed these populations into a common
global clock. Particles retain their root labels, while measurability does not
require the ambient root type to be countable.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace Concurrent

open Combinatorics.UlamHarris Combinatorics.Branching

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The age-indexed population supplied by one pre-sampled root. The start
generation is an interface parameter; the underlying fresh tree depends only
on its age. -/
noncomputable def candidate
    {Root I α X : Type*} (R : Step.FiniteSelection α X)
    (root : I → Root) (i : I) (_start age : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    Finset (RootIndexed.TreeNode Root α) :=
  (RootIndexed.StepSelection.population R age ω (root i)).image
    fun u => (root i, u)

theorem mem_candidate_iff
    {Root I α X : Type*} (R : Step.FiniteSelection α X)
    (root : I → Root) (i : I) (start age : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (q : RootIndexed.TreeNode Root α) :
    q ∈ candidate R root i start age ω ↔
      q.1 = root i ∧
        q.2 ∈ RootIndexed.StepSelection.population R age ω (root i) := by
  simp [candidate, Prod.ext_iff, eq_comm, and_comm]

/-- A candidate of age `age` is observable by global generation
`start + age`. Neither roots nor child slots are enumerated in the
measurability proof. -/
theorem candidate_adapted
    {Root I α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : I → Root) (i : I) (start age : ℕ) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (start + age)]
      (candidate R root i start age) := by
  have hpopulation : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) age]
      (fun ω => RootIndexed.StepSelection.population R age ω (root i)) :=
    (measurable_pi_apply (root i)).comp
      (RootIndexed.StepSelection.population_adapted R hR age)
  have hcandidate : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) age]
      (candidate R root i start age) := by
    let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) age
    rw [measurable_finset_iff]
    intro q
    by_cases hq : q.1 = root i
    · have hmem := (measurable_finset_mem q.2).comp hpopulation
      convert hmem using 1
      funext ω
      simp only [Function.comp_apply, mem_candidate_iff, hq, true_and]
    · simp only [mem_candidate_iff, hq, false_and]
      exact measurable_const
  exact hcandidate.mono
    ((RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)).mono
      (Nat.le_add_left age start)) le_rfl

/-- One root population embedded at its observable random start time. -/
noncomputable def component
    {Root I α X : Type*}
    (start : I → RootIndexed.StepField Root α X → WithTop ℕ)
    (R : Step.FiniteSelection α X) (root : I → Root) (i : I) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    Finset (RootIndexed.TreeNode Root α) :=
  ProbabilityTheory.BranchingRandomWalk.Concurrent.Finite.component
    start (candidate R root) i n ω

/-- Union of the finitely enabled root populations at global generation
`n`. -/
noncomputable def population
    {Root I α X : Type*}
    (enabled : ℕ → RootIndexed.StepField Root α X → Finset I)
    (start : I → RootIndexed.StepField Root α X → WithTop ℕ)
    (R : Step.FiniteSelection α X) (root : I → Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    Finset (RootIndexed.TreeNode Root α) :=
  ProbabilityTheory.BranchingRandomWalk.Concurrent.Finite.population
    enabled start (candidate R root) n ω

theorem component_adapted
    {Root I α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : I → Root)
    (start : I → RootIndexed.StepField Root α X → WithTop ℕ)
    (hstart : ∀ i, IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (start i)) :
    ∀ i n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (component start R root i n) := by
  exact ProbabilityTheory.BranchingRandomWalk.Concurrent.Finite.component_adapted
    (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
    start hstart (candidate R root) (candidate_adapted R hR root)

theorem population_adapted
    {Root I α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : I → Root)
    (enabled : ℕ → RootIndexed.StepField Root α X → Finset I)
    (start : I → RootIndexed.StepField Root α X → WithTop ℕ)
    (henabled : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | enabled n ω = s})
    (henabledRange : ∀ n, (Set.range (enabled n)).Countable)
    (hstart : ∀ i, IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (start i)) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (population enabled start R root n) := by
  exact ProbabilityTheory.BranchingRandomWalk.Concurrent.Finite.population_adapted
    (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
    enabled start (candidate R root) henabled henabledRange
    (component_adapted R hR root start hstart)

end Concurrent
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk
