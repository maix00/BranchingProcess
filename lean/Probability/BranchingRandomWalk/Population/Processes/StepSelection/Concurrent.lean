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
    {Root α X : Type*} (R : Step.FiniteSelection α X)
    (r : Root) (_start age : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    Finset (RootIndexed.TreeNode Root α) :=
  (RootIndexed.StepSelection.population R age ω r).image fun u => (r, u)

theorem mem_candidate_iff
    {Root α X : Type*} (R : Step.FiniteSelection α X)
    (r : Root) (start age : ℕ) (ω : RootIndexed.StepField Root α X)
    (q : RootIndexed.TreeNode Root α) :
    q ∈ candidate R r start age ω ↔
      q.1 = r ∧ q.2 ∈ RootIndexed.StepSelection.population R age ω r := by
  simp [candidate, Prod.ext_iff, eq_comm, and_comm]

/-- A candidate of age `age` is observable by global generation
`start + age`. Countability is needed for the Ulam--Harris addresses used by
the finite selected population, not for the root labels. -/
theorem candidate_adapted
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (start age : ℕ) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (start + age)]
      (candidate R r start age) := by
  have hpopulation : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) age]
      (fun ω => RootIndexed.StepSelection.population R age ω r) :=
    (measurable_pi_apply r).comp
      (RootIndexed.StepSelection.population_adapted R hR age)
  have hcandidate : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) age]
      (candidate R r start age) := by
    let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) age
    rw [measurable_finset_iff]
    intro q
    by_cases hq : q.1 = r
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
    {Root α X : Type*}
    (start : Root → RootIndexed.StepField Root α X → WithTop ℕ)
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    Finset (RootIndexed.TreeNode Root α) :=
  ProbabilityTheory.BranchingRandomWalk.Concurrent.Finite.component
    start (candidate R) r n ω

/-- Union of the finitely enabled root populations at global generation
`n`. -/
noncomputable def population
    {Root α X : Type*}
    (enabled : ℕ → RootIndexed.StepField Root α X → Finset Root)
    (start : Root → RootIndexed.StepField Root α X → WithTop ℕ)
    (R : Step.FiniteSelection α X) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    Finset (RootIndexed.TreeNode Root α) :=
  ProbabilityTheory.BranchingRandomWalk.Concurrent.Finite.population
    enabled start (candidate R) n ω

theorem component_adapted
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (start : Root → RootIndexed.StepField Root α X → WithTop ℕ)
    (hstart : ∀ r, IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (start r)) :
    ∀ r n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (component start R r n) := by
  exact ProbabilityTheory.BranchingRandomWalk.Concurrent.Finite.component_adapted
    (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
    start hstart (candidate R) (candidate_adapted R hR)

theorem population_adapted
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (enabled : ℕ → RootIndexed.StepField Root α X → Finset Root)
    (start : Root → RootIndexed.StepField Root α X → WithTop ℕ)
    (henabled : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | enabled n ω = s})
    (henabledRange : ∀ n, (Set.range (enabled n)).Countable)
    (hstart : ∀ r, IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (start r)) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (population enabled start R n) := by
  exact ProbabilityTheory.BranchingRandomWalk.Concurrent.Finite.population_adapted
    (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
    enabled start (candidate R) henabled henabledRange
    (component_adapted R hR start hstart)

end Concurrent
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk
