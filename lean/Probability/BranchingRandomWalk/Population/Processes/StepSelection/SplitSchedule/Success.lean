module

public import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Completion

/-!
# Population-size success on a split schedule

A trial succeeds when its started selected population has reached the target
size at its fixed completion generation.  The test is adapted at every global
generation.  At the actual completion time it agrees with the corresponding
fixed-age population of the assigned pre-sampled root.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The started trial population has reached `target` particles at global
generation `n`. -/
def successTest
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold target i n : ℕ) : Set (RootIndexed.StepField Root α X) :=
  {ω | target ≤
    (component (time R root initial threshold i) R root i n ω).card}

theorem successTest_measurable_of_countable
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (hinitial : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) initial)
    (threshold target i n : ℕ) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (successTest R root initial threshold target i n) := by
  have hcomponent := component_adapted R hR root i
    (time R root initial threshold i)
    (time_isStoppingTime_of_countable R hR root initial hinitial threshold i) n
  have hcard : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (fun ω => (component
        (time R root initial threshold i) R root i n ω).card) :=
    (measurable_of_countable
      (fun s : Finset (TreeNode α) => s.card)).comp hcomponent
  exact hcard measurableSet_Ici

/-- A finite completion identity forces the corresponding split start to be
finite and exactly `duration` generations earlier. -/
theorem component_eq_population_of_completion
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold duration i n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hcompletion : completion R root initial threshold duration i ω = n) :
    component (time R root initial threshold i) R root i n ω =
      RootIndexed.StepSelection.population R duration ω (root i) := by
  let start := time R root initial threshold i ω
  have hfinite : start ≠ ⊤ := by
    intro htop
    have : completion R root initial threshold duration i ω = ⊤ := by
      simp [completion, start, htop]
    rw [this] at hcompletion
    exact WithTop.top_ne_coe hcompletion
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hsum : k + duration = n := by
    apply WithTop.coe_injective
    calc
      ((k + duration : ℕ) : WithTop ℕ) = (k : WithTop ℕ) + duration := by
        simp
      _ = start + duration := congrArg (fun z : WithTop ℕ => z + duration) hk
      _ = completion R root initial threshold duration i ω := by
        rfl
      _ = (n : WithTop ℕ) := hcompletion
  have hkn : k ≤ n := by omega
  have hsub : n - k = duration := by omega
  unfold component
  rw [ProbabilityTheory.BranchingRandomWalk.Concurrent.Finite.component_eq_of_start
    (fun _ : Unit => time R root initial threshold i)
    (fun _ : Unit => candidate R root i) () ω hkn]
  · simp [candidate, hsub]
  · exact hk.symm

theorem mem_successTest_at_completion_iff
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold duration target i n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hcompletion : completion R root initial threshold duration i ω = n) :
    ω ∈ successTest R root initial threshold target i n ↔
      target ≤
        (RootIndexed.StepSelection.population R duration ω (root i)).card := by
  simp only [successTest, Set.mem_ofPred_eq]
  rw [component_eq_population_of_completion R root initial threshold duration
    i n ω hcompletion]

theorem mem_successAtCompletion_iff_population
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold duration target i : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hfinite : completion R root initial threshold duration i ω ≠ ⊤) :
    ω ∈ successAtCompletion
        (completion R root initial threshold duration i)
        (successTest R root initial threshold target i) ↔
      target ≤
        (RootIndexed.StepSelection.population R duration ω (root i)).card := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
  constructor
  · rintro ⟨k, hk, hsuccess⟩
    have hkn : k = n := WithTop.coe_injective (hk.symm.trans hn.symm)
    subst k
    exact (mem_successTest_at_completion_iff R root initial threshold
      duration target i n ω hn.symm).mp hsuccess
  · intro hsuccess
    exact ⟨n, hn.symm,
      (mem_successTest_at_completion_iff R root initial threshold
        duration target i n ω hn.symm).mpr hsuccess⟩

/-- The first trial whose fixed-age selected population reaches `target` is a
stopping time. -/
theorem firstPopulationSuccess_isStoppingTime
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold duration target : ℕ)
    (hcompletion : ∀ i, IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (completion R root initial threshold duration i))
    (htest : ∀ i n, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (successTest R root initial threshold target i n))
    (candidates : Set ℕ) :
    IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (firstDeclaredSuccess
        (orderedCandidateDeclarationWithin
          (completion R root initial threshold duration)
          (fun i => successAtCompletion
            (completion R root initial threshold duration i)
            (successTest R root initial threshold target i))
          candidates (fun j i => j < i))) := by
  exact firstSuccessfulCompletion_isStoppingTime R root initial
    threshold duration hcompletion
    (successTest R root initial threshold target) htest candidates

theorem firstPopulationSuccess_isStoppingTime_of_countable
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (hinitial : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) initial)
    (threshold duration target : ℕ) (candidates : Set ℕ) :
    IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (firstDeclaredSuccess
        (orderedCandidateDeclarationWithin
          (completion R root initial threshold duration)
          (fun i => successAtCompletion
            (completion R root initial threshold duration i)
            (successTest R root initial threshold target i))
          candidates (fun j i => j < i))) := by
  apply firstPopulationSuccess_isStoppingTime R root initial
    threshold duration target
  · exact completion_isStoppingTime_of_countable R hR root initial hinitial
      threshold duration
  · exact successTest_measurable_of_countable R hR root initial hinitial
      threshold target

/-- The observable ordered declaration is exactly the event that the current
fixed-age population reaches the target and all earlier trial populations do
not. -/
theorem mem_orderedPopulationDeclaration_iff
    {Root α X : Type*}
    (R : Step.FiniteSelection α X) (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (threshold duration target : ℕ) (candidates : Set ℕ)
    (n : ℕ) (ω : RootIndexed.StepField Root α X) :
    ω ∈ orderedCandidateDeclarationWithin
        (completion R root initial threshold duration)
        (fun i => successAtCompletion
          (completion R root initial threshold duration i)
          (successTest R root initial threshold target i))
        candidates (fun j i => j < i) n ↔
      ∃ i ∈ candidates,
        completion R root initial threshold duration i ω = n ∧
        target ≤
          (RootIndexed.StepSelection.population R duration ω (root i)).card ∧
        ∀ j ∈ candidates, j < i →
          ¬ target ≤
            (RootIndexed.StepSelection.population R duration ω (root j)).card := by
  rw [mem_orderedDeclaration_iff R root initial threshold duration
    (fun i => successAtCompletion
      (completion R root initial threshold duration i)
      (successTest R root initial threshold target i)) candidates n ω]
  constructor
  · rintro ⟨i, hi, hcompletion, hsuccess, hfailed⟩
    have hfinitei : completion R root initial threshold duration i ω ≠ ⊤ := by
      intro htop
      rw [htop] at hcompletion
      exact WithTop.top_ne_coe hcompletion
    refine ⟨i, hi, hcompletion,
      (mem_successAtCompletion_iff_population R root initial threshold
        duration target i ω hfinitei).mp hsuccess, ?_⟩
    intro j hj hji hpopulation
    apply hfailed j hj hji
    have hle := completion_mono R root initial threshold duration ω
      (Nat.le_of_lt hji)
    have hfinitej : completion R root initial threshold duration j ω ≠ ⊤ := by
      intro htop
      apply hfinitei
      exact top_unique (htop ▸ hle)
    exact (mem_successAtCompletion_iff_population R root initial threshold
      duration target j ω hfinitej).mpr hpopulation
  · rintro ⟨i, hi, hcompletion, hpopulation, hfailed⟩
    have hfinitei : completion R root initial threshold duration i ω ≠ ⊤ := by
      intro htop
      rw [htop] at hcompletion
      exact WithTop.top_ne_coe hcompletion
    refine ⟨i, hi, hcompletion,
      (mem_successAtCompletion_iff_population R root initial threshold
        duration target i ω hfinitei).mpr hpopulation, ?_⟩
    intro j hj hji hsuccess
    apply hfailed j hj hji
    have hle := completion_mono R root initial threshold duration ω
      (Nat.le_of_lt hji)
    have hfinitej : completion R root initial threshold duration j ω ≠ ⊤ := by
      intro htop
      apply hfinitei
      exact top_unique (htop ▸ hle)
    exact (mem_successAtCompletion_iff_population R root initial threshold
      duration target j ω hfinitej).mp hsuccess

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk
