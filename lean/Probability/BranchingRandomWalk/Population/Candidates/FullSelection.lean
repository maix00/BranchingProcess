import Probability.BranchingRandomWalk.Population.Candidates.FullRank.Selection
import MeasureTheory.BranchingWalk.Step.Ordered

/-!
# Full selection versus finite truncation

On a fully ordered multi-root marked tree, exact equality of the finite
first-`N`-slot selection with the global top-`N` selection from all countably
many children, and the corresponding step of the adapted recursion.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory



/-- On a fully ordered multi-root marked tree, every step of the adapted
finite recursion equals the global top-`N` selection from all countably
many children of its current labelled population. -/
theorem selectedPopulation_fullSelection_step {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (n : ℕ) (ω : FiniteRootStepField m ℝ)
    (hω : ∀ i : Fin m, ∀ u : 𝕍,
      OrderedNatRealStep (ω i u)) :
    (↑(selectedPopulation N x (n + 1) ω) : Set (RootAddress m)) =
      {q | q ∈ allMultiRootChildren
          (selectedPopulation N x n ω) ω ∧
        fullRankBelow N x ω
          (allMultiRootChildren (selectedPopulation N x n ω) ω) q} := by
  classical
  let s := selectedPopulation N x n ω
  have hsdepth : ∀ p ∈ s, p.2.length = n := by
    intro p hp
    exact selectedPopulation_depth N x n ω p hp
  have hsfilter : s.filter (fun p => p.2.length = n) = s :=
    Finset.filter_true_of_mem hsdepth
  have hcdepth : ∀ q ∈ multiRootCandidates N s ω,
      q.2.length = n + 1 := by
    intro q hq
    exact multiRootCandidates_depth N s ω hsdepth q hq
  have hcfilter :
      (multiRootCandidates N s ω).filter
        (fun q => q.2.length = n + 1) =
      multiRootCandidates N s ω :=
    Finset.filter_true_of_mem hcdepth
  change (↑(finiteLeftmostAtGeneration N (n + 1) x ω
    (multiRootCandidatesAtGeneration N n s ω)) :
      Set (RootAddress m)) = _
  simp only [multiRootCandidatesAtGeneration,
    finiteLeftmostAtGeneration, hsfilter, hcfilter]
  exact finiteLeftmost_eq_fullSelection N x s ω
    (fun p _ => hω p.1 p.2)

theorem selectedPopulation_fullSelection_step_ae
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ orderedSteps = 1)
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ) :
    ∀ᵐ ω ∂finiteRootStepFieldLaw μ m, ∀ n : ℕ,
      (↑(selectedPopulation N x (n + 1) ω) : Set (RootAddress m)) =
        {q | q ∈ allMultiRootChildren
            (selectedPopulation N x n ω) ω ∧
          fullRankBelow N x ω
            (allMultiRootChildren
              (selectedPopulation N x n ω) ω) q} := by
  filter_upwards [finiteRootStepFieldLaw_all_ordered μ hμ m] with ω hω
  exact fun n => selectedPopulation_fullSelection_step N x n ω hω

end ProbabilityTheory.BranchingRandomWalk
