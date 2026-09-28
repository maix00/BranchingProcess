import Probability.BranchingRandomWalk.Walk.Path
import Probability.Sequence.IID

/-!
# Independent increment laws

The countable product of a one-step law is the canonical increment-path law
of a random walk. This construction is independent of branching and tilting.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

/-- Canonical independent increment-path law with common marginal `ν`. -/
noncomputable def independentIncrementLaw (ν : Measure ℝ) :
    Measure (ℕ → ℝ) :=
  iidSequenceLaw ν

noncomputable instance independentIncrementLaw.instIsProbabilityMeasure
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (independentIncrementLaw ν) := by
  unfold independentIncrementLaw
  exact iidSequenceLaw.instIsProbabilityMeasure ν

theorem independentIncrementLaw_coordinate (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (independentIncrementLaw ν).map (fun increment => increment n) = ν := by
  unfold independentIncrementLaw
  exact iidSequenceLaw_map_apply ν n

theorem independentIncrementLaw_independent (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    iIndepFun (fun n (increment : ℕ → ℝ) => increment n)
      (independentIncrementLaw ν) := by
  unfold independentIncrementLaw
  exact iidSequenceLaw_independent ν

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
