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

/-- The increment process seen after any deterministic time has the original
i.i.d. increment law. -/
theorem independentIncrementLaw_map_natAdd (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (offset : ℕ) :
    (independentIncrementLaw ν).map
        (fun increment n => increment (offset + n)) =
      independentIncrementLaw ν := by
  exact ProbabilityTheory.iidSequenceLaw_map_natAdd ν offset

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
