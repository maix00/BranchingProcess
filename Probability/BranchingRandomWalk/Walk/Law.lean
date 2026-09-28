import Probability.BranchingRandomWalk.Walk.Path
import Mathlib.Probability.Independence.InfinitePi

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
  Measure.infinitePi fun _ : ℕ => ν

noncomputable instance independentIncrementLaw.instIsProbabilityMeasure
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (independentIncrementLaw ν) := by
  unfold independentIncrementLaw
  infer_instance

theorem independentIncrementLaw_coordinate (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (independentIncrementLaw ν).map (fun increment => increment n) = ν := by
  unfold independentIncrementLaw
  exact Measure.infinitePi_map_eval (fun _ : ℕ => ν) n

theorem independentIncrementLaw_independent (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    iIndepFun (fun n (increment : ℕ → ℝ) => increment n)
      (independentIncrementLaw ν) := by
  unfold independentIncrementLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : ℕ => ν) (X := fun _ : ℕ => id)
    (fun _ => measurable_id))

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
