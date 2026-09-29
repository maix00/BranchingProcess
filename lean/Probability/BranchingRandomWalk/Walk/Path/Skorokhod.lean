import Combinatorics.BranchingWalk.Walk.Path.Skorokhod
import Probability.BranchingRandomWalk.Walk.Law

/-!
# Laws of normalized random-walk paths in Skorokhod space

This file places the deterministic normalized step path under the canonical
i.i.d. increment law.  Its measurability uses the verified Skorokhod topology,
not the product measurable structure on an ambient function space.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- Law of the normalized `n`-step càdlàg path under i.i.d. increments. -/
noncomputable def normalizedStepPathLaw (ν : Measure ℝ)
    (scale : ℕ → ℝ) (n : ℕ) :
    Measure (CadlagPath Skorokhod.UnitInterval ℝ) :=
  (independentIncrementLaw ν).map
    (normalizedStepCadlagPathIcc scale n)

noncomputable instance normalizedStepPathLaw.instIsProbabilityMeasure
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (n : ℕ) :
    IsProbabilityMeasure (normalizedStepPathLaw ν scale n) := by
  unfold normalizedStepPathLaw
  infer_instance

theorem hasLaw_normalizedStepCadlagPathIcc
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (n : ℕ) :
    HasLaw (normalizedStepCadlagPathIcc scale n)
      (normalizedStepPathLaw ν scale n) (independentIncrementLaw ν) where
  aemeasurable := (measurable_normalizedStepCadlagPathIcc scale n).aemeasurable
  map_eq := rfl

end ProbabilityTheory.RandomWalk
