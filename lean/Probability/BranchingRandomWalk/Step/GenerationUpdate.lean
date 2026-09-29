module

public import Combinatorics.BranchingWalk.Step.GenerationUpdate
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field

@[expose] public section

/-!
# Measurability of generation-local step-field updates

The deterministic update is coordinatewise.  Consequently an update of one
address depth is measurable whenever its replacement and fallback fields are
measurable; no countability assumption on roots or child slots is involved.
-/

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory
open Combinatorics.Branching

namespace RootIndexed.StepField

/-- A generation-local update of two measurable random root-indexed fields is
measurable as a complete root-indexed field. -/
theorem updateGeneration_measurable
    {Ω Root α X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (n : ℕ)
    (replacement fallback : Ω → RootIndexed.StepField Root α X)
    (hreplacement : Measurable replacement)
    (hfallback : Measurable fallback) :
    Measurable fun ω =>
      Combinatorics.Branching.RootIndexed.StepField.updateGeneration n
        (replacement ω) (fallback ω) := by
  apply measurable_pi_iff.mpr
  intro r
  apply measurable_pi_iff.mpr
  intro u
  by_cases hu : u.length = n
  · simp only [Combinatorics.Branching.RootIndexed.StepField.updateGeneration,
      Combinatorics.Branching.StepField.updateGeneration, hu, ↓reduceIte]
    fun_prop
  · simp only [Combinatorics.Branching.RootIndexed.StepField.updateGeneration,
      Combinatorics.Branching.StepField.updateGeneration, hu, ↓reduceIte]
    fun_prop

end RootIndexed.StepField

end ProbabilityTheory.BranchingRandomWalk
