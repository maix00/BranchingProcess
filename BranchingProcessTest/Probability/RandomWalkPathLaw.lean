import Probability.BranchingRandomWalk.Walk.Path.Law
import Probability.BranchingRandomWalk.Walk.Path.Scaling

/-!
# Tests for full random-walk path-law conversion

These examples exercise path-valued pushforward laws, rather than only
one-time marginals.
-/

open MeasureTheory ProbabilityTheory
open Combinatorics.Branching

example (initial : ℝ) (μ : Measure (ℕ → ℝ)) :
    Measure.map (_root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.processPath id)
        (Measure.map (Walk.ofIncrements initial) μ) =
      Measure.map (_root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.positionPath id initial) μ := by
  exact _root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.map_processPath_map_ofIncrements id measurable_id initial μ

example (initial : ℝ) (ν : Measure (ℕ → ℝ))
    [IsProbabilityMeasure ν] :
    Measure.map (_root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.processPath id)
        ((_root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.ofIncrementLaw initial ν :
          ProbabilityTheory.BranchingRandomWalk.RandomWalk ℝ ℝ).law) =
      Measure.map (_root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.positionPath id initial) ν := by
  exact _root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.map_processPath_ofIncrementLaw id measurable_id initial ν

example (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ) (t : ℝ) :
    _root_.ProbabilityTheory.RandomWalk.normalizedStepPath scale n increment t =
      (scale n)⁻¹ *
        Combinatorics.Branching.displaceWith id
          (Combinatorics.Branching.Walk.stepFieldOfIncrements increment) []
          (Combinatorics.Branching.Walk.lineNode ⌊(n : ℝ) * t⌋₊) := by
  exact ProbabilityTheory.BranchingRandomWalk.Walk.normalizedStepPath_eq_displaceWith
    id scale n increment t

example (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ) (t : ℝ) :
    _root_.ProbabilityTheory.RandomWalk.normalizedStepPath scale n increment t =
      (scale n)⁻¹ *
        (Combinatorics.Branching.Cloud.discreteTimeCloud_ofBranchingWalk id
          (Combinatorics.Branching.Walk.ofIncrements 0 increment)).position
            PUnit.unit (Combinatorics.Branching.Walk.lineNode ⌊(n : ℝ) * t⌋₊) := by
  exact ProbabilityTheory.BranchingRandomWalk.Walk.normalizedStepPath_eq_discreteTimeCloud_position
    id scale n increment t

#print axioms ProbabilityTheory.BranchingRandomWalk.RandomWalk.processPath_ofIncrements
#print axioms ProbabilityTheory.BranchingRandomWalk.RandomWalk.map_processPath_map_ofIncrements
#print axioms ProbabilityTheory.BranchingRandomWalk.RandomWalk.map_processPath_ofIncrementLaw
#print axioms ProbabilityTheory.BranchingRandomWalk.Walk.normalizedStepPath_eq_displaceWith
#print axioms ProbabilityTheory.BranchingRandomWalk.Walk.normalizedStepPath_eq_discreteTimeCloud_position
