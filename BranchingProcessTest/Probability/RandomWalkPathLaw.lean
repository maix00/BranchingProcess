import Probability.BranchingRandomWalk.Walk.Path.Law

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
