import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.Horizontal

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open scoped BigOperators

/-- A source-style finite partition may have unequal segment lengths and a
different oscillation event on each segment. The IID probability is the
product of its one-block probabilities. -/
example (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    iidSequenceLaw ν {increment : ℕ → ℝ | ∀ j : Fin 3,
      Combinatorics.Sequence.blockCoordinates
        (AdditivePath.blockStart (fun k => k + 1) j.val) (j.val + 1) increment ∈
          blockOscillationLTEvent (1 : ℝ) (j.val + 1)} =
      ∏ j : Fin 3, iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 (j.val + 1) increment ∈
          blockOscillationLTEvent (1 : ℝ) (j.val + 1)} := by
  exact iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent ν
    (fun k => k + 1) 3
    (fun j => blockOscillationLTEvent (1 : ℝ) (j.val + 1))
    (by intro j; exact measurableSet_blockOscillationLTEvent 1 (j.val + 1))

#print axioms ProbabilityTheory.RandomWalk.iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent
