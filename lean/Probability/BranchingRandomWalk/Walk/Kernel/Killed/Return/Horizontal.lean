import Probability.BranchingRandomWalk.Walk.Kernel.Killed.Return
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Horizontal

/-!
# Horizontal tubes and killed return kernels

Strict centered tube events give lower bounds for killed walks that remain in
a wider closed interval and return to the closed tube interval.  This bridge
is independent of any asymptotic theorem.
-/

open MeasureTheory Set

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A strict centered tube is contained in the corresponding killed-return
event with any wider outer interval. -/
theorem strictTubeProbability_le_returnKernel_centeredIcc
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {innerWidth outerWidth : ℝ} {n : ℕ}
    (hn : 0 < n) (hinner : 0 ≤ innerWidth)
    (hwidth : innerWidth ≤ outerWidth) :
    independentIncrementLaw ν
        {increment | InOpenHorizontalTube (1 / 2) innerWidth n increment} ≤
      returnKernel ν
        (Set.Icc (-(outerWidth / 2)) (outerWidth / 2)) measurableSet_Icc
        (Set.Icc (-(innerWidth / 2)) (innerWidth / 2)) measurableSet_Icc
        n ⟨0, by constructor <;> linarith⟩ univ := by
  rw [returnKernel_apply_univ_eq_staysIn_endsIn]
  apply measure_mono
  intro increment hincrement
  change StaysIn (Set.Icc (-(outerWidth / 2)) (outerWidth / 2))
      n 0 increment ∧
    0 + partialSum n increment ∈
      Set.Icc (-(innerWidth / 2)) (innerWidth / 2)
  simpa only [zero_add] using
    InOpenHorizontalTube.staysIn_and_endpoint_centeredIcc hincrement hn hwidth

end ProbabilityTheory.RandomWalk
