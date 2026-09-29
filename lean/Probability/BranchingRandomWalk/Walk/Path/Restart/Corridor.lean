import Probability.BranchingRandomWalk.Walk.Path.Restart.Basic
import Probability.BranchingRandomWalk.Walk.Path.Corridor.Horizontal

/-!
# Restarted horizontal-corridor laws

The generic restarted-window law is defined in `Restart.Basic`.  This file
contains the IID factorization for constant horizontal corridors, after the
ordinary horizontal-tube probability has been introduced.
-/

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A constant restarted horizontal tube under IID increments factors into
the ordinary tube probabilities before and after the restart. -/
theorem restartedWindowProbability_horizontal_add_eq_mul
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a width : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : 0 ≤ width)
    (cutoff tail : ℕ) (initial : ℝ) :
    restartedWindowProbability (iidSequenceLaw ν) cutoff
        (fun _ => Set.Icc (-a * width) ((1 - a) * width))
        (cutoff + tail) initial =
      horizontalTubeProbability (iidSequenceLaw ν) a width cutoff *
        horizontalTubeProbability (iidSequenceLaw ν) a width tail := by
  rw [restartedWindowProbability_Icc_add_eq_mul]
  have hzero : (0 : ℝ) ∈ Set.Icc (-a * width) ((1 - a) * width) := by
    constructor <;> nlinarith
  have hevent (n : ℕ) :
      {increment : ℕ → ℝ |
        InClosedInterval (-a * width) ((1 - a) * width) n 0 increment} =
      {increment | InHorizontalTube a width n increment} := by
    ext increment
    simpa [StaysIn, InHorizontalTube] using
      (staysIn_Icc_iff_inClosedInterval
        (-a * width) ((1 - a) * width) n 0 hzero increment).symm
  rw [hevent cutoff, hevent tail]
  rfl

/-- Unified formula for a restarted horizontal tube at an arbitrary
observation time. -/
theorem restartedWindowProbability_horizontal_eq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a width : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : 0 ≤ width)
    (cutoff n : ℕ) (initial : ℝ) :
    restartedWindowProbability (iidSequenceLaw ν) cutoff
        (fun _ => Set.Icc (-a * width) ((1 - a) * width)) n initial =
      if n ≤ cutoff then
        horizontalTubeProbability (iidSequenceLaw ν) a width n
      else
        horizontalTubeProbability (iidSequenceLaw ν) a width cutoff *
          horizontalTubeProbability (iidSequenceLaw ν) a width (n - cutoff) := by
  by_cases hn : n ≤ cutoff
  · rw [ite_eq_left hn]
    unfold restartedWindowProbability horizontalTubeProbability
    congr 1
    ext increment
    exact (inRestartedWindows_Icc_of_le_iff
      (-a * width) ((1 - a) * width) hn initial increment).trans <| by
        have hzero : (0 : ℝ) ∈
            Set.Icc (-a * width) ((1 - a) * width) := by
          constructor <;> nlinarith
        simpa [StaysIn, InHorizontalTube] using
          (staysIn_Icc_iff_inClosedInterval
            (-a * width) ((1 - a) * width) n 0 hzero increment).symm
  · rw [ite_eq_right hn]
    have hnEq : n = cutoff + (n - cutoff) := by omega
    conv_lhs => rw [hnEq]
    exact restartedWindowProbability_horizontal_add_eq_mul
      ν ha0 ha1 hwidth cutoff (n - cutoff) initial

end ProbabilityTheory.RandomWalk
