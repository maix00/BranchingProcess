import Combinatorics.BranchingWalk.Walk.Path.Corridor.Horizontal
import Probability.BranchingRandomWalk.Walk.Law
import Probability.BranchingRandomWalk.Walk.Path.Window
import Probability.BranchingRandomWalk.Walk.Path.Restart
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Horizontal tube probabilities for random walks

The logarithm is `ENNReal.log : ENNReal → EReal`, so an impossible tube has
log-probability `-∞`, as required by small-deviation asymptotics.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

theorem measurableSet_inHorizontalTube (a width : ℝ) (n : ℕ) :
    MeasurableSet {increment : ℕ → ℝ |
      InHorizontalTube a width n increment} := by
  rw [show {increment : ℕ → ℝ | InHorizontalTube a width n increment} =
      ⋂ k : Fin n,
        {increment | -a * width ≤ partialSum (k + 1) increment} ∩
        {increment | partialSum (k + 1) increment ≤ (1 - a) * width} by
    ext increment
    simp [InHorizontalTube]]
  exact MeasurableSet.iInter fun k =>
    measurableSet_Ici.preimage (partialSum_measurable (k + 1)) |>.inter
      (measurableSet_Iic.preimage (partialSum_measurable (k + 1)))

/-- Probability of the horizontal-tube event under an increment-path law. -/
def horizontalTubeProbability (incrementLaw : Measure (ℕ → ℝ))
    (a width : ℝ) (n : ℕ) : ENNReal :=
  incrementLaw {increment | InHorizontalTube a width n increment}

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

/-- Extended-real log-probability of a horizontal tube. -/
noncomputable def horizontalTubeLogProbability
    (incrementLaw : Measure (ℕ → ℝ)) (a width : ℝ) (n : ℕ) : EReal :=
  ENNReal.log (horizontalTubeProbability incrementLaw a width n)

/-- The horizontal-tube probability is monotone in its width. -/
theorem horizontalTubeProbability_mono_width
    (incrementLaw : Measure (ℕ → ℝ))
    {a width₁ width₂ : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : width₁ ≤ width₂) :
    horizontalTubeProbability incrementLaw a width₁ n ≤
      horizontalTubeProbability incrementLaw a width₂ n :=
  measure_mono (inHorizontalTube_mono_width ha0 ha1 hwidth)

/-- The thesis monotonicity lemma for `q(width,n)`, stated with the
extended-real logarithm so it remains valid when a tube has probability zero.
-/
theorem horizontalTubeLogProbability_mono_width
    (incrementLaw : Measure (ℕ → ℝ))
    {a width₁ width₂ : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : width₁ ≤ width₂) :
    horizontalTubeLogProbability incrementLaw a width₁ n ≤
      horizontalTubeLogProbability incrementLaw a width₂ n :=
  ENNReal.log_monotone
    (horizontalTubeProbability_mono_width incrementLaw ha0 ha1 hwidth)

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
