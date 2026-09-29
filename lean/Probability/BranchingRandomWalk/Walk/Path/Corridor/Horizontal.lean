import Combinatorics.BranchingWalk.Walk.Path.Corridor.Horizontal
import Probability.BranchingRandomWalk.Walk.Law
import Probability.BranchingRandomWalk.Walk.Path.Window
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Horizontal tube probabilities for random walks

The logarithm is `ENNReal.log : ENNReal → EReal`, so an impossible tube has
log-probability `-∞`, as required by small-deviation asymptotics.
-/

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

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

/-- The strict horizontal-tube event is measurable. -/
theorem measurableSet_inOpenHorizontalTube (a width : ℝ) (n : ℕ) :
    MeasurableSet {increment : ℕ → ℝ |
      InOpenHorizontalTube a width n increment} := by
  rw [show {increment : ℕ → ℝ | InOpenHorizontalTube a width n increment} =
      ⋂ k : Fin n,
        {increment | -a * width < partialSum (k + 1) increment} ∩
        {increment | partialSum (k + 1) increment < (1 - a) * width} by
    ext increment
    simp [InOpenHorizontalTube]]
  exact MeasurableSet.iInter fun k =>
    measurableSet_Ioi.preimage (partialSum_measurable (k + 1)) |>.inter
      (measurableSet_Iio.preimage (partialSum_measurable (k + 1)))

/-- Probability of the horizontal-tube event under an increment-path law. -/
def horizontalTubeProbability (incrementLaw : Measure (ℕ → ℝ))
    (a width : ℝ) (n : ℕ) : ENNReal :=
  incrementLaw {increment | InHorizontalTube a width n increment}

/-- Reflecting the one-step law exchanges the left and right portions of a
horizontal tube.  No symmetry assumption on the increment law is needed. -/
theorem horizontalTubeProbability_map_neg
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a width : ℝ) (n : ℕ) :
    horizontalTubeProbability (independentIncrementLaw (ν.map fun x => -x))
        (1 - a) width n =
      horizontalTubeProbability (independentIncrementLaw ν) a width n := by
  unfold independentIncrementLaw
  rw [← iidSequenceLaw_map_coordinatewise ν (fun x : ℝ => -x) measurable_neg]
  unfold horizontalTubeProbability
  rw [Measure.map_apply]
  · congr 1
    ext increment
    exact inHorizontalTube_neg_iff a width n increment
  · exact Measurable.of_eval fun i =>
      measurable_neg.comp (measurable_pi_apply i)
  · exact measurableSet_inHorizontalTube (1 - a) width n

/-- Standardizing every increment by a positive constant divides the tube
width by the same constant and leaves its probability unchanged. -/
theorem horizontalTubeProbability_map_div
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a width : ℝ) (n : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    horizontalTubeProbability
        (independentIncrementLaw (ν.map fun x => x / sigma))
        a (width / sigma) n =
      horizontalTubeProbability (independentIncrementLaw ν) a width n := by
  unfold independentIncrementLaw
  rw [← iidSequenceLaw_map_coordinatewise ν
    (fun x : ℝ => x / sigma) (measurable_id.div_const sigma)]
  unfold horizontalTubeProbability
  rw [Measure.map_apply]
  · congr 1
    ext increment
    exact inHorizontalTube_div_iff a width n increment hsigma
  · exact Measurable.of_eval fun i =>
      (measurable_id.div_const sigma).comp (measurable_pi_apply i)
  · exact measurableSet_inHorizontalTube a (width / sigma) n

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

/-- A tube constraint through a longer horizon implies the same constraint
through every shorter horizon. -/
theorem horizontalTubeProbability_mono_horizon
    (incrementLaw : Measure (ℕ → ℝ)) (a width : ℝ)
    {short long : ℕ} (hshort : short ≤ long) :
    horizontalTubeProbability incrementLaw a width long ≤
      horizontalTubeProbability incrementLaw a width short := by
  unfold horizontalTubeProbability
  apply measure_mono
  intro increment hlong k
  exact hlong ⟨k, lt_of_lt_of_le k.isLt hshort⟩

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

end ProbabilityTheory.RandomWalk
