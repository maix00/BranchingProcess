/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Basic
public import Probability.Sequence.IID
public import Probability.Process.RandomWalk.Path.Window
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Horizontal tube probabilities for random walks

The logarithm is `ENNReal.log : ENNReal → EReal`, so an impossible tube has
log-probability `-∞`, as required by small-deviation asymptotics.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk


theorem measurableSet_inHorizontalTube (a width : ℝ) (n : ℕ) :
    MeasurableSet {increment : ℕ → ℝ |
      InHorizontalTube a width n increment} := by
  rw [show {increment : ℕ → ℝ | InHorizontalTube a width n increment} =
      ⋂ k : Fin n,
        {increment | -a * width ≤ AdditivePath.displacement (k + 1) increment} ∩
        {increment | AdditivePath.displacement (k + 1) increment ≤ (1 - a) * width} by
    ext increment
    simp [InHorizontalTube]]
  exact MeasurableSet.iInter fun k =>
    measurableSet_Ici.preimage (displacement_measurable (k + 1)) |>.inter
      (measurableSet_Iic.preimage (displacement_measurable (k + 1)))

/-- The strict horizontal-tube event is measurable. -/
theorem measurableSet_inOpenHorizontalTube (a width : ℝ) (n : ℕ) :
    MeasurableSet {increment : ℕ → ℝ |
      InOpenHorizontalTube a width n increment} := by
  rw [show {increment : ℕ → ℝ | InOpenHorizontalTube a width n increment} =
      ⋂ k : Fin n,
        {increment | -a * width < AdditivePath.displacement (k + 1) increment} ∩
        {increment | AdditivePath.displacement (k + 1) increment < (1 - a) * width} by
    ext increment
    simp [InOpenHorizontalTube]]
  exact MeasurableSet.iInter fun k =>
    measurableSet_Ioi.preimage (displacement_measurable (k + 1)) |>.inter
      (measurableSet_Iio.preimage (displacement_measurable (k + 1)))

/-- The strict range-oscillation event for the partial-sum path through time
`n`. It is translation invariant: it constrains pairwise differences, not the
position of the path relative to a fixed center. -/
def partialSumRangeOscillationLTEvent (width : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {increment | ∀ i j : Fin (n + 1),
    |AdditivePath.displacement (i : ℕ) increment -
      AdditivePath.displacement (j : ℕ) increment| < width}

/-- The strict partial-sum range event is measurable. -/
theorem measurableSet_partialSumRangeOscillationLTEvent (width : ℝ) (n : ℕ) :
    MeasurableSet (partialSumRangeOscillationLTEvent width n) := by
  rw [show partialSumRangeOscillationLTEvent width n =
      ⋂ i : Fin (n + 1), ⋂ j : Fin (n + 1),
        {increment : ℕ → ℝ |
          |AdditivePath.displacement (i : ℕ) increment -
            AdditivePath.displacement (j : ℕ) increment| < width} by
    ext increment
    simp [partialSumRangeOscillationLTEvent]]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by
    exact measurableSet_Iio.preimage <|
      continuous_abs.measurable.comp <|
        (displacement_measurable (i : ℕ)).sub (displacement_measurable (j : ℕ))

/-- A path confined to a fixed open horizontal tube has strictly bounded
pairwise range. This forgets the tube's center and retains only its width. -/
theorem InOpenHorizontalTube.subset_partialSumRangeOscillationLTEvent
    {a width : ℝ} {n : ℕ} {increment : ℕ → ℝ}
    (ha : 0 < a) (ha' : a < 1) (hwidth : 0 < width)
    (h : InOpenHorizontalTube a width n increment) :
    increment ∈ partialSumRangeOscillationLTEvent width n := by
  have hposition (time : ℕ) (htime : time ≤ n) :
      -a * width < AdditivePath.displacement time increment ∧
        AdditivePath.displacement time increment < (1 - a) * width := by
    cases time with
    | zero =>
      constructor
      · have : 0 < a * width := mul_pos ha hwidth
        rw [AdditivePath.displacement_zero]
        nlinarith
      · have : 0 < (1 - a) * width := mul_pos (by linarith) hwidth
        rw [AdditivePath.displacement_zero]
        nlinarith
    | succ time =>
      have htime' : time < n := by omega
      simpa [InOpenHorizontalTube] using h ⟨time, htime'⟩
  change ∀ i j : Fin (n + 1),
    |AdditivePath.displacement (i : ℕ) increment -
      AdditivePath.displacement (j : ℕ) increment| < width
  intro i j
  have hi := hposition (i : ℕ) (Nat.le_of_lt_succ i.isLt)
  have hj := hposition (j : ℕ) (Nat.le_of_lt_succ j.isLt)
  apply abs_lt.mpr
  constructor <;> nlinarith

/-- Probability of the horizontal-tube event under an increment-path law. -/
def horizontalTubeProbability (incrementLaw : Measure (ℕ → ℝ))
    (a width : ℝ) (n : ℕ) : ENNReal :=
  incrementLaw {increment | InHorizontalTube a width n increment}

/-- Probability of the strict horizontal-tube event under an increment-path
law. -/
def openHorizontalTubeProbability (incrementLaw : Measure (ℕ → ℝ))
    (a width : ℝ) (n : ℕ) : ENNReal :=
  incrementLaw {increment | InOpenHorizontalTube a width n increment}

/-- Probability of the strict partial-sum range event under an
increment-path law. -/
def partialSumRangeOscillationLTProbability
    (incrementLaw : Measure (ℕ → ℝ)) (width : ℝ) (n : ℕ) : ENNReal :=
  incrementLaw (partialSumRangeOscillationLTEvent width n)

/-- A longer-horizon range event is contained in the corresponding shorter
one, since the latter observes only an initial segment of the partial-sum
path. -/
theorem partialSumRangeOscillationLTProbability_antitone_horizon
    (incrementLaw : Measure (ℕ → ℝ)) (width : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    partialSumRangeOscillationLTProbability incrementLaw width n ≤
      partialSumRangeOscillationLTProbability incrementLaw width m := by
  unfold partialSumRangeOscillationLTProbability partialSumRangeOscillationLTEvent
  apply measure_mono
  intro increment h i j
  exact h ⟨i.val, by omega⟩ ⟨j.val, by omega⟩

/-- The probability of a centered open tube is bounded by the probability of
the translation-invariant range event of the same width. -/
theorem openHorizontalTubeProbability_le_partialSumRangeOscillationLTProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a width : ℝ} (ha : 0 < a) (ha' : a < 1) (hwidth : 0 < width) (n : ℕ) :
    openHorizontalTubeProbability (iidSequenceLaw ν) a width n ≤
      partialSumRangeOscillationLTProbability (iidSequenceLaw ν) width n := by
  change iidSequenceLaw ν {increment | InOpenHorizontalTube a width n increment} ≤
    iidSequenceLaw ν (partialSumRangeOscillationLTEvent width n)
  apply measure_mono
  intro increment h
  exact InOpenHorizontalTube.subset_partialSumRangeOscillationLTEvent
    ha ha' hwidth h

/-- Reflecting the one-step law exchanges the left and right portions of a
horizontal tube.  No symmetry assumption on the increment law is needed. -/
theorem horizontalTubeProbability_map_neg
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a width : ℝ) (n : ℕ) :
    horizontalTubeProbability (iidSequenceLaw (ν.map fun x => -x))
        (1 - a) width n =
      horizontalTubeProbability (iidSequenceLaw ν) a width n := by
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
        (iidSequenceLaw (ν.map fun x => x / sigma))
        a (width / sigma) n =
      horizontalTubeProbability (iidSequenceLaw ν) a width n := by
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
