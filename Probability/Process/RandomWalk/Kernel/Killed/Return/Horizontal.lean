/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Killed.Return
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal

/-!
# Horizontal tubes and killed return kernels

Strict centered tube events give lower bounds for killed walks that remain in
a wider closed interval and return to the closed tube interval.  This bridge
is independent of any asymptotic theorem.
-/

@[expose] public section

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

/-- The same strict centered increment tube lower-bounds a return row from
every initial point in a centered initial interval, provided the sum of the
initial and path widths fits inside both target intervals. -/
theorem strictTubeProbability_le_returnKernel_centeredIcc_from
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {pathWidth initialWidth outerWidth returnWidth initial : ℝ} {n : ℕ}
    (hn : 0 < n) (hpathWidth : 0 ≤ pathWidth)
    (hinitial : initial ∈
      Set.Icc (-(initialWidth / 2)) (initialWidth / 2))
    (houter : initialWidth + pathWidth ≤ outerWidth)
    (hreturn : initialWidth + pathWidth ≤ returnWidth) :
    independentIncrementLaw ν
        {increment | InOpenHorizontalTube (1 / 2) pathWidth n increment} ≤
      returnKernel ν
        (Set.Icc (-(outerWidth / 2)) (outerWidth / 2)) measurableSet_Icc
        (Set.Icc (-(returnWidth / 2)) (returnWidth / 2)) measurableSet_Icc
        n ⟨initial, by
          have _hsum : initialWidth ≤ returnWidth := by linarith
          constructor <;> nlinarith [hinitial.1, hinitial.2]⟩ Set.univ := by
  rw [returnKernel_apply_univ_eq_staysIn_endsIn]
  apply measure_mono
  intro increment hincrement
  exact hincrement.staysIn_and_endpoint_centeredIcc_from
    hn hinitial houter hreturn

/-- Scaled normalized form of
`strictTubeProbability_le_returnKernel_centeredIcc_from`. -/
theorem strictTubeProbability_le_returnKernel_centeredIcc_from_normalized
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {pathWidth initialWidth outerWidth returnWidth scale initial : ℝ} {n : ℕ}
    (hn : 0 < n) (hscale : 0 < scale) (hpathWidth : 0 ≤ pathWidth)
    (hinitial : initial ∈
      Set.Icc (-(initialWidth / 2)) (initialWidth / 2))
    (houter : initialWidth + pathWidth ≤ outerWidth)
    (hreturn : initialWidth + pathWidth ≤ returnWidth) :
    independentIncrementLaw ν
        {increment |
          InOpenHorizontalTube (1 / 2) (pathWidth * scale) n increment} ≤
      returnKernel ν
        (Set.Icc (-(outerWidth * scale / 2))
          (outerWidth * scale / 2)) measurableSet_Icc
        (Set.Icc (-(returnWidth * scale / 2))
          (returnWidth * scale / 2)) measurableSet_Icc
        n ⟨scale * initial, by
          have _hreturnWidth : initialWidth ≤ returnWidth := by linarith
          constructor <;> nlinarith [hinitial.1, hinitial.2]⟩ Set.univ := by
  simpa only [add_mul] using
    strictTubeProbability_le_returnKernel_centeredIcc_from
      ν hn (mul_nonneg hpathWidth hscale.le)
        (initial := scale * initial)
        (pathWidth := pathWidth * scale)
        (initialWidth := initialWidth * scale)
        (outerWidth := outerWidth * scale)
        (returnWidth := returnWidth * scale)
        (by constructor <;> nlinarith [hinitial.1, hinitial.2])
        (by nlinarith [mul_le_mul_of_nonneg_right houter hscale.le])
        (by nlinarith [mul_le_mul_of_nonneg_right hreturn hscale.le])

/-- A strict centered tube together with an explicit terminal constraint is
contained in the corresponding killed-return event.  The width controlling
the path and the terminal interval are independent parameters. -/
theorem strictTubeEndsInProbability_le_returnKernel_Icc
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {corridorWidth outerWidth returnLower returnUpper : ℝ} {n : ℕ}
    (hn : 0 < n) (hwidth : corridorWidth ≤ outerWidth)
    (hreturnLower : returnLower ≤ 0) (hreturnUpper : 0 ≤ returnUpper) :
    independentIncrementLaw ν {increment |
        InOpenHorizontalTube (1 / 2) corridorWidth n increment ∧
          partialSum n increment ∈ Set.Ioo returnLower returnUpper} ≤
      returnKernel ν
        (Set.Icc (-(outerWidth / 2)) (outerWidth / 2)) measurableSet_Icc
        (Set.Icc returnLower returnUpper) measurableSet_Icc
        n ⟨0, hreturnLower, hreturnUpper⟩ Set.univ := by
  rw [returnKernel_apply_univ_eq_staysIn_endsIn]
  apply measure_mono
  rintro increment ⟨hcorridorEvent, hreturn⟩
  constructor
  · exact (InOpenHorizontalTube.staysIn_and_endpoint_centeredIcc
      hcorridorEvent hn hwidth).1
  · simpa only [zero_add] using ⟨hreturn.1.le, hreturn.2.le⟩

/-- Scaled centered form of `strictTubeEndsInProbability_le_returnKernel_Icc`.
The terminal constraint is stated in normalized coordinates. -/
theorem strictTubeNormalizedEndsInProbability_le_returnKernel_centeredIcc
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {corridorWidth outerWidth returnWidth scale : ℝ} {n : ℕ}
    (hn : 0 < n) (hscale : 0 < scale)
    (hwidth : corridorWidth ≤ outerWidth) (hreturn : 0 ≤ returnWidth) :
    independentIncrementLaw ν {increment |
        InOpenHorizontalTube (1 / 2) (corridorWidth * scale) n increment ∧
          partialSum n increment / scale ∈
            Set.Ioo (-(returnWidth / 2)) (returnWidth / 2)} ≤
      returnKernel ν
        (Set.Icc (-(outerWidth * scale / 2))
          (outerWidth * scale / 2)) measurableSet_Icc
        (Set.Icc (-(returnWidth * scale / 2))
          (returnWidth * scale / 2)) measurableSet_Icc
        n ⟨0, by constructor <;> nlinarith⟩ Set.univ := by
  calc
    _ ≤ independentIncrementLaw ν {increment |
        InOpenHorizontalTube (1 / 2) (corridorWidth * scale) n increment ∧
          partialSum n increment ∈
            Set.Ioo (-(returnWidth * scale / 2))
              (returnWidth * scale / 2)} := by
      apply measure_mono
      rintro increment ⟨hcorridor, hendpoint⟩
      refine ⟨hcorridor, ?_⟩
      constructor
      · have := (lt_div_iff₀ hscale).mp hendpoint.1
        nlinarith
      · have := (div_lt_iff₀ hscale).mp hendpoint.2
        nlinarith
    _ ≤ _ := by
      apply strictTubeEndsInProbability_le_returnKernel_Icc
        ν hn (mul_le_mul_of_nonneg_right hwidth hscale.le)
      all_goals nlinarith

end ProbabilityTheory.RandomWalk
