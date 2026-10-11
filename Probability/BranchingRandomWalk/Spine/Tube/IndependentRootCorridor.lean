/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Tube.RightTailOneGeneration
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.IndependentEventCount

/-!
# Independent-root lower bounds for tube populations

This file composes the path-count Paley--Zygmund estimate with the independent
root Chernoff bound.  The caller supplies the one-root first and second moment
estimates; the result counts initial roots whose descendant field contains a
path through the prescribed corridor.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

/-- If the one-root corridor path count has first moment `mean` and second
moment at most `second`, then exponentially few independent initial roots
have at most one quarter of the Paley--Zygmund mean number of corridor hits.
The moment bounds remain explicit inputs so that the random-walk corridor
estimates can be proved independently and then supplied here. -/
theorem measure_finiteRootCorridorCount_le_quarter_pzMean
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (initial : ℝ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (m : ℕ) (hm : 0 < m)
    (mean second : ℝ≥0∞)
    (hmean : (∫⁻ ω, Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
      ∂stepFieldLaw μ) = mean)
    (hsecond : (∫⁻ ω, (Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω) ^ 2
      ∂stepFieldLaw μ) ≤ second)
    (hsecond_pos : 0 < second) (hsecond_top : second ≠ ∞) :
    let pzMean := mean ^ 2 / second
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          (∑ r : Fin m,
            (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
              (fun _ => (1 : ℝ)) (field r)) ≤
            (m : ℝ) * pzMean.toReal / 4} ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := by
  classical
  let event : Set (StepField ℕ X) :=
    hasPathHistoryIn (ι := ℕ) φ n initial corridor
  let pzMean : ℝ≥0∞ := mean ^ 2 / second
  have hevent : MeasurableSet event :=
    measurableSet_hasPathHistoryIn φ n initial corridor hcorridor
  have hpz : pzMean ≤ (stepFieldLaw μ) event := by
    dsimp [pzMean, event]
    exact measure_hasPathHistoryIn_ge_of_pathGeneration_moments
      φ μ n initial corridor hcorridor mean second hmean hsecond
      hsecond_pos hsecond_top
  have hevent_le_one : (stepFieldLaw μ) event ≤ 1 := by
    calc
      (stepFieldLaw μ) event ≤ (stepFieldLaw μ) Set.univ :=
        measure_mono (Set.subset_univ event)
      _ = 1 := measure_univ
  have hpz_le_one : pzMean ≤ 1 := hpz.trans hevent_le_one
  have hpz_top : pzMean ≠ ∞ := ne_of_lt (hpz_le_one.trans_lt ENNReal.one_lt_top)
  have hpz_real_le_event : pzMean.toReal ≤ ((stepFieldLaw μ) event).toReal :=
    ENNReal.toReal_mono (measure_ne_top (stepFieldLaw μ) event) hpz
  have hthreshold : (m : ℝ) * pzMean.toReal / 4 ≤
      (m : ℝ) * ((stepFieldLaw μ) event).toReal / 4 := by
    have hmReal : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hpz_real_le_event hmReal]
  have hcount :=
    measure_finiteRootEventCount_le_quarter_mean μ event hevent m hm
  have hsubset :
      {field : FiniteRootStepField m ℕ X |
        (∑ r : Fin m, event.indicator (fun _ => (1 : ℝ)) (field r)) ≤
          (m : ℝ) * pzMean.toReal / 4} ⊆
      {field : FiniteRootStepField m ℕ X |
        (∑ r : Fin m, event.indicator (fun _ => (1 : ℝ)) (field r)) ≤
          (m : ℝ) * ((stepFieldLaw μ) event).toReal / 4} := by
    intro field hfield
    exact hfield.trans hthreshold
  have hcount' :
      (finiteRootStepFieldLaw μ m)
          {field : FiniteRootStepField m ℕ X |
            (∑ r : Fin m, event.indicator (fun _ => (1 : ℝ)) (field r)) ≤
              (m : ℝ) * ((stepFieldLaw μ) event).toReal / 4} ≤
        ENNReal.ofReal (Real.exp
          (-((m : ℝ) * ((stepFieldLaw μ) event).toReal / 4))) := by
    simpa only [event] using hcount
  calc
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          (∑ r : Fin m, event.indicator (fun _ => (1 : ℝ)) (field r)) ≤
            (m : ℝ) * pzMean.toReal / 4} ≤
      (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          (∑ r : Fin m, event.indicator (fun _ => (1 : ℝ)) (field r)) ≤
            (m : ℝ) * ((stepFieldLaw μ) event).toReal / 4} :=
      measure_mono hsubset
    _ ≤ ENNReal.ofReal (Real.exp
          (-((m : ℝ) * ((stepFieldLaw μ) event).toReal / 4))) := hcount'
    _ ≤ ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hmReal : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hpz_real_le_event hmReal]

end ProbabilityTheory.BranchingRandomWalk.Spine

end
