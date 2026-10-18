/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Tube.SecondMoment.OneGenerationTail
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.IndependentEventCount

/-!
# Independent-root lower bounds for tube populations

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.measure_finiteRootCorridorCount_le_quarter_pzMean`
  bounds the probability that `m` independent roots produce at most
  `m * mean² / (4 * second)` corridor paths by
  `exp (-m * mean² / (4 * second))`, when the one-root path count has mean
  `mean` and second moment at most `second`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGeneration_ge_exp_mul_spineProbability`
  gives `exp (lower - initial) * P_tilted(history_n ∈ corridor) ≤ E[pathCount]`
  when every corridor endpoint is at least `lower`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.measure_finiteRootCorridorCount_le_quarter_spineLowerPZ`
  combines that lower mean with a one-root second-moment bound in the same
  exponential root-count estimate.
* `ProbabilityTheory.BranchingRandomWalk.Spine.measure_finiteRootCorridor_allRootsAvoid_le_exp_of_spineLowerPZ`
  bounds the probability that every root misses the corridor by
  `exp (-m * pzMean / 4)`, with `pzMean` formed from the spine lower mean and
  the pair-moment input.

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

open ProbabilityTheory.RandomWalk

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

/-- A lower terminal endpoint converts the spine corridor probability into a
lower bound on the expected number of corridor paths. The identity is the
unweighted many-to-one formula; the exponential factor is bounded below on
the corridor by its terminal constraint. -/
theorem lintegral_pathGeneration_ge_exp_mul_spineProbability
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial lower : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminalLower : ∀ history ∈ corridor,
      lower ≤ history ⟨n, Nat.lt_succ_self n⟩) :
    ENNReal.ofReal (Real.exp (lower - initial)) *
        (tiltedIncrementFieldLaw φ μ)
          {increment | RandomWalk.history n initial increment ∈ corridor} ≤
      ∫⁻ ω, Spine.pathGeneration φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
        ∂stepFieldLaw μ := by
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history n initial increment ∈ corridor}
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  have hspineEvent : MeasurableSet spineEvent :=
    hcorridor.preimage (RandomWalk.history_measurable n initial)
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hterminalPath (increment : ℕ → ℝ)
      (hevent : increment ∈ spineEvent) :
      lower - initial ≤ AdditivePath.displacement n increment := by
    have h := hterminalLower (RandomWalk.history n initial increment)
      (by simpa [spineEvent] using hevent)
    rw [RandomWalk.history_last, AdditivePath.fromIncrements_apply] at h
    linarith
  calc
    ENNReal.ofReal (Real.exp (lower - initial)) *
        (tiltedIncrementFieldLaw φ μ) spineEvent =
      ∫⁻ increment, ENNReal.ofReal (Real.exp (lower - initial)) *
        spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment
        ∂tiltedIncrementFieldLaw φ μ := by
          rw [lintegral_const_mul _
            (measurable_const.indicator hspineEvent)]
          rw [lintegral_indicator_const hspineEvent]
          simp
    _ ≤ ∫⁻ increment,
        ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
          F (RandomWalk.history n initial increment)
        ∂tiltedIncrementFieldLaw φ μ := by
      apply lintegral_mono
      intro increment
      by_cases hevent : increment ∈ spineEvent
      · have hhistory : RandomWalk.history n initial increment ∈ corridor := by
          simpa [spineEvent] using hevent
        have hweight : ENNReal.ofReal (Real.exp (lower - initial)) ≤
            ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) :=
          ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.mpr (hterminalPath increment hevent))
        have hleft : spineEvent.indicator
            (fun _ => (1 : ℝ≥0∞)) increment = 1 := by
          simp [Set.indicator, hevent]
        have hright : F (RandomWalk.history n initial increment) = 1 := by
          change corridor.indicator (fun _ => (1 : ℝ≥0∞))
            (RandomWalk.history n initial increment) = 1
          rw [Set.indicator_of_mem hhistory]
        change ENNReal.ofReal (Real.exp (lower - initial)) *
            spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment ≤
          ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
            F (RandomWalk.history n initial increment)
        rw [hleft, hright]
        simpa using hweight
      · have hhistory : RandomWalk.history n initial increment ∉ corridor := by
          intro h
          exact hevent (by simpa [spineEvent] using h)
        have hleft : spineEvent.indicator
            (fun _ => (1 : ℝ≥0∞)) increment = 0 := by
          simp [Set.indicator, hevent]
        have hright : F (RandomWalk.history n initial increment) = 0 := by
          change corridor.indicator (fun _ => (1 : ℝ≥0∞))
            (RandomWalk.history n initial increment) = 0
          rw [Set.indicator_of_notMem hhistory]
        change ENNReal.ofReal (Real.exp (lower - initial)) *
            spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment ≤
          ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
            F (RandomWalk.history n initial increment)
        rw [hleft, hright]
        simp
    _ = ∫⁻ ω, Spine.pathGeneration φ n F initial ω
        ∂stepFieldLaw μ :=
      (Spine.pathManyToOneCore φ μ hboundary n hF initial).symm

/-- Independent initial roots inherit the long-corridor lower tail directly
from a spine lower bound on the first moment and an explicit one-root second
moment bound. The second-moment estimate remains an input for the separate
many-generation tube argument. -/
theorem measure_finiteRootCorridorCount_le_quarter_spineLowerPZ
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial lower : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminalLower : ∀ history ∈ corridor,
      lower ≤ history ⟨n, Nat.lt_succ_self n⟩)
    (m : ℕ) (hm : 0 < m) (second : ℝ≥0∞)
    (hsecond : (∫⁻ ω, (Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω) ^ 2
      ∂stepFieldLaw μ) ≤ second)
    (hsecond_pos : 0 < second) (hsecond_top : second ≠ ∞) :
    let spineEvent :=
      {increment | RandomWalk.history n initial increment ∈ corridor}
    let pzMean :=
      (ENNReal.ofReal (Real.exp (lower - initial)) *
        (tiltedIncrementFieldLaw φ μ) spineEvent) ^ 2 / second
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          (∑ r : Fin m,
            (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
              (fun _ => (1 : ℝ)) (field r)) ≤
            (m : ℝ) * pzMean.toReal / 4} ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := by
  classical
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history n initial increment ∈ corridor}
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  let mean : ℝ≥0∞ :=
    ∫⁻ ω, Spine.pathGeneration φ n F initial ω ∂stepFieldLaw μ
  let lowerMean : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (lower - initial)) *
      (tiltedIncrementFieldLaw φ μ) spineEvent
  let actualPZ : ℝ≥0∞ := mean ^ 2 / second
  let pzMean : ℝ≥0∞ := lowerMean ^ 2 / second
  have hmean : (∫⁻ ω, Spine.pathGeneration φ n F initial ω
      ∂stepFieldLaw μ) = mean := rfl
  have hmeanLower : lowerMean ≤ mean := by
    exact lintegral_pathGeneration_ge_exp_mul_spineProbability
      φ μ hboundary n initial lower corridor hcorridor hterminalLower
  have hsuccess : actualPZ ≤
      (stepFieldLaw μ) (hasPathHistoryIn (ι := ℕ) φ n initial corridor) := by
    dsimp [actualPZ, mean, F]
    exact measure_hasPathHistoryIn_ge_of_pathGeneration_moments
      φ μ n initial corridor hcorridor
      (∫⁻ ω, Spine.pathGeneration φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
        ∂stepFieldLaw μ) second rfl hsecond hsecond_pos hsecond_top
  have hprob_le_one :
      (stepFieldLaw μ) (hasPathHistoryIn (ι := ℕ) φ n initial corridor) ≤ 1 := by
    calc
      (stepFieldLaw μ) (hasPathHistoryIn (ι := ℕ) φ n initial corridor) ≤
          (stepFieldLaw μ) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hactualPZ_le_one : actualPZ ≤ 1 := hsuccess.trans hprob_le_one
  have hactualPZ_top : actualPZ ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hactualPZ_le_one ENNReal.one_lt_top)
  have hpzMean_le_actualPZ : pzMean ≤ actualPZ := by
    dsimp [pzMean, actualPZ]
    apply ENNReal.div_le_div_right
    exact pow_le_pow_left₀ bot_le hmeanLower 2
  have hpzReal_le_actual : pzMean.toReal ≤ actualPZ.toReal :=
    ENNReal.toReal_mono hactualPZ_top hpzMean_le_actualPZ
  have hcountActual :=
    measure_finiteRootCorridorCount_le_quarter_pzMean
      φ μ n initial corridor hcorridor m hm mean second hmean
      hsecond hsecond_pos hsecond_top
  have hcountActual' :
      (finiteRootStepFieldLaw μ m)
          {field : FiniteRootStepField m ℕ X |
            (∑ r : Fin m,
              (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
                (fun _ => (1 : ℝ)) (field r)) ≤
              (m : ℝ) * actualPZ.toReal / 4} ≤
        ENNReal.ofReal (Real.exp (-((m : ℝ) * actualPZ.toReal / 4))) := by
    simpa [actualPZ, mean, F] using hcountActual
  have hmReal : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hthreshold : (m : ℝ) * pzMean.toReal / 4 ≤
      (m : ℝ) * actualPZ.toReal / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hpzReal_le_actual hmReal]
  have hsubset :
      {field : FiniteRootStepField m ℕ X |
        (∑ r : Fin m,
          (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
            (fun _ => (1 : ℝ)) (field r)) ≤
          (m : ℝ) * pzMean.toReal / 4} ⊆
      {field : FiniteRootStepField m ℕ X |
        (∑ r : Fin m,
          (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
            (fun _ => (1 : ℝ)) (field r)) ≤
          (m : ℝ) * actualPZ.toReal / 4} := by
    intro field hfield
    exact hfield.trans hthreshold
  calc
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          (∑ r : Fin m,
            (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
              (fun _ => (1 : ℝ)) (field r)) ≤
            (m : ℝ) * pzMean.toReal / 4} ≤
      (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          (∑ r : Fin m,
            (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
              (fun _ => (1 : ℝ)) (field r)) ≤
            (m : ℝ) * actualPZ.toReal / 4} := measure_mono hsubset
    _ ≤ ENNReal.ofReal (Real.exp (-((m : ℝ) * actualPZ.toReal / 4))) :=
      hcountActual'
    _ ≤ ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hpzReal_le_actual hmReal]

/-- The same estimate bounds complete failure among all independent roots,
so its complement is a lower bound for survival to the corridor's terminal
generation. -/
theorem measure_finiteRootCorridor_allRootsAvoid_le_exp_of_spineLowerPZ
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial lower : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminalLower : ∀ history ∈ corridor,
      lower ≤ history ⟨n, Nat.lt_succ_self n⟩)
    (m : ℕ) (hm : 0 < m) (second : ℝ≥0∞)
    (hsecond : (∫⁻ ω, (Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω) ^ 2
      ∂stepFieldLaw μ) ≤ second)
    (hsecond_pos : 0 < second) (hsecond_top : second ≠ ∞) :
    let spineEvent :=
      {increment | RandomWalk.history n initial increment ∈ corridor}
    let pzMean :=
      (ENNReal.ofReal (Real.exp (lower - initial)) *
        (tiltedIncrementFieldLaw φ μ) spineEvent) ^ 2 / second
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m,
            field r ∉ hasPathHistoryIn (ι := ℕ) φ n initial corridor} ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := by
  classical
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history n initial increment ∈ corridor}
  let pzMean : ℝ≥0∞ :=
    (ENNReal.ofReal (Real.exp (lower - initial)) *
      (tiltedIncrementFieldLaw φ μ) spineEvent) ^ 2 / second
  have hcount := measure_finiteRootCorridorCount_le_quarter_spineLowerPZ
    φ μ hboundary n initial lower corridor hcorridor hterminalLower
    m hm second hsecond hsecond_pos hsecond_top
  have hsmall :
      (finiteRootStepFieldLaw μ m)
          {field : FiniteRootStepField m ℕ X |
            (∑ r : Fin m,
              (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
                (fun _ => (1 : ℝ)) (field r)) ≤
              (m : ℝ) * pzMean.toReal / 4} ≤
        ENNReal.ofReal (Real.exp (-((m : ℝ) * pzMean.toReal / 4))) := by
    simpa [spineEvent, pzMean] using hcount
  have hsubset :
      {field : FiniteRootStepField m ℕ X |
        ∀ r : Fin m,
          field r ∉ hasPathHistoryIn (ι := ℕ) φ n initial corridor} ⊆
      {field : FiniteRootStepField m ℕ X |
        (∑ r : Fin m,
          (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
            (fun _ => (1 : ℝ)) (field r)) ≤
          (m : ℝ) * pzMean.toReal / 4} := by
    intro field havoid
    have hzero : ∀ r : Fin m,
        (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
          (fun _ => (1 : ℝ)) (field r) = 0 := by
      intro r
      simp [Set.indicator, havoid r]
    have hcount_zero :
        (∑ r : Fin m,
          (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
            (fun _ => (1 : ℝ)) (field r)) = 0 := by
      simp [hzero]
    change (∑ r : Fin m,
        (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
          (fun _ => (1 : ℝ)) (field r)) ≤
      (m : ℝ) * pzMean.toReal / 4
    rw [hcount_zero]
    positivity
  exact (measure_mono hsubset).trans hsmall

end ProbabilityTheory.BranchingRandomWalk.Spine

end
