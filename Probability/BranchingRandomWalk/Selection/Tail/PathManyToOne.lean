/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Path.ManyToOne
import Probability.BranchingRandomWalk.Spine.RandomWalk

/-!
# One-root path events and the spine walk

This file records the many-to-one estimate for an arbitrary measurable
finite-history corridor. It is the first-moment input used when bounding the
number of particles in a killed branching random walk.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- There is a surviving particle at generation `n` whose ancestral history
belongs to `corridor`. -/
def hasPathHistoryIn {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (initial : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ)) : Set (StepField ι X) :=
  {ω | ∃ u : TreeNode ι, u.length = n ∧ surviveAlong ω [] u ∧
    Spine.pathHistory φ n initial ω u ∈ corridor}

theorem measurableSet_hasPathHistoryIn
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (initial : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ)) (hcorridor : MeasurableSet corridor) :
    MeasurableSet (hasPathHistoryIn (ι := ι) φ n initial corridor) := by
  rw [show hasPathHistoryIn (ι := ι) φ n initial corridor =
      ⋃ u : TreeNode ι,
        {ω | u.length = n ∧ surviveAlong ω [] u ∧
          Spine.pathHistory φ n initial ω u ∈ corridor} by
    ext ω
    simp [hasPathHistoryIn]]
  apply MeasurableSet.iUnion
  intro u
  have hlength : MeasurableSet {ω : StepField ι X | u.length = n} := by
    by_cases hu : u.length = n <;> simp [hu]
  have hsurvive : MeasurableSet {ω : StepField ι X | surviveAlong ω [] u} :=
    Spine.measurableSet_surviveAlong (X := X) [] u
  have hcorridor' : MeasurableSet
      {ω : StepField ι X | Spine.pathHistory φ n initial ω u ∈ corridor} :=
    hcorridor.preimage (Spine.pathHistory_measurable φ n initial u)
  rw [show {ω : StepField ι X | u.length = n ∧ surviveAlong ω [] u ∧
      Spine.pathHistory φ n initial ω u ∈ corridor} =
      {ω | u.length = n} ∩ {ω | surviveAlong ω [] u} ∩
        {ω | Spine.pathHistory φ n initial ω u ∈ corridor} by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]]
  exact (hlength.inter hsurvive).inter hcorridor'

/-- A one-root many-to-one estimate for an arbitrary finite-history event.
The terminal upper bound controls the reciprocal exponential weight in the
unweighted branching formula. -/
theorem measure_hasPathHistoryIn_le_exp_mul_spineProbability
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial terminalUpper : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
      (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n, Nat.lt_succ_self n⟩ ≤ terminalUpper) :
    (stepFieldLaw μ) (hasPathHistoryIn (ι := ι) φ n initial corridor) ≤
      ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
        (tiltedIncrementFieldLaw φ μ)
          {increment | ProbabilityTheory.RandomWalk.history n initial increment ∈
            corridor} := by
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ := corridor.indicator fun _ => 1
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | ProbabilityTheory.RandomWalk.history n initial increment ∈
      corridor}
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hspineEvent : MeasurableSet spineEvent :=
    hcorridor.preimage (ProbabilityTheory.RandomWalk.history_measurable n initial)
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    Spine.tiltedIncrementFieldLaw_isProbability φ μ hboundary
  let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) := htilted
  have hpathCount : ∀ ω : StepField ι X,
      (hasPathHistoryIn (ι := ι) φ n initial corridor).indicator
        (fun _ => (1 : ℝ≥0∞)) ω ≤ Spine.pathGeneration φ n F initial ω := by
    intro ω
    by_cases hω : ω ∈ hasPathHistoryIn (ι := ι) φ n initial corridor
    · obtain ⟨u, hu, hsurvive, hcorridorPath⟩ := hω
      have hterm : Spine.pathGenerationTerm φ n F initial u ω = 1 := by
        simp [Spine.pathGenerationTerm, Set.indicator, hu, hsurvive, F,
          hcorridorPath]
      have hleft :
          (hasPathHistoryIn (ι := ι) φ n initial corridor).indicator
            (fun _ => (1 : ℝ≥0∞)) ω = 1 := by
        have hmem : ω ∈ hasPathHistoryIn (ι := ι) φ n initial corridor :=
          ⟨u, hu, hsurvive, hcorridorPath⟩
        simp [Set.indicator, hmem]
      rw [hleft]
      rw [Spine.pathGeneration]
      calc
        (1 : ℝ≥0∞) = Spine.pathGenerationTerm φ n F initial u ω := hterm.symm
        _ ≤ ∑' p : TreeNode ι,
            Spine.pathGenerationTerm φ n F initial p ω :=
          ENNReal.le_tsum (f := fun p =>
            Spine.pathGenerationTerm φ n F initial p ω) u
    · simp [Set.indicator, hω]
  have hset : MeasurableSet
      (hasPathHistoryIn (ι := ι) φ n initial corridor) :=
    measurableSet_hasPathHistoryIn φ n initial corridor hcorridor
  have hterminalPath (increment : ℕ → ℝ)
      (hevent : increment ∈ spineEvent) :
      AdditivePath.displacement n increment ≤ terminalUpper - initial := by
    have h := hterminal (ProbabilityTheory.RandomWalk.history n initial increment)
      (by simpa [spineEvent] using hevent)
    rw [ProbabilityTheory.RandomWalk.history_last,
      AdditivePath.fromIncrements_apply] at h
    linarith
  calc
    (stepFieldLaw μ)
        (hasPathHistoryIn (ι := ι) φ n initial corridor) =
      ∫⁻ ω, (hasPathHistoryIn (ι := ι) φ n initial corridor).indicator
        (fun _ => (1 : ℝ≥0∞)) ω ∂stepFieldLaw μ := by
          rw [lintegral_indicator_const hset]
          simp
    _ ≤ ∫⁻ ω, Spine.pathGeneration φ n F initial ω ∂stepFieldLaw μ :=
      lintegral_mono hpathCount
    _ = ∫⁻ increment,
          ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
            F (ProbabilityTheory.RandomWalk.history n initial increment)
          ∂tiltedIncrementFieldLaw φ μ :=
      Spine.pathManyToOneCore φ μ hboundary n hF initial
    _ ≤ ∫⁻ increment,
          ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
            spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment
          ∂tiltedIncrementFieldLaw φ μ := by
      apply lintegral_mono
      intro increment
      change ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
          F (ProbabilityTheory.RandomWalk.history n initial increment) ≤
        ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
          spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment
      by_cases hevent : increment ∈ spineEvent
      · have hhistory : ProbabilityTheory.RandomWalk.history n initial increment ∈
            corridor := by
          simpa [spineEvent] using hevent
        have hexp : ENNReal.ofReal
              (Real.exp (AdditivePath.displacement n increment)) ≤
            ENNReal.ofReal (Real.exp (terminalUpper - initial)) :=
          ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.mpr (hterminalPath increment hevent))
        have htest : F (ProbabilityTheory.RandomWalk.history n initial increment) = 1 := by
          change corridor.indicator (fun _ => (1 : ℝ≥0∞))
            (ProbabilityTheory.RandomWalk.history n initial increment) = 1
          rw [Set.indicator_of_mem hhistory]
        have hindicator : spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment = 1 := by
          simp [Set.indicator, hevent]
        rw [htest, hindicator]
        simpa using hexp
      · have hhistory : ProbabilityTheory.RandomWalk.history n initial increment ∉
            corridor := by
          intro h
          exact hevent (by simpa [spineEvent] using h)
        have htest : F (ProbabilityTheory.RandomWalk.history n initial increment) = 0 := by
          change corridor.indicator (fun _ => (1 : ℝ≥0∞))
            (ProbabilityTheory.RandomWalk.history n initial increment) = 0
          rw [Set.indicator_of_notMem hhistory]
        have hindicator : spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment = 0 := by
          simp [Set.indicator, hevent]
        rw [htest, hindicator]
        simp
    _ = ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
          (tiltedIncrementFieldLaw φ μ) spineEvent := by
      rw [lintegral_const_mul _ (measurable_const.indicator hspineEvent)]
      rw [lintegral_indicator_const hspineEvent]
      simp

end ProbabilityTheory.BranchingRandomWalk.Selection.Tail
