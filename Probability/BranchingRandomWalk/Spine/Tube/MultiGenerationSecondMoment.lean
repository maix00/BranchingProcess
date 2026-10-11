/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Tube.RightTailOneGeneration
import Probability.BranchingRandomWalk.Spine.Path.SecondMoment
import Probability.BranchingRandomWalk.Spine.Tube.IndependentRootCorridor

/-!
# Multi-generation pair decomposition for corridor path counts

The one-generation second-moment recursion keeps a diagonal child-subtree
square.  This file iterates that recursion to all generations.  For a
zero-one path test, the diagonal is exactly the first moment, and the
remainder consists of ordered pairs of distinct successful paths, split at
their most recent common ancestor.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- If a corridor has a finite first moment, then the recursive
most-recent-common-ancestor remainder agrees almost everywhere with the
direct ordered-pair count.  The finite first moment rules out an infinite
diagonal count, so it is legitimate to cancel that diagonal from the two
second-moment decompositions. -/
theorem pathGenerationOffDiagonalPairs_ae_eq_distinctAddressPairCount
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial terminalUpper : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminalUpper : ∀ history ∈ corridor,
      history ⟨n, Nat.lt_succ_self n⟩ ≤ terminalUpper) :
    pathGenerationOffDiagonalPairs φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial =ᵐ[stepFieldLaw μ]
      pathGenerationDistinctAddressPairCount φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial := by
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hF01 : ∀ history, F history = 0 ∨ F history = 1 := by
    intro history
    by_cases h : history ∈ corridor <;> simp [F, h]
  have hcount : Measurable (pathGeneration φ n F initial) :=
    pathGeneration_measurable (ι := ℕ) φ n hF initial
  letI : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    Spine.tiltedIncrementFieldLaw_isProbability φ μ hboundary
  have hcountIntegral := lintegral_pathGeneration_le_exp_mul_spineProbability
    φ μ hboundary n initial terminalUpper corridor hcorridor hterminalUpper
  have hcountIntegral_ne_top :
      (∫⁻ ω, pathGeneration φ n F initial ω ∂stepFieldLaw μ) ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top (tiltedIncrementFieldLaw φ μ) _))
    simpa [F] using hcountIntegral
  have hcount_ne_top : ∀ᵐ ω ∂stepFieldLaw μ,
      pathGeneration φ n F initial ω ≠ ∞ := by
    filter_upwards [ae_lt_top hcount hcountIntegral_ne_top] with ω hω
    exact hω.ne
  filter_upwards [hcount_ne_top] with ω hω
  have hrecursive := pathGeneration_sq_eq_self_add_offDiagonalPairs
    φ n F hF01 initial ω
  have hdirect := pathGeneration_sq_eq_self_add_distinctAddressPairCount
    φ n F hF01 initial ω
  apply (ENNReal.add_right_inj hω).mp
  calc
    pathGeneration φ n F initial ω + pathGenerationOffDiagonalPairs φ n F initial ω =
        (pathGeneration φ n F initial ω) ^ 2 := hrecursive.symm
    _ = pathGeneration φ n F initial ω +
        pathGenerationDistinctAddressPairCount φ n F initial ω := hdirect

/-- The expected recursive MRCA remainder can therefore be computed using
the measurable direct distinct-address pair count. -/
theorem lintegral_pathGenerationOffDiagonalPairs_eq_distinctAddressPairCount
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial terminalUpper : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminalUpper : ∀ history ∈ corridor,
      history ⟨n, Nat.lt_succ_self n⟩ ≤ terminalUpper) :
    (∫⁻ ω, pathGenerationOffDiagonalPairs φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω ∂stepFieldLaw μ) =
      (∫⁻ ω, pathGenerationDistinctAddressPairCount φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω ∂stepFieldLaw μ) := by
  exact lintegral_congr_ae
    (pathGenerationOffDiagonalPairs_ae_eq_distinctAddressPairCount
      φ μ hboundary n initial terminalUpper corridor hcorridor hterminalUpper)

/-- Pair-moment input for a long corridor can be passed directly to the
independent-root survival estimate. The only missing probabilistic input is
the paper's estimate on the expected number of ordered distinct successful
path pairs; this theorem turns that input into the full second moment and
then applies the existing Paley--Zygmund/root-count adapter. -/
theorem measure_finiteRootCorridorCount_le_quarter_spineLower_of_pairMoment
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial lower terminalUpper : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminalLower : ∀ history ∈ corridor,
      lower ≤ history ⟨n, Nat.lt_succ_self n⟩)
    (hterminalUpper : ∀ history ∈ corridor,
      history ⟨n, Nat.lt_succ_self n⟩ ≤ terminalUpper)
    (m : ℕ) (hm : 0 < m)
    (pairBound : ℝ≥0∞)
    (hpairBound : (∫⁻ ω,
      pathGenerationDistinctAddressPairCount φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
      ∂stepFieldLaw μ) ≤ pairBound)
    (hpairBound_top : pairBound ≠ ∞)
    (hspinePositive : 0 < (tiltedIncrementFieldLaw φ μ)
      {increment | RandomWalk.history n initial increment ∈ corridor}) :
    let spineEvent :=
      {increment | RandomWalk.history n initial increment ∈ corridor}
    let lowerMean := ENNReal.ofReal (Real.exp (lower - initial)) *
      (tiltedIncrementFieldLaw φ μ) spineEvent
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          (∑ r : Fin m,
            (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
              (fun _ => (1 : ℝ)) (field r)) ≤
            (m : ℝ) * (lowerMean ^ 2 /
              (ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
                (tiltedIncrementFieldLaw φ μ) spineEvent + pairBound)).toReal / 4} ≤
      ENNReal.ofReal (Real.exp
        (-((m : ℝ) * (lowerMean ^ 2 /
          (ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
            (tiltedIncrementFieldLaw φ μ) spineEvent + pairBound)).toReal / 4))) := by
  classical
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history n initial increment ∈ corridor}
  let upperMean : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
      (tiltedIncrementFieldLaw φ μ) spineEvent
  let second : ℝ≥0∞ := upperMean + pairBound
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hF01 : ∀ history, F history = 0 ∨ F history = 1 := by
    intro history
    by_cases h : history ∈ corridor <;> simp [F, h]
  have hmeanUpper :
      (∫⁻ ω, pathGeneration φ n F initial ω ∂stepFieldLaw μ) ≤ upperMean := by
    simpa [F, spineEvent, upperMean] using
      lintegral_pathGeneration_le_exp_mul_spineProbability
        φ μ hboundary n initial terminalUpper corridor hcorridor hterminalUpper
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    Spine.tiltedIncrementFieldLaw_isProbability φ μ hboundary
  letI : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) := htilted
  have hpairs := lintegral_pathGeneration_sq_eq_add_distinctAddressPairCount
    φ μ n F hF hF01 initial
  have hsecond :
      (∫⁻ ω, (pathGeneration φ n F initial ω) ^ 2 ∂stepFieldLaw μ) ≤ second := by
    calc
      _ = (∫⁻ ω, pathGeneration φ n F initial ω ∂stepFieldLaw μ) +
          (∫⁻ ω, pathGenerationDistinctAddressPairCount φ n F initial ω
            ∂stepFieldLaw μ) := hpairs
      _ ≤ upperMean + pairBound := add_le_add hmeanUpper hpairBound
      _ = second := rfl
  have hupperMean_top : upperMean ≠ ∞ := by
    dsimp [upperMean]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  have hsecond_top : second ≠ ∞ := by
    dsimp [second]
    exact ENNReal.add_ne_top.mpr ⟨hupperMean_top, hpairBound_top⟩
  have hupperMean_pos : 0 < upperMean := by
    dsimp [upperMean, spineEvent]
    exact ENNReal.mul_pos (by positivity) (ne_of_gt hspinePositive)
  have hsecond_pos : 0 < second := by
    dsimp [second]
    exact lt_of_lt_of_le hupperMean_pos le_self_add
  have hresult :=
    measure_finiteRootCorridorCount_le_quarter_spineLowerPZ
      φ μ hboundary n initial lower corridor hcorridor hterminalLower m hm
      second hsecond hsecond_pos hsecond_top
  simpa [spineEvent, F, upperMean, second] using hresult

end ProbabilityTheory.BranchingRandomWalk.Spine
