/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Probability.BranchingRandomWalk.Spine.Path.SecondMoment.Basic
public import Probability.BranchingRandomWalk.Spine.RandomWalk.IncrementProcess
import all Probability.BranchingRandomWalk.Spine.Tube.MRCA.Lemmas.ChildPairBound

/-!
# Cross-child continuation bounds for the root-split MRCA term

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Spine.pathGenerationChildMean_offDiagonal_le_crossPotentialWeight`:
  if all shifted-spine corridor probabilities on a first-step window are at
  most $q$, then the ordered sum of distinct-child continuation means is at
  most $(e^{u-x}q)^2$ times `crossPotentialWeight φ (-1) ξ`.
- `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGenerationChildMean_offDiagonal_le_crossPotentialWeight`:
  integrating the same estimate over the root-step law bounds the expected
  ordered off-diagonal contribution by $(e^{u-x}q)^2$ times the integral of
  `crossPotentialWeight φ (-1)`.

These are the cross-child estimates used for the root-split term in Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (master's thesis, Fudan University, 2026), Chapter 4, Lemma 4.5.
The conditional-observable and t-sum calculations supporting them are in the
neighboring `Lemmas/ChildPairBound.lean` module.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The root's ordered off-diagonal continuation terms are controlled by the
cross-child exponential weight once the shifted spine corridor probabilities
have a uniform bound. This is the fixed-ancestor estimate in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(master's thesis, Fudan University, 2026), Chapter 4, Lemma 4.5. -/
theorem pathGenerationChildMean_offDiagonal_le_crossPotentialWeight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ)
    (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q)
    (ξ : Step ℕ X) :
    (∑' i, ∑' j, if i ≠ j then
      (∫⁻ η, pathGenerationChildObservable φ n
        (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
        ∂offspringFieldLaw μ) *
      (∫⁻ ζ, pathGenerationChildObservable φ n
        (corridor.indicator fun _ => (1 : ℝ≥0∞)) x j ξ ζ
        ∂offspringFieldLaw μ)
      else 0) ≤
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          crossPotentialWeight φ (-1) ξ := by
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (terminalUpper - x)) * q
  let m : ℕ → ℝ≥0∞ := fun i =>
    ∫⁻ η, pathGenerationChildObservable φ n
      (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
      ∂offspringFieldLaw μ
  have hm (i : ℕ) : m i ≤ K * realizedPotentialWeight φ (-1) ξ i := by
    simpa [m, K] using
      lintegral_pathGenerationChildObservable_le_firstWindowProbability_mul_weight
        φ μ hboundary n x terminalUpper corridor hcorridor hterminal
        window q hfirst hprob i ξ
  simpa [K, m] using
    ennreal_tsum_offDiagonal_mul_le_crossPotentialWeight_of_childMomentBound
      φ ξ K m hm

/-- Integrating the fixed-ancestor off-diagonal estimate over the root step
gives the expected cross-child contribution in the MRCA decomposition. -/
theorem lintegral_pathGenerationChildMean_offDiagonal_le_crossPotentialWeight
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ)
    (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q) :
    (∑' i, ∑' j, if i ≠ j then
      ∫⁻ ξ, (∫⁻ η, pathGenerationChildObservable φ n
        (corridor.indicator fun _ => (1 : ℝ≥0∞)) x i ξ η
        ∂offspringFieldLaw μ) *
        (∫⁻ ζ, pathGenerationChildObservable φ n
          (corridor.indicator fun _ => (1 : ℝ≥0∞)) x j ξ ζ
          ∂offspringFieldLaw μ) ∂μ
      else 0) ≤
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) := by
  let F : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    corridor.indicator fun _ => (1 : ℝ≥0∞)
  let childMean (i : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    ∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
      ∂offspringFieldLaw μ
  let offTerm (i j : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    if i ≠ j then childMean i ξ * childMean j ξ else 0
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hchildMean (i : ℕ) : Measurable (childMean i) := by
    apply Measurable.lintegral_prod_right
    simpa [F] using pathGenerationChildObservable_measurable
      φ n (corridor.indicator fun _ => (1 : ℝ≥0∞))
      (measurable_const.indicator hcorridor) x i
  have hoffTerm (i j : ℕ) : Measurable (offTerm i j) := by
    by_cases hij : i ≠ j
    · simp only [offTerm, ite_eq_left hij]
      exact (hchildMean i).mul (hchildMean j)
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [offTerm, hEq]
  have hoffInner (i : ℕ) :
      Measurable (fun ξ => ∑' j, offTerm i j ξ) := by
    apply Measurable.tsum
    intro j
    exact hoffTerm i j
  have hoffSum : Measurable (fun ξ => ∑' i, ∑' j, offTerm i j ξ) := by
    apply Measurable.tsum
    intro i
    exact hoffInner i
  have hoffInnerIntegral (i : ℕ) :
      (∫⁻ ξ, ∑' j, offTerm i j ξ ∂μ) =
        ∑' j, ∫⁻ ξ, offTerm i j ξ ∂μ := by
    rw [lintegral_tsum]
    intro j
    exact (hoffTerm i j).aemeasurable
  have hoffIntegral :
      (∫⁻ ξ, ∑' i, ∑' j, offTerm i j ξ ∂μ) =
        ∑' i, ∑' j, ∫⁻ ξ, offTerm i j ξ ∂μ := by
    rw [lintegral_tsum]
    · apply tsum_congr
      intro i
      exact hoffInnerIntegral i
    · intro i
      exact (hoffInner i).aemeasurable
  have hoffTermIntegral (i j : ℕ) :
      (∫⁻ ξ, offTerm i j ξ ∂μ) =
        if i ≠ j then ∫⁻ ξ, childMean i ξ * childMean j ξ ∂μ else 0 := by
    by_cases hij : i ≠ j
    · simp [offTerm, hij]
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [offTerm, hEq]
  have hsum :
      (∑' i, ∑' j, if i ≠ j then
        ∫⁻ ξ, childMean i ξ * childMean j ξ ∂μ else 0) =
        ∫⁻ ξ, ∑' i, ∑' j, offTerm i j ξ ∂μ := by
    calc
      _ = ∑' i, ∑' j, ∫⁻ ξ, offTerm i j ξ ∂μ := by
        apply tsum_congr
        intro i
        apply tsum_congr
        intro j
        rw [hoffTermIntegral]
      _ = ∫⁻ ξ, ∑' i, ∑' j, offTerm i j ξ ∂μ := hoffIntegral.symm
  have hpointwise (ξ : Step ℕ X) :
      (∑' i, ∑' j, offTerm i j ξ) ≤
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          crossPotentialWeight φ (-1) ξ := by
    simpa [offTerm, childMean, F] using
      pathGenerationChildMean_offDiagonal_le_crossPotentialWeight
        φ μ hboundary n x terminalUpper corridor hcorridor hterminal
        window q hfirst hprob ξ
  have hbound := calc
      (∑' i, ∑' j, if i ≠ j then
        ∫⁻ ξ, childMean i ξ * childMean j ξ ∂μ else 0) ≤
          ∫⁻ ξ, (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
            crossPotentialWeight φ (-1) ξ ∂μ := by
        rw [hsum]
        exact lintegral_mono hpointwise
      _ = (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          (∫⁻ ξ, crossPotentialWeight φ (-1) ξ ∂μ) := by
        rw [lintegral_const_mul _ (crossPotentialWeight_measurable φ (-1))]
  simpa [F, childMean] using hbound

end ProbabilityTheory.BranchingRandomWalk.Spine
