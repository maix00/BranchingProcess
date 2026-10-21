/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Tube.SecondMoment.OneGenerationTail
import Probability.BranchingRandomWalk.Assumptions.CrossWeight
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# MRCA pair contributions in affine tubes

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeRootMRCAPairMean`
  is `∑' i, ∑' j, if i ≠ j then ∫⁻ ξ, cᵢ(ξ) * cⱼ(ξ) ∂μ else 0`, where
  `cᵢ(ξ) = ∫⁻ η, pathGenerationChildObservable φ n F initial i ξ η
  ∂stepFieldLaw μ` and `F` is the indicator of
  `affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper`.
  Its integral
  representations are
  `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeRootMRCAPairMean_eq_lintegral`
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeRootMRCAPairMean_eq_lintegral_pathGenerationMRCAContribution`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.pathGenerationChildMeanOffDiagonal_le_of_shiftedProbability`,
  `ProbabilityTheory.BranchingRandomWalk.Spine.pathGenerationChildMeanOffDiagonal_normalized_le_of_shiftedProbability`,
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.pathGenerationChildMeanOffDiagonal_normalized_le_of_uniformShiftedProbability`
  bound `pathGenerationChildMeanOffDiagonal φ μ n
  (corridor.indicator (fun _ => 1)) x ξ` by
  `(exp (terminalUpper - x) * q)^2 * crossChildWeight φ ξ`; the latter two
  state the normalized inequality
  `ENNReal.ofReal (exp (2 * x)) * pathGenerationChildMeanOffDiagonal φ μ n
  (corridor.indicator (fun _ => 1)) x ξ ≤ ENNReal.ofReal
  (exp (2 * terminalUpper)) * q^2 * crossChildWeight φ ξ`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_affineTube_pathGeneration_succ_sq_eq_diagonal_add_rootMRCAPairMean`
  decomposes the next-generation second moment. With
  `F := (affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper).indicator
  (fun _ => (1 : ℝ≥0∞))`, its identity is
  `∫⁻ ω, (pathGeneration φ (n + 1) F initial ω)^2 =
   ∑' i ∫⁻ ξ ∫⁻ η (pathGenerationChildObservable φ n F initial i ξ η)^2 +
   affineTubeRootMRCAPairMean φ μ n initial lower drift width endpointUpper`.
  The child observable is integrated under `stepFieldLaw μ`, the outer child
  mark under `μ`, and the squared path count under `stepFieldLaw μ`.
  `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeRootMRCAPairMean_le_of_segmentProbability`
  bounds that root-split term by the finite cross-child moment and the uniform
  shifted-segment probability.
* `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeRootMRCAPairMean_le_of_mogulskiiSegmentBound`
  applies the Chapter 4, Lemma 4.2 segment estimate in Wang Yiyang,
  *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
  (master's thesis, Fudan University, 2026). The absorption results
  `ProbabilityTheory.BranchingRandomWalk.Spine.exists_width0_crossChildMoment_le_exp_rpow`
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeRootMRCAPairMean_le_of_mogulskiiSegmentBound_of_crossAbsorption`
  absorb the finite cross-child moment into a large-width exponential factor.
* `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeRootMRCAPairMean_ne_top_of_segmentProbability`
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeRootMRCAPairMean_ne_top_of_mogulskiiSegmentBound`
  establish finiteness of the root-split contribution under the corresponding
  segment-probability hypotheses.
* `ProbabilityTheory.BranchingRandomWalk.Spine.weightedPrefixCrossChildWeightSum`
  is `∑' u, weightedPathGenerationTerm φ n F x u ω * crossChildWeight φ (ω u)`;
  `ProbabilityTheory.BranchingRandomWalk.Spine.weightedPrefixSquareCrossChildWeightSum`
  is `∑' u, weightedPathGenerationTerm φ n F x u ω *
  ENNReal.ofReal (exp (-pathPotential φ ω u)) * crossChildWeight φ (ω u)`, and
  `ProbabilityTheory.BranchingRandomWalk.Spine.weightedPrefixSquareObservableSum`
  is `∑' u, weightedPathGenerationTerm φ n F x u ω *
  ENNReal.ofReal (exp (-pathPotential φ ω u)) * g (ω u)` for an arbitrary
  offspring observable `g`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_generationPrefixParameterizedObservableSum_le`
  bounds a position-dependent frontier observable by a uniform bound times
  the generation-prefix integral. Its child-pair form is
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_generationPrefixChildPairObservable_le`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_weightedPrefixSquareObservableSum_eq_mul`
  factors the expected square-weighted prefix observable. The corresponding
  domination is
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_weightedPrefixSquareObservableSum_le_of_crossChildBound`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_weightedPrefixSquareCrossChildWeightSum_eq_crossMoment_mul`
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_weightedPrefixCrossChildWeightSum_eq_crossMoment_mul`
  factor the expected prefix/cross-child sum into the finite cross-child
  moment and its prefix integral. With a corridor indicator this becomes
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_weightedPrefixCrossChildWeightSum_indicator_eq_crossMoment_mul_spineProbability`;
  the corresponding upper bounds are
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_weightedPrefixCrossChildWeightSum_indicator_le_crossMoment_mul`
  and
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_weightedPrefixSquareCrossChildWeightSum_indicator_le`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_weightedPrefixSquareMass_indicator_le_spineProbability`
  bounds the square-weighted corridor-prefix mass by its tilted-spine
  probability.
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_weightedPrefixContinuationPair_indicator_le`
  factors a fixed-depth MRCA contribution into this prefix mass and a
  continuation-pair bound; its affine-tube drawdown specialization is
  `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_affineCorridorPrefixContinuationPair_indicator_le_of_drawdown`.
* `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeMRCAPairContribution`
  is the integral over `ω` of
  `∑' u, pathGenerationTerm φ m prefix initial u ω *
  pathGenerationChildMeanOffDiagonal φ μ n continuation
  (initial + pathPotential φ ω u) (ω u)`, where `prefix` is the indicator of
  `affineCorridorPrefix m lower drift width` and `continuation` is the
  indicator of
  `affineCorridorHistoryEndpointCutoff n (lower + drift * m) drift width endpointUpper`;
  the outer integral is under `stepFieldLaw μ`.
  The normalization identity
  `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeMRCAPairContribution_eq_normalized`
  identifies it with the square-weighted continuation expression;
  `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeMRCAPairContribution_le_of_drawdown`
  bounds each positive-depth contribution, and
  `ProbabilityTheory.BranchingRandomWalk.Spine.sum_affineTubeMRCAPairContribution_le_of_drawdown`
  sums these bounds over all possible MRCA generations.

This module specializes the branching-random-walk path-level MRCA
decomposition to affine tubes. Each positive-depth term factors into an
ancestral-prefix mass and a continuation-pair estimate. The modules
`ActualContribution`, `PairBound`, and `SecondMoment` identify and assemble
these terms into the corridor-count second-moment bound.
-/

open MeasureTheory
open Filter
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.RandomWalk

/-- The expected ordered pair contribution whose two paths split at the
root. Each child continuation is averaged over its descendant field, and the
two conditional means are multiplied before averaging the root step. -/
noncomputable def affineTubeRootMRCAPairMean
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) (n : ℕ)
    (initial lower drift width endpointUpper : ℝ) : ℝ≥0∞ := by
  let corridor :=
    affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper
  let F : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  exact ∑' i, ∑' j, if i ≠ j then
    ∫⁻ ξ,
      (∫⁻ η, pathGenerationChildObservable φ n F initial i ξ η
        ∂stepFieldLaw μ) *
      (∫⁻ ζ, pathGenerationChildObservable φ n F initial j ξ ζ
        ∂stepFieldLaw μ) ∂μ
    else 0

/-- The root MRCA mean is the integral of its conditional off-diagonal
continuation observable. This form is also used at later ancestors, where the
starting position is measurable with respect to the prefix. -/
theorem affineTubeRootMRCAPairMean_eq_lintegral
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (initial lower drift width endpointUpper : ℝ) :
    affineTubeRootMRCAPairMean φ μ n initial lower drift width endpointUpper =
      ∫⁻ ξ, pathGenerationChildMeanOffDiagonal φ μ n
        ((affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper).indicator
          (fun _ => (1 : ℝ≥0∞))) initial ξ ∂μ := by
  classical
  let corridor :=
    affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper
  let F : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  let childMean (i : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    ∫⁻ η, pathGenerationChildObservable φ n F initial i ξ η
      ∂stepFieldLaw μ
  let offTerm (i j : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    if i ≠ j then childMean i ξ * childMean j ξ else 0
  have hF : Measurable F :=
    measurable_const.indicator
      (measurableSet_affineCorridorHistoryEndpointCutoff
        n lower drift width endpointUpper)
  have hchildMean (i : ℕ) : Measurable (childMean i) := by
    apply Measurable.lintegral_prod_right
    simpa [F, childMean, corridor] using
      pathGenerationChildObservable_measurable φ n F hF initial i
  have hoffTerm (i j : ℕ) : Measurable (offTerm i j) := by
    by_cases hij : i ≠ j
    · simp only [offTerm, if_pos hij]
      exact (hchildMean i).mul (hchildMean j)
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [offTerm, hEq]
  have hoffInner (i : ℕ) : Measurable (fun ξ => ∑' j, offTerm i j ξ) := by
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
  simpa [affineTubeRootMRCAPairMean, pathGenerationChildMeanOffDiagonal,
    corridor, F, childMean, offTerm] using hsum

/-- The affine-tube root-split pair mean is exactly the expected depth-zero
MRCA contribution in the generic BRW path decomposition. -/
theorem affineTubeRootMRCAPairMean_eq_lintegral_pathGenerationMRCAContribution
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (initial lower drift width endpointUpper : ℝ) :
    affineTubeRootMRCAPairMean φ μ n initial lower drift width endpointUpper =
      (∫⁻ ω, pathGenerationMRCAContribution φ 0 (n + 1)
        ((affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper).indicator
          (fun _ => (1 : ℝ≥0∞))) initial ω ∂stepFieldLaw μ) := by
  let F : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    (affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper).indicator
      (fun _ => (1 : ℝ≥0∞))
  have hF : Measurable F :=
    measurable_const.indicator
      (measurableSet_affineCorridorHistoryEndpointCutoff
        n lower drift width endpointUpper)
  calc
    affineTubeRootMRCAPairMean φ μ n initial lower drift width endpointUpper =
        ∫⁻ ξ, pathGenerationChildMeanOffDiagonal φ μ n F initial ξ ∂μ := by
      simpa [F] using
        affineTubeRootMRCAPairMean_eq_lintegral
          φ μ n initial lower drift width endpointUpper
    _ = ∫⁻ ω, pathGenerationMRCAContribution φ 0 (n + 1) F initial ω
          ∂stepFieldLaw μ :=
      (lintegral_pathGenerationMRCAContribution_zero_eq_childMeanOffDiagonal
        φ μ n F hF initial).symm
    _ = _ := by rfl

/-- The pointwise continuation-pair observable is bounded by the
cross-child weight under the shifted-spine probability estimate used in the
one-ancestor second-moment bound. -/
theorem pathGenerationChildMeanOffDiagonal_le_of_shiftedProbability
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ) (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q) :
    ∀ ξ, pathGenerationChildMeanOffDiagonal φ μ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ξ ≤
        (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
          crossChildWeight φ ξ := by
  intro ξ
  simpa [pathGenerationChildMeanOffDiagonal] using
    pathGenerationChildMean_offDiagonal_le_crossChildWeight
      φ μ hboundary n x terminalUpper corridor hcorridor hterminal
      window q hfirst hprob ξ

/-- After extracting the endpoint factor `exp(-2 * x)`, the continuation
pair observable has a bound uniform in the ancestor position. -/
theorem pathGenerationChildMeanOffDiagonal_normalized_le_of_shiftedProbability
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (x terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ) (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q) :
    ∀ ξ, ENNReal.ofReal (Real.exp (2 * x)) *
        pathGenerationChildMeanOffDiagonal φ μ n
          (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ξ ≤
      ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2 *
        crossChildWeight φ ξ := by
  intro ξ
  have hraw := pathGenerationChildMeanOffDiagonal_le_of_shiftedProbability
    φ μ hboundary n x terminalUpper corridor hcorridor hterminal window q
    hfirst hprob ξ
  have hconstant :
      ENNReal.ofReal (Real.exp (2 * x)) *
          (ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 =
        ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2 := by
    have hexp :
        Real.exp (2 * x) *
            (Real.exp (terminalUpper - x) * Real.exp (terminalUpper - x)) =
          Real.exp (2 * terminalUpper) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = (ENNReal.ofReal (Real.exp (2 * x)) *
            ENNReal.ofReal (Real.exp (terminalUpper - x)) *
            ENNReal.ofReal (Real.exp (terminalUpper - x))) * q ^ 2 := by
          simp only [pow_two]
          ac_rfl
      _ = ENNReal.ofReal
            (Real.exp (2 * x) *
              (Real.exp (terminalUpper - x) *
                Real.exp (terminalUpper - x))) * q ^ 2 := by
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
          rw [← ENNReal.ofReal_mul
            (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))]
          congr 2
          ring
      _ = ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2 := by
          rw [hexp]
  calc
    ENNReal.ofReal (Real.exp (2 * x)) *
        pathGenerationChildMeanOffDiagonal φ μ n
          (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ξ ≤
        ENNReal.ofReal (Real.exp (2 * x)) *
          ((ENNReal.ofReal (Real.exp (terminalUpper - x)) * q) ^ 2 *
            crossChildWeight φ ξ) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2 *
          crossChildWeight φ ξ := by
      rw [← mul_assoc, hconstant]

/-- The normalized continuation-pair bound holds uniformly over every
ancestor position when the shifted-spine estimate is uniform in that
position. -/
theorem pathGenerationChildMeanOffDiagonal_normalized_le_of_uniformShiftedProbability
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (terminalUpper : ℝ)
    (corridor : Set (Fin (n + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ) (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ x y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            corridor} ≤ q) :
    ∀ x ξ, ENNReal.ofReal (Real.exp (2 * x)) *
        pathGenerationChildMeanOffDiagonal φ μ n
          (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ξ ≤
      ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2 *
        crossChildWeight φ ξ := by
  intro x ξ
  exact pathGenerationChildMeanOffDiagonal_normalized_le_of_shiftedProbability
    φ μ hboundary n x terminalUpper corridor hcorridor hterminal window q
    hfirst (fun y hy => hprob x y hy) ξ

/-- The root-split MRCA pair contribution is the off-diagonal term in the
one-step second moment recursion for the affine tube count. The other term
keeps both paths in the same first-generation subtree and contains every
later ancestor-generation contribution. -/
theorem lintegral_affineTube_pathGeneration_succ_sq_eq_diagonal_add_rootMRCAPairMean
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (initial lower drift width endpointUpper : ℝ) :
    (∫⁻ ω, (Spine.pathGeneration φ (n + 1)
      ((affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper).indicator
        (fun _ => (1 : ℝ≥0∞))) initial ω) ^ 2 ∂stepFieldLaw μ) =
      (∑' i, ∫⁻ ξ, ∫⁻ η,
        (pathGenerationChildObservable φ n
          ((affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper).indicator
            (fun _ => (1 : ℝ≥0∞))) initial i ξ η) ^ 2
          ∂stepFieldLaw μ ∂μ) +
        affineTubeRootMRCAPairMean φ μ n initial lower drift width endpointUpper := by
  let corridor :=
    affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper
  let F : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  have hF : Measurable F :=
    measurable_const.indicator
      (measurableSet_affineCorridorHistoryEndpointCutoff
        n lower drift width endpointUpper)
  simpa [affineTubeRootMRCAPairMean, corridor, F] using
    (lintegral_pathGeneration_succ_sq_eq_childPairRecursion
      φ μ n F hF initial)

/-- The root-split MRCA pair contribution is bounded by the finite
cross-child moment once the shifted continuation probability has a uniform
upper bound. -/
theorem affineTubeRootMRCAPairMean_le_of_segmentProbability
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial lower drift width endpointUpper : ℝ)
    (hdrift : 0 ≤ drift) (q : ℝ≥0∞)
    (hsegment : (tiltedIncrementFieldLaw φ μ)
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ))) ≤ q) :
    affineTubeRootMRCAPairMean φ μ n initial lower drift width endpointUpper ≤
      (ENNReal.ofReal (Real.exp (endpointUpper - initial)) * q) ^ 2 *
        (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
  let corridor :=
    affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper
  let window := affineCorridorFirstWindow lower drift width
  have hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window := by
    intro history hh
    exact affineCorridorHistoryEndpointCutoff_firstWindow
      n lower drift width endpointUpper history hh
  have hterminal : ∀ history ∈ corridor,
      history ⟨n + 1, by omega⟩ ≤ endpointUpper := by
    intro history hh
    exact affineCorridorHistoryEndpointCutoff_terminalUpper
      n lower drift width endpointUpper history hh
  have hprob : ∀ y : ℝ, initial + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory initial
          (ProbabilityTheory.RandomWalk.history n (initial + y) increment) ∈
            corridor} ≤ q := by
    intro y hy
    exact tiltedIncrementFieldLaw_affineCorridorHistoryEndpointCutoff_le_drawdown
      φ μ n initial lower drift width endpointUpper y hdrift q hsegment
  simpa [affineTubeRootMRCAPairMean, corridor] using
    (lintegral_pathGenerationChildMean_offDiagonal_le_crossChildWeight
      φ μ hboundary n initial endpointUpper corridor
      (measurableSet_affineCorridorHistoryEndpointCutoff
        n lower drift width endpointUpper)
      hterminal window q hfirst hprob)

/-- The segment-probability estimate in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), Chapter 4, Lemma 4.2, gives an explicit bound for the
root-split MRCA pair contribution. The drawdown event in `hsegment` follows
from the affine tube geometry. -/
theorem affineTubeRootMRCAPairMean_le_of_mogulskiiSegmentBound
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial lower drift width endpointUpper v d : ℝ)
    (hdrift : 0 ≤ drift)
    (hsegment : (tiltedIncrementFieldLaw φ μ)
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ))) ≤
      ENNReal.ofReal (Real.exp (width ^ v - d * (n : ℝ) / width ^ 2))) :
    affineTubeRootMRCAPairMean φ μ n initial lower drift width endpointUpper ≤
      (ENNReal.ofReal (Real.exp (endpointUpper - initial)) *
        ENNReal.ofReal (Real.exp (width ^ v - d * (n : ℝ) / width ^ 2))) ^ 2 *
        (∫⁻ ξ, crossChildWeight φ ξ ∂μ) :=
  affineTubeRootMRCAPairMean_le_of_segmentProbability
    φ μ hboundary n initial lower drift width endpointUpper hdrift
    (ENNReal.ofReal (Real.exp (width ^ v - d * (n : ℝ) / width ^ 2)))
    hsegment

/-- Finiteness of the cross-child moment lets the fixed constant be
absorbed into `exp(width ^ v)` for all sufficiently large tube widths. This
is the only use of the large-width threshold in the root-split contribution
estimate. -/
theorem exists_width0_crossChildMoment_le_exp_rpow
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X))
    (hcross : HasFiniteCrossWeight φ μ) (v : ℝ) (hv : 0 < v) :
    ∃ width0 : ℝ, ∀ width : ℝ, width0 ≤ width →
      (∫⁻ ξ, crossChildWeight φ ξ ∂μ) ≤
        ENNReal.ofReal (Real.exp (width ^ v)) := by
  let c : ℝ≥0∞ := ∫⁻ ξ, crossChildWeight φ ξ ∂μ
  have hc : c ≠ ∞ := hcross
  have hexp : Tendsto (fun width : ℝ => Real.exp (width ^ v)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (_root_.tendsto_rpow_atTop hv)
  have heventually : ∀ᶠ width : ℝ in atTop,
      c.toReal ≤ Real.exp (width ^ v) :=
    hexp.eventually (eventually_ge_atTop c.toReal)
  obtain ⟨width0, hwidth0⟩ := Filter.eventually_atTop.1 heventually
  refine ⟨width0, ?_⟩
  intro width hwidth
  have hreal : c.toReal ≤ Real.exp (width ^ v) := hwidth0 width hwidth
  change c ≤ ENNReal.ofReal (Real.exp (width ^ v))
  rw [← ENNReal.ofReal_toReal hc]
  exact ENNReal.ofReal_le_ofReal hreal

/-- After absorbing the finite cross-child moment into the large-width
factor, the root-split contribution has the same `3 * width^v` loss as the
corresponding single summand in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), Chapter 4, Lemma 4.5. Contributions from later ancestor
generations still require the generation-`m` prefix estimate. -/
theorem affineTubeRootMRCAPairMean_le_of_mogulskiiSegmentBound_of_crossAbsorption
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial lower drift width endpointUpper v d : ℝ)
    (hdrift : 0 ≤ drift)
    (hsegment : (tiltedIncrementFieldLaw φ μ)
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ))) ≤
      ENNReal.ofReal (Real.exp (width ^ v - d * (n : ℝ) / width ^ 2)))
    (hcrossAbsorb : (∫⁻ ξ, crossChildWeight φ ξ ∂μ) ≤
      ENNReal.ofReal (Real.exp (width ^ v))) :
    affineTubeRootMRCAPairMean φ μ n initial lower drift width endpointUpper ≤
      (ENNReal.ofReal (Real.exp (endpointUpper - initial)) *
        ENNReal.ofReal (Real.exp (width ^ v - d * (n : ℝ) / width ^ 2))) ^ 2 *
        ENNReal.ofReal (Real.exp (width ^ v)) := by
  calc
    affineTubeRootMRCAPairMean φ μ n initial lower drift width endpointUpper ≤
        (ENNReal.ofReal (Real.exp (endpointUpper - initial)) *
          ENNReal.ofReal (Real.exp (width ^ v - d * (n : ℝ) / width ^ 2))) ^ 2 *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) :=
      affineTubeRootMRCAPairMean_le_of_mogulskiiSegmentBound
        φ μ hboundary n initial lower drift width endpointUpper v d hdrift hsegment
    _ ≤
        (ENNReal.ofReal (Real.exp (endpointUpper - initial)) *
          ENNReal.ofReal (Real.exp (width ^ v - d * (n : ℝ) / width ^ 2))) ^ 2 *
          ENNReal.ofReal (Real.exp (width ^ v)) := by
      gcongr

/-- In particular, the root-split MRCA pair contribution is finite under the
finite cross-child condition whenever the segment-probability bound
is finite. This is a derived finiteness result, not a pair-moment assumption. -/
theorem affineTubeRootMRCAPairMean_ne_top_of_segmentProbability
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (hcross : HasFiniteCrossWeight φ μ)
    (n : ℕ) (initial lower drift width endpointUpper : ℝ)
    (hdrift : 0 ≤ drift) (q : ℝ≥0∞) (hq : q ≠ ∞)
    (hsegment : (tiltedIncrementFieldLaw φ μ)
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ))) ≤ q) :
    affineTubeRootMRCAPairMean φ μ n initial lower drift width endpointUpper ≠ ∞ := by
  have hbound := affineTubeRootMRCAPairMean_le_of_segmentProbability
    φ μ hboundary n initial lower drift width endpointUpper hdrift q hsegment
  have hfactor : ENNReal.ofReal (Real.exp (endpointUpper - initial)) * q ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq
  have hsquare :
      (ENNReal.ofReal (Real.exp (endpointUpper - initial)) * q) ^ 2 ≠ ∞ := by
    rw [pow_two]
    exact ENNReal.mul_ne_top hfactor hfactor
  have hcross : (∫⁻ ξ, crossChildWeight φ ξ ∂μ) ≠ ∞ := hcross
  have hright :
      (ENNReal.ofReal (Real.exp (endpointUpper - initial)) * q) ^ 2 *
        (∫⁻ ξ, crossChildWeight φ ξ ∂μ) ≠ ∞ :=
    ENNReal.mul_ne_top hsquare hcross
  exact ne_of_lt (lt_of_le_of_lt hbound (lt_top_iff_ne_top.mpr hright))

/-- Under the finite cross-weight condition, the explicit
Mogulskii-controlled root-split contribution is finite. -/
theorem affineTubeRootMRCAPairMean_ne_top_of_mogulskiiSegmentBound
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (hcross : HasFiniteCrossWeight φ μ)
    (n : ℕ) (initial lower drift width endpointUpper v d : ℝ)
    (hdrift : 0 ≤ drift)
    (hsegment : (tiltedIncrementFieldLaw φ μ)
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ))) ≤
      ENNReal.ofReal (Real.exp (width ^ v - d * (n : ℝ) / width ^ 2))) :
    affineTubeRootMRCAPairMean φ μ n initial lower drift width endpointUpper ≠ ∞ := by
  exact affineTubeRootMRCAPairMean_ne_top_of_segmentProbability
    φ μ hboundary hcross n initial lower drift width endpointUpper hdrift
    (ENNReal.ofReal (Real.exp (width ^ v - d * (n : ℝ) / width ^ 2)))
    ENNReal.ofReal_ne_top hsegment

/-- A generation-`n` prefix contributes its weighted ancestral path mass,
multiplied by the cross-child weight at the frontier mark. -/
noncomputable def weightedPrefixCrossChildWeightSum
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (x : ℝ) (ω : StepField ℕ X) : ℝ≥0∞ :=
  ∑' u : TreeNode ℕ,
    weightedPathGenerationTerm φ n F x u ω *
      crossChildWeight φ (ω u)

/-- The ancestor-prefix cross-weight sum with one extra reciprocal-potential
factor. In the MRCA expansion this contributes the prefix indicator times
`exp(-2 * pathPotential)` and the cross-child weight at that ancestor. -/
noncomputable def weightedPrefixSquareCrossChildWeightSum
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (x : ℝ) (ω : StepField ℕ X) : ℝ≥0∞ :=
  ∑' u : TreeNode ℕ,
    weightedPathGenerationTerm φ n F x u ω *
      ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
        crossChildWeight φ (ω u)

/-- The square-weighted prefix sum with an arbitrary observable of the
offspring mark at the generation-`n` frontier.  This is the reusable form of
the ancestor factor in an MRCA pair contribution;
`weightedPrefixSquareCrossChildWeightSum` is its cross-child specialization. -/
noncomputable def weightedPrefixSquareObservableSum
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (x : ℝ) (g : Step ℕ X → ℝ≥0∞) (ω : StepField ℕ X) : ℝ≥0∞ :=
  ∑' u : TreeNode ℕ,
    weightedPathGenerationTerm φ n F x u ω *
      ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) * g (ω u)

/-- A frontier continuation observable may depend on its ancestor's
position. A uniform bound in that position lets the position-dependent
observable be dominated by a fixed offspring observable, which then factors
from the generation prefix. -/
theorem lintegral_generationPrefixParameterizedObservableSum_le
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ)
    (A : TreeNode ℕ → StepField ℕ X → ℝ≥0∞)
    (position : TreeNode ℕ → StepField ℕ X → ℝ)
    (g : ℝ → Step ℕ X → ℝ≥0∞)
    (hAgen : ∀ u, Measurable[generationFiltration (M := Step ℕ X) n]
      (A u))
    (hA : ∀ u, Measurable (A u))
    (hsupport : ∀ u, u.length ≠ n → A u = fun _ => 0)
    (C : ℝ≥0∞)
    (hbound : ∀ x ξ, g x ξ ≤ C * crossChildWeight φ ξ) :
    (∫⁻ ω, ∑' u : TreeNode ℕ,
      A u ω * g (position u ω) (ω u) ∂stepFieldLaw μ) ≤
        C * (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂stepFieldLaw μ) := by
  classical
  have hpoint (ω : StepField ℕ X) :
      (∑' u : TreeNode ℕ,
        A u ω * g (position u ω) (ω u)) ≤
        ∑' u : TreeNode ℕ,
          A u ω * (C * crossChildWeight φ (ω u)) := by
    exact ENNReal.tsum_le_tsum (fun u =>
      mul_le_mul_of_nonneg_left (hbound (position u ω) (ω u)) (by positivity))
  have hbase : Measurable (fun ω : StepField ℕ X =>
      ∑' u : TreeNode ℕ, A u ω * crossChildWeight φ (ω u)) := by
    apply Measurable.tsum
    intro u
    exact (hA u).mul
      ((crossChildWeight_measurable φ).comp (measurable_pi_apply u))
  have hmajor (ω : StepField ℕ X) :
      (∑' u : TreeNode ℕ,
        A u ω * (C * crossChildWeight φ (ω u))) =
        C * (∑' u : TreeNode ℕ,
          A u ω * crossChildWeight φ (ω u)) := by
    calc
      _ = ∑' u : TreeNode ℕ,
          C * (A u ω * crossChildWeight φ (ω u)) := by
        apply tsum_congr
        intro u
        ac_rfl
      _ = _ := ENNReal.tsum_mul_left
  calc
    (∫⁻ ω, ∑' u : TreeNode ℕ,
        A u ω * g (position u ω) (ω u) ∂stepFieldLaw μ) ≤
        ∫⁻ ω, ∑' u : TreeNode ℕ,
          A u ω * (C * crossChildWeight φ (ω u))
          ∂stepFieldLaw μ := lintegral_mono hpoint
    _ = C * (∫⁻ ω, ∑' u : TreeNode ℕ,
          A u ω * crossChildWeight φ (ω u) ∂stepFieldLaw μ) := by
      calc
        _ = ∫⁻ ω, C * (∑' u : TreeNode ℕ,
              A u ω * crossChildWeight φ (ω u)) ∂stepFieldLaw μ := by
          apply lintegral_congr
          exact hmajor
        _ = _ := lintegral_const_mul C hbase
    _ = C * (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂stepFieldLaw μ) := by
      rw [lintegral_generationPrefixObservableSum_eq_mul μ n A
        (crossChildWeight φ) hAgen hA hsupport
        (crossChildWeight_measurable φ)]
      ac_rfl

/-- The uniform shifted-spine continuation estimate can be averaged over a
generation-`prefixLength` prefix. This is the local expected-pair bound for one fixed
MRCA depth; the prefix weight `A` is supplied by its ancestral corridor. -/
theorem lintegral_generationPrefixChildPairObservable_le
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (prefixLength continuationLength : ℕ)
    (A : TreeNode ℕ → StepField ℕ X → ℝ≥0∞)
    (position : TreeNode ℕ → StepField ℕ X → ℝ)
    (hAgen : ∀ u,
      Measurable[generationFiltration (M := Step ℕ X) prefixLength]
      (A u))
    (hA : ∀ u, Measurable (A u))
    (hsupport : ∀ u, u.length ≠ prefixLength → A u = fun _ => 0)
    (terminalUpper : ℝ)
    (corridor : Set (Fin (continuationLength + 2) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨continuationLength + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ) (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ corridor,
      history ⟨1, by omega⟩ ∈ window)
    (hprob : ∀ x y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history continuationLength (x + y) increment) ∈
            corridor} ≤ q) :
    (∫⁻ ω, ∑' u : TreeNode ℕ,
      A u ω * ENNReal.ofReal (Real.exp (2 * position u ω)) *
        pathGenerationChildMeanOffDiagonal φ μ continuationLength
          (corridor.indicator (fun _ => (1 : ℝ≥0∞)))
          (position u ω) (ω u) ∂stepFieldLaw μ) ≤
        ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2 *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂stepFieldLaw μ) := by
  let g : ℝ → Step ℕ X → ℝ≥0∞ := fun x ξ =>
    ENNReal.ofReal (Real.exp (2 * x)) *
      pathGenerationChildMeanOffDiagonal φ μ continuationLength
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ξ
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2
  have hbound : ∀ x ξ, g x ξ ≤ C * crossChildWeight φ ξ := by
    intro x ξ
    simpa [g, C, mul_assoc] using
      pathGenerationChildMeanOffDiagonal_normalized_le_of_uniformShiftedProbability
        φ μ hboundary continuationLength terminalUpper corridor hcorridor
        hterminal window q
        hfirst hprob x ξ
  simpa [g, C, mul_assoc] using
    lintegral_generationPrefixParameterizedObservableSum_le
      φ μ prefixLength A position g hAgen hA hsupport C hbound

private lemma displaceWith_measurable_generation
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (v p : TreeNode ℕ)
    (hvp : v.length + p.length ≤ n) :
    Measurable[generationFiltration (M := Step ℕ X) n]
      (fun ω : StepField ℕ X =>
        Combinatorics.Branching.displaceWith φ ω v p) := by
  induction p generalizing v with
  | nil => exact measurable_const
  | cons i p ih =>
      have hparent : v.length < n := by
        simp only [List.length_cons] at hvp
        omega
      have hstep : Measurable[generationFiltration (M := Step ℕ X) n]
          (fun ω : StepField ℕ X =>
            value' ((ω v).map φ) i) := by
        exact (value'_measurable i).comp
          ((Step.map_measurable φ.measurable_toFun).comp
            (mark_measurable_of_depth_lt (M := Step ℕ X) v n hparent))
      have htailBound : (v ++ [i]).length + p.length ≤ n := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        simp only [List.length_cons] at hvp
        omega
      have htail := ih (v := v ++ [i]) htailBound
      change Measurable[generationFiltration (M := Step ℕ X) n]
        (fun ω : StepField ℕ X =>
          value' ((ω v).map φ) i +
            Combinatorics.Branching.displaceWith φ ω (v ++ [i]) p)
      exact hstep.add htail

private lemma pathHistory_measurable_generation
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ) (u : TreeNode ℕ)
    (hu : u.length ≤ n) :
    Measurable[generationFiltration (M := Step ℕ X) n]
      (fun ω : StepField ℕ X => pathHistory φ n x ω u) := by
  letI : MeasurableSpace (StepField ℕ X) :=
    generationFiltration (M := Step ℕ X) n
  rw [measurable_pi_iff]
  intro k
  have htake : (u.take k).length ≤ n := by
    have hlen : (u.take k).length ≤ k.val := by
      simp [List.length_take]
    omega
  exact measurable_const.add
    (displaceWith_measurable_generation φ n [] (u.take k)
      (by simpa using htake))

private lemma weightedPathGenerationTerm_measurable_generation
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F)
    (x : ℝ) (u : TreeNode ℕ) :
    Measurable[generationFiltration (M := Step ℕ X) n]
      (weightedPathGenerationTerm φ n F x u) := by
  letI : MeasurableSpace (StepField ℕ X) :=
    generationFiltration (M := Step ℕ X) n
  by_cases hu : u.length = n
  · rw [weightedPathGenerationTerm]
    have hpotential :
        Measurable[generationFiltration (M := Step ℕ X) n]
          (fun ω : StepField ℕ X => pathPotential φ ω u) := by
      simpa [pathPotential] using
        displaceWith_measurable_generation φ n [] u (by simpa [hu])
    have hhistory := pathHistory_measurable_generation φ n x u (by omega)
    have hvalue : Measurable[generationFiltration (M := Step ℕ X) n]
        (fun ω : StepField ℕ X =>
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
            F (pathHistory φ n x ω u)) :=
      hpotential.neg.exp.ennreal_ofReal.mul (hF.comp hhistory)
    have hsurvive : MeasurableSet[generationFiltration (M := Step ℕ X) n]
        {ω : StepField ℕ X | surviveAlong ω [] u} := by
      exact surviveAlong_measurableSet (X := X) [] u n (by simpa [hu])
    have hset : {ω : StepField ℕ X |
        u.length = n ∧ surviveAlong ω [] u} =
        {ω : StepField ℕ X | surviveAlong ω [] u} := by
      ext ω
      simp [hu]
    rw [hset]
    exact hvalue.indicator hsurvive
  · have hzero : weightedPathGenerationTerm φ n F x u = 0 := by
      funext ω
      simp [weightedPathGenerationTerm, hu]
    rw [hzero]
    exact measurable_const

/-- Exact factorization of the square-weighted prefix observable.  Its
cross-child instance is the ancestor-side term in the positive-depth
MRCA sum. -/
theorem lintegral_weightedPrefixSquareObservableSum_eq_mul
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) (g : Step ℕ X → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, weightedPrefixSquareObservableSum φ n F x g ω
      ∂stepFieldLaw μ) =
        (∫⁻ ξ, g ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ,
            weightedPathGenerationTerm φ n F x u ω *
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
            ∂stepFieldLaw μ) := by
  let A (u : TreeNode ℕ) : StepField ℕ X → ℝ≥0∞ := fun ω =>
    weightedPathGenerationTerm φ n F x u ω *
      ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
  have hAgen (u : TreeNode ℕ) :
      Measurable[generationFiltration (M := Step ℕ X) n] (A u) := by
    by_cases hu : u.length = n
    · have hp := displaceWith_measurable_generation φ n [] u (by simpa [hu])
      have hpotential : Measurable[generationFiltration (M := Step ℕ X) n]
          (fun ω : StepField ℕ X => pathPotential φ ω u) := by
        simpa [pathPotential] using hp
      exact (weightedPathGenerationTerm_measurable_generation φ n hF x u).mul
        hpotential.neg.exp.ennreal_ofReal
    · have hzero : A u = fun _ => 0 := by
        funext ω
        simp [A, weightedPathGenerationTerm, hu]
      rw [hzero]
      exact measurable_const
  have hA (u : TreeNode ℕ) : Measurable (A u) := by
    by_cases hu : u.length = n
    · exact (weightedPathGenerationTerm_measurable φ n hF x u).mul
        ((ENNReal.continuous_ofReal.measurable.comp
          (Real.continuous_exp.measurable.comp
            ((pathPotential_measurable φ [] u).neg))))
    · have hzero : A u = fun _ => 0 := by
        funext ω
        simp [A, weightedPathGenerationTerm, hu]
      rw [hzero]
      exact measurable_const
  have hsupport (u : TreeNode ℕ) (hu : u.length ≠ n) :
      A u = fun _ => 0 := by
    funext ω
    simp [A, weightedPathGenerationTerm, hu]
  simpa [weightedPrefixSquareObservableSum, A] using
    (lintegral_generationPrefixObservableSum_eq_mul μ n A g
      hAgen hA hsupport hg)

/-- A pointwise cross-child domination for a frontier continuation observable
can be pulled through the prefix sum.  This is the estimate used for a fixed
MRCA depth after the shifted continuation probabilities have been bounded. -/
theorem lintegral_weightedPrefixSquareObservableSum_le_of_crossChildBound
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) (g : Step ℕ X → ℝ≥0∞) (hg : Measurable g)
    (C : ℝ≥0∞)
    (hbound : ∀ ξ, g ξ ≤ C * crossChildWeight φ ξ) :
    (∫⁻ ω, weightedPrefixSquareObservableSum φ n F x g ω
      ∂stepFieldLaw μ) ≤
        C * (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ,
            weightedPathGenerationTerm φ n F x u ω *
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
            ∂stepFieldLaw μ) := by
  rw [lintegral_weightedPrefixSquareObservableSum_eq_mul
    φ μ n F hF x g hg]
  have hmean :
      (∫⁻ ξ, g ξ ∂μ) ≤ C * (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
    calc
      (∫⁻ ξ, g ξ ∂μ) ≤
          ∫⁻ ξ, C * crossChildWeight φ ξ ∂μ := lintegral_mono hbound
      _ = C * (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
        rw [lintegral_const_mul _ (crossChildWeight_measurable φ)]
  calc
    (∫⁻ ξ, g ξ ∂μ) *
        (∫⁻ ω, ∑' u : TreeNode ℕ,
          weightedPathGenerationTerm φ n F x u ω *
            ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
          ∂stepFieldLaw μ) ≤
      (C * (∫⁻ ξ, crossChildWeight φ ξ ∂μ)) *
        (∫⁻ ω, ∑' u : TreeNode ℕ,
          weightedPathGenerationTerm φ n F x u ω *
            ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
          ∂stepFieldLaw μ) := by
      exact mul_le_mul_of_nonneg_right hmean (by positivity)
    _ = C * (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ,
            weightedPathGenerationTerm φ n F x u ω *
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
            ∂stepFieldLaw μ) := by
      ac_rfl

/-- The square-weighted prefix/cross-child observable factors into the
offspring cross-child moment and the mean square-weighted prefix mass. -/
theorem lintegral_weightedPrefixSquareCrossChildWeightSum_eq_crossMoment_mul
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, weightedPrefixSquareCrossChildWeightSum φ n F x ω
      ∂stepFieldLaw μ) =
        (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ,
            weightedPathGenerationTerm φ n F x u ω *
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
            ∂stepFieldLaw μ) := by
  simpa [weightedPrefixSquareCrossChildWeightSum,
    weightedPrefixSquareObservableSum] using
    (lintegral_weightedPrefixSquareObservableSum_eq_mul
      φ μ n F hF x (crossChildWeight φ) (crossChildWeight_measurable φ))

/-- The frontier cross-child weight is independent of the generation-`n`
prefix. Consequently the expected weighted prefix/cross-weight sum factors
exactly into the finite cross-child moment and the spine prefix integral. This
is the ancestor-side factor in each positive-depth MRCA pair contribution. -/
theorem lintegral_weightedPrefixCrossChildWeightSum_eq_crossMoment_mul
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, weightedPrefixCrossChildWeightSum φ n F x ω
      ∂stepFieldLaw μ) =
      (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
        (∫⁻ ω, weightedPathGeneration φ n F x ω ∂stepFieldLaw μ) := by
  classical
  let A (u : TreeNode ℕ) : StepField ℕ X → ℝ≥0∞ :=
    weightedPathGenerationTerm φ n F x u
  let B (u : TreeNode ℕ) : StepField ℕ X → ℝ≥0∞ :=
    fun ω => crossChildWeight φ (ω u)
  have hA (u : TreeNode ℕ) :
      Measurable[generationFiltration (M := Step ℕ X) n] (A u) := by
    simpa [A] using
      weightedPathGenerationTerm_measurable_generation φ n hF x u
  have hB (u : TreeNode ℕ) :
      Measurable[MeasurableSpace.comap (subtreeStepField u) inferInstance]
        (B u) := by
    have hroot : Measurable (fun η : StepField ℕ X =>
        crossChildWeight φ (η [])) :=
      (crossChildWeight_measurable φ).comp
        (measurable_pi_apply ([] : TreeNode ℕ) :
          Measurable (fun η : StepField ℕ X => η []))
    apply Measurable.of_comap_le
    exact MeasurableSpace.comap_le_comap_of_eq_comp
      (f := subtreeStepField u) (g := B u)
      (h := fun η : StepField ℕ X => crossChildWeight φ (η [])) hroot (by
        funext ω
        simp [B, subtreeStepField])
  have hAfull (u : TreeNode ℕ) : Measurable (A u) := by
    simpa [A] using weightedPathGenerationTerm_measurable φ n hF x u
  have hBfull (u : TreeNode ℕ) : Measurable (B u) := by
    simpa [B, Function.comp_def] using
      (crossChildWeight_measurable φ).comp
        (measurable_pi_apply u :
          Measurable (fun ω : StepField ℕ X => ω u))
  have hfactor (u : TreeNode ℕ) :
      (∫⁻ ω, A u ω * B u ω ∂stepFieldLaw μ) =
        (∫⁻ ω, A u ω ∂stepFieldLaw μ) *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
    by_cases hu : u.length = n
    · subst n
      have hind : IndepFun (A u) (B u) (stepFieldLaw μ) := by
        rw [IndepFun_iff_Indep]
        exact indep_of_indep_of_le_right
          (indep_of_indep_of_le_left
            (generation_subtreeStepField_independent μ u) (hA u).comap_le)
          (hB u).comap_le
      calc
        (∫⁻ ω, A u ω * B u ω ∂stepFieldLaw μ) =
            (∫⁻ ω, A u ω ∂stepFieldLaw μ) *
              (∫⁻ ξ, B u ξ ∂stepFieldLaw μ) :=
          lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
            (hAfull u) (hBfull u) hind
        _ = (∫⁻ ω, A u ω ∂stepFieldLaw μ) *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
          congr 1
          change (∫⁻ ω, crossChildWeight φ (ω u) ∂stepFieldLaw μ) = _
          calc
            _ = ∫⁻ ξ, crossChildWeight φ ξ ∂
                (stepFieldLaw μ).map (fun ω : StepField ℕ X => ω u) := by
              exact (lintegral_map (crossChildWeight_measurable φ)
                (measurable_pi_apply u :
                  Measurable (fun ω : StepField ℕ X => ω u))).symm
            _ = ∫⁻ ξ, crossChildWeight φ ξ ∂μ := by
              rw [stepFieldLaw_coordinate μ u]
    · have hzero : A u = fun _ => 0 := by
        funext ω
        simp [A, weightedPathGenerationTerm, hu]
      simp [hzero]
  have htermMeas (u : TreeNode ℕ) :
      Measurable (fun ω : StepField ℕ X => A u ω * B u ω) :=
    ((weightedPathGenerationTerm_measurable φ n hF x u).mul
      ((crossChildWeight_measurable φ).comp (measurable_pi_apply u)))
  have hsumIntegral :
      (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω * B u ω ∂stepFieldLaw μ) =
        ∑' u : TreeNode ℕ,
          ∫⁻ ω, A u ω * B u ω ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    intro u
    exact (htermMeas u).aemeasurable
  have hweighted :
      (∑' u : TreeNode ℕ, ∫⁻ ω, A u ω ∂stepFieldLaw μ) =
        ∫⁻ ω, weightedPathGeneration φ n F x ω ∂stepFieldLaw μ := by
    simp only [weightedPathGeneration]
    rw [lintegral_tsum]
    intro u
    exact (weightedPathGenerationTerm_measurable φ n hF x u).aemeasurable
  calc
    (∫⁻ ω, weightedPrefixCrossChildWeightSum φ n F x ω
      ∂stepFieldLaw μ) =
        ∑' u : TreeNode ℕ,
          ∫⁻ ω, A u ω * B u ω ∂stepFieldLaw μ := by
      change (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω * B u ω
        ∂stepFieldLaw μ) = _
      exact hsumIntegral
    _ = ∑' u : TreeNode ℕ,
          (∫⁻ ω, A u ω ∂stepFieldLaw μ) *
            (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
      apply tsum_congr
      intro u
      exact hfactor u
    _ = (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (∫⁻ ω, weightedPathGeneration φ n F x ω ∂stepFieldLaw μ) := by
      rw [ENNReal.tsum_mul_right]
      rw [hweighted, mul_comm]

/-- For an indicator prefix corridor, the factorization above is exactly the
cross-child moment times the corresponding tilted-spine corridor probability.
This is the ancestor-prefix factor appearing in each positive-depth MRCA
pair contribution in Wang Yiyang, *Asymptotic Speed of the N-Branching Random
Walk with Infinite Offspring* (master's thesis, Fudan University, 2026),
Chapter 4, Lemma 4.5. -/
theorem lintegral_weightedPrefixCrossChildWeightSum_indicator_eq_crossMoment_mul_spineProbability
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (x : ℝ) :
    (∫⁻ ω, weightedPrefixCrossChildWeightSum φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ω
      ∂stepFieldLaw μ) =
      (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
        (tiltedIncrementFieldLaw φ μ)
          {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor} := by
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor}
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hspineEvent : MeasurableSet spineEvent :=
    hcorridor.preimage (ProbabilityTheory.RandomWalk.history_measurable n x)
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    tiltedIncrementFieldLaw_isProbability φ μ hboundary
  letI : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) := htilted
  have hmanyToOne := weightedPathManyToOneCore φ μ hboundary n hF x
  calc
    (∫⁻ ω, weightedPrefixCrossChildWeightSum φ n F x ω
        ∂stepFieldLaw μ) =
        (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (∫⁻ ω, weightedPathGeneration φ n F x ω ∂stepFieldLaw μ) :=
      lintegral_weightedPrefixCrossChildWeightSum_eq_crossMoment_mul
        φ μ n F hF x
    _ = (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (tiltedIncrementFieldLaw φ μ) spineEvent := by
      rw [hmanyToOne]
      congr 1
      change (∫⁻ increment, spineEvent.indicator
        (fun _ => (1 : ℝ≥0∞)) increment ∂tiltedIncrementFieldLaw φ μ) = _
      rw [lintegral_indicator_const hspineEvent]
      simp [spineEvent]

/-- A shifted-spine estimate for the prefix corridor immediately gives the
corresponding averaged ancestor cross-weight bound. No second-moment or
pair-bound assumption is introduced here. -/
theorem lintegral_weightedPrefixCrossChildWeightSum_indicator_le_crossMoment_mul
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (x : ℝ) (q : ℝ≥0∞)
    (hprefix : (tiltedIncrementFieldLaw φ μ)
      {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor} ≤ q) :
    (∫⁻ ω, weightedPrefixCrossChildWeightSum φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ω
      ∂stepFieldLaw μ) ≤
      (∫⁻ ξ, crossChildWeight φ ξ ∂μ) * q := by
  rw [lintegral_weightedPrefixCrossChildWeightSum_indicator_eq_crossMoment_mul_spineProbability
    φ μ hboundary n corridor hcorridor x]
  gcongr

/-- The lower boundary of a generation-`n` corridor controls the extra
reciprocal-potential factor in a squared ancestral weight.  The remaining
weighted path mass is exactly its tilted-spine probability. -/
theorem lintegral_weightedPrefixSquareMass_indicator_le_spineProbability
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (x lower : ℝ)
    (hlower : ∀ history ∈ corridor,
      lower ≤ history ⟨n, Nat.lt_succ_self n⟩) :
    (∫⁻ ω, ∑' u : TreeNode ℕ,
      weightedPathGenerationTerm φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x u ω *
        ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
      ∂stepFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (x - lower)) *
        (tiltedIncrementFieldLaw φ μ)
          {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor} := by
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (x - lower))
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hterm (u : TreeNode ℕ) (ω : StepField ℕ X) :
      weightedPathGenerationTerm φ n F x u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) ≤
        K * weightedPathGenerationTerm φ n F x u ω := by
    by_cases hu : u.length = n
    · by_cases hs : surviveAlong ω [] u
      · by_cases hc : pathHistory φ n x ω u ∈ corridor
        · have hendpoint := hlower (pathHistory φ n x ω u) hc
          rw [pathHistory_last φ n x ω u hu] at hendpoint
          have hpotential : -pathPotential φ ω u ≤ x - lower := by linarith
          have hweight : weightedPathGenerationTerm φ n F x u ω =
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) := by
            simp [weightedPathGenerationTerm, F, hu, hs, hc]
          have hextra : ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) ≤ K := by
            exact ENNReal.ofReal_le_ofReal
              (Real.exp_le_exp.mpr hpotential)
          rw [hweight]
          exact mul_le_mul_of_nonneg_right hextra (by positivity)
        · simp [weightedPathGenerationTerm, F, hu, hs, hc]
      · simp [weightedPathGenerationTerm, hu, hs]
    · simp [weightedPathGenerationTerm, hu]
  have hsumPointwise (ω : StepField ℕ X) :
      (∑' u : TreeNode ℕ,
        weightedPathGenerationTerm φ n F x u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u))) ≤
        K * weightedPathGeneration φ n F x ω := by
    calc
      _ ≤ ∑' u : TreeNode ℕ,
          K * weightedPathGenerationTerm φ n F x u ω :=
        ENNReal.tsum_le_tsum (fun u => hterm u ω)
      _ = K * weightedPathGeneration φ n F x ω := by
        rw [weightedPathGeneration, ENNReal.tsum_mul_left]
  have hsumMeas : Measurable (fun ω : StepField ℕ X =>
      ∑' u : TreeNode ℕ,
        weightedPathGenerationTerm φ n F x u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u))) := by
    apply Measurable.tsum
    intro u
    exact (weightedPathGenerationTerm_measurable φ n hF x u).mul
      ((ENNReal.continuous_ofReal.measurable.comp
        (Real.continuous_exp.measurable.comp
          ((pathPotential_measurable φ [] u).neg))))
  have hweighted : Measurable (weightedPathGeneration φ n F x) :=
    weightedPathGeneration_measurable (ι := ℕ) φ n hF x
  have hsumIntegral :
      (∫⁻ ω, ∑' u : TreeNode ℕ,
        weightedPathGenerationTerm φ n F x u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
        ∂stepFieldLaw μ) =
        ∑' u : TreeNode ℕ,
          ∫⁻ ω, weightedPathGenerationTerm φ n F x u ω *
            ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
            ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    intro u
    exact ((weightedPathGenerationTerm_measurable φ n hF x u).mul
      ((ENNReal.continuous_ofReal.measurable.comp
        (Real.continuous_exp.measurable.comp
          ((pathPotential_measurable φ [] u).neg))))).aemeasurable
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor}
  have hspineEvent : MeasurableSet spineEvent :=
    hcorridor.preimage (ProbabilityTheory.RandomWalk.history_measurable n x)
  have hmanyToOne := weightedPathManyToOneCore φ μ hboundary n hF x
  calc
    (∫⁻ ω, ∑' u : TreeNode ℕ,
        weightedPathGenerationTerm φ n F x u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
        ∂stepFieldLaw μ) ≤
      ∫⁻ ω, K * weightedPathGeneration φ n F x ω ∂stepFieldLaw μ :=
        lintegral_mono hsumPointwise
    _ = K * (∫⁻ ω, weightedPathGeneration φ n F x ω ∂stepFieldLaw μ) :=
      lintegral_const_mul K hweighted
    _ = K * (∫⁻ increment, F
          (ProbabilityTheory.RandomWalk.history n x increment)
          ∂tiltedIncrementFieldLaw φ μ) := by rw [hmanyToOne]
    _ = K * (tiltedIncrementFieldLaw φ μ) spineEvent := by
      congr 1
      change (∫⁻ increment, spineEvent.indicator
        (fun _ => (1 : ℝ≥0∞)) increment ∂tiltedIncrementFieldLaw φ μ) = _
      rw [lintegral_indicator_const hspineEvent]
      simp [spineEvent]
    _ = _ := by
      simp only [K]
      congr 1

/-- A fixed MRCA depth factors into the continuation-pair estimate and the
square-weighted ancestral corridor mass. This is the positive-depth analogue
of the root-split contribution estimate, before summing over all possible MRCA depths. -/
theorem lintegral_weightedPrefixContinuationPair_indicator_le
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (m n : ℕ) (prefixCorridor : Set (Fin (m + 1) → ℝ))
    (hprefixCorridor : MeasurableSet prefixCorridor)
    (initial prefixLower : ℝ)
    (hprefixLower : ∀ history ∈ prefixCorridor,
      prefixLower ≤ history ⟨m, Nat.lt_succ_self m⟩)
    (continuationCorridor : Set (Fin (n + 2) → ℝ))
    (hcontinuationCorridor : MeasurableSet continuationCorridor)
    (terminalUpper : ℝ)
    (hterminalUpper : ∀ history ∈ continuationCorridor,
      history ⟨n + 1, by omega⟩ ≤ terminalUpper)
    (window : Set ℝ) (q : ℝ≥0∞)
    (hfirst : ∀ history ∈ continuationCorridor,
      history ⟨1, by omega⟩ ∈ window)
    (hcontinuation : ∀ x y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            continuationCorridor} ≤ q) :
    ENNReal.ofReal (Real.exp (-(2 * initial))) *
      (∫⁻ ω, ∑' u : TreeNode ℕ,
        weightedPathGenerationTerm φ m
          (prefixCorridor.indicator (fun _ => (1 : ℝ≥0∞))) initial u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
          ENNReal.ofReal
            (Real.exp (2 * (initial + pathPotential φ ω u))) *
          pathGenerationChildMeanOffDiagonal φ μ n
            (continuationCorridor.indicator (fun _ => (1 : ℝ≥0∞)))
            (initial + pathPotential φ ω u) (ω u)
        ∂stepFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2) *
        (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
        (ENNReal.ofReal (Real.exp (initial - prefixLower)) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | ProbabilityTheory.RandomWalk.history m initial increment ∈
              prefixCorridor}) := by
  let F : (Fin (m + 1) → ℝ) → ℝ≥0∞ :=
    prefixCorridor.indicator (fun _ => (1 : ℝ≥0∞))
  let G : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    continuationCorridor.indicator (fun _ => (1 : ℝ≥0∞))
  let A : TreeNode ℕ → StepField ℕ X → ℝ≥0∞ := fun u ω =>
    weightedPathGenerationTerm φ m F initial u ω *
      ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
  let position : TreeNode ℕ → StepField ℕ X → ℝ := fun u ω =>
    initial + pathPotential φ ω u
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * terminalUpper)) * q ^ 2
  have hF : Measurable F := measurable_const.indicator hprefixCorridor
  have hG : Measurable G := measurable_const.indicator hcontinuationCorridor
  have hAgen (u : TreeNode ℕ) :
      Measurable[generationFiltration (M := Step ℕ X) m] (A u) := by
    by_cases hu : u.length = m
    · have hp :
          Measurable[generationFiltration (M := Step ℕ X) m]
            (fun ω : StepField ℕ X => pathPotential φ ω u) := by
        simpa [pathPotential] using
          displaceWith_measurable_generation φ m [] u (by simpa [hu])
      exact (weightedPathGenerationTerm_measurable_generation φ m hF initial u).mul
        hp.neg.exp.ennreal_ofReal
    · have hzero : A u = fun _ => 0 := by
        funext ω
        simp [A, weightedPathGenerationTerm, hu]
      rw [hzero]
      exact measurable_const
  have hA (u : TreeNode ℕ) : Measurable (A u) := by
    by_cases hu : u.length = m
    · exact (weightedPathGenerationTerm_measurable φ m hF initial u).mul
        ((ENNReal.continuous_ofReal.measurable.comp
          (Real.continuous_exp.measurable.comp
            ((pathPotential_measurable φ [] u).neg))))
    · have hzero : A u = fun _ => 0 := by
        funext ω
        simp [A, weightedPathGenerationTerm, hu]
      rw [hzero]
      exact measurable_const
  have hsupport (u : TreeNode ℕ) (hu : u.length ≠ m) :
      A u = fun _ => 0 := by
    funext ω
    simp [A, weightedPathGenerationTerm, hu]
  have hpair :=
    lintegral_generationPrefixChildPairObservable_le
      φ μ hboundary m n A position hAgen hA hsupport terminalUpper
      continuationCorridor hcontinuationCorridor hterminalUpper window q
      hfirst hcontinuation
  have hmass :=
    lintegral_weightedPrefixSquareMass_indicator_le_spineProbability
      φ μ hboundary m prefixCorridor hprefixCorridor initial prefixLower
      hprefixLower
  have hpair' :
      (∫⁻ ω, ∑' u : TreeNode ℕ,
        A u ω * ENNReal.ofReal (Real.exp (2 * position u ω)) *
          pathGenerationChildMeanOffDiagonal φ μ n G
            (position u ω) (ω u) ∂stepFieldLaw μ) ≤
        C * (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂stepFieldLaw μ) := by
    simpa [A, G, position, C, mul_assoc] using hpair
  have hmass' :
      (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂stepFieldLaw μ) ≤
        ENNReal.ofReal (Real.exp (initial - prefixLower)) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | ProbabilityTheory.RandomWalk.history m initial increment ∈
              prefixCorridor} := by
    simpa [A, F] using hmass
  calc
    ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (∫⁻ ω, ∑' u : TreeNode ℕ,
          A u ω * ENNReal.ofReal (Real.exp (2 * position u ω)) *
            pathGenerationChildMeanOffDiagonal φ μ n G
              (position u ω) (ω u) ∂stepFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (C * (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂stepFieldLaw μ)) :=
      mul_le_mul_of_nonneg_left hpair' (by positivity)
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (C * (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (ENNReal.ofReal (Real.exp (initial - prefixLower)) *
            (tiltedIncrementFieldLaw φ μ)
              {increment | ProbabilityTheory.RandomWalk.history m initial increment ∈
                prefixCorridor})) := by
      gcongr
    _ = _ := by
      simp [C, mul_assoc]

/-- The fixed-depth estimate for the affine tube follows from the drawdown
bound on the continuation increments. The prefix and continuation lengths
are separate: together they describe paths through MRCA depth `m` and then
`n + 1` further generations. -/
theorem lintegral_affineCorridorPrefixContinuationPair_indicator_le_of_drawdown
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (m n : ℕ) (initial lower drift width endpointUpper : ℝ)
    (hdrift : 0 ≤ drift) (q : ℝ≥0∞)
    (hdrawdown : (tiltedIncrementFieldLaw φ μ)
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ))) ≤ q) :
    ENNReal.ofReal (Real.exp (-(2 * initial))) *
      (∫⁻ ω, ∑' u : TreeNode ℕ,
        weightedPathGenerationTerm φ m
          ((affineCorridorPrefix m lower drift width).indicator
            (fun _ => (1 : ℝ≥0∞))) initial u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
          ENNReal.ofReal
            (Real.exp (2 * (initial + pathPotential φ ω u))) *
          pathGenerationChildMeanOffDiagonal φ μ n
            ((affineCorridorHistoryEndpointCutoff n
              (lower + drift * (m : ℝ)) drift width endpointUpper).indicator
                (fun _ => (1 : ℝ≥0∞)))
            (initial + pathPotential φ ω u) (ω u)
        ∂stepFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (ENNReal.ofReal (Real.exp (2 * endpointUpper)) * q ^ 2) *
        (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
        (ENNReal.ofReal (Real.exp
          (initial - (lower + drift * (m : ℝ)))) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | ProbabilityTheory.RandomWalk.history m initial increment ∈
              affineCorridorPrefix m lower drift width}) := by
  let prefixCorridor := affineCorridorPrefix m lower drift width
  let continuationCorridor := affineCorridorHistoryEndpointCutoff n
    (lower + drift * (m : ℝ)) drift width endpointUpper
  have hprefixMeas : MeasurableSet prefixCorridor :=
    measurableSet_affineCorridorPrefix m lower drift width
  have hcontinuationMeas : MeasurableSet continuationCorridor :=
    measurableSet_affineCorridorHistoryEndpointCutoff n
      (lower + drift * (m : ℝ)) drift width endpointUpper
  have hprefixLower : ∀ history ∈ prefixCorridor,
      lower + drift * (m : ℝ) ≤ history ⟨m, Nat.lt_succ_self m⟩ := by
    intro history hh
    simpa [prefixCorridor, affineCorridorPrefix] using
      (hh ⟨m, Nat.lt_succ_self m⟩).1
  have hterminal : ∀ history ∈ continuationCorridor,
      history ⟨n + 1, by omega⟩ ≤ endpointUpper := by
    intro history hh
    exact affineCorridorHistoryEndpointCutoff_terminalUpper n
      (lower + drift * (m : ℝ)) drift width endpointUpper history hh
  let window := affineCorridorFirstWindow
    (lower + drift * (m : ℝ)) drift width
  have hfirst : ∀ history ∈ continuationCorridor,
      history ⟨1, by omega⟩ ∈ window := by
    intro history hh
    exact affineCorridorHistoryEndpointCutoff_firstWindow n
      (lower + drift * (m : ℝ)) drift width endpointUpper history hh
  have hcontinuation : ∀ x y : ℝ, x + y ∈ window →
      (tiltedIncrementFieldLaw φ μ)
        {increment | prependHistory x
          (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
            continuationCorridor} ≤ q := by
    intro x y _
    exact tiltedIncrementFieldLaw_affineCorridorHistoryEndpointCutoff_le_drawdown
      φ μ n x (lower + drift * (m : ℝ)) drift width endpointUpper y hdrift q
      hdrawdown
  simpa [prefixCorridor, continuationCorridor, window] using
    lintegral_weightedPrefixContinuationPair_indicator_le
      φ μ hboundary m n prefixCorridor hprefixMeas initial
      (lower + drift * (m : ℝ)) hprefixLower continuationCorridor
      hcontinuationMeas endpointUpper hterminal window q hfirst hcontinuation

/-- Expected ordered successful path pairs whose most recent common ancestor
is at generation `m`, with `n + 1` generations remaining below that ancestor. -/
noncomputable def affineTubeMRCAPairContribution
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X))
    (m n : ℕ) (initial lower drift width endpointUpper : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' u : TreeNode ℕ,
    pathGenerationTerm φ m
      ((affineCorridorPrefix m lower drift width).indicator
        (fun _ => (1 : ℝ≥0∞))) initial u ω *
    pathGenerationChildMeanOffDiagonal φ μ n
      ((affineCorridorHistoryEndpointCutoff n
        (lower + drift * (m : ℝ)) drift width endpointUpper).indicator
          (fun _ => (1 : ℝ≥0∞)))
      (initial + pathPotential φ ω u) (ω u) ∂stepFieldLaw μ

private lemma expReciprocalSquareNormalization (x s : ℝ) :
    ENNReal.ofReal (Real.exp (-(2 * x))) *
      ((ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (Real.exp (-s))) *
        ENNReal.ofReal (Real.exp (2 * (x + s)))) = 1 := by
  have hcancel (t : ℝ) :
      ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal (Real.exp t) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg (-t)), ← Real.exp_add]
    simp
  have hdouble :
      ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (Real.exp (-s)) =
        ENNReal.ofReal (Real.exp (-(2 * s))) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg (-s)), ← Real.exp_add]
    congr 1
    ring_nf
  have hsplit : ENNReal.ofReal (Real.exp (2 * (x + s))) =
      ENNReal.ofReal (Real.exp (2 * x)) *
        ENNReal.ofReal (Real.exp (2 * s)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg (2 * x))]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  calc
    _ = (ENNReal.ofReal (Real.exp (-(2 * x))) *
          ENNReal.ofReal (Real.exp (2 * x))) *
        ((ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (Real.exp (-s))) *
          ENNReal.ofReal (Real.exp (2 * s))) := by ac_rfl
    _ = 1 := by
      rw [hcancel (2 * x), hdouble, hcancel (2 * s)]
      simp

/-- The square-weighted continuation expression is exactly the expected
ordered-pair contribution at this MRCA depth after the initial-position
normalization. -/
theorem affineTubeMRCAPairContribution_eq_normalized
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X))
    (m n : ℕ) (initial lower drift width endpointUpper : ℝ) :
    affineTubeMRCAPairContribution φ μ m n initial lower drift width endpointUpper =
      ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (∫⁻ ω, ∑' u : TreeNode ℕ,
          weightedPathGenerationTerm φ m
            ((affineCorridorPrefix m lower drift width).indicator
              (fun _ => (1 : ℝ≥0∞))) initial u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
          ENNReal.ofReal
            (Real.exp (2 * (initial + pathPotential φ ω u))) *
          pathGenerationChildMeanOffDiagonal φ μ n
            ((affineCorridorHistoryEndpointCutoff n
              (lower + drift * (m : ℝ)) drift width endpointUpper).indicator
                (fun _ => (1 : ℝ≥0∞)))
            (initial + pathPotential φ ω u) (ω u)
          ∂stepFieldLaw μ) := by
  let F : (Fin (m + 1) → ℝ) → ℝ≥0∞ :=
    (affineCorridorPrefix m lower drift width).indicator
      (fun _ => (1 : ℝ≥0∞))
  let G : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    (affineCorridorHistoryEndpointCutoff n
      (lower + drift * (m : ℝ)) drift width endpointUpper).indicator
        (fun _ => (1 : ℝ≥0∞))
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(2 * initial)))
  have hterm (ω : StepField ℕ X) (u : TreeNode ℕ) :
      pathGenerationTerm φ m F initial u ω *
        pathGenerationChildMeanOffDiagonal φ μ n G
          (initial + pathPotential φ ω u) (ω u) =
      c * (weightedPathGenerationTerm φ m F initial u ω *
        ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
        ENNReal.ofReal
          (Real.exp (2 * (initial + pathPotential φ ω u))) *
        pathGenerationChildMeanOffDiagonal φ μ n G
          (initial + pathPotential φ ω u) (ω u)) := by
    rw [weightedPathGenerationTerm_eq_reciprocal_mul_pathGenerationTerm]
    have hscalar := expReciprocalSquareNormalization initial
      (pathPotential φ ω u)
    dsimp [c]
    calc
      _ = 1 * (pathGenerationTerm φ m F initial u ω *
          pathGenerationChildMeanOffDiagonal φ μ n G
            (initial + pathPotential φ ω u) (ω u)) := by simp
      _ = (ENNReal.ofReal (Real.exp (-(2 * initial))) *
            ((ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u))) *
              ENNReal.ofReal
                (Real.exp (2 * (initial + pathPotential φ ω u))))) *
            (pathGenerationTerm φ m F initial u ω *
              pathGenerationChildMeanOffDiagonal φ μ n G
                (initial + pathPotential φ ω u) (ω u)) := by
          rw [hscalar]
      _ = _ := by ac_rfl
  calc
    affineTubeMRCAPairContribution φ μ m n initial lower drift width endpointUpper =
        ∫⁻ ω, c * (∑' u : TreeNode ℕ,
          weightedPathGenerationTerm φ m F initial u ω *
            ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
            ENNReal.ofReal
              (Real.exp (2 * (initial + pathPotential φ ω u))) *
            pathGenerationChildMeanOffDiagonal φ μ n G
              (initial + pathPotential φ ω u) (ω u)) ∂stepFieldLaw μ := by
      apply lintegral_congr
      intro ω
      calc
        _ = ∑' u : TreeNode ℕ,
            c * (weightedPathGenerationTerm φ m F initial u ω *
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
              ENNReal.ofReal
                (Real.exp (2 * (initial + pathPotential φ ω u))) *
              pathGenerationChildMeanOffDiagonal φ μ n G
                (initial + pathPotential φ ω u) (ω u)) := by
              apply tsum_congr
              intro u
              exact hterm ω u
        _ = _ := ENNReal.tsum_mul_left
    _ = c * (∫⁻ ω, ∑' u : TreeNode ℕ,
          weightedPathGenerationTerm φ m F initial u ω *
            ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
            ENNReal.ofReal
              (Real.exp (2 * (initial + pathPotential φ ω u))) *
            pathGenerationChildMeanOffDiagonal φ μ n G
              (initial + pathPotential φ ω u) (ω u)
          ∂stepFieldLaw μ) := by
      exact lintegral_const_mul' c _ ENNReal.ofReal_ne_top
    _ = _ := by simp [c, F, G]

/-- The affine-tube MRCA pair contribution at each positive ancestor
generation is bounded by the same drawdown and cross-child estimates as its
normalized continuation term. -/
theorem affineTubeMRCAPairContribution_le_of_drawdown
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (m n : ℕ) (initial lower drift width endpointUpper : ℝ)
    (hdrift : 0 ≤ drift) (q : ℝ≥0∞)
    (hdrawdown : (tiltedIncrementFieldLaw φ μ)
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ))) ≤ q) :
    affineTubeMRCAPairContribution φ μ m n initial lower drift width endpointUpper ≤
      ENNReal.ofReal (Real.exp (-(2 * initial))) *
        (ENNReal.ofReal (Real.exp (2 * endpointUpper)) * q ^ 2) *
        (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
        (ENNReal.ofReal (Real.exp
          (initial - (lower + drift * (m : ℝ)))) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | ProbabilityTheory.RandomWalk.history m initial increment ∈
              affineCorridorPrefix m lower drift width}) := by
  rw [affineTubeMRCAPairContribution_eq_normalized]
  exact lintegral_affineCorridorPrefixContinuationPair_indicator_le_of_drawdown
    φ μ hboundary m n initial lower drift width endpointUpper hdrift q hdrawdown

/-- Summing the affine-tube MRCA pair contributions over every possible
branching generation gives the corresponding finite aggregate estimate. -/
theorem sum_affineTubeMRCAPairContribution_le_of_drawdown
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (N : ℕ) (initial lower drift width endpointUpper : ℝ)
    (hdrift : 0 ≤ drift) (q : ℕ → ℝ≥0∞)
    (hdrawdown : ∀ n,
      (tiltedIncrementFieldLaw φ μ)
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          n width (width + drift * (n : ℝ))) ≤ q n) :
    (∑ m : Fin N, affineTubeMRCAPairContribution φ μ m.val
        (N - m.val - 1) initial lower drift width endpointUpper) ≤
      ∑ m : Fin N,
        ENNReal.ofReal (Real.exp (-(2 * initial))) *
          (ENNReal.ofReal (Real.exp (2 * endpointUpper)) *
            q (N - m.val - 1) ^ 2) *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (ENNReal.ofReal
            (Real.exp (initial - (lower + drift * (m.val : ℝ)))) *
            (tiltedIncrementFieldLaw φ μ)
              {increment | ProbabilityTheory.RandomWalk.history m.val initial increment ∈
                affineCorridorPrefix m.val lower drift width}) := by
  apply Finset.sum_le_sum
  intro m hm
  exact affineTubeMRCAPairContribution_le_of_drawdown
    φ μ hboundary m.val (N - m.val - 1) initial lower drift width endpointUpper
    hdrift (q (N - m.val - 1)) (hdrawdown (N - m.val - 1))

/-- The prefix endpoint lower bound removes one of the two reciprocal
potential factors in a positive-depth MRCA term. The remaining expectation is
the spine prefix probability times the cross-child moment. -/
theorem lintegral_weightedPrefixSquareCrossChildWeightSum_indicator_le
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (x lower : ℝ)
    (hlower : ∀ history ∈ corridor,
      lower ≤ history ⟨n, Nat.lt_succ_self n⟩) :
    (∫⁻ ω, weightedPrefixSquareCrossChildWeightSum φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ω
      ∂stepFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (x - lower)) *
        (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
        (tiltedIncrementFieldLaw φ μ)
          {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor} := by
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (x - lower))
  have hprefixMeas : Measurable (weightedPrefixCrossChildWeightSum φ n F x) := by
    unfold weightedPrefixCrossChildWeightSum
    apply Measurable.tsum
    intro u
    exact (weightedPathGenerationTerm_measurable φ n
      (measurable_const.indicator hcorridor) x u).mul
      ((crossChildWeight_measurable φ).comp (measurable_pi_apply u))
  have hterm (u : TreeNode ℕ) (ω : StepField ℕ X) :
      weightedPathGenerationTerm φ n F x u ω *
          ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
          crossChildWeight φ (ω u) ≤
        K * (weightedPathGenerationTerm φ n F x u ω *
          crossChildWeight φ (ω u)) := by
    by_cases hu : u.length = n
    · by_cases hs : surviveAlong ω [] u
      · by_cases hc : pathHistory φ n x ω u ∈ corridor
        · have hterminal := hlower (pathHistory φ n x ω u) hc
          rw [pathHistory_last φ n x ω u hu] at hterminal
          have hpotential : -pathPotential φ ω u ≤ x - lower := by linarith
          have hextra : ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) ≤ K := by
            exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hpotential)
          have hweight : weightedPathGenerationTerm φ n F x u ω =
              ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) := by
            simp [weightedPathGenerationTerm, F, hu, hs, hc]
          rw [hweight]
          dsimp [K]
          calc
            _ = ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
                (ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
                  crossChildWeight φ (ω u)) := by ac_rfl
            _ ≤ ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
                (ENNReal.ofReal (Real.exp (x - lower)) *
                  crossChildWeight φ (ω u)) := by gcongr
            _ = ENNReal.ofReal (Real.exp (x - lower)) *
                (ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
                  crossChildWeight φ (ω u)) := by ac_rfl
        · have hzero : weightedPathGenerationTerm φ n F x u ω = 0 := by
            simp [weightedPathGenerationTerm, F, hu, hs, hc]
          simp [hzero]
      · have hzero : weightedPathGenerationTerm φ n F x u ω = 0 := by
          simp [weightedPathGenerationTerm, hu, hs]
        simp [hzero]
    · have hzero : weightedPathGenerationTerm φ n F x u ω = 0 := by
        simp [weightedPathGenerationTerm, hu]
      simp [hzero]
  have hpoint (ω : StepField ℕ X) :
      weightedPrefixSquareCrossChildWeightSum φ n F x ω ≤
        K * weightedPrefixCrossChildWeightSum φ n F x ω := by
    unfold weightedPrefixSquareCrossChildWeightSum weightedPrefixCrossChildWeightSum
    calc
      _ ≤ ∑' u : TreeNode ℕ, K *
          (weightedPathGenerationTerm φ n F x u ω *
            crossChildWeight φ (ω u)) :=
        ENNReal.tsum_le_tsum (fun u => hterm u ω)
      _ = K * ∑' u : TreeNode ℕ,
          weightedPathGenerationTerm φ n F x u ω *
            crossChildWeight φ (ω u) := ENNReal.tsum_mul_left
  calc
    (∫⁻ ω, weightedPrefixSquareCrossChildWeightSum φ n F x ω
        ∂stepFieldLaw μ) ≤
        ∫⁻ ω, K * weightedPrefixCrossChildWeightSum φ n F x ω
          ∂stepFieldLaw μ := lintegral_mono hpoint
    _ = K * (∫⁻ ω, weightedPrefixCrossChildWeightSum φ n F x ω
          ∂stepFieldLaw μ) := lintegral_const_mul K hprefixMeas
    _ = K * ((∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (tiltedIncrementFieldLaw φ μ)
            {increment | ProbabilityTheory.RandomWalk.history n x increment ∈ corridor}) := by
      rw [lintegral_weightedPrefixCrossChildWeightSum_indicator_eq_crossMoment_mul_spineProbability
        φ μ hboundary n corridor hcorridor x]
    _ = _ := by ac_rfl

end ProbabilityTheory.BranchingRandomWalk.Spine
