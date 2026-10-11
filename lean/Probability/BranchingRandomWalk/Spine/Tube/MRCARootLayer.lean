/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Tube.RightTailOneGeneration
import Probability.BranchingRandomWalk.Assumptions.CrossWeight
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The root MRCA layer of the long-corridor second moment

For a generation-`n + 1` tube count, the off-diagonal term at its root is
exactly the contribution of pairs whose most recent common ancestor is the
root.  This file specializes the one-generation branching estimate to the
affine tube and endpoint cutoff from Lemma 4.5.  It derives this root layer
from a segment-probability estimate and the finite cross-child moment; it does
not yet sum the layers with positive MRCA depth.
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

/-- The root MRCA layer is the off-diagonal term in the one-step second
moment recursion for the affine tube count. The other term keeps the two
paths in the same first-generation subtree and therefore contains all deeper
MRCA layers. -/
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

/-- The root MRCA layer is bounded by the finite cross-child moment once the
shifted continuation probability has a uniform upper bound. -/
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

/-- The source's small-drift Mogulskii bound gives an explicit estimate for
the root MRCA layer. Here `hsegment` is precisely the remaining segment
probability input from Lemma 4.2, with the drawdown event obtained from the
affine tube geometry. -/
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

/-- Finiteness of the cross-child moment lets the paper's fixed constant be
absorbed into `exp(width ^ v)` for all sufficiently large tube widths. This
is the only use of the large-width threshold in the root-layer estimate. -/
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
factor, the root layer has the same `3 * width^v` loss as the corresponding
single summand of Lemma 4.5. The remaining layers still require the
generation-`m` prefix estimate. -/
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

/-- In particular, the root MRCA layer is finite under the paper's
finite cross-child condition whenever the segment-probability bound is
finite. This is a derived finiteness result, not a pair-moment assumption. -/
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

/-- Under the paper's finite cross-weight condition, the explicit
Mogulskii-controlled root layer is finite. -/
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

private theorem displaceWith_measurable_generation
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

private theorem pathHistory_measurable_generation
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

private theorem weightedPathGenerationTerm_measurable_generation
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

/-- The frontier cross-child weight is independent of the generation-`n`
prefix. Consequently the expected weighted prefix/cross-weight sum factors
exactly into the finite cross-child moment and the spine prefix integral. This
is the ancestor-side factor in each positive-depth MRCA layer. -/
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
layer of Lemma 4.5. -/
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
