/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingProcess.Offspring.Count
import Probability.BranchingProcess.Offspring.Law
import Probability.BranchingRandomWalk.Selection.NSelection.Tail.EndpointDeviationParameterSelection
import Probability.BranchingRandomWalk.Selection.NSelection.Tail.PolynomialEndpointSublevelHorizon
import Probability.BranchingRandomWalk.Spine.Variance
import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Selected-endpoint sublevel from the law assumptions

The law hypotheses in the paper-facing declaration are the boundary
normalization, supercriticality, zero spine mean, and finite spine variance
used for this endpoint direction. The arbitrary horizon and its
logarithmic-cube limit are the sequence input. The endpoint event itself is
direction-neutral; this adapter proves its lower-endpoint instance using the
left-side boundary and the spine law tilted at `-1`. The corresponding
OrderDual adapter under the right-side conditions remains to be formalized;
it does not require reflection invariance of the offspring law. All block,
rate, binning, and exponent parameters for this instance are derived
internally.
-/


open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- The deterministic tie break for a finite initial population and
Ulam--Harris descendants: first order by root label, then lexicographically by
the child-label word. -/
@[instance_reducible] noncomputable def root_address_linear_order (m : ℕ) :
    LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) := by
  letI : LinearOrder (Fin m ×ₗ List ℕ) := inferInstance
  exact LinearOrder.lift'
    (fun x : RootIndexed.TreeNode (Fin m) ℕ => toLex (x.1, x.2))
    (by
      intro x y h
      exact toLex.injective h)

/-- The arbitrary-horizon endpoint sublevel under the displayed individual
law assumptions. The variance, positive variance parameter, and all geometric
and exponent parameters are derived from those assumptions. -/
theorem eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_polynomial_of_boundary_and_spine_assumptions
    {L : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ}
    (hboundary : HasBoundaryNormalization realPotential
      (L : Measure (Step ℕ ℝ)))
    (hsupercritical : L.IsSupercritical)
    (hspineMean : (∫ y : ℝ, y ∂tiltedPotentialLaw realPotential (-1)
      (L : Measure (Step ℕ ℝ))) = 0)
    (hspineFiniteVariance : MemLp id 2
      (tiltedPotentialLaw realPotential (-1) (L : Measure (Step ℕ ℝ))))
    {m N horizon : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {a t zeta : ℝ} (ha_one : a ≤ 1) (ht : 0 < t)
    (hhorizon : Tendsto
      (fun n => (horizon n : ℝ) / logarithmOfSampleSize N n ^ 3)
      atTop (𝓝 t))
    (hbelow : zeta < -a + (Real.pi ^ 2 / 2) *
      (∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw realPotential (-1)
        (L : Measure (Step ℕ ℝ))) * t)
    (hmPow : ∀ᶠ n : ℕ in atTop,
      (m n : ℝ) ≤ (N n : ℝ) ^ a) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      (finiteRootStepFieldLaw (L : Measure (Step ℕ ℝ)) (m n))
        (@firstNSelectedEndpointBelow (m n) (N n)
          (horizon n) (root_address_linear_order (m n))
          (logarithmicEndpointThreshold N zeta n)) ≤
        ENNReal.ofReal
          (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
  let μ : Measure (Step ℕ ℝ) := L
  let ν : Measure ℝ := tiltedPotentialLaw realPotential (-1) μ
  let variance : ℝ := ∫ y : ℝ, y ^ 2 ∂ν
  have hvarianceIntegrable : Integrable (fun y : ℝ => y ^ 2) ν :=
    (memLp_two_iff_integrable_sq
      stronglyMeasurable_id.aestronglyMeasurable).1 hspineFiniteVariance
  have hspineMomentVariance : IsCenteredSecondMoment ν variance := by
    refine ⟨?_, ?_⟩
    · simpa [ν, μ] using hspineMean
    · rfl
  have hvariancePos : 0 < variance :=
    spine_secondMoment_pos_of_normalized_supercritical L hboundary
      hsupercritical hspineMomentVariance hvarianceIntegrable
  let sigma : ℝ := Real.sqrt variance
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact Real.sqrt_pos.2 hvariancePos
  have hsigmaSq : sigma ^ 2 = variance := by
    dsimp [sigma]
    exact Real.sq_sqrt hvariancePos.le
  have hspineMoment : IsCenteredSecondMoment ν (sigma ^ 2) := by
    refine ⟨?_, ?_⟩
    · simpa [ν, μ] using hspineMean
    · rw [hsigmaSq]
  have hbelowSigma : zeta < -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t := by
    simpa [variance, ν, μ, hsigmaSq] using hbelow
  obtain ⟨b, factor, eta, rangeRate, targetRate, k, hk,
      hb, hfactor, heta, hrangeRate, hrangeRateLt, htargetRate, hgap,
      hbin, hmargin⟩ :=
    exists_endpoint_sublevel_parameters_of_diffusive_gap (a := a) (t := t) (zeta := zeta)
      (sigma := sigma) ht hsigma hbelowSigma
  have hbound :=
    eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_polynomial_of_horizonRawRate
      μ hboundary hspineMoment hsigma (m := m) (N := N) hN
      (fun n => root_address_linear_order (m n))
      (horizon := horizon) (a := a) (t := t) (zeta := zeta) (b := b)
      (factor := factor)
      (eta := eta) (rangeRate := rangeRate) (targetRate := targetRate)
      ha_one ht hb hhorizon hfactor heta hrangeRate k hk hrangeRateLt htargetRate
      (by simpa [logarithmicRateBeta] using hgap) hbin hmPow hmargin
  simpa [μ] using hbound

/-- The endpoint sublevel estimate with the logarithmic population size, horizon
sequence, and endpoint threshold. The assumptions are stated individually,
and the finite-root order is supplied by a deterministic address order. -/
theorem eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_polynomial_of_logarithmic_scales
    {L : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ}
    (hboundary : HasBoundaryNormalization realPotential
      (L : Measure (Step ℕ ℝ)))
    (hsupercritical : L.IsSupercritical)
    (hspineMean : (∫ y : ℝ, y ∂tiltedPotentialLaw realPotential (-1)
      (L : Measure (Step ℕ ℝ))) = 0)
    (hspineFiniteVariance : MemLp id 2
      (tiltedPotentialLaw realPotential (-1) (L : Measure (Step ℕ ℝ))))
    {horizon : ℕ → ℕ} {a t zeta : ℝ}
    (_ha_zero : 0 ≤ a) (ha_one : a ≤ 1) (ht : 0 < t)
    (hhorizon : Tendsto
      (fun n : ℕ => (horizon n : ℝ) / Real.log (n : ℝ) ^ 3)
      atTop (𝓝 t))
    (hbelow : zeta < -a + (Real.pi ^ 2 / 2) *
      (∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw realPotential (-1)
        (L : Measure (Step ℕ ℝ))) * t) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      (finiteRootStepFieldLaw (L : Measure (Step ℕ ℝ))
          (Nat.floor ((n : ℝ) ^ a)))
        (@firstNSelectedEndpointBelow (Nat.floor ((n : ℝ) ^ a)) n
          (horizon n)
          (root_address_linear_order (Nat.floor ((n : ℝ) ^ a)))
          (zeta * Real.log (n : ℝ))) ≤
        ENNReal.ofReal (Real.exp (-epsilon * Real.log (n : ℝ))) := by
  have hN : Tendsto (fun n : ℕ => n) atTop atTop := tendsto_id
  let m : ℕ → ℕ := fun n => Nat.floor ((n : ℝ) ^ a)
  have hmPow : ∀ᶠ n : ℕ in atTop, (m n : ℝ) ≤ (n : ℝ) ^ a := by
    filter_upwards [hN.eventually_ge_atTop 1] with n hn
    dsimp [m]
    exact Nat.floor_le (by positivity)
  let μ : Measure (Step ℕ ℝ) := L
  let ν : Measure ℝ := tiltedPotentialLaw realPotential (-1) μ
  let variance : ℝ := ∫ y : ℝ, y ^ 2 ∂ν
  have hvarianceIntegrable : Integrable (fun y : ℝ => y ^ 2) ν :=
    (memLp_two_iff_integrable_sq
      stronglyMeasurable_id.aestronglyMeasurable).1 hspineFiniteVariance
  have hspineMomentVariance : IsCenteredSecondMoment ν variance := by
    refine ⟨?_, ?_⟩
    · simpa [ν, μ] using hspineMean
    · rfl
  have hvariancePos : 0 < variance :=
    spine_secondMoment_pos_of_normalized_supercritical L hboundary
      hsupercritical hspineMomentVariance hvarianceIntegrable
  let sigma : ℝ := Real.sqrt variance
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact Real.sqrt_pos.2 hvariancePos
  have hsigmaSq : sigma ^ 2 = variance := by
    dsimp [sigma]
    exact Real.sq_sqrt hvariancePos.le
  have hspineMoment : IsCenteredSecondMoment ν (sigma ^ 2) := by
    refine ⟨?_, ?_⟩
    · simpa [ν, μ] using hspineMean
    · rw [hsigmaSq]
  have hbelowSigma : zeta < -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t := by
    simpa [variance, ν, μ, hsigmaSq] using hbelow
  have horder (n : ℕ) :
      LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ) :=
    root_address_linear_order (m n)
  obtain ⟨b, factor, eta, rangeRate, targetRate, k, hk,
      hb, hfactor, heta, hrangeRate, hrangeRateLt, htargetRate, hgap,
      hbin, hmargin⟩ :=
    exists_endpoint_sublevel_parameters_of_diffusive_gap (a := a) (t := t) (zeta := zeta)
      (sigma := sigma) ht hsigma hbelowSigma
  have hbound :=
    eventually_finiteRootStepFieldLaw_firstNSelectedEndpointBelow_le_polynomial_of_boundary_and_spine_assumptions
      hboundary hsupercritical hspineMean hspineFiniteVariance
      (m := m) (N := fun n : ℕ => n) (horizon := horizon) hN
      (a := a) (t := t) (zeta := zeta) ha_one ht
      (by simpa [logarithmOfSampleSize] using hhorizon)
      hbelow (by simpa [m] using hmPow)
  simpa [μ, m, logarithmicEndpointThreshold, logarithmOfSampleSize] using hbound

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
