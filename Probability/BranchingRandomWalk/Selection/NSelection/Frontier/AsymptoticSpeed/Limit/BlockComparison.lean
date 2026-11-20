/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.InitialPopulation.Speed.Transport
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.FirstMoment
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.Lemmas.SingleRootBlock
import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Continuation

/-!
# Finite-horizon upper comparison for the speed

## Public declarations

* `speed_le_singleRootEndpointMean_div`: for the common $L^1$ speed
  $v_N$ and each positive horizon $H$,
  $v_N\le H^{-1}\mathbb E[M_H^{N|0}]$. The comparison requires
  boundary normalization, nonempty offspring, and the leftmost first moment.

This is the single-root block comparison in Wang Yiyang, *Asymptotic Speed
of the N-Branching Random Walk with Infinite Offspring* (Fudan University,
2026), Theorem 1.2.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open EndpointDeviation

noncomputable local instance speedBlockAddressOrder (s : ℕ) :
    LinearOrder (RootIndexed.TreeNode (Fin s) ℕ) :=
  RootIndexed.addressLinearOrder (Fin s) ℕ

/-- Starting every block at one particle at the current minimum gives the
finite-horizon upper bound for the speed. -/
public theorem speed_le_singleRootEndpointMean_div
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hne : L.raw nonemptySupport = 1) (hfirst : HasLeftmostFirstMoment L)
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    {speed : ℝ}
    (hL1 : Tendsto (fun n : ℕ => eLpNorm (fun field =>
      (n : ℝ)⁻¹ * @selectedPopulationEndpointTrajectoryWithParameter N _
        (RootIndexed.addressLinearOrder (Fin N) ℕ)
        ((fun _ => 0), field) n - speed) 1
      (finiteRootStepFieldLaw L.sortedPotentialImage N)) atTop (𝓝 0)) :
    speed ≤ (∫ field, @firstNSelectedEndpointMinimum 1 N H
      (RootIndexed.addressLinearOrder (Fin 1) ℕ) field
      ∂finiteRootStepFieldLaw L.sortedPotentialImage 1) / H := by
  let μ := L.sortedPotentialImage
  have hboundary' := L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hne' : μ nonemptySupport = 1 := by
    dsimp [μ]
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport, hne]
  have hmoment (m n : ℕ) (hm : 0 < m) :
      Integrable (fun field =>
        RootIndexed.selectedPopulationEndpointWithParameter m N n ((fun _ => 0), field))
        (RootIndexed.stepFieldLaw μ) := by
    have h := finiteRootStepFieldLaw_integrable_firstNSelectedEndpointMinimum
      m N n hm hN L hboundary hne hfirst
    exact h.congr (Eventually.of_forall
      (firstNSelectedEndpointMinimum_eq_endpointWithParameter_zero m N n))
  have hb := speed_le_integral_singleRootEndpoint_div hN hH μ hboundary' hne' speed
    (fun n => hmoment N n hN) (hmoment 1 H Nat.one_pos) hL1
  have heq : (∫ field, RootIndexed.selectedPopulationEndpointWithParameter
      1 N H ((fun _ => 0), field) ∂RootIndexed.stepFieldLaw μ) =
      ∫ field, firstNSelectedEndpointMinimum 1 N H field ∂finiteRootStepFieldLaw μ 1 :=
    integral_congr_ae (Eventually.of_forall fun field =>
      (firstNSelectedEndpointMinimum_eq_endpointWithParameter_zero 1 N H field).symm)
  rw [heq] at hb
  exact hb

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
