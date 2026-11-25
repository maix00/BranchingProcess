/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.CountableRoots
public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Probability.BranchingRandomWalk.Assumptions.SpinalWeightTail
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.UpperTail.Lemmas.SpinalWeight.Parameters
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.UpperTail.Lemmas.SpinalWeight.Logarithmic
public import Probability.Distributions.Moments.Real

/-!
# Endpoint upper tail with a positive initial exponent

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_countableRootEndpointMinimum_ge_le_polynomial_of_spinalWeightTail`:
  the same endpoint conclusion holds with `HasSpinalWeightTail` instead of a
  finite cross-child weight, retaining only the original finite spinal variance:
  for `0<a<1`, `H_n/log³N_n→t>0` and `ζ>-a+π²σ²t/2`,
  `P(M_n≥ζ log N_n)≤N_n^(-p)` eventually for some `p>0`.

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_countableRootEndpointMinimum_ge_le_polynomial_of_initialExponent`:
  when $0<a<1$, $H_n/(\log N_n)^3\to t>0$, and
  $\zeta>-a+\pi^2\sigma^2t/2$, the minimum $M_n$ from
  $\lfloor N_n^a\rfloor$ zero-position roots at capacity $N_n$ satisfies
  $\mathbb P(M_n\ge\zeta\log N_n)\le N_n^{-p}$ eventually for some $p>0$.
  This finite-cross-weight specialization derives from the weak-tail theorem;
  its former separate two-stage proof is removed.

This is the positive-exponent case of the endpoint upper-tail estimate in
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 4, proof of Theorem 1.1.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- The positive-initial-exponent polynomial endpoint tail under Mallein's
weak reproductive condition (1.9). The strict logarithmic margins instantiate
the cutoff-moment argument of B. Mallein, *N-branching random walk with
α-stable spine*, Lemma 3.4, arXiv:1503.03762v2, on the endpoint scales of
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 4, Theorem 1.1. -/
theorem eventually_countableRootEndpointMinimum_ge_le_polynomial_of_spinalWeightTail
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (htail : HasSpinalWeightTail realPotential μ)
    {sigma a t ζ : ℝ} (hsigma : 0 < sigma)
    (hcentered : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hgap : -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t < ζ)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (horder : ∀ n, LinearOrder
      (RootIndexed.TreeNode (Fin (Nat.floor ((N n : ℝ) ^ a))) ℕ)) :
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
      (RootIndexed.stepFieldLaw (Root := ℕ) μ)
        {field | ζ * Real.log (N n : ℝ) ≤
          @countableRootEndpointMinimum (Nat.floor ((N n : ℝ) ^ a)) (N n) (H n) (horder n)
            field} ≤ ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) := by
  let κ := (Real.pi ^ 2 / 2) * sigma ^ 2
  have hκ : 0 < κ := mul_pos (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num))
    (sq_pos_of_pos hsigma)
  obtain ⟨w, α, a₀, b₀, ρ, dUpper, dLower, β, hw, hα, hρ, _,
    ha₀, ha₀', hb₀, hb₀', hdUpper, hUpper, hLower, _, hβ, hroot, hcap, hend⟩ :=
    exists_weakTail_logarithmicParameters ha ha1 hκ hgap
  exact eventually_endpointUpperTail_of_weakTail_logarithmicMargins hN μ hboundary htail
    hsigma hcentered ha ht hw hα ha₀ ha₀' hb₀ hb₀' hρ hdUpper hUpper hLower
    hβ hroot hcap hend hH horder

/-- The case $0<a<1$ of the upper-tail estimate in Wang Yiyang's
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, proof of Theorem 1.1. -/
theorem eventually_countableRootEndpointMinimum_ge_le_polynomial_of_initialExponent
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    {sigma a t ζ : ℝ} (hsigma : 0 < sigma)
    (hcentered : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hgap : -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t < ζ)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (horder : ∀ n, LinearOrder
      (RootIndexed.TreeNode (Fin (Nat.floor ((N n : ℝ) ^ a))) ℕ)) :
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
      (RootIndexed.stepFieldLaw (Root := ℕ) μ)
        {field | ζ * Real.log (N n : ℝ) ≤
          @countableRootEndpointMinimum (Nat.floor ((N n : ℝ) ^ a)) (N n) (H n) (horder n)
            field} ≤ ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) := by
  have hsq : Integrable (fun x : ℝ => x ^ 2) (tiltedPotentialLaw realPotential (-1) μ) :=
    Integrable.of_integral_ne_zero (by rw [hcentered.2]; exact pow_ne_zero 2 hsigma.ne')
  exact eventually_countableRootEndpointMinimum_ge_le_polynomial_of_spinalWeightTail
    hN μ hboundary (hcross.hasSpinalWeightTail realPotential μ hboundary hsq)
    hsigma hcentered ha ha1 ht hgap hH horder

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
