/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.PositiveInitialExponent
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization

/-!
# Uniform endpoint upper bound for a short stopping-time window

## Public declarations

* `eventually_countableRootEndpointMinimum_ge_le_polynomial_sub_horizon`:
  if $H_n/(\log N_n)^3\to t>0$ and $T_n/(\log N_n)^3\to0$, then the
  positive-exponent upper bound at $\zeta\log N_n$ holds simultaneously at
  all horizons $H_n-i$, $0\le i\le T_n$, with a common positive exponent.
* `eventually_stoppedSubtreeEndpoint_ge_le_polynomial_sub_horizon`: for
  a stopped vector of distinct roots and a stopped event $A_n$,
  $\mathbb P(A_n,\tau_n\le T_n,M^{\mathrm{fresh}}_{H_n-\tau_n}
  \ge\zeta\log N_n)\le\mathbb P(A_n,\tau_n\le T_n)N_n^{-p}$
  eventually. The fresh endpoint starts all selected roots at zero.

This is the uniform consequence of the positive-exponent estimate used at the
stopping time in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring* (Fudan University, 2026), Chapter 4, Theorem 1.1,
case $a=0$.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- The polynomial upper bound is uniform over the remaining horizons at the
restart time in Theorem 1.1 of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (Fudan University, 2026), Chapter 4. -/
theorem eventually_countableRootEndpointMinimum_ge_le_polynomial_sub_horizon
    {N H T : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    {sigma a t ζ : ℝ} (hsigma : 0 < sigma)
    (hcentered : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hgap : -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t < ζ)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (hT : Tendsto (fun n => (T n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 0))
    (horder : ∀ n, LinearOrder
      (RootIndexed.TreeNode (Fin (Nat.floor ((N n : ℝ) ^ a))) ℕ)) :
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop, ∀ i ≤ T n,
      (RootIndexed.stepFieldLaw (Root := ℕ) μ)
        {field | ζ * Real.log (N n : ℝ) ≤
          @countableRootEndpointMinimum (Nat.floor ((N n : ℝ) ^ a)) (N n)
            (H n - i) (horder n) field} ≤ ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) := by
  classical
  let L (n : ℕ) := Real.log (N n : ℝ)
  let m (n : ℕ) := Nat.floor ((N n : ℝ) ^ a)
  let P := RootIndexed.stepFieldLaw (Root := ℕ) μ
  let bad (n i : ℕ) := P {field | ζ * L n ≤
    @countableRootEndpointMinimum (m n) (N n) (H n - i) (horder n) field}
  let bound (p : ℝ) (n : ℕ) := ENNReal.ofReal (Real.exp (-p * L n))
  change ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop, ∀ i ≤ T n, bad n i ≤ bound p n
  by_contra! h
  have hchoose (k : ℕ) :
      ∃ n ≥ k, ∃ i ≤ T n, bound (1 / ((k : ℝ) + 1)) n < bad n i := by
    have hk := h (1 / ((k : ℝ) + 1)) (by positivity)
    rw [Filter.frequently_atTop] at hk
    exact hk k
  choose n hn i hi hbad using hchoose
  have hnTop : Tendsto n atTop atTop := tendsto_atTop.2 fun k =>
    (eventually_ge_atTop k).mono fun j hj => hj.trans (hn j)
  have hlog : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hTH : ∀ᶠ j in atTop, T j ≤ H j := by
    filter_upwards [hlog.eventually_gt_atTop 0,
      hT.eventually (Iio_mem_nhds (show (0 : ℝ) < t / 2 by positivity)),
      hH.eventually (Ioi_mem_nhds (show t / 2 < t by linarith))] with j hLj hs hh
    exact_mod_cast ((div_lt_div_iff_of_pos_right (pow_pos hLj 3)).mp (hs.trans hh)).le
  have hsmall : Tendsto (fun k => (i k : ℝ) / L (n k) ^ 3) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (hT.comp hnTop)
    · filter_upwards [(hlog.comp hnTop).eventually_gt_atTop 0] with k hk
      positivity
    · filter_upwards [(hlog.comp hnTop).eventually_gt_atTop 0] with k hk
      exact div_le_div_of_nonneg_right (by exact_mod_cast hi k) (pow_pos hk 3).le
  have hremaining : Tendsto (fun k => ((H (n k) - i k : ℕ) : ℝ) / L (n k) ^ 3)
      atTop (𝓝 t) := by
    have hdiff := (hH.comp hnTop).sub hsmall
    rw [sub_zero] at hdiff
    apply hdiff.congr'
    filter_upwards [hnTop.eventually hTH] with k hk
    simp [L, Nat.cast_sub ((hi k).trans hk), sub_div]
  obtain ⟨p, hp, htail⟩ :=
    eventually_countableRootEndpointMinimum_ge_le_polynomial_of_initialExponent
      (hN.comp hnTop) μ hboundary hcross hsigma hcentered ha ha1 ht hgap hremaining
      (fun k => horder (n k))
  have hone : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hcontr : ∀ᶠ k : ℕ in atTop, False := by
    filter_upwards [htail, (hlog.comp hnTop).eventually_gt_atTop 0,
      hone.eventually (Iio_mem_nhds hp)] with k ht hk hp'
    have hcmp : bound p (n k) ≤ bound (1 / ((k : ℝ) + 1)) (n k) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (neg_le_neg hp'.le) hk.le))
    exact (hbad k).not_ge (ht.trans hcmp)
  obtain ⟨k, hk⟩ := eventually_atTop.mp hcontr
  exact hk k le_rfl

/-- The positive-exponent bound for a continuation at a short stopping
time, with its starting locations reset to zero. This is the fresh-forest
probability in the proof of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (Fudan University, 2026), Chapter 4,
Theorem 1.1, case $a=0$. -/
theorem eventually_stoppedSubtreeEndpoint_ge_le_polynomial_sub_horizon
    {Root : Type*} {N H T : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    {sigma a t ζ : ℝ} (hsigma : 0 < sigma)
    (hcentered : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hgap : -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t < ζ)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (hT : Tendsto (fun n => (T n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 0))
    (horder : ∀ n, LinearOrder
      (RootIndexed.TreeNode (Fin (Nat.floor ((N n : ℝ) ^ a))) ℕ))
    (τ : ℕ → RootIndexed.StepField Root ℕ ℝ → WithTop ℕ)
    (hτ : ∀ n, IsStoppingTime (RootIndexed.stepFiltration (Root := Root) (α := ℕ) (X := ℝ))
      (τ n))
    (A : ℕ → Set (RootIndexed.StepField Root ℕ ℝ))
    (hA : ∀ n, MeasurableSet[(hτ n).measurableSpace] (A n))
    (roots : ∀ n, RootIndexed.StepField Root ℕ ℝ →
      Fin (Nat.floor ((N n : ℝ) ^ a)) → RootIndexed.TreeNode Root ℕ)
    (hcount : ∀ n, (Set.range (roots n)).Countable)
    (hfiber : ∀ n r, MeasurableSet[(hτ n).measurableSpace] {field | roots n field = r})
    (hdepth : ∀ n field (i : ℕ), τ n field = (i : WithTop ℕ) →
      ∀ j, (roots n field j).2.length = i)
    (hinj : ∀ n field, τ n field ≠ ⊤ → Function.Injective (roots n field)) :
    let P := RootIndexed.stepFieldLaw (Root := Root) μ
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
      P {field | field ∈ A n ∧ ∃ i ≤ T n, τ n field = (i : WithTop ℕ) ∧
        ζ * Real.log (N n : ℝ) ≤
          @firstNSelectedEndpointMinimum (Nat.floor ((N n : ℝ) ^ a)) (N n)
            (H n - i) (horder n) (RootIndexed.selectedSubtreeStepFieldVector (roots n) field)} ≤
        P (A n ∩ {field | τ n field ≤ (T n : WithTop ℕ)}) *
          ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) := by
  intro P
  obtain ⟨p, hp, hwindow⟩ :=
    eventually_countableRootEndpointMinimum_ge_le_polynomial_sub_horizon hN μ hboundary
      hcross hsigma hcentered ha ha1 ht hgap hH hT horder
  refine ⟨p, hp, ?_⟩
  filter_upwards [hwindow] with n hn
  let _ := horder n
  let m := Nat.floor ((N n : ℝ) ^ a)
  let x := ζ * Real.log (N n : ℝ)
  let B (i : ℕ) := {field | x ≤ firstNSelectedEndpointMinimum m (N n) (H n - i) field}
  have hB (i : ℕ) : MeasurableSet (B i) :=
    (measurable_firstNSelectedEndpointMinimum m (N n) (H n - i)) measurableSet_Ici
  have hbound (i : ℕ) (hi : i ≤ T n) :
      (finiteRootStepFieldLaw μ m) (B i) ≤ ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) := by
    have hmap := congrArg (fun law : Measure ℝ => law (Set.Ici x))
      (countableRootEndpointMinimum_map_eq μ m (N n) (H n - i))
    rw [Measure.map_apply (measurable_countableRootEndpointMinimum m (N n) (H n - i))
        measurableSet_Ici,
      Measure.map_apply (measurable_firstNSelectedEndpointMinimum m (N n) (H n - i))
        measurableSet_Ici] at hmap
    exact hmap.ge.trans (hn i hi)
  exact RootIndexed.stopped_selectedSubtreeStepFieldVector_measure_test_le
    μ (τ n) (hτ n) (roots n) (hcount n) (hfiber n) (hdepth n) (hinj n)
    (A n) (hA n) B hB (T n) _ hbound

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
