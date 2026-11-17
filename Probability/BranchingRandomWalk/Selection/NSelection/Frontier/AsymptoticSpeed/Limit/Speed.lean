/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.BlockComparison
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.RestartMean
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.SpeedLowerBound
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.Lemmas.RemainingHorizon

/-!
# The asymptotic speed of the N-branching random walk

## Public declarations

* `exists_speed_with_logSq_limit`: from each deterministic nonempty
  initial population of size at most $N$, the minimum divided by time
  converges almost surely and in $L^1$ to the common speed $v_N$.
  Under boundary normalization and the stated offspring moment assumptions,
  $v_N(\log N)^2\to\pi^2\sigma^2/2$.

This is Theorem 1.2 of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (Fudan University, 2026), Chapter 4.
-/

open Asymptotics MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open EndpointDeviation ProbabilityTheory.BranchingRandomWalk.Spine

noncomputable local instance (m : ℕ) : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
  RootIndexed.addressLinearOrder (Fin m) ℕ

private lemma eventually_logSq_mul_speed_lt
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hfour : HasLeftmostFourthMoment L)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (speed : ℕ → ℝ)
    (hL1 : ∀ N : ℕ, 0 < N →
      Tendsto (fun n : ℕ => eLpNorm (fun field =>
        (n : ℝ)⁻¹ * selectedPopulationEndpointTrajectoryWithParameter N
          ((fun _ => 0), field) n - speed N) 1
        (finiteRootStepFieldLaw L.sortedPotentialImage N)) atTop (𝓝 0))
    {r : ℝ} (hr : (Real.pi ^ 2 / 2) * sigma ^ 2 < r) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ 2 * speed n < r := by
  let c := (Real.pi ^ 2 / 2) * sigma ^ 2
  let t := 12 / (r - c)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hgap : 0 < r - c := sub_pos.mpr hr
  have ht : 0 < t := div_pos (by norm_num) hgap
  have hrpos : 0 < r := hc.trans_lt hr
  have htarget : (c * t + 6) / r < t := by
    apply (div_lt_iff₀ hrpos).2
    have heq : t * (r - c) = 12 := div_mul_cancel₀ _ hgap.ne'
    linarith only [heq, show c * t + t * (r - c) = t * r by ring]
  let N : ℕ → ℕ := Nat.succ
  have hN : Tendsto N atTop atTop := tendsto_add_atTop_nat 1
  let H := logarithmicHorizon N t
  have hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t) :=
    logarithmicHorizon_div_logCube_tendsto hN ht
  let μ := L.sortedPotentialImage
  have hremaining (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (T : ℕ → ℕ)
      (hT : Tendsto (fun n => (T n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 0)) :
      ∀ᶠ n in atTop, ∀ i ≤ T n,
        (∫ field, firstNSelectedEndpointMinimum ⌊(N n : ℝ) ^ a⌋₊ (N n) (H n - i) field
             ∂finiteRootStepFieldLaw μ ⌊(N n : ℝ) ^ a⌋₊) ≤
          (c * t + 1) * Real.log (N n : ℝ) := by
    have hmean := eventually_endpointMean_sub_horizon_le L hsuper hnonempty hboundary hcross hfour
      hsigma hspine ha ha1 ht one_pos (fun n => Nat.succ_pos n) hN hH hT
    filter_upwards [hmean, eventually_gt_atTop (0 : ℕ)] with n hn hpos i hi
    have hlog : 0 < Real.log (N n : ℝ) :=
      Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hpos)
    let m := ⌊(N n : ℝ) ^ a⌋₊
    have hone : 1 ≤ (N n : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hm : 0 < m := Nat.floor_pos.mpr (Real.one_le_rpow hone ha.le)
    let F := firstNSelectedEndpointMinimum m (N n) (H n - i)
    have hI : Integrable F (finiteRootStepFieldLaw μ m) :=
      finiteRootStepFieldLaw_integrable_firstNSelectedEndpointMinimum m (N n) (H n - i)
        hm (Nat.succ_pos n) L hboundary hnonempty (fourthMoment_implies_firstMoment L hfour)
    have hcomp := (RootIndexed.StepField.measurePreserving_first μ m).integral_comp_of_integrable hI
    have h := hn i hi
    change (∫ field, F (RootIndexed.StepField.first m field) / Real.log (N n : ℝ)
        ∂RootIndexed.stepFieldLaw (Root := ℕ) μ) ≤ -a + c * t + 1 at h
    rw [integral_div, hcomp] at h
    exact (div_le_iff₀ hlog).mp (h.trans (by linarith))
  have hup := eventually_singleRootEndpointMean_div_log_le_of_remainingMean
    L hsuper hnonempty hboundary hfour hc ht hN hH hremaining
  suffices hs : ∀ᶠ n : ℕ in atTop, Real.log (N n : ℝ) ^ 2 * speed (N n) < r by
    obtain ⟨k, hk⟩ := eventually_atTop.mp hs
    refine eventually_atTop.mpr ⟨k + 1, ?_⟩
    intro n hn
    cases n with
    | zero => omega
    | succ n => exact hk n (by omega)
  filter_upwards [hup, hH.eventually (lt_mem_nhds htarget), eventually_gt_atTop (0 : ℕ)]
    with n hup_n hscale hn
  have hlog : 0 < Real.log (N n : ℝ) := Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hn)
  have hHpos : 0 < H n := Nat.succ_pos _
  let mean := ∫ field, firstNSelectedEndpointMinimum 1 (N n) (H n) field
    ∂finiteRootStepFieldLaw μ 1
  have hblock : speed (N n) ≤ mean / H n :=
    speed_le_singleRootEndpointMean_div L hboundary hnonempty
      (fourthMoment_implies_firstMoment L hfour) (Nat.succ_pos n) hHpos (hL1 (N n) (Nat.succ_pos n))
  have hHreal : 0 < (H n : ℝ) := by exact_mod_cast hHpos
  have hscalePos : 0 < (H n : ℝ) / Real.log (N n : ℝ) ^ 3 := by positivity
  calc
    _ ≤ Real.log (N n : ℝ) ^ 2 * (mean / H n) :=
      mul_le_mul_of_nonneg_left hblock (sq_nonneg _)
    _ = (mean / Real.log (N n : ℝ)) / ((H n : ℝ) / Real.log (N n : ℝ) ^ 3) := by
      field_simp [hHreal.ne', hlog.ne']
    _ ≤ (c * t + 6) / ((H n : ℝ) / Real.log (N n : ℝ) ^ 3) :=
      div_le_div_of_nonneg_right hup_n hscalePos.le
    _ < r := (div_lt_iff₀ hscalePos).2 (by
      have h := (div_lt_iff₀ hrpos).mp hscale
      simpa only [mul_comm r] using h)

/-- Common speed and its logarithmic asymptotic, from the two block comparisons. -/
theorem exists_speed_with_logSq_limit
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hfour : HasLeftmostFourthMoment L)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2)) :
    ∃ speed : ℕ → ℝ,
      (∀ N m : ℕ, 0 < m → m ≤ N → ∀ initial : Fin m → ℝ,
        let P := finiteRootStepFieldLaw L.sortedPotentialImage m
        let endpoint := fun field n =>
          RootIndexed.selectedPopulationEndpointWithParameter m N n (initial, field)
        (∀ᵐ field ∂P, HasAsymptoticSpeed (𝕜 := ℝ) (endpoint field) (speed N)) ∧
        Tendsto (fun n : ℕ => eLpNorm (fun field =>
          (n : ℝ)⁻¹ * endpoint field n - speed N) 1 P) atTop (𝓝 0)) ∧
      Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2 * speed N) atTop
        (𝓝 ((Real.pi ^ 2 / 2) * sigma ^ 2)) := by
  obtain ⟨speed, hspeed, hlow⟩ := exists_speed_with_logSq_lowerBound L hsuper hnonempty
    hboundary hcross hfour hsigma hspine
  refine ⟨speed, hspeed, tendsto_order.2 ⟨hlow, ?_⟩⟩
  intro r hr
  apply eventually_logSq_mul_speed_lt L hsuper hnonempty hboundary hcross hfour hsigma hspine
    speed _ hr
  intro N hN
  have h := (hspeed N N hN le_rfl (fun _ => 0)).2
  simpa only [selectedPopulationEndpointTrajectoryWithParameter] using h

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
