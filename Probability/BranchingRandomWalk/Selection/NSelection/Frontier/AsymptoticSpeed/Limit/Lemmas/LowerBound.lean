/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.L2Limit
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.InitialPopulation.Speed.Transport

/-!
# Lower bound for the logarithmically rescaled speed

For Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring* (Fudan University, 2026), Theorem 1.2, the full-capacity
estimate at a horizon of order $t\log^3N$ gives
$\liminf_{N\to\infty} v_N\log^2N\ge\pi^2\sigma^2/2-1/t$.
Taking $t\to\infty$ gives the lower bound.

## Internal proof declarations

* `eventually_lt_logSq_mul_speed`: every real $r<\pi^2\sigma^2/2$ lies below
  $v_N\log^2N$ for all sufficiently large capacities.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open EndpointDeviation ProbabilityTheory.BranchingRandomWalk.Spine

noncomputable local instance blockLowerAddressOrder (m : ℕ) : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
  RootIndexed.addressLinearOrder (Fin m) ℕ

/-- The full-capacity half of the speed estimate in Wang Yiyang,
Theorem 1.2, follows from the endpoint limit at $a=1$. -/
lemma eventually_lt_logSq_mul_speed
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
    {r : ℝ} (hr : r < (Real.pi ^ 2 / 2) * sigma ^ 2) :
    ∀ᶠ n : ℕ in atTop, r < Real.log (n : ℝ) ^ 2 * speed n := by
  let rate := (Real.pi ^ 2 / 2) * sigma ^ 2
  let t := 2 / (rate - r)
  have hgap : 0 < rate - r := sub_pos.mpr hr
  have ht : 0 < t := div_pos (by norm_num) hgap
  let N : ℕ → ℕ := Nat.succ
  have hN : Tendsto N atTop atTop := tendsto_add_atTop_nat 1
  let H := logarithmicHorizon N t
  have hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t) :=
    logarithmicHorizon_div_logCube_tendsto hN ht
  let μ := L.sortedPotentialImage
  let P := RootIndexed.stepFieldLaw (Root := ℕ) μ
  let E (n : ℕ) := ∫ field, countableRootEndpointMinimum (N n) (N n) (H n) field /
    Real.log (N n : ℝ) ∂P
  have hE : Tendsto E atTop (𝓝 (-1 + rate * t)) := by
    have hm : (fun n => ⌊(N n : ℝ) ^ (1 : ℝ)⌋₊) = N := by
      funext n
      rw [Real.rpow_one, Nat.floor_natCast]
    have h := tendsto_integral_countableRootEndpointMinimum_div L hsuper hnonempty
      hboundary hcross hfour hsigma hspine (a := 1) (by simp) ht
      (fun h => (one_ne_zero h).elim) (fun n => Nat.succ_pos n) hN hH
    dsimp only at h
    let M (m : ℕ → ℕ) (n : ℕ) :=
      @countableRootEndpointMinimum (m n) (N n) (H n)
        (RootIndexed.addressLinearOrder (Fin (m n)) ℕ)
    change Tendsto (fun n => ∫ field,
      M (fun k => ⌊(N k : ℝ) ^ (1 : ℝ)⌋₊) n field / Real.log (N n : ℝ) ∂P)
      atTop (𝓝 (-1 + rate * t)) at h
    rw [hm] at h
    exact h
  have hratio := hE.div hH ht.ne'
  have hlimit : r < (-1 + rate * t) / t := by
    apply (lt_div_iff₀ ht).2
    have heq : t * (rate - r) = 2 := div_mul_cancel₀ _ hgap.ne'
    linarith only [heq, show r * t + t * (rate - r) = rate * t by ring]
  suffices hsucc : ∀ᶠ n : ℕ in atTop,
      r < Real.log (N n : ℝ) ^ 2 * speed (N n) by
    obtain ⟨k, hk⟩ := eventually_atTop.mp hsucc
    refine eventually_atTop.mpr ⟨k + 1, ?_⟩
    intro n hn
    cases n with
    | zero => omega
    | succ n => exact hk n (by omega)
  filter_upwards [hratio.eventually (Ioi_mem_nhds hlimit), eventually_gt_atTop (0 : ℕ)]
    with n hratio_n hn
  have hpos : 0 < N n := Nat.succ_pos n
  have hHpos : 0 < H n := Nat.succ_pos _
  have hlog : 0 < Real.log (N n : ℝ) := Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hn)
  let F := selectedPopulationEndpointTrajectoryWithParameter (N n)
  let Q := finiteRootStepFieldLaw μ (N n)
  have hmean : E n = (∫ field, F ((fun _ => 0), field) (H n) ∂Q) /
      Real.log (N n : ℝ) := by
    dsimp only [E]
    rw [integral_div]
    have hpres := RootIndexed.StepField.measurePreserving_first μ (N n)
    congr 1
    have hint := finiteRootStepFieldLaw_integrable_firstNSelectedEndpointMinimum
      (N n) (N n) (H n) hpos hpos L hboundary hnonempty
      (fourthMoment_implies_firstMoment L hfour)
    calc
      _ = ∫ field, firstNSelectedEndpointMinimum (N n) (N n) (H n) field ∂Q :=
        hpres.integral_comp_of_integrable hint
      _ = _ := integral_congr_ae (Eventually.of_forall fun field =>
        firstNSelectedEndpointMinimum_eq_endpointWithParameter_zero (N n) (N n) (H n) field)
  have hblock := integral_fullCapacityEndpoint_div_le_speed hpos L hboundary hnonempty
    (fourthMoment_implies_firstMoment L hfour) (hL1 (N n) hpos) hHpos
  change r < E n / ((H n : ℝ) / Real.log (N n : ℝ) ^ 3) at hratio_n
  rw [hmean] at hratio_n
  refine hratio_n.trans_le ?_
  have heq : ((∫ field, F ((fun _ => 0), field) (H n) ∂Q) / Real.log (N n : ℝ)) /
      ((H n : ℝ) / Real.log (N n : ℝ) ^ 3) =
      Real.log (N n : ℝ) ^ 2 * ((∫ field, F ((fun _ => 0), field) (H n) ∂Q) / H n) := by
    have hcast : (H n : ℝ) ≠ 0 := by exact_mod_cast hHpos.ne'
    field_simp [hlog.ne', hcast]
  rw [heq]
  exact mul_le_mul_of_nonneg_left hblock (sq_nonneg _)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
