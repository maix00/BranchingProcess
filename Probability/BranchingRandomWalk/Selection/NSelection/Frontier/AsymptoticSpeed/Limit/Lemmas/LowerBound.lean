/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.L2Limit
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.ExpectationLower
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
* `eventually_lt_logSq_mul_speed_of_firstMoment`: the same inequality follows
  under a first moment from the one-sided mean bound of Lemma 4.1.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open EndpointDeviation ProbabilityTheory.BranchingRandomWalk.Spine

noncomputable local instance blockLowerAddressOrder (m : ℕ) : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
  RootIndexed.addressLinearOrder (Fin m) ℕ

/-- Transfer the full-capacity mean to the block speed at a positive horizon. -/
private lemma scaledEndpointMean_le_logSq_mul_speed
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hfirst : HasLeftmostFirstMoment L)
    {n H : ℕ} {speed : ℝ}
    (hL1 : Tendsto (fun k : ℕ => eLpNorm (fun field =>
        (k : ℝ)⁻¹ * selectedPopulationEndpointTrajectoryWithParameter n
          ((fun _ => 0), field) k - speed) 1
        (finiteRootStepFieldLaw L.sortedPotentialImage n)) atTop (𝓝 0))
    (hn : 1 < n) (hHpos : 0 < H) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    ((∫ field, countableRootEndpointMinimum n n H field ∂P) / Real.log (n : ℝ)) /
      ((H : ℝ) / Real.log (n : ℝ) ^ 3) ≤ Real.log (n : ℝ) ^ 2 * speed := by
  intro P
  let μ := L.sortedPotentialImage
  let F := selectedPopulationEndpointTrajectoryWithParameter n
  let Q := finiteRootStepFieldLaw μ n
  have hnpos : 0 < n := zero_lt_one.trans hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hmean : (∫ field, countableRootEndpointMinimum n n H field ∂P) =
      ∫ field, F ((fun _ => 0), field) H ∂Q := by
    have hpres := RootIndexed.StepField.measurePreserving_first μ n
    have hint := finiteRootStepFieldLaw_integrable_firstNSelectedEndpointMinimum
      n n H hnpos hnpos L hboundary hnonempty hfirst
    calc
      _ = ∫ field, firstNSelectedEndpointMinimum n n H field ∂Q :=
        hpres.integral_comp_of_integrable hint
      _ = _ := integral_congr_ae (Eventually.of_forall fun field =>
        firstNSelectedEndpointMinimum_eq_endpointWithParameter_zero n n H field)
  have hblock := integral_fullCapacityEndpoint_div_le_speed hnpos L hboundary hnonempty
    hfirst hL1 hHpos
  rw [hmean]
  have heq : ((∫ field, F ((fun _ => 0), field) H ∂Q) / Real.log (n : ℝ)) /
      ((H : ℝ) / Real.log (n : ℝ) ^ 3) =
      Real.log (n : ℝ) ^ 2 * ((∫ field, F ((fun _ => 0), field) H ∂Q) / H) := by
    have hcast : (H : ℝ) ≠ 0 := by exact_mod_cast hHpos.ne'
    field_simp [hlog.ne', hcast]
  rw [heq]
  exact mul_le_mul_of_nonneg_left hblock (sq_nonneg _)

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
  have hscaled := scaledEndpointMean_le_logSq_mul_speed L hnonempty hboundary
    (fourthMoment_implies_firstMoment L hfour) (hL1 (N n) hpos)
    (show 1 < N n from Nat.succ_lt_succ hn) hHpos
  change r < E n / ((H n : ℝ) / Real.log (N n : ℝ) ^ 3) at hratio_n
  rw [show E n = (∫ field, countableRootEndpointMinimum (N n) (N n) (H n) field ∂P) /
      Real.log (N n : ℝ) by simp only [E, integral_div]] at hratio_n
  exact hratio_n.trans_le hscaled

/-- The first-moment lower speed bound follows from the full-capacity
endpoint estimate in Chapter 4, Lemma 4.1 of Wang Yiyang. -/
lemma eventually_lt_logSq_mul_speed_of_firstMoment
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hfirst : HasLeftmostFirstMoment L)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (speed : ℕ → ℝ)
    (hL1 : ∀ N : ℕ, 0 < N →
      Tendsto (fun k : ℕ => eLpNorm (fun field =>
        (k : ℝ)⁻¹ * selectedPopulationEndpointTrajectoryWithParameter N
          ((fun _ => 0), field) k - speed N) 1
        (finiteRootStepFieldLaw L.sortedPotentialImage N)) atTop (𝓝 0))
    {r : ℝ} (hr : r < (Real.pi ^ 2 / 2) * sigma ^ 2) :
    ∀ᶠ n : ℕ in atTop, r < Real.log (n : ℝ) ^ 2 * speed n := by
  let rate := (Real.pi ^ 2 / 2) * sigma ^ 2
  let t := 2 / (rate - r)
  have hgap : 0 < rate - r := sub_pos.mpr hr
  have ht : 0 < t := div_pos (by norm_num) hgap
  have hmargin : r * t + (1 / 2 : ℝ) < -1 + rate * t := by
    have heq : t * (rate - r) = 2 := div_mul_cancel₀ _ hgap.ne'
    linarith only [heq, show r * t + t * (rate - r) = rate * t by ring]
  let H := logarithmicHorizon (id : ℕ → ℕ) t
  have hH : Tendsto (fun n => (H n : ℝ) / Real.log (n : ℝ) ^ 3) atTop (𝓝 t) :=
    logarithmicHorizon_div_logCube_tendsto tendsto_id ht
  let μ := L.sortedPotentialImage
  let P := RootIndexed.stepFieldLaw (Root := ℕ) μ
  let E (n : ℕ) := (∫ field, countableRootEndpointMinimum n n (H n) field ∂P) /
    Real.log (n : ℝ)
  have hE : ((-1 + rate * t : ℝ) : EReal) ≤ atTop.liminf (fun n => (E n : EReal)) :=
    le_liminf_integral_countableRootEndpointMinimum_div_log L hboundary hnonempty hfirst
      hsigma hspine ht H blockLowerAddressOrder hH
  have hevent : ∀ᶠ n in atTop, r * t + (1 / 2 : ℝ) < E n := by
    have hlt : ((r * t + (1 / 2 : ℝ) : ℝ) : EReal) < atTop.liminf (fun n => (E n : EReal)) :=
      (EReal.coe_lt_coe_iff.mpr hmargin).trans_le hE
    exact (eventually_lt_of_lt_liminf hlt).mono fun _ hn => EReal.coe_lt_coe_iff.mp hn
  have hscaled := hH.const_mul r
  filter_upwards [hevent, hscaled.eventually (gt_mem_nhds (by linarith : r * t < r * t + 1 / 2)),
    eventually_gt_atTop (1 : ℕ)] with n he hs hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hHpos : 0 < H n := Nat.succ_pos _
  have hnpos : 0 < n := zero_lt_one.trans hn
  have hratio : r < E n / ((H n : ℝ) / Real.log (n : ℝ) ^ 3) :=
    (lt_div_iff₀ (div_pos (by exact_mod_cast hHpos) (pow_pos hlog 3))).mpr (hs.trans he)
  exact hratio.trans_le (scaledEndpointMean_le_logSq_mul_speed L hnonempty hboundary hfirst
    (hL1 n hnpos) (H := H n) hn hHpos)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
