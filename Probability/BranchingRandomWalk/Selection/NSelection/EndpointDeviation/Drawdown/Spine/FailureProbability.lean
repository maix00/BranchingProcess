/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.Spine
import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Process.RandomWalk.Path.Restart.Basic
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Rate.LogScales
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Cutoff
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Window
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.PairBound

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Lemmas.Asymptotics
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Lemmas.CapacityProbability
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Lemmas.ParameterBounds

/-!
# Positive-initial-mass killed-capacity failure bound

The public declarations in namespace
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail` are:

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveAKilledCapacityFailureProbability m ell ellN horizon
  logN b v c κ μ` is the probability under the `m`-root step-field law that
  the restarted-window causal population fails to reach capacity by
  `horizon`, as used in Proposition 3.1, equation (4.15), of Elie Aïdékon
  and Yueyun Hu, *Average-weight percolation on the complete graph*,
  arXiv:2512.23266 (2025).
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.exists_rightTailPositiveAKilledCapacityFailure_le_polynomial_of_endpointGap`
  states that if $N_n\to\infty$, the tilted increment law is centered with
  variance $\sigma^2>0$, the Brownian inputs satisfy the pre-Brownian
  hypotheses, $0<a<1$, $t>0$, and
  $-a+\frac{\pi^2}{2}\sigma^2t<\zeta$, then there are admissible corridor
  parameters and $\varepsilon>0$ for which the failure probability is at
  most $\exp(-\varepsilon\log N_n)$ eventually.

The endpoint-gap conclusion formalizes the positive-initial-mass estimate in
Proposition 3.1, equation (4.15), of Elie Aïdékon and Yueyun Hu,
*Average-weight percolation on the complete graph*, arXiv:2512.23266 (2025),
and Chapter 4, equation (4.15), of Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026).
The logarithmic-scale reduction used in its proof is private to this module;
the capacity and tube estimates remain under `Lemmas/`.

-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The failure probability for the two-stage killed population in the
positive-initial-mass estimate of Aïdékon and Hu, Proposition 3.1, equation
(4.15). -/
noncomputable def rightTailPositiveAKilledCapacityFailureProbability
    (m ell ellN horizon : ℕ) (logN b v c κ : ℝ)
    (μ : Measure (Step ℕ ℝ)) : ℝ≥0∞ := by
  let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
  let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
  let population := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
    (fun _ : Fin m => (0 : ℝ)) id measurable_id
    (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
    (by
      intro q hq
      rcases RootIndexed.mem_initialPopulation_iff.mp hq with ⟨r, _hr, rfl⟩
      simp) ell window
    (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
    upper (rightTailPositiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)
  exact (RootIndexed.stepFieldLaw (Root := Fin m) μ)
    (population.capacityEvent horizon ellN)ᶜ

/-- Under logarithmic cutoffs, the first term in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
master's thesis, Fudan University (2026), Chapter 4, equation (4.15), has
polynomial decay whenever its two exponent margins are positive. The uniform
threshold is chosen once and then used for every `N`. -/
private lemma eventually_rightTailPositiveAKilledCapacityFailure_le_polynomial_of_logarithmicScales
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma : ℝ}
    (hspine : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {brownianMeasure : Measure Ω}
    [IsProbabilityMeasure brownianMeasure] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B brownianMeasure)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {a t b v c κ target blockTarget p : ℝ}
    (_ha : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hb : 0 ≤ b) (hvb : v ≤ b) (hc : 0 < c) (hvc : v ≤ c)
    (hκ : 0 ≤ κ) (hκrate : κ = target * sigma ^ 2)
    (htarget : 0 < target) (htargetBlock : target < blockTarget)
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2)
    (hp : 0 < p) (hpHalf : p < 1 / 2)
    (hmargin : a + (-b + v + c * (t ^ (3⁻¹ : ℝ))) < 1) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      rightTailPositiveAKilledCapacityFailureProbability
        (Nat.floor ((N n : ℝ) ^ a))
        (rightTailFirstStageCutoff N n)
        (logarithmicHorizon N t n) (N n)
        (logarithmOfSampleSize N n) b v c κ μ ≤
        ENNReal.ofReal (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
  let m : ℕ → ℕ := fun n => Nat.floor ((N n : ℝ) ^ a)
  let ell : ℕ → ℕ := rightTailFirstStageCutoff N
  let ellN : ℕ → ℕ := logarithmicHorizon N t
  let D : ℕ → ℕ := fun n => ellN n - ell n
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let E : ℕ → ℝ := fun n =>
    (-b + v) * L n + c * ((D n : ℝ) ^ (3⁻¹ : ℝ)) +
      κ * c ^ p * ((D n : ℝ) ^ (p / 3))
  let P : ℕ → ℝ≥0∞ := fun n =>
    rightTailPositiveAKilledCapacityFailureProbability
      (m n) (ell n) (ellN n) (N n) (L n) b v c κ μ
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hellPos : ∀ᶠ n : ℕ in atTop, 0 < ell n := by
    simpa [ell] using
      (tendsto_rightTailFirstStageCutoff_atTop hN).eventually_gt_atTop 0
  have hellN : ∀ᶠ n : ℕ in atTop, ell n < ellN n := by
    simpa [ell, ellN] using eventually_rightTailFirstStageCutoff_lt_horizon hN ht
  have horder : ∀ᶠ n : ℕ in atTop, ell n ≤ ellN n :=
    hellN.mono (fun _ h => Nat.le_of_lt h)
  have hcutoffScale : Tendsto (fun n => (ell n : ℝ) / L n ^ 3)
      atTop (𝓝 0) := by
    simpa [ell, L] using tendsto_rightTailFirstStageCutoff_div_logCube hN
  have hhorizonScale : Tendsto (fun n => (ellN n : ℝ) / L n ^ 3)
      atTop (𝓝 t) := by
    simpa [ellN, L] using logarithmicHorizon_div_logCube_tendsto hN ht
  have hDScale : Tendsto (fun n => (D n : ℝ) / L n ^ 3)
      atTop (𝓝 t) := by
    apply tendsto_rightTailPositiveASpan_cubicRatio_of_stageRatios hL
      hcutoffScale hhorizonScale
    exact horder
  have hfirstCountLog : Tendsto
      (fun n => Real.log ((ellN n : ℝ) + 1) / L n) atTop (𝓝 0) := by
    simpa using tendsto_rightTailPositiveA_log_add_one_div_log_of_cubic_scale
      hL (fun _ => Nat.cast_nonneg _) hhorizonScale ht
  have hspanCountLog : Tendsto
      (fun n => Real.log ((D n : ℝ) + 1) / L n) atTop (𝓝 0) := by
    simpa using tendsto_rightTailPositiveA_log_add_one_div_log_of_cubic_scale
      hL (fun _ => Nat.cast_nonneg _) hDScale ht
  have hERate : Tendsto (fun n => E n / L n) atTop
      (𝓝 (-b + v + c * (t ^ (3⁻¹ : ℝ)))) := by
    simpa [E, D, L, ell, ellN] using
      tendsto_rightTailPositiveAAHExponent_div_log_of_logarithmicScales
        hN ht (by linarith : p < 1)
  have hspan : Tendsto (fun n => (D n : ℝ)) atTop atTop := by
    simpa [D, ell, ellN] using
      tendsto_rightTailPositiveASpan_atTop_of_logarithmicScales hN ht
  obtain ⟨delta0, hdelta0, hAH⟩ :=
    iidSequenceLaw_rightTailPositiveASecondStageDrawdown_le_of_ah
      ν hspine hsigma hB hcontinuous hmeasurable κ c target blockTarget p
      hκ hc htarget htargetBlock hblockTarget hp
  have hscale := eventually_rightTailPositiveASecondStageAHScale
    D c p delta0 hc (by linarith : p < 1) hspan
  have htiltedLog : ∀ᶠ n : ℕ in atTop, 0 ≤ L n :=
    hLpos.mono (fun _ h => h.le)
  have hm : ∀ᶠ n : ℕ in atTop, (m n : ℝ) ≤ (N n : ℝ) ^ a := by
    filter_upwards [hN.eventually_gt_atTop 0] with n hn
    dsimp [m]
    exact Nat.floor_le (by positivity : 0 ≤ (N n : ℝ) ^ a)
  have hraw : ∀ᶠ n : ℕ in atTop,
      P n ≤ (m n : ℝ≥0∞) *
        (((ell n + 1 : ℕ) : ℝ≥0∞) +
          ((D n : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) /
          (N n + 1 : ℕ) := by
    filter_upwards [hscale, hellPos, hellN, htiltedLog] with n hscale hnell hnorder hnlog
    have hcap :=
      measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHPolynomialInput_of_uniformAH
        (m n) (ell n) (ellN n) (N n) (L n) b v c κ
        hnell hnorder hb hnlog hκ hvb hc hvc μ hboundary ν hν target p hκrate
        delta0 hAH hscale.1
    simpa [P, rightTailPositiveAKilledCapacityFailureProbability, m, ell,
      ellN, D, E, L] using hcap
  exact eventually_probability_le_polynomial_of_canceledAH_capacity_bound
    (P := P) (m := m) (ell := ell) (ellN := ellN) (N := N) (E := E)
    hN horder (by simpa [L, logarithmOfSampleSize] using hfirstCountLog)
    (by simpa [L, D, logarithmOfSampleSize] using hspanCountLog)
    (by simpa [L, logarithmOfSampleSize] using hERate) ha1 hmargin hm hraw

/-- Choose the corridor parameters from the endpoint gap and apply
the logarithmic-scale killed-capacity estimate. This is the endpoint-gap
form of Chapter 4, equation (4.15), in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), and Proposition 3.1, equation (4.15), in Elie Aïdékon and
Yueyun Hu, *Average-weight percolation on the complete graph*,
arXiv:2512.23266 (2025). -/
theorem exists_rightTailPositiveAKilledCapacityFailure_le_polynomial_of_endpointGap
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma : ℝ}
    (hspine : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {brownianMeasure : Measure Ω}
    [IsProbabilityMeasure brownianMeasure] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B brownianMeasure)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {a t zeta : ℝ} (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hgap : -a + Real.pi ^ 2 / 2 * sigma ^ 2 * t < zeta) :
    ∃ b v c epsilon : ℝ,
      0 < b ∧ b < a ∧ 0 < v ∧ v < b ∧ v ≤ c ∧ 0 < c ∧
      c < (t ^ (3⁻¹ : ℝ))⁻¹ ∧
      c * t ^ (3⁻¹ : ℝ) + (a - b) + v < 1 ∧
      0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
        rightTailPositiveAKilledCapacityFailureProbability
          (Nat.floor ((N n : ℝ) ^ a))
          (rightTailFirstStageCutoff N n)
          (logarithmicHorizon N t n) (N n)
          (logarithmOfSampleSize N n) b v c
          ((3 * Real.pi ^ 2 / 8) * sigma ^ 2) μ ≤
          ENNReal.ofReal (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
  let r : ℝ := t ^ (3⁻¹ : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos ht _
  have hrcube : r ^ 3 = t := by
    dsimp [r]
    calc
      (t ^ (3⁻¹ : ℝ)) ^ 3 = t ^ ((3⁻¹ : ℝ) * 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
        congr 1
      _ = t := by
        rw [show (3⁻¹ : ℝ) * 3 = 1 by norm_num, Real.rpow_one]
  obtain ⟨b, v, c, hb, hba, hv, hvb, hvc, hc, hcr, hmargin, _hendpoint⟩ :=
    exists_rightTailPositiveAParameters a t r (sigma ^ 2) zeta
      ha ht hr hrcube (sq_nonneg sigma) hgap
  let target : ℝ := 3 * Real.pi ^ 2 / 8
  let blockTarget : ℝ := 7 * Real.pi ^ 2 / 16
  have htarget : 0 < target := by
    dsimp [target]
    positivity
  have htargetBlock : target < blockTarget := by
    dsimp [target, blockTarget]
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hblockTarget : blockTarget < Real.pi ^ 2 / 2 := by
    dsimp [blockTarget]
    nlinarith [sq_pos_of_pos Real.pi_pos]
  let κ : ℝ := target * sigma ^ 2
  have hκ : 0 ≤ κ := by dsimp [κ, target]; positivity
  have hκrate : κ = target * sigma ^ 2 := rfl
  have hmargin' : a + (-b + v + c * (t ^ (3⁻¹ : ℝ))) < 1 := by
    have hmain : c * r + (a - b) + v < 1 := by simpa [r] using hmargin
    have hmain' : a + (-b + v + c * r) < 1 := by nlinarith [hmain]
    simpa [r] using hmain'
  have hp : 0 < (1 / 4 : ℝ) := by norm_num
  have hpHalf : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨epsilon, hepsilon, hcapacity⟩ :=
    eventually_rightTailPositiveAKilledCapacityFailure_le_polynomial_of_logarithmicScales
      hN μ hboundary ν hν hspine hsigma hB hcontinuous hmeasurable
      (a := a) (t := t) (b := b) (v := v) (c := c) (κ := κ)
      (target := target) (blockTarget := blockTarget) (p := 1 / 4)
      ha ha1 ht hb.le (by linarith [hvb]) hc hvc hκ hκrate
      htarget htargetBlock hblockTarget hp hpHalf hmargin'
  refine ⟨b, v, c, epsilon, hb, hba, hv, hvb, hvc, hc, ?_, ?_, hepsilon, hcapacity⟩
  · simpa [r] using hcr
  · simpa [r] using hmargin

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
