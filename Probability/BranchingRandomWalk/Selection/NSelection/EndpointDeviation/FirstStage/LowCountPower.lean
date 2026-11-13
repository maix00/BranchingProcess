/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.FirstStage.Lemmas.PZAssembly
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Population.LowCount
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.FirstStage.Cutoff
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.FirstStage.Lemmas.CorridorLowerBound
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Population.RestartedWindow
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.LogarithmicScales
public import Probability.Distributions.Moments.Real
public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event
public import Analysis.Asymptotics.Power.FloorProduct

/-!
# First-stage population low-count power bound

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_positiveA_populationLowCount_le_exp_neg_power`:
  put `m_n=\lfloor N_n^a\rfloor`, let `K_n` be the first-stage selected BRW
  population size at cutoff `\ell_n=\operatorname{positiveAFirstStageCutoff}(N,n)`,
  and let `p_n=\operatorname{toReal}(u_n^2/(w_n+R_n))` be the one-root PZ
  quotient, with `u_n`, `w_n`, and `R_n` as in `FirstStage/Lemmas/PZAssembly.lean`.
  Write `\mathbb P_{\mu,m_n}=finiteRootStepFieldLaw(\mu,m_n)`. Under
  the finite-second-moment, boundary, and cross-weight hypotheses, if
  `\delta<a-b-2v-3\varepsilon`, then
  \[
    \mathbb P_{\mu,m_n}\!\left(K_n\le\frac{m_np_n}{4}\right)
      \le e^{-N_n^\delta}
  \]
  eventually.

This is the first-stage probability estimate in the proof of Chapter 3,
Lemma 3.5 of WANG Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring*.

The quantitative one-root Paley--Zygmund estimate gives a polynomial lower
bound for the expected number of successful roots. The existing population
embedding then turns its binomial lower-tail estimate into the first-stage
failure term used in the two-stage argument.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

/-- Under the finite second moment, boundary normalization, and
finite cross-weight assumptions, the first-stage selected BRW population has at
least `N^δ` successful particles with an exponentially small failure
probability. The exponent condition is only the parameter budget
`δ < a - b - 2v - 3ε`; it is not an additional probabilistic hypothesis. -/
theorem eventually_positiveA_populationLowCount_le_exp_neg_power
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma a b v epsilon delta c κ : ℝ}
    (hνMoment : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) (hvb : v < b)
    (hepsilon : 0 < epsilon) (hbudget : delta < a - b - 2 * v - 3 * epsilon)
    (ellN : ℕ → ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let m := Nat.floor ((N n : ℝ) ^ a)
      let ell := positiveAFirstStageCutoff N n
      let logN := logarithmOfSampleSize N n
      let corridor := affineCorridorThrough ell (-b * logN) 0
        (b * logN) ((-b + v) * logN)
      let spineEvent := {increment : ℕ → ℝ |
        RandomWalk.history ell 0 increment ∈ corridor}
      let lowerMean := ENNReal.ofReal (Real.exp (-b * logN)) *
        (tiltedIncrementFieldLaw realPotential μ) spineEvent
      let upperMean := ENNReal.ofReal (Real.exp ((-b + v) * logN)) *
        (tiltedIncrementFieldLaw realPotential μ) spineEvent
      let q : ℕ → ℝ≥0∞ := fun _ => 1
      let pairBound := ∑ j : Fin ell,
        ENNReal.ofReal (Real.exp 0) *
          (ENNReal.ofReal (Real.exp (2 * ((-b + v) * logN))) *
            q (ell - j.val - 1) ^ 2) *
          (∫⁻ ξ, crossPotentialWeight realPotential (-1) ξ ∂μ) *
          (ENNReal.ofReal (Real.exp (0 - (-b * logN))) *
            (tiltedIncrementFieldLaw realPotential μ)
              {increment | RandomWalk.history j.val 0 increment ∈
                affineCorridorPrefix j.val (-b * logN) 0 (b * logN)})
      let pzMean := lowerMean ^ 2 / (upperMean + pairBound)
      let initial := RootIndexed.initialPopulation (α := ℕ)
        (Finset.univ : Finset (Fin m))
      let window := positiveARestartedWindow ell (ellN n)
        logN b v c κ
      let upper := positiveAWindowUpper ell (ellN n)
        logN b v c κ
      let populationFinite :=
        RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
          (fun _ : Fin m => 0) id measurable_id initial
          (by simp [initial, RootIndexed.mem_initialPopulation_iff])
          ell window (measurableSet_positiveARestartedWindow
            ell (ellN n) logN b v c κ)
          upper (positiveARestartedWindow_subset_Iic_upper
            ell (ellN n) logN b v c κ)
      (finiteRootStepFieldLaw μ m)
        {field | ((populationFinite.toFinset ell field).card : ℝ) ≤
          (m : ℝ) * pzMean.toReal / 4} ≤
        ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ delta))) := by
  classical
  let m : ℕ → ℕ := fun n => Nat.floor ((N n : ℝ) ^ a)
  let ell : ℕ → ℕ := positiveAFirstStageCutoff N
  let logN : ℕ → ℝ := logarithmOfSampleSize N
  let initial (n : ℕ) :=
    RootIndexed.initialPopulation (α := ℕ)
      (Finset.univ : Finset (Fin (m n)))
  let window (n : ℕ) := positiveARestartedWindow
    (ell n) (ellN n) (logN n) b v c κ
  let upper (n : ℕ) := positiveAWindowUpper
    (ell n) (ellN n) (logN n) b v c κ
  let populationFinite (n : ℕ) :=
    RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
      (fun _ : Fin (m n) => 0) id measurable_id (initial n)
      (by simp [initial, RootIndexed.mem_initialPopulation_iff])
      (ell n) (window n)
      (measurableSet_positiveARestartedWindow
        (ell n) (ellN n) (logN n) b v c κ)
      (upper n) (positiveARestartedWindow_subset_Iic_upper
        (ell n) (ellN n) (logN n) b v c κ)
  let pzMean (n : ℕ) : ℝ≥0∞ :=
    let corridor := affineCorridorThrough (ell n) (-b * logN n) 0
      (b * logN n) ((-b + v) * logN n)
    let spineEvent := {increment : ℕ → ℝ |
      RandomWalk.history (ell n) 0 increment ∈ corridor}
    let lowerMean := ENNReal.ofReal (Real.exp (-b * logN n)) *
      (tiltedIncrementFieldLaw realPotential μ) spineEvent
    let upperMean := ENNReal.ofReal (Real.exp ((-b + v) * logN n)) *
      (tiltedIncrementFieldLaw realPotential μ) spineEvent
    let q : ℕ → ℝ≥0∞ := fun _ => 1
    let pairBound := ∑ j : Fin (ell n),
      ENNReal.ofReal (Real.exp 0) *
        (ENNReal.ofReal (Real.exp (2 * ((-b + v) * logN n))) *
          q (ell n - j.val - 1) ^ 2) *
        (∫⁻ ξ, crossPotentialWeight realPotential (-1) ξ ∂μ) *
        (ENNReal.ofReal (Real.exp (0 - (-b * logN n))) *
          (tiltedIncrementFieldLaw realPotential μ)
            {increment | RandomWalk.history j.val 0 increment ∈
              affineCorridorPrefix j.val (-b * logN n) 0 (b * logN n)})
    lowerMean ^ 2 / (upperMean + pairBound)
  have hPZ := eventually_positiveA_pzMean_toReal_ge_power_of_centeredSecondMoment
    hN μ hboundary hcross ν hν hνMoment hsigma hb hv hvb hepsilon
  have hNReal : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hthresholdRaw := Asymptotics.eventually_floor_rpow_mul_ge
    (x := fun n => (N n : ℝ)) (y := fun n => (pzMean n).toReal) hNReal
    (a := a) (r := -b - 2 * v - 3 * epsilon) (δ := delta) (C := 4)
    ha (by linarith [hbudget]) (by
      filter_upwards [hPZ] with n hn
      simpa [m, pzMean, logN, logarithmOfSampleSize] using hn)
  have hthreshold : ∀ᶠ n : ℕ in atTop,
      ((Nat.floor ((N n : ℝ) ^ a) : ℕ) : ℝ) * (pzMean n).toReal / 4 ≥
        (N n : ℝ) ^ delta := by
    filter_upwards [hthresholdRaw] with n hn
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by
      simpa [mul_comm] using hn)
  have hpositive :=
    eventually_positiveA_spineCorridor_pos_of_centeredSecondMoment
      hN μ ν hν hνMoment hsigma hb hv hvb
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw realPotential μ) :=
    tiltedIncrementFieldLaw_isProbability realPotential μ hboundary
  have hmPos : ∀ᶠ n : ℕ in atTop, 0 < m n := by
    have hpow : Tendsto (fun n : ℕ => (N n : ℝ) ^ a) atTop atTop :=
      (_root_.tendsto_rpow_atTop ha).comp
        (tendsto_natCast_atTop_atTop.comp hN)
    filter_upwards [hpow.eventually_gt_atTop 1] with n hn
    have hfloor : 1 ≤ Nat.floor ((N n : ℝ) ^ a) :=
      Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ (N n : ℝ) ^ a by exact_mod_cast hn.le)
    exact lt_of_lt_of_le Nat.zero_lt_one hfloor
  filter_upwards [hthreshold, hpositive, hmPos] with n hcount hpositive hm
  let q : ℕ → ℝ≥0∞ := fun _ => 1
  have hdrawdown (k : ℕ) :
      (tiltedIncrementFieldLaw realPotential μ)
        (RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          k (b * logN n) (b * logN n)) ≤ q k := by
    rw [show q k = 1 by simp [q]]
    calc
      (tiltedIncrementFieldLaw realPotential μ)
          (RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
            k (b * logN n) (b * logN n)) ≤
        (tiltedIncrementFieldLaw realPotential μ) Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hlow := measure_positiveA_population_le_pzThreshold_le_exp_of_affineCorridorDrawdown
    (m n) (ell n) (ellN n) hm (logN n) b v c κ μ hboundary hcross q
    (by intro k; simp [q]) hdrawdown
    (show 0 < (tiltedIncrementFieldLaw realPotential μ)
      {increment | RandomWalk.history (ell n) 0 increment ∈
        affineCorridorThrough (ell n) (-b * logN n) 0
          (b * logN n) ((-b + v) * logN n)} from hpositive)
  have hexp : ENNReal.ofReal
      (Real.exp (-((m n : ℝ) * (pzMean n).toReal / 4))) ≤
        ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ delta))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact neg_le_neg hcount
  calc
    (finiteRootStepFieldLaw μ (m n))
        {field | (((populationFinite n).toFinset (ell n) field).card : ℝ) ≤
          (m n : ℝ) * (pzMean n).toReal / 4} ≤
      ENNReal.ofReal (Real.exp (-((m n : ℝ) * (pzMean n).toReal / 4))) := by
        simpa [m, ell, logN, pzMean, q, initial, window, upper,
          populationFinite, RandomWalk.history] using hlow
    _ ≤ ENNReal.ofReal (Real.exp (-((N n : ℝ) ^ delta))) := hexp

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
