/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.FirstStage.Lemmas.PZBudget
import Analysis.Asymptotics.Power.ENNRealRatio
/-!
* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.eventually_rightTailPositiveA_pzMean_toReal_ge_power_of_centeredSecondMoment`:
  if `lowerMean` is the one-root corridor contribution and `upperMean +
  pairBound` is the first two-moment denominator, then eventually
  `N n ^ (-b - 2 * v - 3 * ε) ≤ (lowerMean ^ 2 / (upperMean + pairBound)).toReal`.

# First-stage PZ proof lemmas

This auxiliary module combines the finite-variance corridor estimate with
the MRCA pair bound, using the constant drawdown bound.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown
open ProbabilityTheory.BranchingRandomWalk.Spine

private lemma eventually_one_add_const_mul_log_cube_le_exp
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {C eta : ℝ}
    (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop,
      1 + C * logarithmOfSampleSize N n ^ 3 ≤
        Real.exp (eta * logarithmOfSampleSize N n) := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have hdecay0 : Tendsto (fun n => Real.exp (-eta * L n)) atTop (𝓝 0) := by
    have hlinear : Tendsto (fun n => eta * L n) atTop atTop :=
      hL.const_mul_atTop heta
    have hcomp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear
    have heq : (fun n => Real.exp (-(eta * L n))) =ᶠ[atTop]
        fun n => Real.exp (-eta * L n) := by
      filter_upwards [] with n
      congr 1
      ring
    exact hcomp.congr' heq
  have hdecay3 : Tendsto (fun n => L n ^ 3 * Real.exp (-eta * L n))
      atTop (𝓝 0) := by
    have hraw := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      3 eta heta
    have heq : (fun x : ℝ => x ^ 3 * Real.exp (-eta * x)) =ᶠ[atTop]
        fun x => x ^ (3 : ℝ) * Real.exp (-eta * x) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      simp
    have hreal := hraw.congr' heq.symm
    exact hreal.comp hL
  have hsum := hdecay0.add (hdecay3.const_mul C)
  have hsum' : Tendsto
      (fun n => (1 + C * L n ^ 3) * Real.exp (-eta * L n))
      atTop (𝓝 0) := by
    have heq : (fun n => (1 + C * L n ^ 3) * Real.exp (-eta * L n)) =ᶠ[atTop]
        fun n => Real.exp (-eta * L n) +
          C * (L n ^ 3 * Real.exp (-eta * L n)) := by
      filter_upwards [] with n
      ring
    simpa only [mul_zero, add_zero] using hsum.congr' heq.symm
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (1 + C * L n ^ 3) * Real.exp (-eta * L n) < 1 := by
    exact hsum'.eventually (Iio_mem_nhds (by norm_num))
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  filter_upwards [hsmall, hLpos] with n hn hLn
  have hmul := mul_lt_mul_of_pos_right hn (Real.exp_pos (eta * L n))
  have hcancel : Real.exp (-eta * L n) * Real.exp (eta * L n) = 1 := by
    rw [← Real.exp_add]
    have harg : -eta * L n + eta * L n = 0 := by ring
    rw [harg, Real.exp_zero]
  have hmul' : 1 + C * L n ^ 3 < Real.exp (eta * L n) := by
    have heq : ((1 + C * L n ^ 3) * Real.exp (-eta * L n)) *
        Real.exp (eta * L n) = 1 + C * L n ^ 3 := by
      rw [mul_assoc, hcancel, mul_one]
    rw [← heq]
    simpa only [one_mul] using hmul
  exact le_of_lt hmul'

/-- The first-stage one-root PZ probability has the power rate obtained from
`lowerMean ≳ N^(-b-epsilon)` and `upperMean + MRCA pairs ≲ N^(-b+2v+epsilon)`.
The only random-walk input is the centered finite second moment; in
the pair estimate the drawdown sequence is constantly one. -/
lemma eventually_rightTailPositiveA_pzMean_toReal_ge_power_of_centeredSecondMoment
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Combinatorics.Branching.Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma b v epsilon : ℝ}
    (hνMoment : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) (hb : 0 < b) (hv : 0 < v) (hvb : v < b)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      (N n : ℝ) ^ (-b - 2 * v - 3 * epsilon) ≤
        (let ell := rightTailPositiveAFirstCutoff N n
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
             (∫⁻ ξ, crossChildWeight realPotential ξ ∂μ) *
             (ENNReal.ofReal (Real.exp (0 - (-b * logN))) *
               (tiltedIncrementFieldLaw realPotential μ)
                 {increment | RandomWalk.history j.val 0 increment ∈
                   affineCorridorPrefix j.val (-b * logN) 0 (b * logN)})
         (lowerMean ^ 2 / (upperMean + pairBound)).toReal) := by
  classical
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let ell : ℕ → ℕ := rightTailPositiveAFirstCutoff N
  let corridor (n : ℕ) := affineCorridorThrough (ell n) (-b * L n) 0
    (b * L n) ((-b + v) * L n)
  let spineEvent (n : ℕ) : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history (ell n) 0 increment ∈ corridor n}
  let spineProb (n : ℕ) : ℝ≥0∞ :=
    (tiltedIncrementFieldLaw realPotential μ) (spineEvent n)
  let lowerMean (n : ℕ) : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-b * L n)) * spineProb n
  let upperMean (n : ℕ) : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp ((-b + v) * L n)) * spineProb n
  let q : ℕ → ℝ≥0∞ := fun _ => 1
  let crossMass : ℝ≥0∞ := ∫⁻ ξ, crossChildWeight realPotential ξ ∂μ
  let pairTerm (n : ℕ) (j : Fin (ell n)) : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp 0) *
      (ENNReal.ofReal (Real.exp (2 * ((-b + v) * L n))) *
        q (ell n - j.val - 1) ^ 2) * crossMass *
      (ENNReal.ofReal (Real.exp (0 - (-b * L n))) *
        (tiltedIncrementFieldLaw realPotential μ)
          {increment | RandomWalk.history j.val 0 increment ∈
            affineCorridorPrefix j.val (-b * L n) 0 (b * L n)})
  let pairBound (n : ℕ) : ℝ≥0∞ := ∑ j : Fin (ell n), pairTerm n j
  let pzMean (n : ℕ) : ℝ≥0∞ := lowerMean n ^ 2 / (upperMean n + pairBound n)
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw realPotential μ) :=
    tiltedIncrementFieldLaw_isProbability realPotential μ hboundary
  obtain ⟨C, _hC, entranceMass, hentranceMass, amplitude, hamplitude,
      hcorridor⟩ :=
    eventually_rightTailPositiveASpineCorridor_ge_exp_neg_log
      hN μ ν hν hνMoment hsigma hb hv hvb hepsilon
  have hcrossTop : crossMass ≠ ∞ := hcross
  have hcrossRealNonneg : 0 ≤ crossMass.toReal := ENNReal.toReal_nonneg
  have hcrossEq : crossMass = ENNReal.ofReal crossMass.toReal :=
    (ENNReal.ofReal_toReal hcrossTop).symm
  have hlogCube := tendsto_rightTailPositiveAFirstCutoff_div_logCube hN
  have hlogCubeLt : ∀ᶠ n : ℕ in atTop,
      (ell n : ℝ) / L n ^ 3 < 1 := by
    have h := hlogCube.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h] with n hn
    simpa [ell, L] using hn
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hlargeN : ∀ᶠ n : ℕ in atTop, 1 ≤ N n := hN.eventually_ge_atTop 1
  have hcrossExp := eventually_one_add_const_mul_log_cube_le_exp
    (C := crossMass.toReal) (eta := epsilon) hN hepsilon
  filter_upwards [hcorridor, hLpos, hlargeN, hcrossExp, hlogCubeLt]
    with n hcorr hLn hNlarge hpoly hlogCubeLtN
  rcases hcorr with ⟨hcorrPower, hcorrProb⟩
  let p := spineProb n
  let x := lowerMean n
  let z := upperMean n
  let d := pairBound n
  let y := z + d
  let Lval := L n
  have hpathLower : ENNReal.ofReal (Real.exp (-epsilon * Lval)) ≤ p := by
    calc
      ENNReal.ofReal (Real.exp (-epsilon * Lval)) ≤
          rightTailPositiveASpineCorridorLowerBound ν b v C amplitude
            entranceMass (ell n) := by
        simpa [Lval, L] using hcorrPower
      _ ≤ (tiltedIncrementFieldLaw realPotential μ)
          {increment : ℕ → ℝ | RandomWalk.history (ell n) 0 increment ∈
            affineCorridorThrough (ell n) (-b * Lval) 0
              (b * Lval) ((-b + v) * Lval)} := by
        simpa [Lval, L] using hcorrProb
      _ = p := by
        simp [p, spineProb, spineEvent, corridor, Lval]
  have hpTop : p ≠ ∞ := measure_ne_top _ _
  have hpRealLower : Real.exp (-epsilon * Lval) ≤ p.toReal := by
    have h := ENNReal.toReal_mono hpTop hpathLower
    simpa [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using h
  have hpLeOne : p ≤ 1 := by
    calc
      p ≤ (tiltedIncrementFieldLaw realPotential μ) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hpRealLeOne : p.toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top hpLeOne
  have hxEq : x.toReal = Real.exp (-b * Lval) * p.toReal := by
    dsimp [x, lowerMean, p]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  have hxLower : Real.exp ((-b - epsilon) * Lval) ≤ x.toReal := by
    rw [hxEq]
    have hmult := mul_le_mul_of_nonneg_left hpRealLower (Real.exp_nonneg (-b * Lval))
    have hexp : Real.exp (-b * Lval) * Real.exp (-epsilon * Lval) =
        Real.exp ((-b - epsilon) * Lval) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    exact hmult
  have hxPower : (N n : ℝ) ^ (-b - epsilon) ≤ x.toReal := by
    have hNpos : 0 < (N n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNlarge)
    rw [Real.rpow_def_of_pos hNpos]
    have hlog : Real.log (N n : ℝ) = Lval := by rfl
    rw [hlog]
    simpa [mul_comm] using hxLower
  have hzEq : z.toReal = Real.exp ((-b + v) * Lval) * p.toReal := by
    dsimp [z, upperMean, p]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  have hzUpper : z.toReal ≤ Real.exp ((-b + v) * Lval) := by
    rw [hzEq]
    nlinarith [mul_le_mul_of_nonneg_left hpRealLeOne
      (Real.exp_nonneg ((-b + v) * Lval))]
  have hprefTop (j : Fin (ell n)) :
      (tiltedIncrementFieldLaw realPotential μ)
        {increment | RandomWalk.history j.val 0 increment ∈
          affineCorridorPrefix j.val (-b * Lval) 0 (b * Lval)} ≠ ∞ :=
    measure_ne_top _ _
  have hpairTermTop (j : Fin (ell n)) : pairTerm n j ≠ ∞ := by
    have hq : q (ell n - j.val - 1) ^ 2 ≠ ∞ := by simp [q]
    have hfirst : ENNReal.ofReal (Real.exp 0) ≠ ∞ := ENNReal.ofReal_ne_top
    have hsecond : ENNReal.ofReal (Real.exp (2 * ((-b + v) * Lval))) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have hcross' : crossMass ≠ ∞ := hcrossTop
    have hlast : ENNReal.ofReal (Real.exp (0 - (-b * Lval))) *
        (tiltedIncrementFieldLaw realPotential μ)
          {increment | RandomWalk.history j.val 0 increment ∈
            affineCorridorPrefix j.val (-b * Lval) 0 (b * Lval)} ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hprefTop j)
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.mul_ne_top hfirst
          (ENNReal.mul_ne_top hsecond hq)
      · exact hcross'
    · exact hlast
  have hpairTop : pairBound n ≠ ∞ := by
    apply ENNReal.sum_ne_top.2
    intro j hj
    exact hpairTermTop j
  have hpairTermEq (j : Fin (ell n)) :
      (pairTerm n j).toReal =
        Real.exp ((-b + 2 * v) * Lval) * crossMass.toReal *
          ((tiltedIncrementFieldLaw realPotential μ)
            {increment | RandomWalk.history j.val 0 increment ∈
              affineCorridorPrefix j.val (-b * Lval) 0 (b * Lval)}).toReal := by
    have hexp : Real.exp (2 * ((-b + v) * Lval)) *
        Real.exp (b * Lval) = Real.exp ((-b + 2 * v) * Lval) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      (pairTerm n j).toReal =
          Real.exp (2 * ((-b + v) * Lval)) * crossMass.toReal *
            (Real.exp (b * Lval) *
              ((tiltedIncrementFieldLaw realPotential μ)
                {increment | RandomWalk.history j.val 0 increment ∈
                  affineCorridorPrefix j.val (-b * Lval) 0 (b * Lval)}).toReal) := by
        dsimp [pairTerm]
        simp [q, crossMass, Lval, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (Real.exp_nonneg _)]
      _ = (Real.exp (2 * ((-b + v) * Lval)) * Real.exp (b * Lval)) *
            crossMass.toReal *
              ((tiltedIncrementFieldLaw realPotential μ)
                {increment | RandomWalk.history j.val 0 increment ∈
                  affineCorridorPrefix j.val (-b * Lval) 0 (b * Lval)}).toReal := by ring
      _ = Real.exp ((-b + 2 * v) * Lval) * crossMass.toReal *
            ((tiltedIncrementFieldLaw realPotential μ)
              {increment | RandomWalk.history j.val 0 increment ∈
                affineCorridorPrefix j.val (-b * Lval) 0 (b * Lval)}).toReal := by
        rw [hexp]
  have hpairTermLe (j : Fin (ell n)) :
      (pairTerm n j).toReal ≤
        Real.exp ((-b + 2 * v) * Lval) * crossMass.toReal := by
    rw [hpairTermEq j]
    have hpref : ((tiltedIncrementFieldLaw realPotential μ)
        {increment | RandomWalk.history j.val 0 increment ∈
          affineCorridorPrefix j.val (-b * Lval) 0 (b * Lval)}).toReal ≤ 1 := by
      apply ENNReal.toReal_mono ENNReal.one_ne_top
      calc
        (tiltedIncrementFieldLaw realPotential μ)
            {increment | RandomWalk.history j.val 0 increment ∈
              affineCorridorPrefix j.val (-b * Lval) 0 (b * Lval)} ≤
          (tiltedIncrementFieldLaw realPotential μ) Set.univ :=
            measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    nlinarith [mul_le_mul_of_nonneg_left hpref
      (mul_nonneg (Real.exp_nonneg ((-b + 2 * v) * Lval)) hcrossRealNonneg)]
  have hpairRealEq : (pairBound n).toReal =
      ∑ j : Fin (ell n), (pairTerm n j).toReal := by
    exact ENNReal.toReal_sum (by
      intro j hj
      exact hpairTermTop j)
  have hpairRealLe : (pairBound n).toReal ≤
      (ell n : ℝ) * (Real.exp ((-b + 2 * v) * Lval) * crossMass.toReal) := by
    rw [hpairRealEq]
    calc
      (∑ j : Fin (ell n), (pairTerm n j).toReal) ≤
          ∑ _j : Fin (ell n),
            Real.exp ((-b + 2 * v) * Lval) * crossMass.toReal :=
        Finset.sum_le_sum fun j hj => hpairTermLe j
      _ = (ell n : ℝ) *
          (Real.exp ((-b + 2 * v) * Lval) * crossMass.toReal) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hzTop : z ≠ ∞ := by
    dsimp [z, upperMean]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpTop
  have hyTop : y ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hzTop, hpairTop⟩
  have hyPos : 0 < y := by
    have hpathPos : 0 < p := lt_of_lt_of_le
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)) hpathLower
    have hzPos : 0 < z := by
      dsimp [z, upperMean]
      apply ENNReal.mul_pos
      · exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      · exact hpathPos.ne'
    exact lt_of_lt_of_le hzPos (le_add_right le_rfl)
  have hyRealLe : y.toReal ≤ Real.exp ((-b + 2 * v + epsilon) * Lval) := by
    have hsum : y.toReal ≤ z.toReal + (pairBound n).toReal :=
      ENNReal.toReal_add_le
    have hL3 : (ell n : ℝ) ≤ Lval ^ 3 := by
      have hnratio : (ell n : ℝ) / Lval ^ 3 < 1 := by
        simpa [Lval] using hlogCubeLtN
      have hden : 0 < Lval ^ 3 := by positivity
      have hmul := (div_lt_iff₀ hden).mp hnratio
      nlinarith
    have hpolyN : 1 + crossMass.toReal * Lval ^ 3 ≤ Real.exp (epsilon * Lval) := by
      simpa [Lval] using hpoly
    have hexpOrder : Real.exp ((-b + v) * Lval) ≤
        Real.exp ((-b + 2 * v) * Lval) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hv.le hLn.le]
    calc
      y.toReal ≤ z.toReal + (pairBound n).toReal := hsum
      _ ≤ Real.exp ((-b + v) * Lval) +
          (ell n : ℝ) *
            (Real.exp ((-b + 2 * v) * Lval) * crossMass.toReal) :=
        add_le_add hzUpper hpairRealLe
      _ ≤ Real.exp ((-b + 2 * v) * Lval) *
          (1 + crossMass.toReal * Lval ^ 3) := by
        have hmult : (ell n : ℝ) *
            (Real.exp ((-b + 2 * v) * Lval) * crossMass.toReal) ≤
            Lval ^ 3 *
              (Real.exp ((-b + 2 * v) * Lval) * crossMass.toReal) :=
          mul_le_mul_of_nonneg_right hL3
            (mul_nonneg (Real.exp_nonneg _) hcrossRealNonneg)
        calc
          Real.exp ((-b + v) * Lval) +
              (ell n : ℝ) *
                (Real.exp ((-b + 2 * v) * Lval) * crossMass.toReal) ≤
              Real.exp ((-b + 2 * v) * Lval) + Lval ^ 3 *
                (Real.exp ((-b + 2 * v) * Lval) * crossMass.toReal) :=
            add_le_add hexpOrder hmult
          _ = Real.exp ((-b + 2 * v) * Lval) *
              (1 + crossMass.toReal * Lval ^ 3) := by ring
      _ ≤ Real.exp ((-b + 2 * v) * Lval) * Real.exp (epsilon * Lval) :=
        mul_le_mul_of_nonneg_left hpolyN (Real.exp_nonneg _)
      _ = Real.exp ((-b + 2 * v + epsilon) * Lval) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hpzLower : (N n : ℝ) ^ (-b - 2 * v - 3 * epsilon) ≤ (pzMean n).toReal := by
    have hNpos : 0 < (N n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNlarge)
    have hyPower : y.toReal ≤ (N n : ℝ) ^ (-b + 2 * v + epsilon) := by
      rw [Real.rpow_def_of_pos hNpos]
      have hlog : Real.log (N n : ℝ) = Lval := by rfl
      rw [hlog]
      simpa [mul_comm] using hyRealLe
    have hbudget :=
      Asymptotics.ennreal_rpow_div_toReal_ge_of_power_bounds
        hNpos (by norm_num : 0 ≤ (2 : ℝ)) hyTop hyPos hxPower hyPower
    have hexponent : 2 * (-b - epsilon) - (-b + 2 * v + epsilon) =
        -b - 2 * v - 3 * epsilon := by ring
    rw [hexponent] at hbudget
    simpa [pzMean, x, y, z, d] using hbudget
  simpa [pzMean, L, ell, corridor, spineEvent, spineProb, lowerMean,
    upperMean, q, pairBound, pairTerm] using hpzLower

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
