/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Rate.Endpoint.Windows
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Rate.Endpoint.Selection.Lemmas.FixedParameters
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.Rate.SharpUpper

/-!
# Sharp normal-domain rate from floor endpoint windows

The fixed-parameter floor construction is kept in the proof-only module
`Rate/Endpoint/Selection/Lemmas/FixedParameters.lean`. This file selects the
parameters that approach the Brownian constant and combines the resulting
lower rate with the independent finite-cover upper rate.

The public theorems in this file are:

- `neg_half_pi_sq_le_liminf_scaledLog_horizontalTubeProbability_of_floorEndpointWindows`:
  $-\pi^2/2\le\liminf_n(x_n^2/n)\log\mathbb P(T_n)$ for centered
  unit-variance increments, with eventual positivity of the tube event.
- `tendsto_scaledLog_horizontalTubeProbability_of_centeredUnitSecondMoment`:
  $(x_n^2/n)\log\mathbb P(T_n)\to-\pi^2/2$ for the same law.

This is an internal spectral derivation of the constant in A. A. Mogul'skii,
Theorem 3, Section 4, p. 764 of the 1974 Russian original, “Small deviations
in the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4)
(1974), 755–765; English translation, “Small Deviations in a Space of
Trajectories,” *Theory of Probability and Its Applications* 19(1) (1975),
726–736, DOI 10.1137/1119081. This is the rate input used in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.1(i).
-/

open Filter MeasureTheory ProbabilityTheory Topology
open Asymptotics

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The square-root normalization for a positive quadratic denominator. -/
private lemma sqrt_div_sq_of_pos {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q) :
    Real.sqrt (x / q ^ 2) = Real.sqrt x / q := by
  rw [Real.sqrt_div hx, Real.sqrt_sq_eq_abs, abs_of_pos hq]

/-- The `α = 2` spectral-window construction admits parameters whose lower
rate approaches the sharp Brownian constant. The choice is explicit:
`p = 1/C`, `q = 1 - 10/C`, and `δ = p/(100√C)`. -/
theorem neg_half_pi_sq_le_liminf_scaledLog_horizontalTubeProbability_of_floorEndpointWindows
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    (-(Real.pi ^ 2) / 2 ≤ atTop.liminf (fun n => scale n ^ 2 / (n : ℝ) *
      Real.log (horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n).toReal) ∧
      (∀ᶠ n in atTop, 0 < horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n) ∧
      Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => scale n ^ 2 / (n : ℝ) *
        Real.log (horizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal)) := by
  let pSeq : ℝ → ℝ := fun C => 1 / C
  let qSeq : ℝ → ℝ := fun C => 1 - 10 / C
  let δSeq : ℝ → ℝ := fun C => pSeq C / (100 * Real.sqrt C)
  let expRate : ℝ → ℝ := fun C => (C / qSeq C ^ 2) * (-(Real.pi ^ 2) / 2)
  let lowerProbability : ℝ → ℝ := fun C =>
    pSeq C * Real.exp (expRate C) / 4
  let lowerRate : ℝ → ℝ := fun C => (1 / C) * Real.log (lowerProbability C)
  let a : ℝ := Real.pi ^ 2 / 2

  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hlinearExp : Tendsto
      (fun C : ℝ => C * Real.exp (-a * C)) atTop (nhds 0) := by
    have hraw := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
    have heq : (fun C : ℝ => C * Real.exp (-a * C)) =ᶠ[atTop]
        fun C => C ^ (1 : ℝ) * Real.exp (-a * C) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with C hC
      simp [Real.rpow_one]
    exact hraw.congr' heq.symm
  have hexp : Tendsto (fun C : ℝ => Real.exp (-a * C)) atTop (nhds 0) := by
    have hinv : Tendsto (fun C : ℝ => C⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have hprod := hlinearExp.mul hinv
    have heq : (fun C : ℝ => Real.exp (-a * C)) =ᶠ[atTop]
        fun C => C * Real.exp (-a * C) * C⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with C hC
      field_simp [hC.ne']
    simpa using hprod.congr' heq.symm
  have hsmallProduct : Tendsto
      (fun C : ℝ => (1 + 4 * C) * Real.exp (-a * C)) atTop (nhds 0) := by
    have hsum := hexp.add (hlinearExp.const_mul 4)
    have heq : (fun C : ℝ => (1 + 4 * C) * Real.exp (-a * C)) =ᶠ[atTop]
        fun C => Real.exp (-a * C) + 4 * (C * Real.exp (-a * C)) := by
      filter_upwards [] with C
      ring
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum.congr' heq.symm
  have hsmallProductEventually : ∀ᶠ C : ℝ in atTop,
      (1 + 4 * C) * Real.exp (-a * C) < 1 :=
    hsmallProduct.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))

  have hqSeq : Tendsto qSeq atTop (nhds 1) := by
    have hinv : Tendsto (fun C : ℝ => C⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have hdiv : Tendsto (fun C : ℝ => 10 / C) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (10 : ℝ)) atTop (nhds 10)).mul hinv
    simpa [qSeq, sub_eq_add_neg, add_comm] using hdiv.neg.add_const 1
  have hqSq : Tendsto (fun C : ℝ => qSeq C ^ 2) atTop (nhds (1 : ℝ)) := by
    simpa using hqSeq.pow 2
  have hqInv : Tendsto (fun C : ℝ => (qSeq C ^ 2)⁻¹) atTop (nhds (1 : ℝ)) := by
    simpa using hqSq.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hcoefficient : Tendsto
      (fun C : ℝ => (-(Real.pi ^ 2) / 2) * (qSeq C ^ 2)⁻¹)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (-(Real.pi ^ 2) / 2))
        atTop (nhds (-(Real.pi ^ 2) / 2))).mul hqInv
  have hlogDiv : Tendsto (fun C : ℝ => Real.log C / C) atTop (nhds 0) := by
    simpa [pow_one] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0)
  have hconstDiv : Tendsto (fun C : ℝ => Real.log 4 / C) atTop (nhds 0) := by
    have hinv : Tendsto (fun C : ℝ => C⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.log 4) atTop
        (nhds (Real.log 4))).mul hinv
  have hlowerRateLimit : Tendsto lowerRate atTop (nhds (-(Real.pi ^ 2) / 2)) := by
    have hsum := (hlogDiv.neg.add hcoefficient).sub hconstDiv
    have heq : lowerRate =ᶠ[atTop] fun C : ℝ =>
        -(Real.log C / C) + (-(Real.pi ^ 2) / 2) * (qSeq C ^ 2)⁻¹ -
          Real.log 4 / C := by
      filter_upwards [eventually_gt_atTop (40 : ℝ)] with C hC40
      have hC : 0 < C := by linarith
      have hq : 0 < qSeq C := by
        dsimp [qSeq]
        have : 10 / C < 1 / 4 := (div_lt_iff₀ hC).2 (by linarith)
        linarith
      have hp : 0 < pSeq C := by
        dsimp [pSeq]
        positivity
      have hlogP : Real.log (pSeq C) = -Real.log C := by
        dsimp [pSeq]
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hC.ne', Real.log_one]
        ring
      have hlogApp : Real.log (lowerProbability C) =
          Real.log (pSeq C) + expRate C - Real.log 4 := by
        dsimp [lowerProbability]
        rw [Real.log_div (by positivity : pSeq C * Real.exp (expRate C) ≠ 0)
          (by norm_num : (4 : ℝ) ≠ 0)]
        rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp]
      dsimp [lowerRate]
      rw [hlogApp, hlogP]
      dsimp [expRate]
      field_simp [hC.ne', (sq_pos_of_pos hq).ne']
    have hlimit := hsum.congr' heq.symm
    simpa [lowerRate, add_assoc, sub_eq_add_neg, mul_assoc, mul_comm, mul_left_comm,
      neg_div]
      using hlimit

  have hbound : ∀ᶠ C : ℝ in atTop,
      (lowerRate C ≤ atTop.liminf (fun n => scale n ^ 2 / (n : ℝ) *
        Real.log (horizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal) ∧
      (∀ᶠ n in atTop, 0 < horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n) ∧
      Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => scale n ^ 2 / (n : ℝ) *
        Real.log (horizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal)) := by
    filter_upwards [eventually_gt_atTop (40 : ℝ), hsmallProductEventually]
      with C hlarge hdecay
    have hC : 0 < C := by linarith
    let p : ℝ := pSeq C
    let q : ℝ := qSeq C
    let δ : ℝ := δSeq C
    let spectralLower : ℝ := p * Real.exp ((C / q ^ 2) * (-(Real.pi ^ 2) / 2)) / 2
    let applicationLower : ℝ := p * Real.exp ((C / q ^ 2) * (-(Real.pi ^ 2) / 2)) / 4
    have hp : 0 < p := by
      dsimp [p, pSeq]
      positivity
    have hq : 0 < q := by
      dsimp [q, qSeq]
      have hten : 10 / C < 1 / 4 := (div_lt_iff₀ hC).2 (by linarith)
      linarith
    have hqle : q ≤ 1 := by
      dsimp [q, qSeq]
      have : 0 < 10 / C := by positivity
      linarith
    have hpSmall : p < 1 / 32 := by
      dsimp [p, pSeq]
      apply (div_lt_div_iff₀ hC (by norm_num : (0 : ℝ) < 32)).2
      norm_num
      linarith
    have hδ : 0 < δ := by
      dsimp [δ, δSeq]
      positivity
    have hrootC : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
    have hrootRatio : Real.sqrt (C / q ^ 2) = Real.sqrt C / q :=
      sqrt_div_sq_of_pos hC.le hq
    have hqSquareLe : q ^ 2 ≤ 1 := by nlinarith [hq, hqle]
    have hCq : C ≤ C / q ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hq)).2
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hqSquareLe hC.le
    have hnegative : (-(Real.pi ^ 2) / 2) < 0 := by
      have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      linarith
    have hexpCompare :
        Real.exp ((C / q ^ 2) * (-(Real.pi ^ 2) / 2)) ≤
          Real.exp (-a * C) := by
      have harg : (C / q ^ 2) * (-(Real.pi ^ 2) / 2) ≤ -a * C := by
        rw [show -a * C = C * (-(Real.pi ^ 2) / 2) by dsimp [a]; ring]
        exact mul_le_mul_of_nonpos_right hCq hnegative.le
      exact Real.exp_le_exp.mpr harg
    have hsmallDen : 0 < 1 + 4 * C := by positivity
    have hexpSmall : Real.exp (-a * C) < 1 / (1 + 4 * C) := by
      apply (lt_div_iff₀ hsmallDen).2
      nlinarith [hdecay]
    have hsmallIdentity : 1 / (1 + 4 * C) = p / (p + 4) := by
      dsimp [p, pSeq]
      field_simp [hC.ne']
    have hsmallLimit :
        Real.exp ((C / q ^ 2) * (-(Real.pi ^ 2) / 2)) <
          (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p) /
            (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p + 8) := by
      have hsqrtTwo : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hcoefficient :
          4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 2 := by
        nlinarith [hsqrtTwo]
      calc
        Real.exp ((C / q ^ 2) * (-(Real.pi ^ 2) / 2)) ≤ Real.exp (-a * C) :=
          hexpCompare
        _ < 1 / (1 + 4 * C) := hexpSmall
        _ = p / (p + 4) := hsmallIdentity
        _ = (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p) /
              (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p + 8) := by
          rw [hcoefficient]
          field_simp
          ring
    have htargetPos :
        0 < p * Real.exp ((C / q ^ 2) * (-(Real.pi ^ 2) / 2)) :=
      mul_pos hp (Real.exp_pos _)
    have hspectralLower : spectralLower <
        p * Real.exp ((C / q ^ 2) * (-(Real.pi ^ 2) / 2)) := by
      dsimp [spectralLower]
      nlinarith [htargetPos]
    have happlicationLower : 0 < applicationLower := by
      dsimp [applicationLower]
      positivity
    have happlicationLowerOne : applicationLower ≤ 1 := by
      have hexpLeOne :
          Real.exp ((C / q ^ 2) * (-(Real.pi ^ 2) / 2)) ≤ 1 := by
        have harg : (C / q ^ 2) * (-(Real.pi ^ 2) / 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (div_nonneg hC.le (sq_nonneg q))
            hnegative.le
        calc
          Real.exp ((C / q ^ 2) * (-(Real.pi ^ 2) / 2)) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr harg
          _ = 1 := by simp
      have hpLeOne : p ≤ 1 := by
        dsimp [p, pSeq]
        apply (div_le_iff₀ hC).2
        linarith
      dsimp [applicationLower]
      nlinarith [mul_le_mul_of_nonneg_left hexpLeOne hp.le]
    have happlicationBelow : applicationLower < spectralLower := by
      dsimp [applicationLower, spectralLower]
      nlinarith [htargetPos]
    have hreturnMargin : 3 * δ < p / Real.sqrt (C / q ^ 2) := by
      have hqEq : q = 1 - 10 * p := by
        dsimp [q, qSeq, p, pSeq]
        field_simp [hC.ne']
      have hqLower : (3 : ℝ) / 100 < q := by
        have hpBound : p < 1 / 40 := by
          dsimp [p, pSeq]
          apply (div_lt_div_iff₀ hC (by norm_num : (0 : ℝ) < 40)).2
          norm_num
          linarith
        rw [hqEq]
        nlinarith [hpBound]
      have hdeltaScale : δ * Real.sqrt C = p / 100 := by
        dsimp [δ, δSeq]
        rw [show p = pSeq C by rfl]
        field_simp [hrootC.ne']
      have hrightScale : (p / (Real.sqrt C / q)) * Real.sqrt C = p * q := by
        field_simp [hrootC.ne', hq.ne']
      apply lt_of_mul_lt_mul_right ?_ hrootC.le
      rw [hrootRatio]
      rw [show 3 * δ * Real.sqrt C = 3 * (p / 100) by
        calc
          3 * δ * Real.sqrt C = 3 * (δ * Real.sqrt C) := by ring
          _ = 3 * (p / 100) := by rw [hdeltaScale]]
      rw [hrightScale]
      nlinarith [hp, hqLower]
    have houterMargin :
        2 * ((1 / (2 * Real.sqrt (C / q ^ 2)) + 3 * δ) +
          3 * (p / Real.sqrt (C / q ^ 2)) +
          (p / Real.sqrt (C / q ^ 2) + 3 * δ)) * Real.sqrt C < 1 := by
      have hdeltaScale : δ * Real.sqrt C = p / 100 := by
        dsimp [δ, δSeq]
        rw [show p = pSeq C by rfl]
        field_simp [hrootC.ne']
      rw [hrootRatio]
      rw [show δ = (p / 100) / Real.sqrt C by
        apply (eq_div_iff hrootC.ne').2
        simpa [mul_comm] using hdeltaScale]
      rw [show p / (Real.sqrt C / q) = p * q / Real.sqrt C by
        field_simp [hrootC.ne', hq.ne']]
      rw [show 1 / (2 * (Real.sqrt C / q)) = q / (2 * Real.sqrt C) by
        field_simp [hrootC.ne', hq.ne']]
      have hqEq : q = 1 - 10 * p := by
        dsimp [q, qSeq, p, pSeq]
        field_simp [hC.ne']
      have houterEq :
          2 * ((q / (2 * Real.sqrt C) + 3 * ((p / 100) / Real.sqrt C)) +
            3 * (p * q / Real.sqrt C) +
            (p * q / Real.sqrt C + 3 * ((p / 100) / Real.sqrt C))) *
              Real.sqrt C = q + 8 * p * q + 12 * (p / 100) := by
        have hR := hrootC.ne'
        field_simp [hR]
        ring
      rw [houterEq]
      rw [hqEq]
      dsimp [q, qSeq, p, pSeq]
      nlinarith [hC]
    have hrate :=
      one_div_constant_mul_log_toReal_le_liminf_scaledLog_horizontalTubeProbability_of_floorEndpointWindows
        ν hν hscale hB hcontinuous hmeasurable hC hq hp hpSmall hδ hsmallLimit
        (by dsimp [spectralLower]; nlinarith [htargetPos])
        happlicationLower happlicationLowerOne happlicationBelow
        hreturnMargin houterMargin
    simpa [lowerRate, p, pSeq, lowerProbability, expRate, q, qSeq,
      δ, δSeq, spectralLower, applicationLower] using hrate

  have hliminf : -(Real.pi ^ 2) / 2 ≤ atTop.liminf (fun n =>
      scale n ^ 2 / (n : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) (1 / 2) (scale n) n).toReal) :=
    le_of_tendsto hlowerRateLimit (hbound.mono fun _ h => h.1)
  obtain ⟨_, ⟨_, ⟨hpositive, hlowerBounded⟩⟩⟩ := hbound.exists
  exact ⟨hliminf, hpositive, hlowerBounded⟩

/-- The sharp horizontal Mogulskii limit in the normal domain. This joins the
spectral endpoint-window lower bound to the independent finite-cover upper
bound, discharging eventual positivity and logarithmic lower boundedness from
the same return-kernel construction. -/
theorem tendsto_scaledLog_horizontalTubeProbability_of_centeredUnitSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    Tendsto (fun n => scale n ^ 2 / (n : ℝ) *
      Real.log (horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n).toReal)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  have hside := neg_half_pi_sq_le_liminf_scaledLog_horizontalTubeProbability_of_floorEndpointWindows
    ν hν hscale hB hcontinuous hmeasurable
  have hcentered : (∫ x : ℝ, x ∂ν) = 0 := hν.1
  have hsecondMoment : (∫ x : ℝ, x ^ 2 ∂ν) = 1 := hν.2
  have hlowerCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => scale n ^ 2 / (n : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal) :=
    hside.2.2.isCoboundedUnder_le
  have hupper := limsup_scaledLog_horizontalTubeProbability_le_sharp
    ν hcentered hsecondMoment hB hcontinuous hmeasurable hscale
    hside.2.1 hlowerCobounded
  have hprobability (n : ℕ) :
      horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n ≤ 1 := by
    unfold horizontalTubeProbability
    calc
      iidSequenceLaw ν
          {increment | InHorizontalTube (1 / 2) (scale n) n increment} ≤
          iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hupperBounded : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n => scale n ^ 2 / (n : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal) := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 0)
    filter_upwards [] with n
    have hprobTop : horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n ≠ ⊤ :=
      ne_of_lt ((hprobability n).trans_lt ENNReal.one_lt_top)
    have htoRealOne : (horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n).toReal ≤ 1 :=
      (ENNReal.toReal_le_toReal hprobTop ENNReal.one_ne_top).2
        (hprobability n)
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (Real.log_nonpos ENNReal.toReal_nonneg htoRealOne)
  exact tendsto_of_le_liminf_of_limsup_le hside.1 hupper
    hupperBounded hside.2.2

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
