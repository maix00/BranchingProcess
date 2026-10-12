/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.RawRangeRate

/-!
# Uniform finite-variance drawdown bounds from the raw range rate

This module upgrades the sequence form of the raw Mogul'skii range-rate
estimate to a uniform estimate over all horizons that are superdiffusive
relative to the corridor width. It uses only a centered finite second moment.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

private noncomputable def rawRangeBlockExponent (p : ℝ) : ℝ :=
  (4 + p) / (8 + 4 * p)

/-- A centered finite-variance walk has a uniform exponential bound for a
drawdown event with an endpoint threshold proportional to its width. The
bound holds once the width is large and the horizon dominates
`width ^ (2 + p)`. No Brownian-process witness is used. -/
theorem exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    (thresholdFactor p : ℝ) (hthresholdFactor : 0 ≤ thresholdFactor)
    (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ delta : ℝ, delta0 ≤ delta → ∀ horizon : ℕ,
        delta ^ (2 + p) ≤ (horizon : ℝ) →
          iidSequenceLaw ν (noLargeDropEndpointBelowEvent
            horizon delta (thresholdFactor * delta)) ≤
            ENNReal.ofReal (Real.exp
              (-(Real.pi ^ 2 / 4608) * sigma ^ 2 *
                (horizon : ℝ) / delta ^ 2)) := by
  let rangeRate : ℝ := Real.pi ^ 2 / 144
  let rawRate : ℝ := Real.pi ^ 2 / 1152
  let alpha : ℝ := rawRangeBlockExponent p
  have hpden : 0 < 8 + 4 * p := by positivity
  have halphaPos : 0 < alpha := by
    dsimp [alpha, rawRangeBlockExponent]
    positivity
  have halphaHalf : alpha < 1 / 2 := by
    dsimp [alpha, rawRangeBlockExponent]
    rw [div_lt_iff₀ hpden]
    nlinarith
  have hcountPower : 0 < 2 + p - 1 / alpha := by
    have halphaInv : 1 / alpha < 2 + p := by
      rw [div_lt_iff₀ halphaPos]
      dsimp [alpha, rawRangeBlockExponent]
      field_simp
      nlinarith [sq_pos_of_pos hp]
    linarith
  have hblockPower : 0 < 1 / alpha - 2 := by
    have hhalfInv : 2 < 1 / alpha := by
      rw [lt_div_iff₀ halphaPos]
      nlinarith [halphaHalf]
    linarith
  have hratePos : 0 < rawRate := by
    dsimp [rawRate]
    positivity
  have htargetPos : 0 < rawRate := hratePos
  have hfactor : (1 : ℝ) < 2 := by norm_num
  have heta : (0 : ℝ) < 1 := by norm_num
  have hrangeRatePos : 0 < rangeRate := by
    dsimp [rangeRate]
    positivity
  have henergy :
      (Real.pi ^ 2 / 2) *
          (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.rangeCoverUnion
            1 (by omega)).realEnergy = Real.pi ^ 2 / 72 := by
    rw [ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.rangeCoverUnion_realEnergy]
    norm_num
    ring
  have hrateLt : rangeRate < (Real.pi ^ 2 / 2) *
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.rangeCoverUnion
        1 (by omega)).realEnergy := by
    rw [henergy]
    dsimp [rangeRate]
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hgap : rawRate < rangeRate / (2 * (1 + 1) / 2) ^ 2 := by
    dsimp [rawRate, rangeRate]
    norm_num
    nlinarith [sq_pos_of_pos Real.pi_pos]
  by_contra hnotUniform
  have hbad : ∀ delta0 : ℝ, 0 < delta0 →
      ∃ delta : ℝ, delta0 ≤ delta ∧ ∃ horizon : ℕ,
        delta ^ (2 + p) ≤ (horizon : ℝ) ∧
          ¬ iidSequenceLaw ν (noLargeDropEndpointBelowEvent
              horizon delta (thresholdFactor * delta)) ≤
            ENNReal.ofReal (Real.exp
              (-(Real.pi ^ 2 / 4608) * sigma ^ 2 *
                (horizon : ℝ) / delta ^ 2)) := by
    intro delta0 hdelta0
    by_contra hnotBad
    apply hnotUniform
    refine ⟨delta0, hdelta0, ?_⟩
    intro delta hdelta horizon hlarge
    by_contra hnotBound
    exact hnotBad ⟨delta, hdelta, horizon, hlarge, hnotBound⟩
  have hbadNat : ∀ n : ℕ, ∃ delta : ℝ, (n : ℝ) ≤ delta ∧
      ∃ horizon : ℕ, delta ^ (2 + p) ≤ (horizon : ℝ) ∧
        ¬ iidSequenceLaw ν (noLargeDropEndpointBelowEvent
            horizon delta (thresholdFactor * delta)) ≤
          ENNReal.ofReal (Real.exp
            (-(Real.pi ^ 2 / 4608) * sigma ^ 2 *
              (horizon : ℝ) / delta ^ 2)) := by
    intro n
    obtain ⟨delta, hdelta, horizon, hlarge, hbadBound⟩ :=
      hbad (max (n : ℝ) 1) (lt_of_lt_of_le (by norm_num)
        (le_max_right _ _))
    exact ⟨delta, le_trans (le_max_left _ _) hdelta,
      horizon, hlarge, hbadBound⟩
  choose delta hdeltaLower horizon hpower hbadBound using hbadNat
  have hdeltaTop : Tendsto delta atTop atTop :=
    tendsto_atTop_mono' atTop (Filter.Eventually.of_forall hdeltaLower)
      tendsto_natCast_atTop_atTop
  have hdeltaPos : ∀ᶠ n : ℕ in atTop, 0 < delta n :=
    hdeltaTop.eventually_gt_atTop 0

  let scale : ℕ → ℝ := fun n => (n : ℝ) ^ alpha
  let argument : ℕ → ℝ := fun n => (2 * delta n) ^ (1 / alpha)
  let length : ℕ → ℕ := fun n => ⌊argument n⌋₊
  let rawDelta : ℕ → ℝ := fun n => scale (length n + 1) / 2
  let blocks : ℕ → ℕ := fun n => horizon n / length n
  let totalCost : ℕ → ℝ := fun n => (horizon n : ℝ) / rawDelta n ^ 2
  let blockCost : ℕ → ℝ := fun n => ((length n + 1 : ℕ) : ℝ) / rawDelta n ^ 2

  have hscale : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n) := by
    apply Asymptotics.IsSmallDeviationScale.of_tendsto
    · dsimp [scale]
      exact (_root_.tendsto_rpow_atTop halphaPos).comp
        tendsto_natCast_atTop_atTop
    · have hexp : 0 < 1 / 2 - alpha := by linarith
      have hpow0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 - alpha)))
          atTop (𝓝 0) :=
        (_root_.tendsto_rpow_neg_atTop hexp).comp
          tendsto_natCast_atTop_atTop
      have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (alpha - 1 / 2))
          atTop (𝓝 0) := by
        have heq : alpha - 1 / 2 = -(1 / 2 - alpha) := by ring
        simpa only [heq] using hpow0
      have heq : (fun n : ℕ => scale n / Real.sqrt n) =ᶠ[atTop]
          fun n => (n : ℝ) ^ (alpha - 1 / 2) := by
        filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
        have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
        rw [show Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) by
          rw [Real.sqrt_eq_rpow]]
        dsimp [scale]
        rw [← Real.rpow_sub hnReal]
      exact hpow.congr' heq.symm

  have hargumentTop : Tendsto argument atTop atTop := by
    dsimp [argument]
    have hbase : Tendsto (fun n => 2 * delta n) atTop atTop := by
      simpa [mul_comm] using hdeltaTop.const_mul_atTop (by norm_num : 0 < (2 : ℝ))
    exact (_root_.tendsto_rpow_atTop (by positivity : 0 < 1 / alpha)).comp hbase
  have hlengthTop : Tendsto length atTop atTop := by
    dsimp [length]
    exact tendsto_nat_floor_atTop.comp hargumentTop
  have hlengthSuccTop : Tendsto (fun n => length n + 1) atTop atTop := by
    exact tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall fun n => Nat.le_add_right (length n) 1)
      hlengthTop
  have hlengthRealTop : Tendsto (fun n => (length n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hlengthTop

  have hargumentPos : ∀ᶠ n : ℕ in atTop, 0 < argument n := by
    filter_upwards [hdeltaPos] with n hn
    dsimp [argument]
    positivity
  have hargumentGeOne : ∀ᶠ n : ℕ in atTop, 1 ≤ argument n := by
    have h := hargumentTop.eventually (eventually_ge_atTop (1 : ℝ))
    exact h
  have hrawBounds : ∀ᶠ n : ℕ in atTop,
      delta n ≤ rawDelta n ∧ rawDelta n ≤ 2 * delta n := by
    filter_upwards [hdeltaPos, hargumentGeOne] with n hδ harg
    have hxpow : argument n ^ alpha = 2 * delta n := by
      dsimp [argument]
      calc
        ((2 * delta n) ^ (1 / alpha)) ^ alpha =
            (2 * delta n) ^ ((1 / alpha) * alpha) :=
          (Real.rpow_mul (by positivity : 0 ≤ 2 * delta n) _ _).symm
        _ = 2 * delta n := by
          have hexp : (1 / alpha) * alpha = 1 := by
            field_simp [ne_of_gt halphaPos]
          rw [hexp, Real.rpow_one]
    have hfloorLower : argument n ≤ (length n + 1 : ℕ) := by
      exact_mod_cast (Nat.lt_floor_add_one (argument n)).le
    have hfloorUpper : (length n + 1 : ℕ) ≤ argument n + 1 := by
      have h := Nat.floor_le (le_of_lt (by positivity : 0 < argument n))
      exact_mod_cast (by linarith : (length n : ℝ) + 1 ≤ argument n + 1)
    have hfloorUpper' : (length n + 1 : ℕ) ≤ 2 * argument n := by
      exact le_trans hfloorUpper (by nlinarith [harg])
    have hpowLower : argument n ^ alpha ≤ ((length n + 1 : ℕ) : ℝ) ^ alpha :=
      Real.rpow_le_rpow (le_of_lt (by positivity)) (by exact_mod_cast hfloorLower)
        (le_of_lt halphaPos)
    have hpowUpper : ((length n + 1 : ℕ) : ℝ) ^ alpha ≤
        (2 * argument n) ^ alpha :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hfloorUpper')
        (le_of_lt halphaPos)
    have hpowTwo : (2 : ℝ) ^ alpha ≤ 2 := by
      calc
        2 ^ alpha ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := by norm_num
    have hmulRpow : (2 * argument n) ^ alpha =
        2 ^ alpha * argument n ^ alpha :=
      Real.mul_rpow (by norm_num) (le_of_lt (by positivity))
    have hraw : rawDelta n = ((length n + 1 : ℕ) : ℝ) ^ alpha / 2 := by
      rfl
    constructor
    · rw [hraw]
      have hlow : 2 * delta n ≤ ((length n + 1 : ℕ) : ℝ) ^ alpha := by
        rw [← hxpow]
        exact hpowLower
      linarith
    · rw [hraw]
      calc
        ((length n + 1 : ℕ) : ℝ) ^ alpha / 2 ≤
            (2 * argument n) ^ alpha / 2 :=
          div_le_div_of_nonneg_right hpowUpper (by norm_num)
        _ = 2 ^ alpha * argument n ^ alpha / 2 := by rw [hmulRpow]
        _ ≤ 2 * delta n := by rw [hxpow]; nlinarith

  have hrawPos : ∀ᶠ n : ℕ in atTop, 0 < rawDelta n := by
    filter_upwards [hrawBounds, hdeltaPos] with n hraw hδ
    exact lt_of_lt_of_le hδ hraw.1
  have hblockCostTop : Tendsto blockCost atTop atTop := by
    have hlower : ∀ᶠ n : ℕ in atTop,
        delta n ^ (1 / alpha - 2) / 4 ≤ blockCost n := by
      filter_upwards [hdeltaPos, hrawBounds] with n hδ hraw
      have hargLower : delta n ^ (1 / alpha) ≤ argument n := by
        dsimp [argument]
        have hbase : delta n ≤ 2 * delta n := by linarith
        exact Real.rpow_le_rpow (le_of_lt hδ) hbase (by positivity)
      have hlengthLower : argument n ≤ (length n + 1 : ℕ) := by
        exact_mod_cast (Nat.lt_floor_add_one (argument n)).le
      have hrawSq : rawDelta n ^ 2 ≤ 4 * delta n ^ 2 := by
        nlinarith [hraw.2]
      have hnum : delta n ^ (1 / alpha) ≤ ((length n + 1 : ℕ) : ℝ) :=
        le_trans hargLower (by exact_mod_cast hlengthLower)
      have hratio : delta n ^ (1 / alpha) / (4 * delta n ^ 2) ≤
          ((length n + 1 : ℕ) : ℝ) / rawDelta n ^ 2 := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        calc
          delta n ^ (1 / alpha) * rawDelta n ^ 2 ≤
              ((length n + 1 : ℕ) : ℝ) * rawDelta n ^ 2 :=
            mul_le_mul_of_nonneg_right hnum (sq_nonneg _)
          _ ≤ ((length n + 1 : ℕ) : ℝ) * (4 * delta n ^ 2) := by
            exact mul_le_mul_of_nonneg_left hrawSq (by positivity)
      have hpow : delta n ^ (1 / alpha) / (4 * delta n ^ 2) =
          delta n ^ (1 / alpha - 2) / 4 := by
        rw [Real.rpow_sub hδ]
        have hsq : delta n ^ (2 : ℝ) = delta n ^ (2 : ℕ) :=
          Real.rpow_natCast _ _
        rw [hsq]
        ring
      rw [hpow] at hratio
      change delta n ^ (1 / alpha - 2) / 4 ≤ blockCost n
      simpa [blockCost] using hratio
    have hpowTop : Tendsto (fun n : ℕ => delta n ^ (1 / alpha - 2))
        atTop atTop :=
      (_root_.tendsto_rpow_atTop hblockPower).comp hdeltaTop
    have hscaledTop : Tendsto
        (fun n => delta n ^ (1 / alpha - 2) / 4) atTop atTop := by
      simpa [div_eq_mul_inv, mul_comm] using
        hpowTop.const_mul_atTop (by norm_num : 0 < (1 / 4 : ℝ))
    exact tendsto_atTop_mono' atTop hlower hscaledTop

  have htotalCostTop : Tendsto totalCost atTop atTop := by
    have hlower : ∀ᶠ n : ℕ in atTop,
        delta n ^ p / 4 ≤ totalCost n := by
      filter_upwards [hdeltaPos, hrawBounds, Filter.Eventually.of_forall hpower]
        with n hδ hraw hlarge
      have hrawSq : rawDelta n ^ 2 ≤ 4 * delta n ^ 2 := by
        nlinarith [hraw.2]
      have hden : 0 < rawDelta n ^ 2 := by positivity
      have hratio :
          (horizon n : ℝ) / (4 * delta n ^ 2) ≤
            (horizon n : ℝ) / rawDelta n ^ 2 :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden
          (by nlinarith [hrawSq])
      have hpowerDiv : delta n ^ p ≤ (horizon n : ℝ) / delta n ^ 2 := by
        have hpowEq : delta n ^ (2 + p) = delta n ^ 2 * delta n ^ p := by
          rw [Real.rpow_add hδ]
          congr 1
          exact Real.rpow_natCast _ _
        apply (le_div_iff₀ (sq_pos_of_pos hδ)).2
        calc
          delta n ^ p * delta n ^ 2 = delta n ^ 2 * delta n ^ p := by ring
          _ = delta n ^ (2 + p) := hpowEq.symm
          _ ≤ (horizon n : ℝ) := hlarge
      have hquarter : delta n ^ p / 4 ≤
          (horizon n : ℝ) / (4 * delta n ^ 2) := by
        have h := div_le_div_of_nonneg_right hpowerDiv
          (by norm_num : (0 : ℝ) ≤ 4)
        have heq : ((horizon n : ℝ) / delta n ^ 2) / 4 =
            (horizon n : ℝ) / (4 * delta n ^ 2) := by ring
        rw [heq] at h
        exact h
      have hresult := le_trans hquarter hratio
      simpa [totalCost] using hresult
    have hpowTop : Tendsto (fun n : ℕ => delta n ^ p) atTop atTop :=
      (_root_.tendsto_rpow_atTop hp).comp hdeltaTop
    have hquarterTop : Tendsto (fun n => delta n ^ p / 4) atTop atTop := by
      simpa [div_eq_mul_inv, mul_comm] using hpowTop.const_mul_atTop
        (by norm_num : 0 < (1 / 4 : ℝ))
    exact tendsto_atTop_mono' atTop hlower hquarterTop

  have hcountQuotTop : Tendsto
      (fun n => (horizon n : ℝ) / (length n : ℝ)) atTop atTop := by
    have hlower : ∀ᶠ n : ℕ in atTop,
        ((2 ^ (1 / alpha))⁻¹) * delta n ^ (2 + p - 1 / alpha) ≤
          (horizon n : ℝ) / (length n : ℝ) := by
      filter_upwards [hdeltaPos, hlengthTop.eventually_gt_atTop 0,
        Filter.Eventually.of_forall hpower] with n hδ hlen hlarge
      have hlenPos : 0 < (length n : ℝ) := by exact_mod_cast hlen
      have hargEq : argument n = 2 ^ (1 / alpha) * delta n ^ (1 / alpha) := by
        dsimp [argument]
        rw [Real.mul_rpow (by norm_num) hδ.le]
      have hlenLe : (length n : ℝ) ≤ argument n := by
        exact_mod_cast (Nat.floor_le (by positivity : 0 ≤ argument n))
      have hden : 0 < argument n := by positivity
      have hquot : (horizon n : ℝ) / argument n ≤
          (horizon n : ℝ) / (length n : ℝ) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlenPos hlenLe
      have hpowerQuot :
          ((2 ^ (1 / alpha))⁻¹) * delta n ^ (2 + p - 1 / alpha) ≤
            (horizon n : ℝ) / argument n := by
        rw [hargEq]
        have hconst : 0 < (2 : ℝ) ^ (1 / alpha) := by positivity
        have hδpow : 0 < delta n ^ (1 / alpha) := by positivity
        have hpowers : delta n ^ (2 + p - 1 / alpha) *
            delta n ^ (1 / alpha) = delta n ^ (2 + p) := by
          rw [← Real.rpow_add hδ]
          congr 1
          ring
        apply (le_div_iff₀ (mul_pos hconst hδpow)).2
        calc
          ((2 ^ (1 / alpha))⁻¹ * delta n ^ (2 + p - 1 / alpha)) *
              (2 ^ (1 / alpha) * delta n ^ (1 / alpha)) =
                delta n ^ (2 + p) := by
            calc
              _ = ((2 : ℝ) ^ (1 / alpha))⁻¹ * (2 ^ (1 / alpha)) *
                    (delta n ^ (2 + p - 1 / alpha) * delta n ^ (1 / alpha)) := by ring
              _ = delta n ^ (2 + p) := by rw [inv_mul_cancel₀ hconst.ne', hpowers]; simp
          _ ≤ (horizon n : ℝ) := hlarge
      exact le_trans hpowerQuot hquot
    have hpowTop : Tendsto
        (fun n : ℕ => delta n ^ (2 + p - 1 / alpha)) atTop atTop :=
      (_root_.tendsto_rpow_atTop hcountPower).comp hdeltaTop
    have hscaledTop : Tendsto
        (fun n => (2 ^ (1 / alpha))⁻¹ *
          delta n ^ (2 + p - 1 / alpha)) atTop atTop :=
      hpowTop.const_mul_atTop (inv_pos.mpr (by positivity))
    exact tendsto_atTop_mono' atTop hlower hscaledTop

  have hblocksTop : Tendsto blocks atTop atTop := by
    have hfloorTop : Tendsto
        (fun n => ⌊(horizon n : ℝ) / (length n : ℝ)⌋₊) atTop atTop :=
      tendsto_nat_floor_atTop.comp hcountQuotTop
    simpa [blocks, Nat.floor_div_eq_div] using hfloorTop

  have hcomplete : ∀ᶠ n : ℕ in atTop, blocks n * length n ≤ horizon n := by
    filter_upwards [] with n
    exact Nat.div_mul_le_self _ _
  have hblockCoverage : Tendsto
      (fun n => (blocks n : ℝ) / ((horizon n : ℝ) / (length n : ℝ)))
      atTop (𝓝 1) := by
    have hfloor : Tendsto
        (fun n => (⌊(horizon n : ℝ) / (length n : ℝ)⌋₊ : ℝ) /
          ((horizon n : ℝ) / (length n : ℝ))) atTop (𝓝 1) :=
      tendsto_nat_floor_div_atTop.comp hcountQuotTop
    simpa [blocks, Nat.floor_div_eq_div] using hfloor
  have hlengthRatio : Tendsto
      (fun n => ((length n + 1 : ℕ) : ℝ) / (length n : ℝ))
      atTop (𝓝 1) := by
    have hinv : Tendsto (fun n => (length n : ℝ)⁻¹) atTop (𝓝 0) :=
      hlengthRealTop.inv_tendsto_atTop
    have hsum : Tendsto (fun n => (1 : ℝ) + (length n : ℝ)⁻¹)
        atTop (𝓝 1) := by simpa using tendsto_const_nhds.add hinv
    have heq : (fun n => ((length n + 1 : ℕ) : ℝ) / (length n : ℝ)) =ᶠ[atTop]
        fun n => 1 + (length n : ℝ)⁻¹ := by
      filter_upwards [hlengthTop.eventually_gt_atTop 0] with n hn
      have hnReal : (length n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      have hcast : ((length n + 1 : ℕ) : ℝ) = (length n : ℝ) + 1 := by norm_num
      rw [hcast]
      field_simp [hnReal]
    exact hsum.congr' heq.symm
  have hcoverageProduct : Tendsto
      (fun n => (blocks n : ℝ) / ((horizon n : ℝ) / (length n : ℝ)) *
        (((length n + 1 : ℕ) : ℝ) / (length n : ℝ)))
      atTop (𝓝 1) := by
    simpa using hblockCoverage.mul hlengthRatio
  have hcovered : Tendsto
      (fun n => (blocks n : ℝ) * blockCost n / totalCost n)
      atTop (𝓝 1) := by
    have heq : (fun n => (blocks n : ℝ) * blockCost n / totalCost n) =ᶠ[atTop]
        fun n => (blocks n : ℝ) / ((horizon n : ℝ) / (length n : ℝ)) *
          (((length n + 1 : ℕ) : ℝ) / (length n : ℝ)) := by
      filter_upwards [hrawPos, hlengthTop.eventually_gt_atTop 0,
        hcountQuotTop.eventually_gt_atTop 0] with n hraw hlen hquot
      have hδrawNe : rawDelta n ≠ 0 := ne_of_gt hraw
      have hlenNe : (length n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hlen)
      have hHNe : (horizon n : ℝ) ≠ 0 := by
        have hq : 0 < (horizon n : ℝ) / (length n : ℝ) := hquot
        have hHpos : 0 < (horizon n : ℝ) := by
          have hlenpos : 0 < (length n : ℝ) := by positivity
          exact (div_pos_iff_of_pos_right hlenpos).mp hq
        exact ne_of_gt hHpos
      dsimp [blockCost, totalCost]
      field_simp [hδrawNe, hlenNe, hHNe]
    exact hcoverageProduct.congr' heq.symm

  have hwidth : ∀ᶠ n : ℕ in atTop, rawDelta n = 1 * rawDelta n := by
    filter_upwards [] with n
    ring
  have hthreshold : ∀ᶠ n : ℕ in atTop,
      ⌊(thresholdFactor * rawDelta n + rawDelta n) / rawDelta n⌋₊ =
        ⌊thresholdFactor + 1⌋₊ := by
    filter_upwards [hrawPos] with n hraw
    congr 1
    field_simp [ne_of_gt hraw]
  have hscaleBlock : ∀ᶠ n : ℕ in atTop,
      scale (length n + 1) = (2 * (1 + 1) / 2) * rawDelta n := by
    filter_upwards [] with n
    dsimp [rawDelta]
    ring

  have hrawBound :=
    eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_rangeRate_of_centeredSecondMoment
      (ν := ν) hν hsigma hscale
      (horizon := horizon) (blocks := blocks) (length := length)
      (delta := rawDelta) (width := rawDelta)
      (threshold := fun n => thresholdFactor * rawDelta n)
      (K := ⌊thresholdFactor + 1⌋₊) (k := 1)
      (factor := 2) (eta := 1) (rangeRate := rangeRate) (targetRate := rawRate)
      hfactor heta hrangeRatePos (by omega) hrateLt hratePos
      hlengthSuccTop hblocksTop hblockCostTop htotalCostTop hcovered hcomplete
      hwidth hthreshold hscaleBlock hgap
  have hrawLower : ∀ᶠ n : ℕ in atTop, delta n ≤ rawDelta n :=
    hrawBounds.mono fun n h => h.1
  have hrawUpper : ∀ᶠ n : ℕ in atTop, rawDelta n ≤ 2 * delta n :=
    hrawBounds.mono fun n h => h.2
  have hrawExpCompare : ∀ᶠ n : ℕ in atTop,
      Real.exp (-rawRate * sigma ^ 2 * ((horizon n : ℝ) / rawDelta n ^ 2)) ≤
        Real.exp (-(Real.pi ^ 2 / 4608) * sigma ^ 2 *
          (horizon n : ℝ) / delta n ^ 2) := by
    filter_upwards [hdeltaPos, hrawPos, hrawUpper] with n hδ hraw hupper
    have hrawsq : rawDelta n ^ 2 ≤ 4 * delta n ^ 2 := by nlinarith
    have hratio : (horizon n : ℝ) / (4 * delta n ^ 2) ≤
        (horizon n : ℝ) / rawDelta n ^ 2 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (sq_pos_of_pos hraw)
        (by nlinarith [hrawsq])
    have hcoef : 0 < rawRate * sigma ^ 2 := by positivity
    have hexp : -rawRate * sigma ^ 2 *
          ((horizon n : ℝ) / rawDelta n ^ 2) ≤
        -(Real.pi ^ 2 / 4608) * sigma ^ 2 *
          (horizon n : ℝ) / delta n ^ 2 := by
      have hmul := mul_le_mul_of_nonpos_left hratio (neg_nonpos.mpr hcoef.le)
      have hrateEq : rawRate / 4 = Real.pi ^ 2 / 4608 := by
        dsimp [rawRate]
        ring
      calc
        -rawRate * sigma ^ 2 * ((horizon n : ℝ) / rawDelta n ^ 2) =
            -(rawRate * sigma ^ 2) *
              ((horizon n : ℝ) / rawDelta n ^ 2) := by ring
        _ ≤ -(rawRate * sigma ^ 2) *
              ((horizon n : ℝ) / (4 * delta n ^ 2)) := hmul
        _ = -(Real.pi ^ 2 / 4608) * sigma ^ 2 *
              (horizon n : ℝ) / delta n ^ 2 := by
          rw [← hrateEq]
          ring
    exact Real.exp_le_exp.mpr hexp
  have hgood : ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν (noLargeDropEndpointBelowEvent
        (horizon n) (delta n) (thresholdFactor * delta n)) ≤
        ENNReal.ofReal (Real.exp
          (-(Real.pi ^ 2 / 4608) * sigma ^ 2 *
            (horizon n : ℝ) / delta n ^ 2)) := by
    filter_upwards [hrawBound, hrawLower, hrawExpCompare]
      with n hbound hlower hexp
    have hsubset : noLargeDropEndpointBelowEvent (horizon n) (delta n)
        (thresholdFactor * delta n) ⊆
        noLargeDropEndpointBelowEvent (horizon n) (rawDelta n)
          (thresholdFactor * rawDelta n) := by
      intro increment h
      refine ⟨?_, ?_⟩
      · intro i j hij hj
        exact le_trans (h.1 i j hij hj) hlower
      · have hfactorMono : thresholdFactor * delta n ≤
          thresholdFactor * rawDelta n :=
            mul_le_mul_of_nonneg_left hlower hthresholdFactor
        exact le_trans h.2 hfactorMono
    have hmeasure := (measure_mono hsubset).trans hbound
    have hexpENN : ENNReal.ofReal
          (Real.exp (-rawRate * sigma ^ 2 *
            ((horizon n : ℝ) / rawDelta n ^ 2))) ≤
        ENNReal.ofReal (Real.exp
          (-(Real.pi ^ 2 / 4608) * sigma ^ 2 *
            (horizon n : ℝ) / delta n ^ 2)) :=
      (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).2 hexp
    exact hmeasure.trans hexpENN
  obtain ⟨n, hn⟩ := hgood.exists
  exact hbadBound n hn

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end
