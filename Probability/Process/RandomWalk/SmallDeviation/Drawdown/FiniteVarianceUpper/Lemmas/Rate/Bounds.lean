/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Lemmas.JumpPattern.UnionBound
import Analysis.Asymptotics.Scale.IntermediatePowerBlock
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Asymptotic bounds for drawdown block parameters

The proof-specific declarations are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.jumpPatternProbability_le_exp`: $2^q p^{q-K}\le e^{-dz}$ under the
  block-count, entropy, and jump-count bounds used in the union estimate.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.eventually_drawdownCeilingBinWidth_bounds` and
  `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.eventually_drawdownTubeBlockExponent_le`: for large $\Delta$, the chosen
  ceiling bin width satisfies the size bound, and the block exponent obeys
  the rate inequality required by the proof. The generic floor estimate is
  `Asymptotics.eventually_nat_floor_rpow_intermediate_bounds`.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownBlockCount_scaledBounds` and `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownJumpCount_add_one_le`:
  the number of complete blocks and maximum jumps obey the scaled estimates
  used to apply `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.jumpPatternProbability_le_exp`.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.measureReal_noLargeDropEvent_le_exp_of_blockParameters`: fixed block and
  bin parameters give the exponential drawdown bound.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.exists_drawdownBlockExponent` and
  `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.eventually_drawdownScaleAbsorptions`: choose the auxiliary exponent and
  absorb the remaining powers of $\Delta$ into the final rate.

These estimates assemble the asymptotic parameter choices in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.3.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

private theorem exp_pow_nat (x : ℝ) (n : ℕ) :
    Real.exp x ^ n = Real.exp ((n : ℝ) * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        Real.exp x ^ (n + 1) = Real.exp x ^ n * Real.exp x := by
          rw [pow_succ]
        _ = Real.exp ((n : ℝ) * x) * Real.exp x := by rw [ih]
        _ = Real.exp ((n : ℝ) * x + x) := by rw [← Real.exp_add]
        _ = Real.exp (((n : ℝ) + 1) * x) := by
          congr 1
          ring
        _ = Real.exp (((n + 1 : ℕ) : ℝ) * x) := by
          congr 1
          rw [Nat.cast_succ]

lemma jumpPatternProbability_le_exp
    {q K : ℕ} {z t eta d : ℝ}
    (hz : 0 ≤ z) (ht : 0 < t) (heta : 0 < eta) (hd : 0 < d)
    (hqLower : z / t - 1 ≤ (q : ℝ))
    (hqUpper : (q : ℝ) ≤ z / Real.sqrt t)
    (hqK : K ≤ q)
    (hentropy : Real.log 2 / Real.sqrt t ≤ d * eta)
    (hjump : d * (1 + 2 * eta) * t * ((K : ℝ) + 1) ≤ d * eta * z) :
    (2 : ℝ) ^ q * Real.exp (-d * (1 + 2 * eta) * t) ^ (q - K) ≤
      Real.exp (-d * z) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hqEntropy : (q : ℝ) * Real.log 2 ≤ d * eta * z := by
    calc
      (q : ℝ) * Real.log 2 ≤ (z / Real.sqrt t) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hqUpper hlog2.le
      _ = (Real.log 2 / Real.sqrt t) * z := by ring
      _ ≤ d * eta * z := mul_le_mul_of_nonneg_right hentropy hz
  have hqSub : ((q - K : ℕ) : ℝ) = (q : ℝ) - (K : ℝ) := by
    rw [Nat.cast_sub hqK]
  have hcoef : 0 < d * (1 + 2 * eta) * t := by positivity
  have hqLowerMul :
      -(d * (1 + 2 * eta) * t) * (q : ℝ) ≤
        -(d * (1 + 2 * eta) * t) * (z / t - 1) :=
    mul_le_mul_of_nonpos_left hqLower (neg_nonpos.mpr hcoef.le)
  have hnegative :
      -(d * (1 + 2 * eta) * t) * ((q - K : ℕ) : ℝ) ≤
        -d * (1 + 2 * eta) * z +
          d * (1 + 2 * eta) * t * ((K : ℝ) + 1) := by
    rw [hqSub]
    calc
      -(d * (1 + 2 * eta) * t) * ((q : ℝ) - (K : ℝ)) =
          -(d * (1 + 2 * eta) * t) * (q : ℝ) +
            d * (1 + 2 * eta) * t * (K : ℝ) := by ring
      _ ≤ -(d * (1 + 2 * eta) * t) * (z / t - 1) +
            d * (1 + 2 * eta) * t * (K : ℝ) :=
        by nlinarith [hqLowerMul]
      _ = -d * (1 + 2 * eta) * z +
            d * (1 + 2 * eta) * t * ((K : ℝ) + 1) := by
        field_simp [ht.ne']
        ring
  have hexponent :
      (q : ℝ) * Real.log 2 -
        d * (1 + 2 * eta) * t * ((q - K : ℕ) : ℝ) ≤ -d * z := by
    calc
      (q : ℝ) * Real.log 2 -
          d * (1 + 2 * eta) * t * ((q - K : ℕ) : ℝ) =
          (q : ℝ) * Real.log 2 +
            (-(d * (1 + 2 * eta) * t) * ((q - K : ℕ) : ℝ)) := by ring
      _ ≤ d * eta * z +
            (-d * (1 + 2 * eta) * z +
              d * (1 + 2 * eta) * t * ((K : ℝ) + 1)) :=
        add_le_add hqEntropy hnegative
      _ ≤ d * eta * z + (-d * (1 + 2 * eta) * z + d * eta * z) := by
        nlinarith [hjump]
      _ = -d * z := by ring
  have hpowTwo : (2 : ℝ) ^ q = Real.exp ((q : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ q = (Real.exp (Real.log 2)) ^ q := by
        rw [Real.exp_log (by norm_num)]
      _ = Real.exp ((q : ℝ) * Real.log 2) := exp_pow_nat _ _
  have hpowExp :
      Real.exp (-d * (1 + 2 * eta) * t) ^ (q - K) =
        Real.exp ((-d * (1 + 2 * eta) * t) * ((q - K : ℕ) : ℝ)) := by
    convert exp_pow_nat
      (-(d * (1 + 2 * eta) * t)) (q - K) using 1 <;> ring
  calc
    (2 : ℝ) ^ q * Real.exp (-d * (1 + 2 * eta) * t) ^ (q - K) =
        Real.exp ((q : ℝ) * Real.log 2 -
          d * (1 + 2 * eta) * t * ((q - K : ℕ) : ℝ)) := by
            rw [hpowTwo, hpowExp, ← Real.exp_add]
            congr 1
            ring
    _ ≤ Real.exp (-d * z) := Real.exp_le_exp.mpr hexponent

private theorem eventually_real_rpow_ge_const
    {power bound : ℝ} (hpower : 0 < power) :
    ∀ᶠ x : ℝ in atTop, bound ≤ x ^ power := by
  exact (_root_.tendsto_rpow_atTop hpower).eventually
    (eventually_ge_atTop bound)

lemma eventually_drawdownCeilingBinWidth_bounds
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ Delta : ℝ in atTop,
      1 ≤ Delta ∧
      Delta + (⌈eta * Delta⌉₊ : ℝ) ≤ (1 + 2 * eta) * Delta := by
  filter_upwards [eventually_ge_atTop (1 / eta : ℝ),
      eventually_ge_atTop (1 : ℝ)] with Delta hDeltaEta hDelta
  have hDeltaPos : 0 < Delta := by linarith
  have hEtaDelta : 1 ≤ eta * Delta := by
    have h := (div_le_iff₀ heta).mp hDeltaEta
    nlinarith [h]
  have hceilLower : eta * Delta ≤ (⌈eta * Delta⌉₊ : ℝ) := by
    exact_mod_cast (Nat.le_ceil (eta * Delta))
  have hceilUpper : (⌈eta * Delta⌉₊ : ℝ) < eta * Delta + 1 := by
    exact_mod_cast (Nat.ceil_lt_add_one (mul_nonneg heta.le hDeltaPos.le))
  refine ⟨hDelta, ?_⟩
  calc
    Delta + (⌈eta * Delta⌉₊ : ℝ) ≤ Delta + (eta * Delta + 1) := by
      linarith
    _ ≤ Delta + 2 * eta * Delta := by nlinarith
    _ = (1 + 2 * eta) * Delta := by ring

lemma eventually_drawdownTubeBlockExponent_le
    {eta d : ℝ} (heta : 0 < eta) (hd : 0 < d) :
    ∀ᶠ Delta : ℝ in atTop,
      (⌈eta * Delta⌉₊ + Delta) ^ (eta / 2) -
        d * (1 + 2 * eta) ^ 4 *
          ((⌊Delta ^ (2 + eta)⌋₊ : ℝ) /
            (⌈eta * Delta⌉₊ + Delta) ^ 2) ≤
        -d * (1 + 2 * eta) * Delta ^ eta := by
  let B : ℝ := 1 + 2 * eta
  let A : ℝ := B ^ (eta / 2) + d * B ^ 2
  let R : ℝ := 2 * d * eta * B
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hgrowth := eventually_real_rpow_ge_const
    (power := eta / 2) (bound := A / R) (by linarith)
  filter_upwards [Asymptotics.eventually_nat_floor_rpow_intermediate_bounds
      (p := 2 + eta / 2) (q := 2 + eta) (by linarith) (by linarith),
      eventually_drawdownCeilingBinWidth_bounds heta, hgrowth] with
      Delta hfloor hceil hgrowth
  have hDelta : 1 ≤ Delta := hceil.1
  have hDeltaPos : 0 < Delta := by linarith
  let width : ℝ := (⌈eta * Delta⌉₊ : ℝ) + Delta
  let length : ℝ := (⌊Delta ^ (2 + eta)⌋₊ : ℝ)
  let g : ℝ := Delta ^ (eta / 2)
  let a : ℝ := Delta ^ eta
  have hwidthPos : 0 < width := by dsimp [width]; positivity
  have hwidthUpper : width ≤ B * Delta := by
    dsimp [width, B]
    simpa [add_comm] using hceil.2
  have hwidthPow : width ^ (eta / 2) ≤ B ^ (eta / 2) * g := by
    calc
      width ^ (eta / 2) ≤ (B * Delta) ^ (eta / 2) := by
        apply Real.rpow_le_rpow (le_of_lt hwidthPos) hwidthUpper
        linarith
      _ = B ^ (eta / 2) * g := by
        rw [Real.mul_rpow hB.le hDeltaPos.le]
  have hpowerEta : Delta ^ (2 + eta) = Delta ^ 2 * a := by
    simpa [a, Real.rpow_natCast] using
      (Real.rpow_add hDeltaPos (2 : ℝ) eta)
  have hpowerEtaHalf : Delta ^ (2 + eta / 2) = Delta ^ 2 * g := by
    simpa [g, Real.rpow_natCast] using
      (Real.rpow_add hDeltaPos (2 : ℝ) (eta / 2))
  have hpowOrder : g ≤ a := by
    dsimp [g, a]
    exact Real.rpow_le_rpow_of_exponent_le hDelta (by linarith)
  have hlengthLower : Delta ^ 2 * (a - g) ≤ length := by
    calc
      Delta ^ 2 * (a - g) = Delta ^ (2 + eta) - Delta ^ (2 + eta / 2) := by
        rw [hpowerEta, hpowerEtaHalf]
        ring
      _ ≤ length := by simpa [length] using hfloor.2.1
  have hnumNonneg : 0 ≤ Delta ^ 2 * (a - g) := by
    exact mul_nonneg (sq_nonneg Delta) (sub_nonneg.mpr hpowOrder)
  have hwidthUpperSq : width ^ 2 ≤ (B * Delta) ^ 2 := by
    exact (sq_le_sq₀ (le_of_lt hwidthPos) (mul_nonneg hB.le hDeltaPos.le)).2
      hwidthUpper
  have hwidthSqPos : 0 < width ^ 2 := sq_pos_of_pos hwidthPos
  have hupperSqPos : 0 < (B * Delta) ^ 2 :=
    sq_pos_of_pos (mul_pos hB hDeltaPos)
  have hinv : ((B * Delta) ^ 2)⁻¹ ≤ (width ^ 2)⁻¹ :=
    (inv_le_inv₀ hupperSqPos hwidthSqPos).2 hwidthUpperSq
  have hfrac : (a - g) / B ^ 2 ≤ length / width ^ 2 := by
    have hfrac' :
        Delta ^ 2 * (a - g) / (B * Delta) ^ 2 ≤ length / width ^ 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        Delta ^ 2 * (a - g) * ((B * Delta) ^ 2)⁻¹ ≤
            Delta ^ 2 * (a - g) * (width ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_left hinv hnumNonneg
        _ ≤ length * (width ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_right hlengthLower
                (inv_nonneg.mpr (le_of_lt hwidthSqPos))
    have hcancel :
        Delta ^ 2 * (a - g) / (B * Delta) ^ 2 = (a - g) / B ^ 2 := by
      field_simp [ne_of_gt hDeltaPos, ne_of_gt hB]
    rw [hcancel] at hfrac'
    exact hfrac'
  have hpenalty : d * B ^ 2 * (a - g) ≤
      d * B ^ 4 * (length / width ^ 2) := by
    calc
      d * B ^ 2 * (a - g) = d * B ^ 4 * ((a - g) / B ^ 2) := by
        field_simp [ne_of_gt hB]
      _ ≤ d * B ^ 4 * (length / width ^ 2) :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
  have hdominance : A ≤ R * g := by
    have h := mul_le_mul_of_nonneg_left hgrowth hR.le
    calc
      A = R * (A / R) := by field_simp [ne_of_gt hR]
      _ ≤ R * g := h
  have hdominanceMul : A * g ≤ R * g ^ 2 := by
    calc
      A * g ≤ (R * g) * g :=
        mul_le_mul_of_nonneg_right hdominance (show 0 ≤ g by positivity)
      _ = R * g ^ 2 := by ring
  have hgsq : g ^ 2 = a := by
    dsimp [g, a]
    rw [← Real.rpow_natCast (Delta ^ (eta / 2)) 2,
      ← Real.rpow_mul hDeltaPos.le]
    congr 1
    ring
  have hexponent : width ^ (eta / 2) -
      d * B ^ 4 * (length / width ^ 2) ≤ -d * B * a := by
    dsimp [A, R] at hdominanceMul
    rw [hgsq] at hdominanceMul
    nlinarith [hwidthPow, hpenalty, hdominanceMul]
  simpa [width, length, a, B] using hexponent

lemma drawdownBlockCount_scaledBounds
    {Delta eta : ℝ} {horizon blockLength : ℕ}
    (hDelta : 0 < Delta)
    (hblockLength : 1 ≤ blockLength)
    (hblockLengthLower : Delta ^ (2 + eta / 2) ≤ (blockLength : ℝ))
    (hblockLengthUpper : (blockLength : ℝ) ≤ Delta ^ (2 + eta)) :
    ((horizon : ℝ) / Delta ^ 2) / Delta ^ eta - 1 ≤
        ((horizon / blockLength : ℕ) : ℝ) ∧
      ((horizon / blockLength : ℕ) : ℝ) ≤
        ((horizon : ℝ) / Delta ^ 2) / Real.sqrt (Delta ^ eta) := by
  let q : ℕ := horizon / blockLength
  let qReal : ℝ := (q : ℝ)
  have hblockLengthPos : 0 < (blockLength : ℝ) := by
    exact_mod_cast (show 0 < blockLength by omega)
  have hscaleDenom : Delta ^ (2 + eta) = Delta ^ 2 * Delta ^ eta := by
    simpa [Real.rpow_natCast] using (Real.rpow_add hDelta (2 : ℝ) eta)
  have hscaleDenomHalf : Delta ^ (2 + eta / 2) =
      Delta ^ 2 * Delta ^ (eta / 2) := by
    simpa [Real.rpow_natCast] using (Real.rpow_add hDelta (2 : ℝ) (eta / 2))
  have hsqrt : Real.sqrt (Delta ^ eta) = Delta ^ (eta / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hDelta.le]
    congr 1
    ring
  have hNatDivUpper : q * blockLength ≤ horizon := by
    dsimp [q]
    exact Nat.div_mul_le_self _ _
  have hNatDivLower : horizon < (q + 1) * blockLength := by
    apply (Nat.div_lt_iff_lt_mul hblockLength).mp
    dsimp [q]
    exact Nat.lt_succ_self _
  have hqUpper : qReal ≤ (horizon : ℝ) / Delta ^ (2 + eta / 2) := by
    have hmul : qReal * Delta ^ (2 + eta / 2) ≤ (horizon : ℝ) := by
      calc
        qReal * Delta ^ (2 + eta / 2) ≤ qReal * (blockLength : ℝ) :=
          mul_le_mul_of_nonneg_left hblockLengthLower (by positivity)
        _ ≤ (horizon : ℝ) := by
          change (q : ℝ) * (blockLength : ℝ) ≤ (horizon : ℝ)
          exact_mod_cast hNatDivUpper
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hDelta (2 + eta / 2))).2 hmul
  have hqLower : (horizon : ℝ) / Delta ^ (2 + eta) < qReal + 1 := by
    have hmul : (horizon : ℝ) < (qReal + 1) * Delta ^ (2 + eta) := by
      calc
        (horizon : ℝ) < ((q + 1) * blockLength : ℕ) := by exact_mod_cast hNatDivLower
        _ ≤ (qReal + 1) * Delta ^ (2 + eta) := by
          calc
            ((q + 1) * blockLength : ℕ) =
                ((q + 1 : ℕ) : ℝ) * (blockLength : ℝ) := by norm_num
            _ ≤ ((q + 1 : ℕ) : ℝ) * Delta ^ (2 + eta) :=
              mul_le_mul_of_nonneg_left hblockLengthUpper (by positivity)
            _ = (qReal + 1) * Delta ^ (2 + eta) := by simp [qReal]
    exact (div_lt_iff₀ (Real.rpow_pos_of_pos hDelta (2 + eta))).2 hmul
  have hqLowerScaled :
      ((horizon : ℝ) / Delta ^ 2) / Delta ^ eta - 1 < qReal := by
    have hratio : ((horizon : ℝ) / Delta ^ 2) / Delta ^ eta =
        (horizon : ℝ) / Delta ^ (2 + eta) := by
      rw [div_div, hscaleDenom]
    rw [hratio]
    linarith
  have hqUpperScaled :
      qReal ≤ ((horizon : ℝ) / Delta ^ 2) / Real.sqrt (Delta ^ eta) := by
    have hratio : (horizon : ℝ) / Delta ^ (2 + eta / 2) =
        ((horizon : ℝ) / Delta ^ 2) / Real.sqrt (Delta ^ eta) := by
      rw [div_div, hsqrt, hscaleDenomHalf]
    rw [← hratio]
    exact hqUpper
  constructor
  · exact le_of_lt (by simpa [q, qReal] using hqLowerScaled)
  · simpa [q, qReal] using hqUpperScaled

lemma drawdownJumpCount_add_one_le
    {Delta c eta : ℝ}
    (hDelta : 1 ≤ Delta) (hc : 0 < c)
    (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    ((⌊(Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ)⌋₊ + 1 : ℕ) : ℝ) + 1 ≤
      2 * (1 / c + 2) / eta := by
  have hDeltaPos : 0 < Delta := by linarith
  have hbinLower : eta * Delta ≤ (⌈eta * Delta⌉₊ : ℝ) := by
    exact_mod_cast Nat.le_ceil (eta * Delta)
  have hbinPos : 0 < (⌈eta * Delta⌉₊ : ℝ) :=
    lt_of_lt_of_le (mul_pos heta hDeltaPos) hbinLower
  have hratio : (Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ) ≤
      (1 / c + 1) / eta := by
    have hnum : Delta / c + Delta = (1 / c + 1) * Delta := by ring
    have hfirst :
        (Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ) ≤
          (Delta / c + Delta) / (eta * Delta) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos heta hDeltaPos) hbinLower
    have hsecond : (Delta / c + Delta) / (eta * Delta) =
        (1 / c + 1) / eta := by rw [hnum]; field_simp [ne_of_gt heta, ne_of_gt hDeltaPos]
    exact hfirst.trans_eq hsecond
  have hratioNonneg : 0 ≤ (Delta / c + Delta) /
      (⌈eta * Delta⌉₊ : ℝ) := by positivity
  have hfloor :
      (⌊(Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ)⌋₊ : ℝ) ≤
        (Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ) :=
    Nat.floor_le hratioNonneg
  have hconstant : (1 / c + 1) / eta + 2 ≤ 2 * (1 / c + 2) / eta := by
    have hc' : 0 < 1 / c := by positivity
    field_simp [ne_of_gt hc, ne_of_gt heta]
    nlinarith [hetaLeOne]
  have hcast :
      ((⌊(Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ)⌋₊ + 1 : ℕ) : ℝ) + 1 =
        (⌊(Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ)⌋₊ : ℝ) + 2 := by
    norm_num
    ring
  rw [hcast]
  calc
    (⌊(Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ)⌋₊ : ℝ) + 2 ≤
        (Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ) + 2 := by linarith
    _ ≤ (1 / c + 1) / eta + 2 := by linarith
    _ ≤ 2 * (1 / c + 2) / eta := hconstant

/-- The final entropy and jump-count estimates in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, proof of Lemma 3.3, turn the finite jump-pattern bound into the
desired exponential rate. Here `z = L / Δ^2`, `t = Δ^η`, and `K` bounds the
number of jumps. The one-block rate is assumed in the explicit form
\[
  (w+\Delta)^v-d_0\frac{\ell}{(w+\Delta)^2}
    \le -d(1+2\eta)t.
\] -/
lemma measureReal_noLargeDropEvent_le_exp_of_blockParameters
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance v blockRate eta target t z : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance)
    (hv : 0 < v) (hblockRate : 0 < blockRate)
    (hcritical : blockRate < (Real.pi ^ 2 / 2) * variance)
    (heta : 0 < eta) (ht : 0 < t) (htarget : 0 < target)
    (hz : 0 ≤ z)
    (horizon blockLength : ℕ) (hblockLength : 1 ≤ blockLength)
    (delta threshold binWidth : ℝ) (hbinWidth : 0 < binWidth)
    (honeBlock : (binWidth + delta) ^ v -
        blockRate * ((blockLength : ℝ) / (binWidth + delta) ^ 2) ≤
          -target * (1 + 2 * eta) * t)
    (hqLower : z / t - 1 ≤ ((horizon / blockLength : ℕ) : ℝ))
    (hqUpper : ((horizon / blockLength : ℕ) : ℝ) ≤ z / Real.sqrt t)
    (hmaxJumps :
      ⌊(threshold + delta) / binWidth⌋₊ + 1 ≤ horizon / blockLength)
    (hentropy : Real.log 2 / Real.sqrt t ≤ target * eta)
    (hjump : target * (1 + 2 * eta) * t *
        (((⌊(threshold + delta) / binWidth⌋₊ + 1 : ℕ) : ℝ) + 1) ≤
      target * eta * z) :
    ∃ width₀, 0 < width₀ ∧
      (width₀ ≤ binWidth + delta →
        (iidSequenceLaw ν).real
            (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
          Real.exp (-target * z)) := by
  obtain ⟨width₀, hwidth₀pos, hfinite⟩ :=
    measureReal_noLargeDropEvent_le_jumpPatternCount_mul_pow
      ν hν hsquare hvariance hv hblockRate hcritical
      horizon blockLength hblockLength delta threshold binWidth hbinWidth
  refine ⟨width₀, hwidth₀pos, ?_⟩
  intro hwidth
  have hexponentNonpos :
      (binWidth + delta) ^ v -
        blockRate * ((blockLength : ℝ) / (binWidth + delta) ^ 2) ≤ 0 := by
    calc
      (binWidth + delta) ^ v -
          blockRate * ((blockLength : ℝ) / (binWidth + delta) ^ 2) ≤
          -target * (1 + 2 * eta) * t := honeBlock
      _ ≤ 0 := by
        have hpositive : 0 ≤ target * (1 + 2 * eta) * t := by positivity
        nlinarith
  have hp : Real.exp ((binWidth + delta) ^ v -
      blockRate * ((blockLength : ℝ) / (binWidth + delta) ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr hexponentNonpos
  have hfiniteBound := hfinite hwidth hp
  let q : ℕ := horizon / blockLength
  let K : ℕ := ⌊(threshold + delta) / binWidth⌋₊ + 1
  let p : ℝ := Real.exp ((binWidth + delta) ^ v -
      blockRate * ((blockLength : ℝ) / (binWidth + delta) ^ 2))
  have hqK : K ≤ q := by exact hmaxJumps
  have hsmallBlock : p ≤ Real.exp (-target * (1 + 2 * eta) * t) := by
    exact Real.exp_le_exp.mpr honeBlock
  have hpow : p ^ (q - K) ≤
      Real.exp (-target * (1 + 2 * eta) * t) ^ (q - K) :=
    pow_le_pow_left₀ (Real.exp_nonneg _) hsmallBlock _
  have hfiniteBound' :
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
        (2 : ℝ) ^ q *
          Real.exp (-target * (1 + 2 * eta) * t) ^ (q - K) := by
    calc
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
          (2 : ℝ) ^ q * p ^ (q - K) := by
            simpa only [q, K, p] using hfiniteBound
      _ ≤ (2 : ℝ) ^ q *
          Real.exp (-target * (1 + 2 * eta) * t) ^ (q - K) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
  have hfinal := jumpPatternProbability_le_exp hz ht heta htarget
    (by simpa only [q] using hqLower)
    (by simpa only [q] using hqUpper)
    hqK hentropy (by simpa only [K] using hjump)
  simpa only [q, K] using hfiniteBound'.trans hfinal

lemma exists_drawdownBlockExponent
    {variance endpointPower horizonPower d : ℝ}
    (hvariance : 0 < variance) (hendpoint : 0 < endpointPower)
    (hhorizon : 0 < horizonPower) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ eta : ℝ, 0 < eta ∧ eta < endpointPower ∧ eta < horizonPower ∧
      eta < 1 ∧ d * (1 + 2 * eta) ^ 4 < (Real.pi ^ 2 / 2) * variance := by
  let criticalRatio : ℝ := ((Real.pi ^ 2 / 2) * variance) / d
  have hratio : 1 < criticalRatio := by
    dsimp [criticalRatio]
    exact (one_lt_div hd).2 hcritical
  have hcontinuous : ContinuousAt (fun eta : ℝ => (1 + 2 * eta) ^ 4) 0 := by
    fun_prop
  have hcriticalEventually : ∀ᶠ eta : ℝ in 𝓝 0,
      (1 + 2 * eta) ^ 4 < criticalRatio :=
    hcontinuous.eventually (Iio_mem_nhds (by simpa using hratio))
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hcriticalEventually
  let bound := min radius (min endpointPower (min horizonPower 1))
  let eta := bound / 2
  have hboundPos : 0 < bound := by
    dsimp [bound]
    positivity
  have hetaPos : 0 < eta := by dsimp [eta]; linarith
  have hetaBound : eta < bound := by dsimp [eta]; linarith
  have hboundEndpoint : bound ≤ endpointPower := by
    dsimp [bound]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hboundHorizon : bound ≤ horizonPower := by
    dsimp [bound]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hboundOne : bound ≤ 1 := by
    dsimp [bound]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hetaEndpoint : eta < endpointPower := lt_of_lt_of_le hetaBound hboundEndpoint
  have hetaHorizon : eta < horizonPower := lt_of_lt_of_le hetaBound hboundHorizon
  have hetaOne : eta < 1 := lt_of_lt_of_le hetaBound hboundOne
  have hetaRadius : eta < radius :=
    lt_of_lt_of_le hetaBound (min_le_left _ _)
  have hetaBall : eta ∈ Metric.ball (0 : ℝ) radius := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hetaPos] using hetaRadius
  have hcriticalEta : (1 + 2 * eta) ^ 4 < criticalRatio := hball hetaBall
  refine ⟨eta, hetaPos, hetaEndpoint, hetaHorizon, hetaOne, ?_⟩
  calc
    d * (1 + 2 * eta) ^ 4 < d * criticalRatio :=
      mul_lt_mul_of_pos_left hcriticalEta hd
    _ = (Real.pi ^ 2 / 2) * variance := by
      dsimp [criticalRatio]
      field_simp [ne_of_gt hd]

lemma eventually_drawdownScaleAbsorptions
    {endpointPower horizonPower eta d : ℝ}
    (hhorizon : eta < horizonPower) (heta : 0 < eta) :
    ∀ᶠ Delta : ℝ in atTop,
      2 * (1 + 2 * eta) * (1 / endpointPower + 2) / eta ^ 2 ≤
          Delta ^ (horizonPower - eta) ∧
        Real.log 2 / (d * eta) ≤ Delta ^ (eta / 2) := by
  have hjumpExponent : 0 < horizonPower - eta := by linarith
  have hjump := eventually_real_rpow_ge_const
    (power := horizonPower - eta)
    (bound := 2 * (1 + 2 * eta) * (1 / endpointPower + 2) / eta ^ 2)
    hjumpExponent
  have hentropy := eventually_real_rpow_ge_const
    (power := eta / 2) (bound := Real.log 2 / (d * eta)) (by linarith)
  filter_upwards [hjump, hentropy] with Delta hjump hentropy
  exact ⟨hjump, hentropy⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end
