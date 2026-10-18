/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Rate.Raw
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Explicit logarithmic scales for the selected-population tail estimate

This file constructs the deterministic integer parameters required by
`RawRate`.  It verifies the floor, coverage, and spatial-bin conditions.  The
random-walk rate remains an independent hypothesis of the RawRate theorem.
-/

open Filter
open scoped Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

/-- The logarithmic scale associated to a natural-valued sample-size sequence. -/
noncomputable def logarithmOfSampleSize (N : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.log (N n : ℝ)

/-- The Gaussian small-deviation scale `k ↦ k^(2/5)`. -/
noncomputable def logarithmicSmallDeviationScale (k : ℕ) : ℝ :=
  (k : ℝ) ^ ((2 : ℝ) / 5)

/-- The auxiliary square-root index used to choose an integral block length. -/
noncomputable def logarithmicBlockRoot (N : ℕ → ℕ) (beta b : ℝ) (n : ℕ) : ℕ :=
  ⌊Real.sqrt (beta * b * logarithmOfSampleSize N n)⌋₊

/-- A block length with fifth-power successor, so the `2/5` scale is exact. -/
noncomputable def logarithmicBlockLength (N : ℕ → ℕ) (beta b : ℝ) (n : ℕ) : ℕ :=
  let q := logarithmicBlockRoot N beta b n
  if 1 < q then q ^ 5 - 1 else 1

/-- The drawdown width is asymptotic to `b log N`. -/
noncomputable def logarithmicDrawdown (N : ℕ → ℕ) (beta b : ℝ) (n : ℕ) : ℝ :=
  (logarithmicBlockRoot N beta b n : ℝ) ^ 2 / beta

/-- The finite horizon is asymptotic to `t (log N)^3`. -/
noncomputable def logarithmicHorizon (N : ℕ → ℕ) (t : ℝ) (n : ℕ) : ℕ :=
  ⌊t * logarithmOfSampleSize N n ^ 3⌋₊ + 1

/-- The number of complete blocks in the finite horizon. -/
noncomputable def logarithmicBlockCount (N : ℕ → ℕ) (beta b t : ℝ) (n : ℕ) : ℕ :=
  ⌊(logarithmicHorizon N t n : ℝ) /
      logarithmicBlockLength N beta b n⌋₊

/-- The number of complete blocks fitting in an arbitrary horizon.  This is
the version used for the arbitrary sequence `ℓ_N`, whose only
assumption is its normalized logarithmic-cube limit. -/
noncomputable def logarithmicBlockCountForHorizon (N : ℕ → ℕ) (beta b : ℝ)
    (horizon : ℕ → ℕ) (n : ℕ) : ℕ :=
  ⌊(horizon n : ℝ) / logarithmicBlockLength N beta b n⌋₊

/-- The block-width factor required by the raw range-rate theorem. -/
noncomputable def logarithmicRateBeta (factor eta : ℝ) : ℝ := factor * (1 + eta) / 2

/-- A logarithmic endpoint threshold. -/
noncomputable def logarithmicEndpointThreshold (N : ℕ → ℕ) (zeta : ℝ) (n : ℕ) : ℝ :=
  zeta * logarithmOfSampleSize N n

private lemma tendsto_logarithmOfSampleSize_atTop {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) :
    Tendsto (logarithmOfSampleSize N) atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp hN)

private lemma eventually_logarithmOfSampleSize_pos {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) :
    ∀ᶠ n : ℕ in atTop, 0 < logarithmOfSampleSize N n :=
  (tendsto_logarithmOfSampleSize_atTop hN).eventually_gt_atTop 0

private lemma tendsto_logarithmicBlockRoot_div_sqrtLog
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b : ℝ} (hbeta : 0 < beta) (hb : 0 < b) :
    Tendsto (fun n => (logarithmicBlockRoot N beta b n : ℝ) /
      Real.sqrt (logarithmOfSampleSize N n)) atTop
      (𝓝 (Real.sqrt (beta * b))) := by
  let L := logarithmOfSampleSize N
  let arg : ℕ → ℝ := fun n => Real.sqrt (beta * b * L n)
  have hL : Tendsto L atTop atTop := tendsto_logarithmOfSampleSize_atTop hN
  have harg : Tendsto arg atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    have hmul : Tendsto (fun n => beta * b * L n) atTop atTop :=
      hL.const_mul_atTop (mul_pos hbeta hb)
    exact hmul
  have hfloor : Tendsto (fun n => (Nat.floor (arg n) : ℝ) / arg n)
      atTop (𝓝 1) := tendsto_nat_floor_div_atTop.comp harg
  have hroot : Tendsto (fun n => Real.sqrt (L n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hL
  have hnorm : Tendsto (fun n => arg n / Real.sqrt (L n)) atTop
      (𝓝 (Real.sqrt (beta * b))) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.sqrt (beta * b))
      atTop (𝓝 (Real.sqrt (beta * b)))).congr'
    filter_upwards [hL.eventually_gt_atTop 0] with n hn
    have hsqrt : arg n = Real.sqrt (beta * b) * Real.sqrt (L n) := by
      dsimp [arg]
      rw [show beta * b * L n = (beta * b) * L n by ring,
        Real.sqrt_mul (le_of_lt (mul_pos hbeta hb))]
    rw [hsqrt]
    have hargPos : 0 < arg n :=
      Real.sqrt_pos.2 (mul_pos (mul_pos hbeta hb) hn)
    have hden : Real.sqrt (L n) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
    field_simp [ne_of_gt hargPos, hden]
  have hprod := hfloor.mul hnorm
  have heq : (fun n => (logarithmicBlockRoot N beta b n : ℝ) /
      Real.sqrt (L n)) =ᶠ[atTop]
      fun n => ((Nat.floor (arg n) : ℝ) / arg n) *
        (arg n / Real.sqrt (L n)) := by
    filter_upwards [hL.eventually_gt_atTop 0] with n hn
    have hargPos : 0 < arg n :=
      Real.sqrt_pos.2 (mul_pos (mul_pos hbeta hb) hn)
    have hden : Real.sqrt (L n) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
    change (Nat.floor (arg n) : ℝ) / Real.sqrt (L n) =
      ((Nat.floor (arg n) : ℝ) / arg n) *
        (arg n / Real.sqrt (L n))
    field_simp [hargPos.ne', hden]
  simpa [L, arg] using hprod.congr' heq.symm

private lemma tendsto_logarithmicBlockRoot_atTop
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b : ℝ} (hbeta : 0 < beta) (hb : 0 < b) :
    Tendsto (logarithmicBlockRoot N beta b) atTop atTop := by
  have hratio := tendsto_logarithmicBlockRoot_div_sqrtLog hN hbeta hb
  have hsqrtTop : Tendsto
      (fun n => Real.sqrt (logarithmOfSampleSize N n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_logarithmOfSampleSize_atTop hN)
  have hmul := hsqrtTop.atTop_mul_pos
    (Real.sqrt_pos.2 (mul_pos hbeta hb)) hratio
  have heq : (fun n =>
      Real.sqrt (logarithmOfSampleSize N n) *
        ((logarithmicBlockRoot N beta b n : ℝ) /
          Real.sqrt (logarithmOfSampleSize N n))) =ᶠ[atTop]
      fun n => (logarithmicBlockRoot N beta b n : ℝ) := by
    filter_upwards [eventually_logarithmOfSampleSize_pos hN] with n hn
    have hroot : Real.sqrt (logarithmOfSampleSize N n) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hn)
    field_simp
  have hcast : Tendsto (fun n => (logarithmicBlockRoot N beta b n : ℝ))
      atTop atTop := hmul.congr' heq
  exact (tendsto_natCast_atTop_iff).mp hcast

private lemma eventually_logarithmicBlockLength_succ
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b : ℝ} (hbeta : 0 < beta) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop,
      logarithmicBlockLength N beta b n + 1 =
        logarithmicBlockRoot N beta b n ^ 5 := by
  have hrootTop := tendsto_logarithmicBlockRoot_atTop hN hbeta hb
  filter_upwards [hrootTop.eventually (eventually_gt_atTop 1)] with n hn
  have hq : 1 ≤ logarithmicBlockRoot N beta b n := by omega
  have hqpow : 1 ≤ logarithmicBlockRoot N beta b n ^ 5 :=
    Nat.one_le_pow 5 _ hq
  simp [logarithmicBlockLength, hn, Nat.sub_add_cancel hqpow]

/-- The fifth-root construction makes the Gaussian exponent `2/5` exact. -/
private lemma rpow_fifthPower_two_fifths (q : ℕ) :
    ((q : ℝ) ^ 5) ^ ((2 : ℝ) / 5) = (q : ℝ) ^ 2 := by
  rw [← Real.rpow_natCast (q : ℝ) 5,
    ← Real.rpow_mul (by positivity : 0 ≤ (q : ℝ))]
  norm_num

/-- The selected scale is a genuine small-deviation scale relative to `sqrt`. -/
theorem logarithmicSmallDeviationScale_isSmallDeviationScale :
    Asymptotics.IsSmallDeviationScale logarithmicSmallDeviationScale
      (fun k => Real.sqrt (k : ℝ)) := by
  refine ⟨?_, ?_⟩
  · exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      tendsto_natCast_atTop_atTop
  · have hpow : Tendsto (fun k : ℕ => (k : ℝ) ^ (-(1 : ℝ) / 10))
        atTop (𝓝 0) := by
      convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
        tendsto_natCast_atTop_atTop using 1
      ext k
      norm_num
    have heq : (fun k : ℕ => logarithmicSmallDeviationScale k /
        Real.sqrt (k : ℝ)) =ᶠ[atTop]
        fun k => (k : ℝ) ^ (-(1 : ℝ) / 10) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
      have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
      dsimp [logarithmicSmallDeviationScale]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hkpos]
      norm_num
    exact hpow.congr' heq.symm

private lemma tendsto_logarithmicBlockRoot_sq_div_log
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b : ℝ} (hbeta : 0 < beta) (hb : 0 < b) :
    Tendsto (fun n => (logarithmicBlockRoot N beta b n : ℝ) ^ 2 /
      logarithmOfSampleSize N n) atTop (𝓝 (beta * b)) := by
  let L := logarithmOfSampleSize N
  let root : ℕ → ℝ := fun n => Real.sqrt (L n)
  have hL : Tendsto L atTop atTop := tendsto_logarithmOfSampleSize_atTop hN
  have hq := tendsto_logarithmicBlockRoot_div_sqrtLog hN hbeta hb
  have hpow := hq.pow 2
  have heq : (fun n => (logarithmicBlockRoot N beta b n : ℝ) ^ 2 / L n) =ᶠ[atTop]
      fun n => ((logarithmicBlockRoot N beta b n : ℝ) / root n) ^ 2 := by
    filter_upwards [hL.eventually_gt_atTop 0] with n hn
    have hsqrt : root n ^ 2 = L n := Real.sq_sqrt (le_of_lt hn)
    have hrootne : root n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
    change (logarithmicBlockRoot N beta b n : ℝ) ^ 2 / L n =
      ((logarithmicBlockRoot N beta b n : ℝ) / root n) ^ 2
    rw [← hsqrt]
    field_simp [hrootne]
  have hlimit : (Real.sqrt (beta * b)) ^ 2 = beta * b :=
    Real.sq_sqrt (le_of_lt (mul_pos hbeta hb))
  simpa [L, hlimit] using hpow.congr' heq.symm

private lemma tendsto_logarithmicDrawdown_div_log
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b : ℝ} (hbeta : 0 < beta) (hb : 0 < b) :
    Tendsto (fun n => logarithmicDrawdown N beta b n /
      logarithmOfSampleSize N n) atTop (𝓝 b) := by
  have hq := tendsto_logarithmicBlockRoot_sq_div_log hN hbeta hb
  have hratio : Tendsto (fun n =>
      ((logarithmicBlockRoot N beta b n : ℝ) ^ 2 /
        logarithmOfSampleSize N n) / beta) atTop (𝓝 b) := by
    convert hq.div_const beta using 1
    field_simp [ne_of_gt hbeta]
  have heq : (fun n => logarithmicDrawdown N beta b n /
      logarithmOfSampleSize N n) =ᶠ[atTop]
      fun n => ((logarithmicBlockRoot N beta b n : ℝ) ^ 2 /
        logarithmOfSampleSize N n) / beta := by
    filter_upwards [] with n
    dsimp [logarithmicDrawdown]
    ring
  exact hratio.congr' heq.symm

/-- Public asymptotic ratio for the logarithmic drawdown scale.  This is the
sequence-level input needed to turn a raw endpoint estimate into its
polynomial-in-`N` form. -/
theorem logarithmicDrawdown_div_log_tendsto
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b : ℝ} (hbeta : 0 < beta) (hb : 0 < b) :
    Tendsto (fun n => logarithmicDrawdown N beta b n /
      logarithmOfSampleSize N n) atTop (𝓝 b) :=
  tendsto_logarithmicDrawdown_div_log hN hbeta hb

private lemma tendsto_logarithmicHorizon_div_log_cube
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => (logarithmicHorizon N t n : ℝ) /
      logarithmOfSampleSize N n ^ 3) atTop (𝓝 t) := by
  let L := logarithmOfSampleSize N
  let arg : ℕ → ℝ := fun n => t * L n ^ 3
  have hL : Tendsto L atTop atTop := tendsto_logarithmOfSampleSize_atTop hN
  have harg : Tendsto arg atTop atTop := by
    have hcube : Tendsto (fun n => L n ^ 3) atTop atTop := by
      exact tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0) |>.comp hL
    exact hcube.const_mul_atTop ht
  have hfloor : Tendsto (fun n => (Nat.floor (arg n) : ℝ) / arg n)
      atTop (𝓝 1) := tendsto_nat_floor_div_atTop.comp harg
  have hargNorm : Tendsto (fun n => arg n / L n ^ 3) atTop (𝓝 t) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t)).congr'
    filter_upwards [hL.eventually_gt_atTop 0] with n hn
    dsimp [arg]
    field_simp
  have hbase := hfloor.mul hargNorm
  have hLinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) := hL.inv_tendsto_atTop
  have hoffset : Tendsto (fun n => (L n)⁻¹ ^ 3) atTop (𝓝 0) := by
    simpa using hLinv.pow 3
  have heq : (fun n => (logarithmicHorizon N t n : ℝ) / L n ^ 3) =ᶠ[atTop]
      fun n => ((Nat.floor (arg n) : ℝ) / arg n) *
        (arg n / L n ^ 3) + (L n)⁻¹ ^ 3 := by
    filter_upwards [hL.eventually_gt_atTop 0] with n hn
    have hargPos : 0 < arg n := mul_pos ht (pow_pos hn 3)
    have hargNe : arg n ≠ 0 := ne_of_gt hargPos
    have hLne : L n ≠ 0 := ne_of_gt hn
    change ((Nat.floor (arg n) + 1 : ℕ) : ℝ) / L n ^ 3 = _
    push_cast
    field_simp [hargNe, hLne]
  simpa [L] using (hbase.add hoffset).congr' heq.symm

/-- Public scale limit for the horizon `floor(t log^3 N) + 1`. -/
theorem logarithmicHorizon_div_logCube_tendsto
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => (logarithmicHorizon N t n : ℝ) /
      logarithmOfSampleSize N n ^ 3) atTop (𝓝 t) :=
  tendsto_logarithmicHorizon_div_log_cube hN ht

private lemma tendsto_logarithmicLengthSucc_div_log_two_sqrt
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b : ℝ} (hbeta : 0 < beta) (hb : 0 < b) :
    Tendsto (fun n => ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
      (logarithmOfSampleSize N n ^ 2 *
        Real.sqrt (logarithmOfSampleSize N n))) atTop
      (𝓝 (Real.sqrt (beta * b) ^ 5)) := by
  let L := logarithmOfSampleSize N
  let root : ℕ → ℝ := fun n => Real.sqrt (L n)
  have hL : Tendsto L atTop atTop := tendsto_logarithmOfSampleSize_atTop hN
  have hq := tendsto_logarithmicBlockRoot_div_sqrtLog hN hbeta hb
  have hpow := hq.pow 5
  have hlen := eventually_logarithmicBlockLength_succ hN hbeta hb
  have heq : (fun n => ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
      (L n ^ 2 * root n)) =ᶠ[atTop]
      fun n => ((logarithmicBlockRoot N beta b n : ℝ) / root n) ^ 5 := by
    filter_upwards [hL.eventually_gt_atTop 0, hlen] with n hn hlen
    have hsqrt : root n ^ 2 = L n := Real.sq_sqrt (le_of_lt hn)
    have hrootne : root n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
    have hden : L n ^ 2 * root n = root n ^ 5 := by
      rw [← hsqrt]
      ring
    change ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
      (L n ^ 2 * root n) = _
    rw [hlen]
    push_cast
    rw [hden]
    field_simp [hrootne]
  simpa [L, root] using hpow.congr' heq.symm

private lemma logarithmicBlockLength_pos
    (N : ℕ → ℕ) (beta b : ℝ) (n : ℕ) :
    0 < logarithmicBlockLength N beta b n := by
  dsimp [logarithmicBlockLength]
  split_ifs with h
  · have hq : 1 < logarithmicBlockRoot N beta b n := h
    have hpow : 1 < logarithmicBlockRoot N beta b n ^ 5 :=
      Nat.one_lt_pow (by norm_num) hq
    omega
  · omega

private lemma tendsto_logarithmicBlockLength_succ_atTop
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b : ℝ} (hbeta : 0 < beta) (hb : 0 < b) :
    Tendsto (fun n => logarithmicBlockLength N beta b n + 1) atTop atTop := by
  have hq := tendsto_logarithmicBlockRoot_atTop hN hbeta hb
  have hqCast : Tendsto (fun n => (logarithmicBlockRoot N beta b n : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hq
  have hpow := (tendsto_pow_atTop (by norm_num : (5 : ℕ) ≠ 0)).comp hqCast
  have hlen := eventually_logarithmicBlockLength_succ hN hbeta hb
  have heq : (fun n => ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ)) =ᶠ[atTop]
      fun n => (logarithmicBlockRoot N beta b n : ℝ) ^ 5 := by
    filter_upwards [hlen] with n hn
    exact_mod_cast hn
  have hsucc : Tendsto (fun n => ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ))
      atTop atTop := hpow.congr' heq.symm
  exact (tendsto_natCast_atTop_iff).mp hsucc

private lemma tendsto_logarithmicBlockLength_atTop
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b : ℝ} (hbeta : 0 < beta) (hb : 0 < b) :
    Tendsto (logarithmicBlockLength N beta b) atTop atTop := by
  have hsucc := tendsto_logarithmicBlockLength_succ_atTop hN hbeta hb
  apply Filter.tendsto_atTop.2
  intro k
  filter_upwards [hsucc.eventually_gt_atTop (k + 1)] with n hn
  omega

private lemma tendsto_logarithmicBlockLength_div_log_two_sqrt
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b : ℝ} (hbeta : 0 < beta) (hb : 0 < b) :
    Tendsto (fun n => (logarithmicBlockLength N beta b n : ℝ) /
      (logarithmOfSampleSize N n ^ 2 *
        Real.sqrt (logarithmOfSampleSize N n))) atTop
      (𝓝 (Real.sqrt (beta * b) ^ 5)) := by
  let L := logarithmOfSampleSize N
  let root : ℕ → ℝ := fun n => Real.sqrt (L n)
  have hplus := tendsto_logarithmicLengthSucc_div_log_two_sqrt hN hbeta hb
  have hlenTop := tendsto_logarithmicBlockLength_succ_atTop hN hbeta hb
  have hlenRealTop : Tendsto (fun n => ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hlenTop
  have hinv : Tendsto (fun n => (((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ))⁻¹)
      atTop (𝓝 0) := hlenRealTop.inv_tendsto_atTop
  have hfrac : Tendsto (fun n => (logarithmicBlockLength N beta b n : ℝ) /
      ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hinv
    have heq : (fun n => (logarithmicBlockLength N beta b n : ℝ) /
        ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ)) =ᶠ[atTop]
        fun n => 1 - (((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ))⁻¹ := by
      filter_upwards [] with n
      have hpos : (0 : ℝ) < ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) := by
        positivity
      field_simp
      push_cast
      ring
    simpa using h.congr' heq.symm
  have hmul := hplus.mul hfrac
  have heq : (fun n => (logarithmicBlockLength N beta b n : ℝ) /
      (L n ^ 2 * root n)) =ᶠ[atTop]
      fun n => (((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
          (L n ^ 2 * root n)) *
        ((logarithmicBlockLength N beta b n : ℝ) /
          ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ)) := by
    filter_upwards [tendsto_logarithmOfSampleSize_atTop hN |>.eventually_gt_atTop 0] with n hn
    have hlenPos : (0 : ℝ) < (logarithmicBlockLength N beta b n : ℝ) := by
      exact_mod_cast logarithmicBlockLength_pos N beta b n
    field_simp
  simpa [L, root] using hmul.congr' heq.symm

private lemma tendsto_logarithmicBlockCost_atTop
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b : ℝ} (hbeta : 0 < beta) (hb : 0 < b) :
    Tendsto (fun n => ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
      logarithmicDrawdown N beta b n ^ 2) atTop atTop := by
  have hqTop := tendsto_logarithmicBlockRoot_atTop hN hbeta hb
  have hqCast : Tendsto (fun n => (logarithmicBlockRoot N beta b n : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hqTop
  have htarget : Tendsto (fun n => beta ^ 2 *
      (logarithmicBlockRoot N beta b n : ℝ)) atTop atTop := by
    simpa [mul_comm] using hqCast.const_mul_atTop (sq_pos_of_pos hbeta)
  have hlen := eventually_logarithmicBlockLength_succ hN hbeta hb
  have heq : (fun n => ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
      logarithmicDrawdown N beta b n ^ 2) =ᶠ[atTop]
      fun n => beta ^ 2 * (logarithmicBlockRoot N beta b n : ℝ) := by
    filter_upwards [hlen, hqTop.eventually (eventually_gt_atTop 1)] with n hn hq
    have hqne : (logarithmicBlockRoot N beta b n : ℝ) ≠ 0 := by
      have hqPos : (0 : ℝ) < (logarithmicBlockRoot N beta b n : ℝ) := by
        exact_mod_cast (by omega : 0 < logarithmicBlockRoot N beta b n)
      exact ne_of_gt hqPos
    change ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
      ((logarithmicBlockRoot N beta b n : ℝ) ^ 2 / beta) ^ 2 = _
    rw [hn]
    push_cast
    field_simp [hbeta.ne', hqne]
  exact htarget.congr' heq.symm

private lemma eventually_logarithmicDrawdown_pos
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b : ℝ} (hbeta : 0 < beta) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, 0 < logarithmicDrawdown N beta b n := by
  have hratio := tendsto_logarithmicDrawdown_div_log hN hbeta hb
  have hL := tendsto_logarithmOfSampleSize_atTop hN
  filter_upwards [hratio.eventually (Ioi_mem_nhds hb), hL.eventually_gt_atTop 0]
      with n hr hlog
  have hprod : 0 < (logarithmicDrawdown N beta b n /
      logarithmOfSampleSize N n) * logarithmOfSampleSize N n := mul_pos hr hlog
  have heq : (logarithmicDrawdown N beta b n /
      logarithmOfSampleSize N n) * logarithmOfSampleSize N n =
      logarithmicDrawdown N beta b n := by
    field_simp [ne_of_gt hlog]
  rw [heq] at hprod
  exact hprod

private lemma tendsto_logarithmicTotalCost_atTop
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b t : ℝ} (hbeta : 0 < beta) (hb : 0 < b) (ht : 0 < t) :
    Tendsto (fun n => (logarithmicHorizon N t n : ℝ) /
      logarithmicDrawdown N beta b n ^ 2) atTop atTop := by
  let L := logarithmOfSampleSize N
  have hL : Tendsto L atTop atTop := tendsto_logarithmOfSampleSize_atTop hN
  have hH := tendsto_logarithmicHorizon_div_log_cube hN ht
  have hB := tendsto_logarithmicDrawdown_div_log hN hbeta hb
  have hbase : Tendsto (fun n => (logarithmicHorizon N t n : ℝ) / L n ^ 3 /
      (logarithmicDrawdown N beta b n / L n) ^ 2) atTop
      (𝓝 (t / b ^ 2)) := by
    have hden := hB.pow 2
    have hdiv := hH.div hden (ne_of_gt (sq_pos_of_pos hb))
    change Tendsto
      ((fun n => (logarithmicHorizon N t n : ℝ) / L n ^ 3) /
        (fun n => (logarithmicDrawdown N beta b n / L n) ^ 2))
      atTop (𝓝 (t / b ^ 2))
    exact hdiv
  have hscaled := hL.atTop_mul_pos (div_pos ht (sq_pos_of_pos hb)) hbase
  have hdeltaPos := eventually_logarithmicDrawdown_pos hN hbeta hb
  have heq : (fun n => (logarithmicHorizon N t n : ℝ) /
      logarithmicDrawdown N beta b n ^ 2) =ᶠ[atTop]
      fun n => L n * ((logarithmicHorizon N t n : ℝ) / L n ^ 3 /
        (logarithmicDrawdown N beta b n / L n) ^ 2) := by
    filter_upwards [hL.eventually_gt_atTop 0, hdeltaPos] with n hn hδ
    have hLne : L n ≠ 0 := ne_of_gt hn
    have hδne : logarithmicDrawdown N beta b n ≠ 0 := ne_of_gt hδ
    field_simp [hLne, hδne]
  exact hscaled.congr' heq.symm

private lemma tendsto_logarithmicHorizon_div_length_atTop
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b t : ℝ} (hbeta : 0 < beta) (hb : 0 < b) (ht : 0 < t) :
    Tendsto (fun n => (logarithmicHorizon N t n : ℝ) /
      (logarithmicBlockLength N beta b n : ℝ)) atTop atTop := by
  let L := logarithmOfSampleSize N
  let root : ℕ → ℝ := fun n => Real.sqrt (L n)
  let gamma : ℝ := Real.sqrt (beta * b) ^ 5
  have hgammaPos : 0 < gamma :=
    pow_pos (Real.sqrt_pos.2 (mul_pos hbeta hb)) 5
  have hL : Tendsto L atTop atTop := tendsto_logarithmOfSampleSize_atTop hN
  have hroot : Tendsto root atTop atTop := Real.tendsto_sqrt_atTop.comp hL
  have hH := tendsto_logarithmicHorizon_div_log_cube hN ht
  have hlen := tendsto_logarithmicBlockLength_div_log_two_sqrt hN hbeta hb
  have hratio : Tendsto
      (fun n => ((logarithmicHorizon N t n : ℝ) / L n ^ 3) /
        ((logarithmicBlockLength N beta b n : ℝ) /
          (L n ^ 2 * root n))) atTop (𝓝 (t / gamma)) := by
    have hdiv := hH.div hlen (ne_of_gt hgammaPos)
    change Tendsto
      ((fun n => (logarithmicHorizon N t n : ℝ) /
          logarithmOfSampleSize N n ^ 3) /
        (fun n => (logarithmicBlockLength N beta b n : ℝ) /
          (logarithmOfSampleSize N n ^ 2 *
            Real.sqrt (logarithmOfSampleSize N n))))
      atTop (𝓝 (t / gamma))
    exact hdiv
  have hscaled : Tendsto
      (fun n => root n * (((logarithmicHorizon N t n : ℝ) / L n ^ 3) /
        ((logarithmicBlockLength N beta b n : ℝ) /
          (L n ^ 2 * root n)))) atTop atTop :=
    hroot.atTop_mul_pos (div_pos ht hgammaPos) hratio
  have hlenPos : ∀ᶠ n : ℕ in atTop, 0 < (logarithmicBlockLength N beta b n : ℝ) := by
    filter_upwards [] with n
    exact_mod_cast logarithmicBlockLength_pos N beta b n
  have heq : (fun n => root n * (((logarithmicHorizon N t n : ℝ) / L n ^ 3) /
      ((logarithmicBlockLength N beta b n : ℝ) /
        (L n ^ 2 * root n)))) =ᶠ[atTop]
      fun n => (logarithmicHorizon N t n : ℝ) /
        (logarithmicBlockLength N beta b n : ℝ) := by
    filter_upwards [hL.eventually_gt_atTop 0, hlenPos] with n hn hlen
    have hrootSq : root n ^ 2 = L n := Real.sq_sqrt (le_of_lt hn)
    have hrootNe : root n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
    have hLne : L n ≠ 0 := ne_of_gt hn
    have hlenNe : (logarithmicBlockLength N beta b n : ℝ) ≠ 0 := ne_of_gt hlen
    field_simp [hrootNe, hLne, hlenNe]
    rw [hrootSq]
    ring
  simpa [L, root, gamma] using hscaled.congr' heq

private lemma logarithmicBlockCount_complete
    (N : ℕ → ℕ) (beta b t : ℝ) (n : ℕ) :
    logarithmicBlockCount N beta b t n * logarithmicBlockLength N beta b n ≤
      logarithmicHorizon N t n := by
  let len := logarithmicBlockLength N beta b n
  let horizon := logarithmicHorizon N t n
  have hlenPos : 0 < len := logarithmicBlockLength_pos N beta b n
  have hfloor :
      ((Nat.floor ((horizon : ℝ) / len) : ℕ) : ℝ) ≤ (horizon : ℝ) / len :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hmul := mul_le_mul_of_nonneg_right hfloor (Nat.cast_nonneg len : (0 : ℝ) ≤ len)
  have hcast : (Nat.floor ((horizon : ℝ) / len) : ℝ) * len ≤ horizon := by
    have hlenNe : (len : ℝ) ≠ 0 := by exact_mod_cast hlenPos.ne'
    have h := hmul
    field_simp [hlenNe] at h
    nlinarith [h]
  exact_mod_cast hcast

private lemma tendsto_logarithmicBlockCount_atTop
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b t : ℝ} (hbeta : 0 < beta) (hb : 0 < b) (ht : 0 < t) :
    Tendsto (logarithmicBlockCount N beta b t) atTop atTop := by
  have hquot := tendsto_logarithmicHorizon_div_length_atTop hN hbeta hb ht
  change Tendsto
    (fun n => Nat.floor ((logarithmicHorizon N t n : ℝ) /
      (logarithmicBlockLength N beta b n : ℝ))) atTop atTop
  exact tendsto_nat_floor_atTop.comp hquot

private lemma tendsto_logarithmicBlockCount_div_quotient
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b t : ℝ} (hbeta : 0 < beta) (hb : 0 < b) (ht : 0 < t) :
    Tendsto (fun n => (logarithmicBlockCount N beta b t n : ℝ) /
      ((logarithmicHorizon N t n : ℝ) /
        (logarithmicBlockLength N beta b n : ℝ))) atTop (𝓝 1) := by
  have hquot := tendsto_logarithmicHorizon_div_length_atTop hN hbeta hb ht
  change Tendsto
    (fun n => (Nat.floor ((logarithmicHorizon N t n : ℝ) /
      (logarithmicBlockLength N beta b n : ℝ)) : ℝ) /
        ((logarithmicHorizon N t n : ℝ) /
          (logarithmicBlockLength N beta b n : ℝ))) atTop (𝓝 1)
  exact tendsto_nat_floor_div_atTop.comp hquot

private lemma tendsto_logarithmicLengthSucc_div_length
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b : ℝ} (hbeta : 0 < beta) (hb : 0 < b) :
    Tendsto (fun n => ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
      (logarithmicBlockLength N beta b n : ℝ)) atTop (𝓝 1) := by
  have hlen := tendsto_logarithmicBlockLength_atTop hN hbeta hb
  have hlenReal : Tendsto
      (fun n => (logarithmicBlockLength N beta b n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hlen
  have hinv : Tendsto (fun n => (logarithmicBlockLength N beta b n : ℝ)⁻¹)
      atTop (𝓝 0) := hlenReal.inv_tendsto_atTop
  have hlimit := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (𝓝 1)).add hinv
  have heq : (fun n => ((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
      (logarithmicBlockLength N beta b n : ℝ)) =ᶠ[atTop]
      fun n => 1 + (logarithmicBlockLength N beta b n : ℝ)⁻¹ := by
    filter_upwards [hlen.eventually (eventually_gt_atTop 0)] with n hn
    have hlenPos : (0 : ℝ) < (logarithmicBlockLength N beta b n : ℝ) := by
      exact_mod_cast hn
    field_simp [ne_of_gt hlenPos]
    push_cast
    ring
  simpa using hlimit.congr' heq.symm

private lemma tendsto_logarithmicCoverage
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b t : ℝ} (hbeta : 0 < beta) (hb : 0 < b) (ht : 0 < t) :
    Tendsto (fun n => (logarithmicBlockCount N beta b t n : ℝ) *
      (((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
        logarithmicDrawdown N beta b n ^ 2) /
      ((logarithmicHorizon N t n : ℝ) /
        logarithmicDrawdown N beta b n ^ 2)) atTop (𝓝 1) := by
  have hblocks := tendsto_logarithmicBlockCount_div_quotient hN hbeta hb ht
  have hlength := tendsto_logarithmicLengthSucc_div_length hN hbeta hb
  have hprod := hblocks.mul hlength
  have hdeltaPos := eventually_logarithmicDrawdown_pos hN hbeta hb
  have heq : (fun n => (logarithmicBlockCount N beta b t n : ℝ) *
      (((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
        logarithmicDrawdown N beta b n ^ 2) /
      ((logarithmicHorizon N t n : ℝ) /
        logarithmicDrawdown N beta b n ^ 2)) =ᶠ[atTop]
      fun n => ((logarithmicBlockCount N beta b t n : ℝ) /
          ((logarithmicHorizon N t n : ℝ) /
            (logarithmicBlockLength N beta b n : ℝ))) *
        (((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
          (logarithmicBlockLength N beta b n : ℝ)) := by
    filter_upwards [hdeltaPos] with n hδ
    have hδne : logarithmicDrawdown N beta b n ≠ 0 := ne_of_gt hδ
    have hlenPos : (0 : ℝ) < (logarithmicBlockLength N beta b n : ℝ) := by
      exact_mod_cast logarithmicBlockLength_pos N beta b n
    have hlenNe : (logarithmicBlockLength N beta b n : ℝ) ≠ 0 := ne_of_gt hlenPos
    have hHpos : (0 : ℝ) < (logarithmicHorizon N t n : ℝ) := by
      dsimp [logarithmicHorizon]
      positivity
    field_simp [hδne, hlenNe, ne_of_gt hHpos]
  simpa using hprod.congr' heq.symm

private lemma eventually_natFloor_eq_of_tendsto_of_not_nat
    {x : ℕ → ℝ} {c : ℝ}
    (hx : Tendsto x atTop (𝓝 c))
    (hc : ¬ ∃ k : ℕ, c = (k : ℝ)) :
    ∀ᶠ n : ℕ in atTop, Nat.floor (x n) = Nat.floor c := by
  by_cases hcupper : c < 1
  · have hev := hx.eventually (Iio_mem_nhds hcupper)
    filter_upwards [hev] with n hn
    rw [Nat.floor_eq_zero.mpr hn]
    simp [Nat.floor_eq_zero.mpr hcupper]
  · have hcnonneg : 0 ≤ c := by linarith
    have hclower : (Nat.floor c : ℝ) < c := by
      have hle := Nat.floor_le hcnonneg
      by_contra hnot
      have heq : (Nat.floor c : ℝ) = c := le_antisymm hle (le_of_not_gt hnot)
      exact hc ⟨Nat.floor c, heq.symm⟩
    have hcupper : c < (Nat.floor c : ℝ) + 1 := Nat.lt_floor_add_one c
    have hev := hx.eventually (Ioo_mem_nhds hclower hcupper)
    filter_upwards [hev] with n hn
    apply (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg _) hn.1.le)).2
    exact ⟨hn.1.le, hn.2⟩

private lemma tendsto_logarithmicThresholdRatio
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b eta zeta : ℝ} (hbeta : 0 < beta) (hb : 0 < b) (heta : 0 < eta) :
    Tendsto (fun n =>
      (logarithmicEndpointThreshold N zeta n +
        logarithmicDrawdown N beta b n) /
        (eta * logarithmicDrawdown N beta b n)) atTop
      (𝓝 ((zeta / b + 1) / eta)) := by
  let L := logarithmOfSampleSize N
  have hL : Tendsto L atTop atTop := tendsto_logarithmOfSampleSize_atTop hN
  have hdelta := tendsto_logarithmicDrawdown_div_log hN hbeta hb
  have hnum : Tendsto (fun n => zeta + logarithmicDrawdown N beta b n / L n)
      atTop (𝓝 (zeta + b)) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => zeta) atTop (𝓝 zeta)).add hdelta
  have hden : Tendsto (fun n => eta *
      (logarithmicDrawdown N beta b n / L n)) atTop (𝓝 (eta * b)) :=
    hdelta.const_mul eta
  have hquot : Tendsto (fun n => (zeta + logarithmicDrawdown N beta b n / L n) /
      (eta * (logarithmicDrawdown N beta b n / L n))) atTop
      (𝓝 ((zeta + b) / (eta * b))) :=
    hnum.div hden (ne_of_gt (mul_pos heta hb))
  have hlimit : (zeta + b) / (eta * b) = (zeta / b + 1) / eta := by
    field_simp [ne_of_gt hb, ne_of_gt heta]
  have hdeltaPos := eventually_logarithmicDrawdown_pos hN hbeta hb
  have heq : (fun n => (logarithmicEndpointThreshold N zeta n +
      logarithmicDrawdown N beta b n) /
      (eta * logarithmicDrawdown N beta b n)) =ᶠ[atTop]
      fun n => (zeta + logarithmicDrawdown N beta b n / L n) /
        (eta * (logarithmicDrawdown N beta b n / L n)) := by
    filter_upwards [hL.eventually_gt_atTop 0, hdeltaPos] with n hLpos hδ
    have hLne : L n ≠ 0 := ne_of_gt hLpos
    have hδne : logarithmicDrawdown N beta b n ≠ 0 := ne_of_gt hδ
    change (zeta * L n + logarithmicDrawdown N beta b n) /
        (eta * logarithmicDrawdown N beta b n) = _
    field_simp [hLne, hδne]
  rw [hlimit] at hquot
  exact hquot.congr' heq.symm

private lemma eventually_logarithmicBlockScale_aligned
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {factor eta b : ℝ} (hfactor : 1 < factor) (heta : 0 < eta) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop,
      logarithmicSmallDeviationScale (logarithmicBlockLength N
        (logarithmicRateBeta factor eta) b n + 1) =
        logarithmicRateBeta factor eta *
          logarithmicDrawdown N (logarithmicRateBeta factor eta) b n := by
  let beta := logarithmicRateBeta factor eta
  have hbeta : 0 < beta := by
    dsimp [beta, logarithmicRateBeta]
    positivity
  have hlen := eventually_logarithmicBlockLength_succ hN hbeta hb
  have hbeta' : 0 < logarithmicRateBeta factor eta := hbeta
  filter_upwards [hlen] with n hn
  dsimp [logarithmicSmallDeviationScale, logarithmicDrawdown, beta]
  rw [hn]
  push_cast
  rw [rpow_fifthPower_two_fifths]
  field_simp [ne_of_gt hbeta']
  simp [beta]

private lemma eventually_logarithmicThreshold_floor
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {factor eta b zeta : ℝ}
    (hfactor : 1 < factor) (heta : 0 < eta) (hb : 0 < b)
    (hbin : (zeta / b + 1) / eta < 1 ∨
      ¬ ∃ k : ℕ, (zeta / b + 1) / eta = (k : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      Nat.floor ((logarithmicEndpointThreshold N zeta n +
        logarithmicDrawdown N (logarithmicRateBeta factor eta) b n) /
        (eta * logarithmicDrawdown N (logarithmicRateBeta factor eta) b n)) =
          Nat.floor ((zeta / b + 1) / eta) := by
  let beta := logarithmicRateBeta factor eta
  have hbeta : 0 < beta := by
    dsimp [beta, logarithmicRateBeta]
    positivity
  rcases hbin with hbelow | hnoninteger
  · have hratio := tendsto_logarithmicThresholdRatio
      (N := N) (zeta := zeta) hN hbeta hb heta
    have hev := hratio.eventually (Iio_mem_nhds hbelow)
    filter_upwards [hev] with n hn
    rw [Nat.floor_eq_zero.mpr hn, Nat.floor_eq_zero.mpr hbelow]
  · exact eventually_natFloor_eq_of_tendsto_of_not_nat
      (tendsto_logarithmicThresholdRatio
        (N := N) (zeta := zeta) hN hbeta hb heta) hnoninteger

/-- Concrete logarithmic scales satisfying every deterministic sequence
condition of the raw drawdown endpoint estimate. The random-walk range-rate
inequality remains a separate analytic hypothesis. -/
theorem logarithmicRawRateParameters
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {factor eta b t zeta : ℝ}
    (hfactor : 1 < factor) (heta : 0 < eta) (hb : 0 < b) (ht : 0 < t)
    (hbin : (zeta / b + 1) / eta < 1 ∨
      ¬ ∃ k : ℕ, (zeta / b + 1) / eta = (k : ℝ)) :
    ∃ K : ℕ,
      K = ⌊(zeta / b + 1) / eta⌋₊ ∧
      Asymptotics.IsSmallDeviationScale logarithmicSmallDeviationScale
        (fun k => Real.sqrt (k : ℝ)) ∧
      Tendsto (fun n => logarithmicBlockLength N
        (logarithmicRateBeta factor eta) b n + 1) atTop atTop ∧
      Tendsto (logarithmicBlockCount N
        (logarithmicRateBeta factor eta) b t) atTop atTop ∧
      Tendsto (fun n =>
        ((logarithmicBlockLength N (logarithmicRateBeta factor eta) b n + 1 : ℕ) : ℝ) /
          logarithmicDrawdown N (logarithmicRateBeta factor eta) b n ^ 2)
        atTop atTop ∧
      Tendsto (fun n => (logarithmicHorizon N t n : ℝ) /
        logarithmicDrawdown N (logarithmicRateBeta factor eta) b n ^ 2)
        atTop atTop ∧
      Tendsto (fun n => (logarithmicBlockCount N
          (logarithmicRateBeta factor eta) b t n : ℝ) *
        (((logarithmicBlockLength N (logarithmicRateBeta factor eta) b n + 1 : ℕ) : ℝ) /
          logarithmicDrawdown N (logarithmicRateBeta factor eta) b n ^ 2) /
        ((logarithmicHorizon N t n : ℝ) /
          logarithmicDrawdown N (logarithmicRateBeta factor eta) b n ^ 2))
        atTop (𝓝 1) ∧
      (∀ n, logarithmicBlockCount N
          (logarithmicRateBeta factor eta) b t n *
          logarithmicBlockLength N (logarithmicRateBeta factor eta) b n ≤
        logarithmicHorizon N t n) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < logarithmicDrawdown N (logarithmicRateBeta factor eta) b n) ∧
      (∀ᶠ n : ℕ in atTop,
        ⌊(logarithmicEndpointThreshold N zeta n +
          logarithmicDrawdown N (logarithmicRateBeta factor eta) b n) /
          (eta * logarithmicDrawdown N (logarithmicRateBeta factor eta) b n)⌋₊ = K) ∧
      (∀ᶠ n : ℕ in atTop,
        logarithmicSmallDeviationScale
          (logarithmicBlockLength N (logarithmicRateBeta factor eta) b n + 1) =
          logarithmicRateBeta factor eta *
            logarithmicDrawdown N (logarithmicRateBeta factor eta) b n) := by
  let beta := logarithmicRateBeta factor eta
  have hbeta : 0 < beta := by
    dsimp [beta, logarithmicRateBeta]
    positivity
  refine ⟨⌊(zeta / b + 1) / eta⌋₊, rfl,
    logarithmicSmallDeviationScale_isSmallDeviationScale,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact tendsto_logarithmicBlockLength_succ_atTop hN hbeta hb
  · exact tendsto_logarithmicBlockCount_atTop hN hbeta hb ht
  · exact tendsto_logarithmicBlockCost_atTop hN hbeta hb
  · exact tendsto_logarithmicTotalCost_atTop hN hbeta hb ht
  · exact tendsto_logarithmicCoverage hN hbeta hb ht
  · intro n
    exact logarithmicBlockCount_complete N beta b t n
  · exact eventually_logarithmicDrawdown_pos hN hbeta hb
  · simpa using eventually_logarithmicThreshold_floor hN hfactor heta hb hbin
  · exact eventually_logarithmicBlockScale_aligned hN hfactor heta hb

/-! ## Arbitrary horizons -/

private lemma tendsto_horizon_div_length_atTop_of_logCube_limit
    {N horizon : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b t : ℝ} (hbeta : 0 < beta) (hb : 0 < b) (ht : 0 < t)
    (hH : Tendsto (fun n => (horizon n : ℝ) /
      logarithmOfSampleSize N n ^ 3) atTop (𝓝 t)) :
    Tendsto (fun n => (horizon n : ℝ) /
      (logarithmicBlockLength N beta b n : ℝ)) atTop atTop := by
  let L := logarithmOfSampleSize N
  let root : ℕ → ℝ := fun n => Real.sqrt (L n)
  let gamma : ℝ := Real.sqrt (beta * b) ^ 5
  have hgammaPos : 0 < gamma :=
    pow_pos (Real.sqrt_pos.2 (mul_pos hbeta hb)) 5
  have hL : Tendsto L atTop atTop := tendsto_logarithmOfSampleSize_atTop hN
  have hroot : Tendsto root atTop atTop := Real.tendsto_sqrt_atTop.comp hL
  have hlen := tendsto_logarithmicBlockLength_div_log_two_sqrt hN hbeta hb
  have hratio : Tendsto
      (fun n => ((horizon n : ℝ) / L n ^ 3) /
        ((logarithmicBlockLength N beta b n : ℝ) /
          (L n ^ 2 * root n))) atTop (𝓝 (t / gamma)) := by
    have hdiv := hH.div hlen (ne_of_gt hgammaPos)
    change Tendsto
      ((fun n => (horizon n : ℝ) / logarithmOfSampleSize N n ^ 3) /
        (fun n => (logarithmicBlockLength N beta b n : ℝ) /
          (logarithmOfSampleSize N n ^ 2 *
            Real.sqrt (logarithmOfSampleSize N n))))
      atTop (𝓝 (t / gamma))
    exact hdiv
  have hscaled : Tendsto
      (fun n => root n * (((horizon n : ℝ) / L n ^ 3) /
        ((logarithmicBlockLength N beta b n : ℝ) /
          (L n ^ 2 * root n)))) atTop atTop :=
    hroot.atTop_mul_pos (div_pos ht hgammaPos) hratio
  have hlenPos : ∀ᶠ n : ℕ in atTop,
      0 < (logarithmicBlockLength N beta b n : ℝ) := by
    filter_upwards [] with n
    exact_mod_cast logarithmicBlockLength_pos N beta b n
  have heq : (fun n => root n * (((horizon n : ℝ) / L n ^ 3) /
      ((logarithmicBlockLength N beta b n : ℝ) /
        (L n ^ 2 * root n)))) =ᶠ[atTop]
      fun n => (horizon n : ℝ) /
        (logarithmicBlockLength N beta b n : ℝ) := by
    filter_upwards [hL.eventually_gt_atTop 0, hlenPos] with n hn hlen
    have hrootSq : root n ^ 2 = L n := Real.sq_sqrt (le_of_lt hn)
    have hrootNe : root n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
    have hLne : L n ≠ 0 := ne_of_gt hn
    have hlenNe : (logarithmicBlockLength N beta b n : ℝ) ≠ 0 := ne_of_gt hlen
    field_simp [hrootNe, hLne, hlenNe]
    rw [hrootSq]
    ring
  simpa [L, root, gamma] using hscaled.congr' heq

private lemma tendsto_logarithmicBlockCountForHorizon_atTop
    {N horizon : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b t : ℝ} (hbeta : 0 < beta) (hb : 0 < b) (ht : 0 < t)
    (hH : Tendsto (fun n => (horizon n : ℝ) /
      logarithmOfSampleSize N n ^ 3) atTop (𝓝 t)) :
    Tendsto (logarithmicBlockCountForHorizon N beta b horizon) atTop atTop := by
  have hquot := tendsto_horizon_div_length_atTop_of_logCube_limit
    hN hbeta hb ht hH
  change Tendsto
    (fun n => Nat.floor ((horizon n : ℝ) /
      (logarithmicBlockLength N beta b n : ℝ))) atTop atTop
  exact tendsto_nat_floor_atTop.comp hquot

private lemma tendsto_logarithmicBlockCountForHorizon_div_quotient
    {N horizon : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b t : ℝ} (hbeta : 0 < beta) (hb : 0 < b) (ht : 0 < t)
    (hH : Tendsto (fun n => (horizon n : ℝ) /
      logarithmOfSampleSize N n ^ 3) atTop (𝓝 t)) :
    Tendsto (fun n => (logarithmicBlockCountForHorizon N beta b horizon n : ℝ) /
      ((horizon n : ℝ) /
        (logarithmicBlockLength N beta b n : ℝ))) atTop (𝓝 1) := by
  have hquot := tendsto_horizon_div_length_atTop_of_logCube_limit
    hN hbeta hb ht hH
  change Tendsto
    (fun n => (Nat.floor ((horizon n : ℝ) /
      (logarithmicBlockLength N beta b n : ℝ)) : ℝ) /
        ((horizon n : ℝ) /
          (logarithmicBlockLength N beta b n : ℝ))) atTop (𝓝 1)
  exact tendsto_nat_floor_div_atTop.comp hquot

private lemma tendsto_logarithmicTotalCost_atTop_of_horizon
    {N horizon : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b t : ℝ} (hbeta : 0 < beta) (hb : 0 < b) (ht : 0 < t)
    (hH : Tendsto (fun n => (horizon n : ℝ) /
      logarithmOfSampleSize N n ^ 3) atTop (𝓝 t)) :
    Tendsto (fun n => (horizon n : ℝ) /
      logarithmicDrawdown N beta b n ^ 2) atTop atTop := by
  let L := logarithmOfSampleSize N
  have hL : Tendsto L atTop atTop := tendsto_logarithmOfSampleSize_atTop hN
  have hB := tendsto_logarithmicDrawdown_div_log hN hbeta hb
  have hbase : Tendsto
      (fun n => ((horizon n : ℝ) / L n ^ 3) /
        (logarithmicDrawdown N beta b n / L n) ^ 2) atTop
      (𝓝 (t / b ^ 2)) := by
    have hden := hB.pow 2
    have hdiv := hH.div hden (ne_of_gt (sq_pos_of_pos hb))
    change Tendsto
      ((fun n => (horizon n : ℝ) / L n ^ 3) /
        (fun n => (logarithmicDrawdown N beta b n / L n) ^ 2))
      atTop (𝓝 (t / b ^ 2))
    exact hdiv
  have hscaled := hL.atTop_mul_pos (div_pos ht (sq_pos_of_pos hb)) hbase
  have hdeltaPos := eventually_logarithmicDrawdown_pos hN hbeta hb
  have heq : (fun n => (horizon n : ℝ) /
      logarithmicDrawdown N beta b n ^ 2) =ᶠ[atTop]
      fun n => L n * (((horizon n : ℝ) / L n ^ 3) /
        (logarithmicDrawdown N beta b n / L n) ^ 2) := by
    filter_upwards [hL.eventually_gt_atTop 0, hdeltaPos] with n hn hδ
    have hLne : L n ≠ 0 := ne_of_gt hn
    have hδne : logarithmicDrawdown N beta b n ≠ 0 := ne_of_gt hδ
    field_simp [hLne, hδne]
  exact hscaled.congr' heq.symm

private lemma logarithmicBlockCountForHorizon_complete
    (N horizon : ℕ → ℕ) (beta b : ℝ) (n : ℕ) :
    logarithmicBlockCountForHorizon N beta b horizon n *
      logarithmicBlockLength N beta b n ≤ horizon n := by
  let len := logarithmicBlockLength N beta b n
  let H := horizon n
  have hlenPos : 0 < len := logarithmicBlockLength_pos N beta b n
  have hfloor :
      ((Nat.floor ((H : ℝ) / len) : ℕ) : ℝ) ≤ (H : ℝ) / len :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hmul := mul_le_mul_of_nonneg_right hfloor
    (Nat.cast_nonneg len : (0 : ℝ) ≤ len)
  have hcast : (Nat.floor ((H : ℝ) / len) : ℝ) * len ≤ H := by
    have hlenNe : (len : ℝ) ≠ 0 := by exact_mod_cast hlenPos.ne'
    have h := hmul
    field_simp [hlenNe] at h
    nlinarith [h]
  exact_mod_cast hcast

private lemma tendsto_logarithmicCoverageForHorizon
    {N horizon : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {beta b t : ℝ} (hbeta : 0 < beta) (hb : 0 < b) (ht : 0 < t)
    (hH : Tendsto (fun n => (horizon n : ℝ) /
      logarithmOfSampleSize N n ^ 3) atTop (𝓝 t)) :
    Tendsto (fun n => (logarithmicBlockCountForHorizon N beta b horizon n : ℝ) *
      (((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
        logarithmicDrawdown N beta b n ^ 2) /
      ((horizon n : ℝ) /
        logarithmicDrawdown N beta b n ^ 2)) atTop (𝓝 1) := by
  have hblocks := tendsto_logarithmicBlockCountForHorizon_div_quotient
    hN hbeta hb ht hH
  have hlength := tendsto_logarithmicLengthSucc_div_length hN hbeta hb
  have hprod := hblocks.mul hlength
  have hdeltaPos := eventually_logarithmicDrawdown_pos hN hbeta hb
  have hL : Tendsto (logarithmOfSampleSize N) atTop atTop :=
    tendsto_logarithmOfSampleSize_atTop hN
  have hHpos : ∀ᶠ n : ℕ in atTop, 0 < (horizon n : ℝ) := by
    have hratioPos := hH.eventually (Ioi_mem_nhds (by linarith : 0 < t))
    filter_upwards [hratioPos, hL.eventually_gt_atTop 0] with n hr hln
    have hden : 0 < logarithmOfSampleSize N n ^ 3 := pow_pos hln 3
    rcases (div_pos_iff.mp hr) with ⟨hnum, _⟩ | ⟨_, hdenNeg⟩
    · exact hnum
    · exact (False.elim (not_lt_of_ge hden.le hdenNeg))
  have heq : (fun n => (logarithmicBlockCountForHorizon N beta b horizon n : ℝ) *
      (((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
        logarithmicDrawdown N beta b n ^ 2) /
      ((horizon n : ℝ) /
        logarithmicDrawdown N beta b n ^ 2)) =ᶠ[atTop]
      fun n => ((logarithmicBlockCountForHorizon N beta b horizon n : ℝ) /
          ((horizon n : ℝ) /
            (logarithmicBlockLength N beta b n : ℝ))) *
        (((logarithmicBlockLength N beta b n + 1 : ℕ) : ℝ) /
          (logarithmicBlockLength N beta b n : ℝ)) := by
    filter_upwards [hdeltaPos, hHpos] with n hδ hHn
    have hδne : logarithmicDrawdown N beta b n ≠ 0 := ne_of_gt hδ
    have hlenPos : (0 : ℝ) < (logarithmicBlockLength N beta b n : ℝ) := by
      exact_mod_cast logarithmicBlockLength_pos N beta b n
    have hlenNe : (logarithmicBlockLength N beta b n : ℝ) ≠ 0 := ne_of_gt hlenPos
    field_simp [hδne, hlenNe, ne_of_gt hHn]
  simpa using hprod.congr' heq.symm

/-- Deterministic block parameters for any horizon whose ratio to `log N ^ 3`
tends to a positive constant.  The block count is the floor of the number of
whole blocks fitting in the horizon; its unused remainder is automatically
bounded by one block. -/
theorem logarithmicRawRateParametersForHorizon
    {N horizon : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {factor eta b t zeta : ℝ} (horizonTends :
      Tendsto (fun n => (horizon n : ℝ) /
        logarithmOfSampleSize N n ^ 3) atTop (𝓝 t))
    (hfactor : 1 < factor) (heta : 0 < eta) (hb : 0 < b) (ht : 0 < t)
    (hbin : (zeta / b + 1) / eta < 1 ∨
      ¬ ∃ k : ℕ, (zeta / b + 1) / eta = (k : ℝ)) :
    ∃ K : ℕ,
      K = ⌊(zeta / b + 1) / eta⌋₊ ∧
      Asymptotics.IsSmallDeviationScale logarithmicSmallDeviationScale
        (fun k => Real.sqrt (k : ℝ)) ∧
      Tendsto (fun n => logarithmicBlockLength N
        (logarithmicRateBeta factor eta) b n + 1) atTop atTop ∧
      Tendsto (logarithmicBlockCountForHorizon N
        (logarithmicRateBeta factor eta) b horizon) atTop atTop ∧
      Tendsto (fun n =>
        ((logarithmicBlockLength N (logarithmicRateBeta factor eta) b n + 1 : ℕ) : ℝ) /
          logarithmicDrawdown N (logarithmicRateBeta factor eta) b n ^ 2)
        atTop atTop ∧
      Tendsto (fun n => (horizon n : ℝ) /
        logarithmicDrawdown N (logarithmicRateBeta factor eta) b n ^ 2)
        atTop atTop ∧
      Tendsto (fun n => (logarithmicBlockCountForHorizon N
          (logarithmicRateBeta factor eta) b horizon n : ℝ) *
        (((logarithmicBlockLength N (logarithmicRateBeta factor eta) b n + 1 : ℕ) : ℝ) /
          logarithmicDrawdown N (logarithmicRateBeta factor eta) b n ^ 2) /
        ((horizon n : ℝ) /
          logarithmicDrawdown N (logarithmicRateBeta factor eta) b n ^ 2))
        atTop (𝓝 1) ∧
      (∀ n, logarithmicBlockCountForHorizon N
          (logarithmicRateBeta factor eta) b horizon n *
          logarithmicBlockLength N (logarithmicRateBeta factor eta) b n ≤
        horizon n) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < logarithmicDrawdown N (logarithmicRateBeta factor eta) b n) ∧
      (∀ᶠ n : ℕ in atTop,
        ⌊(logarithmicEndpointThreshold N zeta n +
          logarithmicDrawdown N (logarithmicRateBeta factor eta) b n) /
          (eta * logarithmicDrawdown N (logarithmicRateBeta factor eta) b n)⌋₊ = K) ∧
      (∀ᶠ n : ℕ in atTop,
        logarithmicSmallDeviationScale
          (logarithmicBlockLength N (logarithmicRateBeta factor eta) b n + 1) =
          logarithmicRateBeta factor eta *
            logarithmicDrawdown N (logarithmicRateBeta factor eta) b n) := by
  let beta := logarithmicRateBeta factor eta
  have hbeta : 0 < beta := by
    dsimp [beta, logarithmicRateBeta]
    positivity
  refine ⟨⌊(zeta / b + 1) / eta⌋₊, rfl,
    logarithmicSmallDeviationScale_isSmallDeviationScale,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact tendsto_logarithmicBlockLength_succ_atTop hN hbeta hb
  · exact tendsto_logarithmicBlockCountForHorizon_atTop
      hN hbeta hb ht horizonTends
  · exact tendsto_logarithmicBlockCost_atTop hN hbeta hb
  · exact tendsto_logarithmicTotalCost_atTop_of_horizon
      hN hbeta hb ht horizonTends
  · exact tendsto_logarithmicCoverageForHorizon hN hbeta hb ht horizonTends
  · intro n
    exact logarithmicBlockCountForHorizon_complete N horizon beta b n
  · exact eventually_logarithmicDrawdown_pos hN hbeta hb
  · simpa using eventually_logarithmicThreshold_floor hN hfactor heta hb hbin
  · exact eventually_logarithmicBlockScale_aligned hN hfactor heta hb
