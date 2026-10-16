/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.FiniteVarianceUpper.Lemmas.EqualPartition
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.BlockIteration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rate selection for the horizontal-tube upper bound

The proof-specific declarations are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.exists_partition_size_for_rate`: if $d<d_{\rm crit}$, some $m>0$
  satisfies $d(1+1/m)^2<d_{\rm crit}$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.eventually_uniform_partitionTube_rateBound`: for a fixed partition and
  $d_{\rm rate}<\pi^2\sigma^2/2$, every corridor in the partition has
  the required one-block exponential bound for all sufficiently large widths.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.horizontalTubeProbability_le_exp_of_partitionIndex`: combining the
  selected corridor, block rate, and remainder gives
  $\mathbb P(T_{a,\Delta,L})\le
  \exp(u\Delta^v-dL/\Delta^2)$.

These choices complete Wang Yiyang, *Asymptotic speed of the $N$-branching
random walk with infinite offspring*, Chapter 3, Lemma 3.2 and its following
remark.
-/

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

private theorem smallDeviationBlockFactor_mono
    {u v d : ℝ} (hu : 0 < u) (hv : 0 < v) (hd : 0 < d)
    {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    smallDeviationBlockFactor u v d n₁ ≤ smallDeviationBlockFactor u v d n₂ := by
  have hpow : (n₁ : ℝ) ^ v ≤ (n₂ : ℝ) ^ v :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) hv.le
  have hscaled : u * (n₁ : ℝ) ^ v ≤ u * (n₂ : ℝ) ^ v :=
    mul_le_mul_of_nonneg_left hpow hu.le
  have hquot : u * (n₁ : ℝ) ^ v / (2 * d) ≤ u * (n₂ : ℝ) ^ v / (2 * d) :=
    div_le_div_of_nonneg_right hscaled (by positivity)
  dsimp [smallDeviationBlockFactor]
  exact Nat.add_le_add_right (Nat.floor_mono hquot) 1

private theorem smallDeviationBlockFactor_tendsto
    {u v d : ℝ} (hu : 0 < u) (hv : 0 < v) (hd : 0 < d) :
    Tendsto (fun n : ℕ => (smallDeviationBlockFactor u v d n : ℝ))
      atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ v) atTop atTop :=
    (tendsto_rpow_atTop hv).comp tendsto_natCast_atTop_atTop
  have hscaled : Tendsto (fun n : ℕ => u * (n : ℝ) ^ v) atTop atTop :=
    hpow.const_mul_atTop hu
  have hquot : Tendsto (fun n : ℕ => u * (n : ℝ) ^ v / (2 * d)) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      hscaled.const_mul_atTop (one_div_pos.mpr (by positivity : 0 < 2 * d))
  have hfloor := tendsto_nat_floor_atTop.comp hquot
  have hfactorNat : Tendsto
      (fun n : ℕ => Nat.floor (u * (n : ℝ) ^ v / (2 * d)) + 1) atTop atTop :=
    tendsto_atTop_mono' atTop (Eventually.of_forall fun n => Nat.le_add_right _ 1) hfloor
  simpa [smallDeviationBlockFactor, Function.comp_def] using
    (tendsto_natCast_atTop_atTop.comp hfactorNat)

private theorem smallDeviationBlockLength_strictMono
    {u v d : ℝ} (hu : 0 < u) (hv : 0 < v) (hd : 0 < d) :
    StrictMono (fun k : ℕ => smallDeviationBlockLength u v d (k + 1) + 1) := by
  intro i j hij
  have hn : i + 1 < j + 1 := by omega
  have hfactor := smallDeviationBlockFactor_mono hu hv hd (Nat.le_of_lt hn)
  have hfactorPos : 0 < smallDeviationBlockFactor u v d (i + 1) :=
    Nat.succ_pos _
  have hsq : ((i + 1 : ℝ) ^ 2) < ((j + 1 : ℝ) ^ 2) := by
    have hi : 0 < (i + 1 : ℝ) := by positivity
    have hij' : (i + 1 : ℝ) < (j + 1 : ℝ) := by exact_mod_cast hn
    nlinarith
  have hmul : (smallDeviationBlockLength u v d (i + 1) : ℝ) <
      smallDeviationBlockLength u v d (j + 1) := by
    dsimp [smallDeviationBlockLength]
    have hfirst := mul_lt_mul_of_pos_right hsq
      (show 0 < (smallDeviationBlockFactor u v d (i + 1) : ℝ) by positivity)
    have hsecond := mul_le_mul_of_nonneg_left
      (show (smallDeviationBlockFactor u v d (i + 1) : ℝ) ≤
        smallDeviationBlockFactor u v d (j + 1) by exact_mod_cast hfactor)
      (show 0 ≤ (j + 1 : ℝ) ^ 2 by positivity)
    exact_mod_cast hfirst.trans_le hsecond
  have hnat : smallDeviationBlockLength u v d (i + 1) <
      smallDeviationBlockLength u v d (j + 1) := by
    exact_mod_cast hmul
  exact Nat.add_lt_add_right hnat 1


/-- Convert a strict logarithmic rate bound into the corresponding
probability bound. -/
private theorem probability_le_exp_of_scaledLogProbability_le
    {p : ℝ≥0∞} {width length rate : ℝ}
    (hp : p ≤ 1) (hwidth : 0 < width) (hlength : 0 < length)
    (hrate : 0 < rate)
    (hlog : width ^ 2 / length * Real.log p.toReal ≤ -rate) :
    p ≤ ENNReal.ofReal (Real.exp (-rate * (length / width ^ 2))) := by
  have hpTop : p ≠ ∞ := ne_of_lt (lt_of_le_of_lt hp ENNReal.one_lt_top)
  have hpReal : p.toReal ≤ 1 := by
    exact (ENNReal.toReal_mono ENNReal.one_ne_top hp).trans_eq ENNReal.toReal_one
  have hscale : 0 < width ^ 2 / length := div_pos (sq_pos_of_pos hwidth) hlength
  have hlog' : Real.log p.toReal ≤ (-rate) / (width ^ 2 / length) :=
    (le_div_iff₀ hscale).2 (by simpa [mul_comm] using hlog)
  have hlogEq : (-rate) / (width ^ 2 / length) = -rate * (length / width ^ 2) := by
    field_simp [ne_of_gt hlength, ne_of_gt (sq_pos_of_pos hwidth)]
  rw [hlogEq] at hlog'
  have hpRealPos : 0 < p.toReal := by
    by_contra h
    have hpZero : p.toReal = 0 := by
      exact le_antisymm (not_lt.mp h) (ENNReal.toReal_nonneg)
    rw [hpZero, Real.log_zero] at hlog'
    have hneg : -rate * (length / width ^ 2) < 0 :=
      mul_neg_of_neg_of_pos (neg_neg_of_pos hrate)
        (div_pos hlength (sq_pos_of_pos hwidth))
    exact (not_le_of_gt hneg) hlog'
  have hexp : p.toReal ≤ Real.exp (-rate * (length / width ^ 2)) := by
    rw [← Real.exp_log hpRealPos]
    exact Real.exp_le_exp.mpr hlog'
  calc
    p = ENNReal.ofReal p.toReal := (ENNReal.ofReal_toReal hpTop).symm
    _ ≤ ENNReal.ofReal (Real.exp (-rate * (length / width ^ 2))) :=
      ENNReal.ofReal_le_ofReal hexp

/-- A limiting Mogulskii rate supplies an eventual exponential estimate
whenever the requested exponent is strictly below the limiting rate. -/
private theorem eventually_probability_le_exp_of_scaledLogRate
    {probability : ℕ → ℝ≥0∞} {width length : ℕ → ℝ}
    {critical rate : ℝ}
    (hprob : ∀ k, probability k ≤ 1)
    (hwidth : ∀ k, 0 < width k) (hlength : ∀ k, 0 < length k)
    (hrate : Tendsto (fun k => width k ^ 2 / length k *
      Real.log (probability k).toReal) atTop (𝓝 (-critical)))
    (hratePos : 0 < rate) (hrateCritical : rate < critical) :
    ∀ᶠ k : ℕ in atTop,
      probability k ≤ ENNReal.ofReal
        (Real.exp (-rate * (length k / width k ^ 2))) := by
  have htarget : -critical < -rate := by linarith
  filter_upwards [hrate.eventually (eventually_lt_nhds htarget)] with k hk
  have hlog : width k ^ 2 / length k *
      Real.log (probability k).toReal ≤ -rate := le_of_lt hk
  exact probability_le_exp_of_scaledLogProbability_le (hprob k)
    (hwidth k) (hlength k) hratePos hlog

/-- The chosen block length grows faster than the square of its width. -/
private theorem smallDeviation_widthSq_div_blockLength_tendsto_zero
    {u v d c : ℝ} (hu : 0 < u) (hv : 0 < v) (hd : 0 < d) (hc : 0 < c) :
    Tendsto (fun k : ℕ =>
      (c * (k + 2 : ℕ) : ℝ) ^ 2 /
        (smallDeviationBlockLength u v d (k + 1) + 1 : ℕ))
      atTop (𝓝 0) := by
  let factor : ℕ → ℝ := fun k =>
    (smallDeviationBlockFactor u v d (k + 1) : ℝ)
  have hfactor : Tendsto factor atTop atTop := by
    simpa [factor, Function.comp_def] using
      smallDeviationBlockFactor_tendsto hu hv hd |>.comp
        (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun k => (factor k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hfactor
  have hbound : Tendsto (fun k => 4 * c ^ 2 * (factor k)⁻¹)
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => 4 * c ^ 2) atTop (𝓝 (4 * c ^ 2)) :=
      tendsto_const_nhds
    simpa [mul_assoc] using hconst.mul hinv
  have hwidth : ∀ k : ℕ,
      0 ≤ (c * (k + 2 : ℕ) : ℝ) ^ 2 /
        (smallDeviationBlockLength u v d (k + 1) + 1 : ℕ) := by
    intro k
    positivity
  have hle : ∀ k : ℕ,
      (c * (k + 2 : ℕ) : ℝ) ^ 2 /
          (smallDeviationBlockLength u v d (k + 1) + 1 : ℕ) ≤
        4 * c ^ 2 * (factor k)⁻¹ := by
    intro k
    have hNat : 0 < smallDeviationBlockFactor u v d (k + 1) := Nat.succ_pos _
    have hn : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    have hf : 0 < factor k := by dsimp [factor]; exact_mod_cast hNat
    have hlen : (smallDeviationBlockLength u v d (k + 1) + 1 : ℕ) =
        ((k + 1 : ℝ) ^ 2 * factor k + 1) := by
      simp [factor, smallDeviationBlockLength, pow_two]
    have hratio : (c * (k + 2 : ℕ) : ℝ) ^ 2 /
        (smallDeviationBlockLength u v d (k + 1) + 1 : ℕ) ≤
          4 * c ^ 2 / factor k := by
      rw [hlen]
      apply (div_le_iff₀ (by positivity : 0 < ((k + 1 : ℝ) ^ 2 * factor k + 1))).2
      have hstep : (k + 2 : ℕ) = (k + 1) + 1 := by omega
      have hstepR : (k + 2 : ℕ) = ((k + 1 : ℝ) + 1) := by
        exact_mod_cast hstep
      rw [hstepR]
      dsimp [factor]
      have hsmallSq : ((k + 1 : ℝ) + 1) ^ 2 ≤ 4 * (k + 1 : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((k + 1 : ℝ) - 1)]
      have hratio' : c ^ 2 * ((k + 1 : ℝ) + 1) ^ 2 ≤
          (4 * c ^ 2 / factor k) * ((k + 1 : ℝ) ^ 2 * factor k + 1) := by
        calc
          c ^ 2 * ((k + 1 : ℝ) + 1) ^ 2 ≤
              c ^ 2 * (4 * (k + 1 : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hsmallSq (sq_nonneg c)
          _ ≤ (4 * c ^ 2 / factor k) * ((k + 1 : ℝ) ^ 2 * factor k + 1) := by
            field_simp [ne_of_gt hf]
            nlinarith [sq_nonneg c]
      nlinarith [hratio']
    simpa [div_eq_mul_inv] using hratio
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound (Filter.Eventually.of_forall hwidth)
    (Filter.Eventually.of_forall hle)

theorem exists_partition_size_for_rate {d critical : ℝ}
    (hcritical : d < critical) :
    ∃ m : ℕ, 0 < m ∧ d * (1 + 1 / (m : ℝ)) ^ 2 < critical := by
  have hinv : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsum : Tendsto (fun m : ℕ => 1 + 1 / (m : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hlimit : Tendsto (fun m : ℕ => d * (1 + 1 / (m : ℝ)) ^ 2)
      atTop (𝓝 d) := by
    simpa using tendsto_const_nhds.mul (hsum.pow 2)
  obtain ⟨m, hmBound, hmPos⟩ :=
    (hlimit.eventually (eventually_lt_nhds hcritical)).and
      (eventually_gt_atTop (0 : ℕ)) |>.exists
  exact ⟨m, hmPos, hmBound⟩

private theorem partitionTubeParameter_mem_Ioo {m : ℕ} (hm : 0 < m)
    (k : Fin m) :
    0 < partitionTubeParameter m k ∧ partitionTubeParameter m k < 1 := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hkNonneg : 0 ≤ (k : ℝ) / m := div_nonneg (by positivity) hmReal.le
  have hkLt : (k : ℝ) < m := by exact_mod_cast k.isLt
  have hkLt' : (k : ℝ) < 1 * m := by simp [one_mul, hkLt]
  have hkFracLt : (k : ℝ) / m < 1 := (div_lt_iff₀ hmReal).2 hkLt'
  have hnum : 0 < 1 - (k : ℝ) / m := by linarith
  have hdenom : 0 < 1 + 1 / (m : ℝ) := by positivity
  constructor
  · exact div_pos hnum hdenom
  · apply (div_lt_iff₀ hdenom).2
    have hfracPos : 0 < 1 / (m : ℝ) := by positivity
    linarith

theorem eventually_uniform_partitionTube_rateBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x : ℝ, x ^ 2 ∂ν)
    {u v d : ℝ} (hu : 0 < u) (hv : 0 < v) (hd : 0 < d)
    {m : ℕ} (hm : 0 < m) {rate : ℝ}
    (hratePos : 0 < rate)
    (hrateCritical : rate < (Real.pi ^ 2 / 2) * (∫ x : ℝ, x ^ 2 ∂ν)) :
    ∀ᶠ k : ℕ in atTop, ∀ j : Fin m,
      horizontalTubeProbability (iidSequenceLaw ν)
          (partitionTubeParameter m j)
          (partitionTubeWidth m ((k + 2 : ℕ) : ℝ))
          (smallDeviationBlockLength u v d (k + 1)) ≤
        ENNReal.ofReal (Real.exp
          (-rate * ((smallDeviationBlockLength u v d (k + 1) : ℝ) /
            (partitionTubeWidth m ((k + 2 : ℕ) : ℝ)) ^ 2))) := by
  let block : ℕ → ℕ := fun k => smallDeviationBlockLength u v d (k + 1)
  let time : ℕ → ℕ := fun k => block k + 1
  let width : ℕ → ℝ := fun k => partitionTubeWidth m ((k + 2 : ℕ) : ℝ)
  let lengthReal : ℕ → ℝ := fun k => (block k : ℝ)
  have hc : 0 < 1 + 1 / (m : ℝ) := by positivity
  have htimeStrict : StrictMono time := by
    simpa [time, block] using smallDeviationBlockLength_strictMono hu hv hd
  have htimePos : ∀ k, 0 < time k := by
    intro k
    simp [time]
  have hwidthPos : ∀ k, 0 < width k := by
    intro k
    simp [width, partitionTubeWidth]
    positivity
  have hwidthTop : Tendsto width atTop atTop := by
    have hindex : Tendsto (fun k : ℕ => ((k + 2 : ℕ) : ℝ)) atTop atTop := by
      simpa using tendsto_atTop_add_const_right atTop (2 : ℝ)
        tendsto_natCast_atTop_atTop
    have hscaled := hindex.const_mul_atTop hc
    simpa [width, partitionTubeWidth, mul_comm] using hscaled
  have hwidthSq : Tendsto (fun k : ℕ => width k ^ 2 / (time k : ℝ))
      atTop (𝓝 0) := by
    simpa [width, time, block, partitionTubeWidth] using
      smallDeviation_widthSq_div_blockLength_tendsto_zero hu hv hd hc
  have hrateEach : ∀ j : Fin m, ∀ᶠ k : ℕ in atTop,
      horizontalTubeProbability (iidSequenceLaw ν) (partitionTubeParameter m j)
          (width k) (block k) ≤
        ENNReal.ofReal (Real.exp (-rate *
          (lengthReal k / width k ^ 2))) := fun j => by
      have haj := partitionTubeParameter_mem_Ioo hm j
      have hrate := centeredFiniteVariance_closedHorizontalTubeProbabilityRate_realWidthAlong
        htimeStrict htimePos hwidthPos hwidthTop hwidthSq hcentered hsquare
        hvariance haj.1 haj.2
      have hrateBase : Tendsto (fun k : ℕ => width k ^ 2 / lengthReal k *
          Real.log (horizontalTubeProbability (iidSequenceLaw ν)
            (partitionTubeParameter m j) (width k) (block k)).toReal)
          atTop (𝓝 (-Real.pi ^ 2 / 2 * (∫ x : ℝ, x ^ 2 ∂ν))) := by
        simpa [time, block, width, lengthReal,
          partitionTubeWidth, mul_comm, mul_left_comm, mul_assoc] using hrate
      have hlimit : -Real.pi ^ 2 / 2 * (∫ x : ℝ, x ^ 2 ∂ν) =
          -((Real.pi ^ 2 / 2) * (∫ x : ℝ, x ^ 2 ∂ν)) := by ring_nf
      have hrate' : Tendsto (fun k : ℕ => width k ^ 2 / lengthReal k *
          Real.log (horizontalTubeProbability (iidSequenceLaw ν)
            (partitionTubeParameter m j) (width k) (block k)).toReal)
          atTop (𝓝 (-((Real.pi ^ 2 / 2) * (∫ x : ℝ, x ^ 2 ∂ν)))) := by
        simpa only [hlimit] using hrateBase
      have hprob : ∀ k : ℕ,
          horizontalTubeProbability (iidSequenceLaw ν)
            (partitionTubeParameter m j) (width k) (block k) ≤ 1 := by
        intro k
        unfold horizontalTubeProbability
        exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
      have hlengthPos : ∀ k : ℕ, 0 < lengthReal k := by
        intro k
        dsimp [lengthReal, block]
        exact_mod_cast Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _)) (Nat.succ_pos _)
      exact eventually_probability_le_exp_of_scaledLogRate hprob hwidthPos hlengthPos hrate' hratePos hrateCritical
  have hfinite : ∀ᶠ k : ℕ in atTop, ∀ j : Fin m,
      horizontalTubeProbability (iidSequenceLaw ν) (partitionTubeParameter m j)
          (width k) (block k) ≤
        ENNReal.ofReal (Real.exp (-rate * (lengthReal k / width k ^ 2))) := by
    have hfinite' : ∀ᶠ k : ℕ in atTop, ∀ j ∈ (Finset.univ : Finset (Fin m)),
        horizontalTubeProbability (iidSequenceLaw ν) (partitionTubeParameter m j)
            (width k) (block k) ≤
          ENNReal.ofReal (Real.exp (-rate * (lengthReal k / width k ^ 2))) := by
      refine (Finset.eventually_all (Finset.univ : Finset (Fin m))).mpr ?_
      intro j hj
      exact hrateEach j
    simpa using hfinite'
  filter_upwards [hfinite] with k hk j
  simpa [width, block, lengthReal] using hk j

theorem horizontalTubeProbability_le_exp_of_partitionIndex
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {u v d : ℝ} (hu : 0 < u) (hv : 0 < v) (hd : 0 < d)
    {m n : ℕ} (hm : 0 < m) {rate : ℝ}
    (hratePos : 0 < rate)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hnPos : 0 < (n : ℝ)) (hnΔ : (n : ℝ) ≤ Δ)
    (hΔn : Δ < (n : ℝ) + 1)
    (hcoefficient : d * (1 + 1 / (m : ℝ)) ^ 2 *
        (1 + 1 / (n : ℝ)) ^ 2 < rate)
    (hrounding : 2 * d ≤ u * (n : ℝ) ^ v)
    (hindexRate : ∀ j : Fin m,
      horizontalTubeProbability (iidSequenceLaw ν) (partitionTubeParameter m j)
        (partitionTubeWidth m ((n : ℝ) + 1))
        (smallDeviationBlockLength u v d n) ≤
        ENNReal.ofReal (Real.exp (-rate *
          ((smallDeviationBlockLength u v d n : ℝ) /
            (partitionTubeWidth m ((n : ℝ) + 1)) ^ 2))))
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (horizon : ℕ) :
    horizontalTubeProbability (iidSequenceLaw ν) a Δ horizon ≤
      ENNReal.ofReal (Real.exp
        (u * Δ ^ v - d * ((horizon : ℝ) / Δ ^ 2))) := by
  let block := smallDeviationBlockLength u v d n
  let largeWidth := partitionTubeWidth m ((n : ℝ) + 1)
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnDeltaPos : 0 < (n : ℝ) := hnPos
  have hc : 0 < 1 + 1 / (m : ℝ) := by positivity
  have hlargeWidth : 0 < largeWidth := by
    dsimp [largeWidth, partitionTubeWidth]
    positivity
  have hdeltaWidth : 0 < partitionTubeWidth m Δ := by
    dsimp [partitionTubeWidth]
    positivity
  have hwidthOrder : partitionTubeWidth m Δ ≤ largeWidth := by
    dsimp [largeWidth, partitionTubeWidth]
    exact mul_le_mul_of_nonneg_left hΔn.le hc.le
  have hidentity : (1 + 1 / (n : ℝ)) ^ 2 * (n : ℝ) ^ 2 =
      ((n : ℝ) + 1) ^ 2 := by
    field_simp [ne_of_gt hnDeltaPos]
  have hcoefficientAtN : d * (1 + 1 / (m : ℝ)) ^ 2 *
      ((n : ℝ) + 1) ^ 2 < rate * (n : ℝ) ^ 2 := by
    calc
      d * (1 + 1 / (m : ℝ)) ^ 2 * ((n : ℝ) + 1) ^ 2 =
          (d * (1 + 1 / (m : ℝ)) ^ 2 * (1 + 1 / (n : ℝ)) ^ 2) *
            (n : ℝ) ^ 2 := by rw [← hidentity]; ring
      _ < rate * (n : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_right hcoefficient (sq_pos_of_pos hnDeltaPos)
  have hnSquareLe : (n : ℝ) ^ 2 ≤ Δ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnΔ)
      (add_nonneg hnDeltaPos.le hΔ.le)]
  have hcoefficientAtDelta : d * largeWidth ^ 2 < rate * Δ ^ 2 := by
    calc
      d * largeWidth ^ 2 =
          d * (1 + 1 / (m : ℝ)) ^ 2 * ((n : ℝ) + 1) ^ 2 := by
            dsimp [largeWidth, partitionTubeWidth]
            ring
      _ < rate * (n : ℝ) ^ 2 := hcoefficientAtN
      _ ≤ rate * Δ ^ 2 := mul_le_mul_of_nonneg_left hnSquareLe hratePos.le
  have hrateScale : d / Δ ^ 2 < rate / largeWidth ^ 2 :=
    (div_lt_div_iff₀ (sq_pos_of_pos hΔ) (sq_pos_of_pos hlargeWidth)).2
      hcoefficientAtDelta
  have hblockNonneg : 0 ≤ (block : ℝ) := by positivity
  have hblockCost : d * ((block : ℝ) / Δ ^ 2) ≤
      rate * ((block : ℝ) / largeWidth ^ 2) := by
    calc
      d * ((block : ℝ) / Δ ^ 2) = (d / Δ ^ 2) * (block : ℝ) := by ring
      _ ≤ (rate / largeWidth ^ 2) * (block : ℝ) :=
        mul_le_mul_of_nonneg_right hrateScale.le hblockNonneg
      _ = rate * ((block : ℝ) / largeWidth ^ 2) := by ring
  have hblockExponent : -rate * ((block : ℝ) / largeWidth ^ 2) ≤
      -d * ((block : ℝ) / Δ ^ 2) := by nlinarith [hblockCost]
  have hfactorBound :
      (smallDeviationBlockFactor u v d n : ℝ) ≤ u * (n : ℝ) ^ v / d := by
    dsimp [smallDeviationBlockFactor]
    rw [Nat.cast_add, Nat.cast_one]
    have hquotNonneg : 0 ≤ u * (n : ℝ) ^ v / (2 * d) := by positivity
    have hfloor := Nat.floor_le hquotNonneg
    have hquotLarge : 1 ≤ u * (n : ℝ) ^ v / (2 * d) :=
      (le_div_iff₀ (by positivity : 0 < 2 * d)).2 (by nlinarith [hrounding])
    have hquotDouble : 2 * (u * (n : ℝ) ^ v / (2 * d)) =
        u * (n : ℝ) ^ v / d := by
      field_simp [ne_of_gt hd]
    nlinarith [hfloor, hquotLarge, hquotDouble]
  have hblockEq : (block : ℝ) = (n : ℝ) ^ 2 *
      (smallDeviationBlockFactor u v d n : ℝ) := by
    simp [block, smallDeviationBlockLength]
  have hpowN : (n : ℝ) ^ 2 * (n : ℝ) ^ v = (n : ℝ) ^ (2 + v) := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hnDeltaPos]
    congr 1
  have hblockPower : (block : ℝ) ≤ u * (n : ℝ) ^ (2 + v) / d := by
    calc
      (block : ℝ) = (n : ℝ) ^ 2 *
      (smallDeviationBlockFactor u v d n : ℝ) := hblockEq
      _ ≤ (n : ℝ) ^ 2 * (u * (n : ℝ) ^ v / d) :=
        mul_le_mul_of_nonneg_left hfactorBound (sq_nonneg _)
      _ = u * ((n : ℝ) ^ 2 * (n : ℝ) ^ v) / d := by ring
      _ = u * (n : ℝ) ^ (2 + v) / d := by rw [hpowN]
  have hdeltaPower : Δ ^ (2 + v) = Δ ^ 2 * Δ ^ v := by
    rw [Real.rpow_add hΔ]
    congr 1
    exact Real.rpow_natCast Δ 2
  have hnPowerLe : (n : ℝ) ^ (2 + v) ≤ Δ ^ (2 + v) :=
    Real.rpow_le_rpow hnDeltaPos.le hnΔ (by linarith)
  have hblockRemainder : d * ((block : ℝ) / Δ ^ 2) ≤ u * Δ ^ v := by
    have hblockDelta : (block : ℝ) ≤ (Δ ^ 2 * (u * Δ ^ v)) / d := by
      calc
        (block : ℝ) ≤ u * (n : ℝ) ^ (2 + v) / d := hblockPower
        _ ≤ u * Δ ^ (2 + v) / d := by
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hnPowerLe hu.le
          · positivity
        _ = (Δ ^ 2 * (u * Δ ^ v)) / d := by rw [hdeltaPower]; ring
    calc
      d * ((block : ℝ) / Δ ^ 2) = (d / Δ ^ 2) * (block : ℝ) := by ring
      _ ≤ (d / Δ ^ 2) * ((Δ ^ 2 * (u * Δ ^ v)) / d) :=
        mul_le_mul_of_nonneg_left hblockDelta (by positivity)
      _ = u * Δ ^ v := by field_simp [ne_of_gt hΔ]
  have hblockProbability : ∀ b ∈ Set.Icc (0 : ℝ) 1,
      horizontalTubeProbability (iidSequenceLaw ν) b Δ block ≤
        ENNReal.ofReal (Real.exp (-d * ((block : ℝ) / Δ ^ 2))) := by
    intro b hb
    obtain ⟨j, hcover⟩ := horizontalTubeProbability_le_one_partitionTube ν hm
      hb.1 hb.2 hΔ
    have hwidthMono := horizontalTubeProbability_mono_width
      (iidSequenceLaw ν) (a := partitionTubeParameter m j)
      (n := block)
      (by exact (partitionTubeParameter_mem_Ioo hm j).1.le)
      (by exact (partitionTubeParameter_mem_Ioo hm j).2.le)
      hwidthOrder
    calc
      horizontalTubeProbability (iidSequenceLaw ν) b Δ block ≤
          horizontalTubeProbability (iidSequenceLaw ν)
            (partitionTubeParameter m j) (partitionTubeWidth m Δ) block := hcover
      _ ≤ horizontalTubeProbability (iidSequenceLaw ν)
            (partitionTubeParameter m j) largeWidth block := by
          exact hwidthMono
      _ ≤ ENNReal.ofReal (Real.exp (-rate * ((block : ℝ) / largeWidth ^ 2))) := by
          simpa [block, largeWidth] using hindexRate j
      _ ≤ ENNReal.ofReal (Real.exp (-d * ((block : ℝ) / Δ ^ 2))) :=
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hblockExponent)
  have hnNat : 0 < n := by exact_mod_cast hnPos
  have hblockPos : 0 < block := by
    dsimp [block, smallDeviationBlockLength]
    exact Nat.mul_pos (Nat.pow_pos hnNat) (Nat.succ_pos _)
  exact horizontalTubeProbability_le_exp_of_uniformTubeBlockBound ν ha.1 ha.2
    hΔ hd block horizon hblockPos
    hblockRemainder hblockProbability

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
