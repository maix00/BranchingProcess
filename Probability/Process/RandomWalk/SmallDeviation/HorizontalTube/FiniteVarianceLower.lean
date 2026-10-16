/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.Normal.HorizontalTube.EndpointWindow
/-!
# Finite-variance horizontal-tube endpoint lower bounds

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.eventually_horizontalTubeEndpointWindowProbability_ge_exp_of_centeredSecondMoment`:
  for centered increments of variance $\sigma^2>0$, tube widths tending to infinity,
  and time scales growing faster than the squared width, the probability of
  a horizontal tube with an interior endpoint window has the exponential
  lower bound with any rate above $\pi^2\sigma^2/2$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.exists_eventually_horizontalTubeEndpointWindowProbability_ge_exp_uniform`:
  the same lower bound with common width and time-ratio thresholds for all
  integer widths and horizons.

These are the exponential consequences of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii).
The rate input is Theorem 3, Section 4, p. 764 of A. A. Mogul'skii,
“Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations
in a Space of Trajectories,” *Theory of Probability and Its Applications*
19(1) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The endpoint-window rate in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii),
implies this exponential lower bound along any diverging sequence of integer
tube widths. The endpoint fractions may vary with the width provided they
eventually contain one fixed interval strictly inside the tube. The rate input
is Theorem 3, Section 4, p. 764 of A. A. Mogul'skii, “Small deviations in the
sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(1) (1975), 726--736, DOI
10.1137/1119081. -/
theorem eventually_horizontalTubeEndpointWindowProbability_ge_exp_of_centeredSecondMoment
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma d a u v : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {time width : ℕ → ℕ} (htime : StrictMono time)
    (htimePos : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => (width n : ℝ)) atTop atTop)
    (hwidthSq : Tendsto
      (fun n => (width n : ℝ) ^ 2 / (time n : ℝ)) atTop (𝓝 0))
    {v₁ v₂ : ℕ → ℝ}
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hwindow : ∀ᶠ n : ℕ in atTop,
      v₁ (width n) ≤ u ∧ v ≤ v₂ (width n))
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp
        (-d * ((time n - 1 : ℕ) : ℝ) / (width n : ℝ) ^ 2)) ≤
      horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
        (width n : ℝ) (time n - 1) (v₁ (width n)) (v₂ (width n)) := by
  rcases hν with ⟨hcentered, hsecondMoment⟩
  have hsquare : Integrable (fun x : ℝ => x ^ 2) ν := by
    exact Integrable.of_integral_ne_zero (by
      rw [hsecondMoment]
      exact ne_of_gt (sq_pos_of_pos hsigma))
  have hvariance : 0 < ∫ x : ℝ, x ^ 2 ∂ν := by
    rw [hsecondMoment]
    exact sq_pos_of_pos hsigma
  have hrate := centeredFiniteVariance_endpointWindowProbabilityRate_along
    htime htimePos hwidth hwidthSq ha haOne hu huv hv hwindow
    hcentered hsquare hvariance
  let rate : ℕ → ℝ := fun n => (width n : ℝ) ^ 2 /
    ((time n - 1 : ℕ) : ℝ) * Real.log
      (horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
        (width n : ℝ) (time n - 1) (v₁ (width n)) (v₂ (width n))).toReal
  have hlimit : Tendsto rate atTop
      (𝓝 (-(Real.pi ^ 2 / 2) * sigma ^ 2)) := by
    have h := hrate
    rw [hsecondMoment] at h
    simpa [rate, div_eq_mul_inv, mul_assoc] using h
  have hcritical : 0 < (Real.pi ^ 2 / 2) * sigma ^ 2 :=
    mul_pos (by positivity) (sq_pos_of_pos hsigma)
  have hrateLower : ∀ᶠ n : ℕ in atTop, -d < rate n :=
    hlimit.eventually (Ioi_mem_nhds (by nlinarith [hd]))
  have hrateNegative : ∀ᶠ n : ℕ in atTop, rate n < 0 :=
    hlimit.eventually (Iio_mem_nhds (by nlinarith [hcritical]))
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < (width n : ℝ) := by
    exact hwidth.eventually (eventually_gt_atTop 0)
  have htimeLarge : ∀ᶠ n : ℕ in atTop, 1 < time n :=
    htime.tendsto_atTop.eventually (eventually_gt_atTop 1)
  filter_upwards [hrateLower, hrateNegative, hwidthPos, htimeLarge]
    with n hrateLow hrateNeg hwidthN htimeN
  let probability := horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
    (width n : ℝ) (time n - 1) (v₁ (width n)) (v₂ (width n))
  have hlength : 0 < ((time n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt htimeN)
  let factor : ℝ := (width n : ℝ) ^ 2 /
    ((time n - 1 : ℕ) : ℝ)
  have hfactorPos : 0 < factor := div_pos (sq_pos_of_pos hwidthN) hlength
  have hlogNegative :
      Real.log probability.toReal < 0 := by
    have hrateEq : rate n =
        ((width n : ℝ) ^ 2 /
          ((time n - 1 : ℕ) : ℝ)) * Real.log probability.toReal := by
      rfl
    rw [hrateEq] at hrateNeg
    have hrateNeg' : factor * Real.log probability.toReal < 0 := by
      simpa [factor] using hrateNeg
    by_contra hlog
    have hlogNonneg : 0 ≤ Real.log probability.toReal := le_of_not_gt hlog
    have hproductNonneg := mul_nonneg hfactorPos.le hlogNonneg
    exact (not_lt_of_ge hproductNonneg) hrateNeg'
  have hprobabilityNeZero : probability ≠ 0 := by
    intro hzero
    have hlogZero : Real.log probability.toReal = 0 := by simp [hzero]
    rw [hlogZero] at hlogNegative
    exact (lt_irrefl 0) hlogNegative
  have hprobabilityPos : 0 < probability.toReal :=
    ENNReal.toReal_pos hprobabilityNeZero (measure_ne_top _ _)
  have hlogBound :
      -d * ((time n - 1 : ℕ) : ℝ) / (width n : ℝ) ^ 2 <
        Real.log probability.toReal := by
    have hrateEq : rate n =
        ((width n : ℝ) ^ 2 /
          ((time n - 1 : ℕ) : ℝ)) * Real.log probability.toReal := by
      rfl
    rw [hrateEq] at hrateLow
    have hrateLow' : -d < factor * Real.log probability.toReal := by
      simpa [factor] using hrateLow
    have hdiv : -d / factor < Real.log probability.toReal :=
      (div_lt_iff₀ hfactorPos).2 (by simpa [mul_comm] using hrateLow')
    calc
      -d * ((time n - 1 : ℕ) : ℝ) / (width n : ℝ) ^ 2 =
          -d / factor := by
        dsimp [factor]
        field_simp [ne_of_gt hwidthN, ne_of_gt hlength]
      _ < Real.log probability.toReal := hdiv
  have hexp : Real.exp
      (-d * ((time n - 1 : ℕ) : ℝ) / (width n : ℝ) ^ 2) ≤
        probability.toReal := by
    rw [← Real.exp_log hprobabilityPos]
    exact le_of_lt (Real.exp_lt_exp.mpr hlogBound)
  have hprobabilityTop : probability ≠ ⊤ := measure_ne_top _ _
  change ENNReal.ofReal (Real.exp
    (-d * ((time n - 1 : ℕ) : ℝ) / (width n : ℝ) ^ 2)) ≤ probability
  rw [← ENNReal.ofReal_toReal hprobabilityTop]
  exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).2 hexp

/-- Uniformity in the integer tube width and horizon follows from the
sequential endpoint-window rate in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii).
The endpoint interval is the fixed interval `[u,v]`; this is the block
estimate used after narrowing each staircase tube in Chapter 3, Lemma 3.5.
The rate input is Theorem 3, Section 4, p. 764 of A. A. Mogul'skii, “Small
deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations
in a Space of Trajectories,” *Theory of Probability and Its Applications*
19(1) (1975), 726--736, DOI 10.1137/1119081. -/
theorem exists_eventually_horizontalTubeEndpointWindowProbability_ge_exp_uniform
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma d a u v : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d) :
    ∃ width₀ ratio₀ : ℕ, ∀ width : ℕ, width₀ ≤ width →
      ∀ horizon : ℕ, ratio₀ * width ^ 2 ≤ horizon →
        ENNReal.ofReal (Real.exp
          (-d * (horizon : ℝ) / (width : ℝ) ^ 2)) ≤
        horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
          (width : ℝ) horizon u v := by
  classical
  by_contra hnot
  push Not at hnot
  let widthRaw : ℕ → ℕ := fun n => Classical.choose (hnot (n + 1) (n + 1))
  have hwidthRaw (n : ℕ) : n + 1 ≤ widthRaw n :=
    (Classical.choose_spec (hnot (n + 1) (n + 1))).1
  have hrawHorizon (n : ℕ) : ∃ horizon : ℕ,
      (n + 1) * widthRaw n ^ 2 ≤ horizon ∧
        horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
            (widthRaw n : ℝ) horizon u v < ENNReal.ofReal (Real.exp
          (-d * (horizon : ℝ) / (widthRaw n : ℝ) ^ 2)) :=
    (Classical.choose_spec (hnot (n + 1) (n + 1))).2
  let horizonRaw : ℕ → ℕ := fun n => Classical.choose (hrawHorizon n)
  have hrawRatio (n : ℕ) : (n + 1) * widthRaw n ^ 2 ≤ horizonRaw n :=
    (Classical.choose_spec (hrawHorizon n)).1
  have hrawFail (n : ℕ) :
      horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
          (widthRaw n : ℝ) (horizonRaw n) u v < ENNReal.ofReal (Real.exp
        (-d * (horizonRaw n : ℝ) / (widthRaw n : ℝ) ^ 2)) :=
    (Classical.choose_spec (hrawHorizon n)).2
  have hwidthRawTop : Tendsto widthRaw atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact le_trans (by omega) (hwidthRaw n)
  let timeRaw : ℕ → ℕ := fun n => horizonRaw n + 1
  have htimeRawLower (n : ℕ) : widthRaw n ≤ timeRaw n := by
    have hwidthPos : 1 ≤ widthRaw n := by
      have := hwidthRaw n
      omega
    have hwidthSqLower : widthRaw n ≤ widthRaw n ^ 2 := by
      calc
        widthRaw n = widthRaw n * 1 := by simp
        _ ≤ widthRaw n * widthRaw n := Nat.mul_le_mul_left _ hwidthPos
        _ = widthRaw n ^ 2 := by ring
    have hmul : widthRaw n ^ 2 ≤ (n + 1) * widthRaw n ^ 2 := by
      calc
        widthRaw n ^ 2 = 1 * widthRaw n ^ 2 := by simp
        _ ≤ (n + 1) * widthRaw n ^ 2 := Nat.mul_le_mul_right _ (by omega)
    calc
      widthRaw n ≤ widthRaw n ^ 2 := hwidthSqLower
      _ ≤ (n + 1) * widthRaw n ^ 2 := hmul
      _ ≤ horizonRaw n := hrawRatio n
      _ ≤ timeRaw n := by dsimp [timeRaw]; omega
  have htimeRawTop : Tendsto timeRaw atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hwidthRawTop.eventually (eventually_ge_atTop b)] with n hn
    exact le_trans hn (htimeRawLower n)
  obtain ⟨ψ, hψ, htimeRawStrict⟩ := strictMono_subseq_of_tendsto_atTop htimeRawTop
  let indexFinal : ℕ → ℕ := ψ
  let widthFinal : ℕ → ℕ := fun k => widthRaw (indexFinal k)
  let horizonFinal : ℕ → ℕ := fun k => horizonRaw (indexFinal k)
  let timeFinal : ℕ → ℕ := fun k => timeRaw (indexFinal k)
  have hindexFinalTop : Tendsto indexFinal atTop atTop := by
    exact hψ.tendsto_atTop
  have hwidthFinalTop : Tendsto widthFinal atTop atTop :=
    hwidthRawTop.comp hindexFinalTop
  have hwidthFinalRealTop : Tendsto (fun k => (widthFinal k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthFinalTop
  have htimeFinalStrict : StrictMono timeFinal := by
    exact htimeRawStrict
  have htimeFinalPos : ∀ k, 0 < timeFinal k := by
    intro k
    dsimp [timeFinal, timeRaw]
    omega
  have hwidthSq : Tendsto
      (fun k => (widthFinal k : ℝ) ^ 2 / (timeFinal k : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun k =>
        div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    · filter_upwards with k
      have htimeBoundNat : (indexFinal k + 1) * widthFinal k ^ 2 ≤ timeFinal k := by
        dsimp [timeFinal, timeRaw, widthFinal]
        exact Nat.le_succ_of_le (hrawRatio (indexFinal k))
      have htimeK : 0 < (timeFinal k : ℝ) := by positivity
      have hindexK : 0 < ((indexFinal k + 1 : ℕ) : ℝ) := by positivity
      have hreal : ((indexFinal k + 1 : ℕ) : ℝ) *
          (widthFinal k : ℝ) ^ 2 ≤ (timeFinal k : ℝ) := by
        exact_mod_cast htimeBoundNat
      have hbound : (widthFinal k : ℝ) ^ 2 / (timeFinal k : ℝ) ≤
          1 / ((indexFinal k + 1 : ℕ) : ℝ) := by
        field_simp [ne_of_gt htimeK, ne_of_gt hindexK]
        nlinarith [hreal]
      exact hbound
    · have hrecip := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        hindexFinalTop
      simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using hrecip
  have hwindow : ∀ᶠ k : ℕ in atTop,
      (fun _ : ℕ => u) (widthFinal k) ≤ u ∧
        v ≤ (fun _ : ℕ => v) (widthFinal k) := by
    filter_upwards with k
    exact ⟨le_rfl, le_rfl⟩
  have hprobLower :=
    eventually_horizontalTubeEndpointWindowProbability_ge_exp_of_centeredSecondMoment
      hν hsigma htimeFinalStrict htimeFinalPos hwidthFinalRealTop hwidthSq
      (v₁ := fun _ : ℕ => u) (v₂ := fun _ : ℕ => v)
      ha haOne hu huv hv hwindow hd
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hprobLower
  have hgood := hK K le_rfl
  have hbadK := hrawFail (indexFinal K)
  have hgood' : ENNReal.ofReal (Real.exp
      (-d * (horizonFinal K : ℝ) / (widthFinal K : ℝ) ^ 2)) ≤
        horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
          (widthFinal K : ℝ) (horizonFinal K) u v := by
    simpa [widthFinal, horizonFinal, timeFinal, Function.comp_def, timeRaw,
      indexFinal, Nat.add_sub_cancel_right] using hgood
  exact (not_lt_of_ge hgood') hbadK

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
