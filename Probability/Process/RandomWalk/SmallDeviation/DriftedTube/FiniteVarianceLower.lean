/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.FromIncrementLaw.HorizontalTube

/-!
# Finite-variance lower bounds in a tilted tube

The public objects and theorems in this file are:

- `eventually_horizontalTubeEndpointWindowProbability_ge_exp_of_centeredSecondMoment`:
  if S_j is centered with variance σ², its tube width Δ_n tends to infinity,
  Δ_n²/t_n tends to zero, and the endpoint fractions v₁(Δ_n), v₂(Δ_n)
  eventually contain some fixed interval [u,v] with 0<u<v<1, then for every
  d>π²σ²/2 and all sufficiently large n,
  P(−aΔ_n ≤ S_j ≤ (1−a)Δ_n,
    (v₁(Δ_n)−a)Δ_n ≤ S_{t_n−1} ≤ (v₂(Δ_n)−a)Δ_n)
    ≥ exp(−d(t_n−1)/Δ_n²).
- `exists_eventually_horizontalTubeEndpointWindowProbability_ge_exp_uniform`:
  for fixed 0<a<1 and 0<u<v<1, there are uniform width and time-ratio
  thresholds above which the same exponential lower bound holds for every
  integer width and horizon. This is the uniform block estimate used in the
  staircase part of Wang Yiyang, Chapter 3, Lemma 3.5.

- `staircaseBinLower`, `staircaseBinUpper`, and `staircaseBinWidth` encode
  $b_l=-\frac23+\frac{l}{3m}$,
  $b_{l+1}=b_l+\frac1{3m}$, and $w=1-\frac1{3m}$.
- `exists_staircaseBin_covering_relativeOffset` proves that every
  $r/\Delta\in[-\frac23,-\frac13]$ belongs to one of the $m$ spatial bins
  $[b_l,b_{l+1}]$.
- `relativeHorizontalTubeEndpointWindowEvent` is
  $\{r\le S_j\le r+D\ (1\le j\le n),\ S_n\in
  [r+v_1D,r+v_2D]\}$.
- `horizontalTubeEndpointWindowEvent_subset_relativeHorizontalTubeEndpointWindowEvent`
  proves that the common narrowed event on $[b_{l+1}D,(b_l+1)D]$, with
  terminal interval $[(b_{l+1}+v_1)D,(b_l+v_2)D]$, is contained in the
  target event whenever $b_lD\le r\le b_{l+1}D$. This is the common-event
  step in the staircase argument of Wang Yiyang, Chapter 3, Lemma 3.5.
- `exists_staircaseBin_commonEvent_subset_relativeTube` combines the bin
  cover and this inclusion: every relative starting point in
  $[-2/3,-1/3]$ admits a common narrowed-tube event contained in its target
  tube and endpoint-window event.
- `relativeLowerEdge_mem_staircaseRange_of_centerWindow` derives
  $(-y+r)/D\in[-2/3,-1/3]$ from the paper's central window
  $y\in[r+D/3,r+2D/3]$; `exists_staircaseBin_commonEvent_subset_centerWindow`
  then selects the common event for every point in that window.

This is the exponential form of Wang Yiyang, *Asymptotic speed of the
$N$-branching random walk with infinite offspring*, Chapter 3, Lemma 3.1(ii),
whose rate input is Mogul'skii, "Small Deviations in a Space of Trajectories,"
Theorem 3, Section 4, p. 764 (English translation, *Theory of Probability
and Its Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081).
The staircase-bin definitions and common-event inclusion formalize the
corresponding part of Wang Yiyang, *Asymptotic speed of the $N$-branching
random walk with infinite offspring*, Chapter 3, Lemma 3.5.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The endpoint-window rate from Wang Yiyang, *Asymptotic speed of the
$N$-branching random walk with infinite offspring*, Chapter 3, Lemma 3.1(ii),
implies this uniform exponential lower bound along any increasing sequence
of integer tube widths. The endpoint fractions may vary with the width as
long as they eventually contain one fixed interval strictly inside the tube.
-/
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
sequential endpoint-window rate in Wang Yiyang, *Asymptotic speed of the
$N$-branching random walk with infinite offspring*, Chapter 3, Lemma 3.1(ii).
The endpoint interval is the fixed interval `[u,v]`; this is the block
estimate used after narrowing each staircase tube in the proof of Chapter 3,
Lemma 3.5. The rate input is Mogul'skii, "Small Deviations in a Space of
Trajectories," Theorem 3, Section 4, p. 764 (DOI 10.1137/1119081). -/
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
  have hwidthTimeTop : Tendsto (fun k => widthRaw (ψ k)) atTop atTop :=
    hwidthRawTop.comp hψ.tendsto_atTop
  obtain ⟨φ, hφ, hwidthFinalStrict⟩ :=
    strictMono_subseq_of_tendsto_atTop hwidthTimeTop
  let indexFinal : ℕ → ℕ := fun k => ψ (φ k)
  let widthFinal : ℕ → ℕ := fun k => widthRaw (indexFinal k)
  let horizonFinal : ℕ → ℕ := fun k => horizonRaw (indexFinal k)
  let timeFinal : ℕ → ℕ := fun k => timeRaw (indexFinal k)
  have hindexFinalTop : Tendsto indexFinal atTop atTop := by
    simpa [indexFinal, Function.comp_def] using
      hψ.tendsto_atTop.comp hφ.tendsto_atTop
  have hwidthFinalTop : Tendsto widthFinal atTop atTop :=
    hwidthRawTop.comp hindexFinalTop
  have hwidthFinalRealTop : Tendsto (fun k => (widthFinal k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthFinalTop
  have htimeFinalStrict : StrictMono timeFinal := by
    simpa [timeFinal, indexFinal, Function.comp_def] using
      htimeRawStrict.comp hφ
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

/-- The lower endpoint of the l-th spatial bin in the staircase
construction of Wang Yiyang, Chapter 3, proof of Lemma 3.5. -/
noncomputable def staircaseBinLower (m l : ℕ) : ℝ :=
  -(2 : ℝ) / 3 + (l : ℝ) / (3 * (m : ℝ))

/-- The upper endpoint of the l-th spatial bin in the staircase
construction of Wang Yiyang, Chapter 3, proof of Lemma 3.5. -/
noncomputable def staircaseBinUpper (m l : ℕ) : ℝ :=
  staircaseBinLower m l + 1 / (3 * (m : ℝ))

/-- The width factor of the common narrowed tube in one staircase bin. -/
noncomputable def staircaseBinWidth (m : ℕ) : ℝ :=
  1 - 1 / (3 * (m : ℝ))

/-- The horizontal-tube parameter whose lower edge is b_{l+1} and whose
width is 1 - 1/(3m). -/
noncomputable def staircaseBinTubeParameter (m l : ℕ) : ℝ :=
  -staircaseBinUpper m l / staircaseBinWidth m

/-- The lower endpoint fraction of the common terminal interval in the
narrowed staircase tube. -/
noncomputable def staircaseBinEndpointLowerFraction (m : ℕ) (v₁ : ℝ) : ℝ :=
  v₁ / staircaseBinWidth m

/-- The upper endpoint fraction of the common terminal interval in the
narrowed staircase tube. -/
noncomputable def staircaseBinEndpointUpperFraction (m : ℕ) (v₂ : ℝ) : ℝ :=
  (v₂ - 1 / (3 * (m : ℝ))) / staircaseBinWidth m

/-- The bins in the staircase construction of Wang Yiyang, Chapter 3,
proof of Lemma 3.5, cover the full range of normalized relative starting
positions used there: for every $r/\Delta\in[-2/3,-1/3]$, there is
$0\le l<m$ with $b_l\le r/\Delta\le b_{l+1}$. -/
theorem exists_staircaseBin_covering_relativeOffset
    {m : ℕ} (hm : 2 ≤ m) {offset : ℝ}
    (hoffsetLower : -(2 : ℝ) / 3 ≤ offset)
    (hoffsetUpper : offset ≤ -(1 : ℝ) / 3) :
    ∃ l : ℕ, l < m ∧ staircaseBinLower m l ≤ offset ∧
      offset ≤ staircaseBinUpper m l := by
  let scale : ℝ := 3 * (m : ℝ)
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  let x : ℝ := (offset + (2 : ℝ) / 3) * scale
  have hxLower : 0 ≤ x := by
    dsimp [x]
    apply mul_nonneg _ hscale.le
    linarith [hoffsetLower]
  have hxUpper : x ≤ (m : ℝ) := by
    calc
      x = (offset + (2 : ℝ) / 3) * scale := rfl
      _ ≤ ((1 : ℝ) / 3) * scale :=
        mul_le_mul_of_nonneg_right (by linarith [hoffsetUpper]) hscale.le
      _ = (m : ℝ) := by dsimp [scale]; ring
  let q : ℕ := ⌊x⌋₊
  have hqLower : (q : ℝ) ≤ x := by
    exact Nat.floor_le hxLower
  have hxFloor : x < (q : ℝ) + 1 := by
    exact Nat.lt_floor_add_one x
  let l : ℕ := min q (m - 1)
  have hl : l < m := by
    dsimp [l]
    have hm' : m - 1 < m := by omega
    exact lt_of_le_of_lt (Nat.min_le_right _ _) hm'
  have hlLower : (l : ℝ) ≤ x := by
    dsimp [l]
    exact le_trans (by exact_mod_cast (Nat.min_le_left q (m - 1))) hqLower
  have hlUpper : x ≤ (l : ℝ) + 1 := by
    by_cases hq : q < m
    · have hlEq : l = q := by
        dsimp [l]
        apply Nat.min_eq_left
        omega
      rw [hlEq]
      exact le_of_lt hxFloor
    · have hmq : m ≤ q := by omega
      have hqle : (q : ℝ) ≤ (m : ℝ) := by
        exact le_trans hqLower hxUpper
      have hxeq : x = (m : ℝ) := by
        exact le_antisymm hxUpper (le_trans (by exact_mod_cast hmq : (m : ℝ) ≤ (q : ℝ)) hqLower)
      have hqeq : q = m := by
        exact_mod_cast (le_antisymm hqle (by exact_mod_cast hmq : (m : ℝ) ≤ (q : ℝ)))
      have hleq : l = m - 1 := by
        dsimp [l]
        rw [hqeq]
        exact Nat.min_eq_right (by omega)
      rw [hxeq, hleq]
      norm_cast
      omega
  have hoffsetForm : offset = -(2 : ℝ) / 3 + x / scale := by
    dsimp [x]
    field_simp [ne_of_gt hscale]
    ring
  have hscaleDivLower : (l : ℝ) / scale ≤ x / scale :=
    div_le_div_of_nonneg_right hlLower hscale.le
  have hscaleDivUpper : x / scale ≤ ((l + 1 : ℕ) : ℝ) / scale := by
    apply div_le_div_of_nonneg_right _ hscale.le
    exact_mod_cast hlUpper
  refine ⟨l, hl, ?_, ?_⟩
  · change -(2 : ℝ) / 3 + (l : ℝ) / scale ≤ offset
    rw [hoffsetForm]
    linarith [hscaleDivLower]
  · change offset ≤ -(2 : ℝ) / 3 + (l : ℝ) / scale + 1 / scale
    rw [hoffsetForm]
    have hsuccessor : ((l + 1 : ℕ) : ℝ) / scale =
        (l : ℝ) / scale + 1 / scale := by
      push_cast
      ring
    linarith [hscaleDivUpper, hsuccessor]

/-- A horizontal tube with a specified lower edge and endpoint window. -/
def relativeHorizontalTubeEndpointWindowEvent (lower width : ℝ)
    (horizon : ℕ) (v₁ v₂ : ℝ) : Set (ℕ → ℝ) :=
  {increment | (∀ k : Fin horizon,
      lower ≤ AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment ≤ lower + width) ∧
    AdditivePath.displacement horizon increment ∈
      Set.Icc (lower + v₁ * width) (lower + v₂ * width)}

/-- The central window $[r+D/3,r+2D/3]$ makes the relative lower edge
$r-y$ lie in $[-2D/3,-D/3]$, as used for each block in Wang Yiyang,
Chapter 3, proof of Lemma 3.5. -/
theorem relativeLowerEdge_mem_staircaseRange_of_centerWindow
    {width lowerEdge position : ℝ} (hwidth : 0 < width)
    (hposition : position ∈
      Set.Icc (lowerEdge + width / 3) (lowerEdge + 2 * width / 3)) :
    (lowerEdge - position) / width ∈
      Set.Icc (-(2 : ℝ) / 3) (-(1 : ℝ) / 3) := by
  rcases Set.mem_Icc.mp hposition with ⟨hpositionLower, hpositionUpper⟩
  rw [Set.mem_Icc]
  have hleft : (-(2 : ℝ) / 3) * width ≤ lowerEdge - position := by
    nlinarith [hpositionUpper]
  have hright : lowerEdge - position ≤ (-(1 : ℝ) / 3) * width := by
    nlinarith [hpositionLower]
  constructor
  · calc
      -(2 : ℝ) / 3 = ((-(2 : ℝ) / 3) * width) / width := by
        field_simp [ne_of_gt hwidth]
      _ ≤ (lowerEdge - position) / width :=
        (div_le_div_iff_of_pos_right hwidth).2 hleft
  · calc
      (lowerEdge - position) / width ≤
          ((-(1 : ℝ) / 3) * width) / width :=
        (div_le_div_iff_of_pos_right hwidth).2 hright
      _ = -(1 : ℝ) / 3 := by field_simp [ne_of_gt hwidth]

/-- For a starting offset in one spatial bin, the common narrowed-tube
event is contained in the desired horizontal tube and terminal window.
This is the deterministic bin-inclusion step in the staircase proof of
Wang Yiyang, Asymptotic speed of the N-branching random walk with infinite
offspring, Chapter 3, Lemma 3.5. -/
theorem horizontalTubeEndpointWindowEvent_subset_relativeHorizontalTubeEndpointWindowEvent
    {m l horizon : ℕ} {width v₁ v₂ lower : ℝ}
    (hm : 2 ≤ m)
    (hlower : staircaseBinLower m l * width ≤ lower)
    (hupper : lower ≤ staircaseBinUpper m l * width) :
    horizontalTubeEndpointWindowEvent
        (staircaseBinTubeParameter m l)
        (staircaseBinWidth m * width) horizon
        (staircaseBinEndpointLowerFraction m v₁)
        (staircaseBinEndpointUpperFraction m v₂) ⊆
      relativeHorizontalTubeEndpointWindowEvent lower width horizon v₁ v₂ := by
  have hbinWidth : 0 < staircaseBinWidth m := by
    dsimp [staircaseBinWidth]
    have hm' : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hdenom : 0 < 3 * (m : ℝ) := by positivity
    have hfrac : 1 / (3 * (m : ℝ)) < 1 := by
      rw [div_lt_one hdenom]
      have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      nlinarith [hmR]
    linarith
  have hdelta : 1 / (3 * (m : ℝ)) + staircaseBinWidth m = 1 := by
    dsimp [staircaseBinWidth]
    ring
  have hbinAdjacent : staircaseBinUpper m l =
      staircaseBinLower m l + 1 / (3 * (m : ℝ)) := rfl
  have hparameterWidth :
      staircaseBinTubeParameter m l * staircaseBinWidth m =
        -staircaseBinUpper m l := by
    dsimp [staircaseBinTubeParameter]
    field_simp [ne_of_gt hbinWidth]
  have hnegativeParameterWidth :
      -staircaseBinTubeParameter m l * staircaseBinWidth m =
        staircaseBinUpper m l := by
    calc
      -staircaseBinTubeParameter m l * staircaseBinWidth m =
          -(staircaseBinTubeParameter m l *
            staircaseBinWidth m) := by ring
      _ = staircaseBinUpper m l := by rw [hparameterWidth]; ring
  have hpositiveParameterWidth :
      (1 - staircaseBinTubeParameter m l) * staircaseBinWidth m =
        staircaseBinWidth m + staircaseBinUpper m l := by
    calc
      (1 - staircaseBinTubeParameter m l) * staircaseBinWidth m =
          staircaseBinWidth m -
            staircaseBinTubeParameter m l * staircaseBinWidth m := by ring
      _ = staircaseBinWidth m + staircaseBinUpper m l := by
        rw [hparameterWidth]
        ring
  have hwidthDelta :
      staircaseBinWidth m + 1 / (3 * (m : ℝ)) = 1 := by
    rw [add_comm]
    exact hdelta
  have hleft :
      -staircaseBinTubeParameter m l *
          (staircaseBinWidth m * width) = staircaseBinUpper m l * width := by
    calc
      -staircaseBinTubeParameter m l *
          (staircaseBinWidth m * width) =
          (-staircaseBinTubeParameter m l *
            staircaseBinWidth m) * width := by ring
      _ = staircaseBinUpper m l * width := by rw [hnegativeParameterWidth]
  have hright :
      (1 - staircaseBinTubeParameter m l) *
          (staircaseBinWidth m * width) =
        (staircaseBinLower m l + 1) * width := by
    calc
      (1 - staircaseBinTubeParameter m l) *
          (staircaseBinWidth m * width) =
          ((1 - staircaseBinTubeParameter m l) *
            staircaseBinWidth m) * width := by ring
      _ = (staircaseBinWidth m +
          staircaseBinUpper m l) * width := by rw [hpositiveParameterWidth]
      _ = (staircaseBinLower m l + 1) * width := by
        rw [hbinAdjacent]
        congr 1
        dsimp [staircaseBinWidth] at hdelta
        dsimp [staircaseBinWidth]
        linarith [hdelta]
  have hendpointLowerWidth :
      staircaseBinEndpointLowerFraction m v₁ *
          staircaseBinWidth m = v₁ := by
    dsimp [staircaseBinEndpointLowerFraction]
    field_simp [ne_of_gt hbinWidth]
  have hendpointUpperWidth :
      staircaseBinEndpointUpperFraction m v₂ *
          staircaseBinWidth m =
        v₂ - 1 / (3 * (m : ℝ)) := by
    dsimp [staircaseBinEndpointUpperFraction]
    field_simp [ne_of_gt hbinWidth]
  have hterminalLower :
      (staircaseBinEndpointLowerFraction m v₁ -
          staircaseBinTubeParameter m l) *
          (staircaseBinWidth m * width) =
        (staircaseBinUpper m l + v₁) * width := by
    have hwidthExpr :
        (staircaseBinEndpointLowerFraction m v₁ -
          staircaseBinTubeParameter m l) * staircaseBinWidth m =
            v₁ + staircaseBinUpper m l := by
      calc
        _ = staircaseBinEndpointLowerFraction m v₁ *
              staircaseBinWidth m -
            staircaseBinTubeParameter m l * staircaseBinWidth m := by ring
        _ = v₁ + staircaseBinUpper m l := by
          rw [hendpointLowerWidth, hparameterWidth]
          ring
    calc
      (staircaseBinEndpointLowerFraction m v₁ -
          staircaseBinTubeParameter m l) *
          (staircaseBinWidth m * width) =
          ((staircaseBinEndpointLowerFraction m v₁ -
            staircaseBinTubeParameter m l) *
            staircaseBinWidth m) * width := by ring
      _ = (v₁ + staircaseBinUpper m l) * width := by rw [hwidthExpr]
      _ = (staircaseBinUpper m l + v₁) * width := by ring
  have hterminalUpper :
      (staircaseBinEndpointUpperFraction m v₂ -
          staircaseBinTubeParameter m l) *
          (staircaseBinWidth m * width) =
        (staircaseBinLower m l + v₂) * width := by
    have hwidthExpr :
        (staircaseBinEndpointUpperFraction m v₂ -
          staircaseBinTubeParameter m l) * staircaseBinWidth m =
            staircaseBinLower m l + v₂ := by
      calc
        _ = staircaseBinEndpointUpperFraction m v₂ *
              staircaseBinWidth m -
            staircaseBinTubeParameter m l * staircaseBinWidth m := by ring
        _ = (v₂ - 1 / (3 * (m : ℝ))) +
              staircaseBinUpper m l := by
          rw [hendpointUpperWidth, hparameterWidth]
          ring
        _ = staircaseBinLower m l + v₂ := by rw [hbinAdjacent]; ring
    calc
      (staircaseBinEndpointUpperFraction m v₂ -
          staircaseBinTubeParameter m l) *
          (staircaseBinWidth m * width) =
          ((staircaseBinEndpointUpperFraction m v₂ -
            staircaseBinTubeParameter m l) *
            staircaseBinWidth m) * width := by ring
      _ = (staircaseBinLower m l + v₂) * width := by rw [hwidthExpr]
  intro increment hevent
  change InHorizontalTube (staircaseBinTubeParameter m l)
      (staircaseBinWidth m * width) horizon increment ∧
    AdditivePath.displacement horizon increment ∈
      Set.Icc
        ((staircaseBinEndpointLowerFraction m v₁ -
            staircaseBinTubeParameter m l) *
            (staircaseBinWidth m * width))
        ((staircaseBinEndpointUpperFraction m v₂ -
            staircaseBinTubeParameter m l) *
            (staircaseBinWidth m * width)) at hevent
  rcases hevent with ⟨htube, hend⟩
  refine ⟨?_, ?_⟩
  · intro k
    have hk := htube k
    rw [hleft, hright] at hk
    constructor
    · exact le_trans hupper hk.1
    · have htop : (staircaseBinLower m l + 1) * width ≤ lower + width := by
        have hrewrite : (staircaseBinLower m l + 1) * width =
            staircaseBinLower m l * width + width := by ring
        rw [hrewrite]
        linarith [hlower]
      exact le_trans hk.2 htop
  · rw [hterminalLower, hterminalUpper] at hend
    rcases Set.mem_Icc.mp hend with ⟨hendLower, hendUpper⟩
    rw [Set.mem_Icc]
    constructor
    · nlinarith [hupper, hendLower]
    · nlinarith [hlower, hendUpper]

/-- For every positive tube width and every relative lower edge in
$[-2/3,-1/3]$, one of the staircase bins supplies a common narrowed-tube
event contained in the target tube and endpoint window. This packages the
bin selection and event inclusion used in Wang Yiyang, Chapter 3, proof of
Lemma 3.5. -/
theorem exists_staircaseBin_commonEvent_subset_relativeTube
    {m horizon : ℕ} {width v₁ v₂ lower : ℝ}
    (hm : 2 ≤ m) (hwidth : 0 < width)
    (hrelativeLower : -(2 : ℝ) / 3 ≤ lower / width)
    (hrelativeUpper : lower / width ≤ -(1 : ℝ) / 3) :
    ∃ l : ℕ, l < m ∧
      horizontalTubeEndpointWindowEvent
          (staircaseBinTubeParameter m l)
          (staircaseBinWidth m * width) horizon
          (staircaseBinEndpointLowerFraction m v₁)
          (staircaseBinEndpointUpperFraction m v₂) ⊆
        relativeHorizontalTubeEndpointWindowEvent lower width horizon v₁ v₂ := by
  obtain ⟨l, hl, hbinLower, hbinUpper⟩ :=
    exists_staircaseBin_covering_relativeOffset hm hrelativeLower hrelativeUpper
  have hlower : staircaseBinLower m l * width ≤ lower := by
    calc
      staircaseBinLower m l * width ≤ (lower / width) * width :=
        mul_le_mul_of_nonneg_right hbinLower hwidth.le
      _ = lower := by field_simp [ne_of_gt hwidth]
  have hupper : lower ≤ staircaseBinUpper m l * width := by
    calc
      lower = (lower / width) * width := by field_simp [ne_of_gt hwidth]
      _ ≤ staircaseBinUpper m l * width :=
        mul_le_mul_of_nonneg_right hbinUpper hwidth.le
  exact ⟨l, hl,
    horizontalTubeEndpointWindowEvent_subset_relativeHorizontalTubeEndpointWindowEvent
      hm hlower hupper⟩

/-- At every point of the central window used in the staircase proof, a
common narrowed-tube event is contained in the corresponding target event.
This combines the central-window geometry with the bin selection in Wang
Yiyang, Chapter 3, proof of Lemma 3.5. -/
theorem exists_staircaseBin_commonEvent_subset_centerWindow
    {m horizon : ℕ} {width v₁ v₂ lowerEdge position : ℝ}
    (hm : 2 ≤ m) (hwidth : 0 < width)
    (hposition : position ∈
      Set.Icc (lowerEdge + width / 3) (lowerEdge + 2 * width / 3)) :
    ∃ l : ℕ, l < m ∧
      horizontalTubeEndpointWindowEvent
          (staircaseBinTubeParameter m l)
          (staircaseBinWidth m * width) horizon
          (staircaseBinEndpointLowerFraction m v₁)
          (staircaseBinEndpointUpperFraction m v₂) ⊆
        relativeHorizontalTubeEndpointWindowEvent
          (lowerEdge - position) width horizon v₁ v₂ := by
  have hrelative := relativeLowerEdge_mem_staircaseRange_of_centerWindow
    hwidth hposition
  exact exists_staircaseBin_commonEvent_subset_relativeTube hm hwidth
    hrelative.1 hrelative.2

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
