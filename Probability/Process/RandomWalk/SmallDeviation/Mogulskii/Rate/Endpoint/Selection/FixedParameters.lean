/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Rate.Endpoint.Windows
public import Analysis.Asymptotics.Scale.BlockScale

/-!
# Explicit floor grids for the normal-domain lower bound

For a spatial width $x_n$, let $a_n$, $s_n$, and $w_n$ be the lattice
half-scale, return spacing, and terminal-window radius. The public
declarations are:

- `alphaTwoLatticeScale`, `alphaTwoEndpointSpacing`, and
  `alphaTwoEndpointWindowRadius`:
  $a_n=\lfloor qx_n/8\rfloor_++3$,
  $s_n=\lfloor 8pa_n\rfloor_++1$, and $w_n=s_n+1$, where
  $\lfloor\cdot\rfloor_+$ is the natural-number floor.
- `tendsto_eight_alphaTwoLatticeScale_div`:
  $8a_n/x_n\to q$.
- `tendsto_alphaTwoEndpointSpacing_div_eightLattice` and
  `tendsto_alphaTwoEndpointWindowMinusOne_div_eightLattice`:
  $s_n/(8a_n)\to p$ and $(w_n-1)/(8a_n)\to p$.
- `one_div_constant_mul_log_toReal_le_liminf_scaledLog_horizontalTubeProbability_of_floorEndpointWindows`:
  with fixed admissible spectral parameters and return probability $A>0$,
  $(1/c)\log A\le\liminf_n(x_n^2/n)\log\mathbb P(T_n)$, together with
  eventual positivity and a lower bound for this logarithmic rate.
The floor choices keep the finite spectral and endpoint-window hypotheses
valid. This is the fixed-parameter part of an internal spectral route to the
horizontal-tube constant in Mogul'skii, *Small Deviations in a Space of
Trajectories*, Theorem 3, Section 4; Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), Chapter 3, Lemma 3.1(i), uses that constant.


The original bibliography is A. A. Mogul'skii, “Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations in a Space of Trajectories,” *Theory of Probability and Its Applications* 19(1) (1975), 726--736, DOI 10.1137/1119081. -/

open Filter MeasureTheory ProbabilityTheory Topology
open Asymptotics

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The integer spectral half-scale approximating a fraction `q` of the
outer horizontal-tube width. The additive three-site offset makes the finite
spectral hypotheses valid even at the first indices. -/
noncomputable def alphaTwoLatticeScale (q : ℝ) (scale : ℕ → ℝ) : ℕ → ℕ :=
  fun n => Asymptotics.floorBlockLength (fun k => q * scale k / 8) n + 3

/-- The return-mesh spacing, rounded with a one-site offset so it is positive
at every index. -/
noncomputable def alphaTwoEndpointSpacing (p : ℝ) (q : ℝ)
    (scale : ℕ → ℝ) : ℕ → ℕ :=
  fun n => Asymptotics.floorBlockLength
    (fun k => p * (8 * (alphaTwoLatticeScale q scale k : ℝ))) n + 1

/-- The endpoint-window half-width is one lattice site wider than the mesh
spacing. In particular it is always positive and at most twice the spacing. -/
noncomputable def alphaTwoEndpointWindowRadius (p : ℝ) (q : ℝ)
    (scale : ℕ → ℝ) : ℕ → ℕ :=
  fun n => alphaTwoEndpointSpacing p q scale n + 1

private lemma tendsto_scale_atTop {scale : ℕ → ℝ}
    (hscale : IsMogulskiiScale scale) : Tendsto scale atTop atTop := by
  change IsSmallDeviationScale scale (fun n => Real.sqrt n) at hscale
  exact IsSmallDeviationScale.tendsto_atTop hscale

private lemma tendsto_latticeArgument_atTop {scale : ℕ → ℝ}
    (hscale : IsMogulskiiScale scale) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n => q * scale n / 8) atTop atTop := by
  have hs := tendsto_scale_atTop hscale
  have h' := hs.const_mul_atTop (by positivity : 0 < q / 8)
  convert h' using 1
  · ext n
    ring

/-- The rounded lattice scale has the prescribed asymptotic proportion. -/
theorem tendsto_eight_alphaTwoLatticeScale_div {scale : ℕ → ℝ}
    (hscale : IsMogulskiiScale scale) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n => ((8 * alphaTwoLatticeScale q scale n : ℕ) : ℝ) /
      scale n) atTop (nhds q) := by
  have hs := tendsto_scale_atTop hscale
  have harg := tendsto_latticeArgument_atTop hscale hq
  have hargRatio : Tendsto
      (fun n => (q * scale n / 8) / scale n) atTop (nhds (q / 8)) := by
    have heq : (fun n => (q * scale n / 8) / scale n) =ᶠ[atTop]
        fun _ => q / 8 := by
      filter_upwards [IsMogulskiiScale.eventually_pos hscale] with n hn
      field_simp [hn.ne']
    exact tendsto_const_nhds.congr' heq.symm
  have hrounded := Asymptotics.tendsto_floorBlockLength_add_nat_div_of_argument_ratio
    3 harg hs hargRatio
  have hresult := hrounded.const_mul 8
  convert hresult using 1
  · ext n
    simp [alphaTwoLatticeScale, Asymptotics.floorBlockLength]
    ring_nf
  · field_simp

private lemma tendsto_latticeScale_atTop {scale : ℕ → ℝ}
    (hscale : IsMogulskiiScale scale) {q : ℝ} (hq : 0 < q) :
    Tendsto (alphaTwoLatticeScale q scale) atTop atTop := by
  have hfloor := Asymptotics.tendsto_floorBlockLength_atTop
    (tendsto_latticeArgument_atTop hscale hq)
  rw [tendsto_atTop]
  intro b
  filter_upwards [hfloor.eventually (eventually_ge_atTop b)] with n hn
  dsimp [alphaTwoLatticeScale]
  omega

/-- The mesh spacing has the same positive asymptotic proportion `p` as the
endpoint-window radius minus one. -/
theorem tendsto_alphaTwoEndpointSpacing_div_eightLattice {scale : ℕ → ℝ}
    (hscale : IsMogulskiiScale scale) {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) :
    Tendsto (fun n => (alphaTwoEndpointSpacing p q scale n : ℝ) /
      (8 * (alphaTwoLatticeScale q scale n : ℝ))) atTop (nhds p) := by
  let width : ℕ → ℝ := fun n => 8 * (alphaTwoLatticeScale q scale n : ℝ)
  let argument : ℕ → ℝ := fun n => p * width n
  have hwidthTop : Tendsto width atTop atTop := by
    have hm := tendsto_latticeScale_atTop hscale hq
    have hcast : Tendsto (fun n => (alphaTwoLatticeScale q scale n : ℝ))
        atTop atTop := tendsto_natCast_atTop_atTop.comp hm
    have hmul := hcast.const_mul_atTop (by norm_num : (0 : ℝ) < 8)
    simpa [width] using hmul
  have hargTop : Tendsto argument atTop atTop := by
    have h := hwidthTop.const_mul_atTop hp
    simpa [argument, mul_comm] using h
  have hratio : Tendsto (fun n => argument n / width n)
      atTop (nhds p) := by
    have heq : (fun n => argument n / width n) =ᶠ[atTop]
        fun _ => p := by
      filter_upwards [hwidthTop.eventually_gt_atTop 0] with n hn
      simp [argument, hn.ne']
    exact tendsto_const_nhds.congr' heq.symm
  have hrounded :=
    Asymptotics.tendsto_floorBlockLength_add_nat_div_of_argument_ratio
      1 hargTop hwidthTop hratio
  convert hrounded using 1
  · ext n
    simp [alphaTwoEndpointSpacing, argument, width,
      Asymptotics.floorBlockLength]

theorem tendsto_alphaTwoEndpointWindowMinusOne_div_eightLattice {scale : ℕ → ℝ}
    (hscale : IsMogulskiiScale scale) {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) :
    Tendsto (fun n =>
      ((alphaTwoEndpointWindowRadius p q scale n - 1 : ℕ) : ℝ) /
        (8 * (alphaTwoLatticeScale q scale n : ℝ))) atTop (nhds p) := by
  have hspacing := tendsto_alphaTwoEndpointSpacing_div_eightLattice
    hscale hq hp
  have heq : (fun n =>
      ((alphaTwoEndpointWindowRadius p q scale n - 1 : ℕ) : ℝ) /
        (8 * (alphaTwoLatticeScale q scale n : ℝ))) =ᶠ[atTop]
      fun n => (alphaTwoEndpointSpacing p q scale n : ℝ) /
        (8 * (alphaTwoLatticeScale q scale n : ℝ)) := by
    filter_upwards [] with n
    simp [alphaTwoEndpointWindowRadius]
  exact hspacing.congr' heq.symm

/-- The explicit floor spacing and window satisfy the finite spectral fit
condition at every index, including the initial indices. -/
private lemma alphaTwoEndpointBands_fit (scale : ℕ → ℝ) {q p : ℝ}
    (hp : 0 < p) (hpSmall : p < 1 / 32) (n : ℕ) :
    3 * alphaTwoEndpointSpacing p q scale n +
        alphaTwoEndpointWindowRadius p q scale n ≤
      2 * alphaTwoLatticeScale q scale n := by
  let m := alphaTwoLatticeScale q scale n
  let k := Asymptotics.floorBlockLength
    (fun j => p * (8 * (alphaTwoLatticeScale q scale j : ℝ))) n
  change 3 * (k + 1) + (k + 2) ≤ 2 * m
  have hm : 3 ≤ m := by
    dsimp [m, alphaTwoLatticeScale]
    omega
  have hfloorLe : (k : ℝ) ≤ p * (8 * (m : ℝ)) := by
    dsimp [k, Asymptotics.floorBlockLength]
    exact Nat.floor_le (by positivity)
  by_cases hx : p * (8 * (m : ℝ)) < 1
  · have hklt : (k : ℝ) < 1 := hfloorLe.trans_lt hx
    have hkNat : k < 1 := by exact_mod_cast hklt
    have hkZero : k = 0 := by omega
    omega
  · have hxge : 1 ≤ p * (8 * (m : ℝ)) := le_of_not_gt hx
    have hxp : p * (8 * (m : ℝ)) < (m : ℝ) / 4 := by
      calc
        p * (8 * (m : ℝ)) < (1 / 32 : ℝ) * (8 * (m : ℝ)) :=
          mul_lt_mul_of_pos_right hpSmall (by positivity)
        _ = (m : ℝ) / 4 := by ring
    have hmFive : 5 ≤ m := by
      by_contra hnot
      have hmFour : (m : ℝ) ≤ 4 := by exact_mod_cast (show m ≤ 4 by omega)
      nlinarith [hxge, hxp, hmFour]
    have hmFiveReal : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmFive
    have hrealStrict : 3 * ((k : ℝ) + 1) + ((k : ℝ) + 2) < 2 * (m : ℝ) := by
      calc
        3 * ((k : ℝ) + 1) + ((k : ℝ) + 2) = 4 * (k : ℝ) + 5 := by ring
        _ ≤ 4 * (p * (8 * (m : ℝ))) + 5 := by nlinarith [hfloorLe]
        _ < (m : ℝ) + 5 := by nlinarith [hxp]
        _ ≤ 2 * (m : ℝ) := by nlinarith [hmFiveReal]
    have hreal : 3 * ((k : ℝ) + 1) + ((k : ℝ) + 2) ≤ 2 * (m : ℝ) :=
      le_of_lt hrealStrict
    exact_mod_cast hreal

private lemma tendsto_sqrtBlock_div_width_of_diffusiveRatio
    {length width : ℕ → ℕ} {c : ℝ}
    (hratio : Tendsto (fun n => (length n : ℝ) / (width n : ℝ) ^ 2)
      atTop (nhds c)) :
    Tendsto (fun n => Real.sqrt (length n : ℝ) / (width n : ℝ))
      atTop (nhds (Real.sqrt c)) := by
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  apply hsqrt.congr'
  filter_upwards [] with n
  change Real.sqrt ((length n : ℝ) / (width n : ℝ) ^ 2) = _
  rw [Real.sqrt_div (Nat.cast_nonneg (length n)),
    Real.sqrt_sq (Nat.cast_nonneg (width n))]

/-- Fixed-parameter `α = 2` horizontal lower bound with the actual floor
choices of lattice scale, endpoint spacing, and endpoint-window radius. The
strict hypotheses are precisely the spectral, Portmanteau, and outer-tube
slacks; their asymptotic selection is a separate real-variable step. -/
theorem one_div_constant_mul_log_toReal_le_liminf_scaledLog_horizontalTubeProbability_of_floorEndpointWindows
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {constant q p δ spectralLower applicationLower : ℝ}
    (hconstant : 0 < constant) (hq : 0 < q) (hp : 0 < p)
    (hpSmall : p < 1 / 32) (hδ : 0 < δ)
    (hsmallLimit : Real.exp ((constant / q ^ 2) * (-(Real.pi ^ 2) / 2)) <
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p) /
        (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p + 8))
    (hspectralLower : spectralLower <
      p * Real.exp ((constant / q ^ 2) * (-(Real.pi ^ 2) / 2)))
    (happlicationLower : 0 < applicationLower)
    (happlicationLowerOne : applicationLower ≤ 1)
    (happlicationBelow : applicationLower < spectralLower)
    (hreturnMargin : 3 * δ < p / Real.sqrt (constant / q ^ 2))
    (houterMargin :
      2 * ((1 / (2 * Real.sqrt (constant / q ^ 2)) + 3 * δ) +
        3 * (p / Real.sqrt (constant / q ^ 2)) +
        (p / Real.sqrt (constant / q ^ 2) + 3 * δ)) *
          Real.sqrt constant < 1) :
    ((1 / constant) * Real.log applicationLower ≤
      atTop.liminf (fun n => scale n ^ 2 / (n : ℝ) *
        Real.log (horizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal) ∧
      (∀ᶠ n in atTop, 0 < horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n) ∧
      Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => scale n ^ 2 / (n : ℝ) *
        Real.log (horizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal)) := by
  let blockLength : ℕ → ℕ := diffusiveBlockLength constant scale
  let time : ℕ → ℕ := fun n => max 1 (blockLength n)
  let latticeScale : ℕ → ℕ := alphaTwoLatticeScale q scale
  let spacing : ℕ → ℕ := alphaTwoEndpointSpacing p q scale
  let windowRadius : ℕ → ℕ := alphaTwoEndpointWindowRadius p q scale
  let widthNat : ℕ → ℕ := fun n => 8 * latticeScale n
  let width : ℕ → ℝ := fun n => (widthNat n : ℝ)
  let meshLimit : ℝ := p / Real.sqrt (constant / q ^ 2)
  let spectralRadiusLimit : ℝ := 1 / (2 * Real.sqrt (constant / q ^ 2))
  let spectralWindowLimit : ℝ := p / Real.sqrt (constant / q ^ 2)
  let closedRadius : ℝ := spectralRadiusLimit + δ
  let openRadius : ℝ := spectralRadiusLimit + 2 * δ
  let applicationRadius : ℝ := spectralRadiusLimit + 3 * δ
  let closedWindow : ℝ := spectralWindowLimit + δ
  let openWindow : ℝ := spectralWindowLimit + 2 * δ
  let applicationWindow : ℝ := spectralWindowLimit + 3 * δ

  have hc : 0 < constant / q ^ 2 := div_pos hconstant (sq_pos_of_pos hq)
  have hroot : 0 < Real.sqrt (constant / q ^ 2) := Real.sqrt_pos.2 hc
  have hblockLengthTop : Tendsto blockLength atTop atTop := by
    simpa [blockLength] using
      _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.tendsto_diffusiveBlockLength_atTop
        hscale hconstant
  have hblockLengthPos : ∀ᶠ n in atTop, 0 < blockLength n := by
    simpa [blockLength] using
      _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_diffusiveBlockLength_pos
        hscale hconstant
  have htimePos : ∀ n, 0 < time n := by
    intro n
    exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 (blockLength n))
  have htimeTop : Tendsto time atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hblockLengthTop.eventually (eventually_ge_atTop b)] with n hn
    exact le_trans hn (Nat.le_max_right 1 (blockLength n))
  have htimeEq : ∀ᶠ n in atTop, time n = blockLength n := by
    filter_upwards [hblockLengthPos] with n hn
    dsimp [time]
    exact Nat.max_eq_right (by omega)

  have hcountLimit : Tendsto
      (fun n => ((n / blockLength n + 1 : ℕ) : ℝ) *
        scale n ^ 2 / (n : ℝ)) atTop (nhds (1 / constant)) := by
    simpa [blockLength] using
      _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.tendsto_succ_completeBlockCount_mul_sq_div
        hscale hconstant

  have hlatticePos : ∀ n, 0 < latticeScale n := by
    intro n
    dsimp [latticeScale, alphaTwoLatticeScale]
    omega
  have hwindowLower : ∀ n, 2 ≤ windowRadius n := by
    intro n
    dsimp [windowRadius, alphaTwoEndpointWindowRadius,
      spacing, alphaTwoEndpointSpacing, Asymptotics.floorBlockLength]
    omega
  have hfitSpectral : ∀ n,
      3 * spacing n + windowRadius n ≤ 2 * latticeScale n := by
    intro n
    exact alphaTwoEndpointBands_fit scale hp hpSmall n

  have hwidthRatio : Tendsto (fun n => width n / scale n) atTop (nhds q) := by
    simpa [width, widthNat, latticeScale] using
      tendsto_eight_alphaTwoLatticeScale_div hscale hq
  have hwidthTop : Tendsto width atTop atTop := by
    have hscaleTop := tendsto_scale_atTop hscale
    rw [tendsto_atTop]
    intro b
    let b' : ℝ := max b 1
    have hlarge := hwidthRatio.eventually
      (eventually_gt_nhds (show q / 2 < q by linarith [hq]))
    have hscaleLarge := hscaleTop.eventually (eventually_ge_atTop (2 * b' / q))
    filter_upwards [hlarge, hscaleLarge] with n hratio hlarge
    have hscalePosN : 0 < scale n := lt_of_lt_of_le
      (by dsimp [b']; positivity) hlarge
    have : b ≤ width n := by
      have hratio' : q / 2 < width n / scale n := by simpa [width] using hratio
      have hmul : b' = (q / 2) * (2 * b' / q) := by field_simp [hq.ne']
      have hscaleLower : 2 * b' / q ≤ scale n := hlarge
      have hwidthLower : (q / 2) * scale n < width n :=
        (lt_div_iff₀ hscalePosN).mp hratio'
      have hb' : b ≤ b' := le_max_left _ _
      have hb'Lower : b' ≤ (q / 2) * scale n := by
        rw [hmul]
        exact mul_le_mul_of_nonneg_left hscaleLower (by positivity)
      exact hb'.trans (hb'Lower.trans hwidthLower.le)
    exact this

  have htimeScaleRatio : Tendsto (fun n => (time n : ℝ) / scale n ^ 2)
      atTop (nhds constant) := by
    have hbase :=
      _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.tendsto_diffusiveBlockLength_div_sq
        hscale hconstant
    apply hbase.congr'
    filter_upwards [htimeEq] with n hn
    simp [time, blockLength, hn]

  have hwidthSq : Tendsto (fun n => (width n / scale n) ^ 2)
      atTop (nhds (q ^ 2)) := by
    exact hwidthRatio.pow 2
  have hratioQuotient := htimeScaleRatio.div hwidthSq (by positivity : q ^ 2 ≠ 0)
  have hratio : Tendsto (fun n => (time n : ℝ) / width n ^ 2)
      atTop (nhds (constant / q ^ 2)) := by
    have heq : (fun n => (time n : ℝ) / width n ^ 2) =ᶠ[atTop]
        fun n => ((time n : ℝ) / scale n ^ 2) / ((width n / scale n) ^ 2) := by
      filter_upwards [IsMogulskiiScale.eventually_pos hscale] with n hn
      have hwidthPosN : 0 < widthNat n := by
        dsimp [widthNat, latticeScale, alphaTwoLatticeScale,
          Asymptotics.floorBlockLength]
        omega
      have hwidthPos : 0 < width n := by
        change 0 < (widthNat n : ℝ)
        exact_mod_cast hwidthPosN
      field_simp [hn.ne', hwidthPos.ne']
    have hlim := hratioQuotient.congr' heq.symm
    simpa using hlim

  have hproportion : Tendsto
      (fun n => ((windowRadius n - 1 : ℕ) : ℝ) / width n)
      atTop (nhds p) := by
    simpa [width, widthNat, latticeScale, spacing, windowRadius] using
      tendsto_alphaTwoEndpointWindowMinusOne_div_eightLattice hscale hq hp

  have hspacingRatio : Tendsto (fun n => (spacing n : ℝ) / width n)
      atTop (nhds p) := by
    simpa [width, widthNat, latticeScale, spacing] using
      tendsto_alphaTwoEndpointSpacing_div_eightLattice hscale hq hp

  have hrootRatio := tendsto_sqrtBlock_div_width_of_diffusiveRatio hratio

  have hwindowRatio : Tendsto (fun n => (windowRadius n : ℝ) / width n)
      atTop (nhds p) := by
    have hinv : Tendsto (fun n => (1 : ℝ) / width n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hwidthTop
    have hadd := hspacingRatio.add hinv
    have heq : (fun n => (windowRadius n : ℝ) / width n) =ᶠ[atTop]
        fun n => (spacing n : ℝ) / width n + 1 / width n := by
      filter_upwards [] with n
      simp [windowRadius, alphaTwoEndpointWindowRadius]
      ring
    simpa using hadd.congr' heq.symm

  have hmesh : Tendsto
      (fun n => (spacing n : ℝ) / Real.sqrt (time n : ℝ))
      atTop (nhds meshLimit) := by
    have hquot := hspacingRatio.div hrootRatio hroot.ne'
    have heq : (fun n => (spacing n : ℝ) / Real.sqrt (time n : ℝ)) =ᶠ[atTop]
        fun n => ((spacing n : ℝ) / width n) /
          (Real.sqrt (time n : ℝ) / width n) := by
      filter_upwards [hwidthTop.eventually_gt_atTop 0] with n hn
      have hwidthNe : width n ≠ 0 := ne_of_gt hn
      field_simp [hwidthNe]
    have h := hquot.congr' heq.symm
    simpa [meshLimit] using h

  have hwindowNorm : Tendsto
      (fun n => (windowRadius n : ℝ) / Real.sqrt (time n : ℝ))
      atTop (nhds spectralWindowLimit) := by
    have hquot := hwindowRatio.div hrootRatio hroot.ne'
    have heq : (fun n => (windowRadius n : ℝ) / Real.sqrt (time n : ℝ)) =ᶠ[atTop]
        fun n => ((windowRadius n : ℝ) / width n) /
          (Real.sqrt (time n : ℝ) / width n) := by
      filter_upwards [hwidthTop.eventually_gt_atTop 0] with n hn
      have hwidthNe : width n ≠ 0 := ne_of_gt hn
      field_simp [hwidthNe]
    have h := hquot.congr' heq.symm
    simpa [spectralWindowLimit, meshLimit] using h

  have hwidthOverRoot : Tendsto (fun n => width n / Real.sqrt (time n : ℝ))
      atTop (nhds (1 / Real.sqrt (constant / q ^ 2))) := by
    have hquot := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (nhds 1)).div hrootRatio hroot.ne'
    have heq : (fun n => width n / Real.sqrt (time n : ℝ)) =ᶠ[atTop]
        fun n => 1 / (Real.sqrt (time n : ℝ) / width n) := by
      filter_upwards [hwidthTop.eventually_gt_atTop 0] with n hn
      have hwidthNe : width n ≠ 0 := ne_of_gt hn
      field_simp [hwidthNe]
    exact hquot.congr' heq.symm

  have hspectralRadius : Tendsto
      (fun n => 4 * (latticeScale n : ℝ) / Real.sqrt (time n : ℝ))
      atTop (nhds spectralRadiusLimit) := by
    have hscaled := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ))
      atTop (nhds (1 / 2 : ℝ))).mul hwidthOverRoot
    have heq : (fun n => 4 * (latticeScale n : ℝ) / Real.sqrt (time n : ℝ)) =ᶠ[atTop]
        fun n => (1 / 2 : ℝ) * (width n / Real.sqrt (time n : ℝ)) := by
      filter_upwards [] with n
      simp [width, widthNat, latticeScale]
      ring
    have h := hscaled.congr' heq.symm
    have hlimit : (1 / 2 : ℝ) * (1 / Real.sqrt (constant / q ^ 2)) =
        1 / (2 * Real.sqrt (constant / q ^ 2)) := by
      field_simp [hroot.ne']
    rw [hlimit] at h
    simpa [spectralRadiusLimit] using h

  have hmeshApprox : ∀ᶠ n in atTop,
      meshLimit - δ / 8 < (spacing n : ℝ) / Real.sqrt (time n : ℝ) ∧
        (spacing n : ℝ) / Real.sqrt (time n : ℝ) < meshLimit + δ / 8 := by
    have hlow := hmesh.eventually
      (Ioi_mem_nhds (show meshLimit - δ / 8 < meshLimit by linarith))
    have hhigh := hmesh.eventually
      (Iio_mem_nhds (show meshLimit < meshLimit + δ / 8 by linarith))
    filter_upwards [hlow, hhigh] with n hnlo hnhi
    exact ⟨hnlo, hnhi⟩

  have hwindowNormMesh : Tendsto
      (fun n => (windowRadius n : ℝ) / Real.sqrt (time n : ℝ))
      atTop (nhds meshLimit) := by
    simpa [meshLimit, spectralWindowLimit] using hwindowNorm

  have hwindowApprox : ∀ᶠ n in atTop,
      meshLimit - δ / 8 < (windowRadius n : ℝ) / Real.sqrt (time n : ℝ) ∧
        (windowRadius n : ℝ) / Real.sqrt (time n : ℝ) < meshLimit + δ / 8 := by
    have hlow := hwindowNormMesh.eventually
      (Ioi_mem_nhds (show meshLimit - δ / 8 < meshLimit by linarith))
    have hhigh := hwindowNormMesh.eventually
      (Iio_mem_nhds (show meshLimit < meshLimit + δ / 8 by linarith))
    filter_upwards [hlow, hhigh] with n hnlo hnhi
    exact ⟨hnlo, hnhi⟩

  have hiAbsBound (i : ℤ) (hi : i ∈ Finset.Icc (-3 : ℤ) 3) :
      |(i : ℝ)| ≤ 3 := by
    rcases Finset.mem_Icc.mp hi with ⟨hiLower, hiUpper⟩
    apply abs_le.mpr
    constructor
    · exact_mod_cast hiLower
    · exact_mod_cast hiUpper

  have hcenterError (i : ℤ) (hi : i ∈ Finset.Icc (-3 : ℤ) 3)
      (n : ℕ) (hm : |(spacing n : ℝ) / Real.sqrt (time n : ℝ) - meshLimit| < δ / 8) :
      |(i : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n : ℝ) - meshLimit)| <
        3 * (δ / 8) := by
    rw [abs_mul]
    calc
      |(i : ℝ)| *
          |(spacing n : ℝ) / Real.sqrt (time n : ℝ) - meshLimit|
          ≤ 3 * |(spacing n : ℝ) / Real.sqrt (time n : ℝ) - meshLimit| :=
        mul_le_mul_of_nonneg_right (hiAbsBound i hi) (abs_nonneg _)
      _ < 3 * (δ / 8) := mul_lt_mul_of_pos_left hm (by norm_num)

  have hwindowLimit : ∀ i ∈ Finset.Icc (-3 : ℤ) 3, ∀ᶠ n in atTop,
      4 * (latticeScale n : ℝ) / Real.sqrt (time n : ℝ) ≤ closedRadius ∧
        (i : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n : ℝ)) -
            (windowRadius n : ℝ) / Real.sqrt (time n : ℝ) ≥
          (i : ℝ) * meshLimit - closedWindow ∧
        (i : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n : ℝ)) +
            (windowRadius n : ℝ) / Real.sqrt (time n : ℝ) ≤
          (i : ℝ) * meshLimit + closedWindow := by
    intro i hi
    have hradius := hspectralRadius.eventually
      (Iio_mem_nhds (show spectralRadiusLimit < closedRadius by
        dsimp [closedRadius]
        linarith))
    filter_upwards [hradius, hmeshApprox, hwindowApprox] with n hr hm hw
    have hmeshErr : |(spacing n : ℝ) / Real.sqrt (time n : ℝ) - meshLimit| < δ / 8 := by
      rw [abs_lt]
      constructor <;> linarith [hm.1, hm.2]
    have hwindowErr : |(windowRadius n : ℝ) / Real.sqrt (time n : ℝ) - meshLimit| < δ / 8 := by
      rw [abs_lt]
      constructor <;> linarith [hw.1, hw.2]
    have hcenterErr := hcenterError i hi n hmeshErr
    have hcenterBounds := abs_lt.mp hcenterErr
    have hwindowBounds := abs_lt.mp hwindowErr
    refine ⟨hr.le, ?_, ?_⟩
    · dsimp [closedWindow, spectralWindowLimit]
      nlinarith
    · dsimp [closedWindow, spectralWindowLimit]
      nlinarith

  have hclosedRadius : 0 ≤ closedRadius := by
    dsimp [closedRadius, spectralRadiusLimit]
    positivity
  have hclosedOpenRadius : closedRadius < openRadius := by
    dsimp [closedRadius, openRadius]
    linarith
  have hclosedOpenWindow : closedWindow < openWindow := by
    dsimp [closedWindow, openWindow]
    linarith

  have happlicationContainsOpen : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      ∀ᶠ n in atTop,
        openRadius ≤ applicationRadius ∧
          (i : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n : ℝ)) -
              applicationWindow ≤
            (i : ℝ) * meshLimit - openWindow ∧
          (i : ℝ) * meshLimit + openWindow ≤
            (i : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n : ℝ)) +
              applicationWindow := by
    intro i hi
    filter_upwards [hmeshApprox] with n hm
    have hmeshErr : |(spacing n : ℝ) / Real.sqrt (time n : ℝ) - meshLimit| < δ / 8 := by
      rw [abs_lt]
      constructor <;> linarith [hm.1, hm.2]
    have hcenterErr := hcenterError i hi n hmeshErr
    have hcenterBounds := abs_lt.mp hcenterErr
    refine ⟨?_, ?_, ?_⟩
    · dsimp [openRadius, applicationRadius]
      linarith
    · dsimp [applicationWindow, openWindow, spectralWindowLimit]
      nlinarith
    · dsimp [applicationWindow, openWindow, spectralWindowLimit]
      nlinarith

  have hmeshLimitPos : 0 < meshLimit := by
    dsimp [meshLimit]
    exact div_pos hp hroot

  have hspacingPositive : ∀ᶠ n in atTop,
      0 < (spacing n : ℝ) / Real.sqrt (time n : ℝ) := by
    filter_upwards [hmesh.eventually (Ioi_mem_nhds hmeshLimitPos)] with n hn
    exact hn

  have happlicationWindowPositive : ∀ᶠ n : ℕ in atTop, 0 < applicationWindow := by
    filter_upwards [] with n
    dsimp [applicationWindow, spectralWindowLimit]
    positivity

  have hreturnGap : 0 < meshLimit - 3 * δ := by
    dsimp [meshLimit]
    linarith [hreturnMargin]
  let returnError : ℝ := (meshLimit - 3 * δ) / 4
  have hreturnWindowLe : ∀ᶠ n in atTop,
      applicationWindow ≤ 2 * ((spacing n : ℝ) / Real.sqrt (time n : ℝ)) := by
    have hnear := hmesh.eventually
      (Ioi_mem_nhds (show meshLimit - returnError < meshLimit by
        dsimp [returnError]
        linarith [hreturnGap]))
    filter_upwards [hnear] with n hn
    have hlow : 2 * (meshLimit - returnError) <
        2 * ((spacing n : ℝ) / Real.sqrt (time n : ℝ)) := by
      nlinarith [hn]
    have hbound : applicationWindow ≤ 2 * (meshLimit - returnError) := by
      dsimp [applicationWindow, spectralWindowLimit, returnError]
      nlinarith [hreturnGap]
    exact hbound.trans hlow.le

  have hblockSqrt :=
    _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.tendsto_sqrt_diffusiveBlockLength_div
      hscale hconstant
  have hblockSqrtLocal : Tendsto
      (fun n => Real.sqrt (blockLength n : ℝ) / scale n)
      atTop (nhds (Real.sqrt constant)) := by
    simpa [blockLength] using hblockSqrt
  have hmeshFactor : Tendsto
      (fun n => applicationRadius +
        3 * ((spacing n : ℝ) / Real.sqrt (time n : ℝ)) + applicationWindow)
      atTop (nhds (applicationRadius + 3 * meshLimit + applicationWindow)) := by
    have hradiusConst : Tendsto (fun _ : ℕ => applicationRadius) atTop
        (nhds applicationRadius) := tendsto_const_nhds
    have hthreeMesh : Tendsto
        (fun n => (3 : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n : ℝ)))
        atTop (nhds (3 * meshLimit)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (nhds 3)).mul hmesh
    have hwindowConst : Tendsto (fun _ : ℕ => applicationWindow) atTop
        (nhds applicationWindow) := tendsto_const_nhds
    simpa [add_assoc] using hradiusConst.add hthreeMesh |>.add hwindowConst

  have houterRatio : Tendsto
      (fun n => 2 * (applicationRadius +
        3 * ((spacing n : ℝ) / Real.sqrt (time n : ℝ)) + applicationWindow) *
          Real.sqrt (blockLength n : ℝ) / scale n)
      atTop (nhds (2 * (applicationRadius + 3 * meshLimit + applicationWindow) *
        Real.sqrt constant)) := by
    have hprod := hmeshFactor.mul hblockSqrtLocal
    have hscaled := hprod.const_mul 2
    have hscaled' : Tendsto (fun n =>
        (applicationRadius +
          3 * ((spacing n : ℝ) / Real.sqrt (time n : ℝ)) + applicationWindow) *
          (Real.sqrt (blockLength n : ℝ) / scale n) * 2)
        atTop (nhds ((applicationRadius + 3 * meshLimit + applicationWindow) *
          Real.sqrt constant * 2)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
    have heq : (fun n => 2 * (applicationRadius +
        3 * ((spacing n : ℝ) / Real.sqrt (time n : ℝ)) + applicationWindow) *
          Real.sqrt (blockLength n : ℝ) / scale n) =ᶠ[atTop]
        fun n => (applicationRadius +
          3 * ((spacing n : ℝ) / Real.sqrt (time n : ℝ)) + applicationWindow) *
            (Real.sqrt (blockLength n : ℝ) / scale n) * 2 := by
      filter_upwards [] with n
      ring
    have h := hscaled'.congr' heq.symm
    simpa [mul_assoc, mul_left_comm, mul_comm] using h

  have houterMargin' :
      2 * (applicationRadius + 3 * meshLimit + applicationWindow) *
        Real.sqrt constant < 1 := by
    simpa [applicationRadius, spectralRadiusLimit, meshLimit,
      applicationWindow, spectralWindowLimit] using houterMargin

  have houterEventually := houterRatio.eventually
    (Iio_mem_nhds houterMargin')
  have houterFit : ∀ᶠ n in atTop,
      2 * (applicationRadius +
        3 * ((spacing n : ℝ) / Real.sqrt (time n : ℝ)) + applicationWindow) *
          Real.sqrt (blockLength n : ℝ) ≤ scale n := by
    filter_upwards [houterEventually,
      IsMogulskiiScale.eventually_pos hscale] with n hout hscalePos
    have hdiv := (div_lt_iff₀ hscalePos).mp hout
    linarith

  have hrate :=
    one_div_constant_mul_log_toReal_le_liminf_scaledLog_horizontalTubeProbability_of_spectralEndpointWindows
      ν hν hscale hB hcontinuous hmeasurable hconstant
      blockLength time latticeScale spacing windowRadius
      hblockLengthPos hcountLimit htimePos htimeTop htimeEq hlatticePos
      hwindowLower hfitSpectral hwidthTop hratio hproportion hp hsmallLimit
      hspectralLower happlicationLower happlicationLowerOne
      happlicationBelow
      hclosedRadius hclosedOpenRadius hclosedOpenWindow
      (fun _ => applicationRadius) (fun _ => applicationWindow)
      hwindowLimit happlicationContainsOpen hspacingPositive
      happlicationWindowPositive hreturnWindowLe houterFit
  simpa using hrate

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
