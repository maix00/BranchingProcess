/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.NormalConstant
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.CLT
import Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Scaling.Discretization
import Probability.Process.Stable.Brownian.PathLaw

/-!
# The Brownian escape constant

The path-class theorem identifies the strict centered Rademacher tube rate
with four times the exponent-two stable-process escape constant.  The sharp
spectral theorem gives the rate for closed centered tubes.  Fixed narrower
closed tubes squeeze the strict-tube rate between those spectral limits, and
letting their relative width increase to one identifies the constant.

The Brownian specialization uses the existing rational-coordinate càdlàg
path law of `IsBrownianReal`; it only uses the a.e. continuity recorded by
Mathlib, not an everywhere-continuous sample-path version.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open ProbabilityTheory.RandomWalk.FunctionalLimit.Normal
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian

open ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- A canonical scale well below the diffusive scale, used to calibrate the
scale-independent Brownian escape constant. -/
theorem canonicalMogulskiiScale :
    IsMogulskiiScale (fun n : ℕ => Real.sqrt (Real.sqrt (n : ℝ))) := by
  rw [ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.isMogulskiiScale_iff]
  apply Asymptotics.IsSmallDeviationScale.of_tendsto
  · exact Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  · have hsqrt : Tendsto
        (fun n : ℕ => Real.sqrt (Real.sqrt (n : ℝ))) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hinv := tendsto_inv_atTop_zero.comp hsqrt
    have heq : (fun n : ℕ =>
        Real.sqrt (Real.sqrt (n : ℝ)) / Real.sqrt (n : ℝ)) =ᶠ[atTop]
        fun n : ℕ => (Real.sqrt (Real.sqrt (n : ℝ)))⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
      have hs : 0 < Real.sqrt (Real.sqrt (n : ℝ)) :=
        Real.sqrt_pos.2 (Real.sqrt_pos.2 hn')
      have hsq : Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 = Real.sqrt (n : ℝ) :=
        Real.sq_sqrt (Real.sqrt_nonneg _)
      calc
        Real.sqrt (Real.sqrt (n : ℝ)) / Real.sqrt (n : ℝ) =
            Real.sqrt (Real.sqrt (n : ℝ)) /
              Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 := by rw [hsq]
        _ = (Real.sqrt (Real.sqrt (n : ℝ)))⁻¹ := by
          field_simp [ne_of_gt hs]
    exact hinv.congr' heq.symm

private noncomputable def closedCenteredTubeProbability
    (scale : ℕ → ℝ) (n : ℕ) : ENNReal :=
  horizontalTubeProbability (iidSequenceLaw rademacherMeasure) (1 / 2)
    ((2 : ℝ) * (centeredLatticeRadius scale n : ℝ)) n

private noncomputable def openCenteredTubeProbability
    (scale : ℕ → ℝ) (n : ℕ) : ENNReal :=
  openHorizontalTubeProbability (iidSequenceLaw rademacherMeasure)
    (1 / 2) (scale n) n

private theorem centeredLatticeWidth_gt (scale : ℕ → ℝ) (n : ℕ)
    (hscale : 0 ≤ scale n) :
    scale n < (2 : ℝ) * (centeredLatticeRadius scale n : ℝ) := by
  have hfloor : (⌊scale n / 2⌋₊ : ℝ) ≤ scale n / 2 :=
    Nat.floor_le (by positivity)
  have hfloorLower : scale n / 2 < (⌊scale n / 2⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  simp only [centeredLatticeRadius, Nat.cast_add, Nat.cast_one]
  nlinarith [hfloorLower]

private theorem inOpenTube_subset_inClosedTube
    {innerWidth outerWidth : ℝ} {n : ℕ}
    (hwidth : innerWidth ≤ outerWidth) :
    {increment : ℕ → ℝ |
      RandomWalk.InOpenHorizontalTube (1 / 2) innerWidth n increment} ⊆
    {increment : ℕ → ℝ |
      RandomWalk.InHorizontalTube (1 / 2) outerWidth n increment} := by
  simp only [RandomWalk.InOpenHorizontalTube, RandomWalk.InHorizontalTube]
  intro increment hincrement k
  have hk := hincrement k
  constructor <;> nlinarith [hk.1, hk.2, hwidth]

private theorem inClosedTube_subset_inOpenTube
    {innerWidth outerWidth : ℝ} {n : ℕ}
    (hwidth : innerWidth < outerWidth) :
    {increment : ℕ → ℝ |
      RandomWalk.InHorizontalTube (1 / 2) innerWidth n increment} ⊆
    {increment : ℕ → ℝ |
      RandomWalk.InOpenHorizontalTube (1 / 2) outerWidth n increment} := by
  simp only [RandomWalk.InHorizontalTube, RandomWalk.InOpenHorizontalTube]
  intro increment hincrement k
  have hk := hincrement k
  constructor <;> nlinarith [hk.1, hk.2, hwidth]

/-- The path-class theorem supplies the strict centered-tube rate for every
Rademacher stable Mogulskii scale.  The rate normalization is the familiar
`scale n ^ 2 / n`, because the Rademacher truncated second moment is
eventually one. -/
private theorem rademacher_openCenteredTube_rate
    {C : ℝ} {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate 2 (gaussianReal 0 1) P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess 2 (gaussianReal 0 1) X Q)
    {scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 rademacherMeasure
      (fun n => Real.sqrt n) scale) :
    (∀ᶠ n : ℕ in atTop, 0 < openCenteredTubeProbability scale n) ∧
    Tendsto
        (fun n : ℕ => scale n ^ 2 / (n : ℝ) *
          Real.log (openCenteredTubeProbability scale n).toReal)
        atTop (𝓝 (C * 4)) := by
  have hcentered : (∫ x : ℝ, x ∂rademacherMeasure) = 0 := by
    rw [integral_rademacherMeasure]
    norm_num
  have hsecond : (∫ x : ℝ, x ^ 2 ∂rademacherMeasure) = 1 := by
    rw [integral_rademacherMeasure]
    norm_num
  have hDOA : IsInDomainOfAttractionAlong rademacherMeasure
      (gaussianReal 0 1) (fun n => Real.sqrt n) (fun _ => 0) :=
    isInDomainOfAttractionAlong_gaussianReal_zero_one
      rademacherMeasure hcentered hsecond
  have hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation 2 rademacherMeasure) :=
    hDOA.stableSlowVariation_two_isSlowlyVarying_of_gaussian
  have hnormalizationPos : ∀ n : ℕ, 0 < n → 0 < Real.sqrt n :=
    hscale.stableNorming.1
  have htight : IsTightMeasureSet (Set.range fun n =>
      RandomWalk.normalizedStepPathLaw rademacherMeasure
        (fun n => Real.sqrt n) n) :=
    isTightMeasureSet_range_normalizedStepPathLaw_of_gaussian hDOA hnormalizationPos
  have hcdf : 0 < cdf (gaussianReal 0 1) 0 ∧
      cdf (gaussianReal 0 1) 0 < 1 :=
    cdf_gaussianReal_zero_lt_one (v := 1) (by norm_num)
  obtain ⟨hopenPos, hstableRate⟩ :=
    tendsto_stableRate_openHorizontalTube_eq_escapeRate
      hscale hslow hEscape hX hcdf hDOA htight
  have hrateEq := stableSmallDeviationRate_rademacher_eq_of_scale_ge_one
    hscale
  have hopenRate : Tendsto
      (fun n : ℕ => scale n ^ 2 / (n : ℝ) *
        Real.log (openHorizontalTubeProbability
          (iidSequenceLaw rademacherMeasure) (1 / 2) (scale n) n).toReal)
      atTop (𝓝 (C * 2 ^ (2 : ℝ))) := by
    have heq : (fun n : ℕ => stableSmallDeviationRate 2
        rademacherMeasure scale n * Real.log
          (openHorizontalTubeProbability (iidSequenceLaw rademacherMeasure)
            (1 / 2) (scale n) n).toReal) =ᶠ[atTop]
        (fun n : ℕ => scale n ^ 2 / (n : ℝ) *
          Real.log (openHorizontalTubeProbability
            (iidSequenceLaw rademacherMeasure) (1 / 2) (scale n) n).toReal) := by
      filter_upwards [hrateEq] with n hn
      rw [hn]
    exact hstableRate.congr' heq
  have hfour : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
  refine ⟨?_, ?_⟩
  · simpa [openCenteredTubeProbability] using hopenPos
  · simpa [openCenteredTubeProbability, hfour] using hopenRate

/-- For each fixed relative width `q < 1`, the closed tube with rounded
lattice width `q * scale` lies inside the original strict tube eventually.
Its spectral limit therefore gives a lower bound for the strict-tube rate. -/
private theorem fixedNarrowClosedTube_lower_bound
    {C : ℝ} {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate 2 (gaussianReal 0 1) P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess 2 (gaussianReal 0 1) X Q)
    {scale : ℕ → ℝ}
    (hscale : IsMogulskiiScale scale)
    (hstable : IsStableMogulskiiScale 2 rademacherMeasure
      (fun n => Real.sqrt n) scale)
    {q : ℝ} (hq : 0 < q) (hq' : q < 1) :
    -(Real.pi ^ 2) / (2 * q ^ 2) ≤ C * 4 := by
  let narrowScale : ℕ → ℝ := fun n => q * scale n
  have hnarrowStable : IsStableMogulskiiScale 2 rademacherMeasure
      (fun n => Real.sqrt n) narrowScale := by
    simpa [narrowScale] using hstable.const_mul hq
  have hnarrowMogulskii : IsMogulskiiScale narrowScale := hnarrowStable.2
  have hopenNarrow := rademacher_openCenteredTube_rate hEscape hX hnarrowStable
  have hclosedNarrow : Tendsto
      (fun n : ℕ => narrowScale n ^ 2 / (n : ℝ) *
        Real.log (closedCenteredTubeProbability narrowScale n).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2)) := by
    simpa [closedCenteredTubeProbability] using
      hnarrowMogulskii.tendsto_scaledLog_centeredHorizontalTubeProbability
  have hnarrowTop : Tendsto narrowScale atTop atTop := by
    exact Asymptotics.IsSmallDeviationScale.tendsto_atTop hnarrowMogulskii
  have hwidthNarrow : Tendsto
      (fun n : ℕ =>
        ((2 * centeredLatticeRadius narrowScale n : ℕ) : ℝ) /
          narrowScale n) atTop (𝓝 1) :=
    tendsto_centeredLatticeWidth_div hnarrowTop
  have hwidthRatio : Tendsto
      (fun n : ℕ =>
        ((2 * centeredLatticeRadius narrowScale n : ℕ) : ℝ) /
          scale n) atTop (𝓝 q) := by
    have hprod := hwidthNarrow.mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => q) atTop (𝓝 q))
    have heq : (fun n : ℕ =>
        ((2 * centeredLatticeRadius narrowScale n : ℕ) : ℝ) /
          narrowScale n * q) =ᶠ[atTop]
        (fun n : ℕ =>
          ((2 * centeredLatticeRadius narrowScale n : ℕ) : ℝ) /
            scale n) := by
      filter_upwards [hscale.eventually_pos] with n hn
      dsimp [narrowScale]
      field_simp [ne_of_gt hn, ne_of_gt hq]
    simpa using hprod.congr' heq
  have hwidthLt : ∀ᶠ n : ℕ in atTop,
      ((2 * centeredLatticeRadius narrowScale n : ℕ) : ℝ) < scale n := by
    have hratioLt : ∀ᶠ n : ℕ in atTop,
        ((2 * centeredLatticeRadius narrowScale n : ℕ) : ℝ) / scale n < 1 :=
      hwidthRatio.eventually (Iio_mem_nhds hq')
    filter_upwards [hratioLt, hscale.eventually_pos] with n hr hn
    exact (div_lt_one hn).mp hr
  have hprobNarrowOpenLeClosed : ∀ᶠ n : ℕ in atTop,
      openCenteredTubeProbability narrowScale n ≤
        closedCenteredTubeProbability narrowScale n := by
    filter_upwards [hnarrowMogulskii.eventually_pos] with n hn
    change iidSequenceLaw rademacherMeasure
        {increment | RandomWalk.InOpenHorizontalTube (1 / 2)
          (narrowScale n) n increment} ≤
      iidSequenceLaw rademacherMeasure
        {increment | RandomWalk.InHorizontalTube (1 / 2)
          ((2 : ℝ) * (centeredLatticeRadius narrowScale n : ℝ)) n increment}
    apply measure_mono
    exact inOpenTube_subset_inClosedTube
      (le_of_lt (centeredLatticeWidth_gt narrowScale n hn.le))
  have hprobClosedLeOpen : ∀ᶠ n : ℕ in atTop,
      closedCenteredTubeProbability narrowScale n ≤
        openCenteredTubeProbability scale n := by
    filter_upwards [hwidthLt] with n hn
    change iidSequenceLaw rademacherMeasure
        {increment | RandomWalk.InHorizontalTube (1 / 2)
          ((2 : ℝ) * (centeredLatticeRadius narrowScale n : ℝ)) n increment} ≤
      iidSequenceLaw rademacherMeasure
        {increment | RandomWalk.InOpenHorizontalTube (1 / 2)
          (scale n) n increment}
    apply measure_mono
    have hn' : (2 : ℝ) * (centeredLatticeRadius narrowScale n : ℝ) < scale n := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn
    exact inClosedTube_subset_inOpenTube hn'
  have hclosedNarrowPos : ∀ᶠ n : ℕ in atTop,
      0 < (closedCenteredTubeProbability narrowScale n).toReal := by
    filter_upwards [hopenNarrow.1, hprobNarrowOpenLeClosed] with n hopen hprob
    have hopenENN : 0 < openCenteredTubeProbability narrowScale n := hopen
    have hclosedENN : 0 < closedCenteredTubeProbability narrowScale n :=
      lt_of_lt_of_le hopenENN hprob
    exact ENNReal.toReal_pos hclosedENN.ne'
      (measure_lt_top (iidSequenceLaw rademacherMeasure) _).ne
  have hlogClosedLeOpen :
      (fun n : ℕ => Real.log
        (closedCenteredTubeProbability narrowScale n).toReal) ≤ᶠ[atTop]
      (fun n : ℕ => Real.log
        (openCenteredTubeProbability scale n).toReal) := by
    filter_upwards [hclosedNarrowPos, hprobClosedLeOpen] with n hpos hprob
    have hreal := ENNReal.toReal_mono
      (measure_lt_top (iidSequenceLaw rademacherMeasure) _).ne hprob
    exact Real.log_le_log hpos hreal
  have hclosedRescaled : Tendsto
      (fun n : ℕ => scale n ^ 2 / (n : ℝ) *
        Real.log (closedCenteredTubeProbability narrowScale n).toReal)
      atTop (𝓝 (q⁻¹ ^ 2 * (-(Real.pi ^ 2) / 2))) := by
    have hscaled :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => q⁻¹ ^ 2) atTop (𝓝 (q⁻¹ ^ 2))).mul
        hclosedNarrow
    have heq : (fun n : ℕ => q⁻¹ ^ 2 *
        (narrowScale n ^ 2 / (n : ℝ) *
          Real.log (closedCenteredTubeProbability narrowScale n).toReal)) =ᶠ[atTop]
        (fun n : ℕ => scale n ^ 2 / (n : ℝ) *
          Real.log (closedCenteredTubeProbability narrowScale n).toReal) := by
      filter_upwards [hscale.eventually_pos, eventually_gt_atTop (0 : ℕ)] with n hs hn
      dsimp [narrowScale]
      field_simp [ne_of_gt hq, ne_of_gt hs,
        Nat.cast_ne_zero.mpr hn.ne']
    exact hscaled.congr' heq
  have hscaledComparison :
      (fun n : ℕ => scale n ^ 2 / (n : ℝ) *
        Real.log (closedCenteredTubeProbability narrowScale n).toReal) ≤ᶠ[atTop]
      (fun n : ℕ => scale n ^ 2 / (n : ℝ) *
        Real.log (openCenteredTubeProbability scale n).toReal) := by
    filter_upwards [hlogClosedLeOpen, eventually_gt_atTop (0 : ℕ)] with n hlog hn
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hopenOriginal := rademacher_openCenteredTube_rate hEscape hX hstable
  have hlimit := le_of_tendsto_of_tendsto
    hclosedRescaled hopenOriginal.2 hscaledComparison
  have hconstant : q⁻¹ ^ 2 * (-(Real.pi ^ 2) / 2) =
      -(Real.pi ^ 2) / (2 * q ^ 2) := by
    field_simp [ne_of_gt hq]
  rw [hconstant] at hlimit
  exact hlimit

/-- The exponent-two stable-process escape constant is `-π² / 8`.  The
proof squeezes the strict Rademacher tube between the canonical closed
rounded-width tube and every fixed narrower closed rounded-width tube.
-/
theorem _root_.ProbabilityTheory.Process.SmallDeviation.Mogulskii.HasStableProcessEscapeRate.eq_neg_pi_sq_div_eight
    {C : ℝ} {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate 2 (gaussianReal 0 1) P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess 2 (gaussianReal 0 1) X Q)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale) :
    C = -(Real.pi ^ 2) / 8 := by
  have hcentered : (∫ x : ℝ, x ∂rademacherMeasure) = 0 := by
    rw [integral_rademacherMeasure]
    norm_num
  have hsecond : (∫ x : ℝ, x ^ 2 ∂rademacherMeasure) = 1 := by
    rw [integral_rademacherMeasure]
    norm_num
  let normalization : ℕ → ℝ := fun n => Real.sqrt n
  have hDOA : IsInDomainOfAttractionAlong rademacherMeasure
      (gaussianReal 0 1) normalization (fun _ => 0) := by
    simpa [normalization] using
      isInDomainOfAttractionAlong_gaussianReal_zero_one
        rademacherMeasure hcentered hsecond
  have hnormalizationPos : ∀ n : ℕ, 0 < n → 0 < normalization n := by
    intro n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hnorming : IsStableNorming 2 rademacherMeasure normalization :=
    hDOA.isStableNorming_two_of_gaussian hnormalizationPos
  have hstable : IsStableMogulskiiScale 2 rademacherMeasure normalization scale :=
    ⟨hnorming, hscale⟩
  have hopen := rademacher_openCenteredTube_rate hEscape hX hstable
  have hclosed : Tendsto
      (fun n : ℕ => scale n ^ 2 / (n : ℝ) *
        Real.log (closedCenteredTubeProbability scale n).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2)) := by
    simpa [closedCenteredTubeProbability] using
      hscale.tendsto_scaledLog_centeredHorizontalTubeProbability
  have hwidthGt : ∀ᶠ n : ℕ in atTop,
      scale n < (2 : ℝ) * (centeredLatticeRadius scale n : ℝ) := by
    filter_upwards [hscale.eventually_pos] with n hn
    exact centeredLatticeWidth_gt scale n hn.le
  have hprobOpenLeClosed : ∀ᶠ n : ℕ in atTop,
      openCenteredTubeProbability scale n ≤ closedCenteredTubeProbability scale n := by
    filter_upwards [hwidthGt] with n hn
    change iidSequenceLaw rademacherMeasure
        {increment | RandomWalk.InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤
      iidSequenceLaw rademacherMeasure
        {increment | RandomWalk.InHorizontalTube (1 / 2)
          ((2 : ℝ) * (centeredLatticeRadius scale n : ℝ)) n increment}
    apply measure_mono
    exact inOpenTube_subset_inClosedTube (le_of_lt hn)
  have hlogOpenLeClosed :
      (fun n : ℕ => Real.log (openCenteredTubeProbability scale n).toReal) ≤ᶠ[atTop]
      (fun n : ℕ => Real.log (closedCenteredTubeProbability scale n).toReal) := by
    filter_upwards [hopen.1, hprobOpenLeClosed] with n hpos hprob
    have hreal := ENNReal.toReal_mono
      (measure_lt_top (iidSequenceLaw rademacherMeasure) _).ne hprob
    have hposReal : 0 < (openCenteredTubeProbability scale n).toReal :=
      ENNReal.toReal_pos hpos.ne'
        (measure_lt_top (iidSequenceLaw rademacherMeasure) _).ne
    exact Real.log_le_log hposReal hreal
  have hscaledComparison :
      (fun n : ℕ => scale n ^ 2 / (n : ℝ) *
        Real.log (openCenteredTubeProbability scale n).toReal) ≤ᶠ[atTop]
      (fun n : ℕ => scale n ^ 2 / (n : ℝ) *
        Real.log (closedCenteredTubeProbability scale n).toReal) := by
    filter_upwards [hlogOpenLeClosed, eventually_gt_atTop (0 : ℕ)] with n hlog hn
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hupper : C * 4 ≤ -(Real.pi ^ 2) / 2 :=
    le_of_tendsto_of_tendsto hopen.2 hclosed hscaledComparison
  let q : ℕ → ℝ := fun m => 1 - 1 / ((m : ℝ) + 2)
  have hqpos (m : ℕ) : 0 < q m := by
    dsimp [q]
    have hm : 1 < (m : ℝ) + 2 := by
      have : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
      linarith
    have hrec : 1 / ((m : ℝ) + 2) < 1 := by
      rw [one_div]
      exact inv_lt_one_of_one_lt₀ hm
    linarith
  have hqlt (m : ℕ) : q m < 1 := by
    dsimp [q]
    have hpos : 0 < 1 / ((m : ℝ) + 2) := by positivity
    linarith
  have hqTendsto : Tendsto q atTop (𝓝 1) := by
    have hden : Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have hinv := tendsto_inv_atTop_zero.comp hden
    simpa [q] using tendsto_const_nhds.sub hinv
  have hlowerSequence : ∀ m : ℕ,
      -(Real.pi ^ 2) / (2 * q m ^ 2) ≤ C * 4 := by
    intro m
    exact fixedNarrowClosedTube_lower_bound hEscape hX hscale hstable
      (hqpos m) (hqlt m)
  have hqInv : Tendsto (fun m : ℕ => (q m)⁻¹) atTop (𝓝 1) :=
    by simpa using hqTendsto.inv₀ one_ne_zero
  have hlowerLimit : Tendsto
      (fun m : ℕ => -(Real.pi ^ 2) / (2 * q m ^ 2))
      atTop (𝓝 (-(Real.pi ^ 2) / 2)) := by
    have h := (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => -(Real.pi ^ 2) / 2) atTop
      (𝓝 (-(Real.pi ^ 2) / 2))).mul (hqInv.pow 2)
    have heq : (fun m : ℕ => (-(Real.pi ^ 2) / 2) * (q m)⁻¹ ^ 2) =ᶠ[atTop]
        (fun m : ℕ => -(Real.pi ^ 2) / (2 * q m ^ 2)) := by
      filter_upwards [Filter.Eventually.of_forall
        (fun m => ne_of_gt (hqpos m))] with m hq
      field_simp [hq]
    have h' := h.congr' heq
    simpa using h'
  have hlower : -(Real.pi ^ 2) / 2 ≤ C * 4 :=
    le_of_tendsto_of_tendsto hlowerLimit tendsto_const_nhds
      (Filter.Eventually.of_forall hlowerSequence)
  have hcoef : C * 4 = -(Real.pi ^ 2) / 2 := by
    linarith
  nlinarith [hcoef]

/-- The corresponding full-width exponent-two coefficient is `-π² / 2`. -/
theorem _root_.ProbabilityTheory.Process.SmallDeviation.Mogulskii.HasStableProcessEscapeRate.fullWidthCoefficient_eq_neg_pi_sq_div_two
    {C : ℝ} {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate 2 (gaussianReal 0 1) P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess 2 (gaussianReal 0 1) X Q)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale) :
    C * 2 ^ (2 : ℝ) = -(Real.pi ^ 2) / 2 := by
  have hC :=
    _root_.ProbabilityTheory.Process.SmallDeviation.Mogulskii.HasStableProcessEscapeRate.eq_neg_pi_sq_div_eight
      hEscape hX hscale
  rw [hC]
  have hpow : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
  rw [hpow]
  ring

/-- Mathlib's almost-surely continuous Brownian process has the calibrated
escape constant on its canonical rational-coordinate càdlàg path law.  The
path-law constructor handles the exceptional non-càdlàg set measurably. -/
theorem exists_brownian_escapeRate_eq_neg_pi_sq_div_eight
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B Q)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale) :
    ∃ C, HasStableProcessEscapeRate 2 (gaussianReal 0 1)
      (Process.Path.Cadlag.pathLaw Q
        (fun t ω => B (unitIntervalToNNReal t) ω)
        (fun t => hB.toIsPreBrownianReal.aemeasurable
          (unitIntervalToNNReal t))) C ∧
      C = -(Real.pi ^ 2) / 8 ∧
      C * 2 ^ (2 : ℝ) = -(Real.pi ^ 2) / 2 := by
  have hP := hB.isStableClockProcessLaw_cadlagunitIntervalProcessPathLaw
  have hX := hB.isStableLevyProcess
  have hcdf : 0 < cdf (gaussianReal 0 1) 0 ∧
      cdf (gaussianReal 0 1) 0 < 1 :=
    cdf_gaussianReal_zero_lt_one (v := 1) (by norm_num)
  obtain ⟨C, hEscape⟩ :=
    hP.hasStableProcessEscapeRate_of_isStableLevyProcess hX hcdf
  exact ⟨C, hEscape,
    _root_.ProbabilityTheory.Process.SmallDeviation.Mogulskii.HasStableProcessEscapeRate.eq_neg_pi_sq_div_eight
      hEscape hX hscale,
    _root_.ProbabilityTheory.Process.SmallDeviation.Mogulskii.HasStableProcessEscapeRate.fullWidthCoefficient_eq_neg_pi_sq_div_two
      hEscape hX hscale⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian

end
