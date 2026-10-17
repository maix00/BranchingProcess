/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Block
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.EndpointBandTransfer.StableRate
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Partition
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Core
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer

/-!
# Stable endpoint-return lower bound for horizontal tubes

Write $s_n=\mathrm{scale}(n)$,
$L^*(x)=\mathrm{stableSlowVariation}(\alpha,\nu)(x)$,
$a_n=s_n^\alpha/(nL^*(s_n))$, and
$T_n=\{|S_j|<s_n/2\text{ for }1\leq j\leq n\}$ for partial sums of
i.i.d. increments with law $\nu$. Under the stable scale, slowly varying,
stable escape-rate, domain-of-attraction, tightness, and endpoint-sign
hypotheses, the public declaration is:

- `eventually_openHorizontalTubeProbability_ge_exp_of_stableEscapeRate`:
  under the stable escape-rate, domain-of-attraction, scale, and tightness
  assumptions, for fixed $r>0$, $\varepsilon>0$, $4\varepsilon<r$,
  $2(r+4\varepsilon)<1$, and $\delta>0$, there is $c>0$ such that eventually
  $\bigl(\exp((C/r^\alpha-\delta)c^\alpha)\bigr)^{\lfloor n/\ell_n\rfloor+1}
  \leq \mathbb P(T_n)$, where $T_n$ is the centered open horizontal tube and
  $\ell_n=\mathrm{stableBlockLength}(\alpha,\nu,c^\alpha,\mathrm{scale},n)$.

This is the block-level endpoint-return lower estimate in Theorem 3,
Section 4 of A. A. Mogul'skii, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765;
English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable

/-- The endpoint-return argument in Theorem 3, Section 4 of A. A. Mogul'skii,
“Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations
in a Space of Trajectories,” *Theory of Probability and Its Applications*
19(4) (1975), 726--736, DOI 10.1137/1119081, gives an eventual exponential
lower bound for every fixed strict interior tube. The smaller closed tube
from the discrete return estimate is contained in the requested open tube. -/
theorem eventually_openHorizontalTubeProbability_ge_exp_of_stableEscapeRate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet (Set.range
      fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {radius epsilon delta : ℝ}
    (hradius : 0 < radius) (hepsilon : 0 < epsilon)
    (hmargin : 4 * epsilon < radius)
    (hwidth : 2 * (radius + 4 * epsilon) < 1)
    (hdelta : 0 < delta) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.exp
          ((C / radius ^ α - delta) * c ^ α)) ^
            (n / stableBlockLength α ν (c ^ α) scale n + 1) ≤
          openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
            (scale n) n := by
  let rate : ℝ := C / radius ^ α
  have hscaledMass :=
    ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_scaledStableEndpointBandProbability_ge_exp
      hEscape hX hcdf hradius hepsilon hmargin (by linarith : 0 < delta / 2)
  obtain ⟨c₀, hc₀⟩ := Filter.eventually_atTop.1
    (hscaledMass.and (eventually_gt_atTop (0 : ℝ)))
  let c : ℝ := max c₀ 1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcMass := hc₀ c (le_max_left _ _)
  have hcPower : 0 < c ^ α := Real.rpow_pos_of_pos hc α
  have hlowExponent :
      (rate - delta) * c ^ α < (rate - delta / 2) * c ^ α := by
    nlinarith
  have hlowENN : ENNReal.ofReal (Real.exp ((rate - delta) * c ^ α)) <
      ENNReal.ofReal (Real.exp ((rate - delta / 2) * c ^ α)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2
    exact Real.exp_lt_exp.mpr hlowExponent
  let lowerBound : ENNReal := ENNReal.ofReal
    (Real.exp ((rate - delta) * c ^ α))
  have hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound < P.map (Skorokhod.scalePath c)
        (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
          (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon)) := by
    intro i hi
    exact hlowENN.trans (hcMass.1 i hi)
  let blockLength : ℕ → ℕ := fun n =>
    stableBlockLength α ν (c ^ α) scale n
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hblockTop : Tendsto blockLength atTop atTop := by
    simpa [blockLength] using tendsto_stableBlockLength_atTop_of_slowVariation
      hα hα₂ hslow hcPower hscaleTop
  have hblockPos : ∀ᶠ n : ℕ in atTop, 0 < blockLength n :=
    hblockTop.eventually (eventually_gt_atTop 0)
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hnormBlockPos : ∀ᶠ n : ℕ in atTop,
      0 < normalization (blockLength n) :=
    (hscale.stableNorming.2.1.comp hblockTop).eventually
      (eventually_gt_atTop 0)
  have hblockEq : blockLength = Asymptotics.floorBlockLength
      (fun n => c ^ α * stableScaleTime α ν (scale n)) := by
    funext n
    change ⌊stableBlockArgument α ν (c ^ α) scale n⌋₊ =
      ⌊c ^ α * stableScaleTime α ν (scale n)⌋₊
    rw [stableBlockArgument_eq_constant_mul_stableScaleTime]
  have hnormRatioBase :=
    hscale.stableNorming.tendsto_floorBlock_normalization_div_scale
      hα hα₂ hslow hscaleTop hcPower
  have hnormRatio : Tendsto
      (fun n => normalization (blockLength n) / scale n)
      atTop (𝓝 c) := by
    have hbase : Tendsto
        (fun n => normalization (blockLength n) / scale n)
        atTop (𝓝 ((c ^ α) ^ (1 / α))) := by
      apply hnormRatioBase.congr'
      filter_upwards [] with n
      simp [blockLength, hblockEq]
    have hroot : (c ^ α) ^ (1 / α) = c := by
      rw [← Real.rpow_mul (le_of_lt hc) α (1 / α)]
      have hmul : α * (1 / α) = 1 := by field_simp [ne_of_gt hα]
      rw [hmul, Real.rpow_one]
    convert hbase using 1
    exact congrArg nhds hroot.symm
  have hlimit :=
    RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
        hDOA hEscape.isStableClockProcessLaw htightBase hblockTop
        hscalePos hnormBlockPos hnormRatio
  have hscaleMapMeas : Measurable (Skorokhod.scalePath c) :=
    (Skorokhod.continuous_scalePath.comp
      (continuous_const.prodMk continuous_id)).measurable
  have hlimit' := hlimit.congr_limit (μ'' := P)
    (Z' := Skorokhod.scalePath c) hscaleMapMeas.aemeasurable (by simp)
  have hclosedLower :=
    ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_horizontalTubeProbability_ge_pow_of_pathLawLimit
      ν scale blockLength (fun n => n)
      (Z := Skorokhod.scalePath c) hlimit' hscalePos hblockPos
      hradius hepsilon lowerBound hbelow
  refine ⟨c, hc, ?_⟩
  filter_upwards [hclosedLower, hscalePos] with n hclosed hscaleN
  have hwidthAt :
      2 * (radius + 4 * epsilon) * scale n < scale n := by
    calc
      2 * (radius + 4 * epsilon) * scale n < 1 * scale n :=
        mul_lt_mul_of_pos_right hwidth hscaleN
      _ = scale n := by ring
  have hsubset :
      {increment | InHorizontalTube (1 / 2)
        (2 * (radius + 4 * epsilon) * scale n) n increment} ⊆
      {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} := by
    intro increment h
    change ∀ k : Fin n,
      -(1 / 2 : ℝ) * (2 * (radius + 4 * epsilon) * scale n) ≤
          AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment ≤
          (1 - (1 / 2 : ℝ)) * (2 * (radius + 4 * epsilon) * scale n) at h
    intro k
    rcases h k with ⟨hlo, hhi⟩
    constructor
    · exact (show -(1 / 2 : ℝ) * scale n <
        -(1 / 2 : ℝ) * (2 * (radius + 4 * epsilon) * scale n) by
          nlinarith).trans_le hlo
    · exact hhi.trans_lt (show
        (1 - (1 / 2 : ℝ)) * (2 * (radius + 4 * epsilon) * scale n) <
          (1 - (1 / 2 : ℝ)) * scale n by nlinarith)
  have hmono :
      horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
        (2 * (radius + 4 * epsilon) * scale n) n ≤
      openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
        (scale n) n := by
    change iidSequenceLaw ν
        {increment | InHorizontalTube (1 / 2)
          (2 * (radius + 4 * epsilon) * scale n) n increment} ≤
      iidSequenceLaw ν
        {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment}
    exact measure_mono hsubset
  exact hclosed.trans hmono


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable

end
