/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Rate.Lower.BlockProbability
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Stable lower bounds for horizontal-tube logarithmic rates

Let $(\xi_i)_{i\geq1}$ be i.i.d. with law $\nu$, put
$S_j=\sum_{i=1}^j\xi_i$, and let $\mathbb P_\nu$ denote their product law.
Write $s_n=\mathrm{scale}(n)$,
$L^*(x)=\mathrm{stableSlowVariation}(\alpha,\nu)(x)$,
$a_n=\frac{s_n^\alpha}{nL^*(s_n)}$, and
$T_n=\{|S_j|<s_n/2\text{ for }1\leq j\leq n\}$.
Assume $0<\alpha\leq2$, a stable Mogulskii scale, $a_n\to0$, slow
variation of $L^*$, the stable-process escape-rate hypothesis with constant
$C$, and the stated domain-of-attraction, tightness, and endpoint-sign
conditions. The public declarations are:

- `stableEscapeRate_subtube_liminf_lower`: if $r,\varepsilon,\delta>0$,
  $4\varepsilon<r$, and $2(r+4\varepsilon)<1$, then
  $\frac{C}{r^\alpha}-\delta\leq\liminf_n a_n\log\mathbb P_\nu(T_n)$.
- `stableEscapeRate_liminf_lower`:
  $\frac{C}{(1/2)^\alpha}\leq\liminf_n a_n\log\mathbb P_\nu(T_n)$.

These are the lower-rate conclusions in Theorem 3, Section 4 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081. Their Lean proofs
derive the liminf bounds from the sibling `BlockProbability` module.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable

/-- The endpoint-return argument in Theorem 3, Section 4 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081, gives the sharp
stable lower rate for each strict sub-tube. The radius approaches the target
half-width after the horizon liminf is established. -/
theorem stableEscapeRate_subtube_liminf_lower
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hrate : Tendsto (stableSmallDeviationRate α ν scale)
      atTop (𝓝 0))
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
    C / radius ^ α - delta ≤ atTop.liminf (fun n =>
      stableSmallDeviationRate α ν scale n *
        Real.log (openHorizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal) := by
  let rate : ℝ := C / radius ^ α
  obtain ⟨c, hc, hprobLower⟩ :=
    eventually_openHorizontalTubeProbability_ge_exp_of_stableEscapeRate
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase
      hradius hepsilon hmargin hwidth hdelta
  let constant : ℝ := c ^ α
  let blockLength : ℕ → ℕ := fun n =>
    stableBlockLength α ν constant scale n
  let blockCount : ℕ → ℕ := fun n => stableBlockCount α ν constant scale n
  let lowerReal : ℝ := Real.exp ((rate - delta) * constant)
  let lowerBound : ℝ≥0∞ := ENNReal.ofReal lowerReal
  let probability : ℕ → ℝ≥0∞ := fun n =>
    openHorizontalTubeProbability (iidSequenceLaw ν) (1 / 2) (scale n) n
  let coefficient : ℕ → ℝ := fun n =>
    stableSmallDeviationRate α ν scale n * ((blockCount n + 1 : ℕ) : ℝ)
  have hconstant : 0 < constant := by
    dsimp [constant]
    exact Real.rpow_pos_of_pos hc α
  have hlowerRealPos : 0 < lowerReal := by
    dsimp [lowerReal]
    exact Real.exp_pos _
  have hlowerBoundPos : 0 < lowerBound :=
    ENNReal.ofReal_pos.mpr hlowerRealPos
  have hblockCountRate :=
    tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation
      hα hα₂ hconstant hscale hslow hrate
  have hrateEq : stableSmallDeviationRate α ν scale =ᶠ[atTop]
      fun n => stableScaleTime α ν (scale n) / (n : ℝ) := by
    have hscalePos := IsStableMogulskiiScale.eventually_scale_pos hscale
    have hslowPos : ∀ᶠ n in atTop,
        0 < stableSlowVariation α ν (scale n) :=
      hscale.scale_tendsto_atTop.eventually hslow.eventually_pos
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscalePos, hslowPos]
      with n hn hs hL
    rw [stableSmallDeviationRate, stableScaleTime]
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hnReal, hL.ne']
  have hcountTerm : Tendsto
      (fun n => stableSmallDeviationRate α ν scale n * (blockCount n : ℝ))
      atTop (𝓝 constant⁻¹) := by
    apply hblockCountRate.congr'
    filter_upwards [hrateEq] with n hn
    simp [blockCount, stableBlockCount, hn]
  have hcoefficient : Tendsto coefficient atTop (𝓝 constant⁻¹) := by
    have hsum := hcountTerm.add hrate
    have heq : coefficient =ᶠ[atTop]
        fun n => stableSmallDeviationRate α ν scale n *
          (blockCount n : ℝ) + stableSmallDeviationRate α ν scale n := by
      filter_upwards [] with n
      simp [coefficient]
      ring
    simpa [coefficient] using hsum.congr' heq.symm
  have hleft : Tendsto (fun n => coefficient n * Real.log lowerReal)
      atTop (𝓝 (constant⁻¹ * Real.log lowerReal)) :=
    hcoefficient.mul_const _
  have hleftValue : constant⁻¹ * Real.log lowerReal = rate - delta := by
    simp only [lowerReal, Real.log_exp]
    dsimp [constant]
    field_simp [ne_of_gt hconstant]
  rw [hleftValue] at hleft
  have hprobLower' : ∀ᶠ n in atTop,
      lowerBound ^ (n / blockLength n + 1) ≤ probability n := by
    filter_upwards [hprobLower] with n hn
    simpa [lowerBound, lowerReal, blockLength, blockCount,
      probability, stableBlockCount] using hn
  have hlog : ∀ᶠ n in atTop,
      coefficient n * Real.log lowerReal ≤
        stableSmallDeviationRate α ν scale n *
          Real.log (probability n).toReal := by
    filter_upwards [hprobLower', eventually_gt_atTop (0 : ℕ),
      IsStableMogulskiiScale.eventually_scale_pos hscale,
      hscale.scale_tendsto_atTop.eventually hslow.eventually_pos]
      with n hbound hn hs hL
    have hprobOne : probability n ≤ 1 := by
      change iidSequenceLaw ν
        {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤ 1
      calc
        iidSequenceLaw ν
            {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤
          iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hprobTop : probability n ≠ ∞ :=
      ne_of_lt (hprobOne.trans_lt ENNReal.one_lt_top)
    have hpowTop : lowerBound ^ (n / blockLength n + 1) ≠ ∞ :=
      ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hreal : lowerReal ^ (n / blockLength n + 1) ≤
        (probability n).toReal := by
      have h := (ENNReal.toReal_le_toReal hpowTop hprobTop).2 hbound
      simpa [lowerBound, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hlowerRealPos.le] using h
    have hlogReal : ((n / blockLength n + 1 : ℕ) : ℝ) *
        Real.log lowerReal ≤ Real.log (probability n).toReal := by
      have h := Real.log_le_log
        (pow_pos hlowerRealPos _) hreal
      simpa [Real.log_pow] using h
    have hrateNonneg : 0 ≤ stableSmallDeviationRate α ν scale n := by
      rw [stableSmallDeviationRate]
      positivity
    calc
      coefficient n * Real.log lowerReal =
          stableSmallDeviationRate α ν scale n *
            ((n / blockLength n + 1 : ℕ) : ℝ) * Real.log lowerReal := by
        have hcountEq : blockCount n = n / blockLength n := by
          simp [blockCount, stableBlockCount, blockLength]
        simp [coefficient, hcountEq]
      _ ≤ stableSmallDeviationRate α ν scale n *
            Real.log (probability n).toReal := by
        nlinarith [mul_le_mul_of_nonneg_left hlogReal hrateNonneg]
  have hactualUpper : ∀ᶠ n in atTop,
      stableSmallDeviationRate α ν scale n *
        Real.log (probability n).toReal ≤ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      IsStableMogulskiiScale.eventually_scale_pos hscale,
      hscale.scale_tendsto_atTop.eventually hslow.eventually_pos]
      with n hn hs hL
    have hprobOne : probability n ≤ 1 := by
      change iidSequenceLaw ν
        {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤ 1
      calc
        iidSequenceLaw ν
            {increment | InOpenHorizontalTube (1 / 2) (scale n) n increment} ≤
          iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hprobTop : probability n ≠ ∞ :=
      ne_of_lt (hprobOne.trans_lt ENNReal.one_lt_top)
    have hprobRealOne : (probability n).toReal ≤ 1 :=
      (ENNReal.toReal_le_toReal hprobTop ENNReal.one_ne_top).2 hprobOne
    have hlogNonpos := Real.log_nonpos ENNReal.toReal_nonneg hprobRealOne
    have hrateNonneg : 0 ≤ stableSmallDeviationRate α ν scale n := by
      rw [stableSmallDeviationRate]
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos hrateNonneg hlogNonpos
  calc
    rate - delta = atTop.liminf (fun n => coefficient n * Real.log lowerReal) :=
      hleft.liminf_eq.symm
    _ ≤ atTop.liminf (fun n =>
        stableSmallDeviationRate α ν scale n *
          Real.log (probability n).toReal) :=
      Filter.liminf_le_liminf hlog hleft.isBoundedUnder_ge
        (Filter.isCoboundedUnder_ge_of_eventually_le atTop hactualUpper)

/-- Optimizing the strict interior radius up to one half removes the fixed
sub-tube loss and yields the sharp centered unit-width lower rate. -/
theorem stableEscapeRate_liminf_lower
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hrate : Tendsto (stableSmallDeviationRate α ν scale)
      atTop (𝓝 0))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet (Set.range
      fun n => RandomWalk.normalizedStepPathLaw ν normalization n)) :
    C / ((1 / 2 : ℝ) ^ α) ≤ atTop.liminf (fun n =>
      stableSmallDeviationRate α ν scale n *
        Real.log (openHorizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal) := by
  let target : ℝ := C / ((1 / 2 : ℝ) ^ α)
  let marginSeq : ℕ → ℝ := fun k => 1 / ((k + 3 : ℕ) : ℝ)
  have hden : Tendsto (fun m : ℝ => (1 - m) / 2)
      (𝓝 0) (𝓝 (1 / 2 : ℝ)) := by
    have hnum : Tendsto (fun m : ℝ => (1 : ℝ) - m)
        (𝓝 0) (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub tendsto_id :
        Tendsto (fun m : ℝ => (1 : ℝ) - m)
          (𝓝 0) (𝓝 ((1 : ℝ) - 0)) )
    simpa using hnum.div_const (2 : ℝ)
  have hpow : Tendsto (fun m : ℝ => ((1 - m) / 2) ^ α)
      (𝓝 0) (𝓝 ((1 / 2 : ℝ) ^ α)) := by
    exact (Real.continuousAt_rpow_const (1 / 2 : ℝ) α
      (Or.inl (by norm_num : (1 / 2 : ℝ) ≠ 0))).tendsto.comp hden
  have hdenPos : 0 < (1 / 2 : ℝ) ^ α :=
    Real.rpow_pos_of_pos (by norm_num) α
  have hrateMargin : Tendsto
      (fun m : ℝ => C / (((1 - m) / 2) ^ α))
      (𝓝 0) (𝓝 target) := by
    convert (tendsto_const_nhds.div hpow hdenPos.ne') using 1
  have hmarginSeqZero : Tendsto marginSeq atTop (𝓝 0) := by
    simpa [Function.comp_def, marginSeq, Nat.cast_add, div_eq_mul_inv] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        (tendsto_add_atTop_nat 3)
  have hmarginSeqPos (k : ℕ) : 0 < marginSeq k := by
    dsimp [marginSeq]
    positivity
  have hmarginSeqLtHalf (k : ℕ) : marginSeq k < 1 / 2 := by
    have hk : 2 < k + 3 := by omega
    have hk' : (2 : ℝ) < ((k + 3 : ℕ) : ℝ) := by exact_mod_cast hk
    dsimp [marginSeq]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k + 3 : ℕ))]
    norm_num
    nlinarith
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hcloseTarget : target - δ / 2 < target := by linarith
  have hcloseEvent := (hrateMargin.comp hmarginSeqZero).eventually
    (Ioi_mem_nhds hcloseTarget)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hcloseEvent
  let margin : ℝ := marginSeq N
  let radius : ℝ := (1 - margin) / 2
  let epsilon : ℝ := margin / 32
  have hmarginPos : 0 < margin := hmarginSeqPos N
  have hmarginSmall : margin < 1 / 2 := hmarginSeqLtHalf N
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hendpointMargin : 4 * epsilon < radius := by
    dsimp [epsilon, radius]
    nlinarith [hmarginPos, hmarginSmall]
  have hwidth : 2 * (radius + 4 * epsilon) < 1 := by
    dsimp [epsilon, radius]
    nlinarith [hmarginPos]
  have hclose : target - δ / 2 < C / radius ^ α := by
    simpa [target, radius, margin] using hN N le_rfl
  have hfixed := stableEscapeRate_subtube_liminf_lower
    hscale hα hα₂ hslow hrate hEscape hX hcdf hDOA htightBase
    hradius hepsilon hendpointMargin hwidth (by linarith : 0 < δ / 2)
  have htarget : target ≤ atTop.liminf (fun n =>
      stableSmallDeviationRate α ν scale n *
        Real.log (openHorizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal) + δ := by
    dsimp [target] at hclose ⊢
    linarith
  exact htarget


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable

end
