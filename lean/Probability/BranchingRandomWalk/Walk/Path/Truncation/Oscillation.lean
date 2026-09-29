module

public import Probability.BranchingRandomWalk.Walk.Path.Truncation.Asymptotic
public import Probability.BranchingRandomWalk.Walk.Path.Truncation.Maximal
public import Combinatorics.BranchingWalk.Walk.Path.Block.Scale

/-!
# Asymptotics of truncated oscillation bounds

This file separates the deterministic limit calculation in the fourth-moment
block estimate from its probabilistic proof.  The hypotheses are normalized
component limits, so the calculation is independent of a particular choice of
diffusive or stable scaling.
-/

open Filter MeasureTheory ProbabilityTheory Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- The cutoff contribution for proportional blocks at diffusive scaling. -/
theorem tendsto_proportionalBlock_radius_mul_sqrt_contribution
    {fraction cutoff : ℝ} (hfraction : 0 < fraction) :
    Tendsto (fun n : ℕ =>
      (((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) *
          (cutoff * Real.sqrt n) ^ 2) /
        Real.sqrt n ^ 4)
      atTop (nhds (fraction * cutoff ^ 2)) := by
  have h :=
    (tendsto_proportionalBlockLength_add_one_div hfraction).mul_const
      (cutoff ^ 2)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hsqrtFour : Real.sqrt (n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hsqrtFour]
  field_simp [hn.ne']

/-- The squared block-length contribution for proportional blocks at
diffusive scaling. -/
theorem tendsto_proportionalBlock_sq_sqrt_contribution
    {fraction : ℝ} (hfraction : 0 < fraction) :
    Tendsto (fun n : ℕ =>
      (((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) ^ 2) /
        Real.sqrt n ^ 4)
      atTop (nhds (fraction ^ 2)) := by
  apply (tendsto_proportionalBlockLength_add_one_sq_div_sq hfraction).congr'
  filter_upwards [] with n
  have hsqrtFour : Real.sqrt (n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hsqrtFour]

/-- A fixed number of proportional blocks inspects a finite multiple of the
squared diffusive cutoff. -/
theorem tendsto_proportionalBlock_count_div_cutoff_sq
    (blocks : ℕ) {fraction cutoff : ℝ} (hfraction : 0 < fraction)
    (hcutoff : 0 < cutoff) :
    Tendsto (fun n : ℕ =>
      ((blocks * proportionalBlockLength fraction n + 1 : ℕ) : ℝ) /
        (cutoff * Real.sqrt n) ^ 2)
      atTop (nhds ((blocks : ℝ) * fraction / cutoff ^ 2)) := by
  have hblocks :=
    (tendsto_proportionalBlockLength_div hfraction).const_mul (blocks : ℝ)
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcount : Tendsto (fun n : ℕ =>
      ((blocks * proportionalBlockLength fraction n + 1 : ℕ) : ℝ) / n)
      atTop (nhds ((blocks : ℝ) * fraction)) := by
    convert hblocks.add hone using 1
    · funext n
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    · rw [add_zero]
  have hdiv := hcount.div_const (cutoff ^ 2)
  apply hdiv.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  field_simp [hcutoff.ne', hn.ne']

/-- The discarded-increment union term in the proportional diffusive block
estimate vanishes in the actual `ENNReal` measure codomain. -/
theorem tendsto_proportionalBlock_discardedCost_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (blocks : ℕ) {fraction cutoff : ℝ} (hfraction : 0 < fraction)
    (hcutoff : 0 < cutoff) :
    Tendsto (fun n : ℕ =>
      ((blocks * proportionalBlockLength fraction n + 1 : ℕ) : ENNReal) *
        ν {x | cutoff * Real.sqrt n < |x|})
      atTop (nhds 0) := by
  let count : ℕ → ℕ := fun n =>
    blocks * proportionalBlockLength fraction n + 1
  let radius : ℕ → ℝ := fun n => cutoff * Real.sqrt n
  have hradius : Tendsto radius atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hcutoff
  have hratio : Tendsto (fun n => (count n : ℝ) / radius n ^ 2)
      atTop (nhds ((blocks : ℝ) * fraction / cutoff ^ 2)) := by
    simpa [count, radius] using
      tendsto_proportionalBlock_count_div_cutoff_sq blocks hfraction hcutoff
  have hclosed := tendsto_count_mul_measure_abs_ge_zero
    ν hsq hradius hratio
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa [count, radius] using hclosed)
  · exact Eventually.of_forall fun n => bot_le
  · exact Eventually.of_forall fun n => by
      calc
        ((blocks * proportionalBlockLength fraction n + 1 : ℕ) : ENNReal) *
            ν {x | cutoff * Real.sqrt n < |x|} ≤
            ((blocks * proportionalBlockLength fraction n + 1 : ℕ) : ENNReal) *
              ν {x | cutoff * Real.sqrt n ≤ |x|} :=
          mul_le_mul_of_nonneg_left
            (measure_mono fun x hx => by
              change cutoff * Real.sqrt n < |x| at hx
              change cutoff * Real.sqrt n ≤ |x|
              exact hx.le) bot_le
        _ = ((blocks : ENNReal) * proportionalBlockLength fraction n + 1) *
              ν {x | cutoff * Real.sqrt n ≤ |x|} := by norm_num

/-- The fourth power of the truncation bias contributes nothing for
proportional blocks at diffusive scaling. -/
theorem tendsto_proportionalBlock_truncatedMean_contribution_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    {fraction cutoff : ℝ} (hfraction : 0 < fraction)
    (hcutoff : 0 < cutoff) :
    Tendsto (fun n : ℕ =>
      (((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) *
          truncatedIncrementMean ν (cutoff * Real.sqrt n) ^ 4) /
        Real.sqrt n ^ 4)
      atTop (nhds 0) := by
  have hradius : Tendsto (fun n : ℕ => cutoff * Real.sqrt n) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hcutoff
  have hmeanAbs := tendsto_abs_truncatedIncrementMean_zero
    ν hsq hcentered hradius
  have hmean : Tendsto (fun n : ℕ =>
      truncatedIncrementMean ν (cutoff * Real.sqrt n) ^ 4)
      atTop (nhds 0) := by
    have hpow := hmeanAbs.pow 4
    have hpow' : Tendsto (fun n : ℕ =>
        |truncatedIncrementMean ν (cutoff * Real.sqrt n)| ^ 4)
        atTop (nhds 0) := by
      simpa using hpow
    apply hpow'.congr'
    filter_upwards [] with n
    calc
      |truncatedIncrementMean ν (cutoff * Real.sqrt n)| ^ 4 =
          (|truncatedIncrementMean ν (cutoff * Real.sqrt n)| ^ 2) ^ 2 := by ring
      _ = (truncatedIncrementMean ν (cutoff * Real.sqrt n) ^ 2) ^ 2 := by
        rw [sq_abs]
      _ = truncatedIncrementMean ν (cutoff * Real.sqrt n) ^ 4 := by ring
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmeanDiv : Tendsto (fun n : ℕ =>
      truncatedIncrementMean ν (cutoff * Real.sqrt n) ^ 4 / (n : ℝ))
      atTop (nhds 0) := by
    convert hmean.mul hinv using 1 <;> simp [div_eq_mul_inv]
  have hproduct :=
    (tendsto_proportionalBlockLength_add_one_div hfraction).mul hmeanDiv
  have hproduct' : Tendsto (fun n : ℕ =>
      (((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) / n) *
        (truncatedIncrementMean ν (cutoff * Real.sqrt n) ^ 4 / n))
      atTop (nhds 0) := by
    simpa using hproduct
  apply hproduct'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hsqrtFour : Real.sqrt (n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hsqrtFour]
  field_simp [hn.ne']

/-- Limit of the normalized fourth-moment numerator.  Keeping the three
normalized contributions separate makes this lemma reusable for any cutoff
and block-length parametrization. -/
theorem tendsto_centeredTruncatedFourthNumerator_div_pow
    (ν : Measure ℝ)
    {radius : ℕ → ℝ} {length : ℕ → ℕ} {normalizer : ℕ → ℝ}
    {radiusLimit biasLimit lengthLimit : ℝ}
    (hradius : Tendsto (fun n =>
      (((length n + 1 : ℕ) : ℝ) * radius n ^ 2) / normalizer n ^ 4)
      atTop (nhds radiusLimit))
    (hbias : Tendsto (fun n =>
      (((length n + 1 : ℕ) : ℝ) *
        truncatedIncrementMean ν (radius n) ^ 4) / normalizer n ^ 4)
      atTop (nhds biasLimit))
    (hlength : Tendsto (fun n =>
      (((length n + 1 : ℕ) : ℝ) ^ 2) / normalizer n ^ 4)
      atTop (nhds lengthLimit)) :
    Tendsto (fun n =>
      centeredTruncatedFourthNumerator ν (radius n) (length n) /
        normalizer n ^ 4)
      atTop (nhds
        (8 * (radiusLimit * ∫ x, x ^ 2 ∂ν + biasLimit) +
          3 * lengthLimit * (∫ x, x ^ 2 ∂ν) ^ 2)) := by
  have h := (hradius.mul_const (∫ x, x ^ 2 ∂ν)).add hbias
  have hscaled := (h.const_mul 8).add
    ((hlength.mul_const ((∫ x, x ^ 2 ∂ν) ^ 2)).const_mul 3)
  have hfun : (fun n =>
      centeredTruncatedFourthNumerator ν (radius n) (length n) /
        normalizer n ^ 4) =
      (fun n =>
        8 * ((((length n + 1 : ℕ) : ℝ) * radius n ^ 2 /
              normalizer n ^ 4) * ∫ x, x ^ 2 ∂ν +
            (((length n + 1 : ℕ) : ℝ) *
              truncatedIncrementMean ν (radius n) ^ 4 /
                normalizer n ^ 4)) +
          3 * ((((length n + 1 : ℕ) : ℝ) ^ 2 /
              normalizer n ^ 4) * (∫ x, x ^ 2 ∂ν) ^ 2)) := by
    funext n
    unfold centeredTruncatedFourthNumerator
    ring
  rw [hfun]
  simpa [mul_assoc] using hscaled

/-- Concrete diffusive specialization for a fixed positive block fraction and
cutoff factor. -/
theorem tendsto_proportional_centeredTruncatedFourthNumerator_div_sqrt_pow
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    {fraction cutoff : ℝ} (hfraction : 0 < fraction)
    (hcutoff : 0 < cutoff) :
    Tendsto (fun n : ℕ =>
      centeredTruncatedFourthNumerator ν (cutoff * Real.sqrt n)
          (proportionalBlockLength fraction n) /
        Real.sqrt n ^ 4)
      atTop (nhds
        (8 * (fraction * cutoff ^ 2 * ∫ x, x ^ 2 ∂ν) +
          3 * fraction ^ 2 * (∫ x, x ^ 2 ∂ν) ^ 2)) := by
  have h := tendsto_centeredTruncatedFourthNumerator_div_pow ν
    (tendsto_proportionalBlock_radius_mul_sqrt_contribution hfraction
      (cutoff := cutoff))
    (tendsto_proportionalBlock_truncatedMean_contribution_zero
      ν hsq hcentered hfraction hcutoff)
    (tendsto_proportionalBlock_sq_sqrt_contribution hfraction)
  simpa using h

/-- The accumulated truncation-centering margin is negligible compared with
the diffusive spatial scale. -/
theorem tendsto_proportionalBlock_mul_abs_truncatedMean_div_sqrt_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    {fraction cutoff : ℝ} (hfraction : 0 < fraction)
    (hcutoff : 0 < cutoff) :
    Tendsto (fun n : ℕ =>
      (((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) *
          |truncatedIncrementMean ν (cutoff * Real.sqrt n)|) /
        Real.sqrt n)
      atTop (nhds 0) := by
  have hradius : Tendsto (fun n : ℕ => cutoff * Real.sqrt n) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hcutoff
  have hweighted := tendsto_radius_mul_abs_truncatedIncrementMean_zero
    ν hsq hcentered hradius
  have hsqrtMean : Tendsto (fun n : ℕ =>
      Real.sqrt n * |truncatedIncrementMean ν (cutoff * Real.sqrt n)|)
      atTop (nhds 0) := by
    have h := hweighted.const_mul cutoff⁻¹
    have h' : Tendsto (fun n : ℕ =>
        cutoff⁻¹ * (cutoff * Real.sqrt n *
          |truncatedIncrementMean ν (cutoff * Real.sqrt n)|))
        atTop (nhds 0) := by
      simpa using h
    apply h'.congr'
    filter_upwards [] with n
    field_simp [hcutoff.ne']
  have hproduct :=
    (tendsto_proportionalBlockLength_add_one_div hfraction).mul hsqrtMean
  have hproduct' : Tendsto (fun n : ℕ =>
      (((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) / n) *
        (Real.sqrt n *
          |truncatedIncrementMean ν (cutoff * Real.sqrt n)|))
      atTop (nhds 0) := by
    simpa using hproduct
  apply hproduct'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
  field_simp [hn.ne', hsqrtPos.ne']
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]

/-- Passing from a normalized numerator to the fourth-power threshold
denominator. -/
theorem tendsto_centeredTruncatedFourthNumerator_div_gap_pow
    (ν : Measure ℝ)
    {radius : ℕ → ℝ} {length : ℕ → ℕ}
    {normalizer gap : ℕ → ℝ} {numeratorLimit gapLimit : ℝ}
    (hnumerator : Tendsto (fun n =>
      centeredTruncatedFourthNumerator ν (radius n) (length n) /
        normalizer n ^ 4)
      atTop (nhds numeratorLimit))
    (hgap : Tendsto (fun n => gap n / normalizer n)
      atTop (nhds gapLimit))
    (hgapLimit : gapLimit ≠ 0)
    (hnonzero : ∀ᶠ n in atTop, normalizer n ≠ 0 ∧ gap n ≠ 0) :
    Tendsto (fun n =>
      centeredTruncatedFourthNumerator ν (radius n) (length n) / gap n ^ 4)
      atTop (nhds (numeratorLimit / gapLimit ^ 4)) := by
  have hquotient := hnumerator.div (hgap.pow 4) (pow_ne_zero 4 hgapLimit)
  apply hquotient.congr'
  filter_upwards [hnonzero] with n hn
  rcases hn with ⟨hnorm, hgapn⟩
  dsimp only [Pi.div_apply]
  field_simp [hnorm, hgapn]

/-- `ENNReal.ofReal` transports the preceding finite real limit to the actual
probability-bound codomain. -/
theorem tendsto_ofReal_centeredTruncatedFourthNumerator_div_gap_pow
    (ν : Measure ℝ)
    {radius : ℕ → ℝ} {length : ℕ → ℕ}
    {normalizer gap : ℕ → ℝ} {numeratorLimit gapLimit : ℝ}
    (hnumerator : Tendsto (fun n =>
      centeredTruncatedFourthNumerator ν (radius n) (length n) /
        normalizer n ^ 4)
      atTop (nhds numeratorLimit))
    (hgap : Tendsto (fun n => gap n / normalizer n)
      atTop (nhds gapLimit))
    (hgapLimit : gapLimit ≠ 0)
    (hnonzero : ∀ᶠ n in atTop, normalizer n ≠ 0 ∧ gap n ≠ 0) :
    Tendsto (fun n => ENNReal.ofReal
      (centeredTruncatedFourthNumerator ν (radius n) (length n) /
        gap n ^ 4))
      atTop (nhds (ENNReal.ofReal (numeratorLimit / gapLimit ^ 4))) := by
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_centeredTruncatedFourthNumerator_div_gap_pow ν
      hnumerator hgap hgapLimit hnonzero)

/-- Limit of the reusable fourth-moment probability bound itself. -/
theorem tendsto_centeredTruncatedFourthBound
    (ν : Measure ℝ)
    {radius : ℕ → ℝ} {length : ℕ → ℕ}
    {normalizer gap : ℕ → ℝ} {numeratorLimit gapLimit : ℝ}
    (hnumerator : Tendsto (fun n =>
      centeredTruncatedFourthNumerator ν (radius n) (length n) /
        normalizer n ^ 4)
      atTop (nhds numeratorLimit))
    (hgap : Tendsto (fun n => gap n / normalizer n)
      atTop (nhds gapLimit))
    (hgapLimit : gapLimit ≠ 0)
    (hnonzero : ∀ᶠ n in atTop, normalizer n ≠ 0 ∧ gap n ≠ 0) :
    Tendsto (fun n =>
      centeredTruncatedFourthBound ν (radius n) (length n) (gap n))
      atTop (nhds (ENNReal.ofReal (numeratorLimit / gapLimit ^ 4))) := by
  simpa [centeredTruncatedFourthBound] using
    tendsto_ofReal_centeredTruncatedFourthNumerator_div_gap_pow ν
      hnumerator hgap hgapLimit hnonzero

/-- Explicit limit of the fourth-moment oscillation bound for proportional
blocks, a diffusive cutoff, and a positive diffusive threshold. -/
theorem tendsto_proportional_centeredTruncatedFourthBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    {fraction cutoff threshold : ℝ} (hfraction : 0 < fraction)
    (hcutoff : 0 < cutoff) (hthreshold : 0 < threshold) :
    Tendsto (fun n : ℕ =>
      centeredTruncatedFourthBound ν (cutoff * Real.sqrt n)
        (proportionalBlockLength fraction n)
        (threshold * Real.sqrt n -
          ((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) *
            |truncatedIncrementMean ν (cutoff * Real.sqrt n)|))
      atTop (nhds (ENNReal.ofReal
        ((8 * (fraction * cutoff ^ 2 * ∫ x, x ^ 2 ∂ν) +
          3 * fraction ^ 2 * (∫ x, x ^ 2 ∂ν) ^ 2) /
            threshold ^ 4))) := by
  let gap : ℕ → ℝ := fun n => threshold * Real.sqrt n -
    ((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) *
      |truncatedIncrementMean ν (cutoff * Real.sqrt n)|
  have hbias :=
    tendsto_proportionalBlock_mul_abs_truncatedMean_div_sqrt_zero
      ν hsq hcentered hfraction hcutoff
  have hgap : Tendsto (fun n => gap n / Real.sqrt n)
      atTop (nhds threshold) := by
    have hconst : Tendsto (fun _ : ℕ => threshold) atTop (nhds threshold) :=
      tendsto_const_nhds
    have h := hconst.sub hbias
    have h' : Tendsto (fun n : ℕ => threshold -
        (((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) *
          |truncatedIncrementMean ν (cutoff * Real.sqrt n)|) /
            Real.sqrt n) atTop (nhds threshold) := by
      simpa using h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
    dsimp only [gap]
    field_simp [hsqrtPos.ne']
  have hgapPos : ∀ᶠ n in atTop, 0 < gap n := by
    have hratioPos : ∀ᶠ n in atTop, threshold / 2 < gap n / Real.sqrt n :=
      hgap.eventually (Ioi_mem_nhds (by linarith))
    filter_upwards [hratioPos, eventually_gt_atTop 0] with n hnRatio hn
    have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
    have : 0 < gap n / Real.sqrt n := lt_of_lt_of_le
      (half_pos hthreshold) hnRatio.le
    have hmul := mul_pos this hsqrtPos
    simpa [div_mul_cancel₀ _ hsqrtPos.ne'] using hmul
  apply tendsto_centeredTruncatedFourthBound ν
    (tendsto_proportional_centeredTruncatedFourthNumerator_div_sqrt_pow
      ν hsq hcentered hfraction hcutoff)
    hgap hthreshold.ne'
  filter_upwards [eventually_gt_atTop 0, hgapPos] with n hn hgn
  exact ⟨(Real.sqrt_pos.2 (by positivity)).ne', hgn.ne'⟩

/-- The complete right-hand side of the truncated multiblock estimate has an
explicit diffusive limit. -/
theorem tendsto_proportionalBlock_oscillationBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    (blocks : ℕ) {fraction cutoff threshold : ℝ}
    (hfraction : 0 < fraction) (hcutoff : 0 < cutoff)
    (hthreshold : 0 < threshold) :
    Tendsto (fun n : ℕ =>
      ((blocks * proportionalBlockLength fraction n + 1 : ℕ) : ENNReal) *
          ν {x | cutoff * Real.sqrt n < |x|} +
        (blocks : ENNReal) *
          centeredTruncatedFourthBound ν (cutoff * Real.sqrt n)
            (proportionalBlockLength fraction n)
            (threshold * Real.sqrt n -
              ((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) *
                |truncatedIncrementMean ν (cutoff * Real.sqrt n)|))
      atTop (nhds ((blocks : ENNReal) * ENNReal.ofReal
        ((8 * (fraction * cutoff ^ 2 * ∫ x, x ^ 2 ∂ν) +
          3 * fraction ^ 2 * (∫ x, x ^ 2 ∂ν) ^ 2) /
            threshold ^ 4))) := by
  have htail := tendsto_proportionalBlock_discardedCost_zero
    ν hsq blocks hfraction hcutoff
  have hfour := tendsto_proportional_centeredTruncatedFourthBound
    ν hsq hcentered hfraction hcutoff hthreshold
  simpa [nsmul_eq_mul] using htail.add (hfour.nsmul blocks)

/-- Eventual form of the global proportional-block oscillation estimate.
Any strict upper bound on the explicit limiting right-hand side eventually
controls the actual IID path probability. -/
theorem eventually_measure_exists_block_exists_abs_ge_lt
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    (blocks : ℕ) {fraction cutoff threshold : ℝ}
    (hfraction : 0 < fraction) (hcutoff : 0 < cutoff)
    (hthreshold : 0 < threshold) {bound : ENNReal}
    (hbound : (blocks : ENNReal) * ENNReal.ofReal
        ((8 * (fraction * cutoff ^ 2 * ∫ x, x ^ 2 ∂ν) +
          3 * fraction ^ 2 * (∫ x, x ^ 2 ∂ν) ^ 2) /
            threshold ^ 4) < bound) :
    ∀ᶠ n : ℕ in atTop,
      (iidSequenceLaw ν) {path |
        ∃ j < blocks,
          ∃ k ∈ Finset.range (proportionalBlockLength fraction n + 1),
            threshold * Real.sqrt n ≤
              |blockSum (j * proportionalBlockLength fraction n) (k + 1) path|} <
        bound := by
  let gap : ℕ → ℝ := fun n => threshold * Real.sqrt n -
    ((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) *
      |truncatedIncrementMean ν (cutoff * Real.sqrt n)|
  have hbias :=
    tendsto_proportionalBlock_mul_abs_truncatedMean_div_sqrt_zero
      ν hsq hcentered hfraction hcutoff
  have hgapRatio : Tendsto (fun n => gap n / Real.sqrt n)
      atTop (nhds threshold) := by
    have hconst : Tendsto (fun _ : ℕ => threshold) atTop (nhds threshold) :=
      tendsto_const_nhds
    have h := hconst.sub hbias
    have h' : Tendsto (fun n : ℕ => threshold -
        (((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) *
          |truncatedIncrementMean ν (cutoff * Real.sqrt n)|) /
            Real.sqrt n) atTop (nhds threshold) := by
      simpa using h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
    dsimp only [gap]
    field_simp [hsqrtPos.ne']
  have hgapPos : ∀ᶠ n in atTop, 0 < gap n := by
    have hratioPos : ∀ᶠ n in atTop, threshold / 2 < gap n / Real.sqrt n :=
      hgapRatio.eventually (Ioi_mem_nhds (by linarith))
    filter_upwards [hratioPos, eventually_gt_atTop 0] with n hnRatio hn
    have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hratio : 0 < gap n / Real.sqrt n := lt_of_lt_of_le
      (half_pos hthreshold) hnRatio.le
    have hmul := mul_pos hratio hsqrtPos
    simpa [div_mul_cancel₀ _ hsqrtPos.ne'] using hmul
  have hlimit := tendsto_proportionalBlock_oscillationBound
    ν hsq hcentered blocks hfraction hcutoff hthreshold
  have hright : ∀ᶠ n : ℕ in atTop,
      ((blocks * proportionalBlockLength fraction n + 1 : ℕ) : ENNReal) *
          ν {x | cutoff * Real.sqrt n < |x|} +
        (blocks : ENNReal) *
          centeredTruncatedFourthBound ν (cutoff * Real.sqrt n)
            (proportionalBlockLength fraction n) (gap n) < bound :=
    hlimit.eventually (Iio_mem_nhds hbound)
  filter_upwards [hgapPos, hright] with n hgapN hrightN
  have hgapN' :
      ((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) *
          |truncatedIncrementMean ν (cutoff * Real.sqrt n)| <
        threshold * Real.sqrt n := by
    exact sub_pos.mp (show 0 < gap n from hgapN)
  exact (measure_exists_block_exists_abs_ge_le_of_truncation
    ν hsq (mul_nonneg hcutoff.le (Real.sqrt_nonneg _)) blocks
    (proportionalBlockLength fraction n) hgapN').trans_lt hrightN

end ProbabilityTheory.RandomWalk
