import Probability.BranchingRandomWalk.Walk.Path.Truncation.Asymptotic
import Probability.BranchingRandomWalk.Walk.Path.Truncation.Maximal
import Combinatorics.BranchingWalk.Walk.Path.Block.Scale

/-!
# Asymptotics of truncated oscillation bounds

This file separates the deterministic limit calculation in the fourth-moment
block estimate from its probabilistic proof.  The hypotheses are normalized
component limits, so the calculation is independent of a particular choice of
diffusive or stable scaling.
-/

open Filter MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

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

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
