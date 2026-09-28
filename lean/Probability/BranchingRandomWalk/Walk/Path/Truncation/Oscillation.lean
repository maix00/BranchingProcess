import Probability.BranchingRandomWalk.Walk.Path.Truncation.Asymptotic
import Probability.BranchingRandomWalk.Walk.Path.Truncation.Maximal

/-!
# Asymptotics of truncated oscillation bounds

This file separates the deterministic limit calculation in the fourth-moment
block estimate from its probabilistic proof.  The hypotheses are normalized
component limits, so the calculation is independent of a particular choice of
diffusive or stable scaling.
-/

open Filter MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

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
