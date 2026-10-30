/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Support.BoundedSupport
public import Probability.Distributions.Stable.Attraction.NormingRatios.Tauberian
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Endpoint.Upper
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Endpoint.Lemmas.StrictStableMass
/-!
# Strict-stability input for the endpoint upper bound

## Public declarations

The public declarations are
`eventually_horizontalTubeProbability_le_pow_of_strictStableDomain` and
`eventually_horizontalTubeProbability_le_pow_of_strictStableDomain_indexTwo`.
Under strict stability of the limit law, stable norming, convergence of the
centered block endpoint, and the corresponding stable hypotheses (with the
CDF sign condition in the index-two case), both give $q\in(0,1)$ such that

$$
\mathbb P(\text{horizontal tube through }n)
\le q^{\lfloor n/L_n\rfloor}\quad\text{eventually},
\qquad L_n=\mathrm{stableBlockLength}(\alpha,\nu,c,\mathrm{scale},n).
$$

For $\alpha<2$, strict stability supplies the strict endpoint-mass input.
At index two the CDF hypothesis provides the corresponding gap. The
centering contribution at the selected block scale remains an explicit
hypothesis, as required by the block endpoint convergence theorem.

This non-sharp endpoint-block bound is an auxiliary upper estimate in the
proof of Theorem 1, equation (15), of A. A. Mogul'skii. Its one-block input
comes from Lemma 3, Section 4, p. 764, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.
-/

open Filter MeasureTheory Set
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Under the strict stable-domain assumptions with `0 < α < 2`, strict
stability supplies a strict endpoint-mass bound, and the discrete one-block
upper estimate follows. The block-center ratio is explicit because a general
domain-of-attraction statement does not force this uncentered endpoint limit. -/
theorem eventually_horizontalTubeProbability_le_pow_of_strictStableDomain
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α constant : ℝ} (hstable : IsStrictlyAlphaStable α μ)
    (hα₂ : α < 2) (hconstant : 0 < constant)
    {normalization center scale : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hscale : Tendsto scale atTop atTop)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hcenter : Tendsto
      (fun n => center (stableBlockLength α ν constant scale n) / scale n)
      atTop (nhds 0))
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∀ᶠ n : ℕ in atTop,
        horizontalTubeProbability (iidSequenceLaw ν) a (scale n) n ≤
          ENNReal.ofReal q ^
            (n / stableBlockLength α ν constant scale n) := by
  let αpositive := hstable.1
  have hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν) :=
    hDOA.isSlowlyVarying_stableSlowVariation hstable.isAlphaStable
      αpositive hα₂
  have hmass :
      (μ.map (fun x : ℝ => constant ^ (1 / α) * x))
        (Icc (-1 : ℝ) 1) < 1 :=
    hstable.measure_map_rpow_Icc_lt_one_of_lt_two hα₂ hconstant
  exact eventually_horizontalTubeProbability_le_pow_of_endpointMass
    ν μ αpositive hstable.2.1 hconstant hnorm hslow hscale hDOA hcenter
    ha₀ ha₁ hmass

/-- The same one-block upper bound at `α = 2`. The source `F(0)` condition
provides strict endpoint-mass loss; the slowly varying norming factor remains
explicit because the infinite-variance normal-attraction bridge is separate. -/
theorem eventually_horizontalTubeProbability_le_pow_of_strictStableDomain_indexTwo
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hstable : IsStrictlyAlphaStable 2 μ)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {constant : ℝ} (hconstant : 0 < constant)
    {normalization center scale : ℕ → ℝ}
    (hnorm : IsStableNorming 2 ν normalization)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation 2 ν))
    (hscale : Tendsto scale atTop atTop)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hcenter : Tendsto
      (fun n => center (stableBlockLength 2 ν constant scale n) / scale n)
      atTop (nhds 0))
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∀ᶠ n : ℕ in atTop,
        horizontalTubeProbability (iidSequenceLaw ν) a (scale n) n ≤
          ENNReal.ofReal q ^ (n / stableBlockLength 2 ν constant scale n) := by
  have hmass :
      (μ.map (fun x : ℝ => constant ^ (1 / (2 : ℝ)) * x))
        (Icc (-1 : ℝ) 1) < 1 :=
    hstable.measure_map_rpow_Icc_lt_one_indexTwo hcdf hconstant
  exact eventually_horizontalTubeProbability_le_pow_of_endpointMass
    ν μ (by norm_num) (by norm_num) hconstant hnorm hslow hscale hDOA
    hcenter ha₀ ha₁ hmass

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
