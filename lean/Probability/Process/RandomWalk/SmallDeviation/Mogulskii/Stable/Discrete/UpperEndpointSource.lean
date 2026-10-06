/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Support.BoundedSupport
public import Probability.Distributions.Stable.Attraction.NormingRatios.Tauberian
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.UpperEndpoint

/-!
# Source assumptions for the stable-domain endpoint upper bound

Below index two, strict stability itself supplies the strict endpoint-mass
input. The centering contribution at the selected block scale remains an
explicit hypothesis, as required by the block endpoint convergence theorem.
-/

open Filter MeasureTheory Set
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

private theorem eventually_horizontalTubeProbability_le_pow_of_endpointMass
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α constant : ℝ} (hα : 0 < α) (hα₂ : α ≤ 2)
    (hconstant : 0 < constant)
    {normalization center scale : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hscale : Tendsto scale atTop atTop)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hcenter : Tendsto
      (fun n => center (stableBlockLength α ν constant scale n) / scale n)
      atTop (nhds 0))
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hmass :
      (μ.map (fun x : ℝ => constant ^ (1 / α) * x))
        (Icc (-1 : ℝ) 1) < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∀ᶠ n : ℕ in atTop,
        horizontalTubeProbability (iidSequenceLaw ν) a (scale n) n ≤
          ENNReal.ofReal q ^
            (n / stableBlockLength α ν constant scale n) := by
  let p : ENNReal :=
    (μ.map (fun x : ℝ => constant ^ (1 / α) * x)) (Icc (-1 : ℝ) 1)
  have hp : p < 1 := by simpa [p] using hmass
  have hmapUniv :
      (μ.map (fun x : ℝ => constant ^ (1 / α) * x)) Set.univ = 1 := by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  have hple : p ≤ 1 := by
    calc
      p ≤ (μ.map (fun x : ℝ => constant ^ (1 / α) * x)) Set.univ :=
        measure_mono (subset_univ _)
      _ = 1 := hmapUniv
  have hpfinite : p ≠ ⊤ := ne_top_of_le_ne_top (by simp) hple
  have hpReal : p.toReal < 1 :=
    (ENNReal.toReal_lt_toReal hpfinite (by simp)).mpr hp
  let q : ℝ := (p.toReal + 1) / 2
  have hq0 : 0 < q := by
    dsimp [q]
    have := ENNReal.toReal_nonneg (a := p)
    linarith
  have hq1 : q < 1 := by
    dsimp [q]
    linarith
  have hpmass : p < ENNReal.ofReal q := by
    have hreal : p.toReal < q := by
      dsimp [q]
      linarith
    rw [← ENNReal.ofReal_toReal hpfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff hq0).2 hreal
  refine ⟨q, hq0, hq1, ?_⟩
  exact eventually_horizontalTubeProbability_le_pow_stableBlock_endpointMass
    ν μ hα hα₂ hconstant hnorm hslow hscale hDOA hcenter
    hq0 hq1 hpmass ha₀ ha₁

/-- Under the source stable-domain assumptions with `0 < α < 2`, strict
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
