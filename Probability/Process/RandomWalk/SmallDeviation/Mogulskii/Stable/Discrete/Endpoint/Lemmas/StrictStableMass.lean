/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Endpoint.Upper

/-!
# Endpoint-mass conversion for strict-stability bounds

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_horizontalTubeProbability_le_pow_of_endpointMass`: a strict bound below $1$ on the limiting one-block endpoint mass supplies a base $q\in(0,1)$ for the stable block upper estimate. The strict-stability and index-two cases use this conversion.
-/

open Filter MeasureTheory Set
open scoped ENNReal

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

lemma eventually_horizontalTubeProbability_le_pow_of_endpointMass
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
