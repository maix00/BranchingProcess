/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Real
public import Probability.Process.RandomWalk.FunctionalLimit.Normal.PathLimit
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.CLT

/-!
# Brownian realization of the normal-domain path limit

Centered unit-second-moment increments belong to the standard Gaussian
domain of attraction with normalization `sqrt n`. Combining this scalar
limit with normal-domain `J₁` tightness gives convergence of normalized
càdlàg step paths to the path-valued realization of Mathlib's Brownian
process. The limit realization uses rational coordinates and only the
almost-sure path regularity supplied by `IsBrownianReal`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

/-- Donsker's functional limit for centered unit-second-moment increments,
with the limit realized as the generic rational-coordinate path map of an
actual Mathlib Brownian process. -/
theorem tendsto_normalizedStepCadlagPathIcc_of_centeredUnitSecondMoment_of_brownian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    TendstoInDistribution
      (fun n : ℕ => RandomWalk.normalizedStepCadlagPathIcc
        (fun n => Real.sqrt n) n)
      atTop
      (fun ω => Process.Path.Cadlag.pathMap
        (fun t ω => B (UnitInterval.toNNReal t) ω) ω)
      (fun _ : ℕ => iidSequenceLaw ν) P := by
  change (∫ x : ℝ, x ∂ν) = 0 ∧ (∫ x : ℝ, x ^ 2 ∂ν) = 1 at hν
  obtain ⟨hcentered, hsecondMoment⟩ := hν
  let normalization : ℕ → ℝ := fun n => Real.sqrt n
  have hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0) := by
    simpa [normalization] using
      _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.isInDomainOfAttractionAlong_gaussianReal_zero_one ν
        hcentered hsecondMoment
  have hnormalization : ∀ n, 0 < n → 0 < normalization n := by
    intro n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  let X : unitInterval → Ω → ℝ :=
    fun t ω => B (UnitInterval.toNNReal t) ω
  have hcoordinates : ∀ t, AEMeasurable (X t) P := by
    intro t
    exact hB.toIsPreBrownianReal.aemeasurable (UnitInterval.toNNReal t)
  have hpathLimit := tendsto_normalizedStepPathLaw_of_gaussian_of_brownian
    hDOA hnormalization hB
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact (RandomWalk.measurable_normalizedStepCadlagPathIcc normalization n).aemeasurable
  · exact Process.Path.Cadlag.aemeasurable_pathMap X hcoordinates
  · convert hpathLimit using 1
    · rfl

end ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

end
