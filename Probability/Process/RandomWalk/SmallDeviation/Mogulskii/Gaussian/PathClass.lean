/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.EscapeConstant
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PathClassRegimes

/-!
# The explicit Gaussian path-class rate

The normal-domain path-class theorem identifies the exponent-two rate using
the stable-process escape constant.  The Brownian calibration proves that
constant is `-π² / 8`; this application file combines the two results so the
public path-class limit has the explicit full-width coefficient `-π² / 2`.

The canonical Brownian path law uses Mathlib's rational-coordinate
construction, so the theorem only relies on almost-everywhere continuity of
Brownian paths.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian

open ProbabilityTheory.Process.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The exponent-two path-class theorem for a Mathlib Brownian process, with
the calibrated constants exposed in the statement.  The unique energy value
is the `M₃` corridor energy from the stable path-class theorem, and its
probability rate has the explicit coefficient `-π² / 2`.

The path input is the canonical càdlàg path law built from the a.e.-continuous
Brownian process; no everywhere-continuous sample-path hypothesis is needed.
-/
theorem tendsto_log_probability_ratio_of_IsM_of_index_two_of_brownian_explicit
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 ν normalization scale)
    (hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0))
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B Q)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : IsM 2 G)
    (hGmeas : MeasurableSet G) :
    HasStableProcessEscapeRate 2 (gaussianReal 0 1)
        (Process.Path.Cadlag.pathLaw Q
          (fun t ω => B (unitIntervalToNNReal t) ω)
          (fun t => hB.toIsPreBrownianReal.aemeasurable
            (unitIntervalToNNReal t))) (-(Real.pi ^ 2) / 8) ∧
      (∀ n : ℕ,
        NullMeasurableSet
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}
          (iidSequenceLaw ν)) ∧
      ∃! H : ℝ,
        (∃ A : M3Approximation 2 G, ∃ hLimits : M3EnergyLimits A,
          H = hLimits.hAlpha) ∧
        Tendsto
          (fun n : ℕ => Real.log
            ((iidSequenceLaw ν {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈ G}).toReal) /
                stableRateNormalization 2 ν scale n)
          atTop (𝓝 (-(Real.pi ^ 2) / 2 * H)) := by
  rcases tendsto_log_probability_ratio_of_IsM_of_index_two_of_brownian
      hscale hDOA hB hG hGmeas with
    ⟨C, hEscape, hNull, H, hH, hUnique⟩
  have hX := hB.isStableLevyProcess
  have hC : C = -(Real.pi ^ 2) / 8 :=
    _root_.ProbabilityTheory.Process.SmallDeviation.Mogulskii.HasStableProcessEscapeRate.eq_neg_pi_sq_div_eight
      hEscape hX canonicalMogulskiiScale
  have hfull : C * 2 ^ (2 : ℝ) = -(Real.pi ^ 2) / 2 :=
    _root_.ProbabilityTheory.Process.SmallDeviation.Mogulskii.HasStableProcessEscapeRate.fullWidthCoefficient_eq_neg_pi_sq_div_two
      hEscape hX canonicalMogulskiiScale
  refine ⟨?_, hNull, H, ⟨hH.1, ?_⟩, ?_⟩
  · simpa [hC] using hEscape
  · have hrate := hH.2
    rw [hfull] at hrate
    exact hrate
  · intro H' hH'
    apply hUnique H'
    refine ⟨hH'.1, ?_⟩
    have hrate := hH'.2
    rw [← hfull] at hrate
    exact hrate

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian

end
