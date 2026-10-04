/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Interpolation.Oscillation.Basic
public import Mathlib.Topology.UnitInterval
public import Probability.Process.RandomWalk.Path.Interpolation
public import Probability.Process.RandomWalk.Path.Truncation.Oscillation
public import Topology.ContinuousMap.Compactness

/-!
# Oscillation probabilities for polygonally interpolated walks

This file lifts deterministic multiblock displacement control to the law of
the normalized polygonal path.
-/

open Filter MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- Failure of one polygonal-path oscillation bound is contained in the
finite event that some relative displacement in the covering blocks exceeds
the chosen threshold. -/
theorem normalizedLinearPathLaw_compl_hasOscillationBound_le
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (scale : ℕ → ℝ) {blocks length n : ℕ} {threshold : ℝ}
    (hn : 0 < n) (hlength : 0 < length)
    (hthreshold : 0 ≤ threshold) (hscale : 0 < scale n)
    (hcover : n + 1 ≤ blocks * length) :
    normalizedLinearPathLaw nu scale n
        {f : C(unitInterval, ℝ) |
          ContinuousMap.HasOscillationBound
            (((length : ℝ) - 1) / n) (9 * threshold) f}ᶜ ≤
      independentIncrementLaw nu {increment |
        ∃ block < blocks,
          ∃ k ∈ Finset.range (length + 1),
            threshold * scale n ≤
              |AdditivePath.blockSum (block * length) (k + 1) increment|} := by
  rw [normalizedLinearPathLaw, Measure.map_apply]
  · apply measure_mono
    intro increment hincrement
    change ¬ContinuousMap.HasOscillationBound
      (((length : ℝ) - 1) / n) (9 * threshold)
        (normalizedLinearContinuousPathIcc scale n increment) at hincrement
    by_contra hgood
    apply hincrement
    intro s t hdist
    exact dist_normalizedLinearContinuousPathIcc_le_of_not_exists_block
      hn hlength hthreshold hscale hcover hgood hdist
  · exact measurable_normalizedLinearContinuousPathIcc scale n
  · exact (ContinuousMap.isClosed_setOf_hasOscillationBound
      (((length : ℝ) - 1) / n) (9 * threshold)).measurableSet.compl

/-- Under a centered finite-second-moment increment law, the explicit
truncation estimate eventually bounds failure of one polygonal-path
oscillation condition. -/
theorem eventually_normalizedLinearPathLaw_compl_hasOscillationBound_lt
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hsq : Integrable (fun x : ℝ => x ^ 2) nu)
    (hcentered : (∫ x : ℝ, x ∂nu) = 0)
    (blocks : ℕ) {fraction cutoff threshold : ℝ}
    (hfraction : 0 < fraction) (hcover : 1 < (blocks : ℝ) * fraction)
    (hcutoff : 0 < cutoff) (hthreshold : 0 < threshold)
    {bound : ENNReal}
    (hbound : (blocks : ENNReal) * ENNReal.ofReal
        ((8 * (fraction * cutoff ^ 2 * ∫ x, x ^ 2 ∂nu) +
          3 * fraction ^ 2 * (∫ x, x ^ 2 ∂nu) ^ 2) /
            threshold ^ 4) < bound) :
    ∀ᶠ n : ℕ in atTop,
      normalizedLinearPathLaw nu (fun n => Real.sqrt n) n
          {f : C(unitInterval, ℝ) |
            ContinuousMap.HasOscillationBound
              (((proportionalBlockLength fraction n : ℝ) - 1) / n)
              (9 * threshold) f}ᶜ < bound := by
  have hbad := eventually_measure_exists_block_exists_abs_ge_lt
    nu hsq hcentered blocks hfraction hcutoff hthreshold hbound
  filter_upwards [eventually_gt_atTop 0,
    eventually_proportionalBlockLength_pos hfraction,
    eventually_succ_le_mul_proportionalBlockLength blocks hcover,
    hbad] with n hn hlength hcoverage hbadN
  exact (normalizedLinearPathLaw_compl_hasOscillationBound_le
    nu (fun n => Real.sqrt n) hn hlength hthreshold.le
      (Real.sqrt_pos.2 (by exact_mod_cast hn)) hcoverage).trans_lt hbadN

end ProbabilityTheory.RandomWalk
