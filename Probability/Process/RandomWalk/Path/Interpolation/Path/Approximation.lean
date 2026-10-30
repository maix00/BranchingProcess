/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Interpolation.Core
public import Probability.Process.RandomWalk.Path.MaximalJump.FiniteVariance

/-!
# Step-path approximation by polygonal interpolation

The finite-variance maximal-increment estimate controls the Skorokhod distance
between the right-continuous step path and the polygonal interpolation.

## Public declarations

* `ProbabilityTheory.RandomWalk.tendsto_measureReal_edist_normalizedStepPath_linear_zero`
  proves convergence in probability of the extended Skorokhod distance to zero.
* `ProbabilityTheory.RandomWalk.tendsto_measureReal_dist_normalizedStepPath_linear_zero`
  gives the corresponding real-distance statement.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The step and polygonal realizations of a finite-second-moment walk are
asymptotically equivalent in the Skorokhod `J₁` metric. -/
theorem tendsto_measureReal_edist_normalizedStepPath_linear_zero
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hsq : Integrable (fun x : ℝ => x ^ 2) nu)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto (fun n : ℕ => (iidSequenceLaw nu).real
        {increment | ENNReal.ofReal epsilon ≤
          edist
            (normalizedStepCadlagPathIcc (fun n => Real.sqrt n) n increment)
            (normalizedLinearCadlagPathIcc (fun n => Real.sqrt n) n increment)})
      atTop (nhds 0) := by
  have hmax := tendsto_measureReal_maxAbsUpTo_ge_mul_sqrt_zero
    nu hsq hepsilon
  apply squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) _ hmax
  filter_upwards [eventually_gt_atTop 0] with n hn
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro increment hincrement
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
  have hj1 := j1EDist_normalizedStepPath_linear_le
    (fun n => Real.sqrt n) n increment
  change ENNReal.ofReal epsilon ≤ edist
    (normalizedStepCadlagPathIcc (fun n => Real.sqrt n) n increment)
    (normalizedLinearCadlagPathIcc (fun n => Real.sqrt n) n increment) at hincrement
  rw [Skorokhod.edist_cadlagPath_eq_j1EDist] at hincrement
  simp only [abs_inv, abs_of_pos hsqrt] at hj1
  have hbound := hincrement.trans hj1
  have hmaxNonneg : 0 ≤ (Real.sqrt n)⁻¹ * maxAbsUpTo n increment :=
    mul_nonneg (inv_nonneg.2 hsqrt.le) (maxAbsUpTo_nonneg n increment)
  rw [ENNReal.ofReal_le_ofReal_iff hmaxNonneg] at hbound
  rw [le_inv_mul_iff₀ hsqrt] at hbound
  change epsilon * Real.sqrt n ≤ maxAbsUpTo n increment
  simpa only [mul_comm] using hbound

/-- Real-distance form of the preceding Skorokhod interpolation estimate. -/
theorem tendsto_measureReal_dist_normalizedStepPath_linear_zero
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hsq : Integrable (fun x : ℝ => x ^ 2) nu)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto (fun n : ℕ => (iidSequenceLaw nu).real
        {increment | epsilon ≤
          dist
            (normalizedStepCadlagPathIcc (fun n => Real.sqrt n) n increment)
            (normalizedLinearCadlagPathIcc (fun n => Real.sqrt n) n increment)})
      atTop (nhds 0) := by
  have h := tendsto_measureReal_edist_normalizedStepPath_linear_zero
    nu hsq hepsilon
  apply h.congr'
  filter_upwards [] with n
  congr 1
  ext increment
  simp only [Set.mem_ofPred_eq, edist_dist]
  rw [ENNReal.ofReal_le_ofReal_iff dist_nonneg]

end ProbabilityTheory.RandomWalk
