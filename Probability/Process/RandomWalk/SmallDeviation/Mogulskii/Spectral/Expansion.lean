/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Basis
public import LinearAlgebra.Spectrum.DiagonalBasis

/-!
# Finite spectral expansion of the killed interval kernel

This file turns the sine basis into matrix-power and surviving-row-mass
identities.  Geometric tail estimates are kept in the dependent file
UpperBound.lean.
-/

open scoped Matrix
@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Exact finite spectral expansion of an arbitrary function under an
iterate of the killed interval endomorphism. -/
theorem intervalKernelEnd_pow_apply_eq_sum (interiorCount n : ℕ)
    (f : Fin interiorCount → ℝ) :
    (intervalKernelEnd interiorCount ^ n) f =
      ∑ mode, ((intervalSineBasis interiorCount).repr f mode *
          intervalModeEigenvalue interiorCount mode ^ n) •
        intervalSineMode interiorCount mode := by
  simpa only [intervalSineBasis_apply] using
    Module.End.pow_apply_eq_sum_repr_smul
      (intervalKernelEnd interiorCount)
      (intervalSineBasis interiorCount)
      (intervalModeEigenvalue interiorCount)
      (fun mode => by simpa using
        hasEigenvector_intervalSineMode mode) n f

theorem intervalKernel_pow_mulVecLin (interiorCount n : ℕ) :
    (intervalKernel interiorCount ^ n).mulVecLin =
      intervalKernelEnd interiorCount ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, Matrix.mulVecLin_one,
        Module.End.one_eq_id]
  | succ n ih =>
      rw [pow_succ, Matrix.mulVecLin_mul, ih, pow_succ,
        Module.End.mul_eq_comp]
      rfl

/-- Matrix form of the exact finite spectral expansion. -/
theorem intervalKernel_pow_mulVec_eq_sum (interiorCount n : ℕ)
    (f : Fin interiorCount → ℝ) :
    intervalKernel interiorCount ^ n *ᵥ f =
      ∑ mode, ((intervalSineBasis interiorCount).repr f mode *
          intervalModeEigenvalue interiorCount mode ^ n) •
        intervalSineMode interiorCount mode := by
  rw [← Matrix.mulVecLin_apply, intervalKernel_pow_mulVecLin]
  exact intervalKernelEnd_pow_apply_eq_sum interiorCount n f

/-- Exact spectral expansion of the surviving row mass. -/
theorem intervalKernel_pow_rowSum_eq_spectralSum (interiorCount n : ℕ)
    (start : Fin interiorCount) :
    (∑ finish, (intervalKernel interiorCount ^ n) start finish) =
      ∑ mode, (intervalSineBasis interiorCount).repr
          (fun _ => (1 : ℝ)) mode *
        intervalModeEigenvalue interiorCount mode ^ n *
        intervalSineMode interiorCount mode start := by
  have h := congrFun (intervalKernel_pow_mulVec_eq_sum interiorCount n
    (fun _ => (1 : ℝ))) start
  simpa only [Matrix.mulVec, dotProduct, mul_one, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_assoc] using h

/-- A width-uniform coefficient bound reduces the survival upper estimate
to a finite sum of absolute eigenvalue powers. -/
theorem intervalKernel_pow_rowSum_le_two_mul_sum_absEigenvaluePow
    (interiorCount n : ℕ) (start : Fin interiorCount) :
    (∑ finish, (intervalKernel interiorCount ^ n) start finish) ≤
      ∑ mode, 2 * |intervalModeEigenvalue interiorCount mode| ^ n := by
  rw [intervalKernel_pow_rowSum_eq_spectralSum]
  calc
    (∑ mode, (intervalSineBasis interiorCount).repr
          (fun _ => (1 : ℝ)) mode *
        intervalModeEigenvalue interiorCount mode ^ n *
        intervalSineMode interiorCount mode start) ≤
        |∑ mode, (intervalSineBasis interiorCount).repr
            (fun _ => (1 : ℝ)) mode *
          intervalModeEigenvalue interiorCount mode ^ n *
          intervalSineMode interiorCount mode start| := le_abs_self _
    _ ≤ ∑ mode, |(intervalSineBasis interiorCount).repr
          (fun _ => (1 : ℝ)) mode *
        intervalModeEigenvalue interiorCount mode ^ n *
        intervalSineMode interiorCount mode start| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ mode, 2 * |intervalModeEigenvalue interiorCount mode| ^ n := by
      apply Finset.sum_le_sum
      intro mode _
      rw [abs_mul, abs_mul, abs_pow]
      have hcoeff := abs_intervalSineBasis_repr_one_le_two
        interiorCount mode
      have hmode : |intervalSineMode interiorCount mode start| ≤ 1 := by
        simpa only [intervalSineMode] using
          Real.abs_sin_le_one (intervalModeFrequency interiorCount mode *
            (start.val + 1 : ℕ))
      calc
        |(intervalSineBasis interiorCount).repr
              (fun _ => (1 : ℝ)) mode| *
            |intervalModeEigenvalue interiorCount mode| ^ n *
            |intervalSineMode interiorCount mode start| ≤
          (2 * |intervalModeEigenvalue interiorCount mode| ^ n) *
            |intervalSineMode interiorCount mode start| := by
              gcongr
        _ ≤ (2 * |intervalModeEigenvalue interiorCount mode| ^ n) * 1 := by
          gcongr
        _ = 2 * |intervalModeEigenvalue interiorCount mode| ^ n := by ring

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
