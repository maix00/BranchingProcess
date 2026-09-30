module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Modes
public import Analysis.SpecialFunctions.Trigonometric.FiniteSum

/-!
# Coordinates in the Dirichlet sine basis

This file contains the dot-product formulas and uniform coefficient bounds
used by the killed-kernel spectral estimates.
-/

open scoped Matrix
@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- The coordinate of a vector in the sine basis is characterized by its
dot product with the corresponding mode.  This form avoids choosing a
normalization for the orthogonal basis. -/
theorem intervalSineBasis_repr_mul_selfDot (interiorCount : ℕ)
    (f : Fin interiorCount → ℝ) (mode : Fin interiorCount) :
    (intervalSineBasis interiorCount).repr f mode *
        (intervalSineMode interiorCount mode ⬝ᵥ
          intervalSineMode interiorCount mode) =
      intervalSineMode interiorCount mode ⬝ᵥ f := by
  classical
  conv_rhs => rw [← (intervalSineBasis interiorCount).sum_repr f]
  rw [dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul, intervalSineBasis_apply]
  rw [Finset.sum_eq_single mode]
  · intro other _ hother
    have horth := intervalSineMode_dotProduct_eq_zero
      (interiorCount := interiorCount) (mode₁ := mode) (mode₂ := other)
      (Ne.symm hother)
    simp [horth]
  · simp

theorem intervalSineMode_selfDot_pos {interiorCount : ℕ}
    (mode : Fin interiorCount) :
    0 < intervalSineMode interiorCount mode ⬝ᵥ
      intervalSineMode interiorCount mode := by
  have hnonneg : 0 ≤ intervalSineMode interiorCount mode ⬝ᵥ
      intervalSineMode interiorCount mode := by
    exact Finset.sum_nonneg fun i _ =>
      mul_self_nonneg (intervalSineMode interiorCount mode i)
  have hne : intervalSineMode interiorCount mode ⬝ᵥ
      intervalSineMode interiorCount mode ≠ 0 :=
    fun hzero => intervalSineMode_ne_zero mode
      ((dotProduct_self_eq_zero).mp hzero)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Every discrete Dirichlet sine mode has the same squared norm. -/
theorem intervalSineMode_selfDot (interiorCount : ℕ)
    (mode : Fin interiorCount) :
    intervalSineMode interiorCount mode ⬝ᵥ
        intervalSineMode interiorCount mode =
      ((interiorCount + 1 : ℕ) : ℝ) / 2 := by
  have h := Real.sum_sin_sq_mul_pi_div_succ
    interiorCount (mode.val + 1) (by omega) (by omega)
  rw [← Fin.sum_univ_eq_sum_range] at h
  simpa only [dotProduct, intervalSineMode, intervalModeFrequency,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, sq] using h

/-- Explicit orthogonal-coordinate formula for the (not yet normalized)
Dirichlet sine basis. -/
theorem intervalSineBasis_repr_eq_dotProduct_div (interiorCount : ℕ)
    (f : Fin interiorCount → ℝ) (mode : Fin interiorCount) :
    (intervalSineBasis interiorCount).repr f mode =
      (intervalSineMode interiorCount mode ⬝ᵥ f) /
        (intervalSineMode interiorCount mode ⬝ᵥ
          intervalSineMode interiorCount mode) := by
  apply (eq_div_iff (intervalSineMode_selfDot_pos mode).ne').2
  exact intervalSineBasis_repr_mul_selfDot interiorCount f mode

/-- The normalized coordinate formula with the common Dirichlet sine norm
made explicit. -/
theorem intervalSineBasis_repr_eq_two_mul_dotProduct_div (interiorCount : ℕ)
    (f : Fin interiorCount → ℝ) (mode : Fin interiorCount) :
    (intervalSineBasis interiorCount).repr f mode =
      2 * (intervalSineMode interiorCount mode ⬝ᵥ f) /
        ((interiorCount + 1 : ℕ) : ℝ) := by
  rw [intervalSineBasis_repr_eq_dotProduct_div,
    intervalSineMode_selfDot]
  have hwidth : (((interiorCount + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

theorem abs_intervalSineMode_dotProduct_one_le (interiorCount : ℕ)
    (mode : Fin interiorCount) :
    |intervalSineMode interiorCount mode ⬝ᵥ (fun _ => (1 : ℝ))| ≤
      interiorCount := by
  rw [dotProduct]
  simp only [mul_one]
  calc
    |∑ i, intervalSineMode interiorCount mode i| ≤
        ∑ i, |intervalSineMode interiorCount mode i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin interiorCount, (1 : ℝ) := by
      exact Finset.sum_le_sum fun i _ => by
        simpa only [intervalSineMode] using
          Real.abs_sin_le_one
            (intervalModeFrequency interiorCount mode * (i.val + 1 : ℕ))
    _ = interiorCount := by simp

/-- The sine coefficient of the constant-one vector is uniformly bounded,
independently of the interval width and the mode. -/
theorem abs_intervalSineBasis_repr_one_le_two (interiorCount : ℕ)
    (mode : Fin interiorCount) :
    |(intervalSineBasis interiorCount).repr (fun _ => (1 : ℝ)) mode| ≤ 2 := by
  rw [intervalSineBasis_repr_eq_two_mul_dotProduct_div, abs_div, abs_mul]
  norm_num only [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (interiorCount + 1 : ℕ) by positivity)]
  have hwidth : (0 : ℝ) < (interiorCount + 1 : ℕ) := by positivity
  rw [div_le_iff₀ hwidth]
  have hdot := abs_intervalSineMode_dotProduct_one_le interiorCount mode
  have hcount : (interiorCount : ℝ) ≤ (interiorCount + 1 : ℕ) := by
    exact_mod_cast Nat.le_succ interiorCount
  nlinarith

end ProbabilityTheory.RandomWalk.Mogulskii

end
