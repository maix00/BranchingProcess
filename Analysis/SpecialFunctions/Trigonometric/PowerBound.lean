import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Power bounds for trigonometric functions

Elementary finite-multiple estimates used to compare discrete cosine spectra.
-/

namespace Real

/-- On the nonnegative half-period, the cosine at a natural multiple is at
most the corresponding power of the first cosine. -/
theorem cos_nat_mul_le_pow_cos {x : ℝ} (hx : 0 ≤ x) :
    ∀ {n : ℕ}, (n : ℝ) * x ≤ Real.pi / 2 →
      Real.cos ((n : ℝ) * x) ≤ Real.cos x ^ n := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
      have hn' : (n : ℝ) * x ≤ Real.pi / 2 := by
        have hcast : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
        exact le_trans (mul_le_mul_of_nonneg_right hcast hx) hn
      have hxhalf : x ≤ Real.pi / 2 := by
        have hone : (1 : ℝ) ≤ (n + 1 : ℕ) := by
          exact_mod_cast Nat.succ_pos n
        exact le_trans (by simpa using mul_le_mul_of_nonneg_right hone hx) hn
      have hcosx : 0 ≤ Real.cos x :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hxhalf⟩
      have hsinn : 0 ≤ Real.sin ((n : ℝ) * x) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (Nat.cast_nonneg _) hx)
          (hn'.trans (by linarith [Real.pi_pos]))
      have hsinx : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_nonneg_of_le_pi hx
          (hxhalf.trans (by linarith [Real.pi_pos]))
      rw [Nat.cast_succ, add_mul, one_mul, Real.cos_add, pow_succ]
      calc
        Real.cos ((n : ℝ) * x) * Real.cos x -
              Real.sin ((n : ℝ) * x) * Real.sin x ≤
            Real.cos ((n : ℝ) * x) * Real.cos x :=
          sub_le_self _ (mul_nonneg hsinn hsinx)
        _ ≤ Real.cos x ^ n * Real.cos x :=
          mul_le_mul_of_nonneg_right (ih hn') hcosx

end Real
