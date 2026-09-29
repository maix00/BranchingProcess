import Probability.Kernel.Survival

/-!
# Iterating positive test-function bounds for kernels

A pointwise lower bound on the one-step action of a nonnegative test function
can be iterated through powers of any kernel.  For a sub-Markov kernel, a test
function bounded by one then turns this into a lower bound on remaining mass.
This is the kernel form of the positive-eigenfunction method for killed
processes.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S]

/-- A one-step sub-eigenfunction inequality iterates to every kernel power. -/
theorem pow_lintegral_lower_bound_of_subEigenfunction
    (K : Kernel S S) (f : S → ℝ≥0∞) (hf : Measurable f)
    (factor : ℝ≥0∞)
    (hstep : ∀ x, factor * f x ≤ ∫⁻ y, f y ∂K x) :
    ∀ n x, factor ^ n * f x ≤ ∫⁻ y, f y ∂(K ^ n) x := by
  intro n
  induction n with
  | zero =>
      intro x
      rw [pow_zero]
      change 1 * f x ≤ ∫⁻ y, f y ∂Kernel.id x
      rw [ProbabilityTheory.Kernel.lintegral_id' hf x]
      simp
  | succ n ih =>
      intro x
      have hcomp : K ^ (n + 1) = (K ^ n) ∘ₖ K := by
        simpa using Kernel.pow_add K n 1
      rw [hcomp, Kernel.lintegral_comp _ _ _ hf]
      calc
        factor ^ (n + 1) * f x = factor ^ n * (factor * f x) := by
          rw [pow_succ]
          ac_rfl
        _ ≤ factor ^ n * ∫⁻ y, f y ∂K x :=
          mul_le_mul_of_nonneg_left (hstep x) (by positivity)
        _ = ∫⁻ y, factor ^ n * f y ∂K x := by
          symm
          exact lintegral_const_mul (factor ^ n) hf
        _ ≤ ∫⁻ y, ∫⁻ z, f z ∂(K ^ n) y ∂K x :=
          lintegral_mono fun y => ih y

/-- A sub-eigenfunction bounded by one gives a lower bound on the mass that
survives every number of steps of a sub-Markov kernel. -/
theorem pow_mul_le_remainingMass_of_subEigenfunction
    (K : Kernel S S) [IsSubMarkovKernel K]
    (f : S → ℝ≥0∞) (hf : Measurable f) (hfun : ∀ x, f x ≤ 1)
    (factor : ℝ≥0∞)
    (hstep : ∀ x, factor * f x ≤ ∫⁻ y, f y ∂K x) :
    ∀ n x, factor ^ n * f x ≤ remainingMass K n x := by
  intro n x
  rw [remainingMass]
  calc
    factor ^ n * f x ≤ ∫⁻ y, f y ∂(K ^ n) x :=
      pow_lintegral_lower_bound_of_subEigenfunction K f hf factor hstep n x
    _ ≤ ∫⁻ _ : S, (1 : ℝ≥0∞) ∂(K ^ n) x :=
      lintegral_mono fun y => hfun y
    _ = (K ^ n) x Set.univ := by simp

/-- A blockwise sub-eigenfunction estimate gives an arbitrary-time survival
bound. The extra block covers the terminal remainder, as in the usual
sub-Markov blocking argument. -/
theorem pow_succ_div_mul_le_remainingMass_of_subEigenfunction
    (K : Kernel S S) [IsSubMarkovKernel K]
    {block : ℕ} (hblock : 0 < block) (n : ℕ) (x : S)
    (f : S → ℝ≥0∞) (hf : Measurable f) (hfun : ∀ y, f y ≤ 1)
    (factor : ℝ≥0∞)
    (hstep : ∀ y, factor * f y ≤ ∫⁻ z, f z ∂(K ^ block) y) :
    factor ^ (n / block + 1) * f x ≤ remainingMass K n x := by
  have hmain := pow_mul_le_remainingMass_of_subEigenfunction
    (K ^ block) f hf hfun factor hstep (n / block + 1) x
  have htime : n ≤ (n / block + 1) * block := by
    have hlt : n < (n / block + 1) * block := by
      simpa [mul_comm] using Nat.lt_mul_div_succ n hblock
    exact hlt.le
  calc
    factor ^ (n / block + 1) * f x ≤
        remainingMass (K ^ block) (n / block + 1) x := hmain
    _ = remainingMass K ((n / block + 1) * block) x := by
      simp [remainingMass, pow_mul, Nat.mul_comm]
    _ ≤ remainingMass K n x := antitone_remainingMass K x htime

end ProbabilityTheory.Kernel
