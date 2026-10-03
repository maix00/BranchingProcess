module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
import Algebra.Order.BigOperators.WeightedSum

public section

/-!
# Finite matrix powers and positive eigenfunctions

The statements here are algebraic matrix results.  A killed Markov kernel is
one application of them, but no probability-kernel structure is required.
-/

open scoped BigOperators Matrix

namespace Matrix

section FiniteKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A right eigenfunction remains an eigenfunction of every matrix power. -/
theorem pow_mulVec_of_mulVec_eq_smul
    (kernel : Matrix ι ι ℝ) (weight : ι → ℝ) (eigenvalue : ℝ)
    (heigen : kernel *ᵥ weight = eigenvalue • weight) (n : ℕ) :
    kernel ^ n *ᵥ weight = eigenvalue ^ n • weight := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, heigen]
      simp [pow_succ', smul_smul, mul_comm]

/-- The weighted mass in a row of the `n`-step kernel is the corresponding
eigenvalue power times the starting weight. -/
theorem sum_pow_apply_mul_weight
    (kernel : Matrix ι ι ℝ) (weight : ι → ℝ) (eigenvalue : ℝ)
    (heigen : kernel *ᵥ weight = eigenvalue • weight)
    (n : ℕ) (start : ι) :
    (∑ finish, (kernel ^ n) start finish * weight finish) =
      eigenvalue ^ n * weight start := by
  have h := congrFun (pow_mulVec_of_mulVec_eq_smul kernel weight eigenvalue heigen n) start
  simpa [Matrix.mulVec, dotProduct] using h

/-- A positive eigenfunction bounds total mass in a row of every power of a
finite nonnegative kernel. -/
theorem pow_rowSum_bounds_of_positive_eigenfunction
    (kernel : Matrix ι ι ℝ) (weight : ι → ℝ) (eigenvalue lower upper : ℝ)
    (hkernel : ∀ i j, 0 ≤ kernel i j)
    (heigen : kernel *ᵥ weight = eigenvalue • weight)
    (hlower : ∀ i, lower ≤ weight i)
    (hupper : ∀ i, weight i ≤ upper)
    (n : ℕ) (start : ι) :
    lower * ∑ finish, (kernel ^ n) start finish ≤
        eigenvalue ^ n * weight start ∧
      eigenvalue ^ n * weight start ≤
        upper * ∑ finish, (kernel ^ n) start finish := by
  apply Finset.weightedSum_bounds_of_sum_eq Finset.univ
      (fun finish => (kernel ^ n) start finish) weight lower upper
      (eigenvalue ^ n * weight start)
  · intro finish _
    exact Matrix.pow_apply_nonneg hkernel n start finish
  · exact fun finish _ => hlower finish
  · exact fun finish _ => hupper finish
  · simpa using sum_pow_apply_mul_weight kernel weight eigenvalue heigen n start

end FiniteKernel

end Matrix
